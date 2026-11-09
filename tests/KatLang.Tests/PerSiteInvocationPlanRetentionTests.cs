using KatLang.Evaluation;
using KatLang.Rendering;
using KatLang.Evaluation.Caching;
using KatLang.Optimizations.Loops;
using KatLang.Optimizations.Sequences;

namespace KatLang.Tests;

/// <summary>
/// J7 PER-SITE PLAN RETENTION (C#-only optimization, <see cref="EvaluationBudget.UsesPerSiteInvocationPlans"/>):
/// a LOOP-ONLY run (the gate fired only through <c>while</c>/<c>repeat</c>: no <c>meta</c> binder, no deferred
/// region) plans only the call-shaped supplied cells whose resolved callee can pass them on, so a supplied
/// plain-call pipeline that cannot reach a loop step fuses again. Every case runs the production route and a
/// seam-forced FULLY retaining run (the oracle) on the generic, optimized and async engines and requires the
/// same value or error (with span), host log, <c>tick()</c> effects, accounting and loop-optimizer counters;
/// only the plan count and fusion hits may differ, and only where the rule applies.
/// </summary>
public class PerSiteInvocationPlanRetentionTests
{
    private const string Step = "Step(x) = x + 1, x < 3\n";
    private const string CountingPredicate = "P(x) = tick() > 0 + 0 * x\n";

    /// <summary>
    /// Programs where a supplied call reaches a loop step through a route the per-site rule must see:
    /// every such cell stays a plan, so the production plan count equals the oracle's.
    /// </summary>
    public static TheoryData<string, string> ReachingPrograms => new()
    {
        // Forwarding (AGENTS.md CR-4): the parameter's cell is the step.
        { Step + "W(step) = while(step)\nW(Step(0))", "3" },
        // Higher-order: the cell is a whole argument of a parameter callee.
        { Step + "Apply(f, s) = f(s)\nApply(while, Step(0))", "3" },
        // Closure: the cell is a dot receiver in a nested body.
        { Step + "Run(s) = { G = s.while\nG }\nRun(Step(0))", "3" },
        // Collector spread into a loop.
        { Step + "Fwd(*xs) = while(xs*)\nFwd(Step(0))", "3" },
        // A callable alias of the loop builtin.
        { Step + "W = while\nW(Step(0))", "3" },
        // An extension call whose receiver becomes the step.
        { "Inc(x) = x + 1\nF(s, n) = repeat(s, n)\nInc(0).F(5)", "5" },
        // A clause family whose second clause forwards the slot to a loop.
        { "Inc(x) = x + 1\nL(0, s) = 0\nL(n, s) = repeat(s, n)\nL(3, Inc(0))", "3" },
        // Demanded, then captured: repeat reuses the plan's recorded supply, so the predicate runs 10 times.
        { CountingPredicate + "Both(s) = s + 0, repeat(s, 1)\nBoth(count(filter(range(1, 10), P)))\ntick()", "S[S[10, 10], 11]" },
    };

    [Theory]
    [MemberData(nameof(ReachingPrograms))]
    public async Task ReachingCells_StayPlans_AndMatchFullRetention(string source, string expected)
    {
        foreach (var engine in Engines)
        {
            var (production, oracle) = await Compare(source, engine);
            Assert.Equal("ok " + expected, production.Value);
            Assert.Equal(oracle.Plans, production.Plans);
            Assert.Equal(oracle.Fusions, production.Fusions);
        }
    }

    [Fact]
    public async Task ValueOnlyParameter_FusesItsSuppliedPipeline_AndPredicateRunsOncePerItem()
    {
        // Row five of the brief: `Id` only reads its parameter's VALUE; `Unused` keeps the run loop-only.
        const string source = CountingPredicate + "Id(x) = x\nUnused(s) = s.while\nId(count(filter(range(1, 10), P)))\ntick()";
        foreach (var engine in Engines)
        {
            var (production, oracle) = await Compare(source, engine);
            Assert.Equal("ok S[10, 11]", production.Value);
            // count, filter and range are no plans in production; the oracle plans all three.
            Assert.Equal(3, oracle.Plans);
            Assert.Equal(0, production.Plans);
            Assert.Equal(engine == Engine.Optimized ? 1 : 0, production.Fusions);
            Assert.Equal(0, oracle.Fusions);
        }
    }

    [Fact]
    public async Task InheritedParameterRead_OutsideTheCalleesBody_KeepsThePlan()
    {
        // A host-built body may read a parameter it does not declare: with no lexical owner, the read falls
        // back to the environment a callee inherits below its own bindings, so `D` sees `K`'s `p` although
        // `K`'s own body only calls `D(1)`. The run-wide inherited-read guard keeps `K`'s slot planned.
        static Expr Build(HostOperations operations)
        {
            var parsed = Parser.Parse(Step + "K(p) = D(1)\nD(x) = x\nK(Step(0))", new RunOptions { HostOperations = operations });
            Assert.False(parsed.HasErrors);
            var root = parsed.Root;
            var properties = root.Properties.Select(property => property.Name != "D"
                ? property
                : property with
                {
                    Value = ((Algorithm.User)property.Value) with
                    {
                        Output = [new Expr.Call(new Expr.Resolve("while"), [new Expr.Param("p")])],
                    },
                }).ToList();
            return new Expr.AlgorithmExpr(root with { Properties = properties });
        }

        foreach (var engine in Engines)
        {
            var (production, oracle) = await Compare(Build, engine);
            Assert.Equal("ok 3", production.Value);
            Assert.Equal(oracle.Plans, production.Plans);
        }
        Assert.True(Evaluator.InheritedTransportNames(Build(HostOperations.Create())).Contains("p"));
        Assert.False(Evaluator.InheritedTransportNames(Build(HostOperations.Create())).Contains("x"));
    }

    [Fact]
    public async Task HostLog_IsTheSame_WhenAValueOnlyCellRunsOrdinarily()
    {
        const string source = Step + "Id(x) = x\nId(count(filter(range(1, trace(12)), {v > trace(9)}))), Step(0).while";
        foreach (var engine in Engines)
        {
            var (production, oracle) = await Compare(source, engine);
            Assert.Equal("ok S[3, 3]", production.Value);
            Assert.NotEqual("", production.Log);
            Assert.True(production.Plans < oracle.Plans);
        }
    }

    [Fact]
    public async Task SuppliedPipelineFusion_IsRestored_InALoopProgram()
    {
        const string source = Step + "G(x) = x\nG(count(filter(range(1, 20), {v > 2}))), Step(0).while";
        foreach (var engine in Engines)
        {
            var (production, oracle) = await Compare(source, engine);
            Assert.Equal("ok S[18, 3]", production.Value);
            Assert.Equal(engine == Engine.Optimized, production.Fusions > 0);
            Assert.Equal(0, oracle.Fusions);
            // The loop's own step stays a plan; the pipeline's three call cells do not.
            Assert.Equal(1, production.Plans);
            Assert.Equal(4, oracle.Plans);
        }
    }

    public static TheoryData<int, long> P1Sizes => new() { { 10, 21 }, { 1000, 2001 } };

    [Theory]
    [MemberData(nameof(P1Sizes))]
    public async Task P1Workload_FormsOnlyTheCapturedStepPlan(int n, long oraclePlans)
    {
        var source = $"Id(x) = x\nS(x) = Id(Id(Id(x + 1))), x < {n}\n\nS(0).while";
        foreach (var engine in Engines)
        {
            var (production, oracle) = await Compare(source, engine);
            Assert.Equal($"ok {n}", production.Value);
            Assert.Equal(1, production.Plans);
            Assert.Equal(oraclePlans, oracle.Plans);
        }
    }

    [Fact]
    public void TransportMemo_IsPerBody_NotPerCall()
    {
        // Dispatch wires a callee per call; the per-run memo must not grow with the number of calls.
        int Entries(int n)
        {
            var root = new Expr.AlgorithmExpr(SourceProvenance.ParseValid($"Id(x) = x\nS(x) = Id(Id(Id(x + 1))), x < {n}\n\nS(0).while").Root);
            var (result, budget) = Evaluator.RunCountedObserved(root);
            Assert.True(result.IsOk);
            return budget.TransportedNames.Count + budget.CalleeTransportedNames.Count;
        }
        if (ForcedInvocationPlansHook.Forced) return; // no per-site run, no memo
        Assert.True(Entries(10) > 0);
        Assert.Equal(Entries(10), Entries(500));
    }

    public static TheoryData<string, string> FullyRetainingPrograms => new()
    {
        // A user META binder: per-site retention never applies, plan counts are unchanged.
        { Step + "\nLoop(meta op) = op.Algorithm(op.Arguments*).while\n\nStep(0).Loop", "3" },
        { "Id(x) = x\nCap(meta op) = op.Algorithm(op.Arguments*).while\nS(x) = Id(Id(x + 1)), x < 5\nS(0).Cap", "5" },
        { "Id(x) = x\nUnused(meta op) = op\nS(x) = Id(Id(x + 1)), x < 5\nS(0).while", "5" },
    };

    [Theory]
    [MemberData(nameof(FullyRetainingPrograms))]
    public async Task UserMetaPrograms_KeepFullRetention(string source, string expected)
    {
        foreach (var engine in Engines)
        {
            var (production, oracle) = await Compare(source, engine, expectPerSite: false);
            Assert.Equal("ok " + expected, production.Value);
            Assert.Equal(oracle.Plans, production.Plans);
            Assert.True(production.Plans > 1);
        }
    }

    [Fact]
    public async Task DeferredRegionProgram_KeepsFullRetention()
    {
        var parsed = await Parser.ParseAsync(
            "Id(x) = x\nF(0) = 0\nF(n) = { open 'https://katlang.org/per-site/lib.kat'\n7 }\nS(x) = Id(Id(x + 1)), x < 5\nS(0).while, F(0)",
            new RunOptions { DownloadCode = (_, _) => ValueTask.FromResult("public V = 7") });
        Assert.False(parsed.HasErrors, string.Join(Environment.NewLine, parsed.Diagnostics));
        var program = new Expr.AlgorithmExpr(parsed.Root);
        // A program with a deferred region runs on the async entry only.
        var (production, oracle) = await Compare(_ => program, Engine.Async, expectPerSite: false);
        Assert.Equal("ok S[5, 0]", production.Value);
        Assert.Equal(oracle.Plans, production.Plans);
        Assert.True(production.Plans > 1);
    }

    [Theory]
    [InlineData("Step(x) = x + 1, x < 3\nG(x) = x\nG(1)", false)]
    [InlineData("Step(x) = x + 1, x < 3\nStep(0).while", true)]
    [InlineData("Unused(meta op) = op\nStep(x) = x + 1, x < 3\nStep(0).while", false)]
    public void RunFact_IsLoopOnly_OnlyWhenTheGateFiredThroughTheLoops(string source, bool loopOnly)
    {
        var root = new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root);
        Assert.Null(AstStructuralPreflight.CheckAdmittedProgram(
            root, EvaluationLimits.MaxSupportedAstDepth, AstConsumerProfile.EvaluatorIterativeJoinSpines, out var facts));
        Assert.Equal(loopOnly, facts.IsLoopOnly);
        var (_, budget) = Evaluator.RunCountedObserved(root);
        Assert.Equal(loopOnly && !ForcedInvocationPlansHook.Forced, budget.UsesPerSiteInvocationPlans);
    }

    [Fact]
    public async Task ErrorsSpansAndBudgetFailures_MatchFullRetention()
    {
        foreach (var source in new[]
        {
            Step + "Id(x) = x\nId(count(filter(range(1, 5), {v / 0 > 1}))), Step(0).while",
            Step + "Id(x) = x\nId(Missing(1)), Step(0).while",
            Step + "Id(x) = x\nKeep(a, b) = a + b\nKeep(Id(count(range(1, 3))), Id(1 / 0)), Step(0).while",
        })
        foreach (var engine in Engines)
        {
            var (production, _) = await Compare(source, engine);
            Assert.StartsWith("err ", production.Value, StringComparison.Ordinal);
        }

        const string budgeted = "Id(x) = x\nS(x) = Id(Id(Id(x + 1))), x < 40\n\nS(0).while";
        foreach (var steps in new[] { 1, 7, 50, 300, 900 })
        foreach (var engine in Engines)
            await Compare(budgeted, engine, limits: new EvaluationLimits { MaxSteps = steps });
        foreach (var depth in new[] { 2, 4, 8 })
        foreach (var engine in Engines)
            await Compare(budgeted, engine, limits: new EvaluationLimits { MaxDepth = depth });
    }

    [Fact]
    public void UnplannedCallCell_ReachingAMetaBinder_FailsLoudly()
    {
        if (ForcedInvocationPlansHook.Forced) return; // a forced seam keeps full retention: no per-site run exists
        var budget = EvaluationBudget.Create(null);
        budget.DecideInvocationPlanRetention(programMayCapture: true, loopOnly: true);
        Assert.True(budget.UsesPerSiteInvocationPlans);
        var ctx = Evaluator.EvalCtx.Empty with { Budget = budget };
        var call = new Expr.Call(new Expr.Resolve("Step"), [new Expr.Num(0)]);

        // The per-site rule's ordinary cell for a written invocation.
        var unplanned = Evaluator.SupplyCell(call, ctx, [], unobserved: true);
        Assert.IsType<Evaluator.ExpressionSuspension>(unplanned.Suspension);
        var failure = Assert.Throws<InvalidOperationException>(() => Evaluator.ReferenceAdapterCell(unplanned, ctx));
        Assert.Contains("J7 false negative", failure.Message, StringComparison.Ordinal);

        // A plan of the same run is captured; a non-call cell keeps the ordinary META refusal.
        var planned = Evaluator.SupplyCell(call, ctx, []);
        Assert.IsType<Evaluator.InvocationPlan>(planned.Suspension);
        Assert.True(Evaluator.ReferenceAdapterCell(planned, ctx).IsOk);
        var value = Evaluator.SupplyCell(new Expr.Num(5), ctx, []);
        Assert.IsType<EvalError.NotAnAlgorithm>(Evaluator.ReferenceAdapterCell(value, ctx).Error);
    }

    [Fact]
    public void TransportedNames_ClassifyValueAndTransportPositions()
    {
        static IReadOnlyList<string> Of(string source, string name)
        {
            var root = SourceProvenance.ParseValid(source).Root;
            var algorithm = root.Properties.Single(property => property.Name == name).Value;
            return Evaluator.TransportedNamesOf(algorithm, EvaluationBudget.Create(null)).KnownNames;
        }

        Assert.DoesNotContain("x", Of("Id(x) = x", "Id"));
        Assert.DoesNotContain("x", Of("S(x) = -x + 1, x < 3, x[0]", "S"));
        Assert.Contains("s", Of("W(s) = while(s)", "W"));
        Assert.Contains("s", Of("W(s) = s.while", "W"));
        Assert.Contains("s", Of("W(s) = { G = s\nG.while }", "W"));
        // A nested block reading the parameter is a closure: its row is not the declaring owner's.
        var closure = new Algorithm.User(null, [new CaptureParameterPattern("s")], [], [],
            [new Expr.AlgorithmExpr(new Algorithm.User(null, [], [], [], [new Expr.Param("s")]))]);
        Assert.True(Evaluator.TransportedNamesOf(closure, EvaluationBudget.Create(null)).Contains("s"));
        Assert.Contains("s", Of("W(s) = Id(s)\nId(x) = x", "W"));
        var interpolating = new Algorithm.User(null, [new CaptureParameterPattern("s")], [], [],
            [new Expr.InterpolatedString("", [new InterpolationLink(new Expr.Param("s"), "!")])]);
        Assert.True(Evaluator.TransportedNamesOf(interpolating, EvaluationBudget.Create(null)).Contains("s"));
        // An own-parameter row is a value position; a host-operation call reads its names as transport.
        var hostCall = new Algorithm.User(null, [new CaptureParameterPattern("s")], [], [],
            [new Expr.Param("s"), new Expr.NativeCall("op", ["s"])]);
        Assert.True(Evaluator.TransportedNamesOf(hostCall, EvaluationBudget.Create(null)).Contains("s"));
        Assert.Contains("xs", Of("W(*xs) = Id(xs*)\nId(x) = x", "W"));
        Assert.Contains("s", Of("W(s) = [1, 2][s]", "W"));
    }

    [Fact]
    public void DirectFactQueries_PreserveTheSeamAndItsFullRetentionMode()
    {
        var seam = new InvocationPlanTestSeam();
        using var activation = InvocationPlanTestSeam.Activate(seam);
        var budget = EvaluationBudget.Create(null);
        var body = new Algorithm.User(null, [new CaptureParameterPattern("x")], [], [], [new Expr.Param("x")]);
        budget.DecideInvocationPlanRetention(programMayCapture: true, loopOnly: true, body);
        Assert.Same(seam, budget.PlanTestSeam);
        Assert.False(budget.UsesPerSiteInvocationPlans);
        Assert.False(Evaluator.TransportedNamesOf(body, budget).Contains("x"));
        Assert.Same(seam, budget.PlanTestSeam);
        Assert.False(budget.UsesPerSiteInvocationPlans);
        Assert.True(budget.RetainsInvocationPlans);
    }

    [Fact]
    public void TransportSummaries_AreBounded_OnAdmittedSharedJoinSpines()
    {
        var spine = SharedTransportSpine(4096);
        Assert.Null(AstStructuralPreflight.CheckAdmittedProgram(spine, EvaluationLimits.MaxSupportedAstDepth,
            AstConsumerProfile.EvaluatorIterativeJoinSpines, out _));
        var budget = EvaluationBudget.Create(null);
        var names = Evaluator.TransportedNamesOf(spine, budget);
        Assert.True(names.IsAll);
        Assert.True(names.Contains("not-spelled-in-the-tree"));
        Assert.True(budget.TransportedNames.Count <= 8193);
        Assert.All(budget.TransportedNames.Values, summary =>
            Assert.True(summary.KnownNames.Count <= Evaluator.PerSiteAnalysisWidth));

        var inherited = Evaluator.InheritedTransportNames(spine);
        Assert.True(inherited.IsAll);
        Assert.True(inherited.Contains("not-spelled-in-the-tree"));
    }

    [Fact]
    public async Task SaturatedInheritedSummary_RetainsCellsThatAnExternalBodyCanCapture()
    {
        static Expr Build(HostOperations operations)
        {
            var parsed = Parser.Parse(Step + "K(p) = D(1)\nD(x) = x\nK(Step(0))",
                new RunOptions { HostOperations = operations });
            Assert.False(parsed.HasErrors);
            var properties = parsed.Root.Properties.Select(property => property.Name != "D" ? property : property with
            {
                Value = ((Algorithm.User)property.Value) with
                {
                    Output = [new Expr.Call(new Expr.Resolve("while"), [new Expr.Param("p")])],
                },
            }).ToList();
            properties.Add(new Property("Noise", new Algorithm.User(null, [], [], [], [SharedTransportSpine(256)])));
            return new Expr.AlgorithmExpr(parsed.Root with { Properties = properties });
        }

        Assert.True(Evaluator.InheritedTransportNames(Build(HostOperations.Create())).IsAll);
        foreach (var engine in Engines)
        {
            var (production, oracle) = await Compare(Build, engine);
            Assert.Equal("ok 3", production.Value);
            Assert.Equal(oracle.Plans, production.Plans);
        }
    }

    [Fact]
    public void WideHeadsAndFamilies_StayConservative()
    {
        var width = Evaluator.PerSiteAnalysisWidth + 1;
        var captures = Enumerable.Range(0, width).Select(i => (ParameterPattern)new CaptureParameterPattern("p" + i)).ToArray();
        var body = new Algorithm.User(null, captures, [], [], [new Expr.Param("p0")]);
        var budget = EvaluationBudget.Create(null);
        Assert.False(Evaluator.IsUnobservedSupplySlot(body, 0, budget));

        var wideHead = new Pattern.SequenceValue(Enumerable.Range(0, width).Select(i => (Pattern)new Pattern.LitInt(i)).ToArray());
        var wideFamily = new Algorithm.Conditional(null, [], [new CondBranch(wideHead, body)]);
        Assert.False(Evaluator.IsUnobservedSupplySlot(wideFamily, 0, budget));
        var manyBranches = new Algorithm.Conditional(null, [], Enumerable.Range(0, width)
            .Select(i => new CondBranch(new Pattern.SequenceValue([new Pattern.LitInt(i)]), body)).ToArray());
        Assert.False(Evaluator.IsUnobservedSupplySlot(manyBranches, 0, budget));
    }

    [Fact]
    public void SharedNativeArgumentNames_AreSummarizedOnce()
    {
        var names = new CountedNames(Evaluator.PerSiteAnalysisWidth);
        var native = new Expr.NativeCall("unused", names);
        var root = new Algorithm.User(null, [], [], [], Enumerable.Repeat<Expr>(native, 1024).ToArray());
        var transported = Evaluator.TransportedNamesOf(root, EvaluationBudget.Create(null));
        Assert.False(transported.IsAll);
        Assert.Equal(Evaluator.PerSiteAnalysisWidth, transported.KnownNames.Count);
        Assert.Equal(names.Count, names.Reads);
        names.Reads = 0;
        var inherited = Evaluator.InheritedTransportNames(root);
        Assert.False(inherited.IsAll);
        Assert.Equal(Evaluator.PerSiteAnalysisWidth, inherited.KnownNames.Count);
        Assert.Equal(names.Count, names.Reads);
    }

    [Fact]
    public void InheritedOwnership_DoesNotFlattenSharedPatternDags()
    {
        ParameterPattern pattern = new CaptureParameterPattern("p");
        var levels = new List<CountedPatterns>();
        for (var i = 0; i < 20; i++)
        {
            var items = new CountedPatterns([pattern, pattern]);
            levels.Add(items);
            pattern = new SequenceValueParameterPattern(items);
        }
        var body = new Algorithm.User(null, [pattern], [], [],
            [new Expr.Call(new Expr.Resolve("while"), [new Expr.Param("p")])]);
        Assert.Null(AstStructuralPreflight.CheckAdmittedProgram(body, EvaluationLimits.MaxSupportedAstDepth,
            AstConsumerProfile.EvaluatorIterativeJoinSpines, out _));
        foreach (var items in levels) items.Reads = 0;
        // Structural ownership is deliberately conservative; the million logical captures are never flattened.
        Assert.True(Evaluator.InheritedTransportNames(body).Contains("p"));
        Assert.All(levels, items => Assert.Equal(2, items.Reads));
    }

    private static Expr SharedTransportSpine(int count)
    {
        Expr spine = new Expr.EmptySequence(0);
        for (var i = 0; i < count; i++)
            spine = new Expr.SequenceConstruct(new Expr.SequenceConstruct(spine, spine), new Expr.Param("p" + i));
        return spine;
    }

    private sealed class CountedNames(int count) : IReadOnlyList<string>
    {
        public int Count => count;
        public int Reads { get; set; }
        public string this[int index] { get { Reads++; return "p" + index; } }
        public IEnumerator<string> GetEnumerator()
        {
            for (var i = 0; i < count; i++)
                yield return this[i];
        }
        System.Collections.IEnumerator System.Collections.IEnumerable.GetEnumerator() => GetEnumerator();
    }

    private sealed class CountedPatterns(IReadOnlyList<ParameterPattern> items) : IReadOnlyList<ParameterPattern>
    {
        public int Count => items.Count;
        public int Reads { get; set; }
        public ParameterPattern this[int index] { get { Reads++; return items[index]; } }
        public IEnumerator<ParameterPattern> GetEnumerator()
        {
            for (var i = 0; i < Count; i++) yield return this[i];
        }
        System.Collections.IEnumerator System.Collections.IEnumerable.GetEnumerator() => GetEnumerator();
    }

    // ── Harness ────────────────────────────────────────────────────────────────────────────────

    public enum Engine { Generic, Optimized, Async }

    private static readonly Engine[] Engines = [Engine.Generic, Engine.Optimized, Engine.Async];

    private sealed record Observation(string Value, string Log, string Accounting, string Loops, long Plans, long Fusions, bool PerSite);

    /// <summary>The production run and the seam-forced oracle, asserted equal except for plans and fusion.</summary>
    private static Task<(Observation Production, Observation Oracle)> Compare(
        string source, Engine engine, bool expectPerSite = true, EvaluationLimits? limits = null)
        => Compare(operations => ParseProgram(source, operations), engine, expectPerSite, limits);

    private static async Task<(Observation Production, Observation Oracle)> Compare(
        Func<HostOperations, Expr> build, Engine engine, bool expectPerSite = true, EvaluationLimits? limits = null)
    {
        var production = await Observe(build, engine, oracle: false, limits);
        var oracle = await Observe(build, engine, oracle: true, limits);
        Assert.Equal(oracle.Value, production.Value);
        Assert.Equal(oracle.Log, production.Log);
        Assert.Equal(oracle.Accounting, production.Accounting);
        Assert.Equal(oracle.Loops, production.Loops);
        Assert.False(oracle.PerSite);
        Assert.Equal(expectPerSite && !ForcedInvocationPlansHook.Forced, production.PerSite);
        if (ForcedInvocationPlansHook.Forced)
        {
            // A forced process makes every run an oracle run.
            Assert.Equal(oracle, production);
            return (oracle, oracle);
        }
        Assert.True(production.Plans <= oracle.Plans);
        return (production, oracle);
    }

    private static Expr ParseProgram(string source, HostOperations operations)
    {
        var parsed = Parser.Parse(source, new RunOptions { HostOperations = operations });
        Assert.False(parsed.HasErrors, string.Join(Environment.NewLine, parsed.Diagnostics.Select(static d => d.Message)));
        return new Expr.AlgorithmExpr(parsed.Root);
    }

    private static async Task<Observation> Observe(Func<HostOperations, Expr> build, Engine engine, bool oracle, EvaluationLimits? limits)
    {
        var log = new List<string>();
        var operations = HostOperations.Create(
            HostOperation.Create("trace", (args, _) => { log.Add("trace " + args[0]); return args[0]; }, "x"));
        var program = build(operations);
        using var seam = oracle ? InvocationPlanTestSeam.Activate(new InvocationPlanTestSeam()) : null;
        var observations = new EvaluationObservations();
        var loops = new LoopOptimizationDiagnostics();
        var sequences = new SequencePipelineDiagnostics();
        var (result, budget) = engine == Engine.Async
            ? await Evaluator.RunCountedObservedAsync(program, limits: limits,
                zeroArgPropertyResultCache: new RunScopedAsyncZeroArgPropertyResultCache(),
                loopDiagnostics: loops, sequenceDiagnostics: sequences, observations: observations, hostOperations: operations)
            : Evaluator.RunCountedObserved(program, limits: limits, enableOptimizations: engine == Engine.Optimized,
                loopDiagnostics: loops, sequenceDiagnostics: sequences, observations: observations, hostOperations: operations);
        var value = result.IsOk
            ? "ok " + Neutral(result.Value.Value)
            : $"err {result.Error.Code}: {result.Error} @ {result.Error.Span}";
        var accounting = $"steps={budget.ConsumedSteps} checkpoints={budget.ConsumedExpressionCheckpoints} depth={budget.PeakDepth} "
            + $"items={budget.MaterializedItems} chars={budget.MaterializedStringChars}";
        var s = loops.GetSnapshot();
        var loopCounters = string.Join(",", s.OptimizedLoopHits, s.OptimizedLoopFallbacks, s.LoopPlanBuilds, s.LoopExecutions,
            s.LoopIterations, s.PlannedExpressionHits, s.PlannedExpressionFallbacks, s.GenericExpressionEvaluationsInsideOptimizedLoops,
            s.PlannedBuiltinOperations, s.CountedParameterReferencesPlanned, s.CountedParameterReferencesFallbacks)
            + " " + string.Join(";", s.FallbackReasons.OrderBy(static p => p.Key, StringComparer.Ordinal).Select(static p => p.Key + "=" + p.Value));
        return new Observation(value, string.Join("|", log), accounting, loopCounters,
            observations.InvocationPlanCount, sequences.FilterCountFusionHits, budget.UsesPerSiteInvocationPlans);
    }

    private static string Neutral(Result value) => value switch
    {
        Result.Atom atom => ValueTextRenderer.FormatNumberInvariant(atom.Value),
        Result.Str text => "'" + text.Value + "'",
        Result.Bool boolean => boolean.Value ? "true" : "false",
        Result.SequenceValue sequence => "S[" + string.Join(", ", sequence.Items.Select(Neutral)) + "]",
        Result.ListValue list => "L[" + string.Join(", ", list.Items.Select(Neutral)) + "]",
        Result.CallReference => "CallReference",
    };
}
