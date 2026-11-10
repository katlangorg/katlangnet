using KatLang.Evaluation;
using KatLang.Evaluation.Caching;
using KatLang.Rendering;
using Xunit.Abstractions;

namespace KatLang.Tests;

/// <summary>
/// C# COUNTERPARTS OF LEAN WITNESS PROGRAMS that no other C# test runs. Each test runs the Lean witness's
/// program on the generic, optimized and async engines, once on the production route and once on the
/// seam-forced plan route (<see cref="InvocationPlanTestSeam"/>), and pins what C# does: outcome, value,
/// diagnostic (code, context frames, text, span), budget accounting and the plan counters the seam exposes.
/// <para><b>Plan conservativity (ledger E-18, <c>lean/KatLangArityLaws/PlanConservativityGuards.lean</c>).</b>
/// Lean refutes the unrestricted fresh-plan claim for META self-view programs by comparing, at the plan's own
/// flight state, <c>NeedPlan.execute</c> with the hypothetical <c>ordinaryCall</c> of the same cell. C# has no
/// plan-free route for these programs: a program with a <c>meta</c> binder passes the J7 gate, so production
/// already retains every plan (not per site), and the seam can only force retention, never suppress it. Both C#
/// configurations therefore run the PLAN route, and their agreement is NOT a planned-versus-ordinary comparison.
/// What C# pins is whole-program plan-route behaviour, checked against Lean's whole-program guards; the Lean
/// flight-state comparison is not reachable from C#, and Lean's ordinary side (the deeper cycle, the extra
/// argument cell) has no C# observation. Nothing here discharges E-18's conservativity obligation. Whether the
/// META difference is accepted or waived is an open owner question (E-18): these tests record neither.</para>
/// <para><b>Cache reentrancy (FG-K1, <c>lean/KatLangArityLaws/CacheReentrancyGuards.lean</c>).</b> The
/// spread-count shape <c>A = (if(tick() &lt; 2, [A, 7], [5]))*</c>, observed through a tracing wrapper around
/// the run-scoped property cache.</para>
/// </summary>
public class LeanWitnessCounterpartTests(ITestOutputHelper output)
{
    private const string MetaPrelude = "Capture(meta op) = op\nWrap(x) = x\n";

    /// <summary><c>R = Capture(Wrap(Inner((Capture(R.Arguments*).Invoke())*)))</c> (Lean <c>selfInvokeDecls</c>).</summary>
    private const string SelfInvoke = MetaPrelude + "Inner(x) = x\nR = Capture(Wrap(Inner((Capture(R.Arguments*).Invoke())*)))\n";

    /// <summary><c>Inner2(x) = x + count(Capture(R.Arguments*).Arguments)</c>, <c>R = Capture(Wrap(Inner2(5)))</c> (Lean <c>viewReadDecls</c>).</summary>
    private const string ViewRead = MetaPrelude + "Inner2(x) = x + count(Capture(R.Arguments*).Arguments)\nR = Capture(Wrap(Inner2(5)))\n";

    /// <summary>The positive control <c>Inner3(x) = x + 1</c> (Lean <c>plainDecls</c>, <c>closureMemberStillConservative</c>).</summary>
    private const string Plain = MetaPrelude + "Inner3(x) = x + 1\nR = Capture(Wrap(Inner3(5)))\n";

    private const string RecursiveCount = "A = (if(tick() < 2, [A, 7], [5]))*\n";

    // The re-entrant `Inner` chain C# reports below the frame that demands the argument cell: its inner preparation
    // is a cycle at once. Lean's flight-state comparison counts 3 frames on the plan route and 5 on the ordinary one;
    // whole-program depths add the enclosing frames (`first`'s, or `.Invoke of R` and `Wrap`), so compare this
    // chain, not the whole depth, with the flight-state numbers.
    private const string PlanRouteCycleChain =
        "while evaluating call to Inner | while evaluating dotCall .Invoke of Capture(...) | while evaluating call to Inner";

    // ── E-18 counterexample 1: the captured call re-invokes itself while forming its own supply ──────

    /// <summary>
    /// Counterpart of <c>selfInvokeOutcomeDiffers</c> (<c>PlanConservativityGuards.lean</c>, and the whole-program
    /// <c>#guard</c> after <c>selfInvokeValueDiffers</c>): <c>first(R.Arguments)</c>. Lean: the whole program fails
    /// with the PLAN route's outcome, an innermost <c>demandCycle</c> under 4 context frames (<c>first</c>'s and
    /// three more); the ordinary call would meet the cycle one invocation deeper (5 frames, not 3, below the flight).
    /// C#: the same plan-route outcome on both C# routes, which are both plan routes (see the class summary).
    /// CURRENT BEHAVIOUR, not an accepted one: E-18 leaves the META difference an open owner question.
    /// </summary>
    [Fact]
    public async Task SelfInvokeOutcomeDiffers_FirstOfArguments_FailsWithThePlanRouteCycle_OnBothCSharpRoutes()
    {
        var observed = await ObserveBothRoutes(SelfInvoke + "first(R.Arguments)", expectRetention: true);
        Assert.Equal(
            "err DemandCycle frames=4 [while evaluating call to first | " + PlanRouteCycleChain + "] inner=DemandCycle @ [4:18, 4:58)",
            observed.Outcome);
        Assert.True(SelfInvokeFirstDiagnostic == observed.Diagnostic, observed.Diagnostic);
        Assert.Equal("steps=6 checkpoints=12 depth=4 items=0 strings=0", observed.Accounting);
        Assert.Equal(2, observed.Plans);
        Assert.Equal(2, observed.Formations);
    }

    /// <summary>
    /// Counterpart of <c>selfInvokeValueDiffers</c> (<c>PlanConservativityGuards.lean</c>): the VALUE demand of the
    /// captured call's argument cell. Lean: production <c>demandNeed</c> fails with a cycle 3 frames deep, the
    /// pre-M1.5 ordinary completion 5 frames deep. C#: <c>R.Invoke()</c> demands the cell through <c>Wrap</c>
    /// and fails with the same three-frame plan-route chain below its two enclosing frames;
    /// <c>count(R.Arguments)</c>, the program Lean's <c>reached</c> runs to create the cell, succeeds with 1
    /// and forms only <c>R</c>'s own supply. No C# route shows the 5-frame ordinary outcome.
    /// </summary>
    [Fact]
    public async Task SelfInvokeValueDiffers_ValueDemandOfTheArgumentCell_IsThePlanRouteCycle_OnBothCSharpRoutes()
    {
        var invoked = await ObserveBothRoutes(SelfInvoke + "R.Invoke()", expectRetention: true);
        Assert.Equal(
            "err DemandCycle frames=5 [while evaluating dotCall .Invoke of R | while evaluating call to Wrap | " + PlanRouteCycleChain
                + "] inner=DemandCycle @ [4:18, 4:58)",
            invoked.Outcome);
        Assert.True(SelfInvokeInvokeDiagnostic == invoked.Diagnostic, invoked.Diagnostic);
        Assert.Equal("steps=7 checkpoints=13 depth=5 items=0 strings=0", invoked.Accounting);
        Assert.Equal(2, invoked.Plans);
        Assert.Equal(2, invoked.Formations);

        var reached = await ObserveBothRoutes(SelfInvoke + "count(R.Arguments)", expectRetention: true);
        Assert.Equal("ok 1 n=1", reached.Outcome);
        Assert.Equal("", reached.Diagnostic);
        Assert.Equal("steps=2 checkpoints=4 depth=3 items=0 strings=0", reached.Accounting);
        Assert.Equal(2, reached.Plans);
        Assert.Equal(1, reached.Formations);
    }

    // ── E-18 counterexample 2: the captured call's body reads its own argument view ─────────────────

    /// <summary>
    /// Counterpart of <c>viewReadHeapDiffers</c> (<c>PlanConservativityGuards.lean</c>). Lean: the same value 6 on
    /// both sides, but the ordinary side allocates ONE MORE argument cell (its <c>count</c> prepares the cell afresh,
    /// while the plan route reuses the prepared supply). C#: value 6 on both C# routes, with exactly the plan
    /// counters of the self-view-free control <c>Inner3</c> (2 plans, 2 supply formations): the body's
    /// <c>count(Capture(R.Arguments*).Arguments)</c> causes no extra supply FORMATION, consistent with Lean's plan side
    /// reusing the prepared supply. Formations are only a proxy: C# exposes no argument-cell allocation counter, so this
    /// is not a heap comparison, and the ordinary side's extra cell has no C# observation. CURRENT BEHAVIOUR (E-18,
    /// owner question open).
    /// </summary>
    [Fact]
    public async Task ViewReadHeapDiffers_SameValue_AndNoExtraSupplyFormation_OnBothCSharpRoutes()
    {
        var first = await ObserveBothRoutes(ViewRead + "first(R.Arguments)", expectRetention: true);
        Assert.Equal("ok 6 n=1", first.Outcome);
        Assert.Equal("", first.Diagnostic);
        Assert.Equal("steps=5 checkpoints=17 depth=4 items=0 strings=0", first.Accounting);
        Assert.Equal(2, first.Plans);
        Assert.Equal(2, first.Formations);

        var invoked = await ObserveBothRoutes(ViewRead + "R.Invoke()", expectRetention: true);
        Assert.Equal("ok 6 n=1", invoked.Outcome);
        Assert.Equal("", invoked.Diagnostic);
        Assert.Equal("steps=6 checkpoints=18 depth=5 items=0 strings=0", invoked.Accounting);
        Assert.Equal(2, invoked.Plans);
        Assert.Equal(2, invoked.Formations);

        var reached = await ObserveBothRoutes(ViewRead + "count(R.Arguments)", expectRetention: true);
        Assert.Equal("ok 1 n=1", reached.Outcome);
        Assert.Equal("", reached.Diagnostic);
        Assert.Equal("steps=2 checkpoints=4 depth=3 items=0 strings=0", reached.Accounting);
        Assert.Equal(2, reached.Plans);
        Assert.Equal(1, reached.Formations);

        // The positive control (`closureMemberStillConservative`): the same value and the same plan counters.
        var control = await ObserveBothRoutes(Plain + "first(R.Arguments)", expectRetention: true);
        Assert.Equal("ok 6 n=1", control.Outcome);
        Assert.Equal("steps=3 checkpoints=12 depth=3 items=0 strings=0", control.Accounting);
        Assert.Equal(first.Plans, control.Plans);
        Assert.Equal(first.Formations, control.Formations);
    }

    // ── FG-K1: cache reentrancy, the spread-count shape ──────────────────────────────────────────

    public static TheoryData<string, string, string, string, long> RecursiveCountPrograms => new()
    {
        // Lean `run [("A", recursiveCount)] [readA]`: atoms [5, 7], the entry ("A", [5, 7], 2), 2 ticks.
        { "A", "ok S[5, 7] n=1", "read d1 miss 5#1; read d0 miss S[5, 7]#2", "steps=2 checkpoints=24 depth=2 items=7 strings=0", 2 },
        // The published owner pair is reused by the second read; `tick()` shows only two ticks ran.
        { "A, A, tick()", "ok S[S[5, 7], S[5, 7], 3] n=3", "read d1 miss 5#1; read d0 miss S[5, 7]#2; read d0 hit S[5, 7]#2", "steps=3 checkpoints=26 depth=2 items=10 strings=0", 3 },
        // Lean `[callA, readA]`: [[5, 7], [5, 7]], the invocation owner publishes the property-level pair.
        { "A(), A, tick()", "ok S[S[5, 7], S[5, 7], 3] n=3", "read d1 miss 5#1; invoke d0 S[5, 7]#2; read d0 hit S[5, 7]#2", "steps=3 checkpoints=26 depth=2 items=10 strings=0", 3 },
    };

    /// <summary>
    /// Counterpart of the <c>recursiveCount</c> guards (<c>CacheReentrancyGuards.lean</c>, § 2 and § 3):
    /// <c>A = (if(tick() &lt; 2, [A, 7], [5]))*</c>. Lean: the re-entrant read counts ONE output (<c>[5]</c>), the
    /// owner TWO (<c>[5, 7]</c>); only the owner's pair is published and no owner stays active. C#, on the
    /// generic, optimized and async engines and with and without the plan seam: the re-entrant read (depth 1)
    /// misses, runs and returns <c>5</c> with one output; the owner (depth 0) returns <c>S[5, 7]</c> with two;
    /// exactly one entry is published, later reads hit it, and no owner is active after the run.
    /// </summary>
    [Theory]
    [MemberData(nameof(RecursiveCountPrograms))]
    public async Task RecursiveCount_ReentrantReadCountsOne_AndTheOwnersPairIsPublished(
        string rows, string expected, string trace, string accounting, long ticks)
    {
        foreach (var engine in Engines)
        foreach (var seam in new[] { false, true })
        {
            var observed = await Observe(RecursiveCount + rows, engine, seam, asyncHost: false);
            var where = $"{engine} seam={seam}";
            Assert.True(expected == observed.Outcome, $"{where}: {observed.Outcome}");
            Assert.True(trace == observed.CacheTrace, $"{where}: {observed.CacheTrace}");
            Assert.Equal("", observed.Diagnostic);
            Assert.Equal(accounting, observed.Accounting);
            Assert.Equal(ticks, observed.BuiltinTicks);
            Assert.Equal(0, observed.HostTicks);
            Assert.True(observed.Published == 1, $"{where}: published {observed.Published}");
            // The sync cache counts stores: exactly ONE, so the re-entrant result was never stored, not even transiently.
            Assert.True(observed.Stores == (engine == Engine.Async ? null : 1), $"{where}: stores {observed.Stores}");
            Assert.True(observed.ActiveOwners == 0, $"{where}: active {observed.ActiveOwners}");
            // A META-free, loop-free program: production never retains plans; the seam retains but finds no call cell.
            Assert.Equal(seam || ForcedInvocationPlansHook.Forced, observed.Retains);
            Assert.False(observed.PerSite);
            Assert.Equal(0, observed.Plans);
            Assert.Equal(0, observed.Formations);
        }
    }

    /// <summary>
    /// The same shape with the tick from a HOST operation <c>tock()</c>, asynchronous on the async engine (so the
    /// owner and the re-entrant read really suspend): the same trace and publication, and three host ticks in all.
    /// </summary>
    [Fact]
    public async Task RecursiveCount_WithAnAsyncHostTick_KeepsTheSameReentrancyLaw()
    {
        foreach (var engine in Engines)
        foreach (var seam in new[] { false, true })
        {
            var observed = await Observe("A = (if(tock() < 2, [A, 7], [5]))*\nA, A, tock()", engine, seam, asyncHost: engine == Engine.Async);
            var where = $"{engine} seam={seam}";
            Assert.True(observed.Outcome == "ok S[S[5, 7], S[5, 7], 3] n=3", $"{where}: {observed.Outcome}");
            Assert.True(observed.CacheTrace == "read d1 miss 5#1; read d0 miss S[5, 7]#2; read d0 hit S[5, 7]#2", $"{where}: {observed.CacheTrace}");
            Assert.Equal(1, observed.Published);
            Assert.True(observed.Stores == (engine == Engine.Async ? null : 1), $"{where}: stores {observed.Stores}");
            Assert.Equal(0, observed.ActiveOwners);
            Assert.Equal(3, observed.HostTicks);
            Assert.Equal(0, observed.BuiltinTicks);
            Assert.Equal("", observed.Diagnostic);
            Assert.Equal("steps=6 checkpoints=29 depth=3 items=10 strings=0", observed.Accounting);
            Assert.Equal(seam || ForcedInvocationPlansHook.Forced, observed.Retains);
            Assert.False(observed.PerSite);
            Assert.Equal(0, observed.Plans);
            Assert.Equal(0, observed.Formations);
        }
    }

    // ── Harness ────────────────────────────────────────────────────────────────────────────────

    private const string CycleMessage = "Demand cycle: the argument depends on its own value while it is being evaluated.";
    private const string PlanRouteCycleText =
        "while evaluating call to Inner: while evaluating dotCall .Invoke of Capture(...): while evaluating call to Inner: " + CycleMessage;
    private const string SelfInvokeFirstDiagnostic = "[4:18] while evaluating call to first: " + PlanRouteCycleText;
    private const string SelfInvokeInvokeDiagnostic = "[4:18] while evaluating dotCall .Invoke of R: while evaluating call to Wrap: " + PlanRouteCycleText;

    public enum Engine { Generic, Optimized, Async }

    private static readonly Engine[] Engines = [Engine.Generic, Engine.Optimized, Engine.Async];

    private sealed record Observation(
        string Outcome, string Diagnostic, string Accounting, long Plans, long Formations, bool Retains, bool PerSite,
        string CacheTrace, int Published, int ActiveOwners, long HostTicks, long BuiltinTicks, int? Stores)
    {
        /// <summary>Everything that must agree across engines and routes (the cache trace included).</summary>
        public string Comparable => $"{Outcome} | {Diagnostic} | {Accounting} | plans={Plans} formations={Formations} | {CacheTrace} | published={Published} active={ActiveOwners} hostTicks={HostTicks} builtinTicks={BuiltinTicks}";
    }

    /// <summary>
    /// Runs <paramref name="source"/> on every engine, on the production route and the seam-forced plan route,
    /// and requires one observation everywhere. <paramref name="expectRetention"/>: the program passes the J7 gate,
    /// so production already retains every plan (fully, not per site) — the reason both C# routes are plan routes.
    /// </summary>
    private async Task<Observation> ObserveBothRoutes(string source, bool expectRetention)
    {
        Observation? reference = null;
        foreach (var engine in Engines)
        foreach (var seam in new[] { false, true })
        {
            var observed = await Observe(source, engine, seam, asyncHost: false);
            Assert.True(observed.Retains == (expectRetention || seam || ForcedInvocationPlansHook.Forced), $"{engine} seam={seam}: retains={observed.Retains}");
            Assert.False(observed.PerSite, $"{engine} seam={seam}: per-site");
            Assert.Equal(0, observed.HostTicks);
            Assert.Equal(0, observed.BuiltinTicks);
            reference ??= observed;
            Assert.True(reference.Comparable == observed.Comparable,
                $"{engine} seam={seam} differs:\n  {observed.Comparable}\nfrom the first run:\n  {reference.Comparable}");
        }
        return reference!;
    }

    private async Task<Observation> Observe(string source, Engine engine, bool seam, bool asyncHost)
    {
        long ticks = 0;
        var operations = HostOperations.Create(asyncHost
            ? HostOperation.CreateAsync("tock", async (_, _) => { await Task.Yield(); return new Result.Atom(Interlocked.Increment(ref ticks)); })
            : HostOperation.Create("tock", (_, _) => new Result.Atom(Interlocked.Increment(ref ticks))));
        var parsed = Parser.Parse(source, new RunOptions { HostOperations = operations });
        Assert.False(parsed.HasErrors, string.Join(Environment.NewLine, parsed.Diagnostics.Select(static d => d.Message)));
        var program = new Expr.AlgorithmExpr(parsed.Root);

        using var activation = seam ? InvocationPlanTestSeam.Activate(new InvocationPlanTestSeam()) : null;
        var observations = new EvaluationObservations();
        EvalResult<Evaluator.CountedResult> result;
        EvaluationBudget budget;
        string trace;
        int published, active;
        int? stores = null; // publications ever stored: the sync reference cache counts them, the async one does not
        if (engine == Engine.Async)
        {
            var inner = new RunScopedAsyncZeroArgPropertyResultCache();
            var cache = new TracingAsyncCache(inner);
            (result, budget) = await Evaluator.RunCountedObservedAsync(program, zeroArgPropertyResultCache: cache,
                observations: observations, hostOperations: operations);
            (trace, published, active) = (cache.Trace, inner.PublishedCount, inner.ActiveOwnerCount);
        }
        else
        {
            var inner = new RunScopedZeroArgPropertyResultCache();
            var cache = new TracingCache(inner);
            (result, budget) = Evaluator.RunCountedObserved(program, enableOptimizations: engine == Engine.Optimized,
                zeroArgPropertyResultCache: cache, observations: observations, hostOperations: operations);
            var snapshot = inner.GetSnapshot();
            // Entries are never evicted within a run, so the peak size is the number of published entries.
            (trace, published, active, stores) = (cache.Trace, snapshot.MaxCacheSize, inner.ActiveOwnerCount, snapshot.Stores);
        }

        string outcome, diagnostic;
        if (result.IsOk)
        {
            outcome = $"ok {Neutral(result.Value.Value)} n={result.Value.EmittedCount}";
            diagnostic = "";
        }
        else
        {
            var frames = new List<string>();
            var error = result.Error;
            while (error is EvalError.WithContext context)
            {
                frames.Add(context.Context);
                error = context.Inner;
            }
            outcome = $"err {result.Error.Code} frames={frames.Count} [{string.Join(" | ", frames)}] inner={error.GetType().Name} @ {result.Error.Span}";
            diagnostic = KatLangError.FromEvalError(result.Error).ToString();
        }
        var accounting = $"steps={budget.ConsumedSteps} checkpoints={budget.ConsumedExpressionCheckpoints} depth={budget.PeakDepth} "
            + $"items={budget.MaterializedItems} strings={budget.MaterializedStringChars}";
        Assert.Equal(seam || ForcedInvocationPlansHook.Forced, budget.PlanTestSeam is not null);
        var observed = new Observation(outcome, diagnostic, accounting, observations.InvocationPlanCount, observations.PlanSupplyFormationCount,
            budget.RetainsInvocationPlans, budget.UsesPerSiteInvocationPlans, trace, published, active, Interlocked.Read(ref ticks), budget.TickCount, stores);
        output.WriteLine($"{engine} seam={seam} {source.TrimEnd().Split('\n')[^1]}: {observed.Comparable}");
        return observed;
    }

    /// <summary>
    /// Records every property access in completion order: its kind, its nesting depth among property accesses,
    /// whether a read ran its evaluation (miss) or was served (hit), and the result with its output count.
    /// Changes no access.
    /// </summary>
    private class TracingCache(IZeroArgPropertyResultCache inner) : IZeroArgPropertyResultCache
    {
        private readonly List<string> _log = [];
        private int _depth;

        public string Trace => string.Join("; ", _log);

        protected int Enter() => _depth++;

        protected void Leave(string kind, int depth, bool? ran, EvalResult<ZeroArgPropertyResult> result)
        {
            _depth--;
            var outcome = result.IsOk ? $"{Neutral(result.Value.Value)}#{result.Value.EmittedCount}" : "err " + result.Error.Code;
            _log.Add($"{kind} d{depth}{(ran is { } r ? r ? " miss" : " hit" : "")} {outcome}");
        }

        public EvalResult<ZeroArgPropertyResult> GetOrEvaluate(ZeroArgPropertyExecution execution, Func<EvalResult<ZeroArgPropertyResult>> evaluate)
        {
            var depth = Enter();
            var ran = false;
            var result = inner.GetOrEvaluate(execution, () => { ran = true; return evaluate(); });
            Leave("read", depth, ran, result);
            return result;
        }

        public EvalResult<ZeroArgPropertyResult> Invoke(ZeroArgPropertyExecution execution, Func<EvalResult<ZeroArgPropertyResult>> evaluate)
        {
            var depth = Enter();
            var result = inner.Invoke(execution, evaluate);
            Leave("invoke", depth, null, result);
            return result;
        }

        public bool ReadObtainsPublishedValue(ZeroArgPropertyCacheKey key) => inner.ReadObtainsPublishedValue(key);
    }

    /// <summary>The async-capable <see cref="TracingCache"/>: supplying it routes the run through the async twin family.</summary>
    private sealed class TracingAsyncCache(IAsyncZeroArgPropertyResultCache inner) : TracingCache(inner), IAsyncZeroArgPropertyResultCache
    {
        public async ValueTask<EvalResult<ZeroArgPropertyResult>> GetOrEvaluateAsync(
            ZeroArgPropertyExecution execution, Func<ValueTask<EvalResult<ZeroArgPropertyResult>>> evaluateAsync)
        {
            var depth = Enter();
            var ran = false;
            var result = await inner.GetOrEvaluateAsync(execution, () => { ran = true; return evaluateAsync(); });
            Leave("read", depth, ran, result);
            return result;
        }

        public async ValueTask<EvalResult<ZeroArgPropertyResult>> InvokeAsync(
            ZeroArgPropertyExecution execution, Func<ValueTask<EvalResult<ZeroArgPropertyResult>>> evaluateAsync)
        {
            var depth = Enter();
            var result = await inner.InvokeAsync(execution, evaluateAsync);
            Leave("invoke", depth, null, result);
            return result;
        }
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
