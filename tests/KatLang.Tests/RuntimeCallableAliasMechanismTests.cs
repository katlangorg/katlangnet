using KatLang.Evaluation;
using KatLang.Semantics;

namespace KatLang.Tests;

/// <summary>
/// META-S3-2: the internal invariants of runtime-target callable aliases that source programs cannot
/// distinguish on their own (the source-level corpus is <see cref="RuntimeCallableAliasCorpusTests"/>):
/// <list type="bullet">
///   <item>Option A classification by the front end (FWD-02 after Q-75 / DOT-05 inference and formula
///   lifting, never instead of them);</item>
///   <item>the ONE binding cell per declaration and declaring activation (<see cref="Evaluator.AliasBindingCell"/>):
///   canonical, retained, established without evaluating anything, a parameter row's own cell, first-wins
///   under concurrency and retry-stable inside a non-initiating observation (Guard B);</item>
///   <item>the run pre-mark and the classification of supplied reference cells at their formation;</item>
///   <item>the editor's unknown-signature presentation.</item>
/// </list>
/// </summary>
public class RuntimeCallableAliasMechanismTests
{
    private static Algorithm Property(Algorithm.User owner, string name)
        => owner.Properties.Single(p => p.Name == name).Value;

    // ── Classification (FWD-02 after inference; Option A) ───────────────────────────────────

    [Theory]
    // An enclosing parameter binding.
    [InlineData("Use(f) = {\n    A = f\n    A(9)\n}\nSq(x) = x * x\nUse(Sq)", "Use", "A")]
    // An argumentless `.Algorithm` link, root-owned.
    [InlineData("Sq(x) = x * x\nCapture(meta op) = op\nR = Capture(Sq(5))\nA = R.Algorithm\nA(9)", null, "A")]
    // A parameter-rooted member path whose fallback name RESOLVES (no inferred parameter).
    [InlineData("G(o) = o + 100\nUse(b) = {\n    A = b.G\n    A(3)\n}\nBox = { G(x) = x * 10 }\nUse(Box)", "Use", "A")]
    // A static name naming a runtime alias: a chain, declared before its target (a forward reference).
    [InlineData("Use(f) = {\n    B = A\n    A = f\n    B(9)\n}\nSq(x) = x * x\nUse(Sq)", "Use", "B")]
    // A structure whose one row is a parameter (it keeps its own members).
    [InlineData("Outer(n) = {\n    Lib = { public X = 10\n    n }\n    Lib.X\n}\nOuter(1)", "Outer", "Lib")]
    public void ARuntimeReferenceRow_OfAnOpenParameterlessBody_IsARuntimeTargetAlias(string source, string? owner, string name)
    {
        var root = SourceProvenance.ParseValid(source).Root;
        var holder = owner is null ? root : Assert.IsType<Algorithm.User>(Property(root, owner));
        var alias = Assert.IsType<Algorithm.Alias>(Property(holder, name));
        Assert.True(alias.HasRuntimeTarget);
        // Nothing static is fabricated: no target identity, signature, arity or forwarding contract.
        Assert.Null(alias.ResolvedTarget);
    }

    [Theory]
    // Q-75 / DOT-05 unchanged (F01 = Q02): an unresolved fallback name stays A's inferred parameter.
    [InlineData("Thousand(v) = v * 1000\nUse(b) = {\n    A = b.G\n    A(Thousand)\n}\nUse(5)", "Use", "A", "G")]
    // F04: `Get = obj.size` keeps its inferred `size`.
    [InlineData("Use(obj) = {\n    Get = obj.size\n    Get(count)\n}\nUse([1, 2, 3])", "Use", "Get", "size")]
    // F06 = Q10: both edges of `b.H.G` stay inferred.
    [InlineData("Thousand(v) = v * 1000\nUse(b) = {\n    A = b.H.G\n    A(Thousand, Thousand)\n}\nUse(5)", "Use", "A", "H,G")]
    // Formula lifting runs first: `A = Mk.Algorithm` with `Mk(t)` is lifted to `A(t)`.
    [InlineData("Capture(meta op) = op\nSq(x) = x * x\nMk(t) = Capture(Sq(t))\nA = Mk.Algorithm\nA(9)", null, "A", "t")]
    public void AnInferredOrLiftedParameter_KeepsTheBodyAFormula(string source, string? owner, string name, string parameters)
    {
        var root = SourceProvenance.ParseValid(source).Root;
        var holder = owner is null ? root : Assert.IsType<Algorithm.User>(Property(root, owner));
        var body = Assert.IsType<Algorithm.User>(Property(holder, name));
        Assert.Equal(parameters.Split(','), body.Params);
    }

    [Theory]
    // Two written rows.
    [InlineData("Use(f) = {\n    A = f, 1\n    A\n}\nUse(5)", "Use", "A")]
    // A closed parameter list is bare forwarding territory, never an alias.
    [InlineData("Use(f) = {\n    W(x) = f\n    W(1)\n}\nUse(5)", "Use", "W")]
    // A computed value row.
    [InlineData("Use(f) = {\n    A = f + 1\n    A\n}\nUse(5)", "Use", "A")]
    public void AnyOtherBody_IsNoRuntimeAlias(string source, string owner, string name)
    {
        var root = SourceProvenance.ParseValid(source).Root;
        var holder = Assert.IsType<Algorithm.User>(Property(root, owner));
        Assert.IsType<Algorithm.User>(Property(holder, name));
    }

    // ── The binding cell ────────────────────────────────────────────────────────────────

    private static Expr.DotCall Link(string receiver) => new(new Expr.Resolve(receiver), "Algorithm");

    private static Algorithm.Alias Wired(Algorithm.Alias alias, ScopeCtx? parent) => alias with { Parent = parent };

    private static ScopeCtx ActivatedScope(Evaluator.EvalCtx ctx, string parameter = "p")
        => new(null, [], [], [parameter]) { Activation = ParameterActivation.Capture([parameter], ctx, []) };

    [Fact]
    public void TheBindingCell_IsCanonicalPerDeclarationAndDeclaringActivation_AndEstablishingItEvaluatesNothing()
    {
        var ctx = Evaluator.EvalCtx.Empty;
        var alias = new Algorithm.Alias(null, [], [], Link("R"));
        var first = ActivatedScope(ctx);
        var second = ActivatedScope(ctx);
        var unactivated = new ScopeCtx(null, [], []);

        var cell = Evaluator.AliasBindingCell(Wired(alias, first), ctx);
        Assert.Same(cell, Evaluator.AliasBindingCell(Wired(alias, first), ctx));
        // A link row is the ONE link cell of CR-15, a runtime projection established inertly.
        Assert.True(cell.HasRuntimeProjection);
        Assert.False(cell.HasCompletedValue);
        Assert.Equal(0, cell.ProjectionComputations);

        // Another activation of the same declaration, the run level, and another declaration with the
        // same row each have their own cell.
        var other = Evaluator.AliasBindingCell(Wired(alias, second), ctx);
        Assert.NotSame(cell, other);
        var runLevel = Evaluator.AliasBindingCell(Wired(alias, unactivated), ctx);
        Assert.NotSame(cell, runLevel);
        Assert.Same(runLevel, Evaluator.AliasBindingCell(Wired(alias, unactivated), ctx));
        var twin = new Algorithm.Alias(null, [], [], Link("R"));
        Assert.NotSame(cell, Evaluator.AliasBindingCell(Wired(twin, first), ctx));
    }

    [Fact]
    public void AParameterRow_IsThatParametersOwnCell()
    {
        var ctx = Evaluator.EvalCtx.Empty;
        static EvalResult<Evaluator.CountedResult> Five() => EvalResult<Evaluator.CountedResult>.Ok(new(new Result.Atom(5), 1));
        var supplied = new NeedCell(Five, () => new(Five()), budget: ctx.Budget);
        var owner = new ScopeCtx(null, [], [], ["f"])
        {
            Activation = ParameterActivation.Capture(["f"], ctx.WithNeedEnv([("f", supplied)]), []),
        };
        var alias = Wired(new Algorithm.Alias(null, [], [], new Expr.Param("f")), owner);
        Assert.Same(supplied, Evaluator.AliasBindingCell(alias, ctx));
        Assert.False(supplied.HasCompletedValue);
    }

    [Fact]
    public async Task RacingEstablishments_AgreeOnOneCell()
    {
        var ctx = Evaluator.EvalCtx.Empty;
        var alias = new Algorithm.Alias(null, [], [], Link("R"));
        foreach (var parent in new[] { ActivatedScope(ctx), new ScopeCtx(null, [], []) })
        {
            var wired = Wired(alias, parent);
            using var start = new Barrier(16);
            var cells = await Task.WhenAll(Enumerable.Range(0, 16).Select(_ => Task.Run(() =>
            {
                start.SignalAndWait();
                return Evaluator.AliasBindingCell(wired, ctx);
            })));
            Assert.All(cells, cell => Assert.Same(cells[0], cell));
        }
    }

    [Fact]
    public async Task ASharedDeclaration_KeepsEachDeclaringNamespacesBindingCell()
    {
        // A host DAG shares the SAME alias declaration under distinct namespaces. Each namespace's
        // local R selects a different callee; unactivated scopes must still have distinct keys.
        const string source = "Sq(x) = x * x\nInc(x) = x + 1\nCapture(meta op) = op\nBox1 = { R = Capture(Sq(5))\n A = R.Algorithm }\nBox2 = { R = Capture(Inc(5))\n A = R.Algorithm }\nBox1.A(3), Box2.A(3)";
        var root = SourceProvenance.ParseValid(source).Root;
        var first = Assert.IsType<Algorithm.User>(Property(root, "Box1"));
        var second = Assert.IsType<Algorithm.User>(Property(root, "Box2"));
        var shared = Assert.IsType<Algorithm.Alias>(Property(first, "A"));
        second = second with { Properties = second.Properties.Select(p => p.Name == "A" ? p with { Value = shared } : p).ToArray() };
        root = root with { Properties = root.Properties.Select(p => p.Name == "Box2" ? p with { Value = second } : p).ToArray() };
        var program = new Expr.AlgorithmExpr(root);

        static void Check(EvalResult<Result> result)
        {
            Assert.True(result.IsOk, result.IsOk ? "" : result.Error.ToString());
            var values = Assert.IsType<Result.SequenceValue>(result.Value).Items;
            Assert.Collection(values,
                x => Assert.Equal(9, Assert.IsType<Result.Atom>(x).Value),
                x => Assert.Equal(4, Assert.IsType<Result.Atom>(x).Value));
        }

        Check(Evaluator.RunObserved(program, new EvaluationObservations(), enableOptimizations: false));
        Check(Evaluator.RunObserved(program, new EvaluationObservations(), enableOptimizations: true));
        Check(await Evaluator.RunAsync(program));
    }

    [Fact]
    public async Task RF1_AHostAliasWithoutFrontEndMetadata_KeepsItsNamespaceThroughAnOpen()
    {
        const string source = "Outer(n) = {\n A = n\n Lib = { public Ref = A }\n B = { open Lib\n public K = 10\n Ref }\n P = { open B\n K }\n P\n}\nOuter(1)";
        var root = SourceProvenance.ParseValid(source).Root;
        var outer = Assert.IsType<Algorithm.User>(Property(root, "Outer"));
        var b = Assert.IsType<Algorithm.Alias>(Property(outer, "B")) with { HasRuntimeTarget = false };
        outer = outer with { Properties = outer.Properties.Select(p => p.Name == "B" ? p with { Value = b } : p).ToArray() };
        root = root with { Properties = root.Properties.Select(p => p.Name == "Outer" ? p with { Value = outer } : p).ToArray() };
        var program = new Expr.AlgorithmExpr(root);
        static void Check(EvalResult<Result> result)
        {
            Assert.True(result.IsOk, result.IsOk ? "" : result.Error.ToString());
            Assert.Equal(10, Assert.IsType<Result.Atom>(result.Value).Value);
        }
        Check(Evaluator.RunObserved(program, new EvaluationObservations(), enableOptimizations: false));
        Check(Evaluator.RunObserved(program, new EvaluationObservations(), enableOptimizations: true));
        Check(await Evaluator.RunAsync(program));
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public async Task ConcurrentAliasResolutions_JoinTheOriginalFlight_AndReplaySuccessOrFailure(bool fails)
    {
        var budget = EvaluationBudget.Create(null);
        budget.MarkAsynchronousRun();
        budget.DecideRuntimeAliasReach(true, false);
        var started = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var release = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var computations = 0;
        var span = new SourceSpan(2, 3, 2, 9);
        var target = new Algorithm.User(null, [new CaptureParameterPattern("x")], [], [], [new Expr.Param("x")]);
        var original = NeedCell.WithRuntimeProjection(
            () => throw new InvalidOperationException("CALLABLE must not demand VALUE"),
            () => throw new InvalidOperationException("CALLABLE must not demand VALUE"),
            () => throw new InvalidOperationException("Async resolution must await the projection"),
            async () =>
            {
                Interlocked.Increment(ref computations);
                started.TrySetResult();
                await release.Task;
                return fails ? new EvalError.TypeMismatch("alias projection failed") { Span = span }
                    : EvalResult<Algorithm?>.Ok(target);
            }, span, budget);
        var ctx = (Evaluator.EvalCtx.Empty with { Budget = budget }).WithNeedEnv([("f", original)]);
        var alias = Wired(new Algorithm.Alias(null, [], [], new Expr.Param("f")), ActivatedScope(ctx, "f"));
        Assert.Same(original, Evaluator.AliasBindingCell(alias, ctx));
        var attempts = Enumerable.Range(0, 16).Select(_ => Evaluator.ResolveAliasTargetAsync(alias, ctx).AsTask()).ToArray();
        await started.Task.WaitAsync(TimeSpan.FromSeconds(10));
        Assert.All(attempts, task => Assert.False(task.IsCompleted));
        release.TrySetResult();
        var results = await Task.WhenAll(attempts).WaitAsync(TimeSpan.FromSeconds(10));
        var replay = await Evaluator.ResolveAliasTargetAsync(alias, ctx);
        foreach (var result in results.Append(replay))
        {
            Assert.Equal(fails, result.IsError);
            if (fails)
            {
                Assert.Same(results[0].Error, result.Error);
                Assert.Equal(span, result.Error.Span);
                Assert.True(Evaluator.IsProjectionFailure(result.Error));
                Assert.Equal("alias projection failed", Assert.IsType<EvalError.TypeMismatch>(result.Error).Message);
            }
            else Assert.Same(target, result.Value);
        }
        Assert.Equal(1, computations);
        Assert.Equal(1, original.ProjectionComputations);
        Assert.False(original.HasCompletedValue);
        Assert.False(original.HasProjectionInFlight);
        Assert.Equal(0, original.ProjectionActiveDependencyCount);
    }

    [Fact]
    public void EstablishingInsideANonInitiatingObservation_IsRetryStable_WhileAFreshRuntimeCellStillFailsLoud()
    {
        var ctx = Evaluator.EvalCtx.Empty;
        var wired = Wired(new Algorithm.Alias(null, [], [], Link("R")), ActivatedScope(ctx));
        NeedCell observed;
        var scope = NeedCell.EnterObservation();
        try
        {
            // Retained by its stable owner (the declaring activation): never a fresh allocation.
            observed = Evaluator.AliasBindingCell(wired, ctx);
            // Guard B is unchanged for a fresh, unretained runtime-projection cell.
            Assert.Throws<System.Diagnostics.UnreachableException>(() => Evaluator.SupplyCell(Link("R"), ctx, []));
        }
        finally
        {
            NeedCell.ExitObservation(scope);
        }

        // The retry reaches the very same cell.
        Assert.Same(observed, Evaluator.AliasBindingCell(wired, ctx));
    }

    // ── The run pre-mark and reference-cell classification ────────────────────────────────

    private static EvaluationBudget RunBudget(string source)
    {
        var parsed = SourceProvenance.ParseValid(source);
        var (result, budget) = Evaluator.RunCountedObserved(new Expr.AlgorithmExpr(parsed.Root));
        Assert.True(result.IsOk, result.IsOk ? "" : result.Error.ToString());
        return budget;
    }

    [Theory]
    [InlineData("Use(f) = {\n    A = f\n    A\n}\nUse(5)", true)]
    [InlineData("Sq(x) = x * x\nUse(f) = {\n    B = Sq\n    B(f)\n}\nUse(5)", false)]
    [InlineData("Sq(x) = x * x\nA = Sq\nA(3)", false)]
    [InlineData("Use(f) = f + 1\nUse(5)", false)]
    public void ARunThatMayReachARuntimeAlias_IsPreMarked_AndNoOtherIs(string source, bool marked)
    {
        var budget = RunBudget(source);
        Assert.Equal(marked, budget.MayReachRuntimeAliases);
        Assert.Equal(marked, budget.HasRuntimeProjections);
    }

    [Fact]
    public void OnlyReferencesThatReachARuntimeAlias_AreRuntimeCells()
    {
        IReadOnlyList<NeedCell?>? seen = null;
        var operations = HostOperations.Create(
            HostOperation.Create("Grab", (_, _) => throw new InvalidOperationException("receiver missing"), "a", "b", "c", "d"));
        var seam = new InvocationPlanTestSeam(new Dictionary<string, Func<IReadOnlyList<NeedCell?>, Result>>
        {
            ["Grab"] = cells => { seen = cells; return new Result.Atom(0); },
        });
        // A host operation's arguments are VALUE roles, so the static reference is a property `Z`.
        const string source = "Sq(x) = x * x\nZ = 5\nCapture(meta op) = op\nR = Capture(Sq(5))\nA = R.Algorithm\nB = A\nBox = { C = A }\nGrab(Z, A, B, Box.C)";
        using (InvocationPlanTestSeam.Activate(seam))
        {
            var parsed = Parser.Parse(source, new RunOptions { HostOperations = operations });
            Assert.False(parsed.HasErrors);
            var (result, budget) = Evaluator.RunCountedObserved(new Expr.AlgorithmExpr(parsed.Root), hostOperations: operations);
            Assert.True(result.IsOk, result.IsOk ? "" : result.Error.ToString());
            Assert.True(budget.MayReachRuntimeAliases);
        }

        Assert.NotNull(seen);
        // A static reference keeps its identity-only cell (optimizer recognition keeps its fast path) ...
        Assert.False(seen![0]!.HasRuntimeProjection);
        // ... while a name, a chain link and a structural member reaching the runtime alias are runtime
        // projections from their formation, never runtime work under an identity-only lock.
        Assert.True(seen[1]!.HasRuntimeProjection);
        Assert.True(seen[2]!.HasRuntimeProjection);
        Assert.True(seen[3]!.HasRuntimeProjection);
    }

    [Theory]
    [InlineData("syntax")]
    [InlineData("fetch")]
    [InlineData("unneeded")]
    public async Task DeferredAdmission_ThroughAnAlias_PreservesFailureAndDemandOrder(string mode)
    {
        var downloads = 0;
        var followingEffects = 0;
        var operations = HostOperations.Create(HostOperation.Create("after", (_, _) =>
        {
            Interlocked.Increment(ref followingEffects);
            return new Result.Atom(1);
        }));
        var source = "Inc(x) = x + 1\nCapture(meta op) = op\nF(0) = Capture(Inc(0))\nF(n) = { open 'https://modules.example/m.kat'\n Capture(Inc2(n)) }\nR = F("
            + (mode == "unneeded" ? "0" : "1") + ")\nA = R.Algorithm\nA(5), after()";
        var parsed = await Parser.ParseAsync(source, new RunOptions
        {
            HostOperations = operations,
            AllowedHosts = ["modules.example"],
            DownloadCode = async (_, _) =>
            {
                Interlocked.Increment(ref downloads);
                await Task.Yield();
                if (mode == "fetch") throw new IOException("module unavailable");
                return "public Inc2(x) = (";
            },
        });
        Assert.False(parsed.HasErrors, string.Join(" | ", parsed.Diagnostics.Select(x => x.Message)));
        Assert.Equal(0, downloads);
        var (result, _) = await Evaluator.RunCountedObservedAsync(new Expr.AlgorithmExpr(parsed.Root), hostOperations: operations);
        if (mode == "unneeded")
        {
            Assert.True(result.IsOk, result.IsOk ? "" : result.Error.ToString());
            var values = Assert.IsType<Result.SequenceValue>(result.Value.Value).Items;
            Assert.Collection(values, x => Assert.Equal(6, Assert.IsType<Result.Atom>(x).Value),
                x => Assert.Equal(1, Assert.IsType<Result.Atom>(x).Value));
            Assert.Equal(0, downloads);
            Assert.Equal(1, followingEffects);
        }
        else
        {
            Assert.True(result.IsError);
            var error = result.Error;
            while (error is EvalError.WithContext context) error = context.Inner;
            var admission = Assert.IsType<EvalError.ModuleRegionMaterializationFailed>(error);
            Assert.NotEmpty(admission.Diagnostics);
            if (mode == "fetch") Assert.Equal(KatLangErrorCode.LoadFetchFailed, admission.Code);
            Assert.Equal(1, downloads);
            Assert.Equal(0, followingEffects);
        }
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public async Task AHostExceptionOnTheAliasCalleeRoute_KeepsItsIdentity_WithoutRetry(bool asynchronous)
    {
        var exception = new InvalidOperationException("host failure");
        var calls = 0;
        var followingEffects = 0;
        var operations = HostOperations.Create(
            asynchronous
                ? HostOperation.CreateAsync("fault", async (_, _) => { Interlocked.Increment(ref calls); await Task.Yield(); throw exception; })
                : HostOperation.Create("fault", (_, _) => { Interlocked.Increment(ref calls); throw exception; }),
            HostOperation.Create("after", (_, _) => { Interlocked.Increment(ref followingEffects); return new Result.Atom(1); }));
        const string source = "F(x) = x\nCapture(meta op) = op\nR = if(fault(), Capture(F(0)), 0)\nA = R.Algorithm\nA(9), after()";
        var options = new RunOptions { HostOperations = operations };
        InvalidOperationException observed;
        if (asynchronous) observed = await Assert.ThrowsAsync<InvalidOperationException>(() => KatLangEngine.RunAsync(source, options));
        else observed = Assert.Throws<InvalidOperationException>(() => KatLangEngine.Run(source, options));
        Assert.Same(exception, observed);
        Assert.Equal(1, calls);
        Assert.Equal(0, followingEffects);
    }

    // ── Editor: an unknown runtime signature is never a fabricated one ─────────────────────

    [Fact]
    public void TheEditor_PresentsARuntimeAlias_AsAnUnknownSignature_ThatTakesADotReceiver()
    {
        const string source = "Sq(x) = x * x\nUse(f) = {\n    A = f\n    9.A\n}\nS = Sq\nUse(Sq), S(2)";
        var parsed = Parser.Parse(source);
        Assert.False(parsed.HasErrors);
        var model = SemanticModelBuilder.Build(parsed);

        var runtime = Assert.IsType<PropertyInfo>(model.FindPropertyAt(new SourcePosition(3, 5)));
        Assert.Equal("A", runtime.Name);
        Assert.True(runtime.HasUnknownRuntimeSignature);
        Assert.Empty(runtime.Parameters);
        Assert.True(runtime.SupportsLexicalDotCall);
        Assert.Null(runtime.AliasTarget);
        Assert.NotNull(runtime.Declaration);

        // A static alias keeps its target's surface.
        var @static = Assert.IsType<PropertyInfo>(model.FindPropertyAt(new SourcePosition(6, 1)));
        Assert.False(@static.HasUnknownRuntimeSignature);
        Assert.Equal("x", Assert.Single(@static.Parameters).Name);
    }
}
