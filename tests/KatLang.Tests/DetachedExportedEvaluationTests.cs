using KatLang.Evaluation;
using KatLang.Evaluation.Caching;
using KatLang.Optimizations.Loops;
using KatLang.Tests.AsyncEvaluation;

namespace KatLang.Tests;

/// <summary>
/// EXPORTED-DETACHED (November 2026): the evaluator ENFORCES the exposure classification it formerly
/// trusted. Every evaluation that can create or own an <see cref="PropertyExposure.Exported"/>
/// zero-argument key runs DETACHED from the activations that exist when it starts
/// (<c>Evaluator.DetachedEvaluation</c>), and a captured parameter read is LEXICAL-ONLY
/// (<c>Evaluator.CapturedParameterActivation</c>): it goes through its lexical owner's activation or
/// finds no binding, and never falls back to a caller's environment. The checked paths refuse
/// a misclassified capture with <see cref="KatLangErrorCode.UnknownName"/> at a parameter use or
/// <see cref="KatLangErrorCode.LocalOnlyProperty"/> at a restricted read. A retained local alias
/// cell can still supply its earlier value, as the R-1 tests below demonstrate.
/// (WHERE a value lives is a separate question since the inner-property
/// lifetime rule of the same month: every actual call of an owner has fresh bindings for its inner
/// properties, exported ones included, and a read from outside every call has the separate
/// run-scoped binding — <c>InnerPropertyLifetimeTests</c>. Exposure still decides accessibility and
/// detachment, which is what this class pins.)
/// <para>The subject is the EVALUATOR law, so the trees are MIS-EXPOSED on purpose and independent
/// of which front-end routes classify correctly: a source program is parsed cleanly, the front end's
/// (correct) local-only verdict on one property is asserted, and that one property is then forced to
/// <c>Exported</c> — the tree a wrong exposure analysis, or a host, would hand the evaluator
/// (<see cref="MisExposed"/>). Every case runs on the optimized synchronous route, the generic
/// synchronous route and the async twin family. <see cref="WithoutDetachment_TheSameTreesAreNotRefused"/>
/// is the MUTATION GUARD: under <see cref="DetachedEvaluationTestSeam"/> none of the same trees is
/// refused, and one of them serves a first call's value to the next, so the refusal tests cannot pass
/// without detachment. The neutrality pins at the end hold correctly classified programs to their
/// exact values.</para>
/// </summary>
public class DetachedExportedEvaluationTests
{
    public enum Route
    {
        /// <summary>Synchronous, loop and sequence optimizers on (the engine's strategies).</summary>
        Optimized,

        /// <summary>Synchronous, both optimizers off.</summary>
        Generic,

        /// <summary>The async twin family over an async-capable run cache.</summary>
        AsyncTwin,
    }

    public static TheoryData<Route> Routes() => [Route.Optimized, Route.Generic, Route.AsyncTwin];

    // ── Mis-exposed programs ───────────────────────────────────────────────────────────────────

    /// <summary><c>P</c> reads the parameter of the call around it.</summary>
    private const string EnclosingRead = """
        F(y) = {
          P = y * 10
          P
        }

        """;

    /// <summary><c>P</c> navigates the local-only member <c>Q</c> of <c>Box</c> through a structural step.</summary>
    private const string StructuralStep = """
        F(y) = {
          Box = { public Q = y * 10 }
          P = Box.Q + 0
          P
        }

        """;

    /// <summary><c>P</c> reaches the same local-only member through an <c>open</c>.</summary>
    private const string OpenedStep = """
        F(y) = {
          open Box
          Box = { public Q = y * 10 }
          P = Q + 0
          P
        }

        """;

    /// <summary>The audit's <c>r2</c> shape: <c>P</c> captures a call that reads <c>y</c> only when invoked later.</summary>
    private const string Closure = """
        Cap(meta r) = r
        Inc(x) = x + 1
        F(y) = {
          P = Cap(Inc(y))
          B = P.Invoke() + 0
          B
        }

        """;

    /// <summary>An explicit zero-supply invocation <c>P()</c> beside a read of the same property.</summary>
    private const string ExplicitCall = """
        F(y) = {
          P = y * 10
          P() + P
        }

        """;

    /// <summary><c>P</c> reads the local-only <c>L</c>, whose entry the row has already established: a HIT.</summary>
    private const string LocalOnlyHit = """
        F(y) = {
          L = y * 10
          P = L + 1
          L + P
        }

        """;

    /// <summary>A loop step whose temp reads the loop state.</summary>
    private const string LoopTemp = """
        Step(s) = {
          T = s + 1
          T
        }

        """;

    /// <summary>A runtime alias whose row depends on the enclosing parameter.</summary>
    private const string RuntimeAlias = """
        Cap(meta r) = r
        Inc(x) = x + 1
        Dbl(x) = x * 2
        Sel(k) = if(k > 1, Cap(Dbl(0)), Cap(Inc(0)))
        F(y) = {
          A = Sel(y).Algorithm
          A(5)
        }

        """;

    /// <summary>The audit's <c>d2</c> shape, host-side: a member reached by navigation from outside its owner's call.</summary>
    private const string StaticOwner = """
        G(y) = {
          F(n) = y * n
          0
        }
        H(y) = G.F(1)

        """;

    /// <summary><c>P</c> INVOKES the parameter of the call around it (the review's callee witness).</summary>
    private const string CalleeRead = """
        Inc(n) = n + 1
        F(y) = {
          P = y(5) + 0
          P
        }

        """;

    /// <summary><c>P</c> only TRANSPORTS the parameter: the receiving callee ignores it (the review's transport witness).</summary>
    private const string IgnoredTransport = """
        Ignore(z) = 42
        F(y) = {
          P = Ignore(y) + 0
          P
        }

        """;

    /// <summary>The static-owner shape whose navigated member INVOKES the owner's parameter.</summary>
    private const string StaticOwnerCallee = """
        Inc(n) = n + 1
        G(y) = {
          F(n) = y(n)
          0
        }
        H(y) = G.F(1)

        """;

    /// <summary>The static-owner shape whose navigated member only TRANSPORTS the owner's parameter.</summary>
    private const string StaticOwnerTransport = """
        Ignore(z) = 42
        G(y) = {
          F(n) = Ignore(y) + n
          0
        }
        H(y) = G.F(1)

        """;

    // ── 1. An enclosing-parameter read ─────────────────────────────────────────────────────────

    [Theory]
    [MemberData(nameof(Routes))]
    public async Task EnclosingParameterRead_IsUnknownName_ForOneCall(Route route)
    {
        var result = await Run(MisExposed(EnclosingRead + "F(1)\n", "F.P"), route);

        var unknown = Assert.IsType<EvalError.UnknownName>(EvaluatorTestSupport.Innermost(result.Error));
        Assert.Equal("y", unknown.Name);
    }

    [Theory]
    [MemberData(nameof(Routes))]
    public async Task EnclosingParameterRead_IsUnknownName_ForTwoCalls_NeverTheFirstCallsValueTwice(Route route)
        => Assert.Equal("err unknownName", await Observe(MisExposed(EnclosingRead + "F(1), F(2)\n", "F.P"), route));

    [Fact]
    public async Task EnclosingParameterRead_SaysThatTheNameIsAnInputOfTheEnclosingCall()
    {
        var result = await Run(MisExposed(EnclosingRead + "F(1)\n", "F.P"), Route.Generic);

        Assert.True(result.IsError);
        Assert.Equal(KatLangErrorCode.UnknownName, KatLangError.FromEvalError(result.Error).Code);
        Assert.Contains(Evaluator.DetachedParameterMessage("y"), KatLangError.FromEvalError(result.Error).Message, StringComparison.Ordinal);
        Assert.Contains(Contexts(result.Error), context
            => context is TextErrorContext text && text.Message == Evaluator.DetachedParameterMessage("y"));
    }

    // ── 2. A local-only structural step, in both row orders ────────────────────────────────────

    [Theory]
    [MemberData(nameof(Routes))]
    public async Task LocalOnlyStructuralStep_IsLocalOnlyProperty_WhenTheOwnersCallComesFirst(Route route)
        => Assert.Equal("err localOnlyProperty", await Observe(MisExposed(StructuralStep + "F(1), F.P\n", "F.P"), route));

    [Theory]
    [MemberData(nameof(Routes))]
    public async Task LocalOnlyStructuralStep_IsLocalOnlyProperty_WhenTheOutsideReadComesFirst(Route route)
        => Assert.Equal("err localOnlyProperty", await Observe(MisExposed(StructuralStep + "F.P, F(1)\n", "F.P"), route));

    [Theory]
    [MemberData(nameof(Routes))]
    public async Task LocalOnlyOpenedMember_IsLocalOnlyProperty_InBothRowOrders(Route route)
    {
        Assert.Equal("err localOnlyProperty", await Observe(MisExposed(OpenedStep + "F(1), F.P\n", "F.P"), route));
        Assert.Equal("err localOnlyProperty", await Observe(MisExposed(OpenedStep + "F.P, F(1)\n", "F.P"), route));
    }

    [Theory]
    [MemberData(nameof(Routes))]
    public async Task LocalOnlyStructuralStep_NamesTheRefusedMember(Route route)
    {
        var result = await Run(MisExposed(StructuralStep + "F(1), F.P\n", "F.P"), route);

        var refused = Assert.IsType<EvalError.LocalOnlyProperty>(EvaluatorTestSupport.Innermost(result.Error));
        Assert.Equal("Q", refused.PropertyName);
        Assert.Equal(PropertyExposure.LocalOnlyCapturedAncestorParameters, refused.Exposure);
    }

    // ── 3. The closure shape, an explicit call, a local-only hit, an alias row ─────────────────

    [Theory]
    [MemberData(nameof(Routes))]
    public async Task ClosureCreatedDetached_StaysDetached_WhenItIsInvokedLater(Route route)
    {
        var result = await Run(MisExposed(Closure + "F(1), F(2)\n", "F.P"), route);

        // P's own evaluation reads nothing (a capture is inert); the refusal comes from the later
        // Invoke, which runs the captured call in the context it was captured in.
        var unknown = Assert.IsType<EvalError.UnknownName>(EvaluatorTestSupport.Innermost(result.Error));
        Assert.Equal("y", unknown.Name);
    }

    [Theory]
    [MemberData(nameof(Routes))]
    public async Task ExplicitZeroSupplyInvocation_IsRefused(Route route)
        => Assert.Equal("err unknownName", await Observe(MisExposed(ExplicitCall + "F(1), F(2)\n", "F.P"), route));

    [Theory]
    [MemberData(nameof(Routes))]
    public async Task ExplicitZeroSupplyInvocation_IsRefused_WithRetainedInvocationPlans(Route route)
    {
        using var plans = InvocationPlanTestSeam.Activate(new InvocationPlanTestSeam());

        Assert.Equal("err unknownName", await Observe(MisExposed(ExplicitCall + "F(1), F(2)\n", "F.P"), route));
    }

    [Theory]
    [MemberData(nameof(Routes))]
    public async Task LocalOnlyRead_IsRefused_EvenWhenItsEntryIsAlreadyEstablished(Route route)
    {
        var result = await Run(MisExposed(LocalOnlyHit + "F(1), F(2)\n", "F.P"), route);

        // `L + P` reads L first, so L's entry for this call exists when P's detached evaluation reads
        // it: the refusal runs before the cache is consulted.
        var refused = Assert.IsType<EvalError.LocalOnlyProperty>(EvaluatorTestSupport.Innermost(result.Error));
        Assert.Equal("L", refused.PropertyName);
    }

    [Theory]
    [MemberData(nameof(Routes))]
    public async Task ExportedRuntimeAliasRow_IsSuppliedDetached(Route route)
        => Assert.Equal("err unknownName", await Observe(MisExposed(RuntimeAlias + "F(1), F(2)\n", "F.A"), route));

    // ── 4. Planned and generic loop strategies agree ───────────────────────────────────────────

    [Fact]
    public void PlannedAndGenericLoopStrategies_RefuseTheSameRead()
    {
        var program = MisExposed(LoopTemp + "Step(0).repeat(3)\n", "Step.T");
        var diagnostics = new LoopOptimizationDiagnostics();

        var planned = Evaluator.RunCountedObserved(program, loopDiagnostics: diagnostics).Result;
        var generic = Evaluator.RunCountedObserved(program, enableOptimizations: false).Result;

        Assert.Equal("err unknownName", AsyncEvaluationHarness.NeutralOf(planned));
        Assert.Equal("err unknownName", AsyncEvaluationHarness.NeutralOf(generic));
        Assert.Equal("s", Assert.IsType<EvalError.UnknownName>(EvaluatorTestSupport.Innermost(planned.Error)).Name);
        Assert.Equal("s", Assert.IsType<EvalError.UnknownName>(EvaluatorTestSupport.Innermost(generic.Error)).Name);
        DifferentialErrors.RequireAgreement("detached-loop", planned.Error, generic.Error);
        // The planner met the temp and left it to the generic strategy, for the stated reason.
        Assert.True(diagnostics.FallbackReasons.ContainsKey(LoopOptimizer.ExportedTempInputFallbackReason));
    }

    [Fact]
    public async Task LoopTemp_IsRefused_OnTheAsyncTwin()
        => Assert.Equal("err unknownName", await Observe(MisExposed(LoopTemp + "Step(0).repeat(3)\n", "Step.T"), Route.AsyncTwin));

    [Fact]
    public void CorrectlyExportedLoopTemp_StaysPlanned()
    {
        var diagnostics = new LoopOptimizationDiagnostics();
        var program = new Expr.AlgorithmExpr(SourceProvenance.ParseValid("""
            Step(s) = {
              T = 5
              s + T
            }
            Step(0).repeat(3)
            """).Root);

        var planned = Evaluator.RunCountedObserved(program, loopDiagnostics: diagnostics).Result;

        Assert.Equal("ok raw=15 n=1", AsyncEvaluationHarness.NeutralOf(planned));
        Assert.False(diagnostics.FallbackReasons.ContainsKey(LoopOptimizer.ExportedTempInputFallbackReason));
        Assert.Equal(1, diagnostics.OptimizedLoopHits);
    }

    // ── 5. Lexical-only reads: a static owner never answers with a caller's binding ────────────

    [Theory]
    [MemberData(nameof(Routes))]
    public async Task StaticOwnerRead_IsUnknownName_NeverTheCallersBindingOfTheSameName(Route route)
    {
        // Formerly 3: G's `y` was read from H's dynamically live `y`.
        var result = await Run(MisExposed(StaticOwner + "H(3)\n", "G.F"), route);

        var unknown = Assert.IsType<EvalError.UnknownName>(EvaluatorTestSupport.Innermost(result.Error));
        Assert.Equal("y", unknown.Name);
        // No exported evaluation is involved: this refusal is the lexical-only rule alone.
        Assert.DoesNotContain(Contexts(result.Error), context => context is TextErrorContext { Message: var message }
            && message == Evaluator.DetachedParameterMessage("y"));
    }

    [Theory]
    [MemberData(nameof(Routes))]
    public async Task StaticOwnerRead_IsUnknownName_WithOrWithoutDetachment(Route route)
    {
        using var attached = DetachedEvaluationTestSeam.DisableDetachment();

        Assert.Equal("err unknownName", await Observe(MisExposed(StaticOwner + "H(3)\n", "G.F"), route));
    }

    // ── 5b. Every executed operation on an unavailable parameter is refused ────────────────────
    //
    // The VALUE read is not the only operation on a written parameter. A parameter whose lexical
    // owner has no usable activation is refused where it is INVOKED (its CALLABLE projection: the
    // refusal names the parameter, never a missing callable capability) and where it is TRANSPORTED
    // as a supplied argument (while the supply is formed, whether or not the receiver demands it).

    /// <summary>The correctly classified programs: the supplied callable is invoked, the ignored argument is never demanded.</summary>
    [Theory]
    [MemberData(nameof(Routes))]
    public async Task CalleeAndTransportWitnesses_CorrectlyClassified_KeepTheirValues(Route route)
    {
        Assert.Equal("ok raw=6 n=1", await Observe(Parsed(CalleeRead + "F(Inc)\n"), route));
        Assert.Equal("ok raw=42 n=1", await Observe(Parsed(IgnoredTransport + "F(7)\n"), route));
        // Available cells transport LAZILY: the transported argument is never demanded, so its
        // failure is never observed.
        Assert.Equal("ok raw=42 n=1", await Observe(Parsed(IgnoredTransport + "F(1 / 0)\n"), route));
    }

    [Theory]
    [MemberData(nameof(Routes))]
    public async Task DetachedParameter_IsUnknownName_WhereItIsInvoked(Route route)
    {
        var (result, published) = await RunCountingPublications(MisExposed(CalleeRead + "F(Inc)\n", "F.P"), route);

        // Formerly NotAnAlgorithm, with a message claiming the supplied callable was a value.
        var unknown = Assert.IsType<EvalError.UnknownName>(EvaluatorTestSupport.Innermost(result.Error));
        Assert.Equal("y", unknown.Name);
        Assert.Equal(KatLangErrorCode.UnknownName, KatLangError.FromEvalError(result.Error).Code);
        Assert.Contains(Contexts(result.Error), context
            => context is TextErrorContext text && text.Message == Evaluator.DetachedParameterMessage("y"));
        // The refused owner publishes nothing.
        Assert.Equal(0, published);
    }

    [Theory]
    [MemberData(nameof(Routes))]
    public async Task DetachedParameter_IsUnknownName_WhereItIsTransported_AlthoughTheCalleeIgnoresIt(Route route)
    {
        var (result, published) = await RunCountingPublications(MisExposed(IgnoredTransport + "F(7)\n", "F.P"), route);

        // Formerly 42: the supply of `Ignore(y)` formed a fresh cell nothing ever demanded.
        var unknown = Assert.IsType<EvalError.UnknownName>(EvaluatorTestSupport.Innermost(result.Error));
        Assert.Equal("y", unknown.Name);
        Assert.Contains(Contexts(result.Error), context
            => context is TextErrorContext text && text.Message == Evaluator.DetachedParameterMessage("y"));
        Assert.Equal(0, published);
    }

    /// <summary>The positive controls publish the local-only entry the mutants never reach.</summary>
    [Theory]
    [MemberData(nameof(Routes))]
    public async Task CalleeAndTransportWitnesses_CorrectlyClassified_PublishTheirEntry(Route route)
    {
        var (callee, calleePublished) = await RunCountingPublications(Parsed(CalleeRead + "F(Inc)\n"), route);
        var (transport, transportPublished) = await RunCountingPublications(Parsed(IgnoredTransport + "F(7)\n"), route);

        Assert.Equal("ok raw=6 n=1", AsyncEvaluationHarness.NeutralOf(callee));
        Assert.Equal("ok raw=42 n=1", AsyncEvaluationHarness.NeutralOf(transport));
        Assert.Equal(1, calleePublished);
        Assert.Equal(1, transportPublished);
    }

    /// <summary>The refusals keep the WRITTEN occurrence: the span is the parameter's, in the property's row.</summary>
    [Theory]
    [InlineData(CalleeRead + "F(Inc)\n", 3, 7)]
    [InlineData(IgnoredTransport + "F(7)\n", 3, 14)]
    public async Task DetachedParameterRefusal_IsPositionedAtTheWrittenParameter(string source, int line, int column)
    {
        foreach (var route in new[] { Route.Optimized, Route.Generic, Route.AsyncTwin })
        {
            var result = await Run(MisExposed(source, "F.P"), route);

            var unknown = Assert.IsType<EvalError.UnknownName>(EvaluatorTestSupport.Innermost(result.Error));
            var span = Assert.NotNull(unknown.Span);
            Assert.Equal(line, span.Start.Line);
            Assert.Equal(column, span.Start.Column);
        }
    }

    /// <summary>The same two operations with retained invocation plans: the plan's callee cell and its supply refuse identically.</summary>
    [Theory]
    [MemberData(nameof(Routes))]
    public async Task DetachedParameter_IsRefused_WhereItIsInvokedOrTransported_WithRetainedInvocationPlans(Route route)
    {
        using var plans = InvocationPlanTestSeam.Activate(new InvocationPlanTestSeam());

        Assert.Equal("err unknownName", await Observe(MisExposed(CalleeRead + "F(Inc)\n", "F.P"), route));
        Assert.Equal("err unknownName", await Observe(MisExposed(IgnoredTransport + "F(7)\n", "F.P"), route));
        Assert.Equal("ok raw=6 n=1", await Observe(Parsed(CalleeRead + "F(Inc)\n"), route));
        Assert.Equal("ok raw=42 n=1", await Observe(Parsed(IgnoredTransport + "F(7)\n"), route));
    }

    /// <summary>
    /// A STATIC owner (no exported evaluation involved): the navigated member's parameter operations
    /// are refused by the lexical-only rule alone, and never answered by the caller's same-named binding.
    /// </summary>
    [Theory]
    [MemberData(nameof(Routes))]
    public async Task StaticOwnerParameter_IsUnknownName_WhereItIsInvokedOrTransported(Route route)
    {
        // Formerly 2 (H's `y`, the callable Inc) and 43 (H's `y` transported to Ignore).
        var invoked = await Run(MisExposed(StaticOwnerCallee + "H(Inc)\n", "G.F"), route);
        var transported = await Run(MisExposed(StaticOwnerTransport + "H(7)\n", "G.F"), route);

        foreach (var result in new[] { invoked, transported })
        {
            var unknown = Assert.IsType<EvalError.UnknownName>(EvaluatorTestSupport.Innermost(result.Error));
            Assert.Equal("y", unknown.Name);
            Assert.DoesNotContain(Contexts(result.Error), context => context is TextErrorContext { Message: var message }
                && message == Evaluator.DetachedParameterMessage("y"));
        }
    }

    /// <summary>
    /// The remaining operations on a written parameter occurrence, each through its own route of the
    /// evaluator: the dot-only <c>string</c> intrinsic's receiver, a spread of a collector, a
    /// transparent reference whose row is the parameter, a builtin's argument and callback slot, and
    /// an extension call's injected receiver. Each row: the source, the falsely exported property,
    /// the correctly classified value, and the unavailable parameter the refusal names.
    /// </summary>
    public static TheoryData<string, string, string, string> OtherParameterOperations() => new()
    {
        { "F(y) = {\n  P = y.string\n  P\n}\nF(7)\n", "F.P", "ok raw='7' n=1", "y" },
        { "G(a, b) = a + b\nF(*ys) = {\n  P = G(ys*)\n  P\n}\nF(1, 2)\n", "F.P", "ok raw=3 n=1", "ys" },
        { "F(y) = {\n  P = if(true, 1, y) + 0\n  P\n}\nF(7)\n", "F.P", "ok raw=1 n=1", "y" },
        { "Inc(n) = n + 1\nF(y) = {\n  P = [1, 2].map(y)\n  P\n}\nF(Inc)\n", "F.P", "ok raw=L[2, 3] n=1", "y" },
        { "Inc(n) = n + 1\nF(y) = {\n  P = y.Inc + 0\n  P\n}\nF(7)\n", "F.P", "ok raw=8 n=1", "y" },
        { "F(y) = {\n  P = y[0] + 0\n  P\n}\nF([4, 5])\n", "F.P", "ok raw=4 n=1", "y" },
    };

    [Theory]
    [InlineData("[5][99, y]", "err index")]
    [InlineData("[5][y, (1 / 0)*]", "err div0")]
    [InlineData("repeat(y(1), 0)", "ok raw=1 n=1")]
    [InlineData("repeat(y(1), 1 / 0)", "err div0")]
    public async Task SupplyFormsBeforeSelectorDemandOrRepeatCount(string expression, string declaredOutcome)
    {
        var source = $"F(y) = {{\n  P = {expression} + 0\n  P\n}}\nF(0)\n";
        var declared = Parsed(source);
        var detached = MisExposed(source, "F.P");

        foreach (var route in new[] { Route.Optimized, Route.Generic, Route.AsyncTwin })
        {
            Assert.Equal(declaredOutcome, await Observe(declared, route));
            var result = await Run(detached, route);
            Assert.True(result.IsError);
            var error = Assert.IsType<EvalError.UnknownName>(EvaluatorTestSupport.Innermost(result.Error));
            Assert.Equal("y", error.Name);
            Assert.Equal(source.Split('\n')[1].IndexOf('y') + 1, error.Span?.Start.Column);
        }
    }

    [Theory]
    [InlineData("[5][(1 / 0)*, y]")]
    [InlineData("repeat(y((1 / 0)*), 0)")]
    public async Task EarlierSpreadFailurePrecedesUnavailableParameterTransport(string expression)
    {
        var source = $"F(y) = {{\n  P = {expression} + 0\n  P\n}}\nF(0)\n";
        foreach (var route in new[] { Route.Optimized, Route.Generic, Route.AsyncTwin })
        {
            var result = await Run(MisExposed(source, "F.P"), route);
            Assert.IsType<EvalError.DivByZero>(EvaluatorTestSupport.Innermost(result.Error));
        }
    }

    [Theory]
    [MemberData(nameof(OtherParameterOperations))]
    public async Task EveryOtherParameterOperation_IsRefusedWhenUnavailable_AndUnchangedWhenAvailable(
        string source, string misExposed, string declaredValue, string parameter)
    {
        foreach (var route in new[] { Route.Optimized, Route.Generic, Route.AsyncTwin })
        {
            Assert.True(declaredValue == await Observe(Parsed(source), route),
                $"{route}: expected {declaredValue}, was {await Observe(Parsed(source), route)}\n{source}");

            var result = await Run(MisExposed(source, misExposed), route);
            Assert.True(result.IsError, $"{route}: the mis-exposed tree gave {AsyncEvaluationHarness.NeutralOf(result)}\n{source}");
            var unknown = Assert.IsType<EvalError.UnknownName>(EvaluatorTestSupport.Innermost(result.Error));
            Assert.Equal(parameter, unknown.Name);
        }
    }

    /// <summary>
    /// A TRANSPARENT REFERENCE whose row is the parameter (<c>A = y</c>) owns no entry and no cell of
    /// its own: its binding cell IS the parameter's cell, found from the reading context. Falsely
    /// exported, it therefore shares nothing across calls — a read inside a call is that call's own
    /// parameter — while a read from outside the owner, which the false flag makes accessible, is the
    /// refusal of the unavailable row.
    /// </summary>
    [Theory]
    [MemberData(nameof(Routes))]
    public async Task FalselyExportedParameterRowAlias_ReadsItsOwnCallInside_AndIsRefusedOutside(Route route)
    {
        const string source = "F(y) = {\n  A = y\n  A + 0\n}\n";

        Assert.Equal("ok raw=S[7, 9] n=2", await Observe(Parsed(source + "F(7), F(9)\n"), route));
        Assert.Equal("ok raw=S[7, 9] n=2", await Observe(MisExposed(source + "F(7), F(9)\n", "F.A"), route));

        var outside = await Run(MisExposed(source + "F(7), F.A\n", "F.A"), route);
        var unknown = Assert.IsType<EvalError.UnknownName>(EvaluatorTestSupport.Innermost(outside.Error));
        Assert.Equal("y", unknown.Name);
    }

    /// <summary>
    /// The mutation guard of the two operations: without detachment the mis-exposed trees answer with
    /// the reader's own bindings (the callable is invoked, the transported argument is ignored).
    /// </summary>
    [Theory]
    [MemberData(nameof(Routes))]
    public async Task WithoutDetachment_TheCalleeAndTransportWitnessesAnswerFromTheReader(Route route)
    {
        using var attached = DetachedEvaluationTestSeam.DisableDetachment();

        Assert.Equal("ok raw=6 n=1", await Observe(MisExposed(CalleeRead + "F(Inc)\n", "F.P"), route));
        Assert.Equal("ok raw=42 n=1", await Observe(MisExposed(IgnoredTransport + "F(7)\n", "F.P"), route));
    }

    /// <summary>
    /// AN AVAILABLE VALUE-ONLY CELL keeps the ordinary callable-capability error: the refusal of an
    /// unavailable parameter replaces nothing but the unavailable case.
    /// </summary>
    [Theory]
    [MemberData(nameof(Routes))]
    public async Task AvailableValueOnlyParameter_Invoked_IsStillNotAnAlgorithm(Route route)
    {
        var result = await Run(Parsed(CalleeRead + "F(7)\n"), route);

        Assert.IsType<EvalError.NotAnAlgorithm>(EvaluatorTestSupport.Innermost(result.Error));
    }

    /// <summary>
    /// AN ABSENT LEXICAL OWNER keeps the context lookup on every channel: a host-built free parameter,
    /// which no level of the reading chain binds, is invoked and transported through the reader's own
    /// tiers exactly as its VALUE is read.
    /// </summary>
    [Theory]
    [MemberData(nameof(Routes))]
    public async Task FreeParameter_WithNoLexicalOwner_StillUsesTheReadersTiers_OnEveryChannel(Route route)
    {
        static Expr Free(Expr body, Expr argument)
        {
            // A local-only host property on a level that names no parameter, read by G(x).
            var member = new Property("P", new Algorithm.User(null, [], [], [], new OutputBundle([body])),
                IsPublic: false, PropertyExposure.LocalOnlyCapturedAncestorParameters) { RequiredAncestorParameters = ["x"] };
            var reader = new Property("G", new Algorithm.User(null, [new CaptureParameterPattern("x")], [], [],
                new OutputBundle([new Expr.Resolve("P")])), IsPublic: true);
            var inc = new Property("Inc", new Algorithm.User(null, [new CaptureParameterPattern("n")], [], [],
                new OutputBundle([new Expr.Binary(BinaryOp.Add, new Expr.Param("n"), new Expr.Num(1))])), IsPublic: true);
            var ignore = new Property("Ignore", new Algorithm.User(null, [new CaptureParameterPattern("z")], [], [],
                new OutputBundle([new Expr.Num(42)])), IsPublic: true);
            return new Expr.AlgorithmExpr(new Algorithm.User(null, [], [], [member, reader, inc, ignore],
                new OutputBundle([new Expr.Call(new Expr.Resolve("G"), new OutputBundle([argument]))])));
        }

        var value = Free(new Expr.Param("x"), new Expr.Num(7));
        var invoked = Free(new Expr.Call(new Expr.Param("x"), new OutputBundle([new Expr.Num(5)])), new Expr.Resolve("Inc"));
        var transported = Free(new Expr.Call(new Expr.Resolve("Ignore"), new OutputBundle([new Expr.Param("x")])), new Expr.Num(7));

        Assert.Equal("ok raw=7 n=1", await Observe(value, route));
        Assert.Equal("ok raw=6 n=1", await Observe(invoked, route));
        Assert.Equal("ok raw=42 n=1", await Observe(transported, route));
    }

    // ── 5c. The known residual: a retained local runtime-alias cell (ledger row R-1, OPEN) ──────

    /// <summary>The independent review's retained-alias witness (review-8013526d, finding 6).</summary>
    private const string RetainedAlias = """
        Cap(meta r) = r
        Inc(n) = n + 1
        Dbl(n) = n * 2
        Sel(k) = if(k == 1, Cap(Inc(0)), Cap(Dbl(0)))
        F(y) = {
          A = Sel(y).Algorithm
          P = A(5) + 0
          A(5), P
        }

        """;

    /// <summary>The same sibling read by a callback of the row, after the attached read of the alias.</summary>
    private const string RetainedAliasThroughACallback = """
        Cap(meta r) = r
        Inc(n) = n + 1
        Dbl(n) = n * 2
        Sel(k) = if(k == 1, Cap(Inc(0)), Cap(Dbl(0)))
        F(y) = {
          A = Sel(y).Algorithm
          P = A(5) + 0
          A(5), [0].map{ n + P }[0]
        }

        """;

    /// <summary>
    /// THE DETACHMENT GUARANTEE IS NOT UNCONDITIONAL (R-1, open). The watermark blocks DIRECT access
    /// to a pre-existing input on the checked paths: a captured parameter operation, a local-only
    /// member access, a local-only property read. It does not record what a retained runtime-alias
    /// BINDING CELL depended on. Here the row reads the local alias <c>A</c> ATTACHED first, which
    /// establishes the call's cell from <c>Sel(y)</c>; the falsely exported sibling <c>P</c> then
    /// reuses that established cell from its detached evaluation — nothing it executes reads
    /// <c>y</c> — and is NOT REFUSED, although its value depends on the call's input.
    /// <para>What that costs changed with the inner-property lifetime rule. Until then <c>P</c>'s
    /// value was published run-wide and served to the second call: <c>(10, 6)</c> where the correctly
    /// classified program gives <c>(10, 10)</c> (the witness of the independent review, reproduced on
    /// all three routes at the detachment-only boundary of this follow-up). Now <c>P</c>'s binding
    /// belongs to the call that owns it, the same lifetime as the cell it reused, so the mis-exposed
    /// tree computes the declared value. The residual is the missing REFUSAL: a wrong
    /// <c>Exported</c> flag is not a deterministic refusal here (it is one in the other row order,
    /// <see cref="R1_WithoutAnEarlierAttachedRead_TheSiblingIsRefused"/>). This test PINS it so that
    /// closing R-1 (the dependence bit on retained alias cells, in both evaluators) is a visible
    /// change.</para>
    /// </summary>
    [Theory]
    [MemberData(nameof(Routes))]
    public async Task KnownResidual_R1_AFalselyExportedSiblingReusesAnEstablishedLocalAliasCell_AndIsNotRefused(Route route)
    {
        foreach (var source in new[] { RetainedAlias, RetainedAliasThroughACallback })
        {
            Assert.Equal("ok raw=S[S[6, 6], S[10, 10]] n=2", await Observe(Parsed(source + "F(1), F(2)\n"), route));

            Assert.Equal("ok raw=S[S[6, 6], S[10, 10]] n=2", await Observe(MisExposed(source + "F(1), F(2)\n", "F.P"), route));
        }
    }

    /// <summary>
    /// The same sibling when its detached evaluation is the FIRST use of the alias: establishing the
    /// cell supplies the row detached-side reads refuse, so the residual needs the earlier attached read.
    /// </summary>
    [Theory]
    [MemberData(nameof(Routes))]
    public async Task R1_WithoutAnEarlierAttachedRead_TheSiblingIsRefused(Route route)
    {
        var program = MisExposed(RetainedAlias.Replace("A(5), P", "P, A(5)", StringComparison.Ordinal) + "F(1), F(2)\n", "F.P");

        var result = await Run(program, route);

        Assert.True(result.IsError, AsyncEvaluationHarness.NeutralOf(result));
    }

    // ── 6. The mutation guard ──────────────────────────────────────────────────────────────────

    /// <summary>
    /// The retained-alias shape read through a RUN-SCOPED reader: <c>B</c>, declared outside <c>F</c>,
    /// reads <c>F.P</c>, the outside binding of the falsely exported sibling.
    /// </summary>
    private const string RunScopedReader = """
        Cap(meta r) = r
        Inc(n) = n + 1
        Dbl(n) = n * 2
        Sel(k) = if(k == 1, Cap(Inc(0)), Cap(Dbl(0)))
        F(y) = {
          A = Sel(y).Algorithm
          P = A(5) + 0
          A(5), B
        }
        B = F.P + 0

        """;

    public static TheoryData<string, string, string, string> AttachedOutcomes() => new()
    {
        { EnclosingRead + "F(1)\n", "F.P", "ok raw=10 n=1", "err unknownName" },
        { EnclosingRead + "F(1), F(2)\n", "F.P", "ok raw=S[10, 20] n=2", "err unknownName" },
        { StructuralStep + "F(1), F(2)\n", "F.P", "ok raw=S[10, 20] n=2", "err localOnlyProperty" },
        { OpenedStep + "F(1), F(2)\n", "F.P", "ok raw=S[10, 20] n=2", "err localOnlyProperty" },
        { Closure + "F(1), F(2)\n", "F.P", "ok raw=S[2, 3] n=2", "err unknownName" },
        { ExplicitCall + "F(1), F(2)\n", "F.P", "ok raw=S[20, 40] n=2", "err unknownName" },
        { LocalOnlyHit + "F(1), F(2)\n", "F.P", "ok raw=S[21, 41] n=2", "err localOnlyProperty" },
        { LoopTemp + "Step(0).repeat(3)\n", "Step.T", "ok raw=3 n=1", "err unknownName" },
        { RuntimeAlias + "F(1), F(2)\n", "F.A", "ok raw=S[6, 10] n=2", "err unknownName" },
        // THE WRONG SHARED VALUE detachment still prevents: the second call is served the first call's 6.
        { RunScopedReader + "F(1), F(2)\n", "F.P", "ok raw=S[S[6, 6], S[10, 6]] n=2", "err unknownName" },
    };

    /// <summary>
    /// THE MUTATION GUARD. With detachment disabled NONE of the mis-exposed trees is refused: each
    /// evaluates attached to the call that reads it, so this test and the refusal tests above cannot
    /// both pass unless detachment is what produces the refusal.
    /// <para>What the attached trees compute changed with the inner-property lifetime rule. An inner
    /// property's binding now belongs to its owning call, so the first nine rows compute what the
    /// correctly classified program computes (<see cref="CorrectlyClassified_TheSameProgramsKeepTheirIntendedValues"/>;
    /// before that rule each published the first call's value run-wide and served it to the next
    /// call: <c>(10, 10)</c>, <c>(2, 2)</c>, <c>(20, 30)</c>, <c>(21, 31)</c>, <c>1</c>,
    /// <c>(6, 6)</c>). The last row is the wrong shared value that remains reachable without
    /// detachment: the run-scoped reader <c>B</c> establishes the OUTSIDE binding of <c>F.P</c> from
    /// inside the first call, through that call's retained alias cell, and <c>B</c>'s run-scoped
    /// value is served to the second call — <c>(10, 6)</c>. The correctly classified program refuses
    /// that read (<c>B</c> reads a local-only member from outside its owner).</para>
    /// </summary>
    [Theory]
    [MemberData(nameof(AttachedOutcomes))]
    public async Task WithoutDetachment_TheSameTreesAreNotRefused(string source, string misExposed, string attachedValue, string refusal)
    {
        foreach (var route in new[] { Route.Optimized, Route.Generic, Route.AsyncTwin })
        {
            string attached;
            using (DetachedEvaluationTestSeam.DisableDetachment())
                attached = await Observe(MisExposed(source, misExposed), route);

            Assert.Equal(attachedValue, attached);
            Assert.Equal(refusal, await Observe(MisExposed(source, misExposed), route));
        }
    }

    /// <summary>The run-scoped reader's program, correctly classified: the read from outside the owner is refused.</summary>
    [Theory]
    [MemberData(nameof(Routes))]
    public async Task RunScopedReader_CorrectlyClassified_IsRefusedAtTheLocalOnlyMember(Route route)
        => Assert.Equal("err localOnlyProperty", await Observe(Parsed(RunScopedReader + "F(1), F(2)\n"), route));

    /// <summary>
    /// A READ FROM OUTSIDE THE OWNER'S CALL needs no detachment to be refused: since the
    /// inner-property lifetime rule the outside binding is separate from every call's, so a call's
    /// value is never served to it, and its own evaluation finds no activation of the owner. (Until
    /// that rule, with detachment disabled, the first call's value was published run-wide and the
    /// structural and opened rows returned <c>(10, 10)</c>.)
    /// </summary>
    [Theory]
    [InlineData(EnclosingRead + "F(1), F.P\n", "F.P", "err unknownName")]
    [InlineData(StructuralStep + "F(1), F.P\n", "F.P", "err localOnlyProperty")]
    [InlineData(OpenedStep + "F(1), F.P\n", "F.P", "err localOnlyProperty")]
    [InlineData(RuntimeAlias + "F(1), F.A(5)\n", "F.A", "err unknownName")]
    public async Task OutsideRead_IsRefused_WithAndWithoutDetachment(string source, string misExposed, string refusal)
    {
        foreach (var route in new[] { Route.Optimized, Route.Generic, Route.AsyncTwin })
        {
            string attached;
            using (DetachedEvaluationTestSeam.DisableDetachment())
                attached = await Observe(MisExposed(source, misExposed), route);

            Assert.Equal(refusal, attached);
            Assert.Equal(refusal, await Observe(MisExposed(source, misExposed), route));
        }
    }

    /// <summary>The intended values of the same programs, correctly classified: detachment changes none of them.</summary>
    [Theory]
    [InlineData(EnclosingRead + "F(1), F(2)\n", "ok raw=S[10, 20] n=2")]
    [InlineData(StructuralStep + "F(1), F(2)\n", "ok raw=S[10, 20] n=2")]
    [InlineData(OpenedStep + "F(1), F(2)\n", "ok raw=S[10, 20] n=2")]
    [InlineData(Closure + "F(1), F(2)\n", "ok raw=S[2, 3] n=2")]
    [InlineData(ExplicitCall + "F(1), F(2)\n", "ok raw=S[20, 40] n=2")]
    [InlineData(LocalOnlyHit + "F(1), F(2)\n", "ok raw=S[21, 41] n=2")]
    [InlineData(LoopTemp + "Step(0).repeat(3)\n", "ok raw=3 n=1")]
    [InlineData(RuntimeAlias + "F(1), F(2)\n", "ok raw=S[6, 10] n=2")]
    public async Task CorrectlyClassified_TheSameProgramsKeepTheirIntendedValues(string source, string expected)
    {
        var program = new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root);

        foreach (var route in new[] { Route.Optimized, Route.Generic, Route.AsyncTwin })
            Assert.Equal(expected, await Observe(program, route));
    }

    // ── 7. Neutrality pins: correctly classified programs, exact values ────────────────────────

    /// <summary>
    /// The audit's neutrality probes: detachment changes nothing of a correctly classified program
    /// (<see cref="NeutralityPin_ChargesWhatAnAttachedRunCharges"/> compares each with its attached
    /// run). <c>n1</c>, <c>n2</c>, <c>b2</c> and <c>l1</c> hold the values <c>main</c> had before
    /// EXPORTED-DETACHED. <c>h3</c>, <c>n3</c> and <c>b1</c> hold the values of the inner-property
    /// lifetime rule, the second delta of the follow-up: every call of <c>F</c> has fresh bindings,
    /// so <c>T</c> ticks in each call (<c>(2, 4)</c>; <c>(3, 5, 4)</c> with the separate outside
    /// binding of <c>F.P</c>) and the exported alias <c>A</c> has one binding cell per call, whose
    /// receiver ticks again in the second (<c>((3, 2, 2), (4, 2, 4))</c>). At the detachment-only
    /// boundary of that follow-up — one run-wide entry and one run-wide cell — they were
    /// <c>(2, 3)</c>, <c>(3, 4, 2)</c> and <c>((3, 2, 2), (4, 2, 3))</c>, unchanged from <c>main</c>.
    /// </summary>
    public static TheoryData<string, string, string> NeutralityPins() => new()
    {
        { "h3", "F(x) = {\n  T = tick()\n  T + x\n}\nF(1), F(2)\n", "ok raw=S[2, 4] n=2" },
        { "n1", "F(y) = {\n  Box = { public Q = 1\n    y }\n  P = Box.Q + 0\n  P\n}\nF.P\n", "ok raw=1 n=1" },
        { "n2", "F(y) = {\n  Box = { public Q = 1\n    y }\n  P = Box.Q + 0\n  P\n}\nF(1), F.P\n", "ok raw=S[1, 1] n=2" },
        { "n3", "F(y) = {\n  T = tick()\n  P = T + 1\n  P + y\n}\nF(1), F(2), F.P\n", "ok raw=S[3, 5, 4] n=3" },
        {
            "b1",
            "Cap(meta r) = if(tick() > 0, r, r)\nInc(x) = x + 1\nF(y) = {\n  A = Cap(Inc(5)).Algorithm\n  P = A(1) + 0\n  P + y, A(1), tick()\n}\nF(1), F(2)\n",
            "ok raw=S[S[3, 2, 2], S[4, 2, 4]] n=2"
        },
        {
            "b2",
            "Cap(meta r) = if(tick() > 0, r, r)\nInc(x) = x + 1\nF(y) = {\n  A = Cap(Inc(5)).Algorithm\n  P = A(1) + 0\n  P + y\n}\nF.P\n",
            "ok raw=2 n=1"
        },
        { "l1", "Step(a, n) = { { a * 2 }, n + 1 }\nStep(1, 0).repeat(3)\n", "ok raw=S[8, 3] n=1" },
    };

    [Theory]
    [MemberData(nameof(NeutralityPins))]
    public async Task NeutralityPin_KeepsItsExactValue_OnEveryRoute(string name, string source, string expected)
    {
        var program = new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root);

        foreach (var route in new[] { Route.Optimized, Route.Generic, Route.AsyncTwin })
            Assert.True(expected == await Observe(program, route), $"{name} on {route}: expected {expected}, was {await Observe(program, route)}");

        Assert.Equal(expected.Replace(" n=", "|", StringComparison.Ordinal).Split('|')[0],
            AsyncEvaluationHarness.NeutralOf(KatLangEngineValue(source)));
    }

    /// <summary>
    /// A neutrality pin's charges are the ones a run without detachment makes (I2): the same steps,
    /// depth, materialized items and tick count, on the generic route where every read is charged.
    /// </summary>
    [Theory]
    [MemberData(nameof(NeutralityPins))]
    public void NeutralityPin_ChargesWhatAnAttachedRunCharges(string name, string source, string expected)
    {
        var program = new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root);

        var (detached, detachedBudget) = Evaluator.RunCountedObserved(program, enableOptimizations: false);
        EvalResult<Evaluator.CountedResult> attached;
        EvaluationBudget attachedBudget;
        using (DetachedEvaluationTestSeam.DisableDetachment())
            (attached, attachedBudget) = Evaluator.RunCountedObserved(program, enableOptimizations: false);

        Assert.True(expected == AsyncEvaluationHarness.NeutralOf(detached), name);
        Assert.Equal(AsyncEvaluationHarness.NeutralOf(attached), AsyncEvaluationHarness.NeutralOf(detached));
        Assert.Equal(attachedBudget.ConsumedSteps, detachedBudget.ConsumedSteps);
        Assert.Equal(attachedBudget.PeakDepth, detachedBudget.PeakDepth);
        Assert.Equal(attachedBudget.MaterializedItems, detachedBudget.MaterializedItems);
        Assert.Equal(attachedBudget.TickCount, detachedBudget.TickCount);
    }

    // ── 8. The watermark carrier ───────────────────────────────────────────────────────────────

    [Fact]
    public void Watermark_IsZeroOutsideEveryExportedEvaluation_AndInheritedByEveryDerivedContext()
    {
        var algorithm = new Algorithm.User(null, [], [], [], OutputBundle.Empty);
        var root = Evaluator.EvalCtx.Empty;

        Assert.Equal(0, root.DetachedBefore);
        Assert.Equal(0, root.Push(algorithm).DetachedBefore);

        var detached = root.Push(algorithm).Detach(7);
        Assert.Equal(7, detached.DetachedBefore);
        Assert.Empty(detached.NeedEnv);
        Assert.Same(algorithm, detached.Head);
        Assert.Single(detached.CallStack);

        // A pushed head, and a head pushed above it, carry the watermark.
        var pushed = detached.Push(algorithm).Push(algorithm);
        Assert.Equal(7, pushed.DetachedBefore);
        Assert.Equal(3, pushed.CallStack.Count);
        Assert.All(pushed.CallStack, level => Assert.Same(algorithm, level));

        // A nested detachment never lowers the watermark and may raise it.
        Assert.Equal(7, pushed.Detach(3).DetachedBefore);
        Assert.Equal(9, pushed.Detach(9).DetachedBefore);
        Assert.Equal(9, detached.Detach(8).Detach(9).Detach(2).DetachedBefore);
        Assert.Single(detached.Detach(8).Detach(9).CallStack);
    }

    [Fact]
    public void DetachedEvaluation_KeepsTheReadersBindingIdentity_AndItsInputsOnly()
    {
        var root = Evaluator.EvalCtx.Empty;
        IReadOnlyList<(string Name, Result Value)> readerValues = [("x", new Result.Atom(1))];

        var detached = Evaluator.DetachedEvaluation(root, readerValues, out var values);

        Assert.Empty(values);
        Assert.NotEqual(0, detached.DetachedBefore);
        Assert.Same(Evaluator.BindingContextIdentity(root, readerValues), Evaluator.BindingContextIdentity(detached, values));
    }

    // ── Harness ────────────────────────────────────────────────────────────────────────────────

    /// <summary>
    /// Parses <paramref name="source"/> cleanly and forces each property named by a dotted declaration
    /// path (<c>"F.P"</c>) to <see cref="PropertyExposure.Exported"/>. The front end's own verdict on it
    /// must be local-only: the test breaks a CORRECT classification, it does not rely on a wrong one.
    /// </summary>
    private static Expr MisExposed(string source, params string[] paths)
    {
        Algorithm root = SourceProvenance.ParseValid(source).Root;
        foreach (var path in paths)
            root = Export(root, path.Split('.'), 0);
        return new Expr.AlgorithmExpr(root);
    }

    private static Algorithm Export(Algorithm algorithm, string[] path, int depth)
    {
        var owner = Assert.IsType<Algorithm.User>(algorithm);
        var properties = owner.Properties.ToList();
        var index = properties.FindIndex(property => property.Name == path[depth]);
        Assert.True(index >= 0, $"No property '{path[depth]}' on the path {string.Join('.', path)}.");

        var selected = properties[index];
        if (depth < path.Length - 1)
        {
            properties[index] = selected with { Value = Export(selected.Value, path, depth + 1) };
        }
        else
        {
            Assert.Equal(PropertyExposure.LocalOnlyCapturedAncestorParameters, selected.Exposure);
            properties[index] = selected with
            {
                Exposure = PropertyExposure.Exported,
                RequiredAncestorParameters = [],
                CaptureRequirements = null,
            };
        }

        return owner with { Properties = properties };
    }

    private static Expr Parsed(string source) => new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root);

    /// <summary>
    /// Runs <paramref name="program"/> on <paramref name="route"/> over a run cache the test owns and
    /// returns the outcome with the number of entries the run PUBLISHED.
    /// </summary>
    private static async Task<(EvalResult<Evaluator.CountedResult> Result, int Published)> RunCountingPublications(Expr program, Route route)
    {
        if (route == Route.AsyncTwin)
        {
            var asyncCache = new RunScopedAsyncZeroArgPropertyResultCache();
            var asyncResult = (await AsyncEvaluationHarness.Complete(Evaluator.RunCountedObservedAsync(
                program, zeroArgPropertyResultCache: asyncCache))).Result;
            return (asyncResult, asyncCache.PublishedCount);
        }

        var cache = new RunScopedZeroArgPropertyResultCache();
        var result = Evaluator.RunCountedObserved(program, enableOptimizations: route == Route.Optimized, zeroArgPropertyResultCache: cache).Result;
        return (result, cache.GetSnapshot().Stores);
    }

    private static IEnumerable<ErrorContext> Contexts(EvalError error)
    {
        for (var current = error; current is EvalError.WithContext wrapped; current = wrapped.Inner)
            yield return wrapped.ErrorContext;
    }

    private static async Task<string> Observe(Expr program, Route route)
        => AsyncEvaluationHarness.NeutralOf(await Run(program, route));

    private static async Task<EvalResult<Evaluator.CountedResult>> Run(Expr program, Route route)
        => route switch
        {
            Route.Optimized => Evaluator.RunCountedObserved(program).Result,
            Route.Generic => Evaluator.RunCountedObserved(program, enableOptimizations: false).Result,
            Route.AsyncTwin => (await AsyncEvaluationHarness.Complete(Evaluator.RunCountedObservedAsync(
                program, zeroArgPropertyResultCache: new RunScopedAsyncZeroArgPropertyResultCache()))).Result,
            _ => throw new ArgumentOutOfRangeException(nameof(route)),
        };

    // The public engine's value for a source program (the route users run).
    private static EvalResult<Result> KatLangEngineValue(string source)
    {
        var run = Assert.IsType<RunResult.Success>(KatLangEngine.Run(source));
        return EvalResult<Result>.Ok(run.Value);
    }
}
