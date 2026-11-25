using System.Globalization;
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
/// <see cref="KatLangErrorCode.LocalOnlyProperty"/> at a restricted read, and the reuse of a retained
/// runtime-alias cell known to have read an input of a detached activation is refused before its channel
/// runs, with the alias's own <see cref="KatLangErrorCode.LocalOnlyProperty"/> (ledger R-1, qualified,
/// November 2026: section 5c).
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

    // ── 5c. Retained runtime-alias cells (ledger row R-1) ───────────────────────────────────────

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

    /// <summary>The value route: a parameter-rooted path alias, read bare (<c>P</c>) after an attached bare read.</summary>
    private const string RetainedPathValue = """
        G(v) = v + 1
        F(y) = {
          A = y.G
          P = A + 0
          A + 0, P
        }

        """;

    /// <summary>The value view: a zero-supply call of the value-only path alias, after an attached one.</summary>
    private const string RetainedValueView = """
        G(v) = v + 1
        F(y) = {
          A = y.G
          P = A() + 0
          A(), P
        }

        """;

    /// <summary>
    /// One cell, two channels (a callable link over zero-parameter callees): <c>{0}</c> is the attached
    /// row that warms ONE channel, <c>{1}</c> the falsely exported sibling that reads the OTHER — a cold
    /// channel of a warm cell.
    /// </summary>
    private const string RetainedChannels = """
        Cap(meta r) = r
        One(*xs) = 1
        Two(*xs) = 2
        Sel2(k) = if(k == 1, Cap(One()), Cap(Two()))
        F(y) = {{
          A = Sel2(y).Algorithm
          P = {1} + 0
          {0}, P
        }}

        """;

    /// <summary>The cell's receiver is a local-only property whose entry the row established first: the read is a HIT.</summary>
    private const string RetainedLocalOnlyHit = """
        Cap(meta r) = r
        Inc(n) = n + 1
        Dbl(n) = n * 2
        Sel(k) = if(k == 1, Cap(Inc(0)), Cap(Dbl(0)))
        F(y) = {
          L = Sel(y)
          A = L.Algorithm
          P = A(5) + 0
          L.Algorithm(5), A(5), P
        }

        """;

    /// <summary>A cell whose computation REUSES another retained cell (<c>B</c>) — the dependence passes on.</summary>
    private const string RetainedNested = """
        Cap(meta r) = r
        Inc(n) = n + 1
        Dbl(n) = n * 2
        Sel(k) = if(k == 1, Cap(Inc(0)), Cap(Dbl(0)))
        F(y) = {
          B = Sel(y).Algorithm
          A = Cap(B(0)).Algorithm
          P = A(5) + 0
          B(5), A(5), P
        }

        """;

    /// <summary>The falsely exported sibling reaches the cell through a helper's parameter.</summary>
    private const string RetainedThroughAHelper = """
        Cap(meta r) = r
        Inc(n) = n + 1
        Dbl(n) = n * 2
        Sel(k) = if(k == 1, Cap(Inc(0)), Cap(Dbl(0)))
        Use(f) = f(5)
        F(y) = {
          A = Sel(y).Algorithm
          P = Use(A) + 0
          A(5), P
        }

        """;

    /// <summary>
    /// CONTROL — an INDEPENDENT local-only alias: its row is local-only (it mentions <c>y</c>) but its
    /// computation never reads <c>y</c>, so the record holds no read and the falsely exported sibling
    /// shares the cell: the same value, the same ticks, the same cells.
    /// </summary>
    private const string IndependentLocalAlias = """
        Cap(meta r) = if(tick() > 0, r, r)
        Inc(n) = n + 1
        Dbl(n) = n * 2
        F(y) = {
          A = if(true, Cap(Inc(0)), Cap(Dbl(y))).Algorithm
          P = A(5) + 0
          A(5), P, tick()
        }

        """;

    /// <summary>
    /// CONTROL — a FRESHLY OWNED binding: the correctly exported <c>P</c> calls <c>G</c>, whose local-only
    /// alias cell reads <c>G</c>'s own parameter. The cell is established inside <c>P</c>'s detached
    /// evaluation and reused there: the activation it read through is <c>P</c>'s own, never detached.
    /// </summary>
    private const string FreshlyOwnedAlias = """
        Cap(meta r) = if(tick() > 0, r, r)
        Inc(n) = n + 1
        Dbl(n) = n * 2
        Sel(k) = if(k == 1, Cap(Inc(0)), Cap(Dbl(0)))
        G(z) = {
          A = Sel(z).Algorithm
          A(5) + A(5)
        }
        F(y) = {
          P = G(1) + 0
          P + y, tick()
        }

        """;

    /// <summary>
    /// DEFERRED READS: the cell's VALUE (the zero-supply call of the link's callee <c>Z</c>) is a lazy
    /// list built in the cell's own computation, whose positions read <c>y</c> only when they are read.
    /// The attached row establishes the cell and reads its count — no position, so no read of <c>y</c>
    /// yet — and the falsely exported sibling then reads a position.
    /// </summary>
    private const string RetainedLazyValue = """
        Cap(meta r) = r
        F(y) = {
          Mk(v) = {
            Z(*xs) = [1, 2].map{ n + y }
            Cap(Z())
          }
          A = Mk(5).Algorithm
          P = A[0] + 0
          A.count, P
        }

        """;

    /// <summary>The same lazy value carried OUT of the sibling unread (<c>P = A.take(2)</c>) and read by <c>ROWS</c>.</summary>
    private const string RetainedLazyEscaping = """
        Cap(meta r) = r
        F(y) = {
          Mk(v) = {
            Z(*xs) = [1, 2].map{ n + y }
            Cap(Z())
          }
          A = Mk(5).Algorithm
          P = A.take(2)
          Q = P[0] + 0
          ROWS
        }

        """;

    /// <summary>A cell (<c>A</c>) whose VALUE is another retained cell's (<c>B</c>) lazy value: the read happens in <c>B</c>'s computation.</summary>
    private const string RetainedNestedLazy = """
        Cap(meta r) = r
        F(y) = {
          Mk(v) = {
            Z(*xs) = [1, 2].map{ n + y }
            Cap(Z())
          }
          B = Mk(5).Algorithm
          Mk2(v) = {
            W(*xs) = B
            Cap(W())
          }
          A = Mk2(0).Algorithm
          P = A[0] + 0
          B.count, A.count, P
        }

        """;

    /// <summary>The cell's VALUE is a captured call whose argument reads <c>y</c> when the call runs.</summary>
    private const string RetainedCallReference = """
        Cap(meta r) = r
        Inc(n) = n + 1
        F(y) = {
          Mk(v) = {
            Z(*xs) = Cap(Inc(y))
            Cap(Z())
          }
          A = Mk(5).Algorithm
          P = A.Invoke() + 0
          A.Invoke(), P
        }

        """;

    /// <summary>
    /// CONTROL — an INDEPENDENT lazy value: the row is local-only (it mentions <c>y</c>) but the selected
    /// callee's positions read nothing that existed when the cell was established.
    /// </summary>
    private const string LazyIndependentLocalAlias = """
        Cap(meta r) = r
        Dbl(n) = n * 2
        Z0(*xs) = [1, 2].map{ n + 1 }
        F(y) = {
          A = if(true, Cap(Z0()), Cap(Dbl(y))).Algorithm
          P = A[0] + 0
          A.count, P
        }

        """;

    /// <summary>
    /// A CORRECTLY CLASSIFIED program (independent review 050804fe, finding 1): the root alias <c>B</c>
    /// creates a lazy list under <c>Build(5)</c> — the activation supplying <c>z</c> is recorded INSIDE
    /// <c>B</c>'s computation — a second root alias <c>A</c> returns that same list, and the exported
    /// <c>Observe</c> counts it. <c>ROWS</c> are the root's rows.
    /// </summary>
    private const string FreshlyOwnedForwarded = """
        Cap(meta r) = r
        Build(z) = {
          Z(*xs) = [1, 2].map{ n + z }
          Cap(Z())
        }
        B = Build(5).Algorithm
        Build2(v) = {
          W(*xs) = B
          Cap(W())
        }
        A = Build2(0).Algorithm
        Observe = A.count + 0
        ROWS

        """;

    /// <summary>
    /// A local-only MEMBER whose accessibility uses the enclosing activation although the selected branch
    /// never reads its parameter (independent review 050804fe, finding 2): the retained callable is the
    /// member <c>Box.G</c> itself.
    /// </summary>
    private const string SuspendedMemberCallable = """
        Cap(meta r) = r
        F(y) = {
          Box = {
            public G(x) = if(true, x + 1, y + 0)
          }
          A = Cap(Box.G(0)).Algorithm
          P = A(5) + 0
          A(5), P
        }

        """;

    /// <summary>The same access on a second member path: the cell's receiver is a CALL of the local-only member.</summary>
    private const string SuspendedMemberCall = """
        Cap(meta r) = r
        Inc(x) = x + 1
        F(y) = {
          Box = { public Mk(k) = if(true, Cap(Inc(0)), y + 0) }
          A = Box.Mk(0).Algorithm
          P = A(5) + 0
          A(5), P
        }

        """;

    /// <summary>
    /// One cell, two channels, an EFFECT in the VALUE channel (independent review 050804fe, finding 3):
    /// <c>Same(A, A)</c> warms the CALLABLE and runs no tick; <c>EFFECT</c> is the callee's body.
    /// </summary>
    private const string ChannelEffects = """
        Cap(meta r) = r
        Effect(*xs) = EFFECT
        Sel(k) = if(k == 1, Cap(Effect()), Cap(Effect()))
        Same(f, f) = 0
        F(y) = {
          A = Sel(y).Algorithm
          P = A + 0
          Same(A, A), P
        }

        """;

    /// <summary>A program whose calls each read ONE run-scoped retained cell from a cell of their own (finding 4).</summary>
    internal static string RunScopedCellReadByEveryCall(int calls)
        => """
            Cap(meta r) = r
            Use(*xs) = 9
            Seed = Cap(Use()).Algorithm
            F(y) = {
              Mk(v) = {
                G(*xs) = Seed
                Cap(G())
              }
              A = Mk(y).Algorithm
              A + 0
            }
            Step(n) = n + F(n)

            """ + "repeat(Step(0), " + calls.ToString(CultureInfo.InvariantCulture) + ")\n";

    /// <summary>A DIRECT read of an unavailable captured parameter: <c>UnknownName(y)</c> with the detached-parameter context.</summary>
    private static async Task AssertRefusedForY(Expr program, Route route)
    {
        var result = await Run(program, route);
        Assert.True(result.IsError, AsyncEvaluationHarness.NeutralOf(result));
        var unknown = Assert.IsType<EvalError.UnknownName>(result.Error.UnwrapContext());
        Assert.Equal("y", unknown.Name);
        Assert.Contains(Contexts(result.Error), context =>
            context is TextErrorContext { Message: var message } && message == Evaluator.DetachedParameterMessage("y"));
    }

    /// <summary>
    /// A detached REUSE of a retained cell already known to depend on an inaccessible activation: the
    /// <c>LocalOnlyProperty</c> of the alias itself (audit SPECS §D, step 10), a binding of an enclosing call.
    /// </summary>
    private static async Task AssertReuseRefused(Expr program, Route route, string alias = "A")
    {
        var result = await Run(program, route);
        Assert.True(result.IsError, AsyncEvaluationHarness.NeutralOf(result));
        var refusal = Assert.IsType<EvalError.LocalOnlyProperty>(result.Error.UnwrapContext());
        Assert.Equal(alias, refusal.PropertyName);
        Assert.Equal("an enclosing call", refusal.ObjectDesc);
    }

    /// <summary>
    /// THE RETAINED CELL IS JUDGED AT REUSE (ledger R-1). A retained runtime-alias binding cell records the
    /// input reads of its computation (<c>Evaluator.AliasCellInputs</c>; Lean <c>CellInputs</c>), and a reuse
    /// is judged against the reader before its channel runs (<c>Evaluator.RetainedCellAdmission</c>; Lean
    /// <c>reuseRetainedCell</c>). Here the row reads the local alias <c>A</c> ATTACHED first, which
    /// establishes the call's cell from <c>Sel(y)</c> and records the read of <c>y</c>; the falsely exported
    /// sibling <c>P</c> then reuses that cell from its detached evaluation, where <c>F</c>'s activation is
    /// detached, and is REFUSED with the alias's own <c>LocalOnlyProperty</c>: the cell is known to depend
    /// on an activation the reader may not use. Until November 2026 it was not refused (the pinned residual
    /// gave the declared <c>((6, 6), (10, 10))</c> under the inner-property lifetime rule, and
    /// <c>((6, 6), (10, 6))</c> before it). The correctly classified program is unchanged.
    /// </summary>
    [Theory]
    [MemberData(nameof(Routes))]
    public async Task R1_AFalselyExportedSiblingReusingAnEstablishedLocalAliasCell_IsRefused(Route route)
    {
        foreach (var source in new[] { RetainedAlias, RetainedAliasThroughACallback })
        {
            Assert.Equal("ok raw=S[S[6, 6], S[10, 10]] n=2", await Observe(Parsed(source + "F(1), F(2)\n"), route));
            await AssertReuseRefused(MisExposed(source + "F(1), F(2)\n", "F.P"), route);
        }
    }

    /// <summary>
    /// THE ROW ORDER DOES NOT DECIDE WHETHER THE SIBLING IS REFUSED. With the sibling first its detached
    /// evaluation establishes the cell itself: the row runs at its declaring level's watermark, serving the
    /// sibling, and the read of the written <c>y</c> is refused where it happens — the DIRECT read's
    /// <c>UnknownName(y)</c>, at the occurrence. With the attached read first the cell is already known to
    /// depend on <c>y</c>, and the reuse is its <c>LocalOnlyProperty</c>.
    /// </summary>
    [Theory]
    [MemberData(nameof(Routes))]
    public async Task R1_TheRefusalDoesNotDependOnTheRowOrder(Route route)
    {
        var reversed = MisExposed(RetainedAlias.Replace("A(5), P", "P, A(5)", StringComparison.Ordinal) + "F(1), F(2)\n", "F.P");
        await AssertRefusedForY(reversed, route);
        Assert.Equal(new SourceSpan(6, 11, 6, 12), (await Run(reversed, route)).Error.UnwrapContext().Span);
        await AssertReuseRefused(MisExposed(RetainedAlias + "F(1), F(2)\n", "F.P"), route);
    }

    /// <summary>
    /// The VALUE route and the value view are judged like the CALLABLE route: a bare read of a
    /// parameter-rooted path alias, and a zero-supply call of the value-only alias, each after the attached
    /// row warmed the cell (the reuse refusal), and each in the other order (the direct read's).
    /// </summary>
    [Theory]
    [MemberData(nameof(Routes))]
    public async Task R1_TheValueRouteAndTheValueView_AreRefusedInBothRowOrders(Route route)
    {
        Assert.Equal("ok raw=S[S[2, 2], S[3, 3]] n=2", await Observe(Parsed(RetainedPathValue + "F(1), F(2)\n"), route));
        await AssertReuseRefused(MisExposed(RetainedPathValue + "F(1), F(2)\n", "F.P"), route);
        await AssertRefusedForY(MisExposed(RetainedPathValue.Replace("A + 0, P", "P, A + 0", StringComparison.Ordinal) + "F(1), F(2)\n", "F.P"), route);

        Assert.Equal("ok raw=S[S[2, 2], S[3, 3]] n=2", await Observe(Parsed(RetainedValueView + "F(1), F(2)\n"), route));
        await AssertReuseRefused(MisExposed(RetainedValueView + "F(1), F(2)\n", "F.P"), route);
        await AssertRefusedForY(MisExposed(RetainedValueView.Replace("A(), P", "P, A()", StringComparison.Ordinal) + "F(1), F(2)\n", "F.P"), route);
    }

    /// <summary>
    /// COLD AND WARM CHANNELS of one cell: the attached row warms the CALLABLE (<c>A()</c>) and the sibling
    /// reads the cold VALUE (<c>A</c>), or the other way round. The record belongs to the cell, so either
    /// reuse is judged by everything its computation read so far.
    /// </summary>
    [Theory]
    [MemberData(nameof(Routes))]
    public async Task R1_AColdChannelOfAWarmCell_IsRefused(Route route)
    {
        foreach (var (attached, sibling) in new[] { ("A()", "A"), ("A + 0", "A()") })
        {
            var source = string.Format(CultureInfo.InvariantCulture, RetainedChannels, attached, sibling) + "F(1), F(2)\n";
            Assert.Equal("ok raw=S[S[1, 1], S[2, 2]] n=2", await Observe(Parsed(source), route));
            await AssertReuseRefused(MisExposed(source, "F.P"), route);
        }
    }

    /// <summary>
    /// A KNOWN DEPENDENT CELL IS REFUSED BEFORE ITS CHANNEL RUNS (independent review 050804fe, finding 3).
    /// <c>Same(A, A)</c> warms the CALLABLE — which reads <c>y</c> — and runs no tick; the falsely exported
    /// sibling's VALUE request is then refused with NO tick: the cold channel's effect is not executed for a
    /// reader that may not have the cell. The other row order refuses at the read of <c>y</c>, with no tick
    /// either. The same holds for work instead of an effect: the bounded range the VALUE channel would
    /// materialize is never built, so the refusal is not replaced by the collection limit — which the
    /// correctly classified program, whose channel does run, still reports.
    /// </summary>
    [Theory]
    [MemberData(nameof(Routes))]
    public async Task R1_AKnownDependentCell_IsRefusedBeforeItsChannelRuns(Route route)
    {
        var ticking = ChannelEffects.Replace("EFFECT", "tick()", StringComparison.Ordinal);
        var correct = await RunWithBudget(Parsed(ticking + "F(1)\n"), route);
        Assert.Equal("ok raw=S[0, 1] n=1", AsyncEvaluationHarness.NeutralOf(correct.Result));
        Assert.Equal(1, correct.Budget.TickCount);

        var warmedOnly = await RunWithBudget(Parsed(ticking.Replace("Same(A, A), P", "Same(A, A), 0", StringComparison.Ordinal) + "F(1)\n"), route);
        Assert.Equal("ok raw=S[0, 0] n=1", AsyncEvaluationHarness.NeutralOf(warmedOnly.Result));
        Assert.Equal(0, warmedOnly.Budget.TickCount);

        var warm = await RunWithBudget(MisExposed(ticking + "F(1)\n", "F.P"), route);
        Assert.Equal("A", Assert.IsType<EvalError.LocalOnlyProperty>(warm.Result.Error.UnwrapContext()).PropertyName);
        Assert.Equal(0, warm.Budget.TickCount);

        var siblingFirst = await RunWithBudget(
            MisExposed(ticking.Replace("Same(A, A), P", "P, Same(A, A)", StringComparison.Ordinal) + "F(1)\n", "F.P"), route);
        Assert.Equal("y", Assert.IsType<EvalError.UnknownName>(siblingFirst.Result.Error.UnwrapContext()).Name);
        Assert.Equal(0, siblingFirst.Budget.TickCount);

        var bounded = ChannelEffects.Replace("EFFECT", "range(1, 999999999)", StringComparison.Ordinal);
        Assert.IsType<EvalError.CollectionSizeLimitExceeded>((await Run(Parsed(bounded + "F(1)\n"), route)).Error.UnwrapContext());
        await AssertReuseRefused(MisExposed(bounded + "F(1)\n", "F.P"), route);
        await AssertRefusedForY(MisExposed(bounded.Replace("Same(A, A), P", "P, Same(A, A)", StringComparison.Ordinal) + "F(1)\n", "F.P"), route);
    }

    /// <summary>
    /// The record covers every input read of the cell's computation: a local-only property read through
    /// the key's activation (a HIT here), the reuse of another retained cell (its read passes on), and a
    /// reuse reached through a helper's parameter. Each makes the cell known to depend on <c>F</c>'s
    /// activation, so the sibling's reuse is the alias's <c>LocalOnlyProperty</c>.
    /// </summary>
    [Theory]
    [MemberData(nameof(Routes))]
    public async Task R1_LocalOnlyHitsNestedCellsAndHelpers_AreRefused(Route route)
    {
        Assert.Equal("ok raw=S[S[6, 6, 6], S[10, 10, 10]] n=2", await Observe(Parsed(RetainedLocalOnlyHit + "F(1), F(2)\n"), route));
        await AssertReuseRefused(MisExposed(RetainedLocalOnlyHit + "F(1), F(2)\n", "F.P"), route);

        Assert.Equal("ok raw=S[S[6, 6, 6], S[10, 10, 10]] n=2", await Observe(Parsed(RetainedNested + "F(1), F(2)\n"), route));
        await AssertReuseRefused(MisExposed(RetainedNested + "F(1), F(2)\n", "F.P"), route);

        Assert.Equal("ok raw=S[S[6, 6], S[10, 10]] n=2", await Observe(Parsed(RetainedThroughAHelper + "F(1), F(2)\n"), route));
        await AssertReuseRefused(MisExposed(RetainedThroughAHelper + "F(1), F(2)\n", "F.P"), route);
    }

    /// <summary>
    /// AN ADMITTED MEMBER ACCESS IS AN INPUT READ (independent review 050804fe, finding 2). <c>Box.G</c> and
    /// <c>Box.Mk</c> are local-only members: their accessibility uses <c>F</c>'s activation although the
    /// selected branch never reads <c>y</c>. The cell records that admitted access, so the falsely exported
    /// sibling is refused in BOTH row orders — the reuse of the warm cell, or the member access itself when
    /// its own evaluation establishes the cell — and the correctly classified programs keep their value.
    /// </summary>
    [Theory]
    [MemberData(nameof(Routes))]
    public async Task R1_AnAdmittedLocalOnlyMemberAccess_IsRefusedInBothRowOrders(Route route)
    {
        foreach (var (source, member) in new[] { (SuspendedMemberCallable, "G"), (SuspendedMemberCall, "Mk") })
        {
            Assert.Equal("ok raw=S[6, 6] n=1", await Observe(Parsed(source + "F(1)\n"), route));
            Assert.Equal("ok raw=S[6, 6] n=1",
                await Observe(Parsed(source.Replace("A(5), P", "P, A(5)", StringComparison.Ordinal) + "F(1)\n"), route));

            await AssertReuseRefused(MisExposed(source + "F(1)\n", "F.P"), route);

            var siblingFirst = await Run(MisExposed(source.Replace("A(5), P", "P, A(5)", StringComparison.Ordinal) + "F(1)\n", "F.P"), route);
            Assert.True(siblingFirst.IsError, AsyncEvaluationHarness.NeutralOf(siblingFirst));
            var refusal = Assert.IsType<EvalError.LocalOnlyProperty>(siblingFirst.Error.UnwrapContext());
            Assert.Equal(member, refusal.PropertyName);
            Assert.Equal("Box", refusal.ObjectDesc);
        }
    }

    /// <summary>The same local-only member reached through an <c>open</c> of its block: <c>ROWS</c> and <c>P</c>'s body vary.</summary>
    private const string OpenProvidedMember = """
        Cap(meta r) = r
        F(y) = {
          open Box
          Box = {
            public G(x) = if(true, x + 1, y + 0)
          }
          A = Cap(G(0)).Algorithm
          P = BODY + 0
          ROWS
        }

        """;

    /// <summary>
    /// OPEN QUALIFICATION OF R-1 (pinned residual, November 24 2026). The admitted access of a local-only
    /// member is recorded on the STRUCTURAL routes (a dot access, a static alias path step). An
    /// <c>open</c>-provided name is resolved by the lexical lookup, which is a state-free judgment of the
    /// Lean model (<c>MemberSettled.sf_lookupLexicalPropertyRaw</c>), so that admission is NOT recorded: a
    /// falsely exported sibling that reuses a retained cell whose callable is an <c>open</c>-provided
    /// local-only member is not refused, in EITHER row order (the cell's row runs at its declaring level's
    /// watermark whichever reader establishes it), although the sibling's own direct use of the member is
    /// refused. Not a wrong value — the member's body never reads <c>y</c> here, and a read of <c>y</c>
    /// would be refused — but an access the exposure law forbids. Closing it needs the lookup's laws
    /// restated outside retained computations (follow-up).
    /// </summary>
    [Theory]
    [MemberData(nameof(Routes))]
    public async Task R1_AnOpenProvidedLocalOnlyMember_IsNotRecorded_OpenQualification(Route route)
    {
        static string Program(string body, string rows)
            => OpenProvidedMember.Replace("BODY", body, StringComparison.Ordinal).Replace("ROWS", rows, StringComparison.Ordinal) + "F(1)\n";

        Assert.Equal("ok raw=S[6, 6] n=1", await Observe(Parsed(Program("A(5)", "A(5), P")), route));
        // The residual: neither row order refuses the reuse.
        Assert.Equal("ok raw=S[6, 6] n=1", await Observe(MisExposed(Program("A(5)", "A(5), P"), "F.P"), route));
        Assert.Equal("ok raw=S[6, 6] n=1", await Observe(MisExposed(Program("A(5)", "P, A(5)"), "F.P"), route));

        // The sibling's own use of the member is refused by the access law.
        var direct = await Run(MisExposed(Program("G(5)", "P"), "F.P"), route);
        Assert.True(direct.IsError, AsyncEvaluationHarness.NeutralOf(direct));
        Assert.Equal("G", Assert.IsType<EvalError.LocalOnlyProperty>(direct.Error.UnwrapContext()).PropertyName);
    }

    /// <summary>
    /// CONTROLS: an independent local-only cell is SHARED with the falsely exported sibling — the same
    /// value, the same four ticks (the effect runs once per call), the same established cells, whichever
    /// row establishes it — and a freshly owned binding inside a correctly exported evaluation keeps its
    /// value and its ticks.
    /// </summary>
    [Theory]
    [MemberData(nameof(Routes))]
    public async Task R1_IndependentAndFreshlyOwnedCells_AreShared(Route route)
    {
        var correct = await RunWithBudget(Parsed(IndependentLocalAlias + "F(1), F(2)\n"), route);
        var misExposed = await RunWithBudget(MisExposed(IndependentLocalAlias + "F(1), F(2)\n", "F.P"), route);
        Assert.Equal("ok raw=S[S[6, 6, 2], S[6, 6, 4]] n=2", AsyncEvaluationHarness.NeutralOf(correct.Result));
        Assert.Equal(AsyncEvaluationHarness.NeutralOf(correct.Result), AsyncEvaluationHarness.NeutralOf(misExposed.Result));
        Assert.Equal(4, misExposed.Budget.TickCount);
        Assert.Equal(correct.Budget.TickCount, misExposed.Budget.TickCount);
        Assert.Equal(correct.Budget.AliasBindingCells.AddedCount, misExposed.Budget.AliasBindingCells.AddedCount);

        // The sibling first: it establishes the very cell the row then shares.
        var siblingFirst = IndependentLocalAlias.Replace("A(5), P, tick()", "P, A(5), tick()", StringComparison.Ordinal) + "F(1), F(2)\n";
        var reversedCorrect = await RunWithBudget(Parsed(siblingFirst), route);
        var reversedMisExposed = await RunWithBudget(MisExposed(siblingFirst, "F.P"), route);
        Assert.Equal("ok raw=S[S[6, 6, 2], S[6, 6, 4]] n=2", AsyncEvaluationHarness.NeutralOf(reversedCorrect.Result));
        Assert.Equal(AsyncEvaluationHarness.NeutralOf(reversedCorrect.Result), AsyncEvaluationHarness.NeutralOf(reversedMisExposed.Result));
        Assert.Equal(reversedCorrect.Budget.TickCount, reversedMisExposed.Budget.TickCount);
        Assert.Equal(reversedCorrect.Budget.AliasBindingCells.AddedCount, reversedMisExposed.Budget.AliasBindingCells.AddedCount);

        var owned = await RunWithBudget(Parsed(FreshlyOwnedAlias + "F(1), F(2)\n"), route);
        Assert.Equal("ok raw=S[S[13, 2], S[14, 4]] n=2", AsyncEvaluationHarness.NeutralOf(owned.Result));
        Assert.Equal(4, owned.Budget.TickCount);
    }

    /// <summary>
    /// A CORRECTLY CLASSIFIED PROGRAM KEEPS ITS FRESHLY OWNED INPUTS (independent review 050804fe, finding
    /// 1). <c>Build(5)</c> records the activation supplying <c>z</c> inside <c>B</c>'s own computation, so a
    /// read of <c>z</c> is <c>B</c>'s own work and an input of no cell that reused <c>B</c>: forwarding the
    /// list through <c>A</c>, and the exported <c>Observe</c> counting it, restrict nothing. Every order of
    /// the count reads gives the declared values, with no refusal, on the front end's own classification.
    /// </summary>
    [Theory]
    [MemberData(nameof(Routes))]
    public async Task R1_ACorrectlyClassifiedProgram_KeepsItsFreshlyOwnedInputs(Route route)
    {
        var cases = new (string Rows, string Value)[]
        {
            ("B.count, A.count, Observe, A[0]", "ok raw=S[2, 2, 2, 6] n=4"),
            ("A.count, B.count, Observe, A[0]", "ok raw=S[2, 2, 2, 6] n=4"),
            ("B.count, Observe, A[0]", "ok raw=S[2, 2, 6] n=3"),
            ("B.count, B[0], A.count, Observe, A[0]", "ok raw=S[2, 6, 2, 2, 6] n=5"),
            ("B.count, A[0], Observe", "ok raw=S[2, 6, 2] n=3"),
            ("Observe, A[1], B[0]", "ok raw=S[2, 7, 6] n=3"),
        };
        foreach (var (rows, value) in cases)
        {
            var source = FreshlyOwnedForwarded.Replace("ROWS", rows, StringComparison.Ordinal);
            Assert.Equal(value, await Observe(Parsed(source), route));
            // The judgment decides nothing here: the old reuse path gives the same value.
            string unjudged;
            using (DetachedEvaluationTestSeam.DisableRetainedCellJudgment())
                unjudged = await Observe(Parsed(source), route);
            Assert.Equal(value, unjudged);
        }
    }

    /// <summary>
    /// DEFERRED READS ARE JUDGED AGAINST THEIR DEMANDER: a lazy position or a captured call's argument
    /// created in the cell's computation runs after the channel answered and reads <c>y</c> then. When the
    /// falsely exported sibling ITSELF demands it — a position of the value, a position two cells deep — the
    /// read is refused where it happens, at the written <c>y</c>, in both row orders: the sibling is being
    /// served, and it detaches <c>F</c>'s activation. The captured call's read is made by the attached row
    /// first, so there the cell is already known to depend on <c>y</c> and the reuse is its
    /// <c>LocalOnlyProperty</c>; with the sibling first it is the direct read's refusal.
    /// </summary>
    [Theory]
    [MemberData(nameof(Routes))]
    public async Task R1_ADeferredReadTheDetachedReaderDemands_IsRefusedInBothRowOrders(Route route)
    {
        var cases = new (string Source, string Correct, string Rows, string Reversed)[]
        {
            (RetainedLazyValue, "ok raw=S[S[2, 2], S[2, 3]] n=2", "A.count, P", "P, A.count"),
            (RetainedNestedLazy, "ok raw=S[S[2, 2, 2], S[2, 2, 3]] n=2", "B.count, A.count, P", "P, B.count, A.count"),
        };
        foreach (var (source, correct, rows, reversed) in cases)
        {
            Assert.Equal(correct, await Observe(Parsed(source + "F(1), F(2)\n"), route));
            await AssertRefusedForY(MisExposed(source + "F(1), F(2)\n", "F.P"), route);
            await AssertRefusedForY(MisExposed(source.Replace(rows, reversed, StringComparison.Ordinal) + "F(1), F(2)\n", "F.P"), route);
        }

        var lazyRead = new SourceSpan(4, 30, 4, 31);
        Assert.Equal(lazyRead, (await Run(MisExposed(RetainedLazyValue + "F(1), F(2)\n", "F.P"), route)).Error.UnwrapContext().Span);
        Assert.Equal(lazyRead, (await Run(MisExposed(RetainedLazyValue.Replace("A.count, P", "P, A.count", StringComparison.Ordinal) + "F(1), F(2)\n", "F.P"), route)).Error.UnwrapContext().Span);

        Assert.Equal("ok raw=S[S[2, 2], S[3, 3]] n=2", await Observe(Parsed(RetainedCallReference + "F(1), F(2)\n"), route));
        await AssertReuseRefused(MisExposed(RetainedCallReference + "F(1), F(2)\n", "F.P"), route);
        await AssertRefusedForY(MisExposed(RetainedCallReference.Replace("A.Invoke(), P", "P, A.Invoke()", StringComparison.Ordinal) + "F(1), F(2)\n", "F.P"), route);
    }

    /// <summary>
    /// A DETACHED READER MAY COUNT A LAZY LIST WITHOUT RESTRICTING A LATER ATTACHED READER (owner decision,
    /// November 24 2026). The falsely exported sibling <c>P</c> reads only the count — no position, so
    /// nothing that needs <c>y</c> — and the row then reads a position: that read belongs to <c>F</c>, which
    /// uses its own <c>y</c>. The declared values, in both row orders: with the attached read first, and
    /// with the sibling first, whose detached evaluation establishes the cell at <c>F</c>'s own watermark.
    /// A WARM CELL STILL ENFORCES THE READER'S ACCESS: a sibling that itself demands a position is refused —
    /// at the read while the position is cold, and at the reuse once the row has read it.
    /// </summary>
    [Theory]
    [MemberData(nameof(Routes))]
    public async Task R1_AnAttachedReadAfterADetachedReuse_UsesItsOwnInputsInBothRowOrders(Route route)
    {
        var counting = RetainedLazyValue.Replace("P = A[0] + 0", "P = A.count + 0", StringComparison.Ordinal);
        var declared = "ok raw=S[S[2, 2, 3], S[2, 2, 4]] n=2";
        foreach (var rows in new[] { "A.count, P, A[1]", "P, A.count, A[1]" })
        {
            var program = counting.Replace("A.count, P", rows, StringComparison.Ordinal) + "F(1), F(2)\n";
            Assert.Equal(declared, await Observe(Parsed(program), route));
            Assert.Equal(declared, await Observe(MisExposed(program, "F.P"), route));
        }

        // The single call of the review's later-attached program.
        Assert.Equal("ok raw=S[2, 2, 3] n=1",
            await Observe(MisExposed(counting.Replace("A.count, P", "A.count, P, A[1]", StringComparison.Ordinal) + "F(1)\n", "F.P"), route));
        Assert.Equal("ok raw=S[2, 2, 3] n=1",
            await Observe(MisExposed(counting.Replace("A.count, P", "P, A.count, A[1]", StringComparison.Ordinal) + "F(1)\n", "F.P"), route));

        // The sibling itself demands a position: refused at the written `y` while the position is cold …
        var demanding = RetainedLazyValue.Replace("P = A[0] + 0", "P = A[1] + 0", StringComparison.Ordinal);
        foreach (var rows in new[] { "A.count, P, A[1]", "P, A.count, A[1]" })
        {
            var program = MisExposed(demanding.Replace("A.count, P", rows, StringComparison.Ordinal) + "F(1), F(2)\n", "F.P");
            await AssertRefusedForY(program, route);
            Assert.Equal(new SourceSpan(4, 30, 4, 31), (await Run(program, route)).Error.UnwrapContext().Span);
        }

        // … and at the reuse once the row has read it: the warm cell is known to depend on `y`.
        await AssertReuseRefused(
            MisExposed(demanding.Replace("A.count, P", "A.count, A[1], P", StringComparison.Ordinal) + "F(1), F(2)\n", "F.P"), route);
    }

    /// <summary>
    /// AN ESCAPED LAZY POSITION IS READ BY ITS DEMANDER. The sibling <c>P</c> carries the cell's lazy value
    /// out unread (<c>P = A.take(2)</c>). The row's own read of a position through it is the row's read —
    /// <c>F</c> uses its own <c>y</c> — in both row orders. A second falsely exported sibling
    /// (<c>Q = P[0] + 0</c>) that demands the position is refused at the written <c>y</c>: it is being
    /// served, and it detaches <c>F</c>'s activation, whichever evaluation took the cell.
    /// </summary>
    [Theory]
    [MemberData(nameof(Routes))]
    public async Task R1_AnEscapedLazyPosition_IsJudgedAgainstItsDemander(Route route)
    {
        foreach (var (rows, declared) in new[]
        {
            ("A.count, P[0]", "ok raw=S[S[2, 2], S[2, 3]] n=2"),
            ("P[0], A.count", "ok raw=S[S[2, 2], S[3, 2]] n=2"),
        })
        {
            var program = RetainedLazyEscaping.Replace("ROWS", rows, StringComparison.Ordinal) + "F(1), F(2)\n";
            Assert.Equal(declared, await Observe(Parsed(program), route));
            Assert.Equal(declared, await Observe(MisExposed(program, "F.P"), route));
        }

        foreach (var rows in new[] { "A.count, Q", "Q, A.count" })
        {
            var program = MisExposed(RetainedLazyEscaping.Replace("ROWS", rows, StringComparison.Ordinal) + "F(1), F(2)\n", "F.P", "F.Q");
            await AssertRefusedForY(program, route);
            Assert.Equal(new SourceSpan(4, 30, 4, 31), (await Run(program, route)).Error.UnwrapContext().Span);
        }
    }

    /// <summary>
    /// CONTROL — an independent lazy value is SHARED with the falsely exported sibling: nothing is refused,
    /// because no position reads an input that existed when the cell was established.
    /// </summary>
    [Theory]
    [MemberData(nameof(Routes))]
    public async Task R1_AnIndependentLazyValue_IsShared(Route route)
    {
        var correct = await RunWithBudget(Parsed(LazyIndependentLocalAlias + "F(1), F(2)\n"), route);
        var misExposed = await RunWithBudget(MisExposed(LazyIndependentLocalAlias + "F(1), F(2)\n", "F.P"), route);
        Assert.Equal("ok raw=S[S[2, 2], S[2, 2]] n=2", AsyncEvaluationHarness.NeutralOf(correct.Result));
        Assert.Equal(AsyncEvaluationHarness.NeutralOf(correct.Result), AsyncEvaluationHarness.NeutralOf(misExposed.Result));
        Assert.Equal(correct.Budget.AliasBindingCells.AddedCount, misExposed.Budget.AliasBindingCells.AddedCount);
    }

    [Theory]
    [MemberData(nameof(Routes))]
    public async Task R1_AnEscapedElementsPendingProjectionKeepsItsWatermark(Route route)
    {
        const string source = HostParentDifferentialCorpus.EscapedAliasCall;
        var control = await RunWithBudget(Parsed(source), route);
        Assert.Equal("ok raw=6 n=1", AsyncEvaluationHarness.NeutralOf(control.Result));
        Assert.Equal(1, control.Budget.TickCount);

        var detached = await RunWithBudget(MisExposed(source, "F.P"), route);
        var error = Assert.IsType<EvalError.UnknownName>(detached.Result.Error.UnwrapContext());
        Assert.Equal("y", error.Name);
        Assert.Equal(new SourceSpan(6, 11, 6, 12), error.Span);
        Assert.Equal(0, detached.Budget.TickCount);
    }

    /// <summary>
    /// THE MUTATION GUARD OF R-1: on the OLD REUSE PATH (detachment still on, no judgment, the row supplied
    /// in the using context) the falsely exported sibling takes the cell the attached read established and
    /// is NOT refused, so the refusals above come from the judgment and nothing else.
    /// </summary>
    [Theory]
    [MemberData(nameof(Routes))]
    public async Task R1_WithoutTheReuseJudgment_TheSiblingTakesTheEstablishedCell(Route route)
    {
        foreach (var source in new[] { RetainedAlias, RetainedAliasThroughACallback })
        {
            string unjudged;
            using (DetachedEvaluationTestSeam.DisableRetainedCellJudgment())
                unjudged = await Observe(MisExposed(source + "F(1), F(2)\n", "F.P"), route);
            Assert.Equal("ok raw=S[S[6, 6], S[10, 10]] n=2", unjudged);
            await AssertReuseRefused(MisExposed(source + "F(1), F(2)\n", "F.P"), route);
        }

        string unjudgedValue;
        using (DetachedEvaluationTestSeam.DisableRetainedCellJudgment())
            unjudgedValue = await Observe(MisExposed(RetainedPathValue + "F(1), F(2)\n", "F.P"), route);
        Assert.Equal("ok raw=S[S[2, 2], S[3, 3]] n=2", unjudgedValue);

        // A deferred read: without the judgment no reader is admitted, so nothing refuses the read.
        string unjudgedLazy;
        using (DetachedEvaluationTestSeam.DisableRetainedCellJudgment())
            unjudgedLazy = await Observe(MisExposed(RetainedLazyValue + "F(1), F(2)\n", "F.P"), route);
        Assert.Equal("ok raw=S[S[2, 2], S[2, 3]] n=2", unjudgedLazy);
        await AssertRefusedForY(MisExposed(RetainedLazyValue + "F(1), F(2)\n", "F.P"), route);

        // An admitted member access and a cold channel's effect: unrecorded and unrefused on the old path.
        string unjudgedMember;
        using (DetachedEvaluationTestSeam.DisableRetainedCellJudgment())
            unjudgedMember = await Observe(MisExposed(SuspendedMemberCallable + "F(1)\n", "F.P"), route);
        Assert.Equal("ok raw=S[6, 6] n=1", unjudgedMember);
        using (DetachedEvaluationTestSeam.DisableRetainedCellJudgment())
        {
            var effect = await RunWithBudget(MisExposed(ChannelEffects.Replace("EFFECT", "tick()", StringComparison.Ordinal) + "F(1)\n", "F.P"), route);
            Assert.Equal("ok raw=S[0, 1] n=1", AsyncEvaluationHarness.NeutralOf(effect.Result));
            Assert.Equal(1, effect.Budget.TickCount);
        }
    }

    /// <summary>
    /// AN ALIAS WITHOUT AN OWNING PROPERTY (keyed as a local-only one by its declaring binding identity):
    /// its retained cell records the captured read of the activated level's parameter like any other, and
    /// the judgment refuses exactly the readers that detach that activation — not an attached reader, and
    /// not a reader whose watermark lies below the activation — with the alias's own refusal.
    /// </summary>
    [Fact]
    public void R1_APropertylessAliasCell_IsJudgedLikeAnyRetainedCell()
    {
        var ctx = Evaluator.EvalCtx.Empty;
        var below = ctx.Budget.ActivationWatermark;
        var level = new ScopeCtx(null, [], [], ["p"]) { Activation = ParameterActivation.Capture(["p"], ctx, []) };
        var alias = new Algorithm.Alias(null, [], [], new Expr.DotCall(new Expr.Param("p"), "G")) with { Parent = level };

        var cell = Evaluator.AliasBindingCell(alias, ctx);
        _ = cell.Demand();

        Assert.Null(Evaluator.RetainedCellAdmission(cell, ctx));
        Assert.Null(Evaluator.RetainedCellAdmission(cell, ctx.Detach(below)));
        var refusal = Evaluator.RetainedCellAdmission(cell, ctx.Detach(ctx.Budget.ActivationWatermark));
        var localOnly = Assert.IsType<EvalError.LocalOnlyProperty>(Assert.IsAssignableFrom<EvalError>(refusal).UnwrapContext());
        Assert.Equal("alias", localOnly.PropertyName);

        var terminal = ctx.Budget.RefuseTransientSupply(long.MaxValue);
        Assert.Same(terminal, Evaluator.RetainedCellAdmission(cell, ctx.Detach(ctx.Budget.ActivationWatermark)));
    }

    /// <summary>
    /// THE RECORD'S FORWARDS ARE WEAK, AND STILL COMPLETE FOR WHAT CAN BE READ (independent review 050804fe,
    /// finding 4). A cell forwards its later reads to the record of every cell whose computation reused it.
    /// A reader record that is still reachable — its cell, or a lazy value of it, can still be read —
    /// receives a read made afterwards; one that is no longer reachable is not kept alive by the cell it
    /// once reused.
    /// </summary>
    [Fact]
    public void R1_AReusedCellsLaterRead_ReachesEveryReachableReader_AndKeepsNoneAlive()
    {
        var ctx = Evaluator.EvalCtx.Empty;
        var reused = new Evaluator.AliasCellInputs(10, ctx.Budget);
        var reader = new Evaluator.AliasCellInputs(20, ctx.Budget);
        Assert.Null(reused.Admit(0, reader));
        var dropped = AdmitADroppedReader(reused, ctx.Budget);

        GC.Collect();
        GC.WaitForPendingFinalizers();
        GC.Collect();

        Assert.False(dropped.TryGetTarget(out _));
        // A read made now, through an activation both cells' establishment saw: recorded on both.
        Assert.False(reused.Note(5));
        Assert.True(reused.DependsBelow(6));
        Assert.True(reader.DependsBelow(6));
        Assert.False(reader.DependsBelow(5));
        // A read through an activation recorded after the reused cell was established is its own work.
        Assert.False(reused.Note(15));
        Assert.False(reused.DependsBelow(5));
        GC.KeepAlive(reader);
    }

    [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.NoInlining)]
    private static WeakReference<Evaluator.AliasCellInputs> AdmitADroppedReader(
        Evaluator.AliasCellInputs reused, EvaluationBudget budget)
    {
        var reader = new Evaluator.AliasCellInputs(30, budget);
        Assert.Null(reused.Admit(0, reader));
        return new WeakReference<Evaluator.AliasCellInputs>(reader);
    }

    [Fact]
    public void R1_AReachableReaderReceivesLateReadsThroughACollectedIntermediateCell()
    {
        var budget = Evaluator.EvalCtx.Empty.Budget;
        var source = new Evaluator.AliasCellInputs(10, budget);
        var reader = new Evaluator.AliasCellInputs(30, budget);
        var intermediate = ForwardThroughIntermediate(source, reader, budget);

        GC.Collect();
        GC.WaitForPendingFinalizers();
        GC.Collect();
        Assert.False(intermediate.TryGetTarget(out _));

        Assert.Null(reader.Admit(8, null));
        budget.EnterServing(8);
        Assert.True(source.Note(5));
        budget.ExitServing();
        Assert.False(reader.DependsBelow(8));
        Assert.False(source.Note(5));
        Assert.True(reader.DependsBelow(8));
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void R1_ACollectedReadersAdmissionStillJudgesALiveSourcesLaterRead(bool admitReaderFirst)
    {
        var budget = Evaluator.EvalCtx.Empty.Budget;
        var source = new Evaluator.AliasCellInputs(10, budget);
        var reader = AdmitTransientReader(source, budget, admitReaderFirst);

        GC.Collect();
        GC.WaitForPendingFinalizers();
        GC.Collect();
        Assert.False(reader.TryGetTarget(out _));

        budget.EnterServing(8);
        try
        {
            // Only serials below the reader's establishment watermark (5) are its inputs.
            Assert.False(source.Note(6));
            Assert.True(source.Note(4));
        }
        finally { budget.ExitServing(); }
        Assert.False(source.DependsBelow(5));
        Assert.False(source.Note(4));
        Assert.True(source.DependsBelow(5));
    }

    [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.NoInlining)]
    private static WeakReference<Evaluator.AliasCellInputs> AdmitTransientReader(
        Evaluator.AliasCellInputs source, EvaluationBudget budget, bool admitReaderFirst)
    {
        var reader = new Evaluator.AliasCellInputs(5, budget);
        if (admitReaderFirst)
            Assert.Null(reader.Admit(8, null));
        Assert.Null(source.Admit(0, reader));
        if (!admitReaderFirst)
            Assert.Null(reader.Admit(8, null));
        return new WeakReference<Evaluator.AliasCellInputs>(reader);
    }

    [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.NoInlining)]
    private static WeakReference<Evaluator.AliasCellInputs> ForwardThroughIntermediate(
        Evaluator.AliasCellInputs source, Evaluator.AliasCellInputs reader, EvaluationBudget budget)
    {
        var intermediate = new Evaluator.AliasCellInputs(20, budget);
        Assert.Null(source.Admit(0, intermediate));
        Assert.Null(intermediate.Admit(0, reader));
        return new WeakReference<Evaluator.AliasCellInputs>(intermediate);
    }

    [Theory]
    [InlineData(false, false)]
    [InlineData(false, true)]
    [InlineData(true, false)]
    [InlineData(true, true)]
    public async Task R1_AThrowingDemandRestoresItsReadersWatermark(bool asynchronous, bool cancel)
    {
        var ctx = Evaluator.EvalCtx.Empty.Detach(8);
        var budget = ctx.Budget;
        Exception failure = cancel ? new OperationCanceledException() : new InvalidOperationException("host failure");
        var calls = 0;
        EvalResult<Evaluator.CountedResult> Fail()
        {
            calls++;
            Assert.Equal(8, budget.ServingDetached);
            throw failure;
        }

        var cell = new NeedCell(Fail, async () => { await Task.Yield(); return Fail(); });
        budget.EnterServing(3);
        try
        {
            for (var i = 0; i < 2; i++)
            {
                var thrown = asynchronous
                    ? await Record.ExceptionAsync(async () => await Evaluator.RetainedCellValueAsync(cell, ctx))
                    : Record.Exception(() => Evaluator.RetainedCellValue(cell, ctx));
                Assert.Same(failure, thrown);
                Assert.Equal(3, budget.ServingDetached);
            }
            Assert.Equal(1, calls);
        }
        finally { budget.ExitServing(); }
        Assert.Equal(0, budget.ServingDetached);
    }

    /// <summary>
    /// PER-CALL RECLAMATION (independent review 050804fe, finding 4). Each call reads ONE run-scoped retained
    /// cell from a retained cell of its own. The run-scoped cell's record must keep no completed call
    /// reachable: with the run's stores still held, the live call partitions after a full collection do not
    /// grow with the number of completed calls — the same bound for 32 and for 512 calls, and the bound of
    /// the old reuse path. (The value and the number of cells established are the calls' own.)
    /// </summary>
    [Fact]
    public void R1_ARunScopedCellReadByEveryCall_KeepsNoCompletedCallReachable()
    {
        const int MaxLivePartitions = 4;
        foreach (var calls in new[] { 32, 512 })
        {
            var (judgedLive, judgedAdded, judgedValue) = LiveAliasPartitionsAfter(calls, judged: true);
            var (unjudgedLive, unjudgedAdded, unjudgedValue) = LiveAliasPartitionsAfter(calls, judged: false);

            Assert.Equal((9 * calls).ToString(CultureInfo.InvariantCulture), judgedValue);
            Assert.Equal(judgedValue, unjudgedValue);
            Assert.Equal(calls + 1, judgedAdded);
            Assert.Equal(unjudgedAdded, judgedAdded);
            Assert.InRange(unjudgedLive, 0, MaxLivePartitions);
            Assert.InRange(judgedLive, 0, MaxLivePartitions);
        }
    }

    [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.NoInlining)]
    private static (int Live, long Added, string Value) LiveAliasPartitionsAfter(int calls, bool judged)
    {
        using var oldPath = judged ? null : DetachedEvaluationTestSeam.DisableRetainedCellJudgment();
        var budget = RunForItsBudget(Parsed(RunScopedCellReadByEveryCall(calls)), out var value);
        GC.Collect();
        GC.WaitForPendingFinalizers();
        GC.Collect();
        var live = budget.AliasBindingCells.LivePartitionCount();
        var added = budget.AliasBindingCells.AddedCount;
        GC.KeepAlive(budget);
        return (live, added, value);
    }

    // The run in its own frame, so that nothing of it but the budget is reachable from the caller's.
    [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.NoInlining)]
    private static EvaluationBudget RunForItsBudget(Expr program, out string value)
    {
        var (result, budget) = Evaluator.RunCountedObserved(program, enableOptimizations: false);
        value = AsyncEvaluationHarness.NeutralOf(result).Replace("ok raw=", "", StringComparison.Ordinal).Replace(" n=1", "", StringComparison.Ordinal);
        return budget;
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

    private static async Task<(EvalResult<Evaluator.CountedResult> Result, EvaluationBudget Budget)> RunWithBudget(Expr program, Route route)
        => route switch
        {
            Route.Optimized => Evaluator.RunCountedObserved(program),
            Route.Generic => Evaluator.RunCountedObserved(program, enableOptimizations: false),
            Route.AsyncTwin => await AsyncEvaluationHarness.Complete(Evaluator.RunCountedObservedAsync(
                program, zeroArgPropertyResultCache: new RunScopedAsyncZeroArgPropertyResultCache())),
            _ => throw new ArgumentOutOfRangeException(nameof(route)),
        };

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
