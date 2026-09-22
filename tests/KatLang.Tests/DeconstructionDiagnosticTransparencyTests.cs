using KatLang.Tests.AsyncEvaluation;
using KatLang.Tests.LanguageSpec;
using static KatLang.Tests.LoopDiagnosticParityAssertions;

namespace KatLang.Tests;

/// <summary>
/// The diagnostic-transparency law of assignment deconstruction: a user-facing
/// diagnostic describes the KatLang program the programmer wrote, never the
/// machinery <c>x, *y, z = RHS</c> is elaborated into.
///
/// <para>The parser lowers one deconstruction into a hoisted <c>$deconstruct$N</c>
/// right-hand-side source property plus one anonymous inline projection helper per
/// target (<see cref="Parser"/>, <c>AddDeconstructionProperties</c>). Both are marked
/// as synthetic by structure (<c>Algorithm.IsSyntheticDeconstructionFrame</c>), and the
/// generic evaluation-context enrichment skips them: no <c>while evaluating call to
/// {...}</c> for the helper and no <c>while evaluating property $deconstruct$N</c> for
/// the source. Transparency follows that STRUCTURAL provenance, never the spelling of a
/// name, so a written identifier is never suppressed for resembling the convention and a
/// host-built anonymous callee still reports its ordinary call frame.</para>
///
/// <para>The suppression is diagnostics-only: error kinds, payloads, and source spans are
/// unchanged, genuine user-written frames keep their identity and their outermost-to-
/// innermost order, and the deconstruction's own binding failures keep their
/// <see cref="DeconstructionBindingContext"/> wording.</para>
/// </summary>
public class DeconstructionDiagnosticTransparencyTests
{
    private const string SyntheticSourcePrefix = "$deconstruct$";

    /// <summary>The rendered spelling of an anonymous algorithm in a call context.</summary>
    private const string AnonymousCalleeDescription = "{...}";

    private static EvalError Failure(string source)
    {
        var result = Evaluator.Run(new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root));
        Assert.True(result.IsError, $"Expected a failure but evaluation produced: {(result.IsError ? null : result.Value)}");
        return result.Error;
    }

    private static KatLangError Rendered(string source)
    {
        var failure = Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run(source));
        return Assert.Single(failure.Errors);
    }

    /// <summary>
    /// Neither synthetic identity may appear anywhere in the STRUCTURED error — context
    /// payloads included — nor in the rendered message a host shows.
    /// </summary>
    private static void AssertNoSyntheticIdentity(string source)
    {
        var error = Failure(source);
        foreach (var context in ContextChain(error))
        {
            Assert.DoesNotContain(SyntheticSourcePrefix, context, StringComparison.Ordinal);
            Assert.DoesNotContain(AnonymousCalleeDescription, context, StringComparison.Ordinal);
        }

        var rendered = Rendered(source);
        Assert.DoesNotContain(SyntheticSourcePrefix, rendered.Message, StringComparison.Ordinal);
        Assert.DoesNotContain(AnonymousCalleeDescription, rendered.Message, StringComparison.Ordinal);
    }

    private static string SpanText(SourceSpan? span)
        => span is { } value
            ? $"[{value.Start.Line}:{value.Start.Column}-{value.End.Line}:{value.End.Column})"
            : "null";

    // ── 1. Direct deconstruction failure ────────────────────────────────────

    /// <summary>
    /// The shape failure of a written pattern is reported against that pattern and nothing
    /// else: ONE context frame, the binder's own expected/actual numbers, the demand span,
    /// and no trace of the helper the assignment was elaborated into.
    /// </summary>
    [Theory]
    [InlineData("x, y = 1\nx", "while binding assignment pattern x, y", 2, 1)]
    [InlineData("x, y = 1, 2, 3\nx", "while binding assignment pattern x, y", 2, 3)]
    [InlineData("x, y = ()\nx", "while binding assignment pattern x, y", 2, 0)]
    [InlineData("x, y, z = 1, 2\nx", "while binding assignment pattern x, y, z", 3, 2)]
    [InlineData("x, y = [1, 2, 3]\nx", "while binding assignment pattern x, y", 2, 3)]
    [InlineData("*x, y = ()\nx", "while binding assignment pattern *x, y", 1, 0)]
    public void DirectShapeFailure_ReportsOnlyTheWrittenPattern(
        string source,
        string expectedContext,
        int expectedValues,
        int actualValues)
    {
        var error = Failure(source);

        Assert.Equal([expectedContext], ContextChain(error));
        var context = Assert.IsType<EvalError.WithContext>(error);
        Assert.IsType<DeconstructionBindingContext>(context.ErrorContext);

        var arity = Assert.IsType<EvalError.ArityMismatch>(context.Inner);
        Assert.Equal(expectedValues, arity.Expected);
        Assert.Equal(actualValues, arity.Actual);

        // The synthetic helper never contributes a signature to blame.
        Assert.Null(arity.Signature);

        AssertNoSyntheticIdentity(source);
    }

    /// <summary>
    /// The demand span survives suppression: the report is positioned at the reference that
    /// demanded the target, exactly where the synthetic call frame used to carry it.
    /// </summary>
    [Fact]
    public void DirectShapeFailure_KeepsTheDemandSpan()
    {
        const string source = "x, y = 1\nx";
        var error = Failure(source);

        Assert.Equal("[2:1-2:2)", SpanText(error.Span));
        Assert.Equal("[2:1-2:2)", SpanText(Rendered(source).Span));

        // F2's invariant: a synthetic construct contributes no source location, so the
        // binder's own mismatch stays span-free rather than borrowing the helper's.
        Assert.Null(Innermost(error).Span);
    }

    // ── 2. An error originating in right-hand-side evaluation ───────────────

    /// <summary>
    /// The crucial counterpart of suppression: a failure raised by a user-written call in
    /// the right-hand side keeps that call's own frame. Only the deconstruction helper's
    /// frame disappears.
    /// </summary>
    [Fact]
    public void RightHandSideCallFailure_KeepsTheUserWrittenCallFrame()
    {
        const string source = "Bad(n) = n / 0\nx, y = Bad(1)\nx";
        var error = Failure(source);

        Assert.Equal(["while evaluating call to Bad"], ContextChain(error));
        Assert.IsType<EvalError.DivByZero>(Innermost(error));
        Assert.Equal("[1:10-1:15)", SpanText(error.Span));

        Assert.Equal(
            "while evaluating call to Bad: Division by zero",
            Rendered(source).Message);
    }

    /// <summary>
    /// Ordering between genuine frames is untouched: the outer call, then the inner one.
    /// Before the fix the helper's frame sat BETWEEN them.
    /// </summary>
    [Fact]
    public void NestedUserCallsThroughADeconstruction_KeepTheirOrder()
    {
        const string source = "Outer(n) = {\n  a, b = Inner(n)\n  a\n}\nInner(n) = n / 0\nOuter(1)";
        var error = Failure(source);

        Assert.Equal(
            ["while evaluating call to Outer", "while evaluating call to Inner"],
            ContextChain(error));
        Assert.IsType<EvalError.DivByZero>(Innermost(error));
        AssertNoSyntheticIdentity(source);
    }

    /// <summary>
    /// A deconstruction inside a callable keeps the enclosing call's frame and loses only
    /// the helper's, so the reader still learns which algorithm was running.
    /// </summary>
    [Fact]
    public void DeconstructionInsideACallable_KeepsTheEnclosingCallFrame()
    {
        const string source = "F(n) = {\n  a, b = n / 0, 1\n  a\n}\nF(1)";
        var error = Failure(source);

        Assert.Equal(["while evaluating call to F"], ContextChain(error));
        Assert.Equal(
            "while evaluating call to F: Division by zero",
            Rendered(source).Message);
    }

    // ── 3. Nested deconstruction ────────────────────────────────────────────

    /// <summary>
    /// Two deconstruction frames on one failure path used to stack two helper frames
    /// ("call to {...}: call to {...}"). Neither remains, and no chain of synthetic source
    /// names accumulates either.
    /// </summary>
    [Theory]
    // A deconstruction whose right-hand side is a brace body containing another one.
    [InlineData("F = {\n  a, b = { c, d = { }\n c }, 2\n  a\n}\nF")]
    // Two deconstructions in one scope, the second reading a target of the first.
    [InlineData("F = {\n  a, b = 1, 2\n  c, d = a / 0, b\n  c\n}\nF")]
    // A deconstruction whose right-hand side calls a callable that deconstructs again.
    [InlineData("G(n) = {\n  p, q = n / 0, 1\n  p\n}\nx, y = G(1), 2\nx")]
    public void NestedDeconstruction_AccumulatesNoSyntheticFrames(string source)
    {
        AssertNoSyntheticIdentity(source);
        AssertEveryFrameNamesWrittenText(source);
    }

    /// <summary>
    /// The invariant stated positively, and the test that a name-blind check cannot fake:
    /// every subject a context frame names must be text the programmer actually WROTE. A
    /// leaked helper fails this whatever it is called, and a legitimate frame passes it.
    /// </summary>
    private static void AssertEveryFrameNamesWrittenText(string source)
    {
        foreach (var subject in FrameSubjects(Failure(source)))
        {
            Assert.Contains(
                subject,
                source,
                StringComparison.Ordinal);
        }
    }

    /// <summary>The named subject of each frame that has one, outermost first.</summary>
    private static IEnumerable<string> FrameSubjects(EvalError error)
    {
        while (error is EvalError.WithContext context)
        {
            switch (context.ErrorContext)
            {
                case CallContext call:
                    yield return call.CalleeDescription;
                    break;
                case PropertyEvaluationContext property:
                    yield return property.PropertyName;
                    break;
                case ParameterEvaluationContext parameter:
                    yield return parameter.ParameterName;
                    break;
                case DotCallContext dotCall:
                    yield return dotCall.PropertyName;
                    break;
            }

            error = context.Inner;
        }
    }

    /// <summary>
    /// The nested case pinned exactly: one written property name, one context frame, and
    /// the inner brace's own span on the underlying error.
    /// </summary>
    [Fact]
    public void NestedDeconstruction_RendersTheWrittenProgramOnly()
    {
        const string source = "F = {\n  a, b = { c, d = { }\n c }, 2\n  a\n}\nF";
        var error = Failure(source);

        Assert.Equal(["while evaluating property c"], ContextChain(error));
        Assert.IsType<EvalError.MissingOutput>(Innermost(error));
        Assert.Equal("[2:19-2:22)", SpanText(Innermost(error).Span));
    }

    // ── 4. A right-hand side with no output ─────────────────────────────────

    /// <summary>
    /// F3's requirement for the no-output right-hand side is only that no synthetic frame
    /// is added. With both helper frames gone, a deconstruction reports EXACTLY what the
    /// equivalent ordinary assignment reports — same context chain, same message, and the
    /// same blamed reference — so the elaboration is no longer observable at all. (Whether
    /// the target or the right-hand side is the better blame subject is the separate
    /// no-output question; this pins parity with ordinary assignment, not a new wording.)
    /// The expected span is stated per row because the control spells the same program with
    /// the blamed reference in a different column, not because the two disagree.
    /// </summary>
    [Theory]
    [InlineData("x, y = { }\nx", "x = { }\nx", "[2:1-2:2)")]
    [InlineData("A = { Q = 1 }\nx, y = A\nx", "A = { Q = 1 }\nx = A\nx", "[2:8-2:9)")]
    [InlineData("F(n) = {\n  a, b = { }\n  a\n}\nF(1)", "F(n) = {\n  a = { }\n  a\n}\nF(1)", "[3:3-3:4)")]
    public void NoOutputRightHandSide_MatchesTheOrdinaryAssignmentControl(
        string source,
        string control,
        string expectedSpan)
    {
        var error = Failure(source);
        var controlError = Failure(control);

        Assert.Equal(ContextChain(controlError), ContextChain(error));
        Assert.IsType<EvalError.MissingOutput>(Innermost(error));

        var rendered = Rendered(source);
        Assert.Equal(KatLangErrorCode.MissingOutput, rendered.Code);
        Assert.Equal(Rendered(control).Message, rendered.Message);
        Assert.Equal(expectedSpan, SpanText(rendered.Span));

        AssertNoSyntheticIdentity(source);
        AssertEveryFrameNamesWrittenText(source);
    }

    // ── 5. Error kinds other than arity ─────────────────────────────────────

    /// <summary>
    /// Suppression is not specialized to one error kind: every failure raised anywhere
    /// under a deconstruction keeps its own structured kind and loses only the synthetic
    /// frames.
    /// </summary>
    [Theory]
    [InlineData("x, y = 1/0, 2\nx", KatLangErrorCode.DivisionByZero)]
    [InlineData("x, y = 'a' - 1, 2\nx", KatLangErrorCode.TypeMismatch)]
    [InlineData("x, y = { }\nx", KatLangErrorCode.MissingOutput)]
    [InlineData("x, y = 1\nx", KatLangErrorCode.ArityMismatch)]
    [InlineData("x, y = sum\nx", KatLangErrorCode.ArityMismatch)]
    [InlineData("x, y = reduce([1, 2, 3], 1/0)\nx", KatLangErrorCode.ArityMismatch)]
    [InlineData("R(n) = R(n + 1)\nx, y = R(1)\nx", KatLangErrorCode.EvaluationDepthExceeded)]
    public void EveryErrorKindThroughADeconstruction_LosesOnlyTheSyntheticFrames(
        string source,
        KatLangErrorCode expectedCode)
    {
        Assert.Equal(expectedCode, Rendered(source).Code);
        AssertNoSyntheticIdentity(source);
        AssertEveryFrameNamesWrittenText(source);
    }

    /// <summary>
    /// Resource limits reach the host unchanged: they are already exempt from context
    /// enrichment, so neither the recursion limit nor the step limit may acquire a
    /// synthetic frame on its way out of a deconstruction.
    /// </summary>
    [Fact]
    public void RecursionLimitThroughADeconstruction_CarriesNoContextAtAll()
    {
        const string source = "R(n) = R(n + 1)\nx, y = R(1)\nx";
        var error = Failure(source);

        Assert.Empty(ContextChain(error));
        Assert.IsType<EvalError.EvaluationDepthExceeded>(error);
        Assert.True(error.IsResourceLimit);
    }

    [Fact]
    public void StepLimitThroughADeconstruction_CarriesNoSyntheticFrame()
    {
        const string source = "R(n) = R(n - 1)\nx, y = R(400), 1\nx";
        var result = Evaluator.Run(
            new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root),
            new EvaluationLimits { MaxSteps = 500 });

        Assert.True(result.IsError);
        Assert.True(result.Error.IsResourceLimit);
        foreach (var context in ContextChain(result.Error))
        {
            Assert.DoesNotContain(SyntheticSourcePrefix, context, StringComparison.Ordinal);
            Assert.DoesNotContain(AnonymousCalleeDescription, context, StringComparison.Ordinal);
        }
    }

    // ── 6. Provenance, not spelling ─────────────────────────────────────────

    /// <summary>
    /// A WRITTEN identifier whose text resembles the internal convention is an ordinary
    /// user property and keeps its diagnostic frame. Transparency is decided by the
    /// parser's structural mark, so no name-shaped heuristic can silence a real name.
    /// </summary>
    [Theory]
    [InlineData("deconstruct = { }\nx, y = deconstruct\nx", "deconstruct")]
    [InlineData("deconstruct0 = { }\ndeconstruct0", "deconstruct0")]
    [InlineData("synthetic = { }\nx, y = synthetic\nx", "synthetic")]
    public void UserWrittenIdentifierResemblingTheConvention_IsNotSuppressed(string source, string name)
    {
        Assert.Equal([$"while evaluating property {name}"], ContextChain(Failure(source)));
        Assert.Contains($"Property '{name}'", Rendered(source).Message, StringComparison.Ordinal);
    }

    /// <summary>
    /// A host-built anonymous callee is USER-AUTHORED, not evaluator plumbing: it carries
    /// no deconstruction provenance, so it still reports the ordinary anonymous call frame.
    /// This is the distinction that name-based filtering could not make — the parser emits
    /// an <c>Expr.Call</c> over an <c>Expr.AlgorithmExpr</c> for deconstruction helpers
    /// ONLY, so every other one reaches the evaluator from a host-built tree.
    /// </summary>
    [Fact]
    public void HostBuiltAnonymousCallee_StillReportsItsCallFrame()
    {
        var anonymousCallee = new Algorithm.User(
            Parent: null,
            ParameterPatterns: [new CaptureParameterPattern(new ParameterDeclaration("n"))],
            Opens: [],
            Properties: [],
            Output: [new Expr.Binary(BinaryOp.Div, new Expr.Param("n"), new Expr.Num(0))])
        {
            HasExplicitParameterList = true,
        };

        var root = new Algorithm.User(
            Parent: null,
            ParameterPatterns: [],
            Opens: [],
            Properties: [],
            Output: [new Expr.Call(new Expr.AlgorithmExpr(anonymousCallee), [new Expr.Num(1)])]);

        var result = Evaluator.Run(new Expr.AlgorithmExpr(root));

        Assert.True(result.IsError);
        Assert.Equal([$"while evaluating call to {AnonymousCalleeDescription}"], ContextChain(result.Error));
        Assert.IsType<EvalError.DivByZero>(Innermost(result.Error));
    }

    /// <summary>
    /// The same host-built shape with the deconstruction mark applied is transparent, so
    /// the rule really is the mark and not the node shape: the parser is the only origin of
    /// that mark, and it is what the evaluator consults.
    /// </summary>
    [Fact]
    public void ParserElaboratedHelper_IsTheOnlyTransparentAnonymousCallee()
    {
        var root = SourceProvenance.ParseValid("x, y = 1, 2\nx").Root;
        var target = Assert.IsType<Algorithm.User>(Assert.Single(root.Properties, p => p.Name == "x").Value);
        var helperCall = Assert.IsType<Expr.Call>(Assert.Single(target.Output));
        var helper = Assert.IsType<Algorithm.User>(Assert.IsType<Expr.AlgorithmExpr>(helperCall.Function).Algorithm);

        // The transparent frames are exactly the two the parser synthesizes.
        Assert.NotNull(helper.AssignmentDeconstructionTarget);
        var hoisted = Assert.IsType<Algorithm.User>(
            Assert.Single(root.Properties, p => p.Name.StartsWith(SyntheticSourcePrefix, StringComparison.Ordinal)).Value);
        Assert.True(hoisted.IsAssignmentDeconstructionSource);

        // A written target property is NOT one of them.
        Assert.False(target.IsAssignmentDeconstructionSource);
        Assert.Null(target.AssignmentDeconstructionTarget);
    }

    // ── 7. Async twin and planned execution ─────────────────────────────────

    /// <summary>
    /// The async twin family shares the call-context and property-context attachment
    /// points with the synchronous evaluator, so suppression cannot diverge — proven here
    /// against a GENUINELY suspending run (every zero-argument property access hops
    /// threads), not merely an async-shaped one.
    /// </summary>
    [Theory]
    [InlineData("Bad(n) = n / 0\nx, y = Bad(1)\nx")]
    [InlineData("x, y = { }\nx")]
    [InlineData("x, y = 1\nx")]
    [InlineData("Outer(n) = {\n  a, b = Inner(n)\n  a\n}\nInner(n) = n / 0\nOuter(1)")]
    public async Task AsyncTwinPath_SuppressesTheSameFrames(string source)
    {
        var ast = new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root);
        var sync = Evaluator.RunCounted(ast);
        Assert.True(sync.IsError);

        var cache = new SuspendingAsyncZeroArgPropertyResultCache();
        var (asyncResult, _) = await AsyncEvaluationHarness.Complete(
            Evaluator.RunCountedObservedAsync(ast, zeroArgPropertyResultCache: cache));

        Assert.True(asyncResult.IsError);
        foreach (var context in ContextChain(asyncResult.Error))
        {
            Assert.DoesNotContain(SyntheticSourcePrefix, context, StringComparison.Ordinal);
            Assert.DoesNotContain(AnonymousCalleeDescription, context, StringComparison.Ordinal);
        }

        Assert.Equal(ContextChain(sync.Error), ContextChain(asyncResult.Error));
        Assert.Equal(Innermost(sync.Error).GetType(), Innermost(asyncResult.Error).GetType());
        Assert.Equal(
            KatLangError.FromEvalError(sync.Error).Message,
            KatLangError.FromEvalError(asyncResult.Error).Message);
        Assert.Equal(SpanText(sync.Error.Span), SpanText(asyncResult.Error.Span));

        // The twin path really suspended, and never consulted the synchronous seam.
        Assert.True(cache.AsyncAccesses > 0);
        Assert.Equal(0, cache.SyncAccesses);
    }

    // ── 8. Corpus-wide nets ─────────────────────────────────────────────────

    /// <summary>
    /// A generated matrix rather than a hand-picked list: every written deconstruction
    /// SHAPE crossed with every failure ORIGIN, so a shape or origin nobody thought to
    /// enumerate still has to obey the invariant.
    /// </summary>
    public static TheoryData<string> DeconstructionFailureMatrix()
    {
        string[] patterns =
        [
            "x, y",
            "x, y, z",
            "*x, y",
            "x, *y",
            "x, *y, z",
        ];

        // Each right-hand side fails somewhere else, and through a different context
        // MECHANISM: its own evaluation, a user call, a builtin call, a dot-call edge, a
        // clause family, a property with no output, or the pattern's own shape.
        string[] rightHandSides =
        [
            "1 / 0",
            "Bad(1)",
            "Bad(1), 2",
            "{ }",
            "None",
            "'a' - 1",
            "sum",
            "reduce([1, 2, 3], 1 / 0)",
            "[1, 2].filter(1 / 0)",
            "Choose(0)",
            "Pick(9)",
            "1",
            "1, 2, 3, 4",
            "()",
            "[1, 2, 3, 4]",
            "R(1)",
        ];

        var data = new TheoryData<string>();
        foreach (var pattern in patterns)
        {
            foreach (var rhs in rightHandSides)
            {
                var first = pattern.TrimStart('*').Split(',')[0].Trim();
                data.Add(
                    "Bad(n) = n / 0\n"
                    + "None = { Q = 1 }\n"
                    + "R(n) = R(n + 1)\n"
                    + "Choose(0) = 1 / 0\n"
                    + "Choose(n) = n\n"
                    + "Pick(1) = 1\n"
                    + $"{pattern} = {rhs}\n"
                    + first);
            }
        }

        return data;
    }

    [Theory]
    [MemberData(nameof(DeconstructionFailureMatrix))]
    public void EveryDeconstructionShapeAndFailureOrigin_KeepsTheProgramVisibleOnly(string source)
    {
        var parsed = Parser.Parse(source);
        Assert.False(parsed.HasErrors, string.Join("\n", parsed.Diagnostics.Select(static d => d.Message)));

        var result = Evaluator.Run(new Expr.AlgorithmExpr(parsed.Root));
        if (!result.IsError)
            return;

        foreach (var context in ContextChain(result.Error))
        {
            Assert.DoesNotContain(SyntheticSourcePrefix, context, StringComparison.Ordinal);
            Assert.DoesNotContain(AnonymousCalleeDescription, context, StringComparison.Ordinal);
        }

        foreach (var subject in FrameSubjects(result.Error))
            Assert.Contains(subject, source, StringComparison.Ordinal);

        var message = KatLangError.FromEvalError(result.Error).Message;
        Assert.DoesNotContain(SyntheticSourcePrefix, message, StringComparison.Ordinal);
    }

    /// <summary>
    /// The net over the two canonical differential corpora: whatever they evaluate, no
    /// diagnostic may name a synthetic deconstruction source, and no CALL frame may name an
    /// anonymous algorithm. The second half is exact rather than a text ban because the
    /// parser's ONLY <c>Expr.Call</c> over an <c>Expr.AlgorithmExpr</c> is a deconstruction
    /// helper — a written block still legitimately renders as <c>{...}</c> in a dot-call
    /// receiver or operand description, and those are untouched.
    /// </summary>
    [Fact]
    public void CanonicalCorpora_NeverNameSyntheticDeconstructionMachinery()
    {
        var sources = LanguageSpecCorpus.AllCases()
            .Where(static c => c.Outcome != SpecOutcome.ParseError)
            .Select(static c => c.Source)
            .Concat(SemanticExplorerCorpus.AllCases().Select(static c => c.Source))
            .Distinct(StringComparer.Ordinal);

        // The net is only worth anything if the corpora really do evaluate failing
        // deconstructions; pin that they do, so it can never pass vacuously.
        var failingDeconstructions = LanguageSpecCorpus.AllCases()
            .Where(static c => c.Outcome == SpecOutcome.EvalError && c.Category == "deconstruction")
            .ToList();
        Assert.NotEmpty(failingDeconstructions);
        foreach (var deconstruction in failingDeconstructions)
        {
            var failure = Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run(deconstruction.Source));
            foreach (var reported in failure.Errors)
            {
                Assert.DoesNotContain(SyntheticSourcePrefix, reported.Message, StringComparison.Ordinal);
                Assert.DoesNotContain(AnonymousCalleeDescription, reported.Message, StringComparison.Ordinal);
            }
        }

        var leaks = new List<string>();
        foreach (var source in sources)
        {
            var parsed = Parser.Parse(source);
            if (parsed.HasErrors)
                continue;

            var result = Evaluator.Run(new Expr.AlgorithmExpr(parsed.Root));
            if (!result.IsError)
                continue;

            var error = result.Error;
            while (error is EvalError.WithContext context)
            {
                if (context.ErrorContext is CallContext { CalleeDescription: AnonymousCalleeDescription })
                    leaks.Add($"anonymous call frame: {source}");

                error = context.Inner;
            }

            if (KatLangError.FromEvalError(result.Error).Message.Contains(SyntheticSourcePrefix, StringComparison.Ordinal))
                leaks.Add($"synthetic source name: {source}");
        }

        Assert.Empty(leaks);
    }

    /// <summary>
    /// Planned loop execution reproduces the generic evaluator's call boundary through the
    /// SHARED <c>WithPlannedCallBoundary</c>, which derives its callee name the same way,
    /// so a deconstruction inside a planned step reports identically with the optimizer on
    /// and off — whole structured error tree, context chain, message, and span.
    /// </summary>
    [Theory]
    [InlineData("Step(acc) = {\n  a, b = acc / 0, 1\n  a + b\n}\nrepeat(Step, 3, 1)")]
    [InlineData("Step(acc) = {\n  a, b = acc\n  a + b\n}\nrepeat(Step, 3, 1)")]
    [InlineData("Step(acc) = {\n  a, b = { }\n  a + b\n}\nrepeat(Step, 3, 1)")]
    public void PlannedLoopExecution_SuppressesTheSameFrames(string source)
    {
        var error = AssertOptimizerTransparentFailure(source);

        foreach (var context in ContextChain(error))
        {
            Assert.DoesNotContain(SyntheticSourcePrefix, context, StringComparison.Ordinal);
            Assert.DoesNotContain(AnonymousCalleeDescription, context, StringComparison.Ordinal);
        }
    }
}
