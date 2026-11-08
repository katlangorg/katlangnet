using KatLang.Evaluation;
using KatLang.Evaluation.Caching;
using static KatLang.Tests.LoopDiagnosticParityAssertions;

namespace KatLang.Tests;

/// <summary>
/// A report NAMES a binding or callee as output-less — "Property 'P' …", "Parameter 'x' …",
/// "Cannot call 'F' …", "The value <c>R.n</c> …" — only when the missing output is that
/// subject's OWN (2026-11-08; <c>Evaluator.IsOwnForBlame</c> over the Q-36 origin
/// <see cref="EvalError.MissingOutput.IsNested"/>). <c>H2 = {} + 1</c> HAS an output; its missing
/// output is the <c>{}</c> operand's, nested once the operator consumes it, so the read of
/// <c>H2</c> keeps the innermost generic report at the operand's own span, and the enclosing
/// frames render as ordinary context. The error kind, the innermost error and its origin, the
/// spread decision and every own-case message are unchanged; F3 deconstruction parity holds
/// through <see cref="EvalError.MissingOutput.KeepsOwnBlame"/>.
/// [<c>docs/design/language-rules/evaluator-and-hosting.md</c> § Blame for an output-less written argument]
/// </summary>
public class NestedMissingOutputBlameTests
{
    private const string Generic = "Algorithm has no defined output.";

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

    private static IEnumerable<ErrorContext> Contexts(EvalError error)
    {
        while (error is EvalError.WithContext context)
        {
            yield return context.ErrorContext;
            error = context.Inner;
        }
    }

    private static string Start(SourceSpan? span)
        => span is { } value ? $"[{value.Start.Line}:{value.Start.Column}]" : "null";

    /// <summary>
    /// The nested shape: code, innermost nested <see cref="EvalError.MissingOutput"/>, no property or
    /// parameter frame, no claim in the rendered text, the generic text at the operand's span.
    /// </summary>
    private static KatLangError AssertNestedReport(string source, string expectedStart)
    {
        var error = Failure(source);
        var missing = Assert.IsType<EvalError.MissingOutput>(Innermost(error));
        Assert.True(missing.IsNested, "the innermost missing output must stay nested");
        Assert.False(Evaluator.IsOwnForBlame(missing));
        Assert.Empty(Contexts(error).OfType<PropertyEvaluationContext>());
        Assert.Empty(Contexts(error).OfType<ParameterEvaluationContext>());

        var rendered = Rendered(source);
        Assert.Equal(KatLangErrorCode.MissingOutput, rendered.Code);
        Assert.Contains(Generic, rendered.Message, StringComparison.Ordinal);
        Assert.DoesNotContain("Property '", rendered.Message, StringComparison.Ordinal);
        Assert.DoesNotContain("Parameter '", rendered.Message, StringComparison.Ordinal);
        Assert.DoesNotContain("Cannot call", rendered.Message, StringComparison.Ordinal);
        Assert.DoesNotContain("The value `", rendered.Message, StringComparison.Ordinal);
        Assert.Equal(expectedStart, Start(rendered.Span));
        return rendered;
    }

    // ── 1. A property whose output row consumes an output-less operand ──────

    [Theory]
    [InlineData("H2 = {} + 1\nH2", "[1:6]")]
    [InlineData("H2 = 1 + {}\nH2", "[1:10]")]
    [InlineData("H2 = -{}\nH2", "[1:7]")]
    [InlineData("H2 = not {}\nH2", "[1:10]")]
    [InlineData("H2 = {} * 2\nH2", "[1:6]")]
    [InlineData("H2 = {} < 1\nH2", "[1:6]")]
    [InlineData("H2 = {} == 1\nH2", "[1:6]")]
    [InlineData("H2 = {} + {}\nH2", "[1:6]")]
    [InlineData("H2 = ({} + 1) * 2\nH2", "[1:7]")]
    [InlineData("H2 = {}[0]\nH2", "[1:6]")]
    [InlineData("H2 = [{}]\nH2", "[1:7]")]
    [InlineData("H2 = [1, {}]\nH2", "[1:10]")]
    [InlineData("H2 = ({}, 1)\nH2", "[1:7]")]
    [InlineData("H2 = { {} }\nH2", "[1:8]")]
    [InlineData("H2 = { {} + 1 }\nH2", "[1:8]")]
    [InlineData("A = { { Q = 1 } }\nA", "[1:7]")]
    // Through a structural carrier: the terminal's failure is nested, so neither is blamed.
    [InlineData("P = {} + 1\nA = { P }\nA", "[1:5]")]
    public void NestedOperand_IsNotTheReadPropertysMissingOutput(string source, string expectedStart)
    {
        var rendered = AssertNestedReport(source, expectedStart);
        Assert.Equal($"{Generic}\nAdd an output expression, or use `()` if the empty sequence value was intended.",
            rendered.Message.ReplaceLineEndings("\n"));
    }

    // ── 2. Consumers of such a property ─────────────────────────────────────

    [Theory]
    [InlineData("H2 = {} + 1\nH3 = H2\nH3", "[1:6]", "")]
    [InlineData("H2 = {} + 1\nsum(H2)", "[1:6]", "while evaluating call to sum: ")]
    [InlineData("H2 = {} + 1\nF(x) = H2 + x\nF(1)", "[1:6]", "while evaluating call to F: ")]
    [InlineData("H2 = {} + 1\nF(a) = sum(a)\nF(H2)", "[1:6]", "while evaluating call to F: while evaluating call to sum: ")]
    [InlineData("H2 = {} + 1\nF(x) = x + 1\nF(H2)", "[1:6]", "while evaluating call to F: ")]
    public void ConsumersOfANestedFailure_RenderItAsContextOnly(string source, string expectedStart, string expectedPrefix)
    {
        var rendered = AssertNestedReport(source, expectedStart);
        Assert.StartsWith(expectedPrefix + Generic, rendered.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void Spread_StaysANestedMissingOutputUnderTheSpreadFrame()
    {
        const string source = "H2 = {} + 1\nH2*";
        var error = Failure(source);
        Assert.IsType<SpreadOperandContext>(Assert.Single(Contexts(error)));
        Assert.True(Assert.IsType<EvalError.MissingOutput>(Innermost(error)).IsNested);

        var rendered = AssertNestedReport(source, "[1:6]");
        Assert.StartsWith("while evaluating spread operand H2: " + Generic, rendered.Message, StringComparison.Ordinal);
    }

    // ── 3. Call and member frames ───────────────────────────────────────────

    [Theory]
    [InlineData("H2 = {} + 1\nH2()", "[1:6]", "while evaluating call to H2: ")]
    [InlineData("F(x) = {} + x\nF(1)", "[1:8]", "while evaluating call to F: ")]
    [InlineData("H2 = {} + 1\nApply(f) = f()\nApply(H2)", "[1:6]", "while evaluating call to Apply: while evaluating call to f: ")]
    public void CallFrame_ClaimsOnlyTheCalleesOwnMissingOutput(string source, string expectedStart, string expectedPrefix)
    {
        var error = Failure(source);
        Assert.NotEmpty(Contexts(error).OfType<CallContext>());
        var rendered = AssertNestedReport(source, expectedStart);
        Assert.StartsWith(expectedPrefix + Generic, rendered.Message, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("Box = {\n  public M = {} + 1\n  0\n}\nBox.M", "[2:14]", "while evaluating dotCall .M of Box: ")]
    [InlineData("F(x) = {} + x\n5.F", "[1:8]", "while evaluating dotCall .F of 5: ")]
    [InlineData("Lib = {\npublic P = {} + 1\npublic A = { P }\n0\n}\nLib.A", "[2:12]", "while evaluating dotCall .A of Lib: ")]
    [InlineData("Box = {\n  public string = {} + 1\n  0\n}\nBox.string", "[2:19]", "while evaluating dotCall .string of Box: ")]
    [InlineData("Box = {\n  public string = {} + 1\n  0\n}\nBox.string()", "[2:19]", "while evaluating dotCall .string of Box: ")]
    [InlineData("Box = {\n  public string(x) = {} + x\n  0\n}\nBox.string(1)", "[2:22]", "while evaluating dotCall .string of Box: ")]
    [InlineData("P = {} + 1\nBox = {\n  public string = P\n  0\n}\nBox.string()", "[1:5]", "while evaluating dotCall .string of Box: ")]
    public void MemberFrame_ClaimsOnlyTheMembersOwnMissingOutput(string source, string expectedStart, string expectedPrefix)
    {
        var error = Failure(source);
        Assert.NotEmpty(Contexts(error).OfType<DotCallContext>());
        var rendered = AssertNestedReport(source, expectedStart);
        Assert.StartsWith(expectedPrefix + Generic, rendered.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void RootProgram_KeepsItsGenericReport()
    {
        var rendered = Rendered("{} + 1");
        Assert.Equal(KatLangErrorCode.MissingOutput, rendered.Code);
        Assert.StartsWith(Generic, rendered.Message, StringComparison.Ordinal);
        Assert.Equal("[1:1]", Start(rendered.Span));
    }

    private const string NestedMemberAliasProjection = "H2 = {} + 1\nRun(p) = {\n  Box = {\n    public string = p.Algorithm\n    0\n  }\n  Box.string()\n}\nRun(H2)";

    [Fact]
    public void MemberAliasProjectionFailure_KeepsTheNestedCause()
        => AssertNestedReport(NestedMemberAliasProjection, "[1:6]");

    // ── 4. Own controls: unchanged message and span ─────────────────────────

    private const string PropertyAdvice = "Add an output expression to '{0}', or use `()` if the empty sequence value was intended. To use one of its properties, write `{0}.X`.";
    private const string CallAdvice = "Add an output expression, or use `()` if the empty sequence value was intended. To call one of its properties, use property access instead.";
    private const string ValueAdvice = "Add an output expression, or use `()` if the empty sequence value was intended. To use one of its properties, access it explicitly.";

    public static TheoryData<string, string, string> OwnControls => new()
    {
        { "X = {}\nX", "[2:1]", "Property 'X' has no defined output.\n" + string.Format(PropertyAdvice, "X") },
        { "H2 = { X = 1 }\nH2", "[2:1]", "Property 'H2' has no defined output.\n" + string.Format(PropertyAdvice, "H2") },
        { "G = { X = 1 }\nH2 = G + 1\nH2", "[2:6]", "Property 'G' has no defined output.\n" + string.Format(PropertyAdvice, "G") },
        { "X = {}\nX + 1", "[2:1]", "Property 'X' has no defined output.\n" + string.Format(PropertyAdvice, "X") },
        { "F = { A = 1 }\nF()", "[2:1]", "Cannot call 'F' because it has no defined output.\n" + CallAdvice },
        // An own missing output nested AFTER its frame claimed it keeps that claim (KeepsOwnBlame).
        { "F = { A = 1 }\nF() + 1", "[2:1]", "Cannot call 'F' because it has no defined output.\n" + CallAdvice },
        { "Box = {\npublic M = { X = 1 }\n0\n}\nBox.M", "[5:1]", "The value `Box.M` has no defined output.\n" + ValueAdvice },
        { "Box = {\npublic M = { X = 1 }\n0\n}\nBox.M + 1", "[5:1]", "The value `Box.M` has no defined output.\n" + ValueAdvice },
        {
            "F(x) = x + 1\nF({})", "[2:3]",
            "while evaluating call to F: Parameter 'x' has no defined output: the argument bound to it is an algorithm without an output expression.\n"
                + "Add an output expression to that argument, or use `()` if the empty sequence value was intended."
        },
        {
            "F(a) = sum(a)\nF({})", "[2:3]",
            "while evaluating call to F: while evaluating call to sum: Parameter 'a' has no defined output: the argument bound to it is an algorithm without an output expression.\n"
                + "Add an output expression to that argument, or use `()` if the empty sequence value was intended."
        },
        { "{}.string", "[1:1]", "The value `{...}` has no defined output.\n" + ValueAdvice },
        // A structural carrier is a transparent reference to its terminal (M4★): the terminal's own
        // missing output keeps the terminal's blame although the carrier crossing nests it (Q-36).
        { "P = { Q = 1 }\nA = { P }\nA", "[3:1]", "Property 'P' has no defined output.\n" + string.Format(PropertyAdvice, "P") },
        { "P = { Q = 1 }\nA = { P }\nA*", "[3:1]", "while evaluating spread operand A: Property 'P' has no defined output.\n" + string.Format(PropertyAdvice, "P") },
        { "A = {\n    P = {\n        Q = 1\n    }\n    P\n}\nA", "[7:1]", "Property 'P' has no defined output.\n" + string.Format(PropertyAdvice, "P") },
        { "Lib = {\npublic P = { Q = 1 }\npublic A = { P }\n0\n}\nLib.A", "[6:1]", "The value `Lib.A` has no defined output.\n" + ValueAdvice },
        // The `.string` intrinsic names its RECEIVER, whose failure reaches it nested by design.
        { "G = { X = 1 }\nG.string", "[2:1]", "Property 'G' has no defined output.\n" + string.Format(PropertyAdvice, "G") },
        // Keep the historical own-case rendering of an explicit member named `string` too.
        { "Box = {\n  public string = { X = 1 }\n  0\n}\nBox.string()", "[5:1]", "Property 'Box' has no defined output.\n" + string.Format(PropertyAdvice, "Box") },
    };

    [Theory]
    [MemberData(nameof(OwnControls))]
    public void OwnMissingOutput_KeepsItsSubjectsReport(string source, string expectedStart, string expectedMessage)
    {
        var rendered = Rendered(source);
        Assert.Equal(KatLangErrorCode.MissingOutput, rendered.Code);
        Assert.Equal(expectedMessage, rendered.Message.ReplaceLineEndings("\n"));
        Assert.Equal(expectedStart, Start(rendered.Span));
    }

    [Fact]
    public void FramedOwnMissingOutput_IsNestedButKeepsItsBlame()
    {
        // The origin is nested exactly as Q-36 decides; only the blame survives the consumer.
        var error = Failure("F = { A = 1 }\nF() + 1");
        var call = Assert.IsType<EvalError.WithContext>(error);
        Assert.IsType<CallContext>(call.ErrorContext);
        var missing = Assert.IsType<EvalError.MissingOutput>(call.Inner);
        Assert.True(missing.IsNested);
        Assert.True(missing.KeepsOwnBlame);
        Assert.True(Evaluator.IsOwnForBlame(missing));
    }

    // ── 5. Deconstruction parity (F3) ───────────────────────────────────────

    [Fact]
    public void Deconstruction_CallOfAnOutputLessTarget_StillNamesTheTarget()
    {
        var rendered = Rendered("x, y = { }\nx()");
        Assert.Equal(KatLangErrorCode.MissingOutput, rendered.Code);
        Assert.Equal("Cannot call 'x' because it has no defined output.\n" + CallAdvice, rendered.Message.ReplaceLineEndings("\n"));
        Assert.Equal("[1:8]", Start(rendered.Span));
    }

    [Fact]
    public void Deconstruction_ReadOfAnOwnRightHandSide_NamesTheTargetLikeTheOrdinaryAssignment()
    {
        var error = Failure("x, y = { }\nx");
        Assert.Equal(new PropertyEvaluationContext("x"), Assert.Single(Contexts(error)));
        var missing = Assert.IsType<EvalError.MissingOutput>(Innermost(error));
        // The spread-relevant origin is unchanged (nested by the plumbing); only the blame is kept.
        Assert.True(missing.IsNested);
        Assert.True(missing.KeepsOwnBlame);
        Assert.Equal(Rendered("x = { }\nx").Message, Rendered("x, y = { }\nx").Message);
    }

    [Theory]
    [InlineData("x, y = {} + 1\nx", "[1:8]")]
    [InlineData("x, y = ({ }, 1)\nx", "[1:9]")]
    public void Deconstruction_NestedRightHandSide_IsNotTheTargetsMissingOutput(string source, string expectedStart)
    {
        var rendered = AssertNestedReport(source, expectedStart);
        Assert.StartsWith(Generic, rendered.Message, StringComparison.Ordinal);
    }

    // ── 6. Routes ───────────────────────────────────────────────────────────

    public static TheoryData<string> RouteCases => new()
    {
        "H2 = {} + 1\nH2",
        "H2 = { {} }\nH2",
        "H2 = {} + 1\nH2*",
        "H2 = {} + 1\nH3 = H2\nH3",
        "H2 = {} + 1\nsum(H2)",
        "H2 = {} + 1\nF(x) = H2 + x\nF(1)",
        "H2 = {} + 1\nH2()",
        "F(x) = {} + x\nF(1)",
        "H2 = {} + 1\nApply(f) = f()\nApply(H2)",
        "Box = {\n  public M = {} + 1\n  0\n}\nBox.M",
        "F(x) = {} + x\n5.F",
        "F(x) = {} + x\nG(y) = y + 1\nG(F(1))",
        "X = {}\nX",
        "F = { A = 1 }\nF() + 1",
        "x, y = { }\nx",
        "x, y = { }\nx()",
        "x, y = {} + 1\nx",
        "P = { Q = 1 }\nA = { P }\nA",
        "P = {} + 1\nA = { P }\nA",
        "Lib = {\npublic P = { Q = 1 }\npublic A = { P }\n0\n}\nLib.A",
        "Lib = {\npublic P = {} + 1\npublic A = { P }\n0\n}\nLib.A",
        "Box = {\n  public string = {} + 1\n  0\n}\nBox.string()",
        "Box = {\n  public string(x) = {} + x\n  0\n}\nBox.string(1)",
        "P = {} + 1\nBox = {\n  public string = P\n  0\n}\nBox.string()",
        "Box = {\n  public string = { X = 1 }\n  0\n}\nBox.string()",
        NestedMemberAliasProjection,
    };

    [Theory]
    [MemberData(nameof(RouteCases))]
    public async Task EveryRoute_AgreesOnCodeMessageAndSpan(string source)
    {
        var oracle = await SixRouteAgreement.OnEveryRouteAsync(source);
        Assert.Equal("err", oracle.Kind);
        Assert.StartsWith("MissingOutput: ", Assert.Single(oracle.Errors), StringComparison.Ordinal);
    }

    [Theory]
    [MemberData(nameof(RouteCases))]
    public async Task PlannedRoute_AgreesWithTheOrdinaryRoute(string source)
    {
        static string Observe(string source, bool plans)
        {
            var program = new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root);
            using var activation = plans ? InvocationPlanTestSeam.Activate(new InvocationPlanTestSeam()) : null;
            var (result, budget) = Evaluator.RunCountedObserved(program, enableOptimizations: true);
            Assert.Equal(plans || ForcedInvocationPlansHook.Forced, budget.PlanTestSeam is not null);
            Assert.True(result.IsError);
            var error = KatLangError.FromEvalError(result.Error);
            return $"{error.Code}: {error.Message} @ {error.Span}";
        }

        static async Task<string> ObserveAsync(string source, bool plans)
        {
            var program = new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root);
            using var activation = plans ? InvocationPlanTestSeam.Activate(new InvocationPlanTestSeam()) : null;
            var (result, budget) = await Evaluator.RunCountedObservedAsync(program,
                zeroArgPropertyResultCache: new RunScopedAsyncZeroArgPropertyResultCache());
            Assert.Equal(plans || ForcedInvocationPlansHook.Forced, budget.PlanTestSeam is not null);
            Assert.True(result.IsError);
            var error = KatLangError.FromEvalError(result.Error);
            return $"{error.Code}: {error.Message} @ {error.Span}";
        }

        var expected = Observe(source, plans: false);
        Assert.Equal(expected, Observe(source, plans: true));
        Assert.Equal(expected, await ObserveAsync(source, plans: false));
        Assert.Equal(expected, await ObserveAsync(source, plans: true));
    }
}
