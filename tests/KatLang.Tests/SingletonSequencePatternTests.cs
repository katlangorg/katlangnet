namespace KatLang.Tests;

/// <summary>
/// THE SINGLETON RULE (September 2026, structural patterns): KatLang has no one-item sequence
/// value — a one-item sequence IS its item — so a SEQUENCE pattern with exactly one
/// non-collecting item describes a boundary no value has and could never match. Such a pattern
/// is a front-end error (<see cref="DiagnosticCode.SingletonSequencePattern"/>) at every nesting
/// level of a clause head, in ordinary definitions and clause families alike; the one-element
/// structural pattern is the LIST pattern <c>[x]</c>, a plain name binds a whole value, and the
/// collector-only <c>(*xs)</c> stays valid because a collector is variadic. The head's own
/// parentheses are the call's argument list, never a sequence pattern, and expression grouping
/// is untouched (<c>(x)</c> in an expression IS <c>x</c>). A host-built tree holding such a
/// pattern is rejected before evaluation (<see cref="EvalError.IllegalInEval"/>), exactly as the
/// Lean model's <c>validateExplicitParamOutputInvariant</c> rejects it.
/// </summary>
public class SingletonSequencePatternTests
{
    private static IReadOnlyList<Diagnostic> SingletonDiagnostics(string source)
        => SourceProvenance.ExpectFrontEndError(source)
            .Where(static diagnostic => diagnostic.Code == DiagnosticCode.SingletonSequencePattern)
            .ToList();

    public static TheoryData<string> InvalidHeads => new()
    {
        "F((x)) = x\nF(7)",
        "F(((x))) = x\nF(7)",
        "F((((x)))) = x\nF(7)",
        "F(([x])) = x\nF([1])",
        "F(((x, y))) = x\nF((1, 2))",
        "F(((true))) = 1\nF(true)",
        "F(((1))) = 1\nF(1)",
        "F(('a')) = 1\nF('a')",
        "F((-1)) = 1\nF(-1)",
        // Nested positions: inside a list pattern, inside a larger sequence pattern, beside
        // other parameters, and after a collector.
        "F([(x)]) = x\nF([7])",
        "F((x, (y))) = x\nF((1, 2))",
        "F(((x), y)) = x\nF((1, 2))",
        "F(a, (b)) = a\nF(1, 2)",
        "F((b), a) = a\nF(1, 2)",
        "F(*r, (b)) = b\nF(1, 2)",
        "F([x, (y)]) = x\nF([1, 2])",
        "F((*r, (y))) = y\nF((1, 2))",
    };

    [Theory]
    [MemberData(nameof(InvalidHeads))]
    public void OrdinaryDefinition_WithAOneItemSequencePattern_IsASingletonSequencePatternError(string source)
    {
        var singletons = SingletonDiagnostics(source);
        Assert.Single(singletons);
        Assert.Equal(DiagnosticSeverity.Error, singletons[0].Severity);
        Assert.Contains("one-item sequence value", singletons[0].Message, StringComparison.Ordinal);
    }

    [Theory]
    [MemberData(nameof(InvalidHeads))]
    public void TheSingletonError_IsTheHostFacingSingletonSequencePatternCode(string source)
    {
        var failure = Assert.IsType<RunResult.ParseFailure>(KatLangEngine.Run(source));
        Assert.Contains(failure.Errors, static error => error.Code == KatLangErrorCode.SingletonSequencePattern);
    }

    public static TheoryData<string> InvalidFamilyHeads => new()
    {
        // A clause family follows the same rule: `(x)` never takes a non-sequence value whole.
        "Whole((x)) = x\nWhole(0) = 'zero'\nWhole(7)",
        "G(0) = 0\nG((x)) = x\nG(7)",
        "H([(x)]) = x\nH(0) = 0\nH(0)",
        "K(((1, y))) = y\nK(z) = z\nK(3)",
    };

    [Theory]
    [MemberData(nameof(InvalidFamilyHeads))]
    public void ClauseFamily_WithAOneItemSequencePattern_IsASingletonSequencePatternError(string source)
        => Assert.Single(SingletonDiagnostics(source));

    public static TheoryData<string, string> ValidHeads => new()
    {
        // The collector-only sequence pattern is valid: a collector is variadic.
        { "F((*xs)) = xs\nF((1, 2)), F(())", "[1, 2]\n[]" },
        // The one-element structural pattern is the list pattern, at every depth.
        { "F([x]) = x\nF([7])", "7" },
        { "F([[x]]) = x\nF([[7]])", "7" },
        { "F([(x, y)]) = x\nF([(1, 2)])", "1" },
        // Empty and multi-item sequence patterns, and the head's own parentheses.
        { "F(()) = 0\nF(())", "0" },
        { "F([]) = 0\nF([])", "0" },
        { "F((x, y)) = x\nF((1, 2))", "1" },
        { "F(((x, y), z)) = z\nF(((1, 2), 3))", "3" },
        { "F(([x], y)) = x\nF(([1], 2))", "1" },
        { "F(x) = x\nF(7)", "7" },
        { "F((*xs), y) = y\nF((), 5)", "5" },
        // Expression grouping is untouched: `(x)` in an expression is `x`.
        { "F(x) = (x)\nA = (7)\nF(A), ((A))", "7\n7" },
    };

    [Theory]
    [MemberData(nameof(ValidHeads))]
    public void ValidStructuralPatterns_ParseCleanly_AndRun(string source, string expected)
    {
        SourceProvenance.ParseValid(source);
        var result = Assert.IsType<RunResult.Success>(KatLangEngine.Run(source));
        Assert.Equal(expected, result.ToDisplayString().ReplaceLineEndings("\n"));
    }

    [Fact]
    public void TheDiagnostic_CoversThePatternsParentheses()
    {
        // `F((x)) = x`: the invalid pattern is the inner `(x)` at columns 3 through 5.
        var singleton = Assert.Single(SingletonDiagnostics("F((x)) = x\nF(7)"));
        Assert.Equal(new SourcePosition(1, 3), singleton.Span!.Value.Start);
        Assert.Equal(new SourcePosition(1, 6), singleton.Span!.Value.End);

        // A nested singleton: `F(a, ((x, y)))` — the outer `((x, y))` is the singleton, while
        // its item `(x, y)` is a valid pair pattern.
        var nested = Assert.Single(SingletonDiagnostics("F(a, ((x, y))) = a\nF(1, (2, 3))"));
        Assert.Equal(new SourcePosition(1, 6), nested.Span!.Value.Start);
        Assert.Equal(new SourcePosition(1, 14), nested.Span!.Value.End);

        // Inside a list pattern, the sequence pattern alone is blamed.
        var inList = Assert.Single(SingletonDiagnostics("F([1, (x)]) = x\nF([1, 2])"));
        Assert.Equal(new SourcePosition(1, 7), inList.Span!.Value.Start);
        Assert.Equal(new SourcePosition(1, 10), inList.Span!.Value.End);
    }

    [Fact]
    public void DeeplyNestedSingletons_ReportOnce_AtTheInnermostGroup()
    {
        // `F((((x)))) = x`: each enclosing group holds one item too, but the innermost report
        // owns the region — a cleanly parsed group only is checked, so nothing cascades.
        var singleton = Assert.Single(SingletonDiagnostics("F((((x)))) = x\nF(7)"));
        Assert.Equal(new SourcePosition(1, 5), singleton.Span!.Value.Start);
        Assert.Equal(new SourcePosition(1, 8), singleton.Span!.Value.End);
    }

    [Fact]
    public void AMalformedItem_DoesNotCascadeIntoASingletonError()
    {
        // A detached collect marker is its own error; the recovered fixed binding does not add
        // a second, singleton diagnostic for the same written group.
        var diagnostics = SourceProvenance.ExpectFrontEndError("F((* xs)) = xs\nF((1, 2))");
        Assert.Contains(diagnostics, static diagnostic => diagnostic.Code == DiagnosticCode.InvalidCollectMarker);
        Assert.DoesNotContain(diagnostics, static diagnostic => diagnostic.Code == DiagnosticCode.SingletonSequencePattern);

        // A trailing separator is a missing-item error, never a singleton.
        var trailing = SourceProvenance.ExpectFrontEndError("F((x,)) = x\nF((1, 2))");
        Assert.DoesNotContain(trailing, static diagnostic => diagnostic.Code == DiagnosticCode.SingletonSequencePattern);
    }

    [Fact]
    public void TheHeadsOwnParentheses_AreNeverASequencePattern()
    {
        // `F(x)` has one parameter; the head's parentheses are the call's argument list.
        SourceProvenance.ParseValid("F(x) = x\nF(7)");
        SourceProvenance.ParseValid("F(0) = 0\nF(x) = x\nF(7)");
    }

    // ── Host-built trees: the pre-evaluation rejection (Lean validateExplicitParamOutputInvariant) ──

    private static CaptureParameterPattern Capture(string name, ParameterKind kind = ParameterKind.Normal)
        => new(name, Span: null, kind);

    private static Expr.AlgorithmExpr ProgramCalling(Algorithm callee, params Expr[] arguments)
        => new(new Algorithm.User(
            Parent: null,
            ParameterPatterns: [],
            Opens: [],
            Properties: [new Property("F", callee)],
            Output: [new Expr.Call(new Expr.Resolve("F"), new OutputBundle(arguments))]));

    private static void AssertRejectedBeforeEvaluation(EvalResult<Result> result)
    {
        Assert.True(result.IsError, "A host-built singleton sequence pattern must be rejected.");
        var error = result.Error;
        while (error is EvalError.WithContext context)
            error = context.Inner;
        var illegal = Assert.IsType<EvalError.IllegalInEval>(error);
        Assert.Equal(Parser.SingletonSequencePatternDiagnostic, illegal.Reason);
    }

    [Fact]
    public async Task HostBuiltOrdinaryPattern_WithAOneItemSequence_IsRejectedBeforeEvaluation()
    {
        var callee = new Algorithm.User(
            Parent: null,
            ParameterPatterns: [new ListValueParameterPattern([new SequenceValueParameterPattern([Capture("x")])])],
            Opens: [],
            Properties: [],
            Output: [new Expr.Param("x")])
        { HasExplicitParameterList = true };
        var program = ProgramCalling(callee, new Expr.ListLiteral(new OutputBundle([new Expr.Num(7)])));

        AssertRejectedBeforeEvaluation(Evaluator.Run(program));
        AssertRejectedBeforeEvaluation(await Evaluator.RunAsync(program));
    }

    [Fact]
    public void HostBuiltFamilyHead_WithAOneItemSequence_IsRejectedBeforeEvaluation()
    {
        var family = new Algorithm.Conditional(
            null,
            [],
            [
                new CondBranch(
                    new Pattern.SequenceValue([new Pattern.SequenceValue([new Pattern.Bind("x")])]),
                    new Algorithm.User(Parent: null, ParameterPatterns: [], Opens: [], Properties: [], Output: [new Expr.Param("x")])),
            ]);

        AssertRejectedBeforeEvaluation(Evaluator.Run(ProgramCalling(family, new Expr.Num(7))));
    }

    [Fact]
    public void HostBuiltCollectorOnlyAndListPatterns_AreValid()
    {
        var collector = new Algorithm.User(
            Parent: null,
            ParameterPatterns: [new SequenceValueParameterPattern([Capture("xs", ParameterKind.Collecting)])],
            Opens: [],
            Properties: [],
            Output: [new Expr.Param("xs")])
        { HasExplicitParameterList = true };
        var pair = new Expr.Capture(new OutputBundle([new Expr.Num(1), new Expr.Num(2)]));
        var result = Evaluator.Run(ProgramCalling(collector, pair));
        Assert.True(result.IsOk, result.IsError ? result.Error.ToString() : null);
        var list = Assert.IsType<Result.ListValue>(result.Value);
        Assert.Equal([new Result.Atom(1), new Result.Atom(2)], list.Items);
    }
}
