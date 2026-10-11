using System.Globalization;

namespace KatLang.Tests.Interpolation;

/// <summary>
/// STR-02 value semantics (VAL-12): an interpolated string is ONE string value whose text is
/// the head, then each hole's STRUCTURAL VALUE TEXT followed by its link's text. Numbers are
/// their canonical culture-invariant text (never display decimals or a formatter), Booleans
/// <c>true</c>/<c>false</c>, strings verbatim and UNQUOTED at every nesting level, sequences
/// <c>(a, b)</c>, lists <c>[a, b]</c>, <c>()</c> and <c>[]</c> distinct; nothing is spread,
/// flattened, quoted or re-parsed. The text is human-readable, not a serialization.
/// </summary>
public class InterpolationSemanticsTests
{
    internal static string Text(string source)
    {
        var result = SourceProvenance.ParseValid(source).Evaluate();
        Assert.False(result.IsError, result.IsError ? KatLangError.FromEvalError(result.Error).Message : null);
        return Assert.IsType<Result.Str>(result.Value).Value;
    }

    private static string Display(string source, RunOptions? options = null)
        => Assert.IsType<RunResult.Success>(KatLangEngine.Run(source, options)).ToDisplayString();

    [Theory]
    [InlineData("\"{1}\"", "1")]
    [InlineData("\"{1.5}\"", "1.5")]
    [InlineData("\"{1.50}\"", "1.50")]
    [InlineData("\"{-2}\"", "-2")]
    [InlineData("\"{10 / 4}\"", "2.5")]
    [InlineData("\"{0.1 + 0.2}\"", "0.3")]
    [InlineData("\"{1000000}\"", "1000000")]
    [InlineData("\"{true}\"", "true")]
    [InlineData("\"{1 > 2}\"", "false")]
    [InlineData("\"{'text'}\"", "text")]
    [InlineData("\"{''}\"", "")]
    [InlineData("\"{(1, 2)}\"", "(1, 2)")]
    [InlineData("\"{[1, 2]}\"", "[1, 2]")]
    [InlineData("\"{()}\"", "()")]
    [InlineData("\"{[]}\"", "[]")]
    [InlineData("\"{[()]}\"", "[()]")]
    [InlineData("\"{[[]]}\"", "[[]]")]
    [InlineData("\"{((1, 2), 3)}\"", "((1, 2), 3)")]
    [InlineData("\"{[[1], (2, 3)]}\"", "[[1], (2, 3)]")]
    [InlineData("\"{('a', 'b')}\"", "(a, b)")]
    [InlineData("\"{['one, two', 'three']}\"", "[one, two, three]")]
    [InlineData("\"{[('x', 1), ['y', true]]}\"", "[(x, 1), [y, true]]")]
    [InlineData("\"{range(1, 3)}\"", "[1, 2, 3]")]
    public void EveryValueKind_IsItsStructuralText(string source, string text)
        => Assert.Equal(text, Text(source));

    [Theory]
    [InlineData("\"a{1}b{2}c\"", "a1b2c")]
    [InlineData("\"{1}{2}\"", "12")]
    [InlineData("\"<{\"[{1}]\"}>\"", "<[1]>")]
    [InlineData("\"{{{1}}}\"", "{1}")]
    [InlineData("\"{'{x}'}\"", "{x}")]
    [InlineData("\"{'a\\nb'}\"", "a\\nb")]
    [InlineData("\"{\"q\\\"\"}\"", "q\"")]
    [InlineData("\"{'\"'}\"", "\"")]
    [InlineData("\"tab\\there\"", "tab\there")]
    [InlineData("\"line\\nbreak\"", "line\nbreak")]
    [InlineData("\"back\\\\slash\"", "back\\slash")]
    public void TextAndHoles_Concatenate_AndInsertedStringsAreNeverReparsedOrRequoted(string source, string text)
        => Assert.Equal(text, Text(source));

    [Fact]
    public void SingleQuotedStrings_KeepTheirRawMeaning()
    {
        Assert.Equal("a\\nb", Text("'a\\nb'"));
        Assert.Equal("{x}", Text("'{x}'"));
        Assert.Equal("\"", Text("'\"'"));
    }

    [Theory]
    [InlineData("P = 1, 2\n\"{P}\"", "(1, 2)")]
    [InlineData("xs = [1, 2]\n\"{xs}\"", "[1, 2]")]
    [InlineData("xs = [1, 2]\n\"{(xs*)}\"", "(1, 2)")]
    [InlineData("xs = [1, 2]\n\"{(xs*, 3)}\"", "(1, 2, 3)")]
    [InlineData("xs = [[1, 2]]\n\"{(xs:0)}\"", "[1, 2]")]
    [InlineData("Pair = (1, (2, 3))\n\"{Pair}\"", "(1, (2, 3))")]
    public void AHoleValue_IsNeverSpreadOrFlattened(string source, string text)
        => Assert.Equal(text, Text(source));

    [Fact]
    public void ANumberHole_IsTheCanonicalInvariantText_ExactlyLikeTheNumbersOwnStringConversion()
    {
        foreach (var number in new[] { "0", "-0", "1.50", "10 ^ 30", "0.000001", "1 / 3", "2 ^ 100", "-7.25", "123456789012345678901234567890", "1 / 0.0000001" })
            Assert.Equal(Text($"({number}).string"), Text($"\"{{{number}}}\""));
    }

    [Fact]
    public void ANumberHole_IgnoresTheSourceAndHostDisplayDecimals()
    {
        Assert.Equal("1.5|1.50", Display("DisplayDecimals = 2\n\"{1.5}|{(1.50).string}\""));
        Assert.Equal("1.50", Display("DisplayDecimals = 2\n1.5"));
        Assert.Equal("1.5", Display("\"{1.5}\"", new RunOptions { DefaultDisplayDecimals = 0 }));
    }

    [Fact]
    public void ANumberHole_IgnoresTheCurrentCulture()
    {
        var original = CultureInfo.CurrentCulture;
        try
        {
            CultureInfo.CurrentCulture = CultureInfo.GetCultureInfo("de-DE");
            Assert.Equal("1.5 [1000000, 2.25]", Text("\"{1.5} {[1000000, 2.25]}\""));
        }
        finally
        {
            CultureInfo.CurrentCulture = original;
        }
    }

    [Fact]
    public void AUserStringMember_NeverHijacksTheNumberText()
    {
        Assert.Equal("3", Text("string(x) = 99\n\"{3}\""));
        Assert.Equal("[3]", Text("string(x) = 99\n\"{[3]}\""));
    }

    [Fact]
    public void TheResult_IsAnOrdinaryStringValue()
    {
        AssertEvalBool("\"{1}{2}\" == '12'", true);
        AssertEvalBool("\"abc\" == 'abc'", true);
        AssertEvalBool("\"a{1}\" != 'a1'", false);
        AssertEvalBool("contains(('x', 'y'), \"y\")", true);
        Assert.Equal("1", Text("(\"a\", 'a').distinct.count.string"));
        Assert.Equal("ab", Text("x = \"a{'b'}\"\nx"));
    }

    private static void AssertEvalBool(string source, bool expected)
    {
        var result = SourceProvenance.ParseValid(source).Evaluate();
        Assert.False(result.IsError, result.IsError ? KatLangError.FromEvalError(result.Error).Message : null);
        Assert.Equal(expected, Assert.IsType<Result.Bool>(result.Value).Value);
    }

    [Fact]
    public void AnInterpolatedString_EmitsOneValue()
    {
        var parsed = SourceProvenance.ParseValid("\"{(1, 2)}\", \"{()}\"");
        var counted = Evaluator.RunCounted(new Expr.AlgorithmExpr(parsed.Root));
        Assert.False(counted.IsError);
        var rows = Assert.IsType<Result.SequenceValue>(counted.Value.Value).Items;
        Assert.Equal(new[] { "(1, 2)", "()" }, rows.Select(r => Assert.IsType<Result.Str>(r).Value));
    }

    [Fact]
    public void AHoleWithoutOutput_IsItsMissingOutputError()
    {
        SourceProvenance.ParseValid("B = { A = 1 }\n\"{B}\"").ExpectEvaluationError<EvalError.MissingOutput>();
        SourceProvenance.ParseValid("\"x{ { A = 1 } }\"").ExpectEvaluationError<EvalError.MissingOutput>();
    }

    [Fact]
    public void AHoleFailure_IsTheHolesOwnError_PositionedAtTheHole()
    {
        var error = SourceProvenance.ParseValid("\"ab{1 div 0}\"").ExpectEvaluationError<EvalError.DivByZero>();
        Assert.Equal(new SourceSpan(1, 5, 1, 12), error.Span);
        var typeError = SourceProvenance.ParseValid("\"{-'a'}\"").ExpectEvaluationError<EvalError.TypeMismatch>();
        Assert.Equal(1, Assert.NotNull(typeError.Span).Start.Line);
    }

    [Fact]
    public void AnInterpolatedString_IsNotCallable_AndNotANumber()
    {
        SourceProvenance.ParseValid("\"{1}\" + 1").ExpectEvaluationError<EvalError.TypeMismatch>();
        SourceProvenance.ParseValid("map([1], \"{1}\")").ExpectEvaluationError<EvalError.NotAnAlgorithm>();
    }

    [Fact]
    public void Display_ShowsTheStringRaw_AtTheRootAndUnquotedInsideAValue()
    {
        Assert.Equal("a\"b", Display("\"a\\\"b\""));
        Assert.Equal("[x1, y]", Display("[\"x{1}\", 'y']"));
    }
}
