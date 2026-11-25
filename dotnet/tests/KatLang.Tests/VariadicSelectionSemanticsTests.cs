namespace KatLang.Tests;

/// <summary>
/// VARIADIC POSTFIX SELECTION — values (owner-approved October 2026; the retired colon form is
/// gone). <c>receiver[s1, …, sn]</c> selects one immediate element per supplied index, in supplied
/// order, repetitions repeating stored values, each element whole, and captures the selected values
/// by ordinary normalization of the RESULT GROUPING only: zero selections are <c>()</c>, one is the
/// selected value itself, several are ONE sequence of the selected values. Counting and selection
/// share ONE immediate positional view (numbers, Booleans and strings are one position each; an
/// empty list or sequence has none), so <c>first(v) ≡ v[0]</c> and <c>last(v) ≡ v[count(v) - 1]</c>
/// for every evaluated receiver value. Lean: <c>KatLangArityLaws.lean</c> § Variadic postfix
/// selection, <c>CoreTests/VariadicSelection.lean</c>. Demand order and effects live in
/// <see cref="VariadicSelectionDemandTests"/>, syntax in <see cref="PostfixSelectionSyntaxTests"/>.
/// </summary>
public class VariadicSelectionSemanticsTests
{
    private const string Data = "Data = [10, 20, 30]\n";
    private const string Nested = "Nested = [(10, 20), [30, 40], (), []]\n";

    private static string Display(string source)
    {
        SourceProvenance.ParseValid(source);
        var result = KatLangEngine.Run(source);
        Assert.True(result is RunResult.Success, $"Expected success but got: {result.ToDisplayString()}\nsource:\n{source}");
        return result.ToDisplayString().Replace("\r\n", "\n");
    }

    private static KatLangErrorCode EvalFailureCode(string source)
    {
        SourceProvenance.ParseValid(source);
        var result = KatLangEngine.Run(source);
        var failure = Assert.IsType<RunResult.EvalFailure>(result);
        return Assert.Single(failure.Errors).Code;
    }

    /// <summary>The outcome of a run as a comparable string: the displayed value, or the error code.</summary>
    private static string Outcome(string source)
    {
        SourceProvenance.ParseValid(source);
        return KatLangEngine.Run(source) switch
        {
            RunResult.Success success => "ok " + success.ToDisplayString().Replace("\r\n", "\n"),
            RunResult.EvalFailure failure => "err " + string.Join(",", failure.Errors.Select(static e => e.Code)),
            var other => "unexpected " + other.ToDisplayString(),
        };
    }

    // ── The issue's tables ───────────────────────────────────────────────────

    [Theory]
    [InlineData("Data[]", "()")]
    [InlineData("Data[0]", "10")]
    [InlineData("Data[0, 1]", "(10, 20)")]
    [InlineData("Data[2, 0]", "(30, 10)")]
    [InlineData("Data[2, 0, 2]", "(30, 10, 30)")]
    public void SelectionResults_FollowOrdinaryNormalizationOfTheResultGrouping(string row, string expected)
        => Assert.Equal(expected, Display(Data + row));

    [Theory]
    [InlineData("Nested[0]", "(10, 20)")]
    [InlineData("Nested[1]", "[30, 40]")]
    [InlineData("Nested[2]", "()")]
    [InlineData("Nested[3]", "[]")]
    [InlineData("Nested[0, 1]", "((10, 20), [30, 40])")]
    [InlineData("Nested[2, 3]", "((), [])")]
    [InlineData("Nested[2, 2]", "((), ())")]
    [InlineData("Nested[3, 0, 3]", "([], (10, 20), [])")]
    public void SelectedValues_StayWhole_EmptyValuesIncluded(string row, string expected)
        => Assert.Equal(expected, Display(Nested + row));

    [Fact]
    public void AnEmptySelection_IsTheEmptySequenceValue_NotTheReceiverNorAList()
    {
        // `Data[]` is `()`: as one argument it is ONE value, spread it supplies nothing.
        const string probe = Data + "Cnt(*xs) = xs.count\nColl(*xs) = xs\n";
        Assert.Equal("1", Display(probe + "Cnt(Data[])"));
        Assert.Equal("0", Display(probe + "Cnt(Data[]*)"));
        Assert.Equal("[()]", Display(probe + "Coll(Data[])"));
        Assert.Equal("[]", Display(probe + "[Data[]*]"));
        Assert.Equal("true", Display(Data + "Data[] == ()"));
        Assert.Equal("false", Display(Data + "Data[] == []"));
        Assert.Equal("false", Display(Data + "Data[] == Data"));
    }

    [Fact]
    public void BracketsDoNotRemoveSingletonNormalization()
    {
        // `Data[0]` is the selected pair itself, so a spread opens IT; no selection count
        // survives to recover an outer wrapper. An exact one-per-index list is written explicitly.
        const string pairs = "Data = [(10, 20), 30]\n";
        Assert.Equal("(10, 20)", Display(pairs + "Data[0]"));
        Assert.Equal("[10, 20]", Display(pairs + "[Data[0]*]"));
        Assert.Equal("[(10, 20)]", Display(pairs + "Indexes = [0]\nIndexes.map{Data[i]}"));
        Assert.Equal("[(10, 20), 30]", Display(pairs + "Indexes = [0, 1]\nIndexes.map{Data[i]}"));
    }

    [Fact]
    public void ASelectionResult_IsOneValue_NeverAnArgumentSupply()
    {
        const string add = Data + "Add(a, b) = a + b\n";
        Assert.Equal(KatLangErrorCode.ArityMismatch, EvalFailureCode(add + "Add(Data[0, 1])"));
        Assert.Equal("30", Display(add + "Add(Data[0, 1]*)"));
    }

    // ── The index supply: explicit spread only ───────────────────────────────

    [Theory]
    [InlineData("Indexes = [2, 0, 2]\nData[Indexes*]", "(30, 10, 30)")]
    [InlineData("Data[[0, 1]*]", "(10, 20)")]
    [InlineData("Indexes = []\nData[Indexes*]", "()")]
    [InlineData("Data[()*]", "()")]
    [InlineData("Data[1, [2, 0]*, 1]", "(20, 30, 10, 20)")]
    [InlineData("Data[[2]*, [0, 1]*]", "(30, 10, 20)")]
    [InlineData("Data[(0, 1)*]", "(10, 20)")]
    public void ExplicitSpreads_SupplyIndices(string rows, string expected)
        => Assert.Equal(expected, Display(Data + rows));

    [Theory]
    [InlineData("Data[(0, 1)]")]
    [InlineData("Data[[0, 1]]")]
    [InlineData("Data[()]")]
    [InlineData("Data[[]]")]
    [InlineData("Data['0']")]
    [InlineData("Data[true]")]
    public void ACollectionOrNonNumericSelector_IsOneValueOfTheWrongKind(string row)
        => Assert.Equal(KatLangErrorCode.TypeMismatch, EvalFailureCode(Data + row));

    [Theory]
    [InlineData("Data[3]")]
    [InlineData("Data[-1]")]
    [InlineData("Data[0.5]")]
    [InlineData("Data[3000000000]")]
    public void ANumberNamingNoPosition_IsBadIndex(string row)
        => Assert.Equal(KatLangErrorCode.BadIndex, EvalFailureCode(Data + row));

    [Theory]
    [InlineData("Data[1 / 0]", KatLangErrorCode.DivisionByZero)]
    [InlineData("Data[0, 1 / 0]", KatLangErrorCode.DivisionByZero)]
    [InlineData("Data[-true]", KatLangErrorCode.TypeMismatch)]
    [InlineData("Data[(1 / 0)*]", KatLangErrorCode.DivisionByZero)]
    public void ASelectorOperandFailure_KeepsItsOwnCategory(string row, KatLangErrorCode expected)
        // An operand failure is never relabeled as an index failure.
        => Assert.Equal(expected, EvalFailureCode(Data + row));

    // ── Receivers, grouping, chaining ────────────────────────────────────────

    [Theory]
    [InlineData("Data[0]")]
    [InlineData("(Data)[0]")]
    [InlineData("((Data))[0]")]
    [InlineData("Data()[0]")]
    [InlineData("BuildData(0)[1]")]
    [InlineData("[10, 20, 30][0]")]
    [InlineData("(10, 20, 30)[0]")]
    [InlineData("Data [0]")]
    [InlineData("Data()\t[0]")]
    public void EveryReceiverExpression_IsSelectable(string row)
        => Assert.Equal("10", Display(Data + "BuildData(n) = [n + 5, n + 10]\n" + row));

    [Fact]
    public void CommasSelectSiblings_ChainedBracketsDescend()
    {
        const string grid = "Grid = [[10, 20], [30, 40]]\n";
        Assert.Equal("([10, 20], [30, 40])", Display(grid + "Grid[0, 1]"));
        Assert.Equal("20", Display(grid + "Grid[0][1]"));
        Assert.Equal("20", Display(grid + "Grid [0] [1]"));
        Assert.Equal("(20, 10)", Display(grid + "Grid[0][1, 0]"));
        Assert.Equal("(10, 30)", Display(grid + "(Grid[0][0], Grid[1][0])"));
    }

    // `[]` is syntax, never a call: no user-visible name — `at`, `index`, `select`, `get`, as a
    // property, a parameter or an opened member — takes part in selection.
    [Theory]
    [InlineData("at(xs, i) = 99\nData = [10, 20]\nData[1]", "20")]
    [InlineData("at = 99\nData = [10, 20]\nData[0]", "10")]
    [InlineData("open { public at(xs, i) = 99 }\nData = [10, 20]\nData[0]", "10")]
    [InlineData("F(at) = [10, 20][1]\nF(5)", "20")]
    [InlineData("index(xs, i) = 99\nselect(xs, i) = 99\nget(xs, i) = 99\nData = [10, 20]\nData[1, 0]", "(20, 10)")]
    public void Selection_NeverResolvesAUserVisibleName(string source, string expected)
        => Assert.Equal(expected, Display(source));

    [Fact]
    public void SelectionTakesPartInThePostfixChain()
    {
        Assert.Equal("15", Display("BuildData(n) = [(n, n + 5), 0]\nBuildData(5)[0].sum"));
        Assert.Equal("-10", Display(Data + "-Data[0]"));
        Assert.Equal("100", Display(Data + "Data[0] ^ 2"));
        Assert.Equal("true", Display(Data + "Data[1].string == '20'"));
    }

    // ── One immediate positional view (count, first, last, selection) ───────

    [Theory]
    [InlineData("count('abc')", "1")]
    [InlineData("count('')", "1")]
    [InlineData("''[0]", "")]
    [InlineData("first('abc')", "abc")]
    [InlineData("last('abc')", "abc")]
    [InlineData("'abc'[0]", "abc")]
    [InlineData("count(42)", "1")]
    [InlineData("42[0]", "42")]
    [InlineData("true[0]", "true")]
    [InlineData("count(['abc', 'def'])", "2")]
    [InlineData("['abc', 'def'][1]", "def")]
    [InlineData("count([['a', 'b']])", "1")]
    [InlineData("[10, 20][0, 1]", "(10, 20)")]
    [InlineData("count([])", "0")]
    public void CountingAndSelection_ShareOneImmediatePositionalView(string row, string expected)
        => Assert.Equal(expected, Display(row));

    [Theory]
    [InlineData("'abc'[1]")]
    [InlineData("first([])")]
    [InlineData("[][0]")]
    [InlineData("()[0]")]
    [InlineData("last(())")]
    [InlineData("42[1]")]
    [InlineData("''[1]")]
    public void APositionTheViewDoesNotOffer_IsBadIndex(string row)
        => Assert.Equal(KatLangErrorCode.BadIndex, EvalFailureCode(row));

    public static TheoryData<string> Receivers() => new()
    {
        "42", "-0", "true", "'abc'", "''", "[10, 20, 30]", "[7]", "[]", "()", "(1, (2, 3))",
        "[(), []]", "['abc', 'def']", "[[1, 2]]", "((1, 2), [3])", "range(1, 4)", "{ 5, 6 }",
    };

    [Theory]
    [MemberData(nameof(Receivers))]
    public void FirstIsSelectionAtZero_LastIsSelectionAtCountMinusOne(string receiver)
    {
        // Over ONE evaluated value (a property holds it, so the laws compare values, never two
        // evaluations): same value, or the same BadIndex when the view has no positions.
        var v = $"V = {receiver}\n";
        Assert.Equal(Outcome(v + "first(V)"), Outcome(v + "V[0]"));
        Assert.Equal(Outcome(v + "last(V)"), Outcome(v + "V[count(V) - 1]"));
        Assert.Equal(Outcome(v + "V.first"), Outcome(v + "V[0]"));
    }

    [Theory]
    [MemberData(nameof(Receivers))]
    public void CountIsTheNumberOfSelectablePositions(string receiver)
    {
        var v = $"V = {receiver}\n";
        Assert.Equal("err BadIndex", Outcome(v + "V[count(V)]"));
        var count = int.Parse(Display(v + "count(V)"), System.Globalization.CultureInfo.InvariantCulture);
        if (count > 0)
            Assert.StartsWith("ok ", Outcome(v + "V[count(V) - 1]"), StringComparison.Ordinal);
    }

    // ── No callable identity ─────────────────────────────────────────────────

    [Fact]
    public void ASelection_HasNoCallableIdentity()
    {
        // A selection is never a call target in syntax, and passed where a callable is invoked it
        // has no callable identity.
        var parsed = SourceProvenance.ExpectFrontEndError("F(x) = x + 1\nFs = [F]\nFs[0](1)");
        Assert.Contains(parsed, static d => d.Code == DiagnosticCode.UnseparatedSameLineItem);
        Assert.Equal(KatLangErrorCode.NotAnAlgorithm,
            EvalFailureCode("Inc(x) = x + 1\nApply(f, x) = f(x)\nFs = (1, 2)\nApply(Fs[0], 3)"));
    }

    [Fact]
    public void ADotCallOnASelection_IsTheExtensionCallOnTheSelectedValue()
    {
        Assert.Equal(Display(Data + "Twice(x) = x * 2\nTwice(Data[1])"), Display(Data + "Twice(x) = x * 2\nData[1].Twice"));
        Assert.Equal("(20, 40)", Display(Data + "Pair(a, b) = a * 2, b * 2\nData[0, 1]*.Pair"));
    }
}
