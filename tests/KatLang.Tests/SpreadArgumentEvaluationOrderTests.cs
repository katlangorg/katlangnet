using KatLang.Evaluation.Caching;

namespace KatLang.Tests;

/// <summary>
/// Written-argument-slot evaluation ORDER for builtins that expand spread
/// arguments (<c>Evaluator.ExpandSequenceSpreadBuiltinArguments</c> /
/// Lean <c>expandSequenceSpreadBuiltinArguments</c>).
///
/// <para>The rule pinned here: SPREAD-MARKED slots are forced exactly once, in
/// left-to-right written order, and expanding a spread slot is part of evaluating
/// that slot. Non-spread builtin slots keep their written position but remain
/// algorithm-lazy — the builtin decides whether and when to evaluate them (see
/// <see cref="SpreadSlotsAreForcedDuringExpansion_NonSpreadBuiltinSlotsStayLazy"/>).
/// Lean's expansion recursed into the remaining slots BEFORE evaluating the current
/// spread slot, so two failing spread arguments reported the RIGHTMOST failure while
/// C# reported the leftmost: <c>P = 1 / 0</c>, <c>Q = 'x' + 1</c>,
/// <c>range(P*, Q*)</c> was a division-by-zero in C# and a type mismatch in Lean.
/// C# was correct; these tests pin the language behavior on the C# side while the
/// generated Lean guards (<c>spread-arguments-fail-left-to-right</c> and
/// <c>spread-arguments-keep-written-order</c> in
/// <c>tests/KatLang.Tests/LanguageSpec/LanguageSpecCorpus.cs</c>, plus the
/// <c>spreadBuiltinArgument*</c> guards in <c>lean/CoreTests.lean</c>) pin the same
/// behavior on the Lean side.</para>
/// </summary>
public class SpreadArgumentEvaluationOrderTests
{
    private const string FailingSlots = "P = 1 / 0\nQ = 'x' + 1\n";

    private static Expr Program(string source) => new Expr.Block(Parser.Parse(source).Root);

    private static EvalResult<Result> Eval(string source) => Evaluator.Run(Program(source));

    private static EvalError Innermost(EvalError error)
    {
        while (error is EvalError.WithContext context)
            error = context.Inner;

        return error;
    }

    private static EvalError AssertFails(string source)
    {
        var result = Eval(source);
        Assert.True(result.IsError, $"Expected `{source}` to fail but got: {(result.IsError ? null : result.Value)}");
        return result.Error;
    }

    // ── The leftmost written spread slot's failure wins ──────────────────────

    /// <summary>
    /// Each case is (source, expected innermost error type). Two spread arguments
    /// fail with DIFFERENT errors, so the reported error identifies which slot was
    /// evaluated first. The mirrored spelling of every case pins the rule as an
    /// order rule rather than an error-precedence rule.
    /// </summary>
    public static TheoryData<string, bool> CompetingSpreadFailures()
    {
        var data = new TheoryData<string, bool>();

        // Leftmost is P (division by zero).
        data.Add($"{FailingSlots}range(P*, Q*)", true);
        data.Add($"{FailingSlots}if(P*, Q*, 0)", true);
        data.Add($"{FailingSlots}repeat(P*, Q*, 1)", true);
        data.Add($"{FailingSlots}while(P*, Q*)", true);

        // Leftmost is Q (type mismatch).
        data.Add($"{FailingSlots}range(Q*, P*)", false);
        data.Add($"{FailingSlots}if(Q*, P*, 0)", false);
        data.Add($"{FailingSlots}repeat(Q*, P*, 1)", false);
        data.Add($"{FailingSlots}while(Q*, P*)", false);

        return data;
    }

    [Theory]
    [MemberData(nameof(CompetingSpreadFailures))]
    public void CompetingSpreadArguments_ReportTheLeftmostWrittenSlotsFailure(string source, bool expectDivisionByZero)
    {
        var innermost = Innermost(AssertFails(source));

        if (expectDivisionByZero)
            Assert.IsType<EvalError.DivByZero>(innermost);
        else
            Assert.IsType<EvalError.TypeMismatch>(innermost);
    }

    [Fact]
    public void SpreadSlotsAreForcedDuringExpansion_NonSpreadBuiltinSlotsStayLazy()
    {
        // Established (pre-existing) asymmetry, pinned here so the order rule above is
        // not mistaken for a claim about every builtin argument slot: a builtin's
        // NON-SPREAD slots stay algorithm-lazy and are forced only when the builtin
        // consumes them (that laziness is what lets `if` skip the unselected branch),
        // while a SPREAD slot MUST be evaluated during expansion because its item
        // count decides the supplied argument count. So the forced spread slot's
        // failure is reported even when a lazy non-spread slot is written to its left.
        Assert.IsType<EvalError.TypeMismatch>(Innermost(AssertFails($"{FailingSlots}range(1 / 0, Q*)")));
        Assert.IsType<EvalError.DivByZero>(Innermost(AssertFails($"{FailingSlots}range('x' + 1, P*)")));

        // ... and among the FORCED slots, written order still decides.
        Assert.IsType<EvalError.DivByZero>(Innermost(AssertFails($"{FailingSlots}range(P*, 'x' + 1)")));
        Assert.IsType<EvalError.TypeMismatch>(Innermost(AssertFails($"{FailingSlots}range(Q*, 1 / 0)")));
    }

    [Fact]
    public void SucceedingLeftSpreadSlot_IsEvaluatedBeforeAFailingRightSpreadSlot()
    {
        // The narrow ordering guard: the FIRST spread slot succeeds and performs
        // observable, cacheable work (a zero-argument property access that is stored in
        // the run's cache), and the second fails. Evaluating the second slot first
        // would abort the expansion before the first slot's property was ever
        // evaluated, so nothing would be STORED. (A failed property access is still
        // requested and still misses; only a successful one is stored.)
        var source = """
            Good = 41 + 1
            Bad = 'x' + 1
            range(Good*, Bad*)
            """;

        var cache = new RunScopedZeroArgPropertyResultCache();
        var result = Evaluator.Run(Program(source), cache);

        Assert.True(result.IsError);
        Assert.IsType<EvalError.TypeMismatch>(Innermost(result.Error));

        var stats = cache.GetSnapshot();
        Assert.Equal(2, stats.TotalRequests);
        Assert.Equal(2, stats.Misses);
        Assert.Equal(1, stats.Stores);
        Assert.Equal(0, stats.Hits);

        // Control: with the failing slot written FIRST, the succeeding slot is never
        // reached, so exactly one property is requested and nothing is stored.
        var reversedCache = new RunScopedZeroArgPropertyResultCache();
        var reversed = Evaluator.Run(
            Program("Good = 41 + 1\nBad = 'x' + 1\nrange(Bad*, Good*)"),
            reversedCache);

        Assert.True(reversed.IsError);
        Assert.IsType<EvalError.TypeMismatch>(Innermost(reversed.Error));

        var reversedStats = reversedCache.GetSnapshot();
        Assert.Equal(1, reversedStats.TotalRequests);
        Assert.Equal(1, reversedStats.Misses);
        Assert.Equal(0, reversedStats.Stores);
    }

    [Fact]
    public void SpreadArgumentSlots_AreEvaluatedExactlyOnce()
    {
        // A spread slot whose operand is a zero-argument property is requested once
        // per written slot, never twice: expansion evaluates the slot and reuses the
        // expanded values. Two DISTINCT properties give two requests; the same
        // property written twice gives two requests of which the second is a cache hit
        // (the established `A` property-access rule), and never four.
        var distinctCache = new RunScopedZeroArgPropertyResultCache();
        var distinct = Evaluator.Run(
            Program("Lo = 1 + 1\nHi = 2 + 2\nrange(Lo*, Hi*)"),
            distinctCache);

        Assert.False(distinct.IsError, $"Expected success but got: {(distinct.IsError ? distinct.Error : null)}");
        Assert.Equal([2m, 3m, 4m], distinct.Value.ToHostAtoms());

        var distinctStats = distinctCache.GetSnapshot();
        Assert.Equal(2, distinctStats.TotalRequests);
        Assert.Equal(2, distinctStats.Misses);
        Assert.Equal(2, distinctStats.Stores);
        Assert.Equal(0, distinctStats.Hits);

        var repeatedCache = new RunScopedZeroArgPropertyResultCache();
        var repeated = Evaluator.Run(Program("N = 1 + 1\nrange(N*, N*)"), repeatedCache);

        Assert.False(repeated.IsError, $"Expected success but got: {(repeated.IsError ? repeated.Error : null)}");
        Assert.Equal([2m], repeated.Value.ToHostAtoms());

        var repeatedStats = repeatedCache.GetSnapshot();
        Assert.Equal(2, repeatedStats.TotalRequests);
        Assert.Equal(1, repeatedStats.Misses);
        Assert.Equal(1, repeatedStats.Stores);
        Assert.Equal(1, repeatedStats.Hits);
    }

    // ── Expanded argument VALUES keep the written order ──────────────────────

    [Theory]
    // Two spread slots, one item each.
    [InlineData("Lo = 2\nHi = 4\nrange(Lo*, Hi*)", new[] { 2, 3, 4 })]
    [InlineData("Lo = 2\nHi = 4\nrange(Hi*, Lo*)", new[] { 4, 3, 2 })]
    // One spread slot supplying both arguments.
    [InlineData("Bounds = 2, 4\nrange(Bounds*)", new[] { 2, 3, 4 })]
    [InlineData("Bounds = 4, 2\nrange(Bounds*)", new[] { 4, 3, 2 })]
    // A spread slot mixed with a non-spread slot on either side.
    [InlineData("Lo = 2\nrange(Lo*, 4)", new[] { 2, 3, 4 })]
    [InlineData("Hi = 4\nrange(2, Hi*)", new[] { 2, 3, 4 })]
    public void ExpandedSpreadArguments_PreserveWrittenOrder(string source, int[] expected)
    {
        var result = Eval(source);
        Assert.False(result.IsError, $"Expected `{source}` to succeed but got: {(result.IsError ? result.Error : null)}");
        Assert.Equal(expected.Select(static value => (decimal)value), result.Value.ToHostAtoms());
    }

    [Fact]
    public void ExpandedSpreadArguments_SelectTheIfBranchByWrittenPosition()
    {
        // `if` reads its expanded slots positionally, so a mis-ordered expansion would
        // pick the wrong branch rather than merely reorder a list.
        AssertSingleAtom("Cond = 1\nThen = 7\nElse = 9\nif(Cond*, Then*, Else*)", 7m);
        AssertSingleAtom("Cond = 0\nThen = 7\nElse = 9\nif(Cond*, Then*, Else*)", 9m);
        AssertSingleAtom("Cond = 1\nThen = 7\nElse = 9\nif(Cond*, Else*, Then*)", 9m);
    }

    private static void AssertSingleAtom(string source, decimal expected)
    {
        var result = Eval(source);
        Assert.False(result.IsError, $"Expected `{source}` to succeed but got: {(result.IsError ? result.Error : null)}");
        Assert.Equal([expected], result.Value.ToHostAtoms());
    }
}
