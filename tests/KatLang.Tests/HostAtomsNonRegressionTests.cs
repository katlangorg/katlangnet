namespace KatLang.Tests;

/// <summary>
/// Non-regression pins for the host-boundary numeric flattening contract
/// (<see cref="Result.ToHostAtoms"/>, Lean: <c>Result.hostAtoms</c>) and its
/// host API surface (<c>Evaluator.RunFlat</c>, <c>KatLangEngine.EvaluateToAtoms</c>).
/// Host flattening opens BOTH sequence and list boundaries recursively,
/// left-to-right, omits strings, and returns plain host decimals — never a
/// KatLang collection value. The language-level `atoms` builtin materializes a
/// KatLang list value instead; the two contracts must stay distinct, so this
/// file must not change when builtin semantics change.
/// </summary>
public class HostAtomsNonRegressionTests
{
    private static Result Atom(decimal value) => new Result.Atom(value);

    private static Result Str(string value) => new Result.Str(value);

    private static Result SequenceValue(params Result[] items) => new Result.SequenceValue(items);

    private static Result ListValue(params Result[] items) => new Result.ListValue(items);

    [Fact]
    public void ToHostAtoms_Number_IsSingleton()
        => Assert.Equal([7m], Atom(7).ToHostAtoms());

    [Fact]
    public void ToHostAtoms_String_IsOmitted()
        => Assert.Empty(Str("text").ToHostAtoms());

    [Fact]
    public void ToHostAtoms_EmptyStructures_AreEmpty()
    {
        Assert.Empty(SequenceValue().ToHostAtoms());
        Assert.Empty(ListValue().ToHostAtoms());
    }

    [Fact]
    public void ToHostAtoms_Sequence_FlattensRecursively()
        => Assert.Equal(
            [1m, 2m, 3m],
            SequenceValue(Atom(1), SequenceValue(Atom(2), Atom(3))).ToHostAtoms());

    [Fact]
    public void ToHostAtoms_List_FlattensRecursively()
        => Assert.Equal(
            [1m, 2m, 3m],
            ListValue(Atom(1), ListValue(Atom(2), Atom(3))).ToHostAtoms());

    [Fact]
    public void ToHostAtoms_MixedStructures_FlattenLeftToRight()
    {
        Assert.Equal(
            [3m, 1m, 4m, 2m],
            ListValue(Atom(3), SequenceValue(Atom(1), ListValue(Atom(4), Atom(2)))).ToHostAtoms());
        Assert.Equal(
            [1m, 2m, 3m, 4m],
            SequenceValue(Atom(1), ListValue(Atom(2), SequenceValue(Atom(3), ListValue(Atom(4))))).ToHostAtoms());
    }

    [Fact]
    public void ToHostAtoms_MixedContent_OmitsStringsOnly()
        => Assert.Equal(
            [1m, 2m],
            SequenceValue(Str("a"), Atom(1), ListValue(Str("b"), Atom(2))).ToHostAtoms());

    [Fact]
    public void EvaluateToAtoms_FlattensListResultsForHosts()
    {
        Assert.Equal([1m, 2m, 3m], KatLangEngine.EvaluateToAtoms("range(1, 3)"));
        Assert.Equal([2m, 3m], KatLangEngine.EvaluateToAtoms("[1, 2, 3].skip(1)"));
        Assert.Equal([1m, 2m, 3m, 4m], KatLangEngine.EvaluateToAtoms("[[1, 2], [3, 4]]"));
    }

    [Fact]
    public void RunFlat_FlattensListResultsForHosts()
    {
        var parseResult = Parser.Parse("[1, [2, (3, [4])]]");
        Assert.False(parseResult.HasErrors);
        var result = Evaluator.RunFlat(new Expr.Block(parseResult.Root));
        Assert.False(result.IsError);
        Assert.Equal([1m, 2m, 3m, 4m], result.Value);
    }
}
