namespace KatLang.Tests;

/// <summary>
/// Witnesses for evaluator branches that ordinary KatLang source can no longer
/// reach because the FRONT END guarantees the condition away — but which the
/// evaluator deliberately revalidates because <c>Evaluator.Run</c> /
/// <c>RunCounted</c> are a public API that accepts prebuilt ASTs from hosts and
/// from internal elaboration stages.
///
/// <para>
/// Track 12 classified these as <b>P</b> (pre-empted defensive). Every one of
/// them survived a mutation of the branch itself against the entire suite,
/// because no surface program can reach them: the parser rejects the shape, or
/// an elaboration pass rewrites it first. That makes them invisible to the
/// language corpora by construction, so they are pinned HERE, at the API
/// boundary that actually justifies their existence, rather than with a
/// misleading LanguageSpec or Lean case for behavior the language cannot
/// express.
/// </para>
///
/// <para>
/// Each test states the front-end invariant that pre-empts the branch, so a
/// future change that makes the shape surface-reachable will be recognized as
/// a deliberate contract change rather than a puzzle.
/// </para>
/// </summary>
public class EvaluatorDefensiveBranchTests
{
    private static EvalError Innermost(EvalError error)
    {
        while (error is EvalError.WithContext context)
            error = context.Inner;
        return error;
    }

    private static EvalError FailsWith(Expr root)
    {
        var result = Evaluator.Run(root);
        Assert.True(result.IsError, "Expected the defensive branch to reject this AST.");
        return Innermost(result.Error);
    }

    private static Expr.AlgorithmExpr Program(Algorithm.User root) => new(root);

    private static Algorithm.User Root(
        IReadOnlyList<Expr>? opens = null,
        IReadOnlyList<Property>? properties = null,
        OutputBundle? output = null)
        => new(Parent: null, Parameters: [], Opens: opens ?? [], Properties: properties ?? [], Output: output ?? OutputBundle.Empty);

    private static Algorithm.User Value(decimal n)
        => new(Parent: null, Parameters: [], Opens: [], Properties: [], Output: [new Expr.Num(n)]);

    /// <summary>
    /// <c>Expr.Grace</c> is the implicit-argument placeholder (<c>~</c>). The
    /// front end's implicit-argument resolver replaces every grace node during
    /// elaboration, so a parsed program never carries one into evaluation — the
    /// evaluator's catch-all rejects it only for prebuilt ASTs.
    /// </summary>
    [Fact]
    public void Grace_ReachesTheEvaluatorCatchAll_OnlyFromAPrebuiltAst()
    {
        var error = FailsWith(Program(Root(output: [new Expr.Grace(new Expr.Num(1), Weight: 0)])));

        var illegal = Assert.IsType<EvalError.IllegalInEval>(error);
        Assert.Equal("grace", illegal.Reason);
    }

    /// <summary>
    /// <c>Expr.SequenceConstruct</c> is an INTERNAL sequence-join node the parser
    /// must never produce (guarded by <c>SequenceConstructContainmentTests</c>).
    /// It is a legal evaluation node, but never a legal <c>open</c> target.
    /// </summary>
    [Fact]
    public void SequenceConstructOpenTarget_IsRejected_OnlyFromAPrebuiltAst()
    {
        var error = FailsWith(Program(Root(
            opens: [new Expr.SequenceConstruct(new Expr.Num(1), new Expr.Num(2))],
            output: [new Expr.Resolve("Missing")])));

        Assert.IsType<EvalError.BadOpenForm>(error);
    }

    /// <summary>
    /// The open-form validation pass in <c>ResolveAllOpens</c>. The parser
    /// rejects every non-open form in open position with its own targeted
    /// diagnostic ("Invalid open form: 'spread' is not allowed in open
    /// declarations"), so this loop only ever fires for a prebuilt AST.
    /// </summary>
    [Fact]
    public void NonOpenFormTarget_IsRejected_OnlyFromAPrebuiltAst()
    {
        var error = FailsWith(Program(Root(
            opens: [new Expr.Num(7)],
            output: [new Expr.Resolve("Missing")])));

        Assert.IsType<EvalError.BadOpenForm>(error);
    }

    /// <summary>
    /// <c>ResolveAllOpens</c> validates the SHAPE of every open target before
    /// resolving any of them. That ordering is the only observable difference
    /// between the up-front validation loop and the per-target rejection inside
    /// <c>ResolveAlgForOpen</c> — both produce <c>BadOpenForm</c> on their own,
    /// so a test that merely asserts "a bad form is rejected" cannot tell
    /// whether the loop still exists.
    ///
    /// <para>
    /// Here the FIRST target would fail resolution with <c>IllegalInOpen</c>
    /// (a builtin) while a LATER target is malformed. Validating shapes first
    /// means the malformed target wins.
    /// </para>
    /// </summary>
    [Fact]
    public void OpenFormsAreAllValidatedBeforeAnyTargetIsResolved()
    {
        var error = FailsWith(Program(Root(
            opens: [new Expr.Resolve("count"), new Expr.Num(7)],
            output: [new Expr.Resolve("Missing")])));

        Assert.IsType<EvalError.BadOpenForm>(error);
    }

    /// <summary>
    /// Runtime duplicate-property validation. The parser reports "Property 'X'
    /// is already defined", so this check is pure host-AST defense.
    /// </summary>
    [Fact]
    public void DuplicateProperty_IsRejected_OnlyFromAPrebuiltAst()
    {
        var error = FailsWith(Program(Root(
            properties:
            [
                new Property("X", Value(1)),
                new Property("X", Value(2)),
            ],
            output: [new Expr.Resolve("X")])));

        var duplicate = Assert.IsType<EvalError.DuplicateProperty>(error);
        Assert.Equal("X", duplicate.Name);
    }

    /// <summary>
    /// A spread whose operand has no output must report the spread-specific
    /// error, not the plain missing-output one. Track 4 aligned Lean and C# on
    /// exactly this distinction; the surface spelling is reachable, and this
    /// pins the prebuilt-AST route to the same branch so a host cannot observe
    /// a different verdict.
    /// </summary>
    [Fact]
    public void SpreadOfAnOutputlessBlock_ReportsTheSpreadSpecificError()
    {
        var outputless = new Algorithm.User(
            Parent: null, Parameters: [], Opens: [],
            Properties: [new Property("Q", Value(1))], Output: []);

        var error = FailsWith(Program(Root(
            output: [new Expr.SequenceSpread(new Expr.AlgorithmExpr(outputless))])));

        Assert.IsType<EvalError.SpreadMissingOutput>(error);
    }

    /// <summary>
    /// The same program written in KatLang reaches the same branch, so the
    /// prebuilt-AST route above is defense, not a second semantics.
    /// </summary>
    [Fact]
    public void SpreadOfAnOutputlessBlock_AgreesWithTheSurfaceSpelling()
    {
        var parsed = Parser.Parse("A = {\n    Q = 1\n}\nA*");
        Assert.False(parsed.HasErrors, string.Join(" | ", parsed.Diagnostics.Select(d => d.Message)));

        var result = Evaluator.Run(new Expr.AlgorithmExpr(parsed.Root));
        Assert.True(result.IsError);
        Assert.IsType<EvalError.SpreadMissingOutput>(Innermost(result.Error));
    }
}
