using KatLang.Semantics;

namespace KatLang.Tests;

/// <summary>
/// Executable diagnostic-provenance map: for a given surface source, WHICH
/// language-processing stage decides the outcome — parser, front-end
/// elaboration, editor semantic model, or evaluator.
///
/// <para>
/// Track 13 built this after finding regression tests that asserted an
/// evaluator outcome while an earlier stage had already done the work. The
/// cases here are the ones where the stages genuinely disagree, pinned so the
/// disagreement is a reviewed contract rather than an accident, and so the
/// later structured-error/ownership audit has a factual starting point.
/// </para>
/// </summary>
public class DiagnosticProvenanceTests
{
    private static EvalError InnermostError(string source)
    {
        var provenance = SourceProvenance.ParseValid(source);
        return provenance.ExpectEvaluationError();
    }

    private static IReadOnlyList<string> EditorUnresolved(string source)
    {
        var parsed = Parser.Parse(source);
        Assert.False(parsed.HasErrors, string.Join(" | ", parsed.Diagnostics.Select(d => d.Message)));
        return SemanticModelBuilder.Build(parsed).IdentifierResolutions
            .Where(r => r.Classification == IdentifierClassification.Unresolved)
            .Select(r => r.Occurrence.Name)
            .ToList();
    }

    private static Result EvaluatesTo(string source)
    {
        var result = SourceProvenance.ParseValid(source).Evaluate();
        if (result.IsError)
            Assert.Fail($"Expected success but got: {KatLangError.FromEvalError(result.Error).Message.Split('\n')[0]}");
        return result.Value;
    }

    // ── `open` validation is DEMAND-DRIVEN ────────────────────────────────────

    /// <summary>
    /// An invalid <c>open</c> target is accepted by the parser and never
    /// diagnosed at runtime unless some name actually falls through to the
    /// opens. This is not a C# shortcut: Lean reaches <c>resolveAllOpens</c>
    /// only from <c>lookupOpens</c>, itself only step 3 of <c>lookupLexical</c>,
    /// so laziness is the modelled semantics.
    ///
    /// <para>
    /// The four target kinds below are all invalid for different reasons —
    /// builtin head, missing name, missing dotted member, non-public dotted
    /// member — and all four evaluate successfully when the body uses only
    /// owned names.
    /// </para>
    /// </summary>
    [Theory]
    [InlineData("open count\nQ = 5\nQ")]                                              // builtin head
    [InlineData("open Nope\nQ = 5\nQ")]                                               // missing target
    [InlineData("open Lib.Nope\nLib = {\n    public S = 1\n}\nQ = 5\nQ")]             // missing member
    [InlineData("open Lib.S\nLib = {\n    S = {\n        public X = 1\n    }\n}\nQ = 5\nQ")] // non-public member
    public void InvalidOpenTarget_IsNotDiagnosedWhenNoNameFallsThroughToIt(string source)
        => Assert.Equal(new Result.Atom(5), EvaluatesTo(source));

    /// <summary>
    /// ... and the SAME declaration fails as soon as a lookup demands the opens.
    /// Demand, not declaration, is what triggers validation.
    /// </summary>
    [Fact]
    public void TheSameInvalidOpenFailsAsSoonAsALookupDemandsIt()
    {
        Assert.IsType<EvalError.IllegalInOpen>(
            InnermostError("open count, Pub\nPub = {\n    public Y = 7\n}\nY"));

        // Owned name instead of `Y`: the very same declaration is fine.
        Assert.Equal(
            new Result.Atom(5),
            EvaluatesTo("open count, Pub\nPub = {\n    public Y = 7\n}\nQ = 5\nQ"));
    }

    /// <summary>
    /// The EDITOR does not agree with the runtime here: the semantic model
    /// flags every invalid open target eagerly, including in programs that
    /// evaluate successfully. That is defensible (an editor should warn) but it
    /// IS a layer disagreement, and it is the clearest input this track has for
    /// the structured-error ownership audit: today no layer both accepts the
    /// program and reports the mistake.
    /// </summary>
    [Theory]
    [InlineData("open count\nQ = 5\nQ", "count")]
    [InlineData("open Nope\nQ = 5\nQ", "Nope")]
    public void EditorFlagsAnInvalidOpenTargetThatTheRuntimeNeverDiagnoses(string source, string flagged)
    {
        Assert.Contains(flagged, EditorUnresolved(source));
        Assert.Equal(new Result.Atom(5), EvaluatesTo(source));
    }

    // ── Conditional accessed as a value ───────────────────────────────────────

    /// <summary>
    /// A genuine multi-clause family accessed as a value reports
    /// <c>NoMatchingBranch</c>. This IS surface-reachable.
    /// </summary>
    [Fact]
    public void BareMultiClauseReference_ReportsNoMatchingBranch()
    {
        var multi = Assert.IsType<EvalError.NoMatchingBranch>(InnermostError("F(0) = 1\nF(n) = 2\nF"));
        Assert.Equal("F", multi.AlgorithmName);

        Assert.IsType<EvalError.NoMatchingBranch>(
            InnermostError("A = {\n    public F(0) = 1\n    public F(n) = 2\n}\nA.F"));
    }

    /// <summary>
    /// The OTHER arm of <c>ConditionalValueAccessError</c> — the one that
    /// reports the friendlier arity error for a conditional equivalent to a flat
    /// binder callable — is NOT surface-reachable.
    ///
    /// <para>
    /// Track 12 mutated the selection to always report <c>NoMatchingBranch</c>
    /// and the mutant survived. Track 13 classified the cause, and it is source
    /// PRE-EMPTION, not a missing surface test: <c>TryGetFlatBinderUserEquivalent</c>
    /// requires a single-branch <c>Algorithm.Conditional</c> whose pattern is
    /// flat binders, and <c>Algorithm.ElaborateClauseGroup</c> converts exactly
    /// that shape into an ordinary <c>Algorithm.User</c>. Every written form
    /// tried — <c>F(a) = …</c>, <c>F(a, b) = …</c>, even the repeated-binder
    /// <c>F(x, x) = …</c> — elaborates to a User algorithm and reports its arity
    /// through the ordinary parametrized-property path instead.
    /// </para>
    ///
    /// <para>
    /// So this is a host-API defensive branch and is pinned as one, from a
    /// prebuilt AST. Writing it as a source test would have been exactly the
    /// vacuity this track exists to remove — the source test passes while the
    /// branch is dead code.
    /// </para>
    /// </summary>
    [Fact]
    public void FlatBinderConditionalValueAccess_IsReachableOnlyFromAPrebuiltAst()
    {
        var body = new Algorithm.User(
            Parent: null, Parameters: [], Opens: [], Properties: [],
            Output: [new Expr.Binary(BinaryOp.Add, new Expr.Param("a"), new Expr.Param("b"))]);

        var conditional = new Algorithm.Conditional(
            Parent: null,
            Opens: [],
            Branches: [new CondBranch(
                new Pattern.SequenceValue([new Pattern.Bind("a"), new Pattern.Bind("b")]),
                body)]);

        var root = new Algorithm.User(
            Parent: null, Parameters: [], Opens: [],
            Properties: [new Property("F", conditional)],
            Output: [new Expr.Resolve("F")]);

        var result = Evaluator.Run(new Expr.Block(root));
        Assert.True(result.IsError);

        var error = result.Error;
        while (error is EvalError.WithContext context)
            error = context.Inner;

        var arity = Assert.IsType<EvalError.ArityMismatch>(error);
        Assert.Equal(2, arity.Expected);
        Assert.Equal(0, arity.Actual);
    }
}
