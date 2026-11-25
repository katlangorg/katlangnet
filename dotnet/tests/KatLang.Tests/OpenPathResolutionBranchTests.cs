namespace KatLang.Tests;

/// <summary>
/// Direct witnesses for the evaluator branches inside
/// <c>Evaluator.ResolveAlgForOpen</c> / <c>ResolveOpenPropAccess</c> — the
/// dotted <c>open A.B</c> path. Each of <see cref="EvalError.NotPublicProperty"/>
/// and <see cref="EvalError.UnknownProperty"/> has exactly ONE construction site
/// in the whole evaluator, and both are here.
///
/// <para>
/// <b>Why these need a non-obvious source shape (Track 12).</b> The obvious
/// spelling — <c>open Lib.PrivateSub</c> followed by a name that member would
/// supply — never reaches the evaluator at all. The front end resolves the open
/// target first, finds nothing, and promotes the referenced name to an IMPLICIT
/// PARAMETER; the user then sees an arity/unresolved-implicit-parameter
/// diagnostic and the evaluator's open-path check is never executed. Worse,
/// open resolution is LAZY: it only runs when a name actually falls through to
/// the opens, so even a valid-looking program can leave the whole open list
/// unvalidated.
/// </para>
///
/// <para>
/// The witness therefore pairs the bad target with a SECOND, valid provider and
/// references a name only that provider supplies. Resolving that name forces
/// <c>ResolveAllOpens</c> to resolve every target in the list, which reaches the
/// intended branch. Track 12 mutation evidence: making the open path accept a
/// non-public member, or report a different error for a missing one, survived
/// the entire suite before these tests existed — and the one pre-existing test
/// named for <c>NotPublicProperty</c> was evaluating a PARSE-REJECTED source
/// (its helper ignores parser diagnostics), so it passed for an unrelated
/// reason.
/// </para>
///
/// <para>
/// <b>Since the name-resolution audit (#8, September 2026)</b> the front end refuses a
/// target that resolves to nothing STATICALLY (<see cref="DiagnosticCode.UnresolvedOpenTarget"/>)
/// — the improvement <see cref="ObviousSpelling_NowReportsTheVisibilityErrorDirectly"/> pins —
/// so a missing or non-public open step is no longer a legal program. Those evaluator branches
/// stay reachable exactly as before from the elaborated tree the front end still produces (a
/// diagnostic is added; nothing is rewritten), which is what the witnesses evaluate: the
/// front end's verdict is asserted first, then the evaluator's own branch.
/// </para>
/// </summary>
public class OpenPathResolutionBranchTests
{
    private const string PublicProvider = "Pub = {\n    public Y = 7\n}\n";

    private static EvalError EvalError_(string source, DiagnosticCode? expectedFrontEndRejection = null)
    {
        var parsed = SourceProvenance.ParseAllowingDiagnostics(source);
        if (expectedFrontEndRejection is { } code)
            Assert.Equal(code, Assert.Single(parsed.Diagnostics).Code);
        else
            Assert.False(
                parsed.HasFrontEndErrors,
                "Witness must be a legal program (the branch under test is an EVALUATOR branch): "
                    + string.Join(" | ", parsed.Diagnostics.Select(d => d.Message)));

        var result = Evaluator.Run(new Expr.AlgorithmExpr(parsed.Root));
        Assert.True(result.IsError, $"Expected an evaluation failure for:\n{source}");

        var error = result.Error;
        while (error is EvalError.WithContext context)
            error = context.Inner;
        return error;
    }

    private static Result EvalOk(string source, DiagnosticCode? expectedFrontEndRejection = null)
    {
        var parsed = SourceProvenance.ParseAllowingDiagnostics(source);
        if (expectedFrontEndRejection is { } code)
            Assert.Equal(code, Assert.Single(parsed.Diagnostics).Code);
        else
            Assert.False(parsed.HasFrontEndErrors, string.Join(" | ", parsed.Diagnostics.Select(d => d.Message)));
        var result = Evaluator.Run(new Expr.AlgorithmExpr(parsed.Root));
        if (result.IsError)
            Assert.Fail($"Expected success but got: {KatLangError.FromEvalError(result.Error).Message}");
        return result.Value;
    }

    /// <summary>
    /// A dotted open path requires every member after the lexically-resolved
    /// head to be public. Lean states the same rule in the
    /// <c>resolveAlgForOpen</c> doc comment ("Qualified property access in open
    /// paths still requires each dotted member after the direct lexical head to
    /// be public").
    /// </summary>
    [Fact]
    public void OpenPath_NonPublicMember_IsRejected()
    {
        var error = EvalError_(
            PublicProvider
            + "Lib = {\n    S = {\n        public X = 101\n    }\n}\n"
            + "A = {\n    open Lib.S, Pub\n    Y\n}\nA",
            DiagnosticCode.UnresolvedOpenTarget);

        var notPublic = Assert.IsType<EvalError.NotPublicProperty>(error);
        Assert.Equal("Lib", notPublic.ObjectDesc);
        Assert.Equal("S", notPublic.PropertyName);
    }

    [Fact]
    public void OpenPath_MissingMember_IsRejected()
    {
        var error = EvalError_(
            PublicProvider
            + "Lib = {\n    public S = {\n        public X = 101\n    }\n}\n"
            + "A = {\n    open Lib.Nope, Pub\n    Y\n}\nA",
            DiagnosticCode.UnresolvedOpenTarget);

        var unknown = Assert.IsType<EvalError.UnknownProperty>(error);
        Assert.Equal("Lib", unknown.ObjectDesc);
        Assert.Equal("Nope", unknown.PropertyName);
    }

    /// <summary>
    /// Exposure, not just visibility: a member that is written <c>public</c> but
    /// captures its owner's parameters is local-only and must not be openable.
    /// </summary>
    [Fact]
    public void OpenPath_LocalOnlyMember_IsRejected()
    {
        var error = EvalError_(
            PublicProvider
            + "Lib(p) = {\n    public S = p + 1\n    S\n}\n"
            + "A = {\n    open Lib.S, Pub\n    Y\n}\nA");

        var localOnly = Assert.IsType<EvalError.LocalOnlyProperty>(error);
        Assert.Equal("Lib", localOnly.ObjectDesc);
        Assert.Equal("S", localOnly.PropertyName);
        Assert.Equal(PropertyExposure.LocalOnlyCapturedAncestorParameters, localOnly.Exposure);
    }

    /// <summary>
    /// The pre-emption this class was written around is gone, as its original pin
    /// anticipated ("If a future change made the obvious form report the visibility error
    /// directly, that is an IMPROVEMENT — but it must be a deliberate, reviewed change"): the
    /// obvious spelling of the mistake now reports the non-public step at the open target,
    /// instead of silently promoting the name it would provide to an implicit parameter. The
    /// elaborated tree behind the rejection is unchanged — `X` is still promoted there — which
    /// is exactly why the witnesses above keep reaching the evaluator branches.
    /// </summary>
    [Fact]
    public void ObviousSpelling_NowReportsTheVisibilityErrorDirectly()
    {
        const string source = "Lib = {\n    S = {\n        public X = 101\n    }\n}\n"
            + "A = {\n    open Lib.S\n    X\n}\nA(707)";
        var parsed = SourceProvenance.ParseAllowingDiagnostics(source);
        var diagnostic = Assert.Single(parsed.Diagnostics);
        Assert.Equal(DiagnosticCode.UnresolvedOpenTarget, diagnostic.Code);
        // The target `Lib.S` on line 7 (`    open Lib.S`).
        Assert.Equal(new SourceSpan(7, 10, 7, 15), diagnostic.Span);
        Assert.Contains("property 'S' of 'Lib' is not public", diagnostic.Message, StringComparison.Ordinal);
        Assert.Equal(KatLangErrorCode.UnresolvedOpenTarget,
            Assert.Single(Assert.IsType<RunResult.ParseFailure>(KatLangEngine.Run(source)).Errors).Code);

        // The recovery tree still promotes `X` (the provider supplies nothing), so evaluating
        // it — as the witnesses do — reads the supplied argument.
        Assert.Equal(new Result.Atom(707), EvalOk(source, DiagnosticCode.UnresolvedOpenTarget));
    }

    /// <summary>
    /// The EVALUATOR's open resolution stays LAZY (the modelled semantics: Lean reaches
    /// <c>resolveAllOpens</c> only when a lookup falls through to the opens), and that is why
    /// the witnesses pair the bad target with a valid provider: over the elaborated tree, a
    /// name that resolves by ownership never consults the opens. The FRONT END no longer
    /// depends on that accident — it refuses the target statically in both programs.
    /// </summary>
    [Fact]
    public void EvaluatorValidatesOpenTargetsOnlyWhenANameFallsThroughToThem()
    {
        // `Q` is owned locally, so the evaluator never resolves the malformed `open Lib.S`.
        Assert.Equal(
            new Result.Atom(5),
            EvalOk("Lib = {\n    S = {\n        public X = 101\n    }\n}\n"
                + "A = {\n    open Lib.S\n    Q = 5\n    Q\n}\nA",
                DiagnosticCode.UnresolvedOpenTarget));

        // The same declaration fails as soon as a name must fall through.
        Assert.IsType<EvalError.NotPublicProperty>(EvalError_(
            PublicProvider
            + "Lib = {\n    S = {\n        public X = 101\n    }\n}\n"
            + "A = {\n    open Lib.S, Pub\n    Y\n}\nA",
            DiagnosticCode.UnresolvedOpenTarget));
    }
}
