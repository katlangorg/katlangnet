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
/// </summary>
public class OpenPathResolutionBranchTests
{
    private const string PublicProvider = "Pub = {\n    public Y = 7\n}\n";

    private static EvalError EvalError_(string source)
    {
        var parsed = Parser.Parse(source);
        Assert.False(
            parsed.HasErrors,
            "Witness must be a legal program (the branch under test is an EVALUATOR branch): "
                + string.Join(" | ", parsed.Diagnostics.Select(d => d.Message)));

        var result = Evaluator.Run(new Expr.AlgorithmExpr(parsed.Root));
        Assert.True(result.IsError, $"Expected an evaluation failure for:\n{source}");

        var error = result.Error;
        while (error is EvalError.WithContext context)
            error = context.Inner;
        return error;
    }

    private static Result EvalOk(string source)
    {
        var parsed = Parser.Parse(source);
        Assert.False(parsed.HasErrors, string.Join(" | ", parsed.Diagnostics.Select(d => d.Message)));
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
            + "A = {\n    open Lib.S, Pub\n    Y\n}\nA");

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
            + "A = {\n    open Lib.Nope, Pub\n    Y\n}\nA");

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
    /// The pre-emption itself, pinned. The obvious spelling of the same mistake
    /// never reaches the evaluator: the front end turns the unresolvable name
    /// into an implicit parameter, so the user sees an implicit-parameter
    /// diagnostic instead of the visibility error. If a future change made the
    /// obvious form report the visibility error directly, that is an
    /// IMPROVEMENT — but it must be a deliberate, reviewed change, not a silent
    /// drift, and the witnesses above must keep working either way.
    /// </summary>
    [Fact]
    public void ObviousSpelling_IsPreEmptedByImplicitParameterSynthesis()
    {
        var error = EvalError_(
            "Lib = {\n    S = {\n        public X = 101\n    }\n}\n"
            + "A = {\n    open Lib.S\n    X\n}\nA");

        // Not NotPublicProperty: `X` became an implicit parameter of `A`.
        Assert.IsNotType<EvalError.NotPublicProperty>(error);
        Assert.IsType<EvalError.ArityMismatch>(error);

        // Supplying the argument confirms `X` really is a parameter now.
        Assert.Equal(
            new Result.Atom(707),
            EvalOk("Lib = {\n    S = {\n        public X = 101\n    }\n}\n"
                + "A = {\n    open Lib.S\n    X\n}\nA(707)"));
    }

    /// <summary>
    /// Open resolution is LAZY, and that is the second reason the obvious shapes
    /// miss these branches: a name that resolves by ownership never consults the
    /// opens, so an illegal open target in the same declaration goes completely
    /// unvalidated. Pinned because it decides whether a witness works at all.
    /// </summary>
    [Fact]
    public void OpenTargetsAreOnlyValidatedWhenANameFallsThroughToThem()
    {
        // `Q` is owned locally, so the malformed `open Lib.S` is never resolved.
        Assert.Equal(
            new Result.Atom(5),
            EvalOk("Lib = {\n    S = {\n        public X = 101\n    }\n}\n"
                + "A = {\n    open Lib.S\n    Q = 5\n    Q\n}\nA"));

        // The same declaration fails as soon as a name must fall through.
        Assert.IsType<EvalError.NotPublicProperty>(EvalError_(
            PublicProvider
            + "Lib = {\n    S = {\n        public X = 101\n    }\n}\n"
            + "A = {\n    open Lib.S, Pub\n    Y\n}\nA"));
    }
}
