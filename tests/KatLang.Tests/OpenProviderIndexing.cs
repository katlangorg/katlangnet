using KatLang.Evaluation.Caching;

namespace KatLang.Tests;

/// <summary>
/// Observes the evaluator's open-provider deduplication (Q-19 D-I, <c>Evaluator.ResolveAllOpens</c>)
/// on a PREPARED root — the front end has finished before the measured run, so every count is the
/// evaluator's — through the run's <see cref="EvaluationObservations"/>. Each observation is a fresh
/// run. <see cref="OnBothRoutesAsync"/> runs the synchronous evaluator and the forced async twin and
/// requires them to agree on the complete outcome and on every count: the async route reaches open
/// lookup through the same synchronous resolver (<c>Evaluator.ResolveAsync</c>), so a difference is
/// a regression of either.
/// </summary>
internal static class OpenProviderIndexing
{
    /// <summary>
    /// One run: <see cref="Outcome"/> is <c>ok</c> with the neutral value, or <c>err</c> with the
    /// structured error (<see cref="Describe"/>); the counts are the run's provider-deduplication work
    /// (<see cref="Levels"/> counts level RESOLUTIONS), then its open-level READS: every consultation of a
    /// nonempty level, and the part a level state's memoized providers served without resolving anything
    /// (<c>Evaluator.ResolvedOpenLevel</c>).
    /// </summary>
    internal sealed record Observation(
        string Outcome,
        long Levels,
        long Entries,
        long KeyComparisons,
        long IdentityComparisons,
        long CrossDeclarationIdentityComparisons,
        long Consultations,
        long Reuses)
    {
        /// <summary>Index work per consulted level: entries, key comparisons and identity comparisons.</summary>
        public long WorkPerLevel => Levels == 0 ? 0 : (Entries + KeyComparisons + IdentityComparisons) / Levels;
    }

    /// <summary>
    /// One run's member-index work of WIDE open levels (<c>Evaluator.OpenLevelMemberIndexCache</c>): the indexes
    /// it built, the members those builds visited, and the level states that took an index already built.
    /// </summary>
    internal sealed record MemberIndexWork(long Builds, long Members, long Shares)
    {
        internal static readonly MemberIndexWork None = new(0, 0, 0);

        internal static MemberIndexWork Of(EvaluationObservations observations)
            => new(observations.OpenLevelMemberIndexBuildCount, observations.OpenLevelMemberIndexMemberCount,
                observations.OpenLevelMemberIndexShareCount);
    }

    internal static async Task<Observation> ObserveAsync(Expr program, bool forcedAsync)
        => (await ObserveWithIndexWorkAsync(program, forcedAsync)).Run;

    /// <summary><see cref="ObserveAsync"/> together with the run's <see cref="MemberIndexWork"/>.</summary>
    internal static async Task<(Observation Run, MemberIndexWork Index)> ObserveWithIndexWorkAsync(Expr program, bool forcedAsync)
    {
        var observations = new EvaluationObservations();
        var (result, _) = forcedAsync
            ? await Evaluator.RunCountedObservedAsync(
                program,
                zeroArgPropertyResultCache: new RunScopedAsyncZeroArgPropertyResultCache(),
                observations: observations)
            : Evaluator.RunCountedObserved(program, observations: observations);
        var outcome = result.IsError
            ? "err " + Describe(result.Error)
            : "ok " + SixRouteAgreement.Neutral(result.Value.Value);
        return (new Observation(
            outcome,
            observations.OpenProviderLevelCount,
            observations.OpenProviderIndexEntryCount,
            observations.OpenProviderDeclarationKeyComparisonCount,
            observations.OpenProviderIdentityComparisonCount,
            observations.OpenProviderCrossDeclarationIdentityComparisonCount,
            observations.OpenLevelConsultationCount,
            observations.OpenLevelReuseCount), MemberIndexWork.Of(observations));
    }

    /// <summary>
    /// The synchronous observation and member-index work, after requiring the forced async twin to agree with
    /// both exactly.
    /// </summary>
    internal static async Task<(Observation Run, MemberIndexWork Index)> OnBothRoutesWithIndexWorkAsync(Expr program)
    {
        var synchronous = await ObserveWithIndexWorkAsync(program, forcedAsync: false);
        var asynchronous = await ObserveWithIndexWorkAsync(program, forcedAsync: true);
        Assert.Equal(synchronous, asynchronous);
        return synchronous;
    }

    /// <summary><see cref="OnBothRoutesWithIndexWorkAsync(Expr)"/> of a source the front end accepts cleanly.</summary>
    internal static Task<(Observation Run, MemberIndexWork Index)> OnBothRoutesWithIndexWorkAsync(string source)
        => OnBothRoutesWithIndexWorkAsync(new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root));

    /// <summary>The synchronous observation, after requiring the forced async twin to agree with it — and on its member-index work — exactly.</summary>
    internal static async Task<Observation> OnBothRoutesAsync(Expr program)
        => (await OnBothRoutesWithIndexWorkAsync(program)).Run;

    /// <summary><see cref="OnBothRoutesAsync(Expr)"/> of a source the front end accepts cleanly.</summary>
    internal static Task<Observation> OnBothRoutesAsync(string source)
        => OnBothRoutesAsync(new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root));

    /// <summary>
    /// The complete structured payload of an evaluator error: every context frame with its span, the
    /// innermost error with its fields and span (an ambiguity's providers in order), and the public
    /// error's code, message and span.
    /// </summary>
    internal static string Describe(EvalError error)
    {
        var parts = new List<string>();
        var current = error;
        while (current is EvalError.WithContext frame)
        {
            parts.Add($"[{frame.Context} @ {frame.Span}]");
            current = frame.Inner;
        }

        parts.Add(current switch
        {
            EvalError.AmbiguousOpen ambiguous => $"AmbiguousOpen({ambiguous.Name}: {string.Join(", ", ambiguous.Providers)}) @ {ambiguous.Span}",
            _ => $"{current} @ {current.Span}",
        });
        var report = KatLangError.FromEvalError(error);
        parts.Add($"| {report.Code}: {report.Message} @ {report.Span}");
        return string.Join(" ", parts);
    }
}
