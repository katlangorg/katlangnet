namespace KatLang;

/// <summary>
/// Explicit source-phase provenance for a related family of standalone physical scopes. The frozen query source
/// and final equations are shared persistently; no live producer engine or token is retained. This is not a Q9
/// completed-program continuation and cannot be used to publish one.
/// </summary>
internal sealed class StandaloneScopeAnalysis
{
    private StandaloneScopeAnalysis(StaticStructureQueries.Snapshot source, CompletedStructureContext context,
        StaticAstPhase phase, StaticQueryStatistics statistics, long inheritedStorage)
        => (Source, Context, Phase, Statistics, InheritedStorageUnits) = (source, context, phase, statistics, inheritedStorage);

    internal StaticStructureQueries.Snapshot Source { get; private set; }
    internal CompletedStructureContext Context { get; }
    internal StaticAstPhase Phase { get; }
    internal StaticQueryStatistics Statistics { get; }
    internal long InheritedStorageUnits { get; }

    internal static StandaloneScopeAnalysis Start(Algorithm body, StaticAstPhase phase, object? ownerIdentity = null,
        CancellationToken cancellationToken = default)
    {
        cancellationToken.ThrowIfCancellationRequested();
        Check(body);
        var operation = ownerIdentity is null
            ? StaticStructureAdmission.Create(body, phase: phase, cancellationToken: cancellationToken).Operation
            : StaticStructureAdmission.Create(new Algorithm.User(null, [], [], [], []), phase: phase,
                sourceAncestors: [body], cancellationToken: cancellationToken).Operation;
        var key = ownerIdentity is null ? operation.Root
            : operation.Queries.BodyIn(operation.Queries.Keys.Root, body, ownerIdentity);
        var context = AnalyzedStaticStructures.Project(operation, key, cancellationToken: cancellationToken);
        var source = operation.Queries.Freeze(cancellationToken);
        return new(source, context, phase, operation.Queries.Statistics, 0);
    }

    internal StandaloneScopeAnalysis AtPrelude()
        => new(Source, Context.Facts.Context(Source.Keys.Root), Phase, default, Source.RetainedStorageUnits);

    internal StandaloneScopeAnalysis Inside(Algorithm body, Pattern? pattern, StaticAstPhase phase, object? ownerIdentity,
        CancellationToken cancellationToken = default)
    {
        cancellationToken.ThrowIfCancellationRequested();
        var inherited = Source;
        var declaring = pattern is not null && Context.Facts.Facts(Context.Key)?.Body is Algorithm.Conditional { Opens.Count: 0 }
            ? Context.Key.Parent ?? Source.Keys.Root : Context.Key;
        if (phase == Phase && Context.Facts.Child(declaring, body, pattern) is { } existing)
            return new(Source, Context.Facts.Context(existing), phase, default, Source.RetainedStorageUnits);
        // This root's declaring frame is the supplied, already admitted context. Its AST Parent is not
        // a second source of lexical ownership and must not trigger another walk of that ancestor graph.
        Algorithm local = body switch
        {
            Algorithm.User user => user.Parent is null ? user : user with { Parent = null },
            Algorithm.Conditional family => family.Parent is null ? family : family with { Parent = null },
            Algorithm.Alias alias => alias.Parent is null ? alias : alias with { Parent = null },
            Algorithm.Builtin builtin => builtin,
        };
        Check(local);
        var limits = StaticStructureAdmission.Measure(local, Source.Contexts[Source.Keys.Root].Body,
            cancellationToken: cancellationToken).Limits;
        var operation = new StaticStructureOperation(Source, limits, declaring, body, pattern, phase, ownerIdentity, cancellationToken);
        var context = AnalyzedStaticStructures.Project(operation, operation.Root,
            (AnalyzedStaticStructures)Context.Facts, cancellationToken);
        var source = operation.Queries.Freeze(cancellationToken);
        cancellationToken.ThrowIfCancellationRequested();
        // Append only a successful immutable source version. Related siblings share syntax and closed equations;
        // their projected facts remain separate local overlays, with no growing chain of sibling projections.
        Source = source;
        return new(source, context, phase, operation.Queries.Statistics, inherited.RetainedStorageUnits);
    }

    private static void Check(Algorithm body)
    {
        if (AstStructuralPreflight.Check(body, EvaluationLimits.MaxSupportedAstDepth, AstConsumerProfile.FullyRecursive) is { } rejection)
            throw new ArgumentException($"Standalone scope admission requires a structurally safe AST ({rejection.Kind}).", nameof(body));
    }
}
