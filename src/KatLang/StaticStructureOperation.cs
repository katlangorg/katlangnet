using System.Collections.Immutable;

namespace KatLang;

internal enum StaticPublicationStage : byte { Detected, Resolved }

/// <summary>
/// The hand-off between the default compiler passes. Query
/// definitions always read admitted raw syntax; detected/resolved views are publications, never new definitions.
/// This facade does not cache a second structural conclusion.
/// </summary>
internal sealed partial class StaticStructureOperation
{
    private sealed class Publication(Algorithm source)
    {
        internal Algorithm Source { get; } = source;
        internal Algorithm? Detected;
        internal Algorithm? Resolved;
    }

    internal sealed record FrozenPublication(Algorithm Source, Algorithm Detected, Algorithm Resolved, AliasStructureCell? StructureCell);

    private readonly Dictionary<StaticScopeKey, Publication> _publications = new(ReferenceEqualityComparer.Instance);
    private readonly Dictionary<Algorithm, Algorithm> _sources = new(ReferenceEqualityComparer.Instance);
    private readonly Dictionary<StaticScopeKey, AliasStructureCell> _structureCells = new(ReferenceEqualityComparer.Instance);
    private readonly ImmutableDictionary<StaticScopeKey, FrozenPublication> _frozenPublications
        = ImmutableDictionary.Create<StaticScopeKey, FrozenPublication>(ReferenceEqualityComparer.Instance);
    private readonly ImmutableDictionary<Algorithm, Algorithm> _frozenViews
        = ImmutableDictionary.Create<Algorithm, Algorithm>(ReferenceEqualityComparer.Instance);
    private readonly Dictionary<Algorithm, Algorithm> _resolvedSources = new(ReferenceEqualityComparer.Instance);
    private readonly ImmutableDictionary<Algorithm, Algorithm> _frozenResolvedSources
        = ImmutableDictionary.Create<Algorithm, Algorithm>(ReferenceEqualityComparer.Instance);
    private readonly Pattern? _unitPattern;
    private HashSet<object>? _suppliedSourceNodes;

    internal StaticStructureOperation(Algorithm root, StaticQueryLimits limits, Algorithm? prelude = null, StaticAstPhase phase = StaticAstPhase.RawSource,
        CancellationToken cancellationToken = default)
    {
        Queries = new(root, limits, prelude, phase, cancellationToken);
        Root = Queries.Root;
        Queries.Resources.Metadata(2, cancellationToken: cancellationToken);
        _publications.Add(Root, new(root));
    }

    private StaticStructureOperation(StaticStructureQueries.Snapshot snapshot, ImmutableDictionary<StaticScopeKey, FrozenPublication> publications,
        ImmutableDictionary<Algorithm, Algorithm> views, ImmutableDictionary<Algorithm, Algorithm> resolvedSources, StaticScopeKey declaring,
        Algorithm loadedBody, Pattern pattern, StaticQueryLimits limits, CompletedStaticStructures? completed, long retainedStorageUnits, CancellationToken cancellationToken)
    {
        Queries = new(snapshot, limits, cancellationToken);
        Queries.Resources.Metadata(retainedStorageUnits - snapshot.RetainedStorageUnits, work: 0, cancellationToken: cancellationToken);
        _unitPattern = pattern;
        _frozenPublications = publications;
        _frozenViews = views;
        _frozenResolvedSources = resolvedSources;
        _completedBase = completed;
        Root = Queries.MaterializedBranchIn(declaring, loadedBody, pattern);
        Queries.Resources.Metadata(2, cancellationToken: cancellationToken);
        _publications.Add(Root, new(loadedBody));
    }

    /// <summary>One standalone scope extension over immutable source facts; this never imports completion eligibility.</summary>
    internal StaticStructureOperation(StaticStructureQueries.Snapshot snapshot, StaticQueryLimits limits,
        StaticScopeKey declaring, Algorithm body, Pattern? pattern, StaticAstPhase phase, object? ownerIdentity,
        CancellationToken cancellationToken = default)
    {
        Queries = new(snapshot, limits, phase, cancellationToken);
        Root = pattern is null ? Queries.BodyIn(declaring, body, ownerIdentity)
            : Queries.BranchBodyIn(declaring, body, pattern, ownerIdentity);
        Queries.RequireInputPhase(Root, phase);
        Queries.Resources.Metadata(2, cancellationToken: cancellationToken);
        _publications.Add(Root, new(body));
    }

    internal StaticStructureQueries Queries { get; }
    internal Algorithm RawBody(Algorithm view) => _sources.GetValueOrDefault(view) ?? _frozenViews.GetValueOrDefault(view) ?? view;
    internal Algorithm? ResolvedSource(Algorithm written)
    {
        var source = RawBody(written);
        return _resolvedSources.GetValueOrDefault(source) ?? _frozenResolvedSources.GetValueOrDefault(source);
    }
    /// <summary>This unit's entry body; Queries.Root remains the original never-called program root.</summary>
    internal StaticScopeKey Root { get; }

    internal StaticStructureContext Context(StaticScopeKey scope) => new(this, scope);

    internal ElaboratedPropertyScope CreatePreludeScope(FrontEndTraversalObservations? observations = null)
    {
        Queries.Observations ??= observations;
        return ElaboratedScopeLookup.CreateScope(Queries.BodyOf(Queries.Keys.Root), observations: observations,
            memberIndexes: new OpenMemberIndexCache(observations), staticContext: Context(Queries.Keys.Root));
    }

    internal StaticScopeKey ContextOf(StaticScopeKey declaring, Algorithm body, Pattern? branchPattern = null)
    {
        Queries.EnsureUsable();
        var source = _sources.GetValueOrDefault(body) ?? _frozenViews.GetValueOrDefault(body) ?? body;
        if (_unitPattern is not null && ReferenceEquals(declaring, Root.Parent) && ReferenceEquals(branchPattern, _unitPattern)
            && ReferenceEquals(source, SourceOf(Root))) return Root;
        if (Queries.Keys.FirstDefinitionIn(declaring, source, branchPattern) is { } original
            && !ReferenceEquals(original, source) && !IsRegisteredDefinition(declaring, source, branchPattern)
            && !IsSuppliedSourceNode(source))
            throw new InvalidOperationException("A changed definition requires a new source admission or an explicitly registered pass view.");
        var key = branchPattern is null ? Queries.BodyIn(declaring, source) : Queries.BranchBodyIn(declaring, source, branchPattern);
        if (_publications.TryGetValue(key, out var publication))
        {
            if (!ReferenceEquals(source, publication.Source))
                throw new InvalidOperationException("A static context cannot replace its admitted source definition.");
        }
        else if (_frozenPublications.TryGetValue(key, out var frozen))
        {
            if (!ReferenceEquals(source, frozen.Source)) throw new InvalidOperationException("A frozen external definition cannot change.");
        }
        else { Queries.Resources.Metadata(2); _publications.Add(key, new(source)); }
        return key;
    }

    private bool IsRegisteredDefinition(StaticScopeKey declaring, Algorithm source, Pattern? pattern)
        => Queries.Keys.KnownDefinitionIn(declaring, source, pattern) is { } key
            && (ReferenceEquals(_publications.GetValueOrDefault(key)?.Source, source)
                || ReferenceEquals(_frozenPublications.GetValueOrDefault(key)?.Source, source));

    private bool IsSuppliedSourceNode(Algorithm body)
    {
        if (_suppliedSourceNodes is null)
        {
            // Membership in the supplied immutable AST is admission provenance, not a structural
            // selection. Only a declaration collision needs this bounded, once-per-unit census.
            _suppliedSourceNodes = new(ReferenceEqualityComparer.Instance);
            var pending = new Stack<object>();
            pending.Push(SourceOf(Root));
            pending.Push(SourceOf(Queries.Keys.Root));
            while (pending.TryPop(out var node))
            {
                Queries.EnsureUsable();
                Queries.Resources.Metadata(0);
                if (!_suppliedSourceNodes.Add(node)) continue;
                Queries.Resources.Metadata(2);
                for (var index = 0; AstStructuralPreflight.TryGetChild(node, index, out var child); index++)
                {
                    Queries.Resources.Metadata(0);
                    pending.Push(child);
                }
            }
        }
        return _suppliedSourceNodes.Contains(body);
    }

    internal Algorithm SourceOf(StaticScopeKey scope)
    {
        Queries.EnsureUsable();
        return Queries.BodyOf(scope);
    }
    internal void RequireDetectedRoot(Algorithm root)
    {
        Queries.EnsureUsable();
        if (!ReferenceEquals(Published(Root, StaticPublicationStage.Detected), root)
            || Published(Root, StaticPublicationStage.Resolved) is not null)
            throw new ArgumentException("Resolution requires this operation's exact, unresolved detected root.", nameof(root));
    }

    internal StaticFact Read(StaticQueryKey key) => Queries.Get(key);

    /// <summary>An intermediate pass copy is a view of an admitted definition, not a new query definition.</summary>
    internal void RegisterView(StaticScopeKey scope, Algorithm body)
    {
        Queries.EnsureUsable();
        var source = SourceOf(scope);
        if (!ReferenceEquals(source, body) && Queries.IsSourceDefinition(body))
            throw new InvalidOperationException("An admitted source definition cannot become another definition's pass view.");
        if (!ReferenceEquals(OpenProviderIdentity.DeclarationOf(source), OpenProviderIdentity.DeclarationOf(body)))
            throw new InvalidOperationException("A static source view must preserve declaration identity.");
        var existing = _sources.GetValueOrDefault(body) ?? _frozenViews.GetValueOrDefault(body);
        if (existing is not null && !ReferenceEquals(existing, source))
            throw new InvalidOperationException("A source view cannot represent two different raw definitions.");
        if (!_sources.ContainsKey(body)) Queries.Resources.Metadata(2);
        _sources[body] = source;
    }

    internal void Publish(StaticScopeKey scope, StaticPublicationStage stage, Algorithm body)
    {
        Queries.EnsureUsable();
        if (_frozenPublications.TryGetValue(scope, out var frozen))
        {
            var published = stage == StaticPublicationStage.Detected ? frozen.Detected : frozen.Resolved;
            if (!ReferenceEquals(body, published)) throw new InvalidOperationException("A completed external publication cannot change.");
            return;
        }
        if (!_publications.TryGetValue(scope, out var publication))
        {
            Queries.Resources.Metadata(2);
            _publications.Add(scope, publication = new(Queries.BodyOf(scope)));
        }
        if (!ReferenceEquals(OpenProviderIdentity.DeclarationOf(publication.Source), OpenProviderIdentity.DeclarationOf(body)))
            throw new InvalidOperationException("A published view must preserve its source declaration identity.");
        if (!ReferenceEquals(publication.Source, body) && Queries.IsSourceDefinition(body))
            throw new InvalidOperationException("An admitted source definition cannot become another definition's publication.");
        ref var slot = ref (stage == StaticPublicationStage.Detected ? ref publication.Detected : ref publication.Resolved);
        if (slot is not null && !ReferenceEquals(slot, body))
            throw new InvalidOperationException("A static context can publish each pass's body only once.");
        if (stage == StaticPublicationStage.Resolved && publication.Detected is null)
            throw new InvalidOperationException("Resolution publication requires the detected view.");
        var existing = _sources.GetValueOrDefault(body) ?? _frozenViews.GetValueOrDefault(body);
        if (existing is not null && !ReferenceEquals(existing, publication.Source))
            throw new InvalidOperationException("A published body cannot represent two different raw sources.");
        slot = body;
        if (!_sources.ContainsKey(body)) Queries.Resources.Metadata(2);
        _sources[body] = publication.Source;
        if (stage == StaticPublicationStage.Resolved && !_resolvedSources.ContainsKey(publication.Source))
        {
            Queries.Resources.Metadata(2);
            _resolvedSources.Add(publication.Source, body);
        }
        if (stage == StaticPublicationStage.Resolved && _structureCells.TryGetValue(scope, out var cell)) cell.Complete(body);
    }

    internal Algorithm? Published(StaticScopeKey scope, StaticPublicationStage stage)
    {
        Queries.EnsureUsable();
        if (_publications.TryGetValue(scope, out var publication))
            return stage == StaticPublicationStage.Detected ? publication.Detected : publication.Resolved;
        return _frozenPublications.TryGetValue(scope, out var frozen)
            ? stage == StaticPublicationStage.Detected ? frozen.Detected : frozen.Resolved : null;
    }

    /// <summary>
    /// One publication cell per selected terminal context, shared by transparent references. A carrier keeps its own
    /// cell. The raw body in a pending cell is a recipe only; readers must check IsPending before treating it as final.
    /// </summary>
    internal AliasStructureCell? StructureCell(StaticScopeKey scope)
    {
        var structure = Read(StaticQueryKey.TargetWalk(scope, StaticCycleCheck.Formation));
        if (structure.IsUnknown) throw new InvalidOperationException("An unresolved structural selection cannot publish a cell.");
        if (structure.Kind != StaticFactKind.Structure) return null;
        if (structure.Scope is not { } terminal) return null;
        if (_frozenPublications.TryGetValue(terminal, out var frozen)) return frozen.StructureCell;
        if (!_structureCells.TryGetValue(terminal, out var cell))
        {
            var resolved = Published(terminal, StaticPublicationStage.Resolved);
            Queries.Resources.Metadata(2);
            _structureCells.Add(terminal, cell = resolved is null
                ? AliasStructureCell.PendingOn(SourceOf(terminal)) : AliasStructureCell.Of(resolved));
        }
        return cell;
    }

    /// <summary>
    /// Freeze only at an error-free unit boundary. The returned continuation has no eager engine or token. A later
    /// materialization creates an independent engine, preserving finalized external facts and giving changed syntax
    /// a fresh contextual region. Failed units never get a continuation.
    /// </summary>
    internal Continuation Freeze(CancellationToken cancellationToken = default)
    {
        if (Published(Root, StaticPublicationStage.Resolved) is null)
            throw new InvalidOperationException("A deferred continuation requires the unit's completed resolution publication.");
        var snapshot = Queries.Freeze(cancellationToken);
        var publications = _frozenPublications.ToBuilder();
        var views = _frozenViews.ToBuilder();
        var resolvedSources = _frozenResolvedSources.ToBuilder();
        foreach (var (key, publication) in _publications)
        {
            cancellationToken.ThrowIfCancellationRequested();
            Queries.EnsureUsable();
            if (publication is { Detected: { } detected, Resolved: { } resolved })
            {
                if (!_structureCells.TryGetValue(key, out var cell)) { Queries.Resources.Metadata(2); _structureCells.Add(key, cell = AliasStructureCell.Of(resolved)); }
                if (cell?.IsPending == true) throw new InvalidOperationException("A completed body retained an unfinished structure publication.");
                Queries.Resources.Metadata(16);
                publications.Add(key, new(publication.Source, detected, resolved, cell));
                views[detected] = publication.Source;
                views[resolved] = publication.Source;
                if (!resolvedSources.ContainsKey(publication.Source)) resolvedSources.Add(publication.Source, resolved);
            }
        }
        cancellationToken.ThrowIfCancellationRequested();
        Queries.EnsureUsable();
        // Sealing completes the producer's immutable facts. An independently cancelled copy can
        // discard its export, but cannot poison that source publication while it is being sealed.
        _completed?.Seal(Queries.OperationToken);
        cancellationToken.ThrowIfCancellationRequested();
        Queries.EnsureUsable();
        return new(snapshot, publications.ToImmutable(), views.ToImmutable(), resolvedSources.ToImmutable(), _completed, snapshot.RetainedStorageUnits + 16L * publications.Count + (_completed?.RetainedStorageUnits ?? 0));
    }

    internal sealed class Continuation
    {
        private readonly StaticStructureQueries.Snapshot _snapshot;
        private readonly ImmutableDictionary<StaticScopeKey, FrozenPublication> _publications;
        private readonly ImmutableDictionary<Algorithm, Algorithm> _views;
        private readonly ImmutableDictionary<Algorithm, Algorithm> _resolvedSources;
        private readonly CompletedStaticStructures? _completed;
        private readonly long _retainedStorageUnits;
        internal Continuation(StaticStructureQueries.Snapshot snapshot, ImmutableDictionary<StaticScopeKey, FrozenPublication> publications,
            ImmutableDictionary<Algorithm, Algorithm> views, ImmutableDictionary<Algorithm, Algorithm> resolvedSources,
            CompletedStaticStructures? completed, long retainedStorageUnits)
            => (_snapshot, _publications, _views, _resolvedSources, _completed, _retainedStorageUnits)
                = (snapshot, publications, views, resolvedSources, completed, retainedStorageUnits);

        internal Algorithm Prelude => _snapshot.Contexts[_snapshot.Keys.Root].Body;

        internal StaticStructureOperation Materialize(StaticScopeKey declaring, Algorithm loadedBody, Pattern pattern,
            StaticQueryLimits limits, CancellationToken cancellationToken = default)
            => new(_snapshot, _publications, _views, _resolvedSources, declaring, loadedBody, pattern, limits, _completed, _retainedStorageUnits, cancellationToken);
    }
}
