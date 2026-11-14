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

    // REGION ALIASES (B3-5★): a context whose body the resolver served from the region another context processed holds the
    // very object that context's processing produced, so its descendants' resolved views are that context's — read through
    // the alias, never published once per PATH of a shared graph (exponential in its depth).
    private Dictionary<StaticScopeKey, StaticScopeKey>? _regionAliases;
    private readonly ImmutableDictionary<StaticScopeKey, StaticScopeKey> _frozenRegionAliases
        = ImmutableDictionary.Create<StaticScopeKey, StaticScopeKey>(ReferenceEqualityComparer.Instance);

    // DETECTED REGION ALIASES: the same law one pass earlier. A context detection served from a processed region (or a supplied
    // name-resolved body already registered in another context) holds that context's detected view, and so does every context
    // below it, read through the alias and never published once per path. Resolution may still process such a context on its
    // own (its region key is not detection's): what it publishes there is its own, over the counterpart's detected view.
    private Dictionary<StaticScopeKey, StaticScopeKey>? _detectedAliases;
    private readonly ImmutableDictionary<StaticScopeKey, StaticScopeKey> _frozenDetectedAliases
        = ImmutableDictionary.Create<StaticScopeKey, StaticScopeKey>(ReferenceEqualityComparer.Instance);
    private Dictionary<StaticScopeKey, StaticScopeKey>? _detectedProcessing;
    private int _detectedProcessingCharged;

    /// <summary>The bodies of this admission more than one path reaches; null when none is, and for a deferred unit.</summary>
    internal SharedBodyCensus? SharedBodies { get; init; }

    /// <summary>Admission walked every reachable node of this operation's tree, its prelude included, and met no open list.</summary>
    internal bool AdmittedWithoutOpens { get; init; }

    /// <summary>
    /// Admission walked every reachable node of this operation's tree — source ancestors, loaded modules and the
    /// prelude included — and met a declaration carrying the output-spreading marker
    /// (<see cref="Algorithm.OutputSpread"/>). Only then does implicit-argument resolution ask whether a call is
    /// spread, so a program without markers elaborates exactly as before, read for read. The queries hold the fact
    /// (Q7 orders a marked extension edge's names by it, D1).
    /// </summary>
    internal bool AdmittedWithOutputSpreadMarkers
    {
        get => Queries.AdmittedWithOutputSpreadMarkers;
        init => Queries.AdmittedWithOutputSpreadMarkers = value;
    }

    /// <summary>
    /// D1, the consumer boundary of <see cref="StaticStructureQueries.LoweredReceiver"/>: the marker of the declaration the
    /// receiver call of the written extension edge <paramref name="edge"/> invokes, when the edge is the call
    /// <c>F(R*, args)</c>; null for every other edge. Every fact is final here, and a callee whose selection never
    /// settled has no static identity (R1), so it is not marked.
    /// </summary>
    internal OutputSpreadMarker? LoweredReceiverMarker(StaticScopeKey scope, Expr.DotCall edge)
        => Queries.AdmittedWithOutputSpreadMarkers ? Queries.LoweredReceiver(scope, edge).Marker : null;

    internal StaticStructureOperation(Algorithm root, StaticQueryLimits limits, Algorithm? prelude = null, StaticAstPhase phase = StaticAstPhase.RawSource,
        CancellationToken cancellationToken = default)
    {
        Queries = new(root, limits, prelude, phase, cancellationToken);
        Root = Queries.Root;
        Queries.Resources.Metadata(2, cancellationToken: cancellationToken);
        _publications.Add(Root, new(root));
    }

    private StaticStructureOperation(StaticStructureQueries.Snapshot snapshot, ImmutableDictionary<StaticScopeKey, FrozenPublication> publications,
        ImmutableDictionary<Algorithm, Algorithm> views, ImmutableDictionary<Algorithm, Algorithm> resolvedSources,
        ImmutableDictionary<StaticScopeKey, StaticScopeKey> regionAliases, ImmutableDictionary<StaticScopeKey, StaticScopeKey> detectedAliases,
        StaticScopeKey declaring, Algorithm loadedBody, Pattern pattern, StaticQueryLimits limits, CompletedStaticStructures? completed, long retainedStorageUnits, CancellationToken cancellationToken)
    {
        Queries = new(snapshot, limits, cancellationToken);
        Queries.Resources.Metadata(retainedStorageUnits - snapshot.RetainedStorageUnits, work: 0, cancellationToken: cancellationToken);
        _unitPattern = pattern;
        _frozenPublications = publications;
        _frozenViews = views;
        _frozenResolvedSources = resolvedSources;
        _frozenRegionAliases = regionAliases;
        _frozenDetectedAliases = detectedAliases;
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
        if (stage == StaticPublicationStage.Resolved && DetectedView(scope) is null)
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

    /// <summary>The view <paramref name="stage"/> published for exactly <paramref name="scope"/> (see <see cref="ResolvedView"/>).</summary>
    internal Algorithm? Published(StaticScopeKey scope, StaticPublicationStage stage)
    {
        Queries.EnsureUsable();
        if (_publications.TryGetValue(scope, out var publication))
            return stage == StaticPublicationStage.Detected ? publication.Detected : publication.Resolved;
        return _frozenPublications.TryGetValue(scope, out var frozen)
            ? stage == StaticPublicationStage.Detected ? frozen.Detected : frozen.Resolved : null;
    }

    /// <summary>
    /// The detected view <paramref name="scope"/> holds: its own publication, else, below a region detection served from
    /// another context (<see cref="AliasDetectedRegion"/>), its counterpart's.
    /// </summary>
    internal Algorithm? DetectedView(StaticScopeKey scope)
    {
        if (Published(scope, StaticPublicationStage.Detected) is { } published) return published;
        var processing = DetectedProcessingContext(scope);
        return ReferenceEquals(processing, scope) ? null : Published(processing, StaticPublicationStage.Detected);
    }

    /// <summary>
    /// Records that <paramref name="reach"/> holds the detected view <paramref name="processed"/> holds: everything below the
    /// reach is read through the alias.
    /// </summary>
    internal void AliasDetectedRegion(StaticScopeKey reach, StaticScopeKey processed)
    {
        Queries.EnsureUsable();
        if (ReferenceEquals(reach, processed) || _frozenDetectedAliases.ContainsKey(reach)) return;
        _detectedAliases ??= new(ReferenceEqualityComparer.Instance);
        if (_detectedAliases.TryAdd(reach, processed)) Queries.Resources.Metadata(2);
        _detectedProcessing?.Clear();
    }

    /// <summary>
    /// The context whose processing produced what <paramref name="scope"/> holds: the same path below the alias of its nearest
    /// aliased ancestor (or itself), followed to a context no alias applies to. <paramref name="scope"/> itself when none does.
    /// </summary>
    internal StaticScopeKey DetectedProcessingContext(StaticScopeKey scope)
    {
        Queries.EnsureUsable();
        if (_detectedAliases is null && _frozenDetectedAliases.IsEmpty) return scope;
        // One step per level, memoized by context: a context's answer is its parent's answer's child, so a read costs what
        // it has not read yet, never the chain again. An alias is followed to its end: the target of one is a context
        // detection processed or another reach.
        var memo = _detectedProcessing ??= new(ReferenceEqualityComparer.Instance);
        var path = new Stack<StaticScopeKey>();
        for (StaticScopeKey? at = scope; at is not null && !memo.ContainsKey(at); at = at.Parent) path.Push(at);
        while (path.TryPop(out var key))
        {
            // Retained once: a memo refilled after a new alias replaces entries, it does not add storage.
            Queries.Resources.Metadata(memo.Count < _detectedProcessingCharged ? 0 : 2);
            _detectedProcessingCharged = Math.Max(_detectedProcessingCharged, memo.Count + 1);
            var processing = key;
            if (key.Parent is { } parent && !ReferenceEquals(memo[parent], parent)
                && Queries.Keys.KnownDefinitionIn(memo[parent], SourceOf(key), key.BindingRegion) is { } counterpart)
                processing = counterpart;
            while (TryGetDetectedAlias(processing, out var further)) processing = further;
            memo[key] = processing;
        }

        return memo[scope];
    }

    private bool TryGetDetectedAlias(StaticScopeKey reach, [System.Diagnostics.CodeAnalysis.NotNullWhen(true)] out StaticScopeKey? processed)
        => _detectedAliases is not null && _detectedAliases.TryGetValue(reach, out processed)
            || _frozenDetectedAliases.TryGetValue(reach, out processed);

    /// <summary>
    /// The resolved view a read of <paramref name="scope"/> observes: its own publication, else — below a region the
    /// resolver served from another context's processing (<see cref="AliasResolvedRegion"/>) — that context's
    /// counterpart's (<see cref="RegionCounterpart"/>). A check of what the resolver processed IN a context reads
    /// <see cref="Published"/>.
    /// </summary>
    internal Algorithm? ResolvedView(StaticScopeKey scope)
        => OwnResolvedView(scope)
            ?? (RegionCounterpart(scope) is { } counterpart ? Published(counterpart, StaticPublicationStage.Resolved) : null);

    /// <summary>
    /// What resolution holds for exactly <paramref name="scope"/>: its publication, or a supplied callable alias below a
    /// detected alias, which name-resolved registration resolved once (an alias is its own resolved form).
    /// </summary>
    internal Algorithm? OwnResolvedView(StaticScopeKey scope)
    {
        if (Published(scope, StaticPublicationStage.Resolved) is { } published) return published;
        if (SourceOf(scope) is not Algorithm.Alias) return null;
        var processing = DetectedProcessingContext(scope);
        return ReferenceEquals(processing, scope) ? null : Published(processing, StaticPublicationStage.Resolved);
    }

    /// <summary>
    /// The resolved view an EARLIER operation completed for <paramref name="scope"/> (the frozen continuation a deferred
    /// unit materializes from) — never one this operation published — read like <see cref="ResolvedView"/>.
    /// </summary>
    internal Algorithm? EarlierResolvedView(StaticScopeKey scope)
    {
        Queries.EnsureUsable();
        if (_frozenPublications.TryGetValue(scope, out var frozen))
            return frozen.Resolved;
        // A view THIS operation published is never earlier; a context it merely registered (`ContextOf` keeps an empty
        // slot for every new key) may still lie below a frozen served region, whose counterpart's view is.
        if (_publications.TryGetValue(scope, out var local) && (local.Detected is not null || local.Resolved is not null)
            || _frozenRegionAliases.IsEmpty)
            return null;
        return RegionCounterpart(scope) is { } counterpart && _frozenPublications.TryGetValue(counterpart, out var mapped)
            ? mapped.Resolved : null;
    }

    /// <summary>
    /// Records that the resolver served the region of <paramref name="reach"/> from its processing in
    /// <paramref name="processed"/> (the same processed object, B3-5★): every context below the reach has its counterpart
    /// below the processing context, whose resolved views it observes — never published once per PATH of a shared graph,
    /// which is exponential in its depth.
    /// </summary>
    internal void AliasResolvedRegion(StaticScopeKey reach, StaticScopeKey processed)
    {
        Queries.EnsureUsable();
        if (ReferenceEquals(reach, processed) || _frozenRegionAliases.ContainsKey(reach))
            return;
        _regionAliases ??= new(ReferenceEqualityComparer.Instance);
        if (_regionAliases.TryAdd(reach, processed))
            Queries.Resources.Metadata(2);
    }

    /// <summary>
    /// The directly published context whose resolved views a context without its own observes (<see cref="ResolvedView"/>):
    /// the same path below the processing context of its nearest region-aliased ancestor, followed while that context is
    /// itself unpublished; null when no region alias applies.
    /// </summary>
    internal StaticScopeKey? RegionCounterpart(StaticScopeKey scope)
    {
        Queries.EnsureUsable();
        // Every step consumes a distinct alias of an acyclic map, so the count bounds the chase.
        var remaining = (_regionAliases?.Count ?? 0) + _frozenRegionAliases.Count;
        for (var current = scope; remaining-- > 0 && RegionAliasStep(current) is { } mapped; current = mapped)
        {
            if (Published(mapped, StaticPublicationStage.Resolved) is not null)
                return mapped;
        }

        return null;
    }

    private bool TryGetRegionAlias(StaticScopeKey reach, [System.Diagnostics.CodeAnalysis.NotNullWhen(true)] out StaticScopeKey? processed)
        => _regionAliases is not null && _regionAliases.TryGetValue(reach, out processed)
            || _frozenRegionAliases.TryGetValue(reach, out processed);

    /// <summary>The same path below the nearest region alias of <paramref name="key"/> or its ancestors; null when none applies.</summary>
    private StaticScopeKey? RegionAliasStep(StaticScopeKey key) => AliasStep(key, TryGetRegionAlias);

    private delegate bool TryGetAlias(StaticScopeKey reach, [System.Diagnostics.CodeAnalysis.NotNullWhen(true)] out StaticScopeKey? processed);

    private StaticScopeKey? AliasStep(StaticScopeKey key, TryGetAlias tryGetAlias)
    {
        StaticScopeKey? reach = null;
        for (StaticScopeKey? at = key; at is not null; at = at.Parent)
        {
            Queries.Resources.Work();
            if (tryGetAlias(at, out _))
            {
                reach = at;
                break;
            }
        }

        if (reach is null || !tryGetAlias(reach, out var mapped))
            return null;
        if (ReferenceEquals(reach, key))
            return mapped;
        var path = new Stack<StaticScopeKey>();
        for (var at = key; !ReferenceEquals(at, reach); at = at.Parent!)
            path.Push(at);
        while (path.TryPop(out var child))
        {
            Queries.Resources.Work();
            var source = SourceOf(child);
            StaticScopeKey? next;
            // A served context has no definitions of its own below it: they are its counterpart's.
            while ((next = Queries.Keys.KnownDefinitionIn(mapped, source, child.BindingRegion)) is null)
            {
                Queries.Resources.Work();
                if (!tryGetAlias(mapped, out var further)) return null;
                mapped = further;
            }
            mapped = next;
        }

        return mapped;
    }

    /// <summary>
    /// Completes every structure cell still pending once resolution has ended, from the resolved view its context observes
    /// (<see cref="ResolvedView"/>).
    /// </summary>
    internal void CompletePendingStructureCells()
    {
        Queries.EnsureUsable();
        foreach (var (scope, cell) in _structureCells)
        {
            if (cell.IsPending && ResolvedView(scope) is { } body)
                cell.Complete(body);
        }
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
            var resolved = ResolvedView(terminal);
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
        var regionAliases = _frozenRegionAliases.ToBuilder();
        var detectedAliases = _frozenDetectedAliases.ToBuilder();
        if (_detectedAliases is not null)
        {
            foreach (var (reach, processed) in _detectedAliases)
            {
                cancellationToken.ThrowIfCancellationRequested();
                detectedAliases[reach] = processed;
            }
        }

        if (_regionAliases is not null)
        {
            foreach (var (reach, processed) in _regionAliases)
            {
                cancellationToken.ThrowIfCancellationRequested();
                regionAliases[reach] = processed;
            }
        }

        foreach (var (key, publication) in _publications)
        {
            cancellationToken.ThrowIfCancellationRequested();
            Queries.EnsureUsable();
            if (publication is { Resolved: { } resolved } && (publication.Detected ?? DetectedView(key)) is { } detected)
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
        return new(snapshot, publications.ToImmutable(), views.ToImmutable(), resolvedSources.ToImmutable(), regionAliases.ToImmutable(), detectedAliases.ToImmutable(), _completed,
            snapshot.RetainedStorageUnits + 16L * publications.Count + 2L * (regionAliases.Count + detectedAliases.Count) + (_completed?.RetainedStorageUnits ?? 0))
        {
            // A deferred unit's calls resolve into the eager tree too, so its operation inherits this admission's fact.
            AdmittedWithOutputSpreadMarkers = AdmittedWithOutputSpreadMarkers,
        };
    }

    internal sealed class Continuation
    {
        private readonly StaticStructureQueries.Snapshot _snapshot;
        private readonly ImmutableDictionary<StaticScopeKey, FrozenPublication> _publications;
        private readonly ImmutableDictionary<Algorithm, Algorithm> _views;
        private readonly ImmutableDictionary<Algorithm, Algorithm> _resolvedSources;
        private readonly ImmutableDictionary<StaticScopeKey, StaticScopeKey> _regionAliases;
        private readonly ImmutableDictionary<StaticScopeKey, StaticScopeKey> _detectedAliases;
        private readonly CompletedStaticStructures? _completed;
        private readonly long _retainedStorageUnits;
        internal Continuation(StaticStructureQueries.Snapshot snapshot, ImmutableDictionary<StaticScopeKey, FrozenPublication> publications,
            ImmutableDictionary<Algorithm, Algorithm> views, ImmutableDictionary<Algorithm, Algorithm> resolvedSources,
            ImmutableDictionary<StaticScopeKey, StaticScopeKey> regionAliases, ImmutableDictionary<StaticScopeKey, StaticScopeKey> detectedAliases,
            CompletedStaticStructures? completed, long retainedStorageUnits)
            => (_snapshot, _publications, _views, _resolvedSources, _regionAliases, _detectedAliases, _completed, _retainedStorageUnits)
                = (snapshot, publications, views, resolvedSources, regionAliases, detectedAliases, completed, retainedStorageUnits);

        internal Algorithm Prelude => _snapshot.Contexts[_snapshot.Keys.Root].Body;

        /// <summary>
        /// Whether the eager admission this continuation froze met a declaration-level output-spreading marker
        /// (<see cref="StaticStructureOperation.AdmittedWithOutputSpreadMarkers"/>).
        /// </summary>
        internal bool AdmittedWithOutputSpreadMarkers { get; init; }

        /// <summary>The deferred unit's operation over a loaded unit that holds no output-spreading marker of its own.</summary>
        internal StaticStructureOperation Materialize(StaticScopeKey declaring, Algorithm loadedBody, Pattern pattern,
            StaticQueryLimits limits, CancellationToken cancellationToken = default)
            => Materialize(declaring, loadedBody, pattern, limits, loadedUnitHasOutputSpreadMarkers: false, cancellationToken);

        /// <summary>
        /// The deferred unit's operation. It examines calls for output spreading when the eager admission met a marker or
        /// the loaded unit itself holds one (<paramref name="loadedUnitHasOutputSpreadMarkers"/>, from its measurement): a
        /// deferred call may resolve to either.
        /// </summary>
        internal StaticStructureOperation Materialize(StaticScopeKey declaring, Algorithm loadedBody, Pattern pattern,
            StaticQueryLimits limits, bool loadedUnitHasOutputSpreadMarkers, CancellationToken cancellationToken = default)
            => new(_snapshot, _publications, _views, _resolvedSources, _regionAliases, _detectedAliases, declaring, loadedBody, pattern, limits, _completed, _retainedStorageUnits, cancellationToken)
            {
                AdmittedWithOutputSpreadMarkers = AdmittedWithOutputSpreadMarkers || loadedUnitHasOutputSpreadMarkers,
            };
    }
}
