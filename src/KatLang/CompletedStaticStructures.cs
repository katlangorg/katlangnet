using System.Collections.Immutable;

namespace KatLang;

/// <summary>
/// Completed Q1–Q7 projections. Scope keys contain declaration/pattern identity only: no query definition, engine,
/// token, physical scope or raw-to-processed map is retained. Local erroneous trees may carry these facts; only the
/// pipeline's successful freeze can share them with another unit. Exposure retargets views before sealing the table.
/// </summary>
internal sealed class CompletedStaticStructures : StaticLookupFacts
{
    internal readonly record struct Selection(StaticFactKind Kind, StaticScopeKey? Target = null, OpenProviderIdentity? Identity = null)
    {
        internal static Selection Unavailable => new(StaticFactKind.Unknown);
    }

    internal sealed record BodyFacts(Algorithm? Body, Selection Receiver, Selection Open,
        IReadOnlyDictionary<string, StaticScopeKey> Members, IReadOnlySet<string> Parameters, ImmutableArray<Selection> Providers,
        ImmutableHashSet<string>? UnavailableOpenNames = null, ImmutableHashSet<string>? AmbiguousOpenNames = null,
        bool IsProvisional = false, Selection? RequirementReceiver = null, Selection? RequirementOpen = null);

    private ImmutableDictionary<StaticScopeKey, BodyFacts> _bodies;
    private ImmutableDictionary<(StaticScopeKey Parent, object Declaration, object? Region), StaticScopeKey?> _children;
    // Most keys use the body's declaration. An explicitly supplied owner identity may differ;
    // retain that exception so a missing ordinary child key is conclusive without rebuilding
    // the versioned, body-specific catalog. Only genuine exceptions need this additional metadata.
    private ImmutableHashSet<(StaticScopeKey Parent, object Declaration, object? Region)> _alternateChildDeclarations;
    private Dictionary<StaticScopeKey, BodyFacts>? _local = new(ReferenceEqualityComparer.Instance);
    private bool _failed;
    private StaticQueryResourceBudget? _resources;

    // B3-5★ REGION REACHES. A reach is a context the resolver served from another context's processing of the same region
    // (`StaticStructureOperation.AliasResolvedRegion`): it has facts of its own, and every context BELOW it is a PROJECTION
    // of its counterpart below the processing context — created only when a consumer reaches it, its facts the
    // counterpart's with every selection inside the region re-based onto the reach and re-declared there, and its body the
    // view the exposed tree holds at that occurrence (exposure may copy one occurrence's subtree; see RetargetTree). So a
    // shared graph is never published once per path, and no context reads another occurrence's declaring identity or view.
    // Each projected context has ONE key in this table — the compilation's own key when it named one (paired with its
    // counterpart definition by definition, so definitions sharing one declaration stay apart), else one the table creates
    // per counterpart — and a key the table did not create (another unit's, a consumer's own) reads the facts of its
    // context's key wherever its declaration names one context. A member whose context restarts outside the region (a
    // loaded module's root) is the same context from every occurrence and is never projected.
    internal sealed record Reach(StaticScopeKey Processed, OpenProviderIdentity ReachIdentity, OpenProviderIdentity ProcessedIdentity);

    /// <summary>A projected context: its reach, its counterpart and, when exposure gave this occurrence a view of its own, that view.</summary>
    private sealed record Projection(StaticScopeKey Reach, StaticScopeKey Counterpart, Algorithm? View = null);

    private ImmutableDictionary<StaticScopeKey, Reach> _reaches;
    // One list per processing context (a family may serve many branch occurrences from one): appending stays logarithmic.
    private ImmutableDictionary<StaticScopeKey, ImmutableList<StaticScopeKey>> _reachesOfProcessed;
    // Every projection table below is read and written under this gate only: sealed facts may serve parallel readers. The
    // gate is never held while the body index is built (that index reads projected facts under its own gate).
    private readonly object _projectionGate = new();
    private ImmutableDictionary<StaticScopeKey, Projection> _projections;
    private ImmutableDictionary<(StaticScopeKey Parent, StaticScopeKey Counterpart), StaticScopeKey> _projectedChildren;
    // A later unit inherits the projections this compilation made before sealing — keys, views and all; what a sealed table
    // projects afterwards is its readers' cache, never inherited or charged (both stay independent of who read what, when).
    private ImmutableDictionary<StaticScopeKey, Projection>? _sealedProjections;
    private ImmutableDictionary<(StaticScopeKey Parent, StaticScopeKey Counterpart), StaticScopeKey>? _sealedProjectedChildren;
    // A projected occurrence by the view exposure gave it, under its parent and region (`Child` of that copy).
    private ImmutableDictionary<(StaticScopeKey Parent, object View, object? Region), StaticScopeKey> _viewedChildren;
    private ImmutableDictionary<(StaticScopeKey Parent, object View, object? Region), StaticScopeKey>? _sealedViewedChildren;
    private readonly Dictionary<StaticScopeKey, (Projection Projection, BodyFacts? Counterpart, BodyFacts? Facts)> _projectedFacts
        = new(ReferenceEqualityComparer.Instance);
    private bool _projectionSuspended;

    internal CompletedStaticStructures(StaticScopeKey prelude, CompletedStaticStructures? previous = null, StaticQueryResourceBudget? resources = null)
    {
        previous?.EnsureUsable();
        _resources = resources;
        if (previous is { IsSealed: false }) throw new InvalidOperationException("Only sealed completed facts may cross a unit boundary.");
        RetainedStorageUnits = previous?.RetainedStorageUnits ?? 0;
        HasProvisional = previous?.HasProvisional ?? false;
        PreludeKey = prelude;
        _bodies = previous?._bodies ?? ImmutableDictionary.Create<StaticScopeKey, BodyFacts>(ReferenceEqualityComparer.Instance);
        _children = previous?._children ?? ImmutableDictionary.Create<(StaticScopeKey, object, object?), StaticScopeKey?>(ChildComparer.Instance);
        _alternateChildDeclarations = previous?._alternateChildDeclarations
            ?? ImmutableHashSet.Create<(StaticScopeKey, object, object?)>(ChildComparer.Instance);
        _reaches = previous?._reaches ?? ImmutableDictionary.Create<StaticScopeKey, Reach>(ReferenceEqualityComparer.Instance);
        _reachesOfProcessed = previous?._reachesOfProcessed
            ?? ImmutableDictionary.Create<StaticScopeKey, ImmutableList<StaticScopeKey>>(ReferenceEqualityComparer.Instance);
        _projections = previous?._sealedProjections ?? ImmutableDictionary.Create<StaticScopeKey, Projection>(ReferenceEqualityComparer.Instance);
        _projectedChildren = previous?._sealedProjectedChildren
            ?? ImmutableDictionary.Create<(StaticScopeKey, StaticScopeKey), StaticScopeKey>(KeyPairComparer.Instance);
        _viewedChildren = previous?._sealedViewedChildren
            ?? ImmutableDictionary.Create<(StaticScopeKey, object, object?), StaticScopeKey>(ChildComparer.Instance);
    }

    internal static void Attach(Algorithm body, CompletedStructurePublication publication)
    {
        if (publication.Entry is { } entry && publication.Facts.Facts(entry)?.Body is null)
            publication = publication with { EntryView = body };
        switch (body)
        {
            case Algorithm.User user: user.CompletedStructure = publication; break;
            case Algorithm.Conditional family: family.CompletedStructure = publication; break;
            case Algorithm.Alias alias: alias.CompletedStructure = publication; break;
            case Algorithm.Builtin: throw new InvalidOperationException("A builtin cannot retain a program publication.");
        }
    }

    internal override StaticScopeKey PreludeKey { get; }
    internal bool IsSealed => _local is null;
    internal bool HasProvisional { get; private set; }
    private int _viewVersion;
    internal override int ViewVersion => _viewVersion;
    internal long RetargetNodeVisits { get; private set; }
    /// <summary>Projected facts computed (B3-5★; read under the projection gate): every build is a counterpart change or a first read.</summary>
    internal long ProjectedFactsBuilds { get; private set; }
    internal long RetainedStorageUnits { get; private set; }
    internal bool IsFailed => _failed || _resources?.IsFailed == true;
    internal void RejectUnsealed()
    {
        if (!IsSealed) _failed = true;
    }
    internal int Count => _bodies.Count + (_local?.Keys.Count(k => !_bodies.ContainsKey(k)) ?? 0);
    internal override BodyFacts? Facts(StaticScopeKey key)
    {
        EnsureUsable();
        var direct = _local?.GetValueOrDefault(key) ?? _bodies.GetValueOrDefault(key);
        if (direct is not null || _reaches.IsEmpty || key.Parent is null)
            return direct;
        lock (_projectionGate)
            return _projectionSuspended ? null : ProjectedFacts(key);
    }

    /// <summary>Registers a reach (B3-5★): <paramref name="reach"/> was served from <paramref name="processed"/>'s processing.</summary>
    internal void AddReach(StaticScopeKey reach, StaticScopeKey processed, OpenProviderIdentity reachIdentity, OpenProviderIdentity processedIdentity)
    {
        EnsureUsable();
        if (_local is null) throw new InvalidOperationException("A sealed structural publication is immutable.");
        if (_reaches.ContainsKey(reach)) return;
        _resources?.Metadata(6);
        // A later unit inherits the record and both declaring chains (whose construction its producer charged).
        RetainedStorageUnits += 6 + ((long)reachIdentity.Length + processedIdentity.Length + 7) / 8;
        _reaches = _reaches.Add(reach, new(processed, reachIdentity, processedIdentity));
        _reachesOfProcessed = _reachesOfProcessed.SetItem(processed,
            (_reachesOfProcessed.GetValueOrDefault(processed) ?? ImmutableList<StaticScopeKey>.Empty).Add(reach));
    }

    /// <summary>Whether <paramref name="key"/> is a reach (see <see cref="AddReach"/>).</summary>
    internal bool IsReach(StaticScopeKey key) => _reaches.ContainsKey(key);

    /// <summary>
    /// Suspends projection while the compilation's own facts are being built: nothing below a reach may be projected before
    /// every published context's facts exist (<see cref="AdoptBelowReaches"/> resumes it).
    /// </summary>
    internal void SuspendProjection()
    {
        lock (_projectionGate)
            _projectionSuspended = true;
    }

    /// <summary>
    /// Adopts the compilation's own contexts below reaches (parents first), each paired with its counterpart, as their
    /// projections, then resumes projection: a member key or selection target the compilation already named is the ONE key
    /// of its context.
    /// </summary>
    internal void AdoptBelowReaches(IReadOnlyList<(StaticScopeKey Key, StaticScopeKey Counterpart)> pairs)
    {
        EnsureUsable();
        if (_local is null) throw new InvalidOperationException("A sealed structural publication is immutable.");
        lock (_projectionGate)
        {
            foreach (var (key, counterpart) in pairs)
            {
                _resources?.Metadata(0);
                if (!_projections.ContainsKey(key) && key.Parent is { } parent && ProjectionRootOf(parent) is not null
                    && !_projectedChildren.ContainsKey((parent, counterpart)))
                    Adopt(parent, counterpart, key);
            }

            _projectionSuspended = false;
        }
    }

    // ── Projection (every method below runs under _projectionGate) ──

    private StaticScopeKey? ProjectionRootOf(StaticScopeKey key)
        => _reaches.ContainsKey(key) ? key : _projections.TryGetValue(key, out var projection) ? projection.Reach : null;

    private StaticScopeKey CounterpartOf(StaticScopeKey key)
        => _reaches.TryGetValue(key, out var reach) ? reach.Processed : _projections[key].Counterpart;

    private BodyFacts? FactsUnderGate(StaticScopeKey key)
        => _local?.GetValueOrDefault(key) ?? _bodies.GetValueOrDefault(key) ?? ProjectedFacts(key);

    /// <summary>
    /// The child of <paramref name="parent"/> with this declaration and region: a published one, or — below a reach — the
    /// projection of its counterpart's child (out through the counterparts to the context that publishes it, then back in
    /// through their projections: nested reaches never recurse).
    /// </summary>
    private StaticScopeKey? CounterpartChild(StaticScopeKey parent, object declaration, object? region)
    {
        var owners = new Stack<StaticScopeKey>();
        StaticScopeKey? child;
        // Region aliases are acyclic, so the counterparts of one chain are distinct; the bound only guards that invariant.
        var remaining = _reaches.Count + _projections.Count + 1;
        for (var at = parent; !_children.TryGetValue((at, declaration, region), out child); at = CounterpartOf(at))
        {
            if (ProjectionRootOf(at) is null || remaining-- == 0)
                return null;
            owners.Push(at);
        }

        _resources?.Metadata(0, 1L + owners.Count);
        while (child is not null && owners.TryPop(out var owner))
            child = ProjectedChild(owner, child);
        return child;
    }

    /// <summary>
    /// The ONE key of the context <paramref name="key"/> names: the key itself when this table knows it (published, a reach,
    /// or a projection); otherwise, below a reach, its context's projection — whoever constructed the key; null when it
    /// names no context with facts here.
    /// </summary>
    private StaticScopeKey? CanonicalOf(StaticScopeKey key)
    {
        var path = new Stack<StaticScopeKey>();
        var at = key;
        while (!_reaches.ContainsKey(at) && !_projections.ContainsKey(at) && _local?.ContainsKey(at) != true && !_bodies.ContainsKey(at))
        {
            path.Push(at);
            if (at.Parent is not { } parent)
                return null;
            at = parent;
        }

        _resources?.Metadata(0, 1L + path.Count);
        StaticScopeKey? canonical = at;
        while (canonical is not null && path.TryPop(out var step))
            canonical = CounterpartChild(canonical, step.Declaration, step.BindingRegion);
        return canonical;
    }

    /// <summary>The ONE key of <paramref name="parent"/>'s child corresponding to <paramref name="counterpart"/>.</summary>
    private StaticScopeKey ProjectedChild(StaticScopeKey parent, StaticScopeKey counterpart)
    {
        if (_projectedChildren.TryGetValue((parent, counterpart), out var known))
            return known;
        var key = new StaticScopeKey(parent, counterpart.Declaration, counterpart.BindingRegion);
        Adopt(parent, counterpart, key);
        return key;
    }

    private void Adopt(StaticScopeKey parent, StaticScopeKey counterpart, StaticScopeKey key)
    {
        // The compilation charges what it projects; a sealed table's projections are its readers' cache (see the fields).
        _resources?.Metadata(4);
        if (_local is not null) RetainedStorageUnits += 4;
        _projections = _projections.Add(key, new(ProjectionRootOf(parent)!, counterpart));
        _projectedChildren = _projectedChildren.Add((parent, counterpart), key);
    }

    private BodyFacts? ProjectedFacts(StaticScopeKey key)
    {
        if (!_projections.TryGetValue(key, out var projection))
        {
            // A key this table did not create names the context of its ONE key, whose facts it reads.
            return CanonicalOf(key) is { } canonical && !ReferenceEquals(canonical, key) ? FactsUnderGate(canonical) : null;
        }

        // A projection's facts are a function of its record (reach, counterpart, view) and its counterpart's facts only, so
        // they are recomputed exactly when one of those two objects changed (a revised or retargeted counterpart, a view).
        // Validating reads the counterpart chain, one hop per level, so even a current entry charges its hop.
        var counterpartFacts = FactsUnderGate(projection.Counterpart);
        if (_projectedFacts.TryGetValue(key, out var cached)
            && ReferenceEquals(cached.Projection, projection) && ReferenceEquals(cached.Counterpart, counterpartFacts))
        {
            _resources?.Metadata(0);
            return cached.Facts;
        }
        var reach = projection.Reach;
        var record = _reaches[reach];
        var facts = counterpartFacts;
        if (facts is not null)
        {
            var slots = (long)facts.Members.Count + facts.Providers.Length;
            _resources?.Metadata(4 + 2 * slots, 1 + slots);
            var members = new Dictionary<string, StaticScopeKey>(facts.Members.Count, StringComparer.Ordinal);
            foreach (var (name, member) in facts.Members)
                members[name] = ReferenceEquals(member.Parent, projection.Counterpart) ? ProjectedChild(key, member) : member;
            facts = facts with
            {
                Body = projection.View ?? facts.Body,
                Members = members,
                Receiver = Rebased(facts.Receiver, reach, record),
                Open = Rebased(facts.Open, reach, record),
                Providers = Rebased(facts.Providers, reach, record),
                RequirementReceiver = facts.RequirementReceiver is { } receiver ? Rebased(receiver, reach, record) : null,
                RequirementOpen = facts.RequirementOpen is { } open ? Rebased(open, reach, record) : null,
            };
        }

        ProjectedFactsBuilds++;
        _projectedFacts[key] = (projection, counterpartFacts, facts);
        return facts;
    }

    /// <summary>
    /// The number of projections between <paramref name="key"/> and the published context its counterparts lead to: what
    /// a projection's view is compared with is final once every projection of a lower level has its view.
    /// </summary>
    private int ProjectionLevel(StaticScopeKey key)
    {
        var level = 0;
        for (var at = key; _projections.TryGetValue(at, out var projection); at = projection.Counterpart)
            level++;
        _resources?.Metadata(0, level);
        return level;
    }

    /// <summary>
    /// Records the view the exposed tree holds at a projected occurrence, and whether its subtree needs the same: an
    /// occurrence holding its counterpart's view (exposure shared it) holds that view's whole subtree, so nothing below it
    /// differs; one holding a copy of its own keeps that copy as its body.
    /// </summary>
    private bool RetargetProjection(StaticScopeKey key, Algorithm body)
    {
        lock (_projectionGate)
        {
            if (!_projections.TryGetValue(key, out var projection) || ProjectedFacts(key) is not { Body: { } current }
                || ReferenceEquals(current, body))
                return false;
            if (!ReferenceEquals(OpenProviderIdentity.DeclarationOf(current), OpenProviderIdentity.DeclarationOf(body)))
                throw new InvalidOperationException("Exposure must preserve a published declaration identity.");
            _resources?.Metadata(2);
            RetainedStorageUnits += 2;
            _projections = _projections.SetItem(key, projection with { View = body });
            _viewedChildren = _viewedChildren.SetItem((key.Parent!, body, key.BindingRegion), key);
            _viewVersion++;
            return true;
        }
    }

    /// <summary>
    /// A counterpart's selection as the reach's context reads it: a target inside the region (at or below the processing
    /// context) is the reach's corresponding context, re-declared there; a target outside the region is the same declaration
    /// from every occurrence (the region's free names select it alike).
    /// </summary>
    /// <summary>The counterpart's providers as the reach's context reads them: the same array when none lies inside the region.</summary>
    private ImmutableArray<Selection> Rebased(ImmutableArray<Selection> selections, StaticScopeKey reach, Reach record)
    {
        Selection[]? rebased = null;
        for (var index = 0; index < selections.Length; index++)
        {
            var selection = Rebased(selections[index], reach, record);
            if (rebased is null)
            {
                if (selection == selections[index])
                    continue;
                rebased = selections.ToArray();
            }

            rebased[index] = selection;
        }

        return rebased is null ? selections : System.Runtime.InteropServices.ImmutableCollectionsMarshal.AsImmutableArray(rebased);
    }

    private Selection Rebased(Selection selection, StaticScopeKey reach, Reach record)
    {
        if (selection.Target is not { } target)
            return selection;
        var path = new Stack<StaticScopeKey>();
        var at = target;
        while (at is not null && !ReferenceEquals(at, record.Processed))
        {
            path.Push(at);
            at = at.Parent;
        }

        _resources?.Metadata(0, 1L + path.Count);
        if (at is null)
            return selection;
        var rebased = reach;
        while (path.TryPop(out var step))
            rebased = ProjectedChild(rebased, step);
        if (selection.Identity is not { } identity)
            return selection with { Target = rebased };
        // Re-declaring reads, copies and hashes the whole declaring chain, and the projected facts retain the copy.
        var chain = (long)identity.Length + record.ReachIdentity.Length;
        _resources?.Metadata((chain + 7) / 8, chain);
        return identity.Rebased(record.ProcessedIdentity, record.ReachIdentity) is { } redeclared
            ? selection with { Target = rebased, Identity = redeclared }
            : Selection.Unavailable;
    }

    /// <summary>
    /// Whether the body of <paramref name="key"/> also occurs below a reach, so the context-free body index has no unique
    /// context for it: <paramref name="key"/> lies strictly below a reach's processing context, and that reach's
    /// corresponding context holds no view of its own (a projection's body is its counterpart's unless exposure copied its
    /// occurrence, and a copied occurrence's ancestors below the reach are copies too). <paramref name="memo"/> belongs to one
    /// index build: it records, per context, whether a processing context lies strictly above it, so the owners many
    /// contexts share are walked once and a context no processing context encloses (most of a program) costs nothing more.
    /// </summary>
    internal override bool OccursBelowAReach(StaticScopeKey key, Dictionary<StaticScopeKey, bool> memo)
    {
        if (_reaches.IsEmpty)
            return false;
        var unknown = new Stack<StaticScopeKey>();
        var enclosed = false;
        for (var at = key; at.Parent is { } parent; at = parent)
        {
            if (memo.TryGetValue(at, out enclosed))
                break;
            unknown.Push(at);
            if (_reachesOfProcessed.ContainsKey(parent))
            {
                enclosed = true;
                break;
            }
        }

        _resources?.Metadata(0, 1L + unknown.Count);
        while (unknown.TryPop(out var visited))
            memo[visited] = enclosed;
        if (!enclosed)
            return false;

        // Inside a served region: the precise check walks from the context to each processing context above it, and from
        // each of its reaches down the same path.
        long work = 0;
        try
        {
            lock (_projectionGate)
            {
                var path = new List<StaticScopeKey>();
                for (var at = key; at.Parent is { } parent; at = parent)
                {
                    path.Add(at);
                    work++;
                    if (!_reachesOfProcessed.TryGetValue(parent, out var reaches))
                        continue;
                    foreach (var reach in reaches)
                    {
                        StaticScopeKey? correspondent = reach;
                        for (var step = path.Count - 1; correspondent is not null && step >= 0; step--)
                        {
                            work++;
                            correspondent = _projectedChildren.TryGetValue((correspondent, path[step]), out var next)
                                && _projections[next].View is not null ? next : null;
                        }

                        if (correspondent is null)
                            return true;
                    }
                }
            }

            return false;
        }
        finally
        {
            _resources?.Metadata(0, work);
        }
    }

    internal override void EnsureUsable()
    {
        if (IsFailed) throw new InvalidOperationException("A failed structural publication cannot be read or changed.");
    }

    internal void Add(StaticScopeKey key, BodyFacts facts)
    {
        EnsureUsable();
        if (_local is null) throw new InvalidOperationException("A sealed structural publication is immutable.");
        HasProvisional |= facts.IsProvisional;
        if (!_local.ContainsKey(key) && !_bodies.ContainsKey(key))
            RetainedStorageUnits += 12 + 2L * facts.Members.Count + 4L * facts.Parameters.Count + 2L * facts.Providers.Length
                + 2L * ((facts.UnavailableOpenNames?.Count ?? 0) + (facts.AmbiguousOpenNames?.Count ?? 0))
                + (facts.IsProvisional ? 2 : 0);
        else RetainedStorageUnits += 2L * ((facts.UnavailableOpenNames?.Count ?? 0)
            + (facts.AmbiguousOpenNames?.Count ?? 0) - (Facts(key)?.UnavailableOpenNames?.Count ?? 0)
            - (Facts(key)?.AmbiguousOpenNames?.Count ?? 0));
        _local[key] = facts;
        if (key.Parent is { } parent)
        {
            if (facts.Body is { } body && !ReferenceEquals(key.Declaration, OpenProviderIdentity.DeclarationOf(body)))
            {
                var alternate = (parent, OpenProviderIdentity.DeclarationOf(body), key.BindingRegion);
                if (!_alternateChildDeclarations.Contains(alternate))
                {
                    _resources?.Metadata(2);
                    RetainedStorageUnits += 2;
                    _alternateChildDeclarations = _alternateChildDeclarations.Add(alternate);
                }
            }
            var child = (parent, key.Declaration, key.BindingRegion);
            if (!_children.TryGetValue(child, out var existing)) _children = _children.Add(child, key);
            else if (!ReferenceEquals(existing, key)) _children = _children.SetItem(child, null);
        }
    }

    internal void Retarget(StaticScopeKey key, Algorithm body)
    {
        if (Facts(key) is not { Body: { } previous } facts) return;
        if (!ReferenceEquals(OpenProviderIdentity.DeclarationOf(previous), OpenProviderIdentity.DeclarationOf(body)))
            throw new InvalidOperationException("Exposure must preserve a published declaration identity.");
        if (_local is null || !_local.ContainsKey(key))
        {
            // A module already classified by an earlier successful unit is immutable and reused by identity.
            if (!ReferenceEquals(previous, body)) throw new InvalidOperationException("A completed external view cannot be replaced.");
            return;
        }
        if (!ReferenceEquals(previous, body))
        {
            _resources?.Metadata(2);
            _local[key] = facts with { Body = body };
            _viewVersion++;
        }
    }

    internal void Seal(CancellationToken cancellationToken = default)
    {
        EnsureUsable();
        if (_local is null) return;
        try
        {
            var builder = _bodies.ToBuilder();
            foreach (var (key, facts) in _local)
            {
                cancellationToken.ThrowIfCancellationRequested();
                _resources?.Metadata(2, cancellationToken: cancellationToken);
                builder[key] = facts;
            }
            _bodies = builder.ToImmutable();
            lock (_projectionGate)
                (_sealedProjections, _sealedProjectedChildren, _sealedViewedChildren) = (_projections, _projectedChildren, _viewedChildren);
            _local = null;
            // Completed immutable facts outlive their producer. A later cancellation/fault of that
            // producer cannot invalidate this successful publication or any continuation sharing it.
            _resources = null;
        }
        catch { _failed = true; throw; }
    }

    /// <summary>
    /// Retargets the final exposed tree by published context, including memo hits and branch occurrences. Exposure copies
    /// declaration-preserving views, so each exposed node is walked beside the node it was copied from (its context's view
    /// before retargeting): a copied algorithm finds its context through that original — by member name, branch region or
    /// position — never through its own identity, which nothing records yet, so definitions sharing one declaration stay
    /// apart. B3-5★: an occurrence below a reach is a projection whose view the walk records only where exposure copied it —
    /// walked level by level (<see cref="ProjectionLevel"/>), so each comparison is with a final view and a shared subtree is
    /// never walked per path.
    /// </summary>
    internal void RetargetTree(StaticScopeKey entry, Algorithm tree, CancellationToken cancellationToken = default)
    {
        EnsureUsable();
        if (_local is null) return;
        using var storage = _resources?.Temporary();
        // Every published context's view before retargeting, and the published contexts by (parent, that view, region).
        var original = new Dictionary<StaticScopeKey, Algorithm>(ReferenceEqualityComparer.Instance);
        var byOriginal = new Dictionary<(StaticScopeKey Parent, object View, object? Region), StaticScopeKey>(ChildComparer.Instance);
        var seen = new Dictionary<StaticScopeKey, HashSet<object>>(ReferenceEqualityComparer.Instance);
        var levels = new List<Stack<(object Node, StaticScopeKey Context, object? Original)>> { new() };
        var level = 0;
        try
        {
            foreach (var (key, facts) in _local)
            {
                cancellationToken.ThrowIfCancellationRequested();
                if (facts.Body is not { } view) continue;
                storage?.Add(2, cancellationToken);
                original[key] = view;
                if (key.Parent is { } parent) byOriginal.TryAdd((parent, view, key.BindingRegion), key);
            }

            levels[0].Push((tree, entry, null));
            for (; level < levels.Count; level++)
            {
                while (levels[level].TryPop(out var item))
                {
                    cancellationToken.ThrowIfCancellationRequested();
                    _resources?.Metadata(0, cancellationToken: cancellationToken);
                    if (!seen.TryGetValue(item.Context, out var nodes))
                    {
                        storage?.Add(3, cancellationToken);
                        seen[item.Context] = nodes = new(ReferenceEqualityComparer.Instance);
                    }
                    if (nodes.Contains(item.Node)) continue;
                    storage?.Add(1, cancellationToken);
                    nodes.Add(item.Node);
                    RetargetNodeVisits++;
                    if (item.Node is Algorithm body)
                    {
                        if (_local.TryGetValue(item.Context, out var facts))
                        {
                            if (facts.Body is null) continue;
                            Retarget(item.Context, body);
                        }
                        else if (!RetargetProjection(item.Context, body)) continue;
                        var before = OriginalView(item.Context);
                        var originalProperties = before is not null && before.Properties.Count == body.Properties.Count ? before.Properties : null;
                        for (var index = 0; index < body.Properties.Count; index++)
                        {
                            var property = body.Properties[index];
                            if (property.Value is Algorithm.User { IsAssignmentDeconstructionSource: true } source)
                            {
                                // Detection and resolution admitted these rows in the written owner, and exposure rewrote them
                                // there: each is walked in the owner's context beside its original row.
                                var originalRows = originalProperties?[index] is
                                    { Value: Algorithm.User { IsAssignmentDeconstructionSource: true } copiedFrom } originalProperty
                                    && originalProperty.Name == property.Name && copiedFrom.Output.Count == source.Output.Count
                                        ? copiedFrom.Output : null;
                                for (var row = 0; row < source.Output.Count; row++)
                                    Push(source.Output[row], item.Context, originalRows?[row]);
                            }
                            else if ((MemberContext(item.Context, property) ?? Child(item.Context, property.Value)) is { } child)
                                Push(property.Value, child, null);
                        }
                        var originalOpens = before is not null && before.Opens.Count == body.Opens.Count ? before.Opens : null;
                        for (var index = 0; index < body.Opens.Count; index++)
                            Push(body.Opens[index], PreludeKey, originalOpens?[index]);
                        if (body is Algorithm.Conditional family)
                        {
                            var declaring = family.Opens.Count == 0 ? item.Context.Parent ?? PreludeKey : item.Context;
                            var originalBranches = before is Algorithm.Conditional { } copiedFrom && copiedFrom.Branches.Count == family.Branches.Count
                                ? copiedFrom.Branches : null;
                            for (var index = 0; index < family.Branches.Count; index++)
                            {
                                var branch = family.Branches[index];
                                var child = (originalBranches is { } branches && SameDeclaration(branches[index].Body, branch.Body)
                                    ? ContextOfOriginal(declaring, branches[index].Body, branches[index].Pattern) : null)
                                    ?? Child(declaring, branch.Body, branch.Pattern);
                                if (child is not null) Push(branch.Body, child, null);
                            }
                        }
                        else
                        {
                            var originalRows = before is not null && before.Output.Count == body.Output.Count ? before.Output : null;
                            for (var index = 0; index < body.Output.Count; index++)
                                Push(body.Output[index], item.Context, originalRows?[index]);
                        }
                    }
                    else if (item.Node is Expr.AlgorithmExpr block)
                    {
                        var child = (item.Original is Expr.AlgorithmExpr { Algorithm: var copiedFrom }
                            && SameDeclaration(copiedFrom, block.Algorithm)
                                ? ContextOfOriginal(item.Context, copiedFrom, null) : null) ?? Child(item.Context, block.Algorithm);
                        if (child is not null) Push(block.Algorithm, child, null);
                    }
                    else for (var i = 0; AstStructuralPreflight.TryGetChild(item.Node, i, out var child); i++)
                        Push(child, item.Context, item.Original is { } copiedFrom && copiedFrom.GetType() == item.Node.GetType()
                            && AstStructuralPreflight.TryGetChild(copiedFrom, i, out var originalChild) ? originalChild : null);
                }
            }
        }
        catch
        {
            _failed = true;
            throw;
        }

        // The view a context had before retargeting: a published context's own; a projection's, that of the published
        // context its counterparts lead to (the processing this occurrence was served from).
        Algorithm? OriginalView(StaticScopeKey key)
        {
            lock (_projectionGate)
                for (var at = key; ; at = _projections[at].Counterpart)
                {
                    if (original.TryGetValue(at, out var view)) return view;
                    if (_bodies.TryGetValue(at, out var inherited)) return inherited.Body;
                    if (!_projections.ContainsKey(at)) return null;
                }
        }

        // The context below parent whose view before retargeting was view: a published one, or — below a reach — the
        // projection of its counterpart's (nested reaches recurse once per level).
        StaticScopeKey? ContextOfOriginal(StaticScopeKey parent, Algorithm view, object? region)
        {
            if (byOriginal.TryGetValue((parent, view, region), out var published)) return published;
            StaticScopeKey counterpartParent;
            lock (_projectionGate)
            {
                if (ProjectionRootOf(parent) is null) return null;
                counterpartParent = CounterpartOf(parent);
            }
            if (ContextOfOriginal(counterpartParent, view, region) is not { } counterpart) return null;
            lock (_projectionGate)
                return ProjectedChild(parent, counterpart);
        }

        // A property's context is its owner's member of that name: unambiguous where definitions share one declaration. The
        // declaration check keeps any other member out.
        StaticScopeKey? MemberContext(StaticScopeKey owner, Property property)
            => property.Name is { } name && Member(owner, name) is { } member && Facts(member)?.Body is { } current
                && SameDeclaration(current, property.Value) ? member : null;

        // A positional original is trusted only when it is a view of the same declaration (exposure preserves both).
        static bool SameDeclaration(Algorithm first, Algorithm second)
            => ReferenceEquals(OpenProviderIdentity.DeclarationOf(first), OpenProviderIdentity.DeclarationOf(second));

        // A context's level never falls below its parent's; one that would (an open target, written at the root level) is
        // walked with its parent's.
        void Push(object node, StaticScopeKey context, object? originalNode)
        {
            int at;
            lock (_projectionGate)
                at = Math.Max(level, ProjectionLevel(context));
            while (levels.Count <= at) levels.Add(new());
            levels[at].Push((node, context, originalNode));
        }
    }

    internal override IEnumerable<StaticScopeKey> Scopes
        => _bodies.Keys.Concat(_local?.Keys ?? Enumerable.Empty<StaticScopeKey>())
            .Concat(_projections.Where(projection => projection.Value.View is not null).Select(projection => projection.Key)).Distinct();

    internal override StaticScopeKey? Child(StaticScopeKey parent, Algorithm body, Pattern? pattern = null)
    {
        EnsureUsable();
        var declaring = body.IsModuleRoot ? PreludeKey : parent;
        var region = body.IsModuleRoot ? null : pattern;
        var child = (declaring, OpenProviderIdentity.DeclarationOf(body), region);
        if (_children.TryGetValue(child, out var selected))
            return selected ?? ContextualBody(declaring, body, region);
        // The catalog has no declaration in this exact owner/pattern region. Retargeting
        // preserves declarations, so a missing inert helper cannot become a child after a
        // view change. Ambiguous definitions and alternate owner identities still use the
        // body-specific projection; neither their contexts nor their language identities merge.
        if (_alternateChildDeclarations.Contains(child))
            return ContextualBody(declaring, body, region);
        if (_reaches.IsEmpty || body.IsModuleRoot)
            return null;
        // B3-5★: below a reach, the projection of the counterpart's child for this body. The counterpart's own lookup may build
        // the body index, which reads projected facts under its gate, so it runs outside the projection gate.
        StaticScopeKey? owner, counterpartOwner = null;
        lock (_projectionGate)
        {
            if (_projectionSuspended || CanonicalOf(declaring) is not { } canonical)
                return null;
            owner = canonical;
            if (ReferenceEquals(owner, declaring))
            {
                if (ProjectionRootOf(owner) is null)
                    return null;
                // An occurrence exposure copied is found by its own view; any other one through its counterpart's.
                if (_viewedChildren.TryGetValue((owner, body, region), out var viewed))
                    return viewed;
                counterpartOwner = CounterpartOf(owner);
            }
        }

        // A key this table did not create asks for its context's child under that context's ONE key.
        if (counterpartOwner is null)
            return Child(owner, body, pattern);
        if (Child(counterpartOwner, body, pattern) is not { } counterpart)
            return null;
        lock (_projectionGate)
            return ProjectedChild(owner, counterpart);
    }

    private sealed class KeyPairComparer : IEqualityComparer<(StaticScopeKey Parent, StaticScopeKey Counterpart)>
    {
        internal static readonly KeyPairComparer Instance = new();
        public bool Equals((StaticScopeKey Parent, StaticScopeKey Counterpart) x, (StaticScopeKey Parent, StaticScopeKey Counterpart) y)
            => ReferenceEquals(x.Parent, y.Parent) && ReferenceEquals(x.Counterpart, y.Counterpart);
        public int GetHashCode((StaticScopeKey Parent, StaticScopeKey Counterpart) value)
            => HashCode.Combine(System.Runtime.CompilerServices.RuntimeHelpers.GetHashCode(value.Parent),
                System.Runtime.CompilerServices.RuntimeHelpers.GetHashCode(value.Counterpart));
    }

    private sealed class ChildComparer : IEqualityComparer<(StaticScopeKey Parent, object Declaration, object? Region)>
    {
        internal static readonly ChildComparer Instance = new();
        public bool Equals((StaticScopeKey Parent, object Declaration, object? Region) x, (StaticScopeKey Parent, object Declaration, object? Region) y)
            => ReferenceEquals(x.Parent, y.Parent) && ReferenceEquals(x.Declaration, y.Declaration) && ReferenceEquals(x.Region, y.Region);
        public int GetHashCode((StaticScopeKey Parent, object Declaration, object? Region) value)
            => HashCode.Combine(System.Runtime.CompilerServices.RuntimeHelpers.GetHashCode(value.Parent),
                System.Runtime.CompilerServices.RuntimeHelpers.GetHashCode(value.Declaration),
                value.Region is null ? 0 : System.Runtime.CompilerServices.RuntimeHelpers.GetHashCode(value.Region));
    }
}

/// <summary>Carried metadata; the entry key is present only on a compilation unit's root.</summary>
internal sealed record CompletedStructurePublication(CompletedStaticStructures Facts, StaticScopeKey? Entry = null, Algorithm? EntryView = null)
{
    internal bool MatchesEntry(Algorithm body)
        => Entry is { } entry && (Facts.Facts(entry)?.Body is { } published
            ? ReferenceEquals(published, body) : ReferenceEquals(EntryView, body));
}

/// <summary>A physical completed lookup context. It has no inference or reference-chasing capability.</summary>
internal sealed class CompletedStructureContext(StaticLookupFacts facts, StaticScopeKey key)
{
    internal long Identity => Key.RequirementIdentity;
    internal StaticLookupFacts Facts { get; } = facts;
    internal StaticScopeKey Key { get; } = key;

    internal static CompletedStructureContext? For(Algorithm? body, ElaboratedPropertyScope? parent, Pattern? pattern = null)
    {
        if (body is null) return null;
        if (parent?.CompletedContext is { Facts: AnalyzedStaticStructures } analyzed)
        {
            var declaringKey = pattern is not null && parent.OwnerAlgorithm is Algorithm.Conditional { Opens.Count: 0 }
                ? analyzed.Key.Parent ?? analyzed.Facts.PreludeKey : analyzed.Key;
            return analyzed.Facts.Child(declaringKey, body, pattern) is { } analyzedKey
                ? analyzed.Facts.Context(analyzedKey) : analyzed.Facts.ExactContext(body);
        }
        if (body.CompletedStructure is { Entry: { } entry } root)
            return root.MatchesEntry(body) ? root.Facts.Context(entry) : null;
        var inherited = parent?.CompletedContext;
        var graph = inherited?.Facts ?? body.CompletedStructure?.Facts;
        if (graph is null) return null;
        var declaring = inherited?.Key ?? graph.PreludeKey;
        if (pattern is not null && parent?.OwnerAlgorithm is Algorithm.Conditional { Opens.Count: 0 })
            declaring = declaring.Parent ?? graph.PreludeKey;
        var child = graph.Child(declaring, body, pattern);
        if (child is null && body.CompletedStructure is { } own && !ReferenceEquals(own.Facts, graph))
        {
            graph = own.Facts;
            child = graph.Child(declaring, body, pattern);
        }
        // A declaration-preserving host copy is a supplied view, not the published definition.
        // A real unavailable publication still has its admitted key; an invented key is not provenance.
        if (child is null || graph.Facts(child)?.Body is { } published && !ReferenceEquals(published, body)) return null;
        return new(graph, child);
    }

    internal ElaboratedPropertyScope Level(StaticScopeKey wanted, ElaboratedPropertyScope caller)
    {
        var cache = caller.MemberIndexes?.CompletedLevels;
        for (var physical = caller; physical is not null; physical = physical.Parent)
            if (ReferenceEquals(physical.CompletedContext?.Key, wanted))
            {
                cache?.TryAdd((Facts, wanted), physical);
                return physical;
            }
        if (cache is not null && cache.TryGetValue((Facts, wanted), out var known)) return known;
        var pending = new Stack<StaticScopeKey>();
        var at = wanted;
        while (cache is null || !cache.ContainsKey((Facts, at)))
        {
            pending.Push(at);
            if (at.Parent is not { } parent) break;
            at = parent;
        }
        ElaboratedPropertyScope? level = cache is not null && cache.TryGetValue((Facts, at), out known) ? known : null;
        while (pending.TryPop(out var next))
        {
            var body = Facts.Facts(next)?.Body;
            if (body is null) throw new InvalidOperationException("An unavailable completed owner cannot be materialized.");
            level = ElaboratedScopeLookup.CreateScope(body, level, observations: caller.Observations,
                memberIndexes: caller.MemberIndexes, completedContext: Facts.Context(next));
            cache?.TryAdd((Facts, next), level);
        }
        return level!;
    }

    internal StaticScopeKey? BodyKey(Algorithm body) => Facts.Child(Key, body);

    internal (Algorithm Structure, ElaboratedScopeLookup.StaticStructureScope Scope)? Receiver(Algorithm body, ElaboratedPropertyScope caller)
    {
        var selected = Facts.Child(Key, body);
        if (selected is not null)
        {
            if (Facts.Facts(selected)?.Body is { } published && !ReferenceEquals(published, body))
                throw new ArgumentException("The supplied view requires its own explicit structural admission.", nameof(body));
            return ReceiverAt(selected, caller);
        }
        var context = For(body, caller);
        return context?.ReceiverAt(context.Key, caller);
    }

    internal (Algorithm Structure, ElaboratedScopeLookup.StaticStructureScope Scope)? ReceiverAt(StaticScopeKey scope, ElaboratedPropertyScope caller)
    {
        RecordRead(caller);
        var selection = Facts.Facts(scope)?.Receiver;
        return selection is { Kind: StaticFactKind.Structure, Target: { } target }
            && Facts.Facts(target)?.Body is { } body && target.Parent is { } parent
                ? (body, new(Level(parent, caller), target, Facts)) : null;
    }

    internal ResolvedOpenTarget? Open(Algorithm body, ElaboratedPropertyScope declaring)
    {
        RecordRead(declaring);
        var selectedKey = Facts.Child(Key, body);
        if (selectedKey is not null && Facts.Facts(selectedKey)?.Body is { } published && !ReferenceEquals(published, body))
            throw new ArgumentException("The supplied view requires its own explicit structural admission.", nameof(body));
        var context = selectedKey is not null ? Facts.Context(selectedKey) : For(body, declaring);
        if (context?.Facts.Facts(context.Key)?.Open is not { Kind: StaticFactKind.Structure, Target: { } target, Identity: { } identity }
            || context.Facts.Facts(target)?.Body is not { } selected || target.Parent is not { } parent) return null;
        return new(selected, identity, context.Level(parent, declaring));
    }

    internal ResolvedOpenTarget? ProviderAt(int index, ElaboratedPropertyScope caller)
    {
        RecordRead(caller);
        return Facts.Facts(Key)?.Providers is { } providers && index < providers.Length ? Provider(providers[index], caller) : null;
    }

    private ResolvedOpenTarget? Provider(CompletedStaticStructures.Selection selection, ElaboratedPropertyScope caller)
        => selection is { Kind: StaticFactKind.Structure, Target: { Parent: { } parent } target, Identity: { } identity }
            && Facts.Facts(target)?.Body is { } body ? new(body, identity, Level(parent, caller)) : null;

    internal IReadOnlyList<ResolvedOpenProvider> Providers(ElaboratedPropertyScope caller)
    {
        RecordRead(caller);
        var result = new List<ResolvedOpenProvider>();
        var seen = new HashSet<OpenProviderIdentity>();
        if (Facts.Facts(Key)?.Providers is not { } providers) return result;
        for (var index = 0; index < providers.Length; index++)
            if (Provider(providers[index], caller) is { } selected && seen.Add(selected.Identity))
                result.Add(new(selected.Target, caller.Observations, caller.MemberIndexes, selected.Identity)
                { Level = selected.Level, Written = index < caller.Opens.Count ? caller.Opens[index] : null });
        return result;
    }

    internal bool OpenIsUnavailable(Algorithm body, ElaboratedPropertyScope declaring)
    {
        var context = For(body, declaring);
        return context?.Facts.Facts(context.Key)?.Open.Kind is null or StaticFactKind.Unknown;
    }

    private static void RecordRead(ElaboratedPropertyScope caller)
    {
        if (caller.MemberIndexes is { } cache) cache.RecordCompletedRead();
        else caller.Observations?.RecordCompletedStaticStructureRead();
    }
}
