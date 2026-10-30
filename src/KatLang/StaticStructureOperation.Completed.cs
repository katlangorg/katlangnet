using System.Collections.Frozen;
using System.Collections.Immutable;

namespace KatLang;

internal sealed partial class StaticStructureOperation
{
    private CompletedStaticStructures? _completed;
    private CompletedStaticStructures? _completedBase;

    /// <summary>Projects completed local views, including erroneous resolved trees, without freezing a successful unit.</summary>
    internal void CompleteLookups(Algorithm root)
    {
        Queries.EnsureUsable();
        if (_completed is not null) return;
        var graph = new CompletedStaticStructures(Queries.Keys.Root, _completedBase, Queries.Resources);
        var pending = new Queue<StaticScopeKey>();
        var seen = new HashSet<StaticScopeKey>(ReferenceEqualityComparer.Instance);
        var prelude = new HashSet<StaticScopeKey>(ReferenceEqualityComparer.Instance) { Queries.Keys.Root };
        void Include(StaticScopeKey key)
        {
            var chain = new Stack<StaticScopeKey>();
            for (var at = key; graph.Facts(at) is null && seen.Add(at); at = at.Parent!)
            {
                chain.Push(at);
                if (at.Parent is null) break;
            }
            while (chain.TryPop(out var next)) pending.Enqueue(next);
        }
        Include(Queries.Keys.Root);
        // Include registers query contexts, not publications; do not copy the whole key set.
        foreach (var key in _publications.Keys) { Queries.EnsureUsable(); Queries.Resources.Metadata(0); Include(key); }
        var built = new List<StaticScopeKey>();
        while (pending.TryDequeue(out var key))
        {
            Queries.EnsureUsable();
            var source = SourceOf(key);
            var view = Published(key, StaticPublicationStage.Resolved) ?? (prelude.Contains(key) || source is Algorithm.Builtin ? source : null);
            var detected = Published(key, StaticPublicationStage.Detected);
            var provisional = view is null && detected is Algorithm.User or Algorithm.Conditional
                && (source.DeferredRegion is not null || key.Parent is { } parent && graph.Facts(parent)?.IsProvisional == true);
            var lexicalView = view ?? (provisional ? detected : null);
            // Prelude/host registry objects can outlive a compilation. Never give them a back-reference to its tree.
            if (view is not null && !prelude.Contains(key) && view is not Algorithm.Builtin)
                CompletedStaticStructures.Attach(view, new(graph));
            var ready = view is not null && view is not Algorithm.Alias { ResolvedTargetCell.IsPending: true }
                && view is not Algorithm.Alias { ResolvedStructureCell.IsPending: true };
            Queries.Resources.Metadata(8);
            var members = new Dictionary<string, StaticScopeKey>(StringComparer.Ordinal);
            var writtenParameters = Queries.WrittenParametersOf(key);
            Queries.Resources.Metadata(4L * writtenParameters.Count, 1L + writtenParameters.Count);
            var parameters = new HashSet<string>(writtenParameters, StringComparer.Ordinal);
            if (lexicalView is Algorithm.User user)
            {
                Queries.Resources.Metadata(4L * ParameterPattern.CountCaptures(user.NameResolutionParameterPatterns));
                foreach (var parameter in ParameterPattern.FlattenCaptures(user.NameResolutionParameterPatterns))
                { Queries.EnsureUsable(); Queries.Resources.Metadata(0); parameters.Add(parameter.Name); }
            }
            var receiver = CompletedStaticStructures.Selection.Unavailable;
            var open = CompletedStaticStructures.Selection.Unavailable;
            CompletedStaticStructures.Selection? requirementReceiver = null, requirementOpen = null;
            var providers = new List<CompletedStaticStructures.Selection>();
            if (ready || provisional)
            {
                var q4 = (StaticMembers)Read(StaticQueryKey.Members(key)).Data!;
                foreach (var property in lexicalView!.Properties)
                {
                    Queries.EnsureUsable();
                    Queries.Resources.Metadata(2);
                    var written = q4.Declared(property.Name!);
                    if (written is null) continue;
                    var child = ContextOf(key, property.Value);
                    if (property.Name is not null) members.TryAdd(property.Name, child);
                    if (prelude.Contains(key)) prelude.Add(child);
                    Include(child);
                }
            }
            if (ready)
            {
                receiver = open = Select(new(StaticFactKind.Structure, key));
                if (view is Algorithm.Alias { IsReference: true })
                {
                    receiver = Select(Read(StaticQueryKey.TargetWalk(key, StaticCycleCheck.Formation)));
                    open = Select(Read(StaticQueryKey.Project(StaticQueryKind.TargetWalk, key,
                        StaticQueryProjection.OpenStructure, stratum: StaticCycleCheck.Formation)));
                }
            }
            if (provisional)
            {
                // The source equations can know a namespace without a successful body publication.
                // Keep these answers exclusively for Q8's provisional capture projection.
                Queries.Resources.Metadata(2);
                requirementReceiver = Select(Read(StaticQueryKey.TargetWalk(key, StaticCycleCheck.Formation)));
                requirementOpen = Select(Read(StaticQueryKey.Project(StaticQueryKind.TargetWalk, key,
                    StaticQueryProjection.OpenStructure, stratum: StaticCycleCheck.Formation)));
            }
            if (ready || provisional)
                foreach (var written in SourceOf(key).Opens)
                {
                    Queries.EnsureUsable();
                    Queries.Resources.Metadata(2);
                    var offered = Read(StaticQueryKey.Project(StaticQueryKind.OpenProviders, key,
                        StaticQueryProjection.OpenTarget, stratum: StaticCycleCheck.Formation, node: written));
                    providers.Add(offered.Data is StaticScopeKey[] { Length: 1 } keys
                        ? Select(new(StaticFactKind.Structure, keys[0]))
                        : offered.IsUnknown ? CompletedStaticStructures.Selection.Unavailable : new(StaticFactKind.Missing));
                }
            graph.Add(key, new(ready ? view : null, receiver, open, members.ToFrozenDictionary(StringComparer.Ordinal),
                parameters.ToFrozenSet(StringComparer.Ordinal), providers.ToImmutableArray(), IsProvisional: provisional,
                RequirementReceiver: requirementReceiver, RequirementOpen: requirementOpen));
            built.Add(key);
        }
        // An exact terminal may have no completed view (for example a Q8 depth-limited body). Preserve unavailable
        // knowledge, rather than exporting its written body or treating it as a successful publication.
        foreach (var key in built)
        {
            Queries.EnsureUsable();
            Queries.Resources.Metadata(2);
            var facts = graph.Facts(key)!;
            // A provisional deferred region has no resolved view. Preserve Q2's conclusive name
            // presence separately; it is neither a provider publication nor a member identity.
            ImmutableHashSet<string>? unavailableNames = null;
            ImmutableHashSet<string>? ambiguousNames = null;
            if (facts.Body is null && SourceOf(key).Opens.Count > 0)
            {
                var names = new HashSet<string>(StringComparer.Ordinal);
                var providersSeen = new HashSet<StaticScopeKey>(ReferenceEqualityComparer.Instance);
                foreach (var expression in SourceOf(key).Opens)
                {
                    var offered = Read(StaticQueryKey.Project(StaticQueryKind.OpenProviders, key,
                        StaticQueryProjection.OpenTarget, stratum: StaticCycleCheck.Formation, node: expression));
                    if (offered.Data is not StaticScopeKey[] targets) continue;
                    foreach (var target in targets)
                        if (providersSeen.Add(target))
                            foreach (var property in ((StaticMembers)Read(StaticQueryKey.Members(target)).Data!).PublicProperties)
                            {
                                Queries.Resources.Metadata(0);
                                if (names.Add(property.Name)) Queries.Resources.Metadata(2);
                            }
                }
                foreach (var name in names)
                {
                    var presence = Read(StaticQueryKey.Project(StaticQueryKind.Binding, key,
                        StaticQueryProjection.OpenMatches, name, StaticCycleCheck.Formation,
                        offset: 0, length: SourceOf(key).Opens.Count));
                    if (presence is { Kind: StaticFactKind.OpenMatch, Data: StaticOpenMatch { Provider: not null } })
                        unavailableNames = (unavailableNames ?? ImmutableHashSet.Create<string>(StringComparer.Ordinal)).Add(name);
                    else if (presence.Kind == StaticFactKind.Ambiguous)
                        ambiguousNames = (ambiguousNames ?? ImmutableHashSet.Create<string>(StringComparer.Ordinal)).Add(name);
                }
            }
            graph.Add(key, facts with { Receiver = Eligible(facts.Receiver), Open = Eligible(facts.Open),
                Providers = facts.Providers.Select(Eligible).ToImmutableArray(), UnavailableOpenNames = unavailableNames,
                AmbiguousOpenNames = ambiguousNames });
        }
        // Registry-owned builtin objects never retain a per-program graph; their exposure is already final.
        if (root is Algorithm.Builtin)
        {
            graph.Seal();
            _completed = graph;
            return;
        }
        CompletedStaticStructures.Attach(root, new(graph, Root));
        if (graph.Facts(Root)?.Body is not null) graph.Retarget(Root, root);
        _completed = graph;

        CompletedStaticStructures.Selection Select(StaticFact fact)
        {
            if (fact.Scope is { } selected) Include(selected);
            return new(fact.Kind, fact.Scope, fact.Scope is { } selectedScope
                ? OpenProviderIdentity.DeclaredIn(SourceOf(selectedScope), OwnersOf(selectedScope.Parent ?? Queries.Keys.Root)) : null);
        }
        CompletedStaticStructures.Selection Eligible(CompletedStaticStructures.Selection selection)
            => selection is { Kind: StaticFactKind.Structure, Target: { } target }
                && graph.Facts(target) is not { Body: not null } and not { IsProvisional: true }
                ? CompletedStaticStructures.Selection.Unavailable : selection;
    }
}
