namespace KatLang;

internal sealed partial class StaticStructureQueries
{
    private static readonly StaticFact EmptyMatches = new(StaticFactKind.OpenMatch, Data: new StaticOpenMatch(null, false));
    private static readonly StaticFact EmptyProviderTree = new(StaticFactKind.Providers, Data: new StaticProviderTree());

    private StaticFact ProviderRange(BodyContext context, StaticQueryKey key, StaticQueryReader<StaticQueryKey, StaticFact> reader)
    {
        if (key.Length == 0) return EmptyProviderTree;
        if (key.Length == 1)
        {
            var providers = reader.Read(Project(StaticQueryKind.OpenProviders, context.Key, StaticQueryProjection.OpenTarget,
                stratum: key.Stratum, node: context.Body.Opens[key.Offset]));
            return providers.IsUnknown ? providers : new(StaticFactKind.Providers,
                Data: new StaticProviderTree(Leaves: (StaticScopeKey[])providers.Data!));
        }
        var half = key.Length / 2;
        var left = reader.Read(StaticQueryKey.Project(key.Kind, key.Scope, key.Projection, stratum: key.Stratum, offset: key.Offset, length: half));
        var right = reader.Read(StaticQueryKey.Project(key.Kind, key.Scope, key.Projection, stratum: key.Stratum, offset: key.Offset + half, length: key.Length - half));
        return left.IsUnknown || right.IsUnknown ? StaticFact.Unknown : new(StaticFactKind.Providers,
            Data: new StaticProviderTree((StaticProviderTree)left.Data!, (StaticProviderTree)right.Data!));
    }

    /// <summary>
    /// A bounded-fan-in name projection over Q2's leaves. Known presence is useful even while another provider is
    /// unresolved: promotion is impossible whether that later provider makes the name ambiguous or leaves it single.
    /// Two distinct known providers decide ambiguity immediately. The full ordered Q2 list remains separate.
    /// The level's closed member index answers once it is known; until then the name waits on
    /// <see cref="StaticQueryProjection.DeferredOpenPresence"/>, never on a witness range of its own.
    /// </summary>
    private StaticFact OpenMatches(BodyContext context, StaticQueryKey key, StaticQueryReader<StaticQueryKey, StaticFact> reader)
    {
        if (key.Offset != 0 || key.Length != context.Body.Opens.Count)
            throw new ArgumentException("Open selection describes a whole level; partial ranges are presence witnesses.", nameof(key));
        var index = reader.Read(Project(StaticQueryKind.OpenProviders, context.Key, StaticQueryProjection.OpenMemberIndex, stratum: key.Stratum));
        if (!index.IsUnknown) return IndexedOpenMatch((OpenMemberIndex)index.Data!, key.Name!);
        return reader.Read(StaticQueryKey.Project(StaticQueryKind.Binding, context.Key, StaticQueryProjection.DeferredOpenPresence,
            key.Name, key.Stratum, offset: key.Offset, length: key.Length));
    }

    /// <summary>
    /// THE DEFERRED PRESENCE OF ONE NAME AT ONE LEVEL (November 2026). A decision observer
    /// (<see cref="IsDecisionObserver"/>): the engine computes it only once ordinary work is quiescent. By then the
    /// level's closed member index has settled unless one of its providers still waits — on a decision the level's own
    /// opened names make, or on an observer (a receiver-expansion verdict, a namespace certificate) — so it answers from
    /// the index exactly as <see cref="OpenMatches"/> does and the name builds no witness range. Only while the index is
    /// still unknown does it read the name's presence witnesses (<see cref="OpenPresenceWitnesses"/>), which can decide
    /// presence and ambiguity before the whole provider list settles. Read first, the index made every name of a
    /// K-target level build its own 2K − 1 witness ranges (and, for a repeated target, preserved-presence certificates
    /// over every earlier view, O(K²) per name) while the one index was still settling. This is scheduling only: the
    /// index's answer is the conclusive one the witnesses refine to, and the witnesses still answer while it is unknown.
    /// A level whose index waits on its own names still builds witnesses for each name whose deferred presence runs
    /// before the index settles.
    /// </summary>
    private StaticFact DeferredOpenPresence(BodyContext context, StaticQueryKey key, StaticQueryReader<StaticQueryKey, StaticFact> reader)
    {
        if (key.Offset != 0 || key.Length != context.Body.Opens.Count)
            throw new ArgumentException("Deferred open presence describes a whole level; partial ranges are presence witnesses.", nameof(key));
        var index = reader.Read(Project(StaticQueryKind.OpenProviders, context.Key, StaticQueryProjection.OpenMemberIndex, stratum: key.Stratum));
        if (!index.IsUnknown) return IndexedOpenMatch((OpenMemberIndex)index.Data!, key.Name!);
        return reader.Read(StaticQueryKey.Project(StaticQueryKind.Binding, context.Key, StaticQueryProjection.OpenPresenceWitnesses,
            key.Name, key.Stratum, offset: key.Offset, length: key.Length));
    }

    /// <summary>The closed index's answer for one name: absent, one provider, or ambiguous.</summary>
    private static StaticFact IndexedOpenMatch(OpenMemberIndex index, string name)
        => !index.Members.TryGetValue(name, out var provider) ? EmptyMatches
            : provider is null ? StaticFact.Ambiguous : new(StaticFactKind.OpenMatch, Data: new StaticOpenMatch(provider, false));

    /// <summary>
    /// Answers an absent or unique name from a final level index in this solve or its frozen continuation.
    /// A unique hit uses the same public declaration that Q1 selects. The caller scans for ambiguity to recover
    /// every provider in written order, for a null host name, or while the level has no closed index.
    /// </summary>
    internal bool TrySettledOpenMember(StaticScopeKey scope, StaticCycleCheck stratum, string? name,
        out (StaticScopeKey Provider, PropertyLookupHit Hit)? selected)
    {
        EnsureUsable();
        selected = null;
        if (name is null) return false;
        var key = Project(StaticQueryKind.OpenProviders, scope, StaticQueryProjection.OpenMemberIndex, stratum: stratum);
        if (!_engine.TryGetFinal(key, out var fact) && (_snapshot is null || !_snapshot.Facts.TryGetValue(key, out fact)))
            return false;
        if (fact.Data is not OpenMemberIndex index) return false;
        if (!index.Members.TryGetValue(name, out var provider)) return true;
        if (provider is null) return false;
        var context = ContextOf(provider);
        var property = context.Members.Public(name)
            ?? throw new InvalidOperationException("The settled open index selected a provider without the public declaration.");
        selected = (provider, new(context.Body, property));
        return true;
    }

    private sealed class OpenMemberIndex(Dictionary<string, StaticScopeKey?> members)
    {
        internal Dictionary<string, StaticScopeKey?> Members { get; } = members;
        internal bool Same(OpenMemberIndex other)
            => ReferenceEquals(this, other) || Members.Count == other.Members.Count && Members.All(pair => other.Members.TryGetValue(pair.Key, out var value)
                && ReferenceEquals(pair.Value, value));
    }

    private readonly Dictionary<StaticScopeKey[], OpenMemberIndex> _openMemberIndexes = new(ProviderSequenceComparer.Instance);

    private sealed class ProviderSequenceComparer : IEqualityComparer<StaticScopeKey[]>
    {
        internal static readonly ProviderSequenceComparer Instance = new();
        public bool Equals(StaticScopeKey[]? left, StaticScopeKey[]? right)
        {
            if (ReferenceEquals(left, right)) return true;
            if (left is null || right is null || left.Length != right.Length) return false;
            for (var index = 0; index < left.Length; index++)
                if (!ReferenceEquals(left[index], right[index])) return false;
            return true;
        }
        public int GetHashCode(StaticScopeKey[] providers)
        {
            var hash = new HashCode();
            foreach (var provider in providers) hash.Add(System.Runtime.CompilerServices.RuntimeHelpers.GetHashCode(provider));
            return hash.ToHashCode();
        }
    }

    private StaticFact ClosedOpenMemberIndex(BodyContext context, StaticCycleCheck stratum, StaticQueryReader<StaticQueryKey, StaticFact> reader)
    {
        var providers = reader.Read(StaticQueryKey.OpenProviders(context.Key, stratum));
        if (providers.IsUnknown) return providers;
        var scopes = (StaticScopeKey[])providers.Data!;
        Resources.Metadata(0, 1L + scopes.Length, _cancellationToken);
        if (_openMemberIndexes.TryGetValue(scopes, out var shared)) return new(StaticFactKind.Providers, Data: shared);
        Resources.Metadata(4, cancellationToken: _cancellationToken);
        Observations?.RecordStaticOpenIndexBuild();
        var members = new Dictionary<string, StaticScopeKey?>(StringComparer.Ordinal);
        var groups = new Dictionary<StaticMembers, int>(ReferenceEqualityComparer.Instance);
        foreach (var provider in scopes)
        {
            Resources.Metadata(0, cancellationToken: _cancellationToken);
            var names = ContextOf(provider).Members;
            var count = groups.GetValueOrDefault(names);
            if (count >= 2) continue; // A shared namespace's names are already ambiguous after two providers.
            if (count == 0) Resources.Metadata(2, cancellationToken: _cancellationToken);
            groups[names] = count + 1;
            foreach (var property in names.PublicProperties)
            {
                Observations?.RecordStaticOpenIndexMemberVisit();
                Resources.Metadata(0, cancellationToken: _cancellationToken);
                if (!members.TryGetValue(property.Name, out var previous))
                {
                    Resources.Metadata(2, cancellationToken: _cancellationToken);
                    members.Add(property.Name, provider);
                }
                else if (previous is not null) members[property.Name] = null;
            }
        }
        var result = new OpenMemberIndex(members);
        Resources.Metadata(2 + scopes.Length, cancellationToken: _cancellationToken);
        _openMemberIndexes.Add(scopes, result);
        return new(StaticFactKind.Providers, Data: result);
    }

    /// <summary>
    /// Searches for stable public-name witnesses; it never selects an invocation/member identity. A range of two or more
    /// targets first reads Q2's provider range for those positions in the same stratum, shared by every name.
    /// A settled range with at most one occurrence of the public name needs at most one certificate.
    /// Ranges with multiple occurrences combine their halves to keep certificate subscriptions bounded.
    /// </summary>
    private StaticFact OpenPresenceWitnesses(BodyContext context, StaticQueryKey key, StaticQueryReader<StaticQueryKey, StaticFact> reader)
    {
        if (key.Length == 0) return EmptyMatches;
        if (key.Length == 1)
        {
            var providers = reader.Read(Project(StaticQueryKind.OpenProviders, context.Key, StaticQueryProjection.OpenTarget,
                stratum: key.Stratum, node: context.Body.Opens[key.Offset]));
            if (providers.IsUnknown)
                return OpenMemberIsAbsent(context, key, reader) ? EmptyMatches : providers;
            var scopes = (StaticScopeKey[])providers.Data!;
            if (scopes.Length == 0) return EmptyMatches;
            if (scopes.Length != 1) throw new InvalidOperationException("One written open target must select at most one provider.");
            var members = reader.Read(StaticQueryKey.Members(scopes[0]));
            if (members.IsUnknown)
                return OpenMemberIsAbsent(context, key, reader) ? EmptyMatches : members;
            if (((StaticMembers)members.Data!).Public(key.Name!) is null) return EmptyMatches;
            return CertifiedPresence(key, scopes[0], key.Offset, reader);
        }
        if (SettledOpenTargetReuseForTesting)
        {
            var settled = reader.Read(StaticQueryKey.Project(StaticQueryKind.OpenProviders, context.Key, StaticQueryProjection.ProviderRange,
                stratum: key.Stratum, offset: key.Offset, length: key.Length));
            if (!settled.IsUnknown)
            {
                (StaticScopeKey? Provider, int Offset) match = default;
                if (!HasMultipleOpenOccurrences(key.Name!, (StaticProviderTree)settled.Data!, key.Offset, key.Length, ref match))
                {
                    Observations?.RecordStaticSettledWitnessRange();
                    return match.Provider is { } providerScope ? CertifiedPresence(key, providerScope, match.Offset, reader) : EmptyMatches;
                }
            }
        }
        var half = key.Length / 2;
        var left = reader.Read(StaticQueryKey.Project(key.Kind, key.Scope, key.Projection, key.Name, key.Stratum, offset: key.Offset, length: half));
        var right = reader.Read(StaticQueryKey.Project(key.Kind, key.Scope, key.Projection, key.Name, key.Stratum, offset: key.Offset + half, length: key.Length - half));
        if (left.Kind == StaticFactKind.Ambiguous || right.Kind == StaticFactKind.Ambiguous) return StaticFact.Ambiguous;
        var a = left.IsUnknown ? new StaticOpenMatch(null, true) : (StaticOpenMatch)left.Data!;
        var b = right.IsUnknown ? new StaticOpenMatch(null, true) : (StaticOpenMatch)right.Data!;
        if (a.Provider is not null && b.Provider is not null && !SameProvider(a.Provider, b.Provider)) return StaticFact.Ambiguous;
        var provider = a.Provider ?? b.Provider;
        var pending = a.Pending || b.Pending;
        return provider is null && pending ? StaticFact.Unknown
            : new(StaticFactKind.OpenMatch, Data: new StaticOpenMatch(provider, pending));
    }

    /// <summary>
    /// A target that offers the name is a presence witness once its certificate holds. The closed index selects the binding.
    /// </summary>
    private StaticFact CertifiedPresence(StaticQueryKey key, StaticScopeKey provider, int offset,
        StaticQueryReader<StaticQueryKey, StaticFact> reader)
    {
        var preserved = reader.Read(StaticQueryKey.Project(StaticQueryKind.OpenProviders, key.Scope,
            StaticQueryProjection.PreservedOpenPresence, key.Name, key.Stratum, offset: offset));
        return preserved.Kind != StaticFactKind.Yes ? StaticFact.Unknown
            : new(StaticFactKind.OpenMatch, Data: new StaticOpenMatch(Keys.ProviderScope(provider, Resources, _cancellationToken), true));
    }

    /// <summary>
    /// Test-only: false restores the generic paths that the reuse of settled open targets must agree with: every witness
    /// range combines its subranges, and a preserved-presence certificate solves
    /// every earlier target. Set it before the first query.
    /// </summary>
    internal bool SettledOpenTargetReuseForTesting { get; set; } = true;

    /// <summary>
    /// Test-only: false schedules a deferred open presence with the other decision observers again
    /// (<see cref="IsLateDecisionObserver"/>). Set it before the first query.
    /// </summary>
    internal bool LateDeferredPresenceForTesting { get; set; } = true;

    /// <summary>Test-only: runs before each range node a settled witness range visits, so a test can cancel inside that walk.</summary>
    internal Action? SettledRangeVisitForTesting { get; set; }

    // Scan immutable Q4 namespaces in written order. Stop at a second occurrence, even of the same provider:
    // each written position has its own preserved-presence certificate. Tree depth is bounded by ceil(log2(length)).
    private bool HasMultipleOpenOccurrences(string name, StaticProviderTree part, int offset, int length,
        ref (StaticScopeKey? Provider, int Offset) match)
    {
        SettledRangeVisitForTesting?.Invoke();
        Resources.Metadata(0, cancellationToken: _cancellationToken);
        Observations?.RecordStaticSettledWitnessNodeVisit();
        if (length > 1)
        {
            if (part.Left is not { } left || part.Right is not { } right)
                throw new InvalidOperationException("A settled provider range must split as its witness range does.");
            var half = length / 2;
            return HasMultipleOpenOccurrences(name, left, offset, half, ref match)
                || HasMultipleOpenOccurrences(name, right, offset + half, length - half, ref match);
        }
        if (part.Leaves is not { } scopes)
            throw new InvalidOperationException("A settled provider range must end in one target's providers.");
        if (scopes.Length == 0) return false;
        if (scopes.Length != 1) throw new InvalidOperationException("One written open target must select at most one provider.");
        if (ContextOf(scopes[0]).Members.Public(name) is null) return false;
        if (match.Provider is not null) return true;
        match = (scopes[0], offset);
        return false;
    }

    private bool SameProvider(StaticScopeKey? left, StaticScopeKey? right)
        => left is null || right is null ? ReferenceEquals(left, right)
            : ReferenceEquals(Keys.ProviderScope(left, Resources, _cancellationToken), Keys.ProviderScope(right, Resources, _cancellationToken));

    private static bool OpenMemberIsAbsent(BodyContext context, StaticQueryKey key, StaticQueryReader<StaticQueryKey, StaticFact> reader)
    {
        var empty = reader.Read(Project(StaticQueryKind.OpenProviders, context.Key, StaticQueryProjection.EmptyOpenNamespace,
            stratum: key.Stratum, node: context.Body.Opens[key.Offset]));
        // Await the shared closed cover before starting per-name certificates. An empty provider then needs one
        // proof for all names, rather than one complete traversal per name. Coverage does not assert occupancy.
        return empty.Kind == StaticFactKind.Yes || empty.Kind == StaticFactKind.NamespaceCoverage
            && reader.Read(Project(StaticQueryKind.OpenProviders, context.Key, StaticQueryProjection.OpenMemberAbsence,
                key.Name, key.Stratum, context.Body.Opens[key.Offset])).Kind == StaticFactKind.Yes;
    }
}
