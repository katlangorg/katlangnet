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
    /// </summary>
    private StaticFact OpenMatches(BodyContext context, StaticQueryKey key, StaticQueryReader<StaticQueryKey, StaticFact> reader)
    {
        if (key.Offset != 0 || key.Length != context.Body.Opens.Count)
            throw new ArgumentException("Open selection describes a whole level; partial ranges are presence witnesses.", nameof(key));
        var index = reader.Read(Project(StaticQueryKind.OpenProviders, context.Key, StaticQueryProjection.OpenMemberIndex, stratum: key.Stratum));
        if (!index.IsUnknown)
        {
            var selected = ((OpenMemberIndex)index.Data!).Members;
            return !selected.TryGetValue(key.Name!, out var provider) ? EmptyMatches
                : provider is null ? StaticFact.Ambiguous : new(StaticFactKind.OpenMatch, Data: new StaticOpenMatch(provider, false));
        }
        return reader.Read(StaticQueryKey.Project(StaticQueryKind.Binding, context.Key, StaticQueryProjection.OpenPresenceWitnesses,
            key.Name, key.Stratum, offset: key.Offset, length: key.Length));
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

    /// <summary>Searches for stable public-name witnesses; it never selects an invocation/member identity.</summary>
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
            var preserved = reader.Read(StaticQueryKey.Project(StaticQueryKind.OpenProviders, context.Key,
                StaticQueryProjection.PreservedOpenPresence, key.Name, key.Stratum, offset: key.Offset));
            return preserved.Kind != StaticFactKind.Yes ? StaticFact.Unknown
                : new(StaticFactKind.OpenMatch, Data: new StaticOpenMatch(Keys.ProviderScope(scopes[0], Resources, _cancellationToken), true));
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
