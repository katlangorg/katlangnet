using System.Collections.Immutable;

namespace KatLang;

internal sealed partial class StaticStructureQueries
{
    /// <summary>
    /// A deferred continuation's immutable source and final external facts. It deliberately retains neither the
    /// eager engine's dependency graph nor its cancellation token. Unknown classifications are not imported.
    /// </summary>
    internal sealed class Snapshot
    {
        internal required StaticKeyTable Keys { get; init; }
        internal required StaticScopeKey Root { get; init; }
        internal required ImmutableDictionary<StaticScopeKey, BodyContext> Contexts { get; init; }
        internal required ImmutableDictionary<Algorithm, BodySyntax> Syntax { get; init; }
        internal required ImmutableDictionary<StaticQueryKey, StaticFact> Facts { get; init; }
        internal long RetainedStorageUnits { get; init; }
    }

    internal Snapshot Freeze(CancellationToken cancellationToken = default)
    {
        EnsureUsable();
        cancellationToken.ThrowIfCancellationRequested();
        // Cancelling an independent export discards the copy, not the successful source solve.
        // Work/storage bounds still belong to this operation; its own token remains sticky.
        long retained = _snapshot?.RetainedStorageUnits ?? 0;
        var facts = (_snapshot?.Facts ?? ImmutableDictionary<StaticQueryKey, StaticFact>.Empty).ToBuilder();
        foreach (var (key, value) in _engine.EnumerateFinalValues(cancellationToken))
        {
            cancellationToken.ThrowIfCancellationRequested();
            // A known-presence or pending-provider fact is useful inside a solve, but is not a completed selection.
            if (!value.HasUnknownSelection && value.Data is not StaticOpenMatch { Pending: true })
            {
                if (!facts.ContainsKey(key))
                {
                    var units = 8L + (value.Data is Array array ? array.Length : 0);
                    Resources.Metadata(2, cancellationToken: _cancellationToken);
                    retained += units;
                }
                facts[key] = value;
            }
        }
        var contexts = (_snapshot?.Contexts ?? ImmutableDictionary.Create<StaticScopeKey, BodyContext>(ReferenceEqualityComparer.Instance)).ToBuilder();
        foreach (var (key, context) in _contexts)
        {
            cancellationToken.ThrowIfCancellationRequested();
            if (!contexts.ContainsKey(key))
            {
                Resources.Metadata(2, cancellationToken: _cancellationToken);
                contexts.Add(key, context.Retokenize(null, default));
                retained += 8 + 2L * context.WrittenParameters.Count;
            }
        }
        var syntax = (_snapshot?.Syntax ?? ImmutableDictionary.Create<Algorithm, BodySyntax>(ReferenceEqualityComparer.Instance)).ToBuilder();
        foreach (var (body, source) in _syntaxSources)
        {
            cancellationToken.ThrowIfCancellationRequested();
            if (!syntax.ContainsKey(body))
            {
                // A frozen syntax index is complete and thereafter read-only. A failed deferred attempt
                // must not add unaccounted lazy graph storage to a previous successful snapshot.
                _ = source.Graph(Resources, _cancellationToken);
                Resources.Metadata(2, cancellationToken: _cancellationToken);
                syntax.Add(body, source);
                retained += 2 + source.RetainedStorageUnits;
            }
        }
        retained += Keys.DefinitionIdentityStorageUnits - (_snapshot?.Keys.DefinitionIdentityStorageUnits ?? 0);
        return new()
        {
            Keys = Keys.Fork(cancellationToken),
            Root = Root,
            Contexts = contexts.ToImmutable(),
            Syntax = syntax.ToImmutable(),
            Facts = facts.ToImmutable(),
            RetainedStorageUnits = retained,
        };
    }

    internal StaticStructureQueries(Snapshot snapshot, StaticQueryLimits limits, CancellationToken cancellationToken = default)
        : this(snapshot, limits, StaticAstPhase.RawSource, cancellationToken) { }

    internal StaticStructureQueries(Snapshot snapshot, StaticQueryLimits limits, StaticAstPhase phase, CancellationToken cancellationToken = default)
    {
        _phase = phase;
        cancellationToken.ThrowIfCancellationRequested();
        _cancellationToken = cancellationToken;
        Keys = snapshot.Keys.Fork(cancellationToken);
        Root = snapshot.Root;
        _snapshot = snapshot;
        _engine = new(this, limits: limits, cancellationToken: cancellationToken);
        Resources.Metadata(snapshot.RetainedStorageUnits, work: 0, cancellationToken: cancellationToken);
    }

    /// <summary>
    /// Admits a materialized closed branch under a NEW unit region. Its declaration identity is preserved while its
    /// definition can differ from the eager placeholder. Descendant contexts inherit this fresh parent key.
    /// </summary>
    internal StaticScopeKey MaterializedBranchIn(StaticScopeKey declaring, Algorithm body, Pattern pattern)
    {
        _cancellationToken.ThrowIfCancellationRequested();
        if (body.IsModuleRoot) throw new ArgumentException("A deferred branch is a closed body, not a module root.", nameof(body));
        var key = Keys.Inside(declaring, OpenProviderIdentity.DeclarationOf(body), new object());
        if (!_branchNames.TryGetValue(pattern, out var names))
        {
            var set = new HashSet<string>(StringComparer.Ordinal);
            foreach (var name in pattern.BoundNames()) { Resources.Metadata(1, cancellationToken: _cancellationToken); set.Add(name); }
            _branchNames.Add(pattern, names = set);
        }
        Resources.Metadata(8, cancellationToken: _cancellationToken);
        _contexts.Add(key, new(key, SyntaxOf(body), declaring, names, Resources, _cancellationToken)
        {
            HasOpens = body.Opens.Count != 0 || ContextOf(declaring).HasOpens,
        });
        return key;
    }
}
