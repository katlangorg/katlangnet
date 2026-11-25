namespace KatLang;

internal sealed partial class StaticStructureOperation
{
    private readonly Dictionary<StaticScopeKey, ElaboratedPropertyScope> _lookupLevels = new(ReferenceEqualityComparer.Instance);
    private readonly Dictionary<StaticScopeKey, Dictionary<Expr, Expr>> _writtenNodes = new(ReferenceEqualityComparer.Instance);

    internal void RegisterExpression(StaticScopeKey scope, Expr written, Expr view)
    {
        if (!_writtenNodes.TryGetValue(scope, out var nodes)) { Queries.Resources.Metadata(2); _writtenNodes.Add(scope, nodes = new(ReferenceEqualityComparer.Instance)); }
        if (!nodes.ContainsKey(view)) Queries.Resources.Metadata(2);
        nodes[view] = nodes.GetValueOrDefault(written, written);
    }

    internal Expr WrittenExpression(StaticScopeKey scope, Expr view)
    {
        // A served context reads the written nodes of the context that processed its one detected view.
        scope = DetectedProcessingContext(scope);
        if (!_writtenNodes.TryGetValue(scope, out var nodes)) { Queries.Resources.Metadata(2); _writtenNodes.Add(scope, nodes = new(ReferenceEqualityComparer.Instance)); }
        if (nodes.TryGetValue(view, out var written)) return written;
        // Q8 can rebuild a path after processing its inline block. Canonicalize published block views at this
        // consumer boundary; query callbacks still receive immutable raw definitions, never processed replacements.
        var path = new Stack<Expr.DotCall>();
        var head = view;
        while (head is Expr.DotCall edge && !nodes.ContainsKey(head)) { Queries.Resources.Metadata(1); path.Push(edge); head = edge.Target; }
        head = nodes.GetValueOrDefault(head, head);
        if (head is Expr.AlgorithmExpr block && RawBody(block.Algorithm) is { } source && !ReferenceEquals(source, block.Algorithm))
            head = block with { Algorithm = source };
        while (path.TryPop(out var edge)) head = ReferenceEquals(edge.Target, head) ? edge : edge with { Target = head };
        Queries.Resources.Metadata(2);
        nodes[view] = head;
        return head;
    }

    internal void RegisterLevel(ElaboratedPropertyScope level)
    {
        if (level.StaticContext is not { } context || !ReferenceEquals(context.Operation, this))
            throw new InvalidOperationException("The physical level belongs to another structural operation.");
        if (!_lookupLevels.TryGetValue(context.Key, out var registered)) Queries.Resources.Metadata(8);
        else if (!ReferenceEquals(registered, level)) _lookupLevelReplacements++;
        _lookupLevels[context.Key] = level;
    }

    internal ElaboratedPropertyScope LookupLevel(StaticScopeKey key)
    {
        var pending = new Stack<StaticScopeKey>();
        var current = key;
        while (!_lookupLevels.ContainsKey(current))
        {
            Queries.Resources.Metadata(0);
            pending.Push(current);
            if (current.Parent is not { } parent) break;
            current = parent;
        }
        while (pending.TryPop(out var next))
        {
            var parent = next.Parent is { } outer ? _lookupLevels[outer] : null;
            Queries.Resources.Metadata(8);
            var level = ElaboratedScopeLookup.CreateScope(SourceOf(next), parent,
                memberIndexes: parent?.MemberIndexes ?? new OpenMemberIndexCache(),
                staticContext: Context(next));
            _lookupLevels.Add(next, level);
        }
        return _lookupLevels[key];
    }

    internal StaticFact Binding(StaticScopeKey scope, string name, StaticQueryProjection projection = StaticQueryProjection.Default,
        StaticCycleCheck stratum = StaticCycleCheck.Formation)
        => Read(StaticQueryKey.Project(StaticQueryKind.Binding, scope, projection, name, stratum));

    internal OwnedDeclaration Owned(StaticScopeKey scope, string name, bool excludeNeverCalledOwner = false)
    {
        var binding = Binding(scope, name, excludeNeverCalledOwner ? StaticQueryProjection.OpenHeadBinding : StaticQueryProjection.OwnedBinding);
        return binding.Kind switch
        {
            StaticFactKind.Parameter => OwnedDeclaration.Parameter(LookupLevel(binding.Scope!)),
            StaticFactKind.Declaration => OwnedDeclaration.Property(LookupLevel(binding.Scope!), new(SourceOf(binding.Scope!), binding.Property!)),
            _ => OwnedDeclaration.None,
        };
    }

    internal (Algorithm Structure, ElaboratedScopeLookup.StaticStructureScope Scope)? StructureAt(StaticScopeKey declaring, Algorithm body,
        StaticCycleCheck stratum = StaticCycleCheck.Formation)
    {
        var context = ContextOf(declaring, body);
        var selected = Read(StaticQueryKey.TargetWalk(context, stratum));
        return selected.Kind == StaticFactKind.Structure && selected.Scope is { Parent: { } parent } target
            ? (SourceOf(target), new(LookupLevel(parent), target)) : null;
    }

    internal StaticStructuralMemberProvider Receiver(StaticScopeKey scope, Expr expression)
    {
        var selected = Read(StaticQueryKey.Project(StaticQueryKind.TargetWalk, scope, StaticQueryProjection.Receiver, node: expression));
        return selected.Kind switch
        {
            StaticFactKind.Structure when selected.Scope is { Parent: { } parent } target
                => new(StaticStructuralMemberProviderKind.KnownAlgorithm, SourceOf(target), new ElaboratedScopeLookup.StaticStructureScope(LookupLevel(parent), target)),
            StaticFactKind.Runtime => new(StaticStructuralMemberProviderKind.RuntimeParameter),
            StaticFactKind.Absent => new(StaticStructuralMemberProviderKind.DefinitelyAbsent),
            StaticFactKind.Failure => new(StaticStructuralMemberProviderKind.KnownFailure),
            _ => new(StaticStructuralMemberProviderKind.LexicalReference),
        };
    }

    internal LexicalFallbackSelection Miss(StaticScopeKey scope, Expr.DotCall edge)
        => Read(StaticQueryKey.MissSelection(scope, edge)).Kind switch
        {
            StaticFactKind.Never => LexicalFallbackSelection.Never,
            StaticFactKind.Always => LexicalFallbackSelection.Always,
            _ => LexicalFallbackSelection.Conditional,
        };

    // The providers of each level the lookup adapters asked about, per stratum (RetainedLevelProviders), and how many
    // times a registered level replaced another one for the same context (RegisterLevel): a retained list is current
    // while every provider's declaring level is still the one its context registers.
    private readonly Dictionary<(StaticScopeKey Scope, StaticCycleCheck Stratum), RetainedLevelProviders> _levelProviders = new();
    private long _lookupLevelReplacements;

    /// <summary>
    /// THE PROVIDERS OF ONE LEVEL as the lookup adapters read them (<see cref="ElaboratedPropertyScope.GetResolvedOpenProviders"/>):
    /// every written target's Q2 provider in written order, one per language identity (the first target that reaches it is
    /// its <see cref="ResolvedOpenProvider.Written"/> provenance, a duplicate spelling adds nothing), each declared at its
    /// context's registered level. Built once per level and stratum from final Q2 facts and retained by the operation
    /// (November 2026): every name a body writes asks its open levels (the Q-29 ambiguity check, a Grace marker's reason,
    /// a structural member provider), and a rebuild per question allocated a new provider, identity and declaring chain
    /// for every provider of every level the question reached, and charged their four ledger slots again, a K-provider
    /// level costing O(K) for every name written below it. The list is charged once, where it is built. A retained list
    /// is served while each provider's declaring level is still the one registered for its context; a detector level that
    /// replaced it (<see cref="RegisterLevel"/>) makes the next read rebuild the list, as every read used to. A read of a
    /// failed or cancelled operation throws as before (<see cref="SourceOf"/>), and a build that throws retains nothing.
    /// </summary>
    internal IReadOnlyList<ResolvedOpenProvider> Providers(StaticScopeKey scope, StaticCycleCheck stratum)
        => RetainedProviders(scope, stratum)?.Providers ?? [];

    private RetainedLevelProviders? RetainedProviders(StaticScopeKey scope, StaticCycleCheck stratum)
    {
        var source = SourceOf(scope);
        if (source.Opens.Count == 0) return null;
        if (_levelProviders.TryGetValue((scope, stratum), out var retained) && retained.IsCurrent(this)) return retained;
        var providers = new List<ResolvedOpenProvider>();
        var keys = new List<StaticScopeKey>();
        var seen = new HashSet<StaticScopeKey>(ReferenceEqualityComparer.Instance);
        foreach (var expression in source.Opens)
        {
            var fact = Read(StaticQueryKey.Project(StaticQueryKind.OpenProviders, scope, StaticQueryProjection.OpenTarget,
                stratum: stratum, node: expression));
            if (fact.Data is not StaticScopeKey[] targets) continue;
            foreach (var key in targets)
            {
                var identity = Queries.Keys.ProviderScope(key, Queries.Resources, Queries.OperationToken);
                if (seen.Contains(identity)) continue;
                Queries.Resources.Metadata(4);
                seen.Add(identity);
                var body = SourceOf(key);
                var declaring = LookupLevel(key.Parent ?? Queries.Keys.Root);
                providers.Add(new(body, OpenProviderIdentity.DeclaredAt(body, declaring), declaring, declaring.Observations, declaring.MemberIndexes)
                {
                    Written = expression,
                });
                keys.Add(key);
            }
        }
        Queries.Resources.Metadata(2, cancellationToken: Queries.OperationToken);
        retained = new(providers, [.. keys], _lookupLevelReplacements);
        _levelProviders[(scope, stratum)] = retained;
        Queries.Observations?.RecordStaticLevelProvidersBuild(providers.Count);
        return retained;
    }

    /// <summary>
    /// THE OPENED-NAME RULE AT ONE LEVEL of this operation (<see cref="ElaboratedScopeLookup.SelectOpenLevel(ElaboratedPropertyScope, string, StaticCycleCheck)"/>):
    /// each provider's public member of <paramref name="name"/>, in provider order. A level of more than
    /// <see cref="Evaluator.OpenProviderLinearIndexLimit"/> providers whose closed member index
    /// (<see cref="StaticQueryProjection.OpenMemberIndex"/>, Q1's own selection) is already final answers a name no
    /// provider offers, or exactly one offers, from that index — the index lists every public name of exactly these
    /// providers, with the one provider that offers it or none when two do — without asking each provider; an ambiguous
    /// name, a smaller level, an index not yet settled and every other case scan the providers in order, which is what
    /// every level did. The index is only read, never computed here.
    /// </summary>
    internal OpenNameSelection SelectOpenLevel(ElaboratedPropertyScope level, StaticScopeKey scope, string name, StaticCycleCheck stratum)
    {
        if (RetainedProviders(scope, stratum) is not { } retained) return default;
        var providers = retained.Providers;
        if (providers.Count > Evaluator.OpenProviderLinearIndexLimit
            && Queries.TrySettledOpenMember(scope, stratum, name, out var selected))
        {
            OpenNameSelection selection = default;
            if (selected is { } match)
            {
                var position = retained.PositionOf(match.Provider, Queries.Resources, Queries.OperationToken);
                selection = new(level, new(providers[position], match.Hit), null);
            }
            Queries.Observations?.RecordStaticSettledOpenSelection();
            return selection;
        }
        return ElaboratedScopeLookup.ScanOpenLevel(level, providers, name);
    }

    /// <summary>A level's retained providers (<see cref="Providers"/>), their Q2 keys in the same order, and where each one is.</summary>
    private sealed class RetainedLevelProviders(List<ResolvedOpenProvider> providers, StaticScopeKey[] keys, long replacements)
    {
        private long _replacements = replacements;
        private Dictionary<StaticScopeKey, int>? _positions;

        internal List<ResolvedOpenProvider> Providers { get; } = providers;

        /// <summary>
        /// Whether every provider's declaring level is still the one registered for its context: nothing replaced a level
        /// since this list was built or last checked, or every replacement concerned another context.
        /// </summary>
        internal bool IsCurrent(StaticStructureOperation operation)
        {
            if (_replacements == operation._lookupLevelReplacements) return true;
            for (var index = 0; index < keys.Length; index++)
            {
                operation.Queries.Resources.Metadata(0, cancellationToken: operation.Queries.OperationToken);
                if (!operation._lookupLevels.TryGetValue(keys[index].Parent ?? operation.Queries.Keys.Root, out var registered)
                    || !ReferenceEquals(registered, Providers[index].Level)) return false;
            }
            _replacements = operation._lookupLevelReplacements;
            return true;
        }

        /// <summary>The position of a provider selected from this same Q2 sequence. The table is built and charged once.</summary>
        internal int PositionOf(StaticScopeKey provider, StaticQueryResourceBudget resources, CancellationToken cancellationToken)
        {
            if (_positions is null)
            {
                resources.Metadata(2L * keys.Length, work: 0, cancellationToken);
                var positions = new Dictionary<StaticScopeKey, int>(keys.Length, ReferenceEqualityComparer.Instance);
                for (var index = 0; index < keys.Length; index++)
                {
                    resources.Metadata(0, cancellationToken: cancellationToken);
                    positions.Add(keys[index], index);
                }
                _positions = positions;
            }
            return _positions[provider];
        }
    }

    internal string[] UndecidedInputs(StaticScopeKey scope)
        => Queries.CandidateNames(scope).Where(name => Read(StaticQueryKey.IsInput(scope, name)).IsUnknown).ToArray();

    internal (string Name, SourceSpan? Span) DefinitionOf(StaticScopeKey scope)
    {
        if (scope.Parent is { } parent)
            foreach (var property in SourceOf(parent).Properties)
                if (ReferenceEquals(OpenProviderIdentity.DeclarationOf(property.Value), scope.Declaration))
                    return (property.Name, property.FirstDeclarationSpan);
        return (ReferenceEquals(scope, Queries.Root) ? "<root>" : "<anonymous>", null);
    }
}
