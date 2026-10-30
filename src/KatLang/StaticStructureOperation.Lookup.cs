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
        if (!_lookupLevels.ContainsKey(context.Key)) Queries.Resources.Metadata(8);
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

    internal IReadOnlyList<ResolvedOpenProvider> Providers(StaticScopeKey scope, StaticCycleCheck stratum)
    {
        var source = SourceOf(scope);
        var providers = new List<ResolvedOpenProvider>();
        var seen = new HashSet<StaticScopeKey>(ReferenceEqualityComparer.Instance);
        foreach (var expression in source.Opens)
        {
            var fact = Read(StaticQueryKey.Project(StaticQueryKind.OpenProviders, scope, StaticQueryProjection.OpenTarget,
                stratum: stratum, node: expression));
            if (fact.Data is not StaticScopeKey[] keys) continue;
            foreach (var key in keys)
            {
                var identity = Queries.Keys.ProviderScope(key, Queries.Resources, Queries.OperationToken);
                if (seen.Contains(identity)) continue;
                Queries.Resources.Metadata(4);
                seen.Add(identity);
                var body = SourceOf(key);
                var declaring = LookupLevel(key.Parent ?? Queries.Keys.Root);
                providers.Add(new(body, declaring.Observations, declaring.MemberIndexes, OpenProviderIdentity.DeclaredAt(body, declaring))
                {
                    Level = declaring, Written = expression,
                });
            }
        }
        return providers;
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
