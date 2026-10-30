using System.Collections.Frozen;
using System.Collections.Immutable;

namespace KatLang;

/// <summary>
/// A standalone analysis snapshot of Q1–Q7, not a resolved-signature publication. It never publishes a Q8/Q9
/// completion, attaches to an AST, freezes a deferred continuation, or retains its producer operation/token.
/// </summary>
internal sealed class AnalyzedStaticStructures : StaticLookupFacts
{
    private readonly Dictionary<StaticScopeKey, CompletedStaticStructures.BodyFacts> _facts = new(ReferenceEqualityComparer.Instance);
    private readonly Dictionary<(StaticScopeKey Parent, object Declaration, object? Pattern), StaticScopeKey?> _children = new(ChildComparer.Instance);
    private sealed class ChildComparer : IEqualityComparer<(StaticScopeKey Parent, object Declaration, object? Pattern)>
    {
        internal static readonly ChildComparer Instance = new();
        public bool Equals((StaticScopeKey Parent, object Declaration, object? Pattern) x, (StaticScopeKey Parent, object Declaration, object? Pattern) y)
            => ReferenceEquals(x.Parent, y.Parent) && ReferenceEquals(x.Declaration, y.Declaration) && ReferenceEquals(x.Pattern, y.Pattern);
        public int GetHashCode((StaticScopeKey Parent, object Declaration, object? Pattern) key)
            => HashCode.Combine(System.Runtime.CompilerServices.RuntimeHelpers.GetHashCode(key.Parent),
                System.Runtime.CompilerServices.RuntimeHelpers.GetHashCode(key.Declaration),
                key.Pattern is null ? 0 : System.Runtime.CompilerServices.RuntimeHelpers.GetHashCode(key.Pattern));
    }
    private readonly Dictionary<(StaticScopeKey Parent, object Declaration, object? Pattern), StaticScopeKey> _definitions = new(ChildComparer.Instance);
    private readonly AnalyzedStaticStructures? _base;
    private AnalyzedStaticStructures(StaticScopeKey prelude, AnalyzedStaticStructures? inherited = null)
        => (PreludeKey, _base) = (prelude, inherited);
    internal override StaticScopeKey PreludeKey { get; }
    internal override IEnumerable<StaticScopeKey> Scopes => (_base?.Scopes ?? []).Concat(_facts.Keys);
    internal StaticQueryStatistics Statistics { get; private set; }
    internal override void EnsureUsable() { }
    internal override CompletedStaticStructures.BodyFacts? Facts(StaticScopeKey key) => _facts.GetValueOrDefault(key) ?? _base?.Facts(key);
    internal override StaticScopeKey? Child(StaticScopeKey parent, Algorithm body, Pattern? pattern = null)
        => _definitions.GetValueOrDefault((body.IsModuleRoot ? PreludeKey : parent, body, body.IsModuleRoot ? null : pattern))
            ?? _base?.Child(parent, body, pattern);

    /// <summary>Analyzes an already name-resolved host AST as supplied, without inference or compiler passes.</summary>
    internal static CompletedStructureContext ForBoundAst(Algorithm root, HostOperations? hostOperations = null,
        IReadOnlyList<(Algorithm Body, Pattern? Pattern)>? declaringScopes = null, Pattern? entryPattern = null,
        SourceProcessingLimits? sourceProcessingLimits = null,
        CancellationToken cancellationToken = default)
    {
        cancellationToken.ThrowIfCancellationRequested();
        if (declaringScopes is null && root.CompletedStructure is { } publication)
        {
            var context = publication.Entry is { } entry && publication.MatchesEntry(root)
                ? publication.Facts.Context(entry) : publication.Facts.ExactContext(root);
            if (context is not null) return context;
        }
        // The completed fast path already crossed the source gate. External host graphs must cross it here;
        // this is structural safety admission, never name detection or signature completion.
        if (AstStructuralPreflight.Check(root, EvaluationLimits.MaxSupportedAstDepth,
                AstConsumerProfile.FullyRecursive) is { } rejection)
            throw new ArgumentException($"Standalone structure analysis requires an acyclic, structurally safe AST ({rejection.Kind}).", nameof(root));
        if (declaringScopes is null)
        {
            var parents = new Stack<ScopeCtx>();
            for (var at = root.Parent; at is not null; at = at.Parent) parents.Push(at);
            declaringScopes = parents.Select(parent => (ScopeBody(parent), (Pattern?)null)).ToArray();
        }
        var operation = StaticStructureAdmission.Create(root, hostOperations, sourceProcessingLimits, phase: StaticAstPhase.Resolved,
            sourceAncestors: declaringScopes.Select(scope => scope.Body).ToArray(), cancellationToken: cancellationToken).Operation;
        var declaring = operation.Queries.Keys.Root;
        foreach (var (owner, pattern) in declaringScopes)
        {
            cancellationToken.ThrowIfCancellationRequested();
            declaring = operation.ContextOf(declaring, owner, pattern);
        }
        var key = ReferenceEquals(declaring, operation.Queries.Keys.Root) && entryPattern is null
            ? operation.Root : operation.ContextOf(declaring, root, entryPattern);
        return Project(operation, key, cancellationToken: cancellationToken);
    }

    private static Algorithm ScopeBody(ScopeCtx parent)
        => parent.Owner is Algorithm.User user
            ? user with { Parent = null, Opens = parent.Opens, Properties = parent.Properties, Output = [] }
            : new Algorithm.User(null, [], parent.Opens, parent.Properties, []);

    /// <summary>Projects the immutable source and current views of the caller's admitted raw operation.</summary>
    internal static CompletedStructureContext ForAdmittedSource(StaticStructureContext context,
        CancellationToken cancellationToken = default)
        => Project(context.Operation, context.Key, cancellationToken: cancellationToken);

    internal static CompletedStructureContext Project(StaticStructureOperation operation, StaticScopeKey entry,
        AnalyzedStaticStructures? inherited = null, CancellationToken cancellationToken = default)
    {
        var queries = operation.Queries;
        var result = new AnalyzedStaticStructures(queries.Keys.Root, inherited);
        var pending = new Queue<StaticScopeKey>();
        var admitted = new HashSet<StaticScopeKey>(ReferenceEqualityComparer.Instance);
        var prelude = new HashSet<StaticScopeKey>(ReferenceEqualityComparer.Instance) { queries.Keys.Root };
        void Include(StaticScopeKey key)
        {
            for (var at = key; at is not null && inherited?.Facts(at) is null && !admitted.Contains(at); at = at.Parent)
            {
                queries.Resources.Metadata(4, cancellationToken: cancellationToken);
                admitted.Add(at);
                pending.Enqueue(at);
            }
        }
        Include(entry);
        while (pending.TryDequeue(out var key))
        {
            cancellationToken.ThrowIfCancellationRequested();
            queries.EnsureUsable();
            var source = operation.SourceOf(key);
            var view = operation.Published(key, StaticPublicationStage.Resolved)
                ?? operation.Published(key, StaticPublicationStage.Detected) ?? source;
            var ready = view is not Algorithm.Alias { ResolvedTargetCell.IsPending: true }
                && view is not Algorithm.Alias { ResolvedStructureCell.IsPending: true };
            var members = new Dictionary<string, StaticScopeKey>(StringComparer.Ordinal);
            foreach (var property in source.Properties)
            {
                var child = operation.ContextOf(key, property.Value);
                if (property.Name is not null) members.TryAdd(property.Name, child);
                if (prelude.Contains(key)) prelude.Add(child);
                Include(child);
            }
            if (source is Algorithm.Conditional family)
                foreach (var branch in family.Branches)
                    Include(operation.ContextOf(family.Opens.Count == 0 ? key.Parent ?? queries.Keys.Root : key,
                        branch.Body, branch.Pattern));
            // Own written expressions only. An algorithm reached in an open is rooted at the prelude.
            IncludeExpressions(source.Opens, queries.Keys.Root);
            IncludeExpressions(source.Output, key);
            var receiver = ready ? Select(operation.Read(StaticQueryKey.TargetWalk(key, StaticCycleCheck.Formation)))
                : CompletedStaticStructures.Selection.Unavailable;
            var open = ready ? Select(operation.Read(StaticQueryKey.Project(StaticQueryKind.TargetWalk, key,
                StaticQueryProjection.OpenStructure, stratum: StaticCycleCheck.Formation))) : CompletedStaticStructures.Selection.Unavailable;
            var providers = ImmutableArray.CreateBuilder<CompletedStaticStructures.Selection>(source.Opens.Count);
            foreach (var expression in source.Opens)
            {
                var fact = ready ? operation.Read(StaticQueryKey.Project(StaticQueryKind.OpenProviders, key,
                    StaticQueryProjection.OpenTarget, stratum: StaticCycleCheck.Formation, node: expression)) : StaticFact.Unknown;
                providers.Add(fact.Data is StaticScopeKey[] { Length: 1 } keys ? Select(new(StaticFactKind.Structure, keys[0]))
                    : fact.IsUnknown ? CompletedStaticStructures.Selection.Unavailable : new(StaticFactKind.Missing));
            }
            var parameterNames = new HashSet<string>(queries.WrittenParametersOf(key), StringComparer.Ordinal);
            foreach (var candidate in queries.CandidateNames(key))
                if (operation.Read(StaticQueryKey.IsInput(key, candidate)).Kind == StaticFactKind.Yes)
                    parameterNames.Add(candidate);
            if (view is Algorithm.User user)
                parameterNames.UnionWith(ParameterPattern.FlattenCaptures(user.NameResolutionParameterPatterns).Select(parameter => parameter.Name));
            var parameters = parameterNames.ToFrozenSet(StringComparer.Ordinal);
            queries.Resources.Metadata(12 + 2L * members.Count + 2L * providers.Count + 4L * parameters.Count,
                cancellationToken: cancellationToken);
            result._facts.Add(key, new(ready ? view : null, receiver, open, members.ToFrozenDictionary(StringComparer.Ordinal), parameters, providers.ToImmutable()));
            if (key.Parent is { } outer)
            {
                if (ready) result._definitions.TryAdd((outer, view, key.BindingRegion), key);
                var child = (outer, key.Declaration, key.BindingRegion);
                if (!result._children.TryAdd(child, key) && !ReferenceEquals(result._children[child], key)) result._children[child] = null;
            }
        }
        result.Statistics = queries.Statistics;
        return result.Context(entry);

        CompletedStaticStructures.Selection Select(StaticFact fact)
        {
            if (fact.Kind != StaticFactKind.Structure || fact.Scope is not { } selected) return new(fact.Kind);
            Include(selected);
            return new(fact.Kind, selected, OpenProviderIdentity.DeclaredIn(operation.SourceOf(selected),
                operation.OwnersOf(selected.Parent ?? queries.Keys.Root)));
        }
        void IncludeExpressions(IEnumerable<Expr> expressions, StaticScopeKey declaring)
        {
            var nodes = new Stack<object>();
            var seen = new HashSet<object>(ReferenceEqualityComparer.Instance);
            foreach (var expression in expressions) Add(expression);
            while (nodes.TryPop(out var node))
            {
                cancellationToken.ThrowIfCancellationRequested();
                if (node is Algorithm body) { Include(operation.ContextOf(declaring, body)); continue; }
                for (var i = 0; AstStructuralPreflight.TryGetChild(node, i, out var child); i++) Add(child);
            }
            void Add(object node)
            {
                queries.Resources.Metadata(0, cancellationToken: cancellationToken);
                if (seen.Contains(node)) return;
                queries.Resources.Metadata(2, cancellationToken: cancellationToken);
                seen.Add(node);
                nodes.Push(node);
            }
        }
    }
}
