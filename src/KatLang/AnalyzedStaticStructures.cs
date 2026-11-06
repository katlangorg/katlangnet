using System.Collections.Frozen;
using System.Collections.Immutable;

namespace KatLang;

/// <summary>
/// A standalone analysis snapshot of Q1–Q7, not a resolved-signature publication. It never publishes a Q8/Q9
/// completion, attaches to an AST, freezes a deferred continuation, or retains its producer operation/token.
/// </summary>
internal sealed class AnalyzedStaticStructures : StaticLookupFacts
{
    // Reuse the immutable occurrence projection representation, without attaching it to syntax or publishing Q9 completion.
    // It holds closed analysis facts only; sealing drops the ledger and retains no producer operation or token.
    private readonly CompletedStaticStructures _graph;
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
    private AnalyzedStaticStructures(StaticScopeKey prelude, AnalyzedStaticStructures? inherited, StaticQueryResourceBudget resources)
        => (PreludeKey, _base, _graph) = (prelude, inherited, new(prelude, inherited?._graph, resources));
    internal override StaticScopeKey PreludeKey { get; }
    internal override IEnumerable<StaticScopeKey> Scopes => _graph.Scopes;
    internal StaticQueryStatistics Statistics { get; private set; }
    internal override void EnsureUsable() => _graph.EnsureUsable();
    internal override CompletedStaticStructures.BodyFacts? Facts(StaticScopeKey key) => _graph.Facts(key);
    internal override bool OccursBelowAReach(StaticScopeKey key, Dictionary<StaticScopeKey, bool> memo)
        => _graph.OccursBelowAReach(key, memo);
    internal override StaticScopeKey? Child(StaticScopeKey parent, Algorithm body, Pattern? pattern = null)
    {
        if ((_definitions.GetValueOrDefault((body.IsModuleRoot ? PreludeKey : parent, body, body.IsModuleRoot ? null : pattern))
            ?? _base?.Child(parent, body, pattern)) is { } exact) return exact;
        var projected = _graph.Child(parent, body, pattern);
        // A declaration-preserving host copy is a new source view, not an admitted occurrence of the old body. Analysis
        // previously indexed exact bodies only; projection must preserve that boundary, including unavailable recipes.
        return projected is not null && ReferenceEquals(_graph.Facts(projected)?.Body, body) ? projected : null;
    }

    private readonly record struct Region(Algorithm Body, object? Branch, BindingFootprint Bindings)
    {
        public bool Equals(Region other) => ReferenceEquals(Body, other.Body) && ReferenceEquals(Branch, other.Branch)
            && Bindings.Equals(other.Bindings);
        public override int GetHashCode() => HashCode.Combine(System.Runtime.CompilerServices.RuntimeHelpers.GetHashCode(Body),
            Branch is null ? 0 : System.Runtime.CompilerServices.RuntimeHelpers.GetHashCode(Branch), Bindings);
    }

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
        AnalyzedStaticStructures? inherited = null, bool projectOccurrences = true, CancellationToken cancellationToken = default)
    {
        var queries = operation.Queries;
        var result = new AnalyzedStaticStructures(queries.Keys.Root, inherited, queries.Resources);
        var graph = result._graph;
        graph.SuspendProjection();
        var regions = new Dictionary<Region, StaticScopeKey>();
        var regionNames = new RegionFreeNames(new NameSetInterner());
        var belowReaches = new Dictionary<StaticScopeKey, StaticScopeKey>(ReferenceEqualityComparer.Instance);
        var reaches = new Dictionary<StaticScopeKey, StaticScopeKey>(ReferenceEqualityComparer.Instance);
        var projected = new List<(StaticScopeKey Key, StaticScopeKey Counterpart)>();
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
            // A query may already have named a descendant below a served occurrence (for example its receiver). Adopt that
            // exact key as the projection of its counterpart rather than eagerly expanding its children as well.
            if (key.Parent is { } outer && (reaches.TryGetValue(outer, out var counterpartParent)
                || belowReaches.TryGetValue(outer, out counterpartParent))
                && queries.Keys.KnownDefinitionIn(counterpartParent, source, key.BindingRegion) is { } counterpart)
            {
                queries.Resources.Metadata(4, cancellationToken: cancellationToken);
                belowReaches.Add(key, counterpart);
                projected.Add((key, counterpart));
                Include(counterpart);
                continue;
            }
            var view = operation.Published(key, StaticPublicationStage.Resolved)
                ?? operation.DetectedView(key) ?? source;
            var ready = view is not Algorithm.Alias { ResolvedTargetCell.IsPending: true }
                && view is not Algorithm.Alias { ResolvedStructureCell.IsPending: true };
            var served = false;
            if (ready && key.Parent is { } declaring && !source.IsModuleRoot && source is not Algorithm.Conditional
                && projectOccurrences && operation.SharedBodies?.Holds(source) == true
                && BindingFootprint.At(operation, declaring, regionNames.Of(source)) is { } footprint)
            {
                var region = new Region(source, key.BindingRegion, footprint);
                queries.Resources.Metadata(4, cancellationToken: cancellationToken);
                if (regions.TryGetValue(region, out var processed))
                {
                    var chain = 2L + key.Depth + processed.Depth;
                    queries.Resources.Metadata((chain + 7) / 8, chain, cancellationToken);
                    graph.AddReach(key, processed, Identity(key), Identity(processed));
                    reaches.Add(key, processed);
                    queries.Observations?.StageObserver?.Invoke("analysis-region-reuse", true);
                    queries.EnsureUsable();
                    served = true;
                }
                else regions.Add(region, key);
            }
            var members = new Dictionary<string, StaticScopeKey>(StringComparer.Ordinal);
            foreach (var property in source.Properties)
            {
                var child = operation.ContextOf(key, property.Value);
                if (property.Name is not null) members.TryAdd(property.Name, child);
                if (prelude.Contains(key)) prelude.Add(child);
                if (!served) Include(child);
            }
            if (source is Algorithm.Conditional family)
                foreach (var branch in family.Branches)
                    Include(operation.ContextOf(family.Opens.Count == 0 ? key.Parent ?? queries.Keys.Root : key,
                        branch.Body, branch.Pattern));
            // Own written expressions only. An algorithm reached in an open is rooted at the prelude. A hoisted deconstruction
            // source's rows are its owner's (WrittenRows): its context, storage below that owner, has none of its own.
            if (!served) IncludeExpressions(source.Opens, queries.Keys.Root);
            if (!served && (source is not Algorithm.User { IsAssignmentDeconstructionSource: true } || ReferenceEquals(key, entry)))
                IncludeExpressions(AstHelpers.WrittenRows(source), key);
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
            graph.Add(key, new(ready ? view : null, receiver, open, members.ToFrozenDictionary(StringComparer.Ordinal), parameters, providers.ToImmutable()));
            if (key.Parent is { } parent)
            {
                if (ready) result._definitions.TryAdd((parent, view, key.BindingRegion), key);
            }
        }
        graph.AdoptBelowReaches(projected);
        graph.Seal(cancellationToken);
        result.Statistics = queries.Statistics;
        return result.Context(entry);

        OpenProviderIdentity Identity(StaticScopeKey key)
            => OpenProviderIdentity.DeclaredIn(operation.SourceOf(key), operation.OwnersOf(key.Parent ?? queries.Keys.Root));

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
