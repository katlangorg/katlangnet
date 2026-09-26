namespace KatLang;

internal static class PropertyExposureResolver
{
    internal readonly record struct Requirement(string Name, ElaboratedPropertyScope? Owner);

    internal sealed class AnalysisSummary(IEnumerable<Requirement> requirements)
    {
        public static AnalysisSummary Empty { get; } = new([]);
        public HashSet<Requirement> Requirements { get; } = new(requirements);
        public IEnumerable<string> RequiredAncestorOwnedParameterNames => Requirements.Select(r => r.Name).Distinct(StringComparer.Ordinal);
        public bool RequiresAncestorOwnedParameters => Requirements.Count > 0;
        public bool SetEquals(AnalysisSummary other) => Requirements.SetEquals(other.Requirements);
    }

    /// <summary>
    /// One level of the resolver's lexical chain: the level's elaborated property scope (its
    /// declarations, its <c>open</c> targets, and the ancestor levels through
    /// <see cref="ElaboratedPropertyScope.Parent"/>) paired with the FINAL requirement summary
    /// of each property the level declares (the level in progress carries the current
    /// fixed-point iteration's map). Kept as a chain rather than one merged name→summary map
    /// so that a seed relative to an ANCESTOR level — the requirements of a member reached
    /// through an <c>open</c> provider or a member path declared farther out — is expanded from
    /// that level outward, never against declarations that shadow it only from the consumer's
    /// position.
    /// </summary>
    internal sealed class SummaryScope
    {
        public SummaryScope(
            SummaryScope? parent,
            ElaboratedPropertyScope propertyScope,
            IReadOnlyDictionary<string, AnalysisSummary> summaries,
            IReadOnlySet<string>? parameters = null,
            Algorithm? algorithm = null)
        {
            Algorithm = algorithm;
            Parameters = parameters ?? NoParameters;
            Parent = parent;
            PropertyScope = propertyScope;
            Summaries = summaries;
            Root = parent is null ? this : parent.Root;
        }

        private static readonly IReadOnlySet<string> NoParameters = new HashSet<string>(StringComparer.Ordinal);

        /// <summary>
        /// The names this level binds, as a SET (FE-1): a requirement is attributed to its owner by
        /// membership, so a level of W parameters answers in O(1) — the former list scan cost W per
        /// required name per level, for every property summary at a wide owner.
        /// </summary>
        public IReadOnlySet<string> Parameters { get; }
        public Algorithm? Algorithm { get; }

        public IEnumerable<Requirement> ResolveRequirements(IEnumerable<OwnerQualifiedParameter> requirements,
            IReadOnlySet<Algorithm>? boundOwners = null)
        {
            foreach (var requirement in requirements)
            {
                if (requirement.Owner is not null && boundOwners?.Contains(requirement.Owner) == true)
                    continue;
                if (requirement.Owner is null)
                {
                    yield return new Requirement(requirement.Name, null);
                    continue;
                }
                var owner = this;
                while (owner is not null && !ReferenceEquals(owner.Algorithm, requirement.Owner))
                    owner = owner.Parent;
                yield return new Requirement(requirement.Name, owner?.PropertyScope);
            }
        }

        public IEnumerable<Requirement> ResolveRequirements(IEnumerable<string> names)
        {
            foreach (var name in names)
            {
                var owner = this;
                while (owner is not null && !owner.Parameters.Contains(name))
                    owner = owner.Parent;
                yield return new Requirement(name, owner?.PropertyScope);
            }
        }

        public int OwnerDepth(Requirement requirement)
        {
            var depth = 0;
            for (var level = this; level is not null; level = level.Parent, depth++)
                if (ReferenceEquals(level.PropertyScope, requirement.Owner))
                    return depth;
            return -1;
        }

        public SummaryScope? Parent { get; }

        public ElaboratedPropertyScope PropertyScope { get; }

        public IReadOnlyDictionary<string, AnalysisSummary> Summaries { get; }

        /// <summary>The prelude level every inline <c>open</c> target region starts at.</summary>
        public SummaryScope Root { get; }

        /// <summary>
        /// Ownership-first PROPERTY lookup from this level outward — the direct lexical chain
        /// (the evaluator's <c>LookupLexicalDirect</c>); opens are never consulted here.
        /// </summary>
        public bool TryLookup(string name, out SummaryScope level, out PropertyLookupHit hit, out AnalysisSummary summary)
        {
            for (var current = this; current is not null; current = current.Parent)
            {
                if (current.PropertyScope.TryLookupOwnProperty(name) is { } found)
                {
                    level = current;
                    hit = found;
                    summary = current.Summaries.TryGetValue(name, out var stored) ? stored : AnalysisSummary.Empty;
                    return true;
                }
            }

            level = null!;
            hit = default;
            summary = AnalysisSummary.Empty;
            return false;
        }
    }

    /// <summary>
    /// Shared subtrees (acyclic DAGs) are legal and DAG-safe: exposure classification of a
    /// node referenced from several parents matches the equivalent duplicated tree (summary
    /// seeds are name SETS, so multiplicities never mattered), while the rewrite walk is
    /// reference-identity memoized per constant-context region — work is bounded by the
    /// DISTINCT reachable nodes, never the number of root-to-node paths, and the rewritten
    /// output preserves sharing within a scope. One completed-summary memo (see
    /// <see cref="PropertyDependencyGraphBuilder.SummaryMemo"/>) spans the resolution, plus
    /// per-region rewrite memos. The pass runs ONCE: selection never depends on exposure
    /// (<c>open</c> selects public members, dot access declared members, accessibility is
    /// checked after selection), so classifying a member can never change what any name
    /// resolves to, and no re-elaboration round exists.
    /// </summary>
    public static Algorithm Resolve(Algorithm root)
        => Resolve(root, observations: null);

    /// <remarks><paramref name="hostOperations"/> are the run configuration's host operations,
    /// whose ambient prelude members the chain must see exactly as parameter detection and the
    /// evaluator do (the prelude is the outermost owner level, reached before any <c>open</c>): a
    /// host operation named like an opened member is what a bare reference selects, so charging
    /// the opened member instead would classify a self-contained property local-only.</remarks>
    internal static Algorithm Resolve(
        Algorithm root,
        FrontEndTraversalObservations? observations,
        HostOperations? hostOperations = null)
        => ResolveInScope(
            root,
            new SummaryScope(
                null,
                ElaboratedScopeLookup.CreateScope(
                    hostOperations?.SemanticPreludeAlgorithm ?? BuiltinRegistry.CreateSemanticPreludeAlgorithm()),
                NoSummaries),
            observations);

    private static readonly IReadOnlyDictionary<string, AnalysisSummary> NoSummaries =
        new Dictionary<string, AnalysisSummary>(StringComparer.Ordinal);

    private static Algorithm ResolveInScope(
        Algorithm root,
        SummaryScope parent,
        FrontEndTraversalObservations? observations)
    {
        var run = new ExposureRun();
        root = ProcessAlgorithm(root, parent, new PropertyDependencyGraphBuilder.SummaryMemo(observations), observations, run);
        if (run.HasDotMemberOrigins)
            new DotMemberProvenanceFinalizer(parent.PropertyScope) { TraversalObservations = observations }.VisitAlgorithm(root);
        return root;
    }

    private sealed class ExposureRun
    {
        public bool HasDotMemberOrigins;

        /// <summary>
        /// FE-3: whether an expression subtree is REWRITE-INVARIANT — it reaches no nested algorithm
        /// (the only thing this pass rewrites below an expression) and no dot-call edge (whose
        /// provenance the pass records) — by node reference, for the whole resolution. Such a subtree
        /// is returned as it is in every region instead of being re-copied per region, so one
        /// synthesized argument bundle shared by K owners stays one bundle, walked once.
        /// </summary>
        private Dictionary<object, bool>? _rewriteInvariant;

        public bool IsRewriteInvariant(Expr expr)
        {
            if (!AstTraversalDagSafety.HasTraversableExprChildren(expr))
                return expr is not Expr.AlgorithmExpr and not Expr.DotCall;
            _rewriteInvariant ??= new(ReferenceEqualityComparer.Instance);
            if (_rewriteInvariant.TryGetValue(expr, out var invariant))
                return invariant;
            invariant = expr switch
            {
                Expr.AlgorithmExpr or Expr.DotCall => false,
                Expr.Grace grace => IsRewriteInvariant(grace.Inner),
                Expr.Unary unary => IsRewriteInvariant(unary.Operand),
                Expr.Binary binary => IsRewriteInvariant(binary.Left) && IsRewriteInvariant(binary.Right),
                Expr.Comparison comparison => IsRewriteInvariant(comparison.First)
                    && comparison.Links.All(link => IsRewriteInvariant(link.Operand)),
                Expr.Index index => IsRewriteInvariant(index.Target) && IsRewriteInvariant(index.Selector),
                Expr.SequenceSpread spread => IsRewriteInvariant(spread.Operand),
                Expr.SequenceConstruct construct => IsRewriteInvariant(construct.Left) && IsRewriteInvariant(construct.Right),
                Expr.ListLiteral list => IsRewriteInvariant(list.Items),
                Expr.Capture capture => IsRewriteInvariant(capture.Body),
                Expr.Call call => IsRewriteInvariant(call.Function) && IsRewriteInvariant(call.Args),
                Expr.Resolve or Expr.Param or Expr.Num or Expr.StringLiteral or Expr.BoolLiteral
                    or Expr.EmptySequence or Expr.NativeCall => true,
            };
            _rewriteInvariant[expr] = invariant;
            return invariant;
        }

        public bool IsRewriteInvariant(OutputBundle bundle)
        {
            _rewriteInvariant ??= new(ReferenceEqualityComparer.Instance);
            if (_rewriteInvariant.TryGetValue(bundle, out var invariant))
                return invariant;
            invariant = bundle.Head.All(IsRewriteInvariant) && (bundle.Tail is not { } tail || IsRewriteInvariant(tail));
            _rewriteInvariant[bundle] = invariant;
            return invariant;
        }
    }

    /// <summary>
    /// The ONE classification rule, applied to every property declared in every body — the
    /// root, a brace block, a property value, an open-target block, and a conditional branch
    /// body alike. A property is <see cref="PropertyExposure.Exported"/> when its value is
    /// self-contained, and <see cref="PropertyExposure.LocalOnlyCapturedAncestorParameters"/>
    /// when its value (transitively) requires an input that only an enclosing owner's call
    /// binds: a parameter of an enclosing parameterized algorithm, or a pattern binder of an
    /// enclosing conditional branch (both reach the summary channel as the same
    /// <see cref="Expr.Param"/> references, and neither is owned by the declaring body). The
    /// required names are recorded on the property
    /// (<see cref="Property.RequiredAncestorParameters"/>): owner-qualified capture positions retain the original
    /// bindings for the evaluators' accessibility law, including across shadowing. Exported-ness is thus a fact
    /// about the property's VALUE — evaluable wherever the property can be reached — never
    /// about where the declaration is written, and never a universal hiding: a local-only
    /// member is usable from every lexical context inside the owners of its required inputs.
    /// WHERE it can be reached from is decided structurally by lookup, not here: a
    /// conditional family exposes no structural members, so nothing declared in a branch body
    /// is reachable BY NAME from outside the conditional (the evaluator, the front-end lookup,
    /// the editor, and Lean all deny that at the family and report it as
    /// <see cref="PropertyExposure.LocalOnlyConditionalAlgorithm"/>, which is a family-level
    /// error reason this pass never assigns). Inside the branch — and on the algorithm
    /// channel, for anything the branch itself hands out — a branch declaration therefore
    /// behaves exactly like the same declaration in a parameterized body.
    /// </summary>
    private static PropertyExposure ClassifyDeclaredProperty(AnalysisSummary summary)
        => summary.RequiresAncestorOwnedParameters
            ? PropertyExposure.LocalOnlyCapturedAncestorParameters
            : PropertyExposure.Exported;

    /// <summary>
    /// Reference-identity memo state for ONE exposure rewrite region — one user algorithm's
    /// opens/output/property-value processing (the final visible summaries are fixed before
    /// any of it runs), or one conditional's open list. Shared expressions rewrite once and
    /// stay shared; <see cref="Algorithms"/> memoizes nested-algorithm processing (property
    /// values and <see cref="Expr.AlgorithmExpr"/> contents run under the identical context:
    /// the final summaries), so two properties or wrappers sharing ONE algorithm classify it
    /// once. The resolution-wide summary memo rides along so nested regions keep sharing
    /// completed summaries. Conditional BRANCH bodies use memo regions keyed by their relative binder/open
    /// context. Equivalent family contexts can share analysis, but a plain body or different
    /// binder context has different owner positions and must be classified separately.
    /// </summary>
    private sealed class ExposureWalkMemos(
        PropertyDependencyGraphBuilder.SummaryMemo summaryMemo,
        FrontEndTraversalObservations? observations,
        SummaryScope scope,
        ExposureRun run)
    {
        public Dictionary<Expr, Expr>? Rewrites;

        /// <summary>
        /// Call and dot-call argument bundles rewritten in this region, by bundle reference: implicit
        /// lifting gives every lifted reference to one callable in a resolver region the SAME
        /// synthesized bundle (FE-2), and it must stay one bundle here rather than being copied once
        /// per call edge (see <see cref="RewriteArgumentBundle"/>).
        /// </summary>
        public Dictionary<OutputBundle, OutputBundle>? ArgumentBundles;

        public Dictionary<Algorithm, Algorithm>? Algorithms;

        private Dictionary<IReadOnlyList<Expr>, Dictionary<int, ExposureWalkMemos>>? _branchRegions;

        public ExposureWalkMemos ForBranch(Algorithm.Conditional family, Pattern pattern)
        {
            // These are relative capture positions, not runtime family identities.
            // Equal binder sets and opens under one parent produce the same metadata;
            // retaining that equivalence prevents shared family diamonds expanding paths.
            var opens = family.Opens.Count == 0 ? Array.Empty<Expr>() : family.Opens;
            _branchRegions ??= new(ReferenceEqualityComparer.Instance);
            if (!_branchRegions.TryGetValue(opens, out var byBinders))
                _branchRegions[opens] = byBinders = new();
            var context = SummaryMemo.BranchContexts.NamesOf(pattern);
            var key = context.Id;
            if (!byBinders.TryGetValue(key, out var region))
            {
                var familyScope = ElaboratedScopeLookup.CreateScope(family, Scope.PropertyScope);
                region = new ExposureWalkMemos(SummaryMemo, Observations,
                    new SummaryScope(Scope, familyScope, NoSummaries, context.Names, family), Run);
                byBinders[key] = region;
            }
            return region;
        }

        public readonly PropertyDependencyGraphBuilder.SummaryMemo SummaryMemo = summaryMemo;

        public readonly FrontEndTraversalObservations? Observations = observations;

        public readonly SummaryScope Scope = scope;

        public readonly ExposureRun Run = run;
    }

    private static Algorithm ProcessAlgorithm(
        Algorithm algorithm,
        SummaryScope parent,
        PropertyDependencyGraphBuilder.SummaryMemo summaryMemo,
        FrontEndTraversalObservations? observations,
        ExposureRun run)
        => algorithm switch
        {
            Algorithm.User user => ProcessUserAlgorithm(user, parent, summaryMemo, observations, run),
            // A family reached outside any region (a host root, or a deferred branch's own
            // demand-time elaboration) opens a region of its own.
            Algorithm.Conditional conditional => ProcessConditionalAlgorithm(
                conditional,
                new ExposureWalkMemos(summaryMemo, observations, parent, run)),
            Algorithm.Builtin => algorithm,
        };

    private static Algorithm ProcessUserAlgorithm(
        Algorithm.User algorithm,
        SummaryScope parent,
        PropertyDependencyGraphBuilder.SummaryMemo summaryMemo,
        FrontEndTraversalObservations? observations,
        ExposureRun run)
    {
        // A synthetic assignment-deconstruction helper (`x, *y, z = RHS`) is a fully-elaborated
        // leaf: no properties, no opens, and an output that is exactly its own bound Param. It
        // captures no ancestor-owned parameter, so it needs no exposure rewriting. The general
        // path would still analyze and rewrite it per helper for no observable effect.
        if (algorithm is Algorithm.User { AssignmentDeconstructionTarget: not null })
            return algorithm;

        observations?.RecordExposureAlgorithmExpansion();

        // The summary channel is the ONLY builder data this pass consumes: what ancestors own
        // is not an input to it (a captured parameter is reported by name regardless), so no
        // ancestor-owned or locally-owned name context is threaded here (M17).
        var summaryGraph = PropertyDependencyGraphBuilder.BuildSummaries(
            algorithm,
            summaryMemo,
            observations);

        var levelScope = ElaboratedScopeLookup.CreateScope(algorithm, parent.PropertyScope);
        // This level's parameter names, materialized once per resolution and shared by every
        // fixed-point iteration's scope and the final one (FE-1).
        var parameterNames = summaryMemo.ParameterNamesOf(algorithm, observations);
        var walkMemos = PropertyDependencyGraphBuilder.CreateWalkMemos(summaryMemo, observations);
        var currentPropertySummaries = new Dictionary<string, AnalysisSummary>(StringComparer.Ordinal);
        foreach (var property in algorithm.Properties)
            currentPropertySummaries[property.Name] = AnalysisSummary.Empty;

        // The summary graph already centralizes the stable per-property seed facts:
        // direct required ancestor-owned names plus summary edges to visible names, sibling
        // properties, and pending member paths / opened names. What still changes here is each
        // property's accumulated RequiredAncestorOwnedParameterNames after following those
        // edges through the current local summary map. That closure can be transitive or
        // cyclic (mutually opening libraries included), so the exposure pass runs a local
        // least fixed point before rewriting children with the final summaries.
        while (true)
        {
            var level = new SummaryScope(parent, levelScope, currentPropertySummaries, parameterNames, algorithm);
            var resolution = new PendingResolution(walkMemos);
            var nextPropertySummaries = new Dictionary<string, AnalysisSummary>(StringComparer.Ordinal);
            for (var propertyIndex = 0; propertyIndex < algorithm.Properties.Count; propertyIndex++)
            {
                var property = algorithm.Properties[propertyIndex];
                nextPropertySummaries[property.Name] = SummarizePropertyDependencies(
                    summaryGraph,
                    propertyIndex,
                    level,
                    resolution);
            }

            if (SummariesEqual(currentPropertySummaries, nextPropertySummaries))
            {
                currentPropertySummaries = nextPropertySummaries;
                break;
            }

            currentPropertySummaries = nextPropertySummaries;
        }

        var finalLevel = new SummaryScope(parent, levelScope, currentPropertySummaries, parameterNames, algorithm);
        // Properties and output share one lexical scope and summary context. Inline
        // open providers below have their own memo because they resolve at the prelude.
        var memos = new ExposureWalkMemos(summaryMemo, observations, finalLevel, run);
        var rewrittenProperties = new List<Property>(algorithm.Properties.Count);
        for (var propertyIndex = 0; propertyIndex < algorithm.Properties.Count; propertyIndex++)
        {
            var property = algorithm.Properties[propertyIndex];
            var rewrittenPropertyValue = ProcessSharedNestedAlgorithm(property.Value, memos);

            var summary = currentPropertySummaries[property.Name];
            var rewrittenProperty = new Property(property.Name, rewrittenPropertyValue, property.IsPublic, ClassifyDeclaredProperty(summary))
            {
                DeclarationSpans = property.DeclarationSpans,
                CaptureRequirements = summary.Requirements
                    .Select(r => new CapturedParameterRequirement(r.Name, finalLevel.OwnerDepth(r)))
                    .OrderBy(r => r.Name, StringComparer.Ordinal).ThenBy(r => r.OwnerDepth).ToArray(),
                RequiredAncestorParameters = summary.RequiresAncestorOwnedParameters
                    ? summary.RequiredAncestorOwnedParameterNames.OrderBy(static name => name, StringComparer.Ordinal).ToArray()
                    : [],
            };
            rewrittenProperties.Add(rewrittenProperty);
        }

        var rewrittenOpens = RewriteExprList(
            algorithm.Opens,
            new ExposureWalkMemos(summaryMemo, observations, finalLevel.Root, run));
        var rewrittenOutput = RewriteExprList(algorithm.Output, memos);

        return algorithm with
        {
            Opens = rewrittenOpens,
            Properties = rewrittenProperties,
            Output = OutputBundle.From(rewrittenOutput),
        };
    }

    /// <summary>
    /// Region-memoized nested-algorithm processing (property values,
    /// <see cref="Expr.AlgorithmExpr"/> contents, and conditional branch bodies share the
    /// identical region context — the region's final visible summaries). A nested USER
    /// algorithm opens its own region below; a nested FAMILY uses branch regions that retain
    /// the family's open surface and the matched binder view.
    /// </summary>
    private static Algorithm ProcessSharedNestedAlgorithm(Algorithm algorithm, ExposureWalkMemos memos)
    {
        memos.Algorithms ??= new(ReferenceEqualityComparer.Instance);
        if (!memos.Algorithms.TryGetValue(algorithm, out var rewritten))
        {
            rewritten = algorithm is Algorithm.Conditional conditional
                ? ProcessConditionalAlgorithm(conditional, memos)
                : ProcessAlgorithm(
                    algorithm,
                    memos.Scope,
                    memos.SummaryMemo,
                    memos.Observations,
                    memos.Run);
            memos.Algorithms[algorithm] = rewritten;
        }

        return rewritten;
    }

    private static AnalysisSummary SummarizePropertyDependencies(
        PropertyDependencySummaryGraph summaryGraph,
        int propertyIndex,
        SummaryScope level,
        PendingResolution resolution)
    {
        var node = summaryGraph[propertyIndex];
        var requiredAncestorOwnedParameterNames = new HashSet<Requirement>(
            level.ResolveRequirements(node.RequiredAncestorOwnedParameterNames));
        requiredAncestorOwnedParameterNames.UnionWith(level.ResolveRequirements(node.OwnerQualifiedParameters));

        // A bare visible name is settled by the ONE settlement the pending references use
        // (the chain's own properties first, then the owning level's and its ancestors'
        // opens, in the evaluator's order): a name the property reads through an `open`
        // declared at THIS level — or at an ancestor level — charges the provided member's
        // requirements exactly like a dotted path or an open written inside the value.
        // Dropping such a name classified `Y = X` as Exported beside a local-only opened `X`,
        // so the run-scoped cache handed the first activation's value to every later one.
        foreach (var dependencyName in node.SummaryVisiblePropertyDependencyNames)
            requiredAncestorOwnedParameterNames.UnionWith(resolution.ResolveVisibleName(dependencyName, level));

        foreach (var dependencyIndex in node.SummarySiblingDependencyIndices)
        {
            var dependencyName = summaryGraph.Properties[dependencyIndex].Name;
            if (level.Summaries.TryGetValue(dependencyName, out var summary))
                requiredAncestorOwnedParameterNames.UnionWith(summary.Requirements);
        }

        foreach (var pending in node.PendingReferences)
            requiredAncestorOwnedParameterNames.UnionWith(resolution.Resolve(pending, level));

        return requiredAncestorOwnedParameterNames.Count == 0
            ? AnalysisSummary.Empty
            : new AnalysisSummary(requiredAncestorOwnedParameterNames);
    }

    /// <summary>
    /// The owning level's settlement of the references the scope-free summary walk left
    /// pending (<see cref="PendingReference"/>), in exactly the evaluator's lookup order: the
    /// head as a PROPERTY of the level's chain (ownership first), then the providers of the
    /// levels the reference escaped (innermost first), then the owning level's own
    /// <c>open</c> targets and its ancestors' — each candidate resolved from the level that
    /// declares the open, level by level: the first level at which a target publicly provides
    /// the head decides, its sole provider charging and two or more charging NOTHING (the
    /// evaluator's ambiguousOpen selects no declaration; list order never picks one). A member
    /// reached by navigation charges its requirement seed expanded from ITS declaring level
    /// outward. Requirement sets are monotone unions, so a reference re-entered through a
    /// cycle of mutually opening libraries contributes nothing new (the least fixed point);
    /// the enclosing sibling fixed point iterates the rest to stability.
    /// </summary>
    private sealed class PendingResolution(PropertyDependencyGraphBuilder.SummaryWalkMemos memos)
    {
        private readonly HashSet<(string Key, SummaryScope Level, SummaryScope Site, string Bound)> _inProgress = [];

        public HashSet<Requirement> Resolve(PendingReference pending, SummaryScope level, SummaryScope? site = null,
            IReadOnlySet<Algorithm>? boundOwners = null)
        {
            site ??= level;
            if (pending.BoundOwners.Count > 0)
            {
                var combined = new HashSet<Algorithm>(boundOwners is null ? [] : boundOwners, ReferenceEqualityComparer.Instance);
                combined.UnionWith(pending.BoundOwners);
                boundOwners = combined;
            }
            var key = (pending.ContentKey, level, site,
                boundOwners is null ? "" : string.Join(",", boundOwners.Select(OwnerQualifiedParameter.OwnerKey).Order()));
            var names = new HashSet<Requirement>();
            if (!_inProgress.Add(key))
                return names;

            try
            {
                if (level.TryLookup(pending.Head, out var found, out var hit, out var summary))
                {
                    if (pending.Members.Count == 0)
                    {
                        names.UnionWith(summary.Requirements);
                        return names;
                    }

                    var (charged, navigated) = PropertyDependencyGraphBuilder.ChargePath(
                        hit.Property.Value,
                        PropertyDependencyGraphBuilder.StructuralSteps(pending.Members),
                        memos);
                    names.UnionWith(ResolveSeed(charged, found, site, boundOwners));
                    if (navigated == 0)
                        names.UnionWith(summary.Requirements);
                    return names;
                }

                // The escaped levels' providers, innermost level first. Each level is ONE open
                // lookup: the first level at which any target provides the head decides, and
                // two providers there are the evaluator's ambiguousOpen — the reference then
                // selects NO declaration and charges nothing. Taking the first-listed provider
                // made the classification depend on target order (`open A, B` beside a
                // capturing `A.X` refused `Outer.Y` as local-only while `open B, A` reached the
                // real ambiguity).
                var candidates = pending.Candidates;
                for (var start = 0; start < candidates.Count;)
                {
                    var end = start;
                    while (end < candidates.Count && candidates[end].ProviderLevel == candidates[start].ProviderLevel)
                        end++;

                    var group = new OpenLevelSettlement();
                    for (var i = start; i < end; i++)
                    {
                        var provided = new HashSet<Requirement>();
                        group.Offer(Provides(candidates[i], pending, level, provided, site, boundOwners), provided);
                    }

                    if (group.Decides(names))
                        return names;
                    start = end;
                }

                for (var current = level; current is not null; current = current.Parent)
                {
                    var opens = current.PropertyScope.Opens;
                    HashSet<string>? seen = null;
                    var group = new OpenLevelSettlement();
                    for (var i = 0; i < opens.Count; i++)
                    {
                        var target = opens[i];
                        seen ??= new HashSet<string>(StringComparer.Ordinal);
                        if (!seen.Add(Evaluator.OpenTargetDedupKey(target, i)))
                            continue;

                        var provided = new HashSet<Requirement>();
                        if (target is Expr.AlgorithmExpr(var block))
                        {
                            // An inline target is wired to the prelude: nothing outside it can
                            // be referenced, so only its own requirement names survive.
                            var inlineSeed = PropertyDependencyGraphBuilder.TryChargeProvidedMember(block, pending, memos);
                            if (inlineSeed is not null)
                            {
                                provided.UnionWith(level.Root.ResolveRequirements(inlineSeed.RequiredAncestorOwnedParameterNames));
                                provided.UnionWith(site.ResolveRequirements(inlineSeed.OwnerQualifiedParameters, boundOwners));
                            }

                            group.Offer(inlineSeed is not null, provided);
                            continue;
                        }

                        group.Offer(
                            PropertyDependencyGraphBuilder.TryGetOpenTargetPath(target, out var head, out var steps)
                                && TryProvide(current, head, steps, pending, provided, site, boundOwners),
                            provided);
                    }

                    if (group.Decides(names))
                        return names;
                }

                return names;
            }
            finally
            {
                _inProgress.Remove(key);
            }
        }

        /// <summary>
        /// Whether one carried candidate provides the pending head, accumulating its charge into
        /// <paramref name="provided"/>: a resolved candidate exists only because its target
        /// provides the head, while an unresolved one is settled here, from the owning level
        /// outward (no level it escaped declared the head).
        /// </summary>
        private bool Provides(OpenCandidate candidate, PendingReference pending, SummaryScope level, HashSet<Requirement> provided, SummaryScope site, IReadOnlySet<Algorithm>? boundOwners)
            => candidate switch
            {
                ResolvedOpenCandidate resolved => Charge(provided, ResolveSeed(resolved.Seed, level, site, boundOwners)),
                UnresolvedOpenCandidate unresolved => TryProvide(level, unresolved.Head, unresolved.PublicSteps, pending, provided, site, boundOwners),
            };

        private static bool Charge(HashSet<Requirement> provided, HashSet<Requirement> requirements)
        {
            provided.UnionWith(requirements);
            return true;
        }

        /// <summary>
        /// ONE open lookup level's verdict (the evaluator's <c>LookupOpens</c>): every deduplicated
        /// target of the level is offered; the level decides the lookup as soon as any target
        /// provides the head — the sole provider's charge when exactly one does, and NOTHING when
        /// two or more do, because the evaluator then selects no declaration (ambiguousOpen).
        /// </summary>
        private sealed class OpenLevelSettlement
        {
            private int _providers;
            private HashSet<Requirement>? _charge;

            public void Offer(bool provides, HashSet<Requirement> charge)
            {
                if (!provides)
                    return;

                _providers++;
                _charge = charge;
            }

            public bool Decides(HashSet<Requirement> names)
            {
                if (_providers == 1)
                    names.UnionWith(_charge!);
                return _providers > 0;
            }
        }

        /// <summary>
        /// Whether the named <c>open</c> target declared at <paramref name="openingLevel"/>
        /// publicly provides the pending head: its head resolves through the direct chain from
        /// the opening level outward (the evaluator's <c>lookupLexicalDirect</c>), its dotted
        /// steps are public members, and the provider publicly declares the head. The charged
        /// seed — the navigated steps' and the provided member's requirements — is relative to
        /// the level that declares the target's head and is resolved from there.
        /// </summary>
        private bool TryProvide(SummaryScope openingLevel, string head, IReadOnlyList<string> steps, PendingReference pending, HashSet<Requirement> names, SummaryScope site, IReadOnlySet<Algorithm>? boundOwners)
        {
            if (!openingLevel.TryLookup(head, out var found, out var hit, out _))
                return false;

            var headNode = hit.Property.Value;
            var (providerSeed, providerNavigated) = PropertyDependencyGraphBuilder.ChargePath(
                headNode,
                PropertyDependencyGraphBuilder.PublicSteps(steps),
                memos);
            if (providerNavigated < steps.Count)
                return false;

            var provider = PropertyDependencyGraphBuilder.NavigateNode(headNode, steps);
            if (provider is null
                || PropertyDependencyGraphBuilder.TryChargeProvidedMember(provider, pending, memos) is not { } memberSeed)
                return false;

            var seed = PropertyDependencyGraphBuilder.ExpandThroughNodes(
                memberSeed,
                PropertyDependencyGraphBuilder.NodePath(headNode, steps),
                memos);
            seed.UnionWith(providerSeed);
            names.UnionWith(ResolveSeed(seed, found, site, boundOwners));
            return true;
        }

        /// <summary>The requirement names of a seed relative to <paramref name="level"/>, resolved from there outward.</summary>
        private HashSet<Requirement> ResolveSeed(PropertyDependencyGraphBuilder.SummarySeed seed, SummaryScope level, SummaryScope site, IReadOnlySet<Algorithm>? boundOwners)
        {
            var names = new HashSet<Requirement>(level.ResolveRequirements(seed.RequiredAncestorOwnedParameterNames));
            names.UnionWith(site.ResolveRequirements(seed.OwnerQualifiedParameters, boundOwners));
            foreach (var dependencyName in seed.VisiblePropertyDependencyNames)
                names.UnionWith(ResolveVisibleName(dependencyName, level, site, boundOwners));

            foreach (var pending in seed.PendingReferences)
                names.UnionWith(Resolve(pending, level, site, boundOwners));

            return names;
        }

        /// <summary>
        /// Settlement of a BARE visible name the scope-free summary walk could not reduce
        /// further: the same rule as a member-less, candidate-less pending reference — the
        /// name as a property of the level's chain first (its stored summary), and only then
        /// the level's and its ancestors' <c>open</c> providers, whose provided member charges
        /// its own requirements. A name provided by nothing (an unresolvable name, or one the
        /// prelude declares) contributes no requirement.
        /// </summary>
        public HashSet<Requirement> ResolveVisibleName(string name, SummaryScope level, SummaryScope? site = null,
            IReadOnlySet<Algorithm>? boundOwners = null)
        {
            if (level.TryLookup(name, out _, out _, out var summary))
                return [.. summary.Requirements];

            return Resolve(new PendingReference(name, [], []), level, site, boundOwners);
        }
    }

    private static Algorithm ProcessConditionalAlgorithm(
        Algorithm.Conditional algorithm,
        ExposureWalkMemos memos)
    {
        // Family-owned opens exist in host trees only (parsed families own none; the branch
        // bodies own theirs). They are a lookup level of their own for the branch bodies, and
        // they are rewritten like any open list: an open target's nested algorithms classify
        // under the one rule exactly like every other body.
        var rewrittenOpens = RewriteExprList(
            algorithm.Opens,
            new ExposureWalkMemos(memos.SummaryMemo, memos.Observations, memos.Scope.Root, memos.Run));

        var rewrittenBranches = new List<CondBranch>(algorithm.Branches.Count);
        foreach (var branch in algorithm.Branches)
        {
            var branchMemos = memos.ForBranch(algorithm, branch.Pattern);

            if (branch.Body.DeferredRegion is { } region)
            {
                // B2c: a deferred module region is not materialized eagerly (its provisional
                // body is never evaluated; the FAMILY's classification reads the
                // provisional body's captures through the summary channel above). This pass's
                // output view of the placeholder carries the region forked with the summary
                // chain at the branch — the tree's final region, complete with every earlier
                // context and the recorded validation bindings.
                rewrittenBranches.Add(branch with
                {
                    Body = branch.Body with
                    {
                        DeferredRegion = region.WithExposure(new DeferredBranchContext(branchMemos.Scope)),
                    },
                });
                continue;
            }

            // A branch body is processed exactly like any nested body under the one
            // classification rule (ClassifyDeclaredProperty): its pattern binders are inputs
            // only the family's call binds and arrive as Expr.Param references the body does
            // not own, so a declaration that depends on one is local-only for the same reason
            // a parameter-capturing declaration is, while a self-contained one is Exported —
            // openable, dot-accessible, and hand-out-able within the branch, and unreachable
            // by name from outside it because the family exposes no structural members.
            // Bodies are reference-deduplicated within equivalent branch regions (M4).
            // An ordinary property body or a different binder/open context has different
            // owner positions and is classified separately.
            var rewrittenBody = ProcessSharedNestedAlgorithm(branch.Body, branchMemos);

            rewrittenBranches.Add(branch with { Body = rewrittenBody });
        }

        return algorithm with
        {
            Opens = rewrittenOpens,
            Branches = rewrittenBranches,
        };
    }

    /// <summary>
    /// The exposure context of one deferred module region (B2c): the final summary chain the
    /// eager walk held at the branch, so the demand-time run classifies the resolved body
    /// under the same ancestor facts.
    /// </summary>
    internal sealed record DeferredBranchContext(SummaryScope Scope);

    /// <summary>
    /// Demand-time exposure classification of a deferred region's RESOLVED body — the
    /// ordinary body walk under the ONE rule (<see cref="ClassifyDeclaredProperty"/>).
    /// </summary>
    internal static Algorithm ElaborateDeferredBranch(
        Algorithm resolvedBody,
        DeferredBranchContext context,
        FrontEndTraversalObservations? observations = null)
        => ResolveInScope(resolvedBody, context.Scope, observations);

    /// <summary>
    /// A call's argument bundle may be shared by several call edges — implicit lifting gives every
    /// lifted reference to one callable in a resolver region the same synthesized bundle (FE-2) —
    /// so it rewrites once per region and stays shared, exactly like a shared expression node:
    /// copying it per edge would rebuild the K × L representation the sharing removed.
    /// </summary>
    private static OutputBundle RewriteArgumentBundle(OutputBundle arguments, ExposureWalkMemos memos)
    {
        // A rewrite-invariant bundle is the same bundle in every region (FE-3).
        if (memos.Run.IsRewriteInvariant(arguments))
            return arguments;

        memos.ArgumentBundles ??= new(ReferenceEqualityComparer.Instance);
        if (memos.ArgumentBundles.TryGetValue(arguments, out var rewritten))
            return rewritten;

        memos.Observations?.RecordExposureArgumentBundleRewrite();
        rewritten = OutputBundle.From(RewriteExprList(arguments, memos));
        memos.ArgumentBundles[arguments] = rewritten;
        return rewritten;
    }

    private static List<Expr> RewriteExprList(IReadOnlyList<Expr> expressions, ExposureWalkMemos memos)
    {
        var rewritten = new List<Expr>(expressions.Count);
        foreach (var expression in expressions)
            rewritten.Add(RewriteExpr(expression, memos));

        return rewritten;
    }

    // Expression descent exists to reach nested algorithms — block literals and
    // call/dot-call argument bundles — so their properties receive exposure
    // classifications too. Outside those nested algorithm replacements, each
    // expression keeps the same shape and metadata.
    private static Expr RewriteExpr(Expr expr, ExposureWalkMemos memos)
    {
        // DAG-safety: one rewrite per shared node reference per region; the memo returns
        // the same rewritten node for every later reach, preserving the input's sharing.
        if (!AstTraversalDagSafety.HasTraversableExprChildren(expr))
            return RewriteExprCore(expr, memos);

        // A rewrite-invariant subtree is returned as it is: its copy would be content-identical,
        // and returning it keeps a shared subtree shared across regions (FE-3).
        if (memos.Run.IsRewriteInvariant(expr))
            return expr;

        memos.Rewrites ??= new(ReferenceEqualityComparer.Instance);
        if (memos.Rewrites.TryGetValue(expr, out var rewritten))
            return rewritten;

        memos.Observations?.RecordExposureRewriteExpansion();
        rewritten = RewriteExprCore(expr, memos);
        memos.Rewrites[expr] = rewritten;
        return rewritten;
    }

    private static Expr RewriteExprCore(Expr expr, ExposureWalkMemos memos)
    {
        return expr switch
        {
            // Defensive only — parameter detection strips every grace
            // before exposure resolution runs; `with` keeps the stored
            // grace facts for host-built trees.
            Expr.Grace grace => grace with { Inner = RewriteExpr(grace.Inner, memos) },

            Expr.Unary unary => unary with { Operand = RewriteExpr(unary.Operand, memos) },

            Expr.Binary binary => binary with
            {
                Left = RewriteExpr(binary.Left, memos),
                Right = RewriteExpr(binary.Right, memos),
            },

            Expr.Comparison comparison => comparison with
            {
                First = RewriteExpr(comparison.First, memos),
                Links = AstHelpers.RewriteComparisonLinks(comparison.Links, operand => RewriteExpr(operand, memos)),
            },

            Expr.Index index => index with
            {
                Target = RewriteExpr(index.Target, memos),
                Selector = RewriteExpr(index.Selector, memos),
            },

            Expr.SequenceSpread spread => spread with { Operand = RewriteExpr(spread.Operand, memos) },

            Expr.SequenceConstruct construct => construct with
            {
                Left = RewriteExpr(construct.Left, memos),
                Right = RewriteExpr(construct.Right, memos),
            },

            Expr.ListLiteral list => list with { Items = RewriteExprList(list.Items, memos) },

            Expr.AlgorithmExpr block => block with { Algorithm = ProcessSharedNestedAlgorithm(block.Algorithm, memos) },

            // A capture owns no names and no properties, so its rows rewrite
            // with the same visible summaries — the exact effect the
            // pre-split transparent wrapper had through ProcessAlgorithm.
            Expr.Capture capture => capture with { Body = RewriteExprList(capture.Body, memos) },

            // Argument bundles own no scope: slots rewrite in the enclosing
            // context, exactly like capture rows.
            Expr.Call call => call with
            {
                Function = RewriteExpr(call.Function, memos),
                Args = RewriteArgumentBundle(call.Args, memos),
            },

            Expr.DotCall dotCall => RewriteDotCall(dotCall, memos),

            // Intentional leaves: no nested algorithm to reach, so the
            // expression keeps its exact shape and metadata.
            Expr.Resolve or Expr.Param or Expr.Num or Expr.StringLiteral or Expr.BoolLiteral
                or Expr.EmptySequence or Expr.NativeCall => expr,
        };
    }

    private static Expr RewriteDotCall(Expr.DotCall dotCall, ExposureWalkMemos memos)
    {
        // Diagnostic claims are finalized after the whole pass by the provenance
        // finalizer, against the classified tree.
        memos.Run.HasDotMemberOrigins |= dotCall.InferredFallbackProvenance is not null;

        var rewrittenTarget = RewriteExpr(dotCall.Target, memos);
        var rewrittenArgs = dotCall.Args is { } args ? RewriteArgumentBundle(args, memos) : null;

        // `with` keeps the stored dot-edge facts (member span, lexical fallback, the
        // detector's elaborated fallback selection) intact: exposure never changes
        // what a receiver resolves to, so the detector's verdict is final.
        return dotCall with
        {
            Target = rewrittenTarget,
            Args = rewrittenArgs,
        };
    }

    private static bool SummariesEqual(
        IReadOnlyDictionary<string, AnalysisSummary> left,
        IReadOnlyDictionary<string, AnalysisSummary> right)
    {
        if (left.Count != right.Count)
            return false;

        foreach (var (name, leftSummary) in left)
        {
            if (!right.TryGetValue(name, out var rightSummary) || !leftSummary.SetEquals(rightSummary))
                return false;
        }

        return true;
    }
}
