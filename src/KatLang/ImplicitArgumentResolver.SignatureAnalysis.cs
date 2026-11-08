namespace KatLang;

internal static partial class ImplicitArgumentResolver
{
    // ═══ The static callable identity (B3-5★) ══════════════════════════════════════════════════════════════════════

    /// <summary>
    /// What a written reference denotes after every static reference row is followed (B3-5★): the endpoint's written
    /// declaration (<see cref="Key"/> its context; null for a prelude or registry member, which is final), its body as
    /// written, and the name diagnostics give it (the last written hop through a reference, else the reference itself).
    /// </summary>
    private readonly record struct StaticCallable(StaticScopeKey? Key, Algorithm Written, string DisplayName, bool IsRegistry)
    {
        /// <summary>The identity formula lifting deduplicates callees by: one per endpoint, whatever route reached it.</summary>
        public object Identity => IsRegistry ? Written : Key!;
    }

    /// <summary>
    /// THE STATIC CALLABLE IDENTITY of a written reference (B3-5★): the declaration a name selects (the owner walk over
    /// the document's properties, then the prelude, then the opens) or an argumentless structural member path selects,
    /// followed through every reference row to Q3's invocation endpoint (a transparent reference's or a carrier's target,
    /// an <c>.Algorithm</c> link body, a runtime row's body). It reads only the resolution's INPUT — never a processed
    /// body, never a demand — so the analysis phase and the rewrite phase resolve every reference to the SAME callee by
    /// construction, whatever order bodies are processed in. Null for a reference with no static identity: a parameter,
    /// an unresolved or ambiguous name, a member only a runtime receiver provides.
    /// </summary>
    private static StaticCallable? ResolveStaticCallable(Expr reference, SignatureMap paramMap, ResolverWalkMemos memos, out string writtenName)
    {
        var run = memos.Run;
        StaticDeclaration? declared;
        switch (reference)
        {
            case Expr.Resolve(var name):
                writtenName = name;
                if (paramMap.TryGetValue(name, out var entry))
                {
                    declared = EntryDeclaration(entry, raw: true);
                    break;
                }

                if (run.Prelude.TryGetMember(name, out var preludeMember))
                    return new StaticCallable(null, preludeMember.Value, name, IsRegistry: true);
                declared = StaticOpenedDeclaration(name, run.Level);
                break;

            case Expr.DotCall { Args: null } edge when EdgeKindOf(edge, paramMap, memos) == DotEdgeKind.StructuralMember:
                writtenName = DottedDisplayName(edge);
                declared = StructuralMemberAt(edge, run.Level, StaticCycleCheck.Formation);
                break;

            default:
                writtenName = "";
                return null;
        }

        if (declared is not { } start)
            return null;
        var (end, through) = StaticInvocationTarget(start, run);
        var display = through ?? writtenName;
        if (run.Prelude.IsFinalRegistryAlgorithm(end.Target) || end.Target is Algorithm.Builtin)
            return new StaticCallable(null, end.Target, display, IsRegistry: true);
        var operation = run.StructuralOperation!;
        var key = operation.ContextOf(end.Level?.StaticContext?.Key ?? operation.Queries.Keys.Root, end.Target);
        return new StaticCallable(key, operation.SourceOf(key), display, IsRegistry: false);
    }

    /// <summary>
    /// The KIND of the callee a call or dot edge names (never a signature), read statically like its identity
    /// (<see cref="ResolveStaticCallable"/>): an alias's kind is its endpoint's, so a call through it takes the target's
    /// argument roles (X-45). A written block is a user callee; a callee with no static identity is dynamic.
    /// </summary>
    private static LiftingCallee StaticCalleeKindOf(Expr callee, SignatureMap paramMap, ResolverWalkMemos memos)
    {
        callee = callee.UnwrapGraceOperand();
        if (callee is Expr.AlgorithmExpr)
            return LiftingCallee.User;
        return ResolveStaticCallable(callee, paramMap, memos, out _) is { } resolved
            ? LiftingCallee.OfAlgorithm(resolved.Written, memos.Run.Prelude.IsStrictValue(resolved.Written))
            : LiftingCallee.Dynamic;
    }

    // ═══ The formula-lifting role walk (one implementation, two instantiations) ═════════════════════════════════════

    /// <summary>
    /// What one instantiation of <see cref="WalkLiftingRoles{TSink}"/> does at the walk's decision points: whether a node is
    /// visited (its memo), what a value-role reference contributes, and how a callee and a dot edge are classified.
    /// </summary>
    private interface ILiftingWalkSink
    {
        bool Enter(Expr expr, LiftingRole role, StaticScopeKey? guard);

        void Exit(Expr expr, LiftingRole role, StaticScopeKey? guard);

        void Reference(Expr reference, StaticScopeKey? guard);

        LiftingCallee CalleeKind(Expr callee);

        /// <summary>
        /// The edge's route. When an <c>.Algorithm</c> link's class decides it (analysis only), <paramref name="link"/> is
        /// that link and the result is the route a calculation link gives (MUST), <paramref name="mayKind"/> the route a
        /// runtime reference gives (MAY).
        /// </summary>
        DotEdgeKind EdgeKind(Expr.DotCall edge, out DotEdgeKind mayKind, out StaticScopeKey? link);

        LiftingCallee DotEdgeCallee(Expr.DotCall edge, DotEdgeKind kind);
    }

    /// <summary>
    /// THE FORMULA-LIFTING ROLE WALK: every expression variant hands each child the role of the child's own consumer
    /// (<see cref="FormulaLiftingRoles"/>); only a bare name, an argumentless structural member path and a Grace marker
    /// consume the role they receive. A GUARD rides with a value role into exactly those consumers: a slot whose role a
    /// link's class decides (a value under a calculation link, callable under a runtime reference) is a value read only
    /// when its link is a calculation. Every other node resets the guard — its children's roles are their consumers' own
    /// under either class. Dependency collection and Q8 equation recording are its two instantiations, so role
    /// propagation is written once.
    /// </summary>
    private static void WalkLiftingRoles<TSink>(Expr expr, LiftingRole role, StaticScopeKey? guard, ref TSink sink)
        where TSink : struct, ILiftingWalkSink
    {
        if (!sink.Enter(expr, role, guard))
            return;

        switch (expr)
        {
            case Expr.Resolve:
                if (role == LiftingRole.Value)
                    sink.Reference(expr, guard);
                break;

            case Expr.Call(var function, var callArgs):
            {
                WalkLiftingRoles(function, LiftingRole.Callable, null, ref sink);
                var roles = FormulaLiftingRoles.ArgumentRoles(sink.CalleeKind(function), callArgs);
                for (var i = 0; i < callArgs.Count; i++)
                    WalkLiftingRoles(callArgs[i], roles[i], null, ref sink);
                break;
            }

            case Expr.Binary(_, var left, var right):
                WalkLiftingRoles(left, LiftingRole.Value, null, ref sink);
                WalkLiftingRoles(right, LiftingRole.Value, null, ref sink);
                break;

            case Expr.Comparison(var first, var links):
                WalkLiftingRoles(first, LiftingRole.Value, null, ref sink);
                foreach (var link in links)
                    WalkLiftingRoles(link.Operand, LiftingRole.Value, null, ref sink);
                break;

            case Expr.Unary(_, var operand):
                WalkLiftingRoles(operand, LiftingRole.Value, null, ref sink);
                break;

            case Expr.Index(var target, var selectors):
                // The receiver and EVERY selector slot are VALUE uses (a spread slot's operand through its own arm). A
                // selection has no callee, so its slots are never classified by a callee's argument roles.
                WalkLiftingRoles(target, LiftingRole.Value, null, ref sink);
                foreach (var selector in selectors)
                    WalkLiftingRoles(selector, LiftingRole.Value, null, ref sink);
                break;

            case Expr.SequenceSpread(var operand):
                WalkLiftingRoles(operand, LiftingRole.Value, null, ref sink);
                break;

            case Expr.SequenceConstruct(var left, var right):
                WalkLiftingRoles(left, LiftingRole.Value, null, ref sink);
                WalkLiftingRoles(right, LiftingRole.Value, null, ref sink);
                break;

            case Expr.ListLiteral(var listItems):
                foreach (var item in listItems)
                    WalkLiftingRoles(item, LiftingRole.Value, null, ref sink);
                break;

            case Expr.Capture(var rows):
                // A capture element is a value: a capture has no algorithm identity to transport.
                foreach (var row in rows)
                    WalkLiftingRoles(row, LiftingRole.Value, null, ref sink);
                break;

            case Expr.InterpolatedString(_, var interpolationLinks):
                // An interpolation hole is a VALUE use of the enclosing owner (VAL-12).
                foreach (var link in interpolationLinks)
                    WalkLiftingRoles(link.Hole, LiftingRole.Value, null, ref sink);
                break;

            case Expr.DotCall dotCall:
            {
                var kind = sink.EdgeKind(dotCall, out var mayKind, out var decidingLink);
                if (dotCall.Args is null && kind == DotEdgeKind.StructuralMember)
                {
                    // A dotted callable reference: the edge itself lifts in a value role; its receiver is navigated.
                    if (role == LiftingRole.Value)
                        sink.Reference(dotCall, guard);
                    WalkLiftingRoles(dotCall.Target, LiftingRole.Callable, null, ref sink);
                    break;
                }

                var callee = sink.DotEdgeCallee(dotCall, kind);
                var receiverRole = FormulaLiftingRoles.ReceiverRole(kind, callee);
                var argumentRoles = dotCall.Args is null ? null : FormulaLiftingRoles.DotArgumentRoles(dotCall, kind, callee);
                if (decidingLink is null)
                {
                    WalkLiftingRoles(dotCall.Target, receiverRole, null, ref sink);
                    if (dotCall.Args is { } dotArgs)
                    {
                        for (var i = 0; i < dotArgs.Count; i++)
                            WalkLiftingRoles(dotArgs[i], argumentRoles![i], null, ref sink);
                    }

                    break;
                }

                // A link decides the route: a slot is a value read under a calculation link exactly where the two routes'
                // roles differ (a runtime reference's route classifies nothing as a value).
                var mayCallee = sink.DotEdgeCallee(dotCall, mayKind);
                var mayReceiverRole = FormulaLiftingRoles.ReceiverRole(mayKind, mayCallee);
                WalkGuardedSlot(dotCall.Target, receiverRole, mayReceiverRole, decidingLink, ref sink);
                if (dotCall.Args is { } guardedArgs)
                {
                    var mayArgumentRoles = FormulaLiftingRoles.DotArgumentRoles(dotCall, mayKind, mayCallee);
                    for (var i = 0; i < guardedArgs.Count; i++)
                        WalkGuardedSlot(guardedArgs[i], argumentRoles![i], mayArgumentRoles[i], decidingLink, ref sink);
                }

                break;
            }

            case Expr.Grace(var inner, _):
                WalkLiftingRoles(inner, role, guard, ref sink);
                break;

            case Expr.AlgorithmExpr:
                // A scoped block is its own inferring level: its references lift into ITS signature.
                break;

            // Intentional leaves: no bare callable references to lift.
            case Expr.Num:
            case Expr.Param:
            case Expr.StringLiteral:
            case Expr.BoolLiteral:
            case Expr.EmptySequence:
            case Expr.NativeCall:
                break;

            // Runtime exhaustiveness guard (statement-form walk, which the closed Expr hierarchy cannot make
            // compiler-exhaustive — see AstWalker.VisitExpr): a new Expr variant must be classified above rather than
            // silently contributing no implicit dependencies.
            default:
                throw new InvalidOperationException(
                    $"Unhandled Expr variant in {nameof(ImplicitArgumentResolver)}.{nameof(WalkLiftingRoles)}: {expr.GetType().Name}. " +
                    "Classify the new variant explicitly as a walked case or an intentional leaf.");
        }

        sink.Exit(expr, role, guard);
    }

    private static void WalkGuardedSlot<TSink>(Expr slot, LiftingRole calculationRole, LiftingRole runtimeRole, StaticScopeKey link, ref TSink sink)
        where TSink : struct, ILiftingWalkSink
    {
        if (calculationRole == runtimeRole)
        {
            WalkLiftingRoles(slot, calculationRole, null, ref sink);
            return;
        }

        if (calculationRole != LiftingRole.Value)
            throw new InvalidOperationException("A runtime receiver classified a slot as a value that a calculation receiver does not.");
        WalkLiftingRoles(slot, LiftingRole.Value, link, ref sink);
    }

    // ═══ The analysis phase ════════════════════════════════════════════════════════════════════════════════════════

    /// <summary>
    /// B3-5★ ANALYSIS PHASE: the resolver's own traversal, run once per resolution BEFORE any rewrite, recording the Q8
    /// equation of every body in its declaring context (D1a: one per written body per context) — its own patterns, the
    /// enclosing parameter bindings its forwarding reuses (Q-04), and the ordered value-role references of its written
    /// rows with the link that guards each. It builds the rewrite's levels, maps, open providers, forwarding sets and root
    /// filter by the same functions, walks rows with the same role walk, and resolves references by the same static
    /// identity; it keeps its OWN memo and writes nothing the rewrite reads — no region, module unit, publication, target
    /// cell, processed body, deferred check or diagnostic.
    /// </summary>
    private sealed class SignatureAnalysis
    {
        /// <summary>One analyzed body: its context and the inputs of its equation.</summary>
        internal sealed class Body
        {
            public required int Index { get; init; }
            public required StaticScopeKey Key { get; init; }
            public required Algorithm.User Written { get; init; }
            public required ForwardableParameters Forwardable { get; init; }

            /// <summary>Written list or clause branch: its signature is final as written; it has no equation.</summary>
            public required bool IsClosed { get; init; }

            public required bool IsRoot { get; init; }

            /// <summary>An unbraced lone <c>.Algorithm</c> row (META-S3-1): a calculation exactly when its signature is nonempty.</summary>
            public required bool IsLink { get; init; }

            /// <summary>
            /// The name the body is defined under (its property's; <c>&lt;anonymous&gt;</c> for a block, a module or a branch
            /// body, <c>&lt;root&gt;</c> for the program), its declaration's span, and the import site the walk was inside —
            /// recorded once, so neither composition nor reporting scans a declaring level again.
            /// </summary>
            public required string Name { get; init; }

            public required SourceSpan? Span { get; init; }

            public required SourceSpan? ImportSite { get; init; }

            /// <summary>The ordered value-role occurrences: endpoint, the link that guards it, the reference.</summary>
            public List<(StaticCallable Endpoint, StaticScopeKey? Guard, Expr Reference, string DisplayName)> Occurrences { get; } = [];
        }

        internal readonly Dictionary<StaticScopeKey, Body> Bodies = new(ReferenceEqualityComparer.Instance);
        internal readonly List<Body> Order = [];
        internal readonly HashSet<Algorithm> Modules = new(ReferenceEqualityComparer.Instance);

        /// <summary>The first context each analysis region was analyzed in (<see cref="AnalysisRegionKey"/>).</summary>
        internal readonly Dictionary<AnalysisRegionKey, StaticScopeKey> Regions = [];

        internal SignatureKeyAliases? Aliases;
    }

    /// <summary>
    /// The ANALYSIS REGION of one nested body (DAG safety, B3-5★): the node by reference; the declaration each of its free
    /// reference names sees in the analysis map (the entry by reference — one per declaring level and property, so two
    /// reaches see the same object exactly when they see the same declaration); the enclosing parameter bindings its
    /// forwarding may reuse (Q-04); a branch body's closed binder specification; and the open chain a free name reaches.
    /// It refines the rewrite's <see cref="AlgorithmRegionKey"/> component by component — the same declarations have the
    /// same selected signatures — so a reach the analysis serves from an earlier one is one the rewrite serves from the
    /// same earlier one, and the analysis, like the rewrite, costs one walk per distinct region, never one per path.
    /// </summary>
    private sealed class AnalysisRegionKey(Algorithm node, VisibleProperty?[] visible, CanonicalNameSet forwardableNames,
        CanonicalNameSet forwardableCollectingNames, int? closedSpecification, OpenLevel? opens) : IEquatable<AnalysisRegionKey>
    {
        private readonly int _hash = ComputeHash(node, visible, forwardableNames, forwardableCollectingNames, closedSpecification, opens);

        public bool Equals(AnalysisRegionKey? other)
        {
            if (other is null || _hash != other._hash || !ReferenceEquals(node, other.Node) || !ReferenceEquals(opens, other.Opens)
                || closedSpecification != other.ClosedSpecification || !forwardableNames.Equals(other.ForwardableNames)
                || !forwardableCollectingNames.Equals(other.ForwardableCollectingNames) || visible.Length != other.Visible.Length)
                return false;
            for (var i = 0; i < visible.Length; i++)
            {
                if (!ReferenceEquals(visible[i], other.Visible[i]))
                    return false;
            }

            return true;
        }

        public override bool Equals(object? obj) => Equals(obj as AnalysisRegionKey);

        public override int GetHashCode() => _hash;

        private Algorithm Node => node;
        private VisibleProperty?[] Visible => visible;
        private CanonicalNameSet ForwardableNames => forwardableNames;
        private CanonicalNameSet ForwardableCollectingNames => forwardableCollectingNames;
        private int? ClosedSpecification => closedSpecification;
        private OpenLevel? Opens => opens;

        private static int ComputeHash(Algorithm node, VisibleProperty?[] visible, CanonicalNameSet forwardableNames,
            CanonicalNameSet forwardableCollectingNames, int? closedSpecification, OpenLevel? opens)
        {
            var hash = new HashCode();
            hash.Add(System.Runtime.CompilerServices.RuntimeHelpers.GetHashCode(node));
            foreach (var entry in visible)
                hash.Add(entry is null ? 0 : System.Runtime.CompilerServices.RuntimeHelpers.GetHashCode(entry));
            hash.Add(forwardableNames.GetHashCode());
            hash.Add(forwardableCollectingNames.GetHashCode());
            hash.Add(closedSpecification);
            hash.Add(opens is null ? 0 : System.Runtime.CompilerServices.RuntimeHelpers.GetHashCode(opens));
            return hash.ToHashCode();
        }
    }

    /// <summary>
    /// The analysis's REGION ALIASES (B3-5★): a body reached again in an analysis region already analyzed is not analyzed
    /// again; its context — and every context below it — reads the context it shares a region with. Isomorphic regions
    /// select isomorphic facts (G6 is unique), so a key read through its alias reads the fact its own analysis would give.
    /// </summary>
    internal sealed class SignatureKeyAliases(StaticStructureOperation operation)
    {
        private readonly Dictionary<StaticScopeKey, StaticScopeKey> _aliases = new(ReferenceEqualityComparer.Instance);
        private readonly Dictionary<StaticScopeKey, StaticScopeKey> _resolved = new(ReferenceEqualityComparer.Instance);

        public void Add(StaticScopeKey reach, StaticScopeKey analyzed) => _aliases[reach] = analyzed;

        public bool IsAliased(StaticScopeKey key) => _aliases.ContainsKey(key);

        /// <summary>
        /// The analyzed context <paramref name="key"/> reads: itself, unless it or an ancestor is an alias, in which case the
        /// same path below the alias's target (iteratively: a target's own nested body may be an alias in turn — always one
        /// nested deeper, so it ends). A path the target region never declared reads itself.
        /// </summary>
        public StaticScopeKey Resolve(StaticScopeKey key)
        {
            if (_aliases.Count == 0)
                return key;
            if (_resolved.TryGetValue(key, out var known))
                return known;
            var current = key;
            while (Step(current) is { } next)
                current = next;
            _resolved.Add(key, current);
            return current;
        }

        private StaticScopeKey? Step(StaticScopeKey key)
        {
            var path = new Stack<StaticScopeKey>();
            for (StaticScopeKey? at = key; at is not null; at = at.Parent)
            {
                if (_aliases.TryGetValue(at, out var mapped))
                {
                    while (path.TryPop(out var child))
                    {
                        if (operation.Queries.Keys.KnownDefinitionIn(mapped, operation.SourceOf(child), child.BindingRegion) is not { } next)
                            return null;
                        mapped = next;
                    }

                    return mapped;
                }

                path.Push(at);
            }

            return null;
        }
    }

    /// <summary>The analysis memo of one row region: visited nodes per (role, guard), and the occurrences already recorded.</summary>
    private sealed class EquationWalkMemo
    {
        public readonly Dictionary<(LiftingRole, StaticScopeKey?), HashSet<Expr>> Visited = [];
        public readonly HashSet<(object, StaticScopeKey?)> Recorded = [];
        public readonly HashSet<object> RecordedUnguarded = new(ReferenceEqualityComparer.Instance);
    }

    /// <summary>The analysis instantiation of the role walk: records occurrences; classifies callees and edges statically.</summary>
    private readonly struct EquationSink(SignatureMap paramMap, ResolverWalkMemos memos, SignatureAnalysis.Body body, EquationWalkMemo memo)
        : ILiftingWalkSink
    {
        public bool Enter(Expr expr, LiftingRole role, StaticScopeKey? guard)
        {
            if (!AstTraversalDagSafety.HasTraversableExprChildren(expr))
                return true;
            if (!memo.Visited.TryGetValue((role, guard), out var visited))
                memo.Visited[(role, guard)] = visited = new(ReferenceEqualityComparer.Instance);
            if (visited.Contains(expr))
                return false;
            memos.Run.Observations?.RecordSignatureAnalysisExpansion();
            return true;
        }

        public void Exit(Expr expr, LiftingRole role, StaticScopeKey? guard)
        {
            if (AstTraversalDagSafety.HasTraversableExprChildren(expr))
                memo.Visited[(role, guard)].Add(expr);
        }

        public void Reference(Expr reference, StaticScopeKey? guard)
        {
            memos.Run.StructuralOperation!.Queries.Resources.Work(1, memos.Run.CancellationToken);
            if (ResolveStaticCallable(reference, paramMap, memos, out var writtenName) is not { } callee)
                return;
            // An occurrence after an unguarded one of the same callee, or after one under the same guard, can never be
            // the first ACTIVE occurrence: it adds nothing to the equation.
            var identity = callee.Identity;
            if (memo.RecordedUnguarded.Contains(identity) || !memo.Recorded.Add((identity, guard)))
                return;
            if (guard is null)
                memo.RecordedUnguarded.Add(identity);
            body.Occurrences.Add((callee, guard, reference, writtenName));
        }

        public LiftingCallee CalleeKind(Expr callee) => StaticCalleeKindOf(callee, paramMap, memos);

        public DotEdgeKind EdgeKind(Expr.DotCall edge, out DotEdgeKind mayKind, out StaticScopeKey? link)
        {
            mayKind = default;
            link = null;
            if (edge.ElaboratedMissSelection is null)
                return EdgeKindOf(edge, paramMap, memos.Run.Prelude);
            if (edge.ElaboratedMissSelection is not LexicalFallbackSelection.Conditional)
                return FormulaLiftingRoles.EdgeKind(edge, edge.ElaboratedMissSelection.Value);
            var run = memos.Run;
            var receiver = ReadReceiver(edge.Target, run.Level, paramMap, run, selectedLinks: false);
            if (receiver.Kind == ReceiverReadingKind.Link)
            {
                if (!CertainMissDecidesALift(edge, paramMap, run))
                    return FormulaLiftingRoles.EdgeKind(edge, LexicalFallbackSelection.Conditional);
                link = LinkKey(receiver.Link, run);
                mayKind = FormulaLiftingRoles.EdgeKind(edge, LexicalFallbackSelection.Conditional);
                return FormulaLiftingRoles.EdgeKind(edge, LexicalFallbackSelection.Always);
            }

            return FormulaLiftingRoles.EdgeKind(edge,
                receiver.Lacks(edge.Name, run) ? LexicalFallbackSelection.Always : LexicalFallbackSelection.Conditional);
        }

        public LiftingCallee DotEdgeCallee(Expr.DotCall edge, DotEdgeKind kind)
            => kind switch
            {
                DotEdgeKind.StructuralMember => StaticCalleeKindOf(edge with { Args = null }, paramMap, memos),
                DotEdgeKind.Fallback => StaticCalleeKindOf(edge.EffectiveLexicalFallback, paramMap, memos),
                _ => LiftingCallee.Dynamic,
            };
    }

    /// <summary>The context of the link body a receiver reading found (<see cref="ReceiverReadingKind.Link"/>).</summary>
    private static StaticScopeKey LinkKey(StaticDeclaration link, ResolutionRun run)
    {
        var operation = run.StructuralOperation!;
        return operation.ContextOf(link.Level?.StaticContext?.Key ?? operation.Queries.Keys.Root, link.Target);
    }

    // ═══ Selection: equations → facts ══════════════════════════════════════════════════════════════════════════════

    /// <summary>
    /// The selected Q8 facts of one resolution (B3-5★): every open body's final signature, by its context, and the bodies
    /// refused (each with its category). Immutable once built; the rewrite reads nothing else for a document signature.
    /// </summary>
    /// <summary>A body a refused group is reported at: its recorded name, declaration span and import site.</summary>
    internal sealed record RefusedBody(string Name, SourceSpan? Span, SourceSpan? ImportSite);

    internal sealed class SelectedSignatures
    {
        private readonly Dictionary<StaticScopeKey, SignatureFact> _facts;
        private readonly SignatureKeyAliases _aliases;

        internal SelectedSignatures(
            Dictionary<StaticScopeKey, SignatureFact> facts,
            IReadOnlyList<(IReadOnlyList<RefusedBody> Bodies, IReadOnlyList<string> Links, SignatureSelectionOutcome Outcome)> refusals,
            SignatureKeyAliases aliases)
        {
            _facts = facts;
            Refusals = refusals;
            _aliases = aliases;
        }

        private readonly Dictionary<(StaticScopeKey Key, string Name), CallableSignature> _signatures = [];

        /// <summary>The selected fact of the open body in context <paramref name="key"/>, read through the analysis's region aliases.</summary>
        internal bool TryGetFact(StaticScopeKey key, [System.Diagnostics.CodeAnalysis.MaybeNullWhen(false)] out SignatureFact fact)
            => _facts.TryGetValue(_aliases.Resolve(key), out fact);

        /// <summary>
        /// The selected signature of the open body in context <paramref name="key"/>, displayed as <paramref name="name"/>: ONE
        /// object per body and name, so every reference to the body reads the same pattern list (the region's identity-keyed
        /// forwarding verdicts depend on it).
        /// </summary>
        internal CallableSignature? SignatureOf(StaticScopeKey key, string name)
        {
            var resolved = _aliases.Resolve(key);
            if (!_facts.TryGetValue(resolved, out var fact))
                return null;
            // The fact's own signature under this name: one pattern list, the very one the selection composed with.
            if (!_signatures.TryGetValue((resolved, name), out var signature))
                _signatures.Add((resolved, name), signature = fact.Signature.WithName(name));
            return signature;
        }

        /// <summary>
        /// The refused groups, each reported at its bodies with the names of the <c>.Algorithm</c> links it could not classify
        /// (none for a cycle that does not settle); empty when selection succeeded.
        /// </summary>
        internal IReadOnlyList<(IReadOnlyList<RefusedBody> Bodies, IReadOnlyList<string> Links, SignatureSelectionOutcome Outcome)> Refusals { get; }

        internal bool Succeeded => Refusals.Count == 0;

        /// <summary>
        /// Every body the analysis recorded, open and closed, in analysis order (a body the analysis served from another
        /// context's analysis is not recorded): what the reach invariant checks (<see cref="RequireEveryAnalyzedBodyRewritten"/>).
        /// </summary>
        internal IReadOnlyList<AnalyzedBody> Analyzed { get; init; } = [];
    }

    /// <summary>A body the signature analysis recorded: its context, and its name and location for an internal-defect report.</summary>
    internal sealed record AnalyzedBody(StaticScopeKey Key, string Name, SourceSpan? Span, SourceSpan? ImportSite, Algorithm.User Written)
    {
        /// <summary>
        /// Where the body is written, computed only for a report: its declaration, else the import site the walk was inside,
        /// else (an anonymous block) its first written declaration or row.
        /// </summary>
        internal SourceSpan? Location
            => Span ?? ImportSite
                ?? Written.Properties.Select(static property => property.FirstDeclarationSpan).FirstOrDefault(static span => span is not null)
                ?? Written.Output.Select(static row => row.Span).FirstOrDefault(static span => span is not null);
    }

    /// <summary>
    /// THE REACH INVARIANT (S-10), the mirror of <see cref="RequireSelectedComposition"/>: every body the selection analyzed
    /// has a resolved view when the resolution completes — the rewrite processed it in that context, or served it from the
    /// processing of another (<see cref="StaticStructureOperation.AliasResolvedRegion"/>, which
    /// <see cref="StaticStructureOperation.ResolvedView"/> follows) — so no written body escapes elaboration and no selected
    /// signature goes unused. A miss means the analysis and the rewrite walked different bodies — an internal defect of this
    /// pass, never a program's error — so it fails loudly instead of letting the evaluator run an unelaborated body. Not
    /// checked after a refused selection, which rewrites nothing.
    /// </summary>
    private static void RequireEveryAnalyzedBodyRewritten(ResolutionRun run)
    {
        if (run.Selected is not { Succeeded: true } selected || run.StructuralOperation is not { } operation)
            return;
        foreach (var body in selected.Analyzed)
        {
            operation.Queries.Resources.Work(cancellationToken: run.CancellationToken);
            if (operation.ResolvedView(body.Key) is null)
                throw new InvalidOperationException(
                    $"Implicit-argument resolution analyzed the body '{body.Name}'"
                    + (body.Location is { } location ? $" at {location.Start}" : "")
                    + " but never rewrote it: the analysis and the rewrite walked different bodies.");
        }
    }

    /// <summary>
    /// The B3-5★ selection of one resolution: the analysis phase over <paramref name="root"/> (in the context the rewrite will
    /// process it in), then every equation's fact by rule G6 (<see cref="SignatureSelector"/>). Charged to the operation's
    /// ledger; a refusal publishes nothing.
    /// </summary>
    private static SelectedSignatures SelectSignatures(
        Algorithm root,
        SignatureMap rootMap,
        ForwardableParameters forwardable,
        bool isRoot,
        ConditionalBranchContext? branchContext,
        ResolutionRun run)
    {
        var operation = run.StructuralOperation!;
        var aliases = new SignatureKeyAliases(operation);
        var analysis = run.Analysis = new SignatureAnalysis { Aliases = aliases };
        try
        {
            if (isRoot && root is Algorithm.User rootUser)
                AnalyzeUserAlgorithm(rootUser, rootMap, forwardable, isRoot: true, branchContext, run);
            else
                AnalyzeAlgorithm(root, rootMap, forwardable, isRoot, branchContext, run);
        }
        finally
        {
            run.Analysis = null;
        }

        var equations = analysis.Order.Where(static body => !body.IsClosed).ToArray();
        var equationIndex = new Dictionary<StaticScopeKey, int>(equations.Length, ReferenceEqualityComparer.Instance);
        for (var i = 0; i < equations.Length; i++)
            equationIndex.Add(equations[i].Key, i);

        var references = new IReadOnlyList<SignatureEquationReference>[equations.Length];
        var isLink = new bool[equations.Length];
        for (var i = 0; i < equations.Length; i++)
        {
            var body = equations[i];
            isLink[i] = body.IsLink;
            var list = new List<SignatureEquationReference>(body.Occurrences.Count);
            foreach (var (endpoint, guard, reference, displayName) in body.Occurrences)
            {
                var guardIndex = -1;
                if (guard is not null)
                {
                    if (equationIndex.TryGetValue(aliases.Resolve(guard), out var linkIndex))
                        guardIndex = linkIndex;
                    // A link this resolution did not analyze (an earlier operation's) has a FINAL class: a calculation keeps
                    // the read, a runtime reference drops it.
                    else if (!FinalLinkIsCalculation(guard, run))
                        continue;
                }

                if (endpoint.Key is { } key && equationIndex.TryGetValue(aliases.Resolve(key), out var targetIndex))
                {
                    list.Add(new SignatureEquationReference(targetIndex, null, endpoint.Identity, guardIndex, reference, displayName));
                    continue;
                }

                // A callee whose signature is FINAL here: a registry member, a family, a closed body, an earlier completion
                // — named, like every signature the rewrite reads, by the endpoint's display name. An unnameable family
                // contributes nothing to a signature (the rewrite reports it).
                if (FinalLiftingSignature(endpoint, endpoint.DisplayName, run).Signature is { } external)
                    list.Add(new SignatureEquationReference(-1, external, endpoint.Identity, guardIndex, reference, displayName));
            }

            references[i] = list;
        }

        SignatureFact Compose(int equation, IReadOnlyList<(int Reference, CallableSignature Signature)> lifted)
        {
            run.Observations?.RecordSignatureSelectionStep();
            var body = equations[equation];
            var dependencies = new List<LiftedDependency>(lifted.Count);
            for (var i = 0; i < lifted.Count; i++)
            {
                var reference = references[equation][lifted[i].Reference];
                dependencies.Add(new LiftedDependency(reference.DisplayName, lifted[i].Signature, reference.Reference));
            }

            var own = body.Written.ParameterPatterns;
            var lifting = LiftSignature(own, dependencies, body.Forwardable, run);
            IReadOnlyList<ParameterPattern> patterns = lifting.Patterns;
            ParameterSignatureViolation? violation = null;
            if (lifting.Lifted && ParameterPattern.FindSignatureViolation(patterns) is { } found)
            {
                // X-02: the recovered signature is the one every reader sees (the rewrite reports the violation).
                violation = found;
                patterns = run.Templates.InternFlat(ParameterPattern.KeepFirstCollectingCapturePerLevel(patterns));
            }

            var composition = new SignatureComposition(own, dependencies, body.Forwardable, violation is null ? null : lifting.Patterns);
            return new SignatureFact(patterns, violation, lifting.Lifted, composition, CallableSignature.FromInferredPatterns(body.Name, patterns));
        }

        IReadOnlyDictionary<int, SignatureFact> Seal(IReadOnlyList<int> component, IReadOnlyDictionary<int, SignatureFact> settled,
            SignatureSelector.LiftedFrom liftedFrom)
            => SealCompletion(component, settled, liftedFrom, equations, references, Compose, analysis, run);

        var closed = new SignatureFact([], null, isLifted: false, composition: null, new CallableSignature("", []));
        var selection = new SignatureSelector(references, isLink, Compose, Seal, closed,
            operation.Queries.Resources, run.CancellationToken).Solve();
        if (run.Observations?.OnSignatureSelection is { } observer)
        {
            observer(new SignatureSelectionProbe(
                [.. equations.Select((body, index) => new SignatureSelectionProbeEquation(
                    body.Name, body.Written.ParameterPatterns, [.. body.Forwardable.BoundNames], body.IsLink, references[index]))],
                selection, Compose, closed));
        }

        var facts = new Dictionary<StaticScopeKey, SignatureFact>(selection.Facts.Count, ReferenceEqualityComparer.Instance);
        foreach (var (index, fact) in selection.Facts)
            facts.Add(equations[index].Key, fact);
        var refusals = selection.Refusals
            .Select(refusal => (
                (IReadOnlyList<RefusedBody>)refusal.Equations
                    .Select(index => new RefusedBody(equations[index].Name, equations[index].Span, equations[index].ImportSite)).ToArray(),
                (IReadOnlyList<string>)refusal.Links.Select(index => equations[index].Name).Distinct(StringComparer.Ordinal).ToArray(),
                refusal.Outcome))
            .ToArray();
        if (refusals.Length != 0)
            return new SelectedSignatures(facts, refusals, aliases);

        // A record (including two optional value-type spans) and its array slot need two 64-byte ledger slots per body,
        // plus one for the array header. Charge construction work here; the reach walk charges its own work separately.
        operation.Queries.Resources.Metadata(2L * analysis.Order.Count + 1, work: analysis.Order.Count, cancellationToken: run.CancellationToken);
        return new SelectedSignatures(facts, refusals, aliases)
        {
            Analyzed = [.. analysis.Order.Select(static body => new AnalyzedBody(body.Key, body.Name, body.Span, body.ImportSite, body.Written))],
        };
    }

    /// <summary>
    /// Reports every refused group (B3-5★): one <see cref="DiagnosticCode.SelfDependentInferredParameters"/> per body the
    /// group was refused at, at its definition, worded by the group's category. A body that failed only because it reads
    /// a refused group is not reported again (A1's precedent: dependent lifts are suppressed, not cascaded). Each report is
    /// formatted only when the bounded list keeps it.
    /// </summary>
    private static void ReportRefusedSelection(SelectedSignatures selected, ResolutionRun run)
    {
        if (run.Diagnostics is not { } diagnostics)
            return;
        foreach (var (bodies, links, outcome) in selected.Refusals)
        {
            var names = bodies.Select(static body => body.Name).Distinct(StringComparer.Ordinal).ToArray();
            var group = FormatQuotedNameList(names);
            var linkList = FormatQuotedNameList(links);
            foreach (var body in bodies)
            {
                // An imported declaration carries no location: the report is positioned at the import site the analysis
                // walk was inside, exactly where the rewrite would report about it.
                diagnostics.Report(DiagnosticCode.SelfDependentInferredParameters, body.Span ?? body.ImportSite,
                    (body.Name, Group: group, Single: names.Length == 1, Links: linkList, OneLink: links.Count == 1, Outcome: outcome),
                    static state => RefusedSelectionMessage(ExprNameRenderer.BoundName(state.Name), state.Group, state.Single,
                        state.Links, state.OneLink, state.Outcome));
            }
        }
    }

    /// <summary>
    /// The wording of a refused selection, by category: a recursive inference that does not settle names the group that
    /// uses itself by name; every other category names the <c>.Algorithm</c> references <paramref name="links"/> it could
    /// not classify.
    /// </summary>
    internal static string RefusedSelectionMessage(string name, string group, bool single, string links, bool oneLink, SignatureSelectionOutcome outcome)
    {
        var references = links.Length == 0 ? "references among " + group : oneLink ? "reference " + links : "references " + links;
        return outcome switch
        {
            SignatureSelectionOutcome.NonSettling when single =>
                $"Cannot infer parameters for '{name}' because they depend on themselves and recursive inference does not settle: {group} "
                + "uses itself by name in a formula, and completing its parameters keeps returning to an earlier signature. "
                + "Declare the parameters explicitly, or write the call with its arguments.",
            SignatureSelectionOutcome.NonSettling =>
                $"Cannot infer parameters for '{name}' because they depend on themselves and recursive inference does not settle: {group} "
                + "use one another by name in formulas, and completing their parameters keeps returning to an earlier signature. "
                + "Declare the parameters explicitly, or write the calls with their arguments.",
            SignatureSelectionOutcome.Ambiguous =>
                $"Cannot infer parameters for '{name}' because the .Algorithm {references} can be read in more than one consistent way. "
                + "Declare the parameters explicitly or remove the circular dependency.",
            SignatureSelectionOutcome.UngroundedOnly =>
                $"Cannot infer parameters for '{name}' because every consistent reading of the .Algorithm {references} supports only itself: "
                + "it holds only because of the parameters it would give. Declare the parameters explicitly or remove the circular dependency.",
            SignatureSelectionOutcome.Undetermined =>
                $"Cannot infer parameters for '{name}' because deciding the .Algorithm {references} depends on a recursive inference "
                + "that does not settle. Declare the parameters explicitly or remove the circular dependency.",
            _ =>
                $"Cannot infer parameters for '{name}' because no consistent reading of the .Algorithm {references} exists: "
                + (oneLink ? "whether it is a calculation depends on the parameters this inference would give it. "
                    : "whether they are calculations depends on the parameters this inference would give them. ")
                + "Declare the parameters explicitly or remove the circular dependency.",
        };
    }

    /// <summary>
    /// What one selected signature was composed from (B3-5★): the body's own patterns, the lifted dependencies in order,
    /// the bindings it could reuse, and — for an X-02 violation — the signature before recovery, which the report describes.
    /// </summary>
    private sealed record SignatureComposition(
        IReadOnlyList<ParameterPattern> Own,
        List<LiftedDependency> Dependencies,
        ForwardableParameters Forwardable,
        IReadOnlyList<ParameterPattern>? Unrecovered);

    /// <summary>
    /// The lifted signature of the open body the rewrite is completing at <paramref name="level"/> (B3-5★): the one its
    /// selection composed, read once and never recomposed — so K owners of one L-wide callee keep FE-3's O(K + L) — and an
    /// X-02 violation of it reported here, at the reference the rewrite names, in declaration order. Without a selection
    /// (a resolution with no structural operation) the composition law applies directly.
    /// </summary>
    private static LiftedSignature SelectedLifting(ResolverLevel level, IReadOnlyList<ParameterPattern> own, List<LiftedDependency> deps,
        ForwardableParameters forwardable, ResolverWalkMemos memos)
    {
        var run = memos.Run;
        if (run.Selected is not { } selected || level.StaticContext?.Key is not { } key)
        {
            var direct = LiftSignature(own, deps, forwardable, run);
            return direct.Lifted && ParameterPattern.FindSignatureViolation(direct.Patterns) is { } found
                ? RejectInvalidLiftedSignature(direct, found, deps, memos)
                : direct;
        }

        if (!selected.TryGetFact(key, out var fact))
            throw new InvalidOperationException(
                $"Implicit-argument resolution rewrote the open body '{DefinitionName(key, run)}', which its signature selection never analyzed.");
        RequireSelectedComposition(fact, own, deps, forwardable, key, run);
        if (!fact.IsLifted)
            return new(own, SourceBindingKindsOf(own), Lifted: false);
        if (fact.Violation is { } violation)
            ReportInvalidLiftedSignature(((SignatureComposition)fact.Composition!).Unrecovered!, violation, deps, memos);
        var template = (ImplicitSignatureTemplate)fact.Patterns;
        return new(template, template.Facts.BindingKinds, Lifted: true);
    }

    /// <summary>
    /// THE SELECTION INVARIANT (B3-5★): the rewrite completes an open body from exactly what its selected signature was
    /// composed from — the same own patterns, the same reusable bindings, and the same lifted callee signatures in the same
    /// order (each by reference, so the check costs the dependencies, never the signatures' width). A difference means the
    /// analysis and the rewrite read different callees — an internal defect of this pass, never a program's error — so it
    /// fails loudly instead of publishing two answers.
    /// </summary>
    private static void RequireSelectedComposition(SignatureFact fact, IReadOnlyList<ParameterPattern> own, List<LiftedDependency> deps,
        ForwardableParameters forwardable, StaticScopeKey key, ResolutionRun run)
    {
        var disagreement = fact.Composition is not SignatureComposition composition ? "no composition"
            : !ReferenceEquals(composition.Own, own) ? "its own parameters"
            : !composition.Forwardable.Names.Equals(forwardable.Names)
                || !composition.Forwardable.CollectingNames.Equals(forwardable.CollectingNames) ? "the bindings it reuses"
            : composition.Dependencies.Count != deps.Count ? $"{composition.Dependencies.Count} versus {deps.Count} lifted callees"
            : FirstDifferentDependency(composition.Dependencies, deps) is { } index ? $"the lifted callee '{deps[index].Name}'"
            : null;
        if (disagreement is not null)
            throw new InvalidOperationException(
                $"Implicit-argument resolution completed the open body '{DefinitionName(key, run)}' from other inputs than its "
                + $"selected signature {fact.Signature.DisplayText} was composed from ({disagreement}): the analysis and the rewrite "
                + "read different callees.");

        static int? FirstDifferentDependency(List<LiftedDependency> analyzed, List<LiftedDependency> rewritten)
        {
            for (var i = 0; i < analyzed.Count; i++)
            {
                if (!ReferenceEquals(analyzed[i].Signature.ParameterPatterns, rewritten[i].Signature.ParameterPatterns))
                    return i;
            }

            return null;
        }
    }

    /// <summary>The selected signature of the open body <paramref name="key"/>, when this resolution selected one.</summary>
    private static CallableSignature? SelectedSignatureOf(StaticScopeKey key, string name, ResolutionRun run)
        => run.Selected?.SignatureOf(key, name);

    /// <summary>The name a body is defined under, for its signature's display (the property name; a block or branch is anonymous).</summary>
    private static string DefinitionName(StaticScopeKey key, ResolutionRun run)
        => run.StructuralOperation!.DefinitionOf(key).Name;

    /// <summary>
    /// The FINAL lifting signature of an endpoint the selection does not decide: a registry member's declared one, a clause
    /// family's clause-vote one, a closed body's written list, and a body an EARLIER operation completed (its resolved
    /// publication). An open body of THIS resolution always has an equation instead; what this resolution processes is
    /// never read here, so the analysis and the rewrite read one signature (cached per algorithm and name).
    /// </summary>
    private static LiftingSignature FinalLiftingSignature(StaticCallable endpoint, string name, ResolutionRun run)
    {
        if (endpoint.Key is { } key && run.StructuralOperation!.EarlierResolvedView(key) is { } completed)
            return completed is Algorithm.Alias { ResolvedTarget: { } target } ? target.Signature : LiftingSignatureOf(name, completed, run);
        return LiftingSignatureOf(name, endpoint.Written, run);
    }

    /// <summary>Whether a link an earlier operation completed is a calculation (its resolved body declares a parameter).</summary>
    private static bool FinalLinkIsCalculation(StaticScopeKey link, ResolutionRun run)
        => run.StructuralOperation!.EarlierResolvedView(link) is Algorithm.User { ParameterPatterns.Count: > 0 };

    /// <summary>Whether a body is an unbraced lone <c>.Algorithm</c> row, the one shape whose class Q8 decides (META-S3-1/2).</summary>
    private static bool IsAlgorithmLinkBody(Algorithm.User body)
        => IsUnbracedLoneRowBody(body)
            && body.Output[0] is Expr.DotCall { Args: null } edge && edge.UsesDotAlgorithmIntrinsic();

    /// <summary>
    /// Records the equations of a whole resolution (eager program or one deferred branch): the same recursion the rewrite
    /// makes, in declaration order, with nothing rewritten.
    /// </summary>
    private static void AnalyzeAlgorithm(
        Algorithm alg,
        SignatureMap parentParamMap,
        ForwardableParameters forwardable,
        bool isRoot,
        ConditionalBranchContext? branchContext,
        ResolutionRun run,
        Property? definition = null)
    {
        run.CancellationToken.ThrowIfCancellationRequested();
        switch (alg)
        {
            case Algorithm.Conditional conditional:
                AnalyzeConditionalProperty(conditional, "<anonymous>", parentParamMap, forwardable, run);
                break;
            case Algorithm.User { AssignmentDeconstructionTarget: not null }:
                break;
            case Algorithm.User { IsModuleElaborated: true } module when !isRoot:
                AnalyzeModuleRoot(module, run);
                break;
            case Algorithm.User user:
                AnalyzeUserAlgorithm(user, parentParamMap, forwardable.Rebase(run.ReferenceNameSets), isRoot, branchContext, run, definition);
                break;
        }
    }

    private static void AnalyzeModuleRoot(Algorithm.User module, ResolutionRun run)
    {
        if (!run.Analysis!.Modules.Add(module))
            return;
        using var owners = run.EnterLevel(DeclaringOwners.Root, level: null);
        AnalyzeUserAlgorithm(module, SignatureMap.Empty(run.Observations), ForwardableParameters.None, isRoot: false, branchContext: null, run);
    }

    private static void AnalyzeConditionalProperty(
        Algorithm.Conditional conditional,
        string propertyName,
        SignatureMap parentParamMap,
        ForwardableParameters forwardable,
        ResolutionRun run)
    {
        AnalyzeOpenTargets(conditional.Opens, run);
        var operation = run.StructuralOperation!;
        var familyOwners = conditional.Opens.Count == 0 ? run.Owners : run.Owners.Inside(conditional);
        var familyLevel = conditional.Opens.Count == 0 ? run.Level : new ResolverLevel(
            conditional, familyOwners, run.Level,
            staticContext: operation.Context(operation.ContextOf(run.Level?.StaticContext?.Key ?? operation.Queries.Keys.Root, conditional)));
        using (run.EnterLevel(familyOwners, familyLevel))
        {
            foreach (var branch in conditional.Branches)
            {
                if (branch.Body.DeferredRegion is not null)
                    continue;
                AnalyzeAlgorithm(branch.Body, parentParamMap, forwardable, isRoot: false,
                    new ConditionalBranchContext(propertyName, branch.Pattern), run);
            }
        }
    }

    private static void AnalyzeUserAlgorithm(
        Algorithm.User alg,
        SignatureMap parentParamMap,
        ForwardableParameters forwardable,
        bool isRoot,
        ConditionalBranchContext? branchContext,
        ResolutionRun run,
        Property? definition = null)
    {
        var analysis = run.Analysis!;
        var operation = run.StructuralOperation!;
        var key = operation.ContextOf(run.Level?.StaticContext?.Key ?? operation.Queries.Keys.Root, alg, branchContext?.Pattern);
        if (analysis.Bodies.ContainsKey(key) || analysis.Aliases!.IsAliased(key))
            return;
        if (!isRoot)
        {
            // DAG safety (the rewrite's region memo, mirrored): a body reached again in an analysis region it was already
            // analyzed in reads that context's facts instead of being analyzed once per path.
            var freeNames = FreeReferenceNames(alg, run);
            var visible = new VisibleProperty?[freeNames.Count];
            var index = 0;
            foreach (var name in freeNames.Names)
                visible[index++] = parentParamMap.TryGetValue(name, out var entry) ? entry : null;
            var region = new AnalysisRegionKey(alg, visible, forwardable.Names, forwardable.CollectingNames,
                branchContext is null ? null
                    : HasLoneBareRowShape(alg) ? run.BranchContexts.BareForwardingHeadId(branchContext.Pattern)
                    : run.BranchContexts.ClosedSpecificationId(branchContext.Pattern),
                OpensReadBy(freeNames, parentParamMap, run));
            if (analysis.Regions.TryGetValue(region, out var analyzed))
            {
                analysis.Aliases.Add(key, analyzed);
                return;
            }

            analysis.Regions.Add(region, key);
        }

        operation.Queries.Resources.Metadata(4, cancellationToken: run.CancellationToken);
        run.Observations?.RecordSignatureAnalysisBody();

        var levelOwners = run.Owners.Inside(alg);
        var structuralContext = operation.Context(key);
        var level = new ResolverLevel(levelOwners, run.Level, alg.Opens, structuralContext);
        operation.RegisterResolverLevel(level);
        run.AddWalkLevel(level);
        using var levelScope = run.EnterLevel(levelOwners, level);

        AnalyzeOpenTargets(alg.Opens, run);

        var ownForwarding = forwardable.WithoutProperties(alg.Properties, run.ReferenceNameSets);
        var nestedForwarding = ownForwarding.WithParameters(
            branchContext is null
                ? ParameterPattern.FlattenCaptures(alg.NameResolutionParameterPatterns)
                : ParameterPattern.FlattenCaptures(BranchBinderParameterPatterns(branchContext.Pattern)),
            run.ReferenceNameSets);

        var (_, localEntriesByName) = BuildPropertyEntries(alg.Properties, levelOwners, level, run);
        level.Entries = localEntriesByName;
        var visibleParamMap = localEntriesByName.Count == 0 && alg.Opens.Count == 0
            ? parentParamMap
            : parentParamMap.Extend(localEntriesByName);
        if (alg.Opens.Count > 0)
            visibleParamMap.AttachOpens();

        var isClosed = alg.HasExplicitParameterList || branchContext is not null;
        var body = new SignatureAnalysis.Body
        {
            Index = analysis.Order.Count,
            Key = key,
            Written = alg,
            Forwardable = ownForwarding,
            IsClosed = isClosed,
            IsRoot = isRoot,
            IsLink = !isRoot && !isClosed && IsAlgorithmLinkBody(alg),
            Name = isRoot ? "<root>" : definition?.Name ?? "<anonymous>",
            Span = definition?.FirstDeclarationSpan,
            ImportSite = run.ImportSite,
        };
        analysis.Bodies.Add(key, body);
        analysis.Order.Add(body);

        // The import site each property is processed under, exactly as the rewrite's property loop enters it.
        var loopImportSite = run.ImportSite;
        foreach (var property in alg.Properties)
        {
            // A hoisted deconstruction right-hand side is rows of THIS body (AstHelpers.WrittenRows).
            if (property.Value is Algorithm.User { IsAssignmentDeconstructionSource: true })
                continue;
            using var site = run.EnterImportSiteExactly(KatLang.ImportSite.OfProperty(property) ?? loopImportSite);
            if (property.Value is Algorithm.Conditional family)
                AnalyzeConditionalProperty(family, property.Name, visibleParamMap, nestedForwarding, run);
            else
                AnalyzeAlgorithm(property.Value, visibleParamMap, nestedForwarding, isRoot: false, branchContext: null, run, property);
        }

        var memos = new ResolverWalkMemos(run, run.Observations, diagnostics: null) { NestedForwarding = nestedForwarding };
        if (!isClosed)
        {
            // A lone bare row is never formula-lifted: it is a callable alias or bare forwarding (FWD-02), so its reference
            // takes the CALLABLE role; the root keeps its bare rows as their own zero-argument demands, and such a row
            // never lifts (a preserved row's own references are not walked; one that requires nothing contributes nothing
            // either way). A block written in a preserved row is still a body: the loop below analyzes it, and the rewrite
            // processes it as the row's block head (THE ROOT CLAUSE keeps the row unlifted, never its block).
            var rowRole = !isRoot && HasLoneBareRowShape(alg) ? LiftingRole.Callable : LiftingRole.Value;
            var sink = new EquationSink(visibleParamMap, memos, body, new EquationWalkMemo());
            foreach (var expr in AstHelpers.WrittenRows(alg, isRoot ? expr => !IsBareRootCallableRow(expr, visibleParamMap, memos) : null))
                WalkLiftingRoles(expr, rowRole, null, ref sink);
        }

        // Every block a row holds, a preserved root row's included, is a body of its own (D1a), analyzed in this body's
        // context and under its import site, as the rewrite processes it (enforced by RequireEveryAnalyzedBodyRewritten).
        foreach (var block in BlocksIn(AstHelpers.WrittenRows(alg)))
        {
            using var site = run.EnterImportSite(KatLang.ImportSite.OfBlock(block));
            AnalyzeAlgorithm(block.Algorithm, visibleParamMap, nestedForwarding, isRoot: false, branchContext: null, run);
        }
    }

    /// <summary>A bare root row that names a callable (<see cref="ShouldPreserveBareRootRow"/>'s shape, read statically).</summary>
    private static bool IsBareRootCallableRow(Expr expr, SignatureMap paramMap, ResolverWalkMemos memos)
        => expr is Expr.Resolve or Expr.DotCall { Args: null }
            && ResolveStaticCallable(expr, paramMap, memos, out _) is not null;

    /// <summary>The blocks an open target holds, each a body rooted at the prelude (as the rewrite's open-target region processes them).</summary>
    private static void AnalyzeOpenTargets(IReadOnlyList<Expr> opens, ResolutionRun run)
    {
        if (opens.Count == 0)
            return;
        using var rootOwners = run.EnterLevel(DeclaringOwners.Root, level: null);
        foreach (var block in BlocksIn(opens))
        {
            using var site = run.EnterImportSite(KatLang.ImportSite.OfBlock(block));
            AnalyzeAlgorithm(block.Algorithm, SignatureMap.Empty(run.Observations), ForwardableParameters.None, isRoot: false, branchContext: null, run);
        }
    }

    /// <summary>Every block written in these expressions, outermost first, never descending into a block's own body.</summary>
    private static List<Expr.AlgorithmExpr> BlocksIn(IEnumerable<Expr> rows)
    {
        var found = new List<Expr.AlgorithmExpr>();
        var seen = new HashSet<object>(ReferenceEqualityComparer.Instance);
        var stack = new Stack<object>();
        foreach (var row in rows.Reverse())
            stack.Push(row);
        var children = new List<object>();
        while (stack.TryPop(out var node))
        {
            if (!seen.Add(node))
                continue;
            if (node is Expr.AlgorithmExpr block)
            {
                found.Add(block);
                continue;
            }

            // Expressions and argument bundles only: a block's own body is its own analysis.
            if (node is not (Expr or OutputBundle))
                continue;
            children.Clear();
            for (var index = 0; AstStructuralPreflight.TryGetChild(node, index, out var child); index++)
                children.Add(child);
            for (var i = children.Count - 1; i >= 0; i--)
                stack.Push(children[i]);
        }

        return found;
    }
}
