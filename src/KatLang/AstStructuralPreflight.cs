namespace KatLang;

/// <summary>The structural violation a preflight check found.</summary>
internal enum AstStructuralViolation
{
    /// <summary>A parent-to-descendant path exceeds the profile's weighted structural-depth limit.</summary>
    DepthExceeded,

    /// <summary>The node graph reaches itself again — it is not a tree or DAG.</summary>
    CycleDetected,
}

/// <summary>
/// One structural rejection: what was violated and a best-effort source span of the
/// node where the violation became observable. Allocated only on rejection.
/// </summary>
internal sealed record AstStructuralRejection(AstStructuralViolation Kind, SourceSpan? Span);

/// <summary>
/// How the consumers behind a preflight gate traverse sequence-join spines, which
/// decides whether those spines contribute structural depth.
/// </summary>
internal enum AstConsumerProfile
{
    /// <summary>
    /// The evaluator entry points. Every consumer on this path walks chains of the
    /// INTERNAL sequence-join nodes — <see cref="Expr.SequenceConstruct"/> and
    /// <see cref="Expr.SequenceSpread"/> — with an explicit iterative stack (the
    /// validation walker's flat-output traversal, and the evaluator's flat and counted
    /// spread/join evaluation, pinned by
    /// <c>Eval_SequenceSpread_LongChain_IsStackSafeForFlatAndCountedEvaluation</c>), so
    /// those two node kinds add NO depth WITHIN one kind: an arbitrarily long
    /// single-kind host-built join chain stays accepted, exactly as it evaluates
    /// today. The exception is the ALTERNATION link — a spread whose operand is a
    /// construct — which re-enters generic evaluation recursively and weighs EIGHT
    /// units (see <c>Weight</c>). A <see cref="Expr.DotCall"/>
    /// link weighs THREE units, matching the several large resolution frames each
    /// link consumes at evaluation time. Every other node kind counts one level —
    /// including the unary/binary/index/list spines that the evaluator itself handles
    /// iteratively, because the small-framed recursive consumers around evaluation
    /// (validation walk, optimizer analysis, pattern binding) still traverse them.
    /// </summary>
    EvaluatorIterativeJoinSpines,

    /// <summary>
    /// Consumers that recurse through the base <see cref="AstWalker"/> dispatch or
    /// their own recursive visitors for EVERY node kind (parser front-end passes,
    /// semantic model building). All nodes count toward depth. Parser-produced trees
    /// are unaffected by the difference: the parser has zero origin sites for
    /// <see cref="Expr.SequenceConstruct"/> and caps written spread chains at
    /// <c>Parser.MaxExpressionChainDepth</c>.
    /// </summary>
    FullyRecursive,
}

/// <summary>
/// Non-recursive structural-safety preflight for KatLang ASTs.
///
/// <para><b>Why this exists.</b> The public AST model (<see cref="Expr"/>,
/// <see cref="Algorithm"/>, <see cref="Pattern"/>, <see cref="ParameterPattern"/>,
/// <see cref="ScopeCtx"/>) is host-constructible, and every downstream consumer —
/// <see cref="AstWalker"/> validation, front-end elaboration passes, the optimizers,
/// and <see cref="Evaluator"/> expression evaluation — walks it recursively on the CLR
/// stack. A sufficiently deep tree therefore terminates the whole process with an
/// unhandleable <see cref="StackOverflowException"/>. This preflight runs BEFORE any
/// recursive consumer sees a tree, walking it with an explicit iterative stack and
/// rejecting structurally unsafe input through the normal structured-error protocols
/// (<see cref="EvalError"/> for evaluator entry points, <see cref="Diagnostic"/> for
/// the parser front end).</para>
///
/// <para><b>Depth definition.</b> Structural AST depth is a consumer-profile-weighted
/// cost over the longest parent-to-descendant reference path, counting both endpoints;
/// a one-unit root alone has depth 1. Counted nodes are <see cref="Expr"/>, <see cref="Algorithm"/>,
/// <see cref="Pattern"/>, <see cref="ParameterPattern"/>, and <see cref="ScopeCtx"/>
/// instances. <see cref="Property"/> and <see cref="CondBranch"/> are membranes: the
/// traversal passes through them to their contents without adding a level. On the
/// evaluator gates (<see cref="AstConsumerProfile.EvaluatorIterativeJoinSpines"/>) the
/// two internal sequence-join node kinds (<see cref="Expr.SequenceConstruct"/>,
/// <see cref="Expr.SequenceSpread"/>) also contribute no depth within one kind,
/// because every consumer behind those gates walks single-kind spines with an
/// explicit iterative stack — an arbitrarily long single-kind host-built join chain
/// is a supported, pinned shape. A spread-of-construct ALTERNATION link is the
/// exception: it re-enters generic evaluation recursively and is weighted. This is
/// distinct from — and deliberately much larger than — the runtime limit on
/// simultaneously active dynamic algorithm invocations
/// (<see cref="EvaluationLimits.MaxDepth"/>): a deeply RECURSIVE program has a shallow
/// AST and is governed by <see cref="EvaluationLimits.MaxDepth"/>; a deeply NESTED
/// program tree is governed by this preflight.</para>
///
/// <para><b>Ceilings.</b> Every FAT-FRAME consumer enforces
/// <see cref="EvaluationLimits.MaxSupportedAstDepth"/> (see its documentation for the
/// safety invariant and calibration): the evaluator entry points, front-end
/// ELABORATION (<c>FrontEndPipeline.FinalizeElaboration</c> plus the public
/// <c>ParameterDetector.Detect</c> and <c>ImplicitArgumentResolver.Resolve</c>
/// boundaries), and semantic-model building.
/// <see cref="EvaluationLimits.MaxAstDepth"/> can only request a lower limit, so no
/// configuration can re-open the process-safety hole. Only the small-framed
/// WALKER-CLASS raw-syntax passes — the <c>Parser.ParseSyntax</c> post-parse
/// validation walk and the module composed-root load-invariant walk — plus the
/// module loader's measured traversal use the larger
/// <see cref="RawSyntaxMaxAstDepth"/>, so every parser capacity shape keeps parsing
/// while elaboration and evaluation apply their own bound. Both ceilings are
/// clamped inside <see cref="Check"/> itself.</para>
///
/// <para><b>Sharing and cycles.</b> Some public record collections remain
/// <see cref="IReadOnlyList{T}"/> views over caller-owned lists (OutputBundle is
/// deliberately an immutable snapshot), so hosts can still build shared acyclic
/// subgraphs and reference cycles through the caller-owned collections. Shared subtrees are legal and
/// are visited once (per-node longest-downward-path heights are memoized by reference
/// identity, keeping the walk <c>O(nodes + edges)</c> instead of exponential), while
/// depth is still judged over the longest PATH, so a shared subtree reached again
/// through a longer route is re-judged at that deeper position without being re-walked.
/// Cycles are detected iteratively (a node reached again while still on the traversal
/// path) and rejected deterministically. The preflight never uses record structural
/// equality, recursive hashing, or <c>ToString()</c> — any of those would recurse over
/// the very tree it is guarding — only reference identity.</para>
///
/// <para><b>Costs.</b> The traversal uses no CLR recursion. Its explicit frame stack is
/// bounded by the ACTUAL root-to-node path in the traversed input, not necessarily by
/// the weighted depth limit: zero-weight internal sequence-join/spread spines may be
/// arbitrarily longer than their weighted depth while remaining CLR-stack-safe. The
/// reference-identity color/height table is linear in visited nodes. Under the supported
/// assumption that caller-owned collections remain stable during a check, overall time
/// and storage are <c>O(nodes + edges)</c> and <c>O(nodes)</c>, respectively. The
/// preflight charges nothing to any <see cref="EvaluationBudget"/>: it runs before
/// evaluation begins and consumes no steps, materialization, or string budget. It holds
/// no static state, so concurrent checks are independent.</para>
/// </summary>
internal static class AstStructuralPreflight
{
    /// <summary>
    /// Structural gate for the raw-syntax consumers: the post-parse validation walk
    /// in <c>Parser.ParseSyntax</c> and the module loader's composed-root
    /// load-invariant walk (both walker-class small frames, process-isolated failure
    /// boundary ~3,000-4,000 nodes on a 1 MiB Debug stack, ≥4.5x margin), plus the
    /// module loader's own rebuilding traversal (heavier frames, measured failure
    /// boundary ~1,600-1,700 counted levels Debug / ~1,300-1,600 Release, ≥2.0x
    /// margin — see <c>ModuleLoader.MaxTraversalDepth</c>). 640 admits every tree
    /// the parser can emit (the cumulative weighted recursion budget
    /// <c>Parser.MaxNestingDepth</c> = 384 units caps single-mechanism trees at
    /// ~385 nodes), keeping the raw parser capacity fully intact.
    ///
    /// <para>Every FAT-FRAME consumer is gated by the evaluation ceiling
    /// (<see cref="EvaluationLimits.MaxSupportedAstDepth"/>) instead: front-end
    /// elaboration (a composed tree of ~500-626 nodes overflows a 1 MiB thread inside
    /// <c>ParameterDetector.RewriteParams</c>, Debug and Release alike; the public
    /// <c>ParameterDetector.Detect</c> and <c>ImplicitArgumentResolver.Resolve</c>
    /// boundaries gate the same ceiling), semantic-model building (a 640-node spine
    /// overflows a 512 KiB thread; a 300-node one completes within it), and
    /// evaluation itself. Raw syntax between the two gates parses but front-end
    /// elaboration rejects it with one structured diagnostic.</para>
    /// </summary>
    internal const int RawSyntaxMaxAstDepth = 640;

    /// <summary>
    /// Checks one root node (an <see cref="Expr"/> or <see cref="Algorithm"/>).
    /// Returns <c>null</c> when the tree is structurally safe, otherwise the rejection.
    /// Depth is WEIGHTED by the consumer profile: under
    /// <see cref="AstConsumerProfile.EvaluatorIterativeJoinSpines"/> the internal
    /// sequence-join node kinds contribute no depth because every consumer behind that
    /// gate walks their spines iteratively, and each dot-call link costs THREE units
    /// because its resolution machinery consumes several frames per link; every other
    /// node counts one level.
    /// </summary>
    internal static AstStructuralRejection? Check(object root, int maxDepth, AstConsumerProfile profile)
    {
        // The hard ceiling is enforced HERE, not only at the configuration surface, so
        // no caller — present or future — can hand in a raised limit and re-open the
        // process-safety hole. The fully-recursive profile may use the larger
        // raw-syntax cap (its gated consumers use far shallower frames); nothing may
        // exceed it.
        var ceiling = profile == AstConsumerProfile.FullyRecursive
            ? RawSyntaxMaxAstDepth
            : EvaluationLimits.MaxSupportedAstDepth;
        if (maxDepth > ceiling)
            maxDepth = ceiling;

        if (maxDepth < 1)
            return new AstStructuralRejection(AstStructuralViolation.DepthExceeded, SpanOf(root));

        // Frames: the explicit DFS path. frames[i].Node is the i-th node on the current
        // root-to-node path, so the frame count is the PATH LENGTH IN NODES (bounded by
        // the input size, since weight-0 join nodes stay on the path without consuming
        // depth budget), while pathWeight tracks the WEIGHTED depth that is judged
        // against the limit. The array starts small and doubles so ordinary shallow
        // programs do not pay for deep ones.
        var frames = new Frame[32];
        var frameCount = 0;
        var pathWeight = 0;

        // Longest-downward WEIGHTED heights by reference identity. OnStack marks nodes
        // on the current path (gray); a non-negative value is the memoized weighted
        // height of a completed node (black). Reference identity is essential: record
        // structural equality would recursively walk the tree this guard exists to
        // reject.
        const int OnStack = -1;
        var heights = new Dictionary<object, int>(ReferenceEqualityComparer.Instance);

        var rootWeight = Weight(root, profile);
        if (rootWeight > maxDepth)
            return new AstStructuralRejection(AstStructuralViolation.DepthExceeded, SpanOf(root));

        frames[frameCount++] = new Frame(root, rootWeight);
        pathWeight = rootWeight;
        heights[root] = OnStack;

        while (frameCount > 0)
        {
            ref var frame = ref frames[frameCount - 1];

            if (!TryGetChild(frame.Node, frame.NextChildIndex, out var child))
            {
                // All children processed: this node's weighted height is now exact.
                var height = frame.MaxChildHeight + frame.Weight;
                heights[frame.Node] = height;
                pathWeight -= frame.Weight;
                frameCount--;
                if (frameCount > 0)
                {
                    ref var parent = ref frames[frameCount - 1];
                    if (height > parent.MaxChildHeight)
                        parent.MaxChildHeight = height;
                }

                continue;
            }

            frame.NextChildIndex++;

            if (heights.TryGetValue(child, out var childHeight))
            {
                if (childHeight == OnStack)
                    return new AstStructuralRejection(AstStructuralViolation.CycleDetected, SpanOf(child));

                // Completed shared node: the deepest path through THIS occurrence is the
                // current weighted path plus the memoized weighted height — judged
                // without re-walking the shared subtree.
                if (pathWeight + childHeight > maxDepth)
                    return new AstStructuralRejection(AstStructuralViolation.DepthExceeded, SpanOf(child));

                if (childHeight > frame.MaxChildHeight)
                    frame.MaxChildHeight = childHeight;
                continue;
            }

            var childWeight = Weight(child, profile);
            if (pathWeight + childWeight > maxDepth)
                return new AstStructuralRejection(AstStructuralViolation.DepthExceeded, SpanOf(child));

            heights[child] = OnStack;
            if (frameCount == frames.Length)
                Array.Resize(ref frames, frames.Length * 2);
            frames[frameCount++] = new Frame(child, childWeight);
            pathWeight += childWeight;
        }

        return null;
    }

    /// <summary>
    /// Structural depth cost of one node under the gate's consumer profile. On the
    /// evaluator gates: the internal sequence-join spines are free WITHIN one kind,
    /// because every downstream consumer walks single-kind spines iteratively — but
    /// an ALTERNATION link (a spread whose operand is a construct) re-enters generic
    /// evaluation recursively (~6 CLR frames per link, measured to overflow a 1 MiB
    /// Debug stack between 80 and 96 alternations) and therefore weighs EIGHT units,
    /// admitting at most 37 links under the 300-unit ceiling (≥2.1x Debug margin).
    /// The machine-evaluated unary/binary/index/list spines still cost one unit each
    /// so that the small-framed recursive consumers around evaluation — validation
    /// walk, planner analysis, pattern binding — stay bounded too. A dot-call link costs THREE
    /// units, because each link's resolution machinery (pipeline planning, algorithm
    /// resolution, lexical receiver-injection fallback) consumes several large frames —
    /// process-isolated probes measured pure dot-call chains failing at ~160 links
    /// (Debug) / ~250 links (Release) on a 1 MiB stack, so the 300-unit evaluation
    /// ceiling admits at most ~100 links, a ≥1.6x margin in both configurations.
    /// Everything else is one level everywhere; the fully-recursive front-end profile
    /// counts every node as one level.
    /// </summary>
    private static int Weight(object node, AstConsumerProfile profile)
    {
        // A Capture node stands for what was previously a Block wrapper PLUS its
        // transparent wrapper Algorithm — two nodes costing two units on every
        // profile — and its recursive consumers still spend comparable frames per
        // written paren level, so it keeps that two-unit cost everywhere. A Call
        // node likewise absorbs its former transparent Args wrapper Algorithm
        // (two units everywhere), and an args-bearing DotCall absorbs the same
        // wrapper unit on top of its own link cost. This preserves every
        // measured per-shape stack capacity unchanged, while the recursive
        // consumers now spend the same or fewer frames per level (no wrapper is
        // constructed or wired at runtime).
        if (node is Expr.Capture or Expr.Call)
            return 2;

        if (node is Expr.DotCall argsBearingDotCall && argsBearingDotCall.Args is not null)
            return profile == AstConsumerProfile.EvaluatorIterativeJoinSpines ? 4 : 2;

        if (profile != AstConsumerProfile.EvaluatorIterativeJoinSpines)
            return 1;

        // The join kinds are free only WITHIN one kind: construct spines flatten
        // iteratively and consecutive spread layers unwrap iteratively, but each
        // ALTERNATION — a spread whose operand is a construct — re-enters generic
        // evaluation recursively (~6 CLR frames per alternation, measured to
        // overflow a 1 MiB Debug stack between 80 and 96 alternations). Charging
        // EIGHT units per alternation link admits at most 37 links under the
        // 300-unit evaluation ceiling, a >=2.1x margin in Debug (>=2.9x Release),
        // while pure single-kind chains keep their pinned unbounded acceptance.
        if (node is Expr.SequenceSpread(Expr.SequenceConstruct))
            return 8;

        return node switch
        {
            Expr.SequenceConstruct or Expr.SequenceSpread => 0,
            Expr.DotCall => 3,
            _ => 1,
        };
    }

    /// <summary>Maps a rejection to the evaluator's structured error protocol.</summary>
    internal static EvalError ToEvalError(AstStructuralRejection rejection, int effectiveLimit)
        => rejection.Kind switch
        {
            AstStructuralViolation.CycleDetected =>
                new EvalError.AstCycleDetected { Span = rejection.Span },
            _ => new EvalError.AstDepthLimitExceeded(effectiveLimit) { Span = rejection.Span },
        };

    /// <summary>
    /// Maps a rejection to the parser/front-end structured diagnostic protocol,
    /// citing the limit of the gate that rejected the tree (raw syntax or front-end
    /// elaboration). Parser-built trees are constructed bottom-up and cannot be
    /// cyclic, but the public detector and module-loader boundaries also accept host
    /// ASTs, so a cycle keeps its own accurate diagnostic instead of being mislabeled
    /// as a depth violation.
    /// </summary>
    internal static Diagnostic ToParseDiagnostic(AstStructuralRejection rejection, int limit)
        => new(
            rejection.Kind == AstStructuralViolation.CycleDetected
                ? ParseCycleDiagnosticMessage
                : ParseDepthDiagnosticMessage(limit),
            DiagnosticSeverity.Error,
            rejection.Span ?? new SourceSpan(1, 1, 1, 1));

    internal const string ParseCycleDiagnosticMessage =
        "Program structure contains a reference cycle and cannot be processed safely. "
        + "KatLang ASTs may share acyclic subtrees, but no node may reach itself through its own children.";

    internal static string ParseDepthDiagnosticMessage(int limit)
        => "Program structure is too deep to process safely: the structural AST depth limit of "
            + $"{limit} nodes was exceeded. "
            + "Reduce how deeply parentheses, brackets, braces, calls, operators, and patterns nest "
            + "inside one expression, or split the program into smaller named properties.";

    private struct Frame(object node, int weight)
    {
        public readonly object Node = node;
        public readonly int Weight = weight;
        public int NextChildIndex;
        public int MaxChildHeight;
    }

    private static SourceSpan? SpanOf(object node) => (node as Expr)?.Span;

    /// <summary>
    /// Enumerates the recursively reachable children of one AST node by index, in a
    /// fixed deterministic order, without copying any child collection. Children are
    /// exactly the references the recursive consumers (walker, front-end passes,
    /// optimizers, evaluator) follow later. Node kinds without recursive children
    /// return <c>false</c> immediately. An unknown node kind fails loudly instead of
    /// being silently treated as a leaf: skipping unknown children would let a future
    /// AST variant smuggle unmeasured depth past this guard.
    /// </summary>
    private static bool TryGetChild(object node, int index, out object child)
    {
        switch (node)
        {
            case Expr.Unary unary:
                return PickOne(index, unary.Operand, out child);
            case Expr.Binary binary:
                return PickTwo(index, binary.Left, binary.Right, out child);
            case Expr.Index indexExpr:
                return PickTwo(index, indexExpr.Target, indexExpr.Selector, out child);
            case Expr.SequenceConstruct sequenceConstruct:
                return PickTwo(index, sequenceConstruct.Left, sequenceConstruct.Right, out child);
            case Expr.SequenceSpread spread:
                return PickOne(index, spread.Operand, out child);
            case Expr.Grace grace:
                return PickOne(index, grace.Inner, out child);
            case Expr.AlgorithmExpr block:
                return PickOne(index, block.Algorithm, out child);
            case Expr.Capture capture:
                return PickFromList(index, capture.Body, out child);
            case Expr.Call call:
                if (index == 0)
                {
                    child = call.Function;
                    return true;
                }

                return PickFromList(index - 1, call.Args, out child);
            case Expr.DotCall dotCall:
                if (index == 0)
                {
                    child = dotCall.Target;
                    return true;
                }

                index--;
                // The elaborated lexical-fallback identity is an Expr child
                // (Resolve/Param leaf for parser/front-end trees, but a
                // host-built tree could place anything here), so it is
                // enumerated for the same cycle/depth safety as every other
                // reference the recursive consumers follow.
                if (dotCall.LexicalFallback is { } lexicalFallback)
                {
                    if (index == 0)
                    {
                        child = lexicalFallback;
                        return true;
                    }

                    index--;
                }

                if (dotCall.Args is { } dotArgs)
                    return PickFromList(index, dotArgs, out child);

                child = null!;
                return false;
            case Expr.ListLiteral listLiteral:
                return PickFromList(index, listLiteral.Items, out child);
            case Expr.Param or Expr.Num or Expr.StringLiteral or Expr.EmptySequence
                or Expr.Resolve or Expr.NativeCall:
                child = null!;
                return false;

            // ONE uniform case for every algorithm subtype: the recursive collections
            // are declared as virtual init properties on the Algorithm BASE, so a host
            // initializer can place deep values in ANY of them on ANY subtype —
            // including combinations today's consumers ignore (a Builtin's Output, a
            // Conditional's parameter patterns). Enumerating the base surface uniformly
            // closes that future bypass without double-counting: each subtype's
            // overrides ARE the base properties, read once here.
            case Algorithm algorithm:
            {
                if (algorithm.Parent is { } parent)
                {
                    if (index == 0)
                    {
                        child = parent;
                        return true;
                    }

                    index--;
                }

                var opens = algorithm.Opens;
                if (index < opens.Count)
                {
                    child = opens[index];
                    return true;
                }

                index -= opens.Count;
                var properties = algorithm.Properties;
                if (index < properties.Count)
                {
                    child = properties[index].Value;
                    return true;
                }

                index -= properties.Count;
                var output = algorithm.Output;
                if (index < output.Count)
                {
                    child = output[index];
                    return true;
                }

                index -= output.Count;
                var branches = algorithm.Branches;
                // Avoid `Count * 2`: IReadOnlyList is caller-supplied, and even a
                // virtual collection reporting a huge legal Count must not overflow
                // the child-index arithmetic. The interleaved order stays exactly
                // Pattern(0), Body(0), Pattern(1), Body(1), ... .
                if (index / 2 < branches.Count)
                {
                    var branch = branches[index / 2];
                    child = index % 2 == 0 ? branch.Pattern : branch.Body;
                    return true;
                }

                // Reaching here proves index >= 2 * Count, so the two subtractions
                // are individually non-negative and cannot overflow.
                index -= branches.Count;
                index -= branches.Count;
                var parameterPatterns = algorithm.ParameterPatterns;
                if (index < parameterPatterns.Count)
                {
                    child = parameterPatterns[index];
                    return true;
                }

                index -= parameterPatterns.Count;
                var explicitPatterns = algorithm.ExplicitParameterPatterns;
                if (index < explicitPatterns.Count)
                {
                    child = explicitPatterns[index];
                    return true;
                }

                child = null!;
                return false;
            }

            case Pattern.SequenceValue sequenceValue:
                return PickFromList(index, sequenceValue.Items, out child);
            case Pattern.Bind or Pattern.LitInt or Pattern.LitString:
                child = null!;
                return false;

            case SequenceValueParameterPattern sequencePattern:
                return PickFromList(index, sequencePattern.Items, out child);
            case CaptureParameterPattern:
                child = null!;
                return false;

            case ScopeCtx scope:
            {
                if (scope.Parent is { } parent)
                {
                    if (index == 0)
                    {
                        child = parent;
                        return true;
                    }

                    index--;
                }

                var opens = scope.Opens;
                if (index < opens.Count)
                {
                    child = opens[index];
                    return true;
                }

                index -= opens.Count;
                var properties = scope.Properties;
                if (index < properties.Count)
                {
                    child = properties[index].Value;
                    return true;
                }

                child = null!;
                return false;
            }

            default:
                throw new InvalidOperationException(
                    $"AstStructuralPreflight does not know the AST node kind '{node.GetType()}'. "
                    + "Every recursively reachable node kind must enumerate its children here "
                    + "before trees containing it can be accepted safely.");
        }
    }

    private static bool PickOne(int index, object only, out object child)
    {
        if (index == 0)
        {
            child = only;
            return true;
        }

        child = null!;
        return false;
    }

    private static bool PickTwo(int index, object first, object second, out object child)
    {
        switch (index)
        {
            case 0:
                child = first;
                return true;
            case 1:
                child = second;
                return true;
            default:
                child = null!;
                return false;
        }
    }

    private static bool PickFromList<T>(int index, IReadOnlyList<T> items, out object child)
        where T : class
    {
        if (index < items.Count)
        {
            child = items[index];
            return true;
        }

        child = null!;
        return false;
    }
}
