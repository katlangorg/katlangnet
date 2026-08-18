using System.Collections.Immutable;
using System.Text;

namespace KatLang.Tests.AstGraphFuzz;

/// <summary>
/// The AST-graph node kinds the deterministic structural fuzzer generates. Every kind maps to
/// exactly one supported public <see cref="Expr"/> shape; the generator never manufactures
/// malformed object states, reflection-forged records, or reference cycles (graph node children
/// always have SMALLER ids, so every description is acyclic by construction — cycle handling is
/// pinned separately by <c>AstStructuralDepthTests</c>).
/// </summary>
public enum GKind
{
    // Leaves.
    Num,
    Str,
    Empty,
    Resolve,
    NativeCall,

    // Iterative expression-spine machine kinds (operand-position chains are walked by
    // Evaluator.EvalExpressionSpineCounted).
    Unary,
    Binary,
    Index,
    List,

    // Recursive generic-machine kinds.
    Capture,
    Call,
    DotCall,
    Grace,
    Block,

    // Iterative join-machine kinds (internal sequence-join nodes; the parser never emits
    // SequenceConstruct, so host construction is the only way to exercise these shapes).
    Construct,
    Spread,
}

/// <summary>
/// One node of a deterministic AST-graph description. <see cref="Children"/> hold ids of
/// PREVIOUS nodes only (strictly smaller than the node's own id), which makes every graph
/// acyclic by construction while allowing arbitrary sharing: the same child id may appear
/// under many parents, repeatedly under one parent, and in any argument position.
/// <see cref="Aux"/> selects deterministic payload/name/operator variants from fixed pools.
/// </summary>
public readonly record struct GNode(GKind Kind, int Aux, ImmutableArray<int> Children);

/// <summary>
/// A complete replayable fuzz case: the graph description plus the identity that produced it.
/// The last node is the root expression. <see cref="Describe"/> round-trips through
/// <see cref="AstGraphFuzzer.Parse"/> so a failing case can be replayed from its printed form
/// alone.
/// </summary>
public sealed record GraphCase(ulong Seed, int CaseIndex, ImmutableArray<GNode> Nodes)
{
    public int RootId => Nodes.Length - 1;

    public string Describe()
    {
        var sb = new StringBuilder();
        sb.Append("seed=0x").Append(Seed.ToString("X")).Append(" case=").Append(CaseIndex)
            .Append(" v").Append(AstGraphFuzzer.GeneratorVersion).Append(' ');
        for (var i = 0; i < Nodes.Length; i++)
        {
            if (i > 0) sb.Append(';');
            var n = Nodes[i];
            sb.Append(i).Append(':').Append(n.Kind).Append(':').Append(n.Aux).Append(":[")
                .Append(string.Join(',', n.Children)).Append(']');
        }

        return sb.ToString();
    }
}

/// <summary>
/// Deterministic structural AST-graph fuzzer. Generates supported host-constructed expression
/// DAGs — including shapes ordinary source syntax cannot share by reference — materializes them
/// twice (once preserving reference sharing, once as a fully expanded clone tree), and provides
/// the deterministic reducer used to minimize failing descriptions.
///
/// <para><b>Determinism.</b> All randomness comes from a SplitMix64 stream keyed by
/// (seed, case index, <see cref="GeneratorVersion"/>). No <see cref="Random"/>, no time, no
/// process state: the same triple always yields the same graph on every platform and run.</para>
/// </summary>
public static class AstGraphFuzzer
{
    /// <summary>Bump when generation logic changes so persisted repro lines stay honest.</summary>
    public const int GeneratorVersion = 1;

    // ── deterministic PRNG ──────────────────────────────────────────────────

    /// <summary>SplitMix64: tiny, stable, platform-independent.</summary>
    public struct Rng(ulong state)
    {
        public ulong Next()
        {
            state += 0x9E3779B97F4A7C15UL;
            var z = state;
            z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9UL;
            z = (z ^ (z >> 27)) * 0x94D049BB133111EBUL;
            return z ^ (z >> 31);
        }

        /// <summary>Uniform value in [0, bound).</summary>
        public int Next(int bound) => (int)(Next() % (ulong)bound);

        /// <summary>True with probability percent/100.</summary>
        public bool Chance(int percent) => Next(100) < percent;
    }

    public static Rng RngFor(ulong seed, int caseIndex)
        => new(seed ^ (0x51_7CC1B727220A95UL * (ulong)(caseIndex + 1)) ^ ((ulong)GeneratorVersion << 56));

    // ── fixed pools (indexes selected by GNode.Aux) ─────────────────────────

    /// <summary>Numeric payloads: small, structural stress only.</summary>
    public static readonly decimal[] Numbers = [0m, 1m, 2m, 3m, 7m, -1m, 0.5m];

    public static readonly string[] Strings = ["", "a", "kat"];

    /// <summary>
    /// Lexical names the generated graphs may resolve. All but "U" are defined by
    /// <see cref="HelperPreludeSource"/> or the runtime prelude; "U" is deliberately
    /// undefined so unknown-name error paths stay covered.
    /// </summary>
    public static readonly string[] ResolveNames = ["P0", "P1", "L", "F", "D", "count", "sum", "Math", "U"];

    /// <summary>Dot-call member names: intrinsic, builtin, defined, Math member, missing.</summary>
    public static readonly string[] MemberNames = ["string", "count", "P0", "Pi", "missing"];

    public static readonly UnaryOp[] UnaryOps = [UnaryOp.Minus, UnaryOp.Not];

    public static readonly BinaryOp[] BinaryOps =
        [BinaryOp.Add, BinaryOp.Sub, BinaryOp.Mul, BinaryOp.Eq, BinaryOp.Lt, BinaryOp.And];

    public static readonly string[] NativeNames = ["sin", "sqrt"];

    /// <summary>
    /// Host-program helper scope every generated case evaluates inside: small named values,
    /// a callable, and a shared value DAG (<c>D</c> is the F5/F16 doubling recipe at a safely
    /// bounded depth) so generated consumers can compose AST sharing with value sharing.
    /// Parsed per materialization so the shared and cloned programs never alias helper trees.
    /// </summary>
    public const string HelperPreludeSource =
        """
        P0 = 7
        P1 = (1, 2)
        L = [1, 2, 3]
        F(x) = x + 1
        Wrap(x) = [x, x]
        D = Wrap.repeat(6, 1)
        """;

    // ── generation ──────────────────────────────────────────────────────────

    /// <summary>
    /// Generation-shape knobs. Defaults keep payloads and node counts small: the objective is
    /// structural composition stress, not bulk data.
    /// </summary>
    public sealed record GeneratorSettings(
        int MinNodes = 4,
        int MaxNodes = 28,
        int SharingPercent = 55,
        int RepeatedEdgePercent = 25,
        int MaxFanOut = 4,
        int LeafPercent = 34)
    {
        public static GeneratorSettings Default { get; } = new();
    }

    /// <summary>
    /// Generates one deterministic graph case. Every fourth case is drawn from a targeted
    /// adversarial family instead of the free random walk, so rare compositions (join
    /// alternations, spread/capture interactions, diamonds, repeated argument edges) are
    /// GUARANTEED present in every corpus rather than merely probable.
    /// </summary>
    public static GraphCase Generate(ulong seed, int caseIndex, GeneratorSettings? settings = null)
    {
        settings ??= GeneratorSettings.Default;
        var rng = RngFor(seed, caseIndex);
        return (caseIndex % 4) switch
        {
            3 => GenerateFamilyCase(seed, caseIndex, ref rng),
            _ => GenerateFreeCase(seed, caseIndex, ref rng, settings),
        };
    }

    /// <summary>
    /// Per-node cap on the fully expanded occurrence count during FREE generation. Sharing
    /// multiplies semantic evaluation work (a shared DAG evaluates per occurrence, so its work
    /// is the expanded tree's size, not the graph's): the generator keeps that bounded BY
    /// CONSTRUCTION so the campaign's evaluations stay fast and hang-free, while the
    /// deliberately exponential shape is pinned separately by the DoublingDiamond boundary
    /// family under a configured step budget.
    /// </summary>
    private const long MaxExpandedOccurrencesPerNode = 4_000;

    private static GraphCase GenerateFreeCase(
        ulong seed, int caseIndex, ref Rng rng, GeneratorSettings settings)
    {
        var count = settings.MinNodes + rng.Next(settings.MaxNodes - settings.MinNodes + 1);
        var nodes = ImmutableArray.CreateBuilder<GNode>(count);
        var sizes = new long[count];
        for (var i = 0; i < count; i++)
        {
            if (i == 0 || rng.Chance(settings.LeafPercent))
            {
                nodes.Add(RandomLeaf(ref rng));
                sizes[i] = 1;
                continue;
            }

            var node = RandomInterior(ref rng, i, settings, sizes);
            nodes.Add(node);
            long total = 1;
            foreach (var child in node.Children)
                total += sizes[child];
            sizes[i] = total;
        }

        // Make the root meaningful: if the last node ended up a leaf, cap the graph with a
        // Capture over a handful of earlier nodes so sharing and prior structure stay reachable.
        if (nodes[count - 1].Children.IsEmpty && count > 2)
        {
            var span = Math.Min(3, count - 1);
            var children = ImmutableArray.CreateBuilder<int>(span);
            for (var k = 0; k < span; k++)
                children.Add(rng.Next(count - 1));
            nodes[count - 1] = new GNode(GKind.Capture, 0, children.ToImmutable());
        }

        return new GraphCase(seed, caseIndex, nodes.ToImmutable());
    }

    private static GNode RandomLeaf(ref Rng rng)
        => rng.Next(10) switch
        {
            0 or 1 or 2 or 3 => new GNode(GKind.Num, rng.Next(Numbers.Length), []),
            4 => new GNode(GKind.Str, rng.Next(Strings.Length), []),
            5 => new GNode(GKind.Empty, 0, []),
            6 => new GNode(GKind.NativeCall, rng.Next(NativeNames.Length), []),
            _ => new GNode(GKind.Resolve, rng.Next(ResolveNames.Length), []),
        };

    private static GNode RandomInterior(ref Rng rng, int id, GeneratorSettings settings, long[] sizes)
    {
        var kind = rng.Next(12) switch
        {
            0 => GKind.Unary,
            1 or 2 => GKind.Binary,
            3 => GKind.Index,
            4 => GKind.List,
            5 => GKind.Capture,
            6 or 7 => GKind.Call,
            8 => GKind.DotCall,
            9 => GKind.Construct,
            10 => GKind.Spread,
            _ => rng.Chance(25) ? GKind.Grace : GKind.Block,
        };

        var arity = kind switch
        {
            GKind.Unary or GKind.Spread or GKind.Grace or GKind.Block => 1,
            GKind.Binary or GKind.Index or GKind.Construct => 2,
            GKind.DotCall => 1 + rng.Next(settings.MaxFanOut),
            _ => 1 + rng.Next(settings.MaxFanOut),
        };

        var children = ImmutableArray.CreateBuilder<int>(arity);
        var previous = -1;
        long accumulated = 1;
        for (var slot = 0; slot < arity; slot++)
        {
            int child;
            if (previous >= 0 && rng.Chance(settings.RepeatedEdgePercent))
            {
                child = previous; // deliberate repeated edge: same child twice under one parent
            }
            else if (rng.Chance(settings.SharingPercent))
            {
                child = rng.Next(id); // shared: any earlier node, however distant
            }
            else
            {
                child = id - 1 - rng.Next(Math.Min(3, id)); // fresh-ish: recent chain-building
            }

            // Keep the case's semantic (per-occurrence) evaluation work bounded by
            // construction: an over-budget pick falls back to the always-present leaf 0.
            if (accumulated + sizes[child] > MaxExpandedOccurrencesPerNode)
                child = 0;

            accumulated += sizes[child];
            children.Add(child);
            previous = child;
        }

        var aux = kind switch
        {
            GKind.Unary => rng.Next(UnaryOps.Length),
            GKind.Binary => rng.Next(BinaryOps.Length),
            GKind.DotCall => rng.Next(MemberNames.Length),
            GKind.Grace => 1,
            _ => 0,
        };

        return new GNode(kind, aux, children.ToImmutable());
    }

    /// <summary>
    /// Targeted adversarial families. Each is a deliberately composed topology the free walk
    /// would only produce occasionally: diamonds, deep shared descendants under distinct parent
    /// kinds and argument positions, join/spine machine alternations, and spread/capture/list
    /// interactions.
    /// </summary>
    private static GraphCase GenerateFamilyCase(ulong seed, int caseIndex, ref Rng rng)
    {
        var family = rng.Next(8);
        var b = ImmutableArray.CreateBuilder<GNode>();

        int Add(GKind kind, int aux, params int[] children)
        {
            b.Add(new GNode(kind, aux, [.. children]));
            return b.Count - 1;
        }

        switch (family)
        {
            case 0:
            {
                // Diamond: one shared leaf under two distinct interior parents, re-joined.
                var leaf = Add(GKind.Num, 1);
                var left = Add(GKind.Unary, 0, leaf);
                var right = Add(GKind.Binary, 0, leaf, leaf);
                Add(GKind.Binary, 0, left, right);
                break;
            }

            case 1:
            {
                // Shared subtree under DIFFERENT parent kinds and argument positions:
                // first, middle, and last Call slots plus a list element and a capture slot.
                var shared = Add(GKind.Binary, 0, Add(GKind.Num, 1), Add(GKind.Num, 2));
                var call = Add(GKind.Call, 0, Add(GKind.Resolve, 3), shared, Add(GKind.Num, 0), shared);
                var list = Add(GKind.List, 0, shared, Add(GKind.Num, 4), shared);
                Add(GKind.Capture, 0, call, list, shared);
                break;
            }

            case 2:
            {
                // Join alternation: spread over construct over spread — the re-entry edges the
                // cost model charges — terminating in a shared leaf.
                var leaf = Add(GKind.Num, 3);
                var innerSpread = Add(GKind.Spread, 0, leaf);
                var construct = Add(GKind.Construct, 0, innerSpread, leaf);
                var outerSpread = Add(GKind.Spread, 0, construct);
                Add(GKind.Capture, 0, outerSpread, leaf);
                break;
            }

            case 3:
            {
                // Spine -> non-spine -> spine alternation: Index over Capture over Index.
                var leaf = Add(GKind.Num, 2);
                var innerIndex = Add(GKind.Index, 0, Add(GKind.List, 0, leaf, leaf), Add(GKind.Num, 0));
                var capture = Add(GKind.Capture, 0, innerIndex, innerIndex);
                Add(GKind.Index, 0, capture, Add(GKind.Num, 0));
                break;
            }

            case 4:
            {
                // Join spine handing off to a recursive composite (construct -> call) with the
                // callee shared into an ordinary value position too.
                var callee = Add(GKind.Resolve, 3);
                var call = Add(GKind.Call, 0, callee, Add(GKind.Num, 1));
                var construct = Add(GKind.Construct, 0, call, Add(GKind.Num, 2));
                Add(GKind.Capture, 0, construct, call);
                break;
            }

            case 5:
            {
                // Spread/list/capture boundary mesh over one shared list.
                var list = Add(GKind.List, 0, Add(GKind.Num, 1), Add(GKind.Num, 2));
                var spread = Add(GKind.Spread, 0, list);
                var capture = Add(GKind.Capture, 0, spread, list);
                Add(GKind.List, 0, capture, spread, list);
                break;
            }

            case 6:
            {
                // DotCall receiver/argument sharing: one expression as receiver AND argument,
                // with the same node also reached through a Block output boundary.
                var shared = Add(GKind.Binary, 0, Add(GKind.Num, 3), Add(GKind.Num, 1));
                var dot = Add(GKind.DotCall, 1, shared, shared);
                var block = Add(GKind.Block, 0, shared);
                Add(GKind.Capture, 0, dot, block);
                break;
            }

            default:
            {
                // Value-DAG consumer: AST sharing composed with the shared Result DAG "D".
                var d = Add(GKind.Resolve, 4);
                var eq = Add(GKind.Binary, 3, d, d);
                var count = Add(GKind.DotCall, 1, d);
                Add(GKind.Capture, 0, eq, count, d);
                break;
            }
        }

        return new GraphCase(seed, caseIndex, b.ToImmutable());
    }

    // ── materialization ─────────────────────────────────────────────────────

    /// <summary>
    /// Materializes the description into real <see cref="Expr"/> nodes, PRESERVING sharing:
    /// each graph node becomes exactly one Expr instance, so repeated ids become repeated
    /// references. Returns the root expression of the generated graph.
    /// </summary>
    public static Expr MaterializeShared(GraphCase graphCase)
    {
        var nodes = graphCase.Nodes;
        var built = new Expr[nodes.Length];
        for (var i = 0; i < nodes.Length; i++)
            built[i] = Build(nodes[i], id => built[id]);
        return built[graphCase.RootId];
    }

    /// <summary>
    /// Materializes a fully expanded CLONE: every semantic occurrence becomes its own fresh
    /// Expr instance, so the result contains no shared references at all. Iterative (explicit
    /// stack) so boundary-scale chains cannot consume test-runner stack. The caller must bound
    /// the expansion via <see cref="ExpandedOccurrenceCount"/> first: a heavily shared DAG's
    /// clone is exponentially larger than the graph.
    /// </summary>
    public static Expr MaterializeCloned(GraphCase graphCase)
    {
        var nodes = graphCase.Nodes;

        // Post-order over an explicit occurrence stack. Each frame builds its children first
        // (each occurrence separately), then constructs a fresh node from the collected parts.
        var results = new Stack<Expr>();
        var work = new Stack<(int Id, bool Expand)>();
        work.Push((graphCase.RootId, true));

        while (work.Count > 0)
        {
            var (id, expand) = work.Pop();
            var node = nodes[id];
            if (expand && !node.Children.IsEmpty)
            {
                work.Push((id, false));
                // Push children in reverse so they pop (and complete) in declaration order.
                for (var k = node.Children.Length - 1; k >= 0; k--)
                    work.Push((node.Children[k], true));
                continue;
            }

            var childExprs = new Expr[node.Children.Length];
            for (var k = node.Children.Length - 1; k >= 0; k--)
                childExprs[k] = results.Pop();
            results.Push(Build(node, id2 => throw new InvalidOperationException("unused"), childExprs));
        }

        return results.Pop();
    }

    /// <summary>
    /// Number of node OCCURRENCES in the fully expanded clone tree (the sum over all
    /// root-to-node paths), computed bottom-up without building anything. Saturates at
    /// <see cref="long.MaxValue"/>; callers skip the clone differential above their bound.
    /// </summary>
    public static long ExpandedOccurrenceCount(GraphCase graphCase)
    {
        var nodes = graphCase.Nodes;
        var sizes = new long[nodes.Length];
        for (var i = 0; i < nodes.Length; i++)
        {
            long total = 1;
            foreach (var child in nodes[i].Children)
            {
                total += sizes[child];
                if (total < 0) return long.MaxValue;
            }

            sizes[i] = total;
        }

        return sizes[graphCase.RootId];
    }

    private static Expr Build(GNode node, Func<int, Expr> byId, Expr[]? prebuilt = null)
    {
        Expr Child(int slot) => prebuilt is not null ? prebuilt[slot] : byId(node.Children[slot]);

        Expr[] ChildrenFrom(int start)
        {
            var items = new Expr[node.Children.Length - start];
            for (var k = 0; k < items.Length; k++)
                items[k] = Child(start + k);
            return items;
        }

        return node.Kind switch
        {
            GKind.Num => new Expr.Num(Numbers[node.Aux]),
            GKind.Str => new Expr.StringLiteral(Strings[node.Aux]),
            GKind.Empty => new Expr.EmptySequence(0),
            GKind.Resolve => new Expr.Resolve(ResolveNames[node.Aux]),
            GKind.NativeCall => new Expr.NativeCall(NativeNames[node.Aux], ["x"]),
            GKind.Unary => new Expr.Unary(UnaryOps[node.Aux], Child(0)),
            GKind.Binary => new Expr.Binary(BinaryOps[node.Aux], Child(0), Child(1)),
            GKind.Index => new Expr.Index(Child(0), Child(1)),
            GKind.List => new Expr.ListLiteral(new OutputBundle(ChildrenFrom(0))),
            GKind.Capture => new Expr.Capture(new OutputBundle(ChildrenFrom(0))),
            GKind.Call => new Expr.Call(Child(0), new OutputBundle(ChildrenFrom(1))),
            GKind.DotCall => new Expr.DotCall(
                Child(0),
                MemberNames[node.Aux],
                node.Children.Length > 1 ? new OutputBundle(ChildrenFrom(1)) : null),
            GKind.Grace => new Expr.Grace(Child(0), node.Aux),
            GKind.Block => new Expr.AlgorithmExpr(new Algorithm.User(null, [], [], [], [Child(0)])),
            GKind.Construct => new Expr.SequenceConstruct(Child(0), Child(1)),
            GKind.Spread => new Expr.SequenceSpread(Child(0)),
            _ => throw new InvalidOperationException($"Unhandled fuzz kind {node.Kind}"),
        };
    }

    /// <summary>
    /// Wraps a materialized root expression in the helper program scope: a freshly parsed
    /// helper prelude (per call, so shared/cloned programs never alias helper subtrees) whose
    /// output rows are replaced by the generated expression.
    /// </summary>
    public static Expr WrapInProgram(Expr generatedRoot)
    {
        var helpers = SourceProvenance.ParseValid(HelperPreludeSource).Root;
        return new Expr.AlgorithmExpr(helpers with { Output = new OutputBundle([generatedRoot]) });
    }

    // ── serialization / replay ──────────────────────────────────────────────

    /// <summary>Parses the node list emitted by <see cref="GraphCase.Describe"/> back into a case.</summary>
    public static GraphCase Parse(ulong seed, int caseIndex, string describedNodes)
    {
        var nodes = ImmutableArray.CreateBuilder<GNode>();
        foreach (var part in describedNodes.Split(';', StringSplitOptions.RemoveEmptyEntries))
        {
            var segments = part.Split(':');
            var kind = Enum.Parse<GKind>(segments[1]);
            var aux = int.Parse(segments[2]);
            var childText = segments[3].Trim('[', ']');
            var children = childText.Length == 0
                ? ImmutableArray<int>.Empty
                : [.. childText.Split(',').Select(int.Parse)];
            nodes.Add(new GNode(kind, aux, children));
        }

        return new GraphCase(seed, caseIndex, nodes.ToImmutable());
    }

    // ── reduction ───────────────────────────────────────────────────────────

    /// <summary>
    /// Deterministic greedy reducer: repeatedly applies the smallest structure-shrinking
    /// rewrites that keep <paramref name="stillFails"/> true, to a fixpoint. Reductions are
    /// tried in a fixed order so the same failing case always minimizes identically:
    /// (1) hoist a child over its parent at the root, (2) redirect each edge to the always-leaf
    /// node 0, (3) drop trailing children of variadic nodes, (4) hoist single children over
    /// interior nodes, (5) drop unreachable nodes and renumber.
    /// </summary>
    public static GraphCase Reduce(GraphCase failing, Func<GraphCase, bool> stillFails)
    {
        var current = failing;
        var progress = true;
        while (progress)
        {
            progress = false;

            // (1) Try replacing the whole root with one of its children (keeps the child graph).
            var root = current.Nodes[current.RootId];
            foreach (var child in root.Children)
            {
                var candidate = Retarget(current, child);
                if (stillFails(candidate))
                {
                    current = candidate;
                    progress = true;
                    break;
                }
            }

            if (progress) continue;

            // (2)+(3)+(4) per-node local shrinks, highest id first (closest to root).
            for (var id = current.Nodes.Length - 1; id >= 1 && !progress; id--)
            {
                var node = current.Nodes[id];
                if (node.Children.IsEmpty)
                    continue;

                // Drop the trailing child of variadic nodes. Call/DotCall keep their callee /
                // receiver slot; Capture keeps one body slot (an empty Capture is not a shape
                // the generator produces, so the reducer never introduces it either).
                var minimumChildren = node.Kind switch
                {
                    GKind.Call or GKind.DotCall or GKind.Capture => 1,
                    _ => 0,
                };
                if (node.Kind is GKind.List or GKind.Capture or GKind.Call or GKind.DotCall
                    && node.Children.Length > minimumChildren)
                {
                    var candidate = ReplaceNode(
                        current, id, node with { Children = node.Children.RemoveAt(node.Children.Length - 1) });
                    if (stillFails(candidate))
                    {
                        current = candidate;
                        progress = true;
                        break;
                    }
                }

                // Redirect each edge to leaf node 0.
                for (var slot = 0; slot < node.Children.Length && !progress; slot++)
                {
                    if (node.Children[slot] == 0)
                        continue;
                    var candidate = ReplaceNode(
                        current, id, node with { Children = node.Children.SetItem(slot, 0) });
                    if (stillFails(candidate))
                    {
                        current = candidate;
                        progress = true;
                    }
                }
            }

            if (!progress)
            {
                // (5) Structural cleanup: drop unreachable nodes. Counts as progress only when
                // it actually removed something, so the loop still terminates.
                var pruned = PruneUnreachable(current);
                if (pruned.Nodes.Length < current.Nodes.Length && stillFails(pruned))
                {
                    current = pruned;
                    progress = true;
                }
            }
        }

        return PruneUnreachable(current) is var final && stillFails(final) ? final : current;
    }

    private static GraphCase Retarget(GraphCase graphCase, int newRoot)
    {
        // Append a pass-through of the chosen node as the new last node? Simpler: truncate is
        // wrong (later nodes may be referenced), so retarget by appending nothing — instead
        // mark the root by rebuilding with the node order preserved and the root re-pointed via
        // a trailing single-child Capture... A Capture would change semantics; instead swap the
        // chosen subgraph to the end by pruning from that root.
        return PruneUnreachable(graphCase, newRoot);
    }

    private static GraphCase ReplaceNode(GraphCase graphCase, int id, GNode replacement)
        => graphCase with { Nodes = graphCase.Nodes.SetItem(id, replacement) };

    /// <summary>Drops nodes unreachable from the (optionally overridden) root and renumbers.</summary>
    public static GraphCase PruneUnreachable(GraphCase graphCase, int? rootOverride = null)
    {
        var root = rootOverride ?? graphCase.RootId;
        var nodes = graphCase.Nodes;
        var reachable = new bool[nodes.Length];
        var stack = new Stack<int>();
        stack.Push(root);
        reachable[root] = true;
        while (stack.Count > 0)
        {
            var id = stack.Pop();
            foreach (var child in nodes[id].Children)
            {
                if (!reachable[child])
                {
                    reachable[child] = true;
                    stack.Push(child);
                }
            }
        }

        // Node 0 must stay a valid redirect target for the reducer: keep it always.
        reachable[0] = true;

        var remap = new int[nodes.Length];
        var kept = ImmutableArray.CreateBuilder<GNode>();
        for (var i = 0; i < nodes.Length; i++)
        {
            if (!reachable[i])
                continue;
            remap[i] = kept.Count;
            var node = nodes[i];
            var children = ImmutableArray.CreateBuilder<int>(node.Children.Length);
            foreach (var child in node.Children)
                children.Add(remap[child]);
            kept.Add(node with { Children = children.ToImmutable() });
        }

        // The pruned root must be the LAST node; reachability-ordered ids preserve child<parent
        // because original ids were topologically ordered and remap is monotone. If the root was
        // overridden to an interior node, everything after it was unreachable and got dropped,
        // so the root lands at the end naturally.
        return graphCase with { Nodes = kept.ToImmutable() };
    }

    // ── coverage accounting ─────────────────────────────────────────────────

    /// <summary>Structural composition counters accumulated over reachable nodes of a corpus.</summary>
    public sealed class Coverage
    {
        public Dictionary<GKind, int> KindCounts { get; } = [];
        public int SharedNodes;
        public int RepeatedEdges;
        public int DiamondJoins;
        public int SharedUnderDistinctParentKinds;
        public int SpreadOverConstructEdges;
        public int JoinToRecursiveHandoffs;
        public int SpineToNonSpineHandoffs;
        public int CaptureBoundaryNodes;
        public int SharedInCallArguments;

        public void Accumulate(GraphCase graphCase)
        {
            var nodes = graphCase.Nodes;
            var reachable = ReachableIds(graphCase);
            var parents = new Dictionary<int, List<int>>();

            // Pass 1: kinds, per-edge compositions, and the full parent map.
            foreach (var id in reachable)
            {
                var node = nodes[id];
                KindCounts[node.Kind] = KindCounts.GetValueOrDefault(node.Kind) + 1;
                if (node.Kind is GKind.Capture)
                    CaptureBoundaryNodes++;

                var seenInThisParent = new HashSet<int>();
                foreach (var child in node.Children)
                {
                    if (!seenInThisParent.Add(child))
                        RepeatedEdges++;
                    (parents.TryGetValue(child, out var list) ? list : parents[child] = []).Add(id);

                    var childKind = nodes[child].Kind;
                    if (node.Kind == GKind.Spread && childKind == GKind.Construct)
                        SpreadOverConstructEdges++;
                    if (node.Kind is GKind.Spread or GKind.Construct
                        && childKind is not (GKind.Spread or GKind.Construct)
                        && !nodes[child].Children.IsEmpty)
                    {
                        JoinToRecursiveHandoffs++;
                    }

                    if (node.Kind is GKind.Unary or GKind.Binary or GKind.Index or GKind.List
                        && childKind is not (GKind.Unary or GKind.Binary or GKind.Index or GKind.List)
                        && !nodes[child].Children.IsEmpty)
                    {
                        SpineToNonSpineHandoffs++;
                    }
                }
            }

            // Pass 2: sharing topology from the completed parent map (order-independent).
            foreach (var (child, parentIds) in parents)
            {
                var distinctParents = parentIds.Distinct().ToList();
                var isShared = distinctParents.Count > 1 || parentIds.Count > distinctParents.Count;
                if (distinctParents.Count > 1)
                {
                    SharedNodes++;
                    DiamondJoins += distinctParents.Count - 1;
                    if (distinctParents.Select(p => nodes[p].Kind).Distinct().Count() > 1)
                        SharedUnderDistinctParentKinds++;
                }

                if (!isShared)
                    continue;

                // A shared/repeated node sitting in some Call's ARGUMENT slot (not callee).
                foreach (var parent in distinctParents)
                {
                    var parentNode = nodes[parent];
                    if (parentNode.Kind != GKind.Call)
                        continue;
                    for (var slot = 1; slot < parentNode.Children.Length; slot++)
                    {
                        if (parentNode.Children[slot] == child)
                        {
                            SharedInCallArguments++;
                            break;
                        }
                    }
                }
            }
        }

        private static List<int> ReachableIds(GraphCase graphCase)
        {
            var nodes = graphCase.Nodes;
            var reachable = new bool[nodes.Length];
            var stack = new Stack<int>();
            stack.Push(graphCase.RootId);
            reachable[graphCase.RootId] = true;
            var result = new List<int>();
            while (stack.Count > 0)
            {
                var id = stack.Pop();
                result.Add(id);
                foreach (var child in nodes[id].Children)
                {
                    if (!reachable[child])
                    {
                        reachable[child] = true;
                        stack.Push(child);
                    }
                }
            }

            return result;
        }
    }
}
