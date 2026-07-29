namespace KatLang.Tests;

/// <summary>
/// Structural description of a generated semantic-explorer corpus value.
/// Carries both the written KatLang source form and the equivalent Lean AST
/// construction (mirroring the C# parser's elaboration: parenthesized lists
/// are zero-parameter blocks, redundant parens are one written grouping level).
/// </summary>
public abstract record ExplorerValue
{
    private ExplorerValue() { }

    /// <summary>An integer atom literal.</summary>
    public sealed record Num(int Value) : ExplorerValue;

    /// <summary>The empty sequence value literal <c>()</c>.</summary>
    public sealed record Empty : ExplorerValue;

    /// <summary>A parenthesized list literal with two or more items.</summary>
    public sealed record Seq(IReadOnlyList<ExplorerValue> Items) : ExplorerValue;

    /// <summary>Redundant parentheses around one written value: <c>(x)</c>.</summary>
    public sealed record Wrap(ExplorerValue Inner) : ExplorerValue;

    /// <summary>An exact immutable list literal <c>[a, b]</c> (any element count).</summary>
    public sealed record ListOf(IReadOnlyList<ExplorerValue> Items) : ExplorerValue;

    public string Source => this switch
    {
        Num n => n.Value.ToString(System.Globalization.CultureInfo.InvariantCulture),
        Empty => "()",
        Seq s => "(" + string.Join(", ", s.Items.Select(i => i.Source)) + ")",
        Wrap w => "(" + w.Inner.Source + ")",
        ListOf l => "[" + string.Join(", ", l.Items.Select(i => i.Source)) + "]",
        _ => throw new InvalidOperationException(),
    };

    /// <summary>
    /// Lean Expr text for this written value. Parenthesized lists become
    /// zero-parameter blocks whose output slots are the items (the same
    /// elaboration the C# parser applies); a redundant wrap is a nested
    /// single-output block (one written grouping level); a bracket list
    /// literal is the dedicated exact <c>.listLiteral</c> node.
    /// </summary>
    public string LeanExpr => this switch
    {
        Num n => $"(.num {n.Value})",
        Empty => "(.emptySequence 0)",
        Seq s => $"(.block (alg [] [] [] [{string.Join(", ", s.Items.Select(i => i.LeanExpr))}]))",
        Wrap w => $"(.block (alg [] [] [] [{w.Inner.LeanExpr}]))",
        ListOf l => $"(.listLiteral [{string.Join(", ", l.Items.Select(i => i.LeanExpr))}])",
        _ => throw new InvalidOperationException(),
    };
}

/// <summary>One generated explorer case: a receiver template applied to a value.</summary>
public sealed record ExplorerCase(
    string Id,
    string TemplateId,
    string ValueId,
    string Source,
    string? LeanProgram);

/// <summary>
/// One direct internal-AST-node case: a program constructed without the
/// parser (no KatLang source form exists for it). Used to pin the behavior of
/// internal nodes such as <see cref="Expr.SequenceConstruct"/> on both sides
/// of the Lean/C# differential, and to detect accidental exposure of internal
/// node semantics to surface syntax via the declared surface counterpart.
/// </summary>
public sealed record InternalNodeCase(
    string Id,
    string Description,
    Func<Expr> RootOutput,
    string LeanRootExpr,
    string SurfaceCounterpart,
    InternalNodeRelation Relation);

/// <summary>Declared relation between an internal-node case and its surface counterpart.</summary>
public enum InternalNodeRelation
{
    /// <summary>The internal node intentionally observes the SAME value as the surface form.</summary>
    IntentionallyEqual,

    /// <summary>
    /// The internal node intentionally observes a DIFFERENT value than the
    /// surface form (e.g. `Expr.SequenceConstruct` drops `()` leaves, which
    /// written parentheses never do). If the two ever become equal, either
    /// surface syntax started routing through the internal node or the
    /// internal semantics changed — both must be reviewed.
    /// </summary>
    IntentionallyDifferent,
}

/// <summary>
/// Bounded small-state corpus: structurally rich values crossed with receiver
/// templates covering every boundary operation (capture, calls, collecting and
/// mixed collecting binding, deconstruction, spread, indexing, equality, count,
/// dot access, collection builtins, and re-entry), plus targeted specials.
/// </summary>
public static class SemanticExplorerCorpus
{
    private static ExplorerValue N(int n) => new ExplorerValue.Num(n);
    private static readonly ExplorerValue E = new ExplorerValue.Empty();
    private static ExplorerValue S(params ExplorerValue[] items) => new ExplorerValue.Seq(items);
    private static ExplorerValue W(ExplorerValue inner) => new ExplorerValue.Wrap(inner);
    private static ExplorerValue L(params ExplorerValue[] items) => new ExplorerValue.ListOf(items);

    /// <summary>The bounded value space (deduplicated by source form).</summary>
    public static readonly IReadOnlyList<(string Id, ExplorerValue Value)> Values =
    [
        ("e", E),                              // ()
        ("n0", N(0)),                          // 0
        ("n1", N(1)),                          // 1
        ("p1", W(N(1))),                       // (1)
        ("p12", S(N(1), N(2))),                // (1, 2)
        ("p123", S(N(1), N(2), N(3))),         // (1, 2, 3)
        ("pee", S(E, E)),                      // ((), ())
        ("pe1", S(E, N(1))),                   // ((), 1)
        ("p1e", S(N(1), E)),                   // (1, ())
        ("p12_3", S(S(N(1), N(2)), N(3))),     // ((1, 2), 3)
        ("p12_34", S(S(N(1), N(2)), S(N(3), N(4)))), // ((1, 2), (3, 4))
        ("pe_12", S(E, S(N(1), N(2)))),        // ((), (1, 2))
        ("ppe1_2", S(S(E, N(1)), N(2))),       // (((), 1), 2)
        ("p12_e", S(S(N(1), N(2)), E)),        // ((1, 2), ())
        ("ppe", W(E)),                         // (())
        ("pp1", W(W(N(1)))),                   // ((1))
        ("ppp12", W(W(S(N(1), N(2))))),        // (((1, 2)))
        // Exact immutable list values: empty, singleton, multi, list-in-list,
        // sequence-in-list, list-in-sequence, and wrapped list (redundant
        // parens around a list still canonicalize away).
        ("le", L()),                           // []
        ("l7", L(N(7))),                       // [7]
        ("l12", L(N(1), N(2))),                // [1, 2]
        ("l12_3", L(L(N(1), N(2)), N(3))),     // [[1, 2], 3]
        ("lle", L(L())),                       // [[]]
        ("l_e", L(E)),                         // [()]
        ("l_p12", L(S(N(1), N(2)))),           // [(1, 2)]
        ("p_l12", S(L(N(1), N(2)), N(3))),     // ([1, 2], 3)
        ("pl1", W(L(N(1)))),                   // ([1])
    ];

    // ----- Lean program snippets ---------------------------------------------

    private static string LProg(IEnumerable<string> props, IEnumerable<string> outputs)
        => $".block (alg [] [] [{string.Join(", ", props)}] [{string.Join(", ", outputs)}])";

    private static string LVal(string name, string leanExpr)
        => $"privateProp \"{name}\" (alg [] [] [] [{leanExpr}])";

    private const string LIdentity = "privateProp \"I\" (alg [\"a\"] [] [] [.param \"a\"])";
    private const string LFixed = "privateProp \"F\" (alg [\"a\"] [] [] [.param \"a\"])";
    private const string LCollectingF =
        "privateProp \"F\" (algWithParameters [{ name := \"a\", kind := .collecting }] [] [] [.param \"a\"])";
    private const string LCollectingG =
        "privateProp \"G\" (algWithParameters [{ name := \"a\", kind := .collecting }] [] [] [.param \"a\"])";

    private static string LMixedFront(string bodyParam) =>
        $"privateProp \"F\" (algWithParameters [{{ name := \"h\" }}, {{ name := \"t\", kind := .collecting }}] [] [] [.param \"{bodyParam}\"])";

    private static string LMixedBack(string bodyParam) =>
        $"privateProp \"F\" (algWithParameters [{{ name := \"t\", kind := .collecting }}, {{ name := \"z\" }}] [] [] [.param \"{bodyParam}\"])";

    private static string LContainer(string leanExpr) =>
        $"privateProp \"A\" (alg [] [] [publicProp \"X\" (alg [] [] [] [{leanExpr}])] [])";

    private static string LCall(string callee, params string[] args)
        => $".call (.resolve \"{callee}\") (alg [] [] [] [{string.Join(", ", args)}])";

    /// <summary>
    /// Parser-elaborated assignment deconstruction: RHS evaluated once into a
    /// shared property, each target bound through an inline sequence-value
    /// parameter pattern that opens the shared value (Lean: T:9300-style).
    /// </summary>
    private static string LDecon(string rhsLeanExpr, string[] targets, int collectingIndex, string observed)
    {
        var captures = targets.Select((t, i) => i == collectingIndex
            ? $".capture {{ name := \"{t}\", kind := .collecting }}"
            : $".capture {{ name := \"{t}\" }}");
        var pattern = $".sequenceValue [{string.Join(", ", captures)}]";
        var helper = $".block (algWithParameterPatterns [{pattern}] [] [] [.param \"{observed}\"])";
        return LVal("d", rhsLeanExpr)
            + ", "
            + $"privateProp \"{observed}\" (alg [] [] [] [.call ({helper}) (alg [] [] [] [.resolve \"d\"])])";
    }

    // ----- Receiver templates ------------------------------------------------

    private sealed record Template(
        string Id,
        Func<ExplorerValue, string> Source,
        Func<ExplorerValue, string?> Lean);

    private static readonly IReadOnlyList<Template> Templates =
    [
        new("root",
            v => v.Source,
            v => LProg([], [v.LeanExpr])),
        new("capture",
            v => $"x = {v.Source}\nx",
            v => LProg([LVal("x", v.LeanExpr)], [".resolve \"x\""])),
        new("captureCall",
            v => $"x = {v.Source}\nx()",
            v => LProg([LVal("x", v.LeanExpr)], [".call (.resolve \"x\") (alg [] [] [] [])"])),
        new("dotAccess",
            v => $"A = {{\n    X = {v.Source}\n}}\nA.X",
            v => LProg([LContainer(v.LeanExpr)], [".dotCall (.resolve \"A\") \"X\" none"])),
        new("dotAccessCall",
            v => $"A = {{\n    X = {v.Source}\n}}\nA.X()",
            v => LProg([LContainer(v.LeanExpr)], [".dotCall (.resolve \"A\") \"X\" (some (alg [] [] [] []))"])),
        new("fixed",
            v => $"F(a) = a\nF({v.Source})",
            v => LProg([LFixed], [LCall("F", v.LeanExpr)])),
        new("fixedSpread",
            v => $"F(a) = a\nF({v.Source}*)",
            v => LProg([LFixed], [LCall("F", $".sequenceSpread {v.LeanExpr}")])),
        new("collecting",
            v => $"F(*a) = a\nF({v.Source})",
            v => LProg([LCollectingF], [LCall("F", v.LeanExpr)])),
        new("collectingSpread",
            v => $"F(*a) = a\nF({v.Source}*)",
            v => LProg([LCollectingF], [LCall("F", $".sequenceSpread {v.LeanExpr}")])),
        new("collectingViaProp",
            v => $"F(*a) = a\nx = {v.Source}\nF(x)",
            v => LProg([LCollectingF, LVal("x", v.LeanExpr)], [LCall("F", ".resolve \"x\"")])),
        new("mixed_h",
            v => $"F(h, *t) = h\nF({v.Source}*)",
            v => LProg([LMixedFront("h")], [LCall("F", $".sequenceSpread {v.LeanExpr}")])),
        new("mixed_t",
            v => $"F(h, *t) = t\nF({v.Source}*)",
            v => LProg([LMixedFront("t")], [LCall("F", $".sequenceSpread {v.LeanExpr}")])),
        new("mixedBack_t",
            v => $"F(*t, z) = t\nF({v.Source}*)",
            v => LProg([LMixedBack("t")], [LCall("F", $".sequenceSpread {v.LeanExpr}")])),
        new("mixedBack_z",
            v => $"F(*t, z) = z\nF({v.Source}*)",
            v => LProg([LMixedBack("z")], [LCall("F", $".sequenceSpread {v.LeanExpr}")])),
        new("deconPair_x",
            v => $"x, y = {v.Source}\nx",
            v => LProg([LDecon(v.LeanExpr, ["x", "y"], -1, "x")], [".resolve \"x\""])),
        new("deconPair_y",
            v => $"x, y = {v.Source}\ny",
            v => LProg([LDecon(v.LeanExpr, ["x", "y"], -1, "y")], [".resolve \"y\""])),
        new("deconPairSpread_x",
            v => $"x, y = {v.Source}*\nx",
            v => LProg([LDecon($".sequenceSpread {v.LeanExpr}", ["x", "y"], -1, "x")], [".resolve \"x\""])),
        new("deconCollect_t",
            v => $"h, *t = {v.Source}\nt",
            v => LProg([LDecon(v.LeanExpr, ["h", "t"], 1, "t")], [".resolve \"t\""])),
        new("deconCollectSpread_t",
            v => $"h, *t = {v.Source}*\nt",
            v => LProg([LDecon($".sequenceSpread {v.LeanExpr}", ["h", "t"], 1, "t")], [".resolve \"t\""])),
        new("deconPrefix_p",
            v => $"*p, z = {v.Source}\np",
            v => LProg([LDecon(v.LeanExpr, ["p", "z"], 0, "p")], [".resolve \"p\""])),
        new("deconPrefix_z",
            v => $"*p, z = {v.Source}\nz",
            v => LProg([LDecon(v.LeanExpr, ["p", "z"], 0, "z")], [".resolve \"z\""])),
        new("seqWrapPair",
            v => $"({v.Source}, 99)",
            v => LProg([], [$".block (alg [] [] [] [{v.LeanExpr}, .num 99])"])),
        new("seqWrapSolo",
            v => $"({v.Source})",
            v => LProg([], [$".block (alg [] [] [] [{v.LeanExpr}])"])),
        new("spreadRoot",
            v => $"{v.Source}*",
            v => LProg([], [$".sequenceSpread {v.LeanExpr}"])),
        new("spreadInSeq",
            v => $"({v.Source}*, 99)",
            v => LProg([], [$".block (alg [] [] [] [.sequenceSpread {v.LeanExpr}, .num 99])"])),
        new("count",
            v => $"count({v.Source})",
            v => LProg([], [LCall("count", v.LeanExpr)])),
        new("countSpread",
            v => $"count({v.Source}*)",
            v => LProg([], [LCall("count", $".sequenceSpread {v.LeanExpr}")])),
        new("dotCount",
            v => $"x = {v.Source}\nx.count",
            v => LProg([LVal("x", v.LeanExpr)], [".dotCall (.resolve \"x\") \"count\" none"])),
        new("literalDotCount",
            v => $"({v.Source}).count",
            v => LProg([], [$".dotCall (.block (alg [] [] [] [{v.LeanExpr}])) \"count\" none"])),
        new("index0",
            v => $"x = {v.Source}\nx:0",
            v => LProg([LVal("x", v.LeanExpr)], [".index (.resolve \"x\") (.num 0)"])),
        new("index1",
            v => $"x = {v.Source}\nx:1",
            v => LProg([LVal("x", v.LeanExpr)], [".index (.resolve \"x\") (.num 1)"])),
        new("indexBig",
            v => $"x = {v.Source}\nx:9",
            v => LProg([LVal("x", v.LeanExpr)], [".index (.resolve \"x\") (.num 9)"])),
        // `x:-1` is a C#-parser-level rejection (a negative selector never forms);
        // there is no comparable Lean program, so this case is C#-only.
        new("indexNeg",
            v => $"x = {v.Source}\nx:-1",
            _ => null),
        new("eqSelf",
            v => $"x = {v.Source}\nx == x",
            v => LProg([LVal("x", v.LeanExpr)], [".binary .eq (.resolve \"x\") (.resolve \"x\")"])),
        new("neqSelf",
            v => $"x = {v.Source}\nx != x",
            v => LProg([LVal("x", v.LeanExpr)], [".binary .ne (.resolve \"x\") (.resolve \"x\")"])),
        new("eqIdentity",
            v => $"I(a) = a\nx = {v.Source}\nx == I(x)",
            v => LProg(
                [LIdentity, LVal("x", v.LeanExpr)],
                [$".binary .eq (.resolve \"x\") ({LCall("I", ".resolve \"x\"")})"])),
        new("identity",
            v => $"I(a) = a\nx = {v.Source}\nI(x)",
            v => LProg([LIdentity, LVal("x", v.LeanExpr)], [LCall("I", ".resolve \"x\"")])),
        new("identityTwice",
            v => $"I(a) = a\nx = {v.Source}\nI(I(x))",
            v => LProg([LIdentity, LVal("x", v.LeanExpr)], [LCall("I", LCall("I", ".resolve \"x\""))])),
        new("propChain",
            v => $"P = {v.Source}\nQ = P\nQ",
            v => LProg(
                [LVal("P", v.LeanExpr), "privateProp \"Q\" (alg [] [] [] [.resolve \"P\"])"],
                [".resolve \"Q\""])),
        new("take1",
            v => $"take({v.Source}, 1)",
            v => LProg([], [LCall("take", v.LeanExpr, ".num 1")])),
        new("take9",
            v => $"take({v.Source}, 9)",
            v => LProg([], [LCall("take", v.LeanExpr, ".num 9")])),
        new("skip1",
            v => $"skip({v.Source}, 1)",
            v => LProg([], [LCall("skip", v.LeanExpr, ".num 1")])),
        new("distinct",
            v => $"distinct({v.Source})",
            v => LProg([], [LCall("distinct", v.LeanExpr)])),
        new("order",
            v => $"order({v.Source})",
            v => LProg([], [LCall("order", v.LeanExpr)])),
        new("mapId",
            v => $"M(a) = a\nmap({v.Source}, M)",
            v => LProg(["privateProp \"M\" (alg [\"a\"] [] [] [.param \"a\"])"], [LCall("map", v.LeanExpr, ".resolve \"M\"")])),
        new("filterKeep",
            v => $"T(a) = 1\nfilter({v.Source}, T)",
            v => LProg(["privateProp \"T\" (alg [\"a\"] [] [] [.num 1])"], [LCall("filter", v.LeanExpr, ".resolve \"T\"")])),
        new("atoms",
            v => $"atoms({v.Source})",
            v => LProg([], [LCall("atoms", v.LeanExpr)])),
        new("takeCapture",
            v => $"x = take({v.Source}, 1)\nx",
            v => LProg(
                [$"privateProp \"x\" (alg [] [] [] [{LCall("take", v.LeanExpr, ".num 1")}])"],
                [".resolve \"x\""])),
        new("takeIdentity",
            v => $"I(a) = a\nI(take({v.Source}, 1))",
            v => LProg([LIdentity], [LCall("I", LCall("take", v.LeanExpr, ".num 1"))])),
        new("takeCount",
            v => $"count(take({v.Source}, 1))",
            v => LProg([], [LCall("count", LCall("take", v.LeanExpr, ".num 1"))])),
        new("takeCollecting",
            v => $"G(*a) = a\nG(take({v.Source}, 1))",
            v => LProg([LCollectingG], [LCall("G", LCall("take", v.LeanExpr, ".num 1"))])),
    ];

    // ----- Specials -----------------------------------------------------------

    private static readonly IReadOnlyList<(string Id, string Source, string? Lean)> Specials =
    [
        ("multiProp", "P = 1, 2, 3\nP",
            LProg(["privateProp \"P\" (alg [] [] [] [.num 1, .num 2, .num 3])"], [".resolve \"P\""])),
        ("multiPropCall", "P = 1, 2, 3\nP()",
            LProg(["privateProp \"P\" (alg [] [] [] [.num 1, .num 2, .num 3])"], [".call (.resolve \"P\") (alg [] [] [] [])"])),
        ("multiPropCount", "P = 1, 2, 3\ncount(P)",
            LProg(["privateProp \"P\" (alg [] [] [] [.num 1, .num 2, .num 3])"], [LCall("count", ".resolve \"P\"")])),
        ("multiPropDotCount", "P = 1, 2, 3\nP.count",
            LProg(["privateProp \"P\" (alg [] [] [] [.num 1, .num 2, .num 3])"], [".dotCall (.resolve \"P\") \"count\" none"])),
        ("multiPropDot", "A = {\n    X = 1, 2, 3\n}\nA.X",
            LProg(["privateProp \"A\" (alg [] [] [publicProp \"X\" (alg [] [] [] [.num 1, .num 2, .num 3])] [])"],
                [".dotCall (.resolve \"A\") \"X\" none"])),
        ("multiPropIndex0", "P = 1, 2, 3\nP:0",
            LProg(["privateProp \"P\" (alg [] [] [] [.num 1, .num 2, .num 3])"], [".index (.resolve \"P\") (.num 0)"])),
        ("multiPropEq", "P = 1, 2, 3\nP == (1, 2, 3)",
            LProg(["privateProp \"P\" (alg [] [] [] [.num 1, .num 2, .num 3])"],
                [".binary .eq (.resolve \"P\") (.block (alg [] [] [] [.num 1, .num 2, .num 3]))"])),
        ("multiCollecting", "F(*a) = a\nF(1, 2, 3)",
            LProg([LCollectingF], [LCall("F", ".num 1", ".num 2", ".num 3")])),
        ("multiCollectingCount", "F(*a) = a\ncount(F(1, 2, 3))",
            LProg([LCollectingF], [LCall("count", LCall("F", ".num 1", ".num 2", ".num 3"))])),
        ("collectingEmptyCall", "F(*a) = a\nF()",
            LProg([LCollectingF], [".call (.resolve \"F\") (alg [] [] [] [])"])),
        ("collectingFwdSum", "F(*a) = sum(a)\nF(1, 2, 3)",
            LProg(["privateProp \"F\" (algWithParameters [{ name := \"a\", kind := .collecting }] [] [] [.call (.resolve \"sum\") (alg [] [] [] [.param \"a\"])])"],
                [LCall("F", ".num 1", ".num 2", ".num 3")])),
        ("collectingFwdSpread", "F(*a) = G(a*)\nG(*b) = b\nF(1, 2, 3)",
            LProg(
                ["privateProp \"F\" (algWithParameters [{ name := \"a\", kind := .collecting }] [] [] [.call (.resolve \"G\") (alg [] [] [] [.sequenceSpread (.param \"a\")])])",
                 "privateProp \"G\" (algWithParameters [{ name := \"b\", kind := .collecting }] [] [] [.param \"b\"])"],
                [LCall("F", ".num 1", ".num 2", ".num 3")])),
        ("collectingJoin", "F(*a) = a\nF((1, 2)*, (3, 4)*)",
            LProg([LCollectingF],
                [LCall("F",
                    ".sequenceSpread (.block (alg [] [] [] [.num 1, .num 2]))",
                    ".sequenceSpread (.block (alg [] [] [] [.num 3, .num 4]))")])),
        ("range13", "range(1, 3)", LProg([], [LCall("range", ".num 1", ".num 3")])),
        ("rangeCapture", "x = range(1, 3)\nx",
            LProg([$"privateProp \"x\" (alg [] [] [] [{LCall("range", ".num 1", ".num 3")}])"], [".resolve \"x\""])),
        ("rangeCount", "count(range(1, 3))", LProg([], [LCall("count", LCall("range", ".num 1", ".num 3"))])),
        ("rangeIndex0", "range(1, 3):0", LProg([], [$".index ({LCall("range", ".num 1", ".num 3")}) (.num 0)"])),
        ("takeOneSurvivorPair", "take(((1, 2), (3, 4)), 1)",
            LProg([], [LCall("take", PairOfPairs, ".num 1")])),
        ("takeOneSurvivorPairCount", "count(take(((1, 2), (3, 4)), 1))",
            LProg([], [LCall("count", LCall("take", PairOfPairs, ".num 1"))])),
        ("takeOneSurvivorPairEq", "take(((1, 2), (3, 4)), 1) == (1, 2)",
            LProg([], [$".binary .eq ({LCall("take", PairOfPairs, ".num 1")}) (.block (alg [] [] [] [.num 1, .num 2]))"])),
        ("skipToOnePair", "skip(((1, 2), (3, 4)), 1)",
            LProg([], [LCall("skip", PairOfPairs, ".num 1")])),
        ("distinctEmpties", "distinct((), ())",
            LProg([], [LCall("distinct", ".emptySequence 0", ".emptySequence 0")])),
        ("distinctPairsToOne", "distinct((1, 2), (1, 2))",
            LProg([], [LCall("distinct", "(.block (alg [] [] [] [.num 1, .num 2]))", "(.block (alg [] [] [] [.num 1, .num 2]))")])),
        ("takeEmpties", "take((), (), 2)",
            LProg([], [LCall("take", ".emptySequence 0", ".emptySequence 0", ".num 2")])),
        ("filterOneSurvivor", "Big(a) = a > 2\nfilter((1, 2, 3), Big)",
            LProg(["privateProp \"Big\" (alg [\"a\"] [] [] [.binary .gt (.param \"a\") (.num 2)])"],
                [LCall("filter", "(.block (alg [] [] [] [.num 1, .num 2, .num 3]))", ".resolve \"Big\"")])),
        ("filterOneSurvivorCount", "Big(a) = a > 2\ncount(filter((1, 2, 3), Big))",
            LProg(["privateProp \"Big\" (alg [\"a\"] [] [] [.binary .gt (.param \"a\") (.num 2)])"],
                [LCall("count", LCall("filter", "(.block (alg [] [] [] [.num 1, .num 2, .num 3]))", ".resolve \"Big\""))])),
        ("filterZeroSurvivors", "No(a) = 0\nfilter((1, 2, 3), No)",
            LProg(["privateProp \"No\" (alg [\"a\"] [] [] [.num 0])"],
                [LCall("filter", "(.block (alg [] [] [] [.num 1, .num 2, .num 3]))", ".resolve \"No\"")])),
        ("mapPairSwap", "Swap(a, b) = b, a\nmap(((1, 2), (3, 4)), Swap)",
            LProg(["privateProp \"Swap\" (alg [\"a\", \"b\"] [] [] [.param \"b\", .param \"a\"])"],
                [LCall("map", PairOfPairs, ".resolve \"Swap\"")])),
        ("mapPairSwapOk", "Swap(a, b) = (b, a)\nmap(((1, 2), (3, 4)), Swap)",
            LProg(["privateProp \"Swap\" (alg [\"a\", \"b\"] [] [] [.block (alg [] [] [] [.param \"b\", .param \"a\"])])"],
                [LCall("map", PairOfPairs, ".resolve \"Swap\"")])),
        ("mapToOne", "M(a) = a\nmap((7), M)",
            LProg(["privateProp \"M\" (alg [\"a\"] [] [] [.param \"a\"])"],
                [LCall("map", "(.block (alg [] [] [] [.num 7]))", ".resolve \"M\"")])),
        ("orderSingle", "order(5)", LProg([], [LCall("order", ".num 5")])),
        ("orderEmpty", "order(())", LProg([], [LCall("order", ".emptySequence 0")])),
        ("atomsNested", "atoms(((1, 2), (3, 4)))", LProg([], [LCall("atoms", PairOfPairs)])),
        ("emptyOpGreater", "() > 1", LProg([], [".binary .gt (.emptySequence 0) (.num 1)"])),
        ("emptyOpPlus", "() + 1", LProg([], [".binary .add (.emptySequence 0) (.num 1)"])),
        ("emptyOpBoth", "() + ()", LProg([], [".binary .add (.emptySequence 0) (.emptySequence 0)"])),
        ("emptyEqEmpty", "() == ()", LProg([], [".binary .eq (.emptySequence 0) (.emptySequence 0)"])),
        ("emptyEqNestedEmpty", "() == (())",
            LProg([], [".binary .eq (.emptySequence 0) (.block (alg [] [] [] [.emptySequence 0]))"])),
        ("emptyNeNestedEmpty", "() != (())",
            LProg([], [".binary .ne (.emptySequence 0) (.block (alg [] [] [] [.emptySequence 0]))"])),
        ("propBodyEmptySlot", "P = (), 99\nP",
            LProg(["privateProp \"P\" (alg [] [] [] [.emptySequence 0, .num 99])"], [".resolve \"P\""])),
        ("rootEmptySlots", "(), 99", LProg([], [".emptySequence 0", ".num 99"])),
        ("seqOfSpreadEmpty", "((()*), 1)",
            LProg([], [".block (alg [] [] [] [.block (alg [] [] [] [.sequenceSpread (.emptySequence 0)]), .num 1])"])),
        ("indexPairInSeq", "x = ((1, 2), (3, 4))\n(x:0, 99)",
            LProg([LVal("x", PairOfPairs)], [".block (alg [] [] [] [.index (.resolve \"x\") (.num 0), .num 99])"])),
        ("indexEmptyItemRoot", "x = ((), ())\nx:0",
            LProg([LVal("x", "(.block (alg [] [] [] [.emptySequence 0, .emptySequence 0]))")],
                [".index (.resolve \"x\") (.num 0)"])),
        ("indexCapturedEq", "x = ((1, 2), (3, 4))\ny = x:0\ny == (1, 2)",
            LProg(
                [LVal("x", PairOfPairs), "privateProp \"y\" (alg [] [] [] [.index (.resolve \"x\") (.num 0)])"],
                [".binary .eq (.resolve \"y\") (.block (alg [] [] [] [.num 1, .num 2]))"])),
        ("chainedListIndex", "x = [[1, 2], [3, 4]]\nx:1:0",
            LProg(
                [LVal("x", "(.listLiteral [.listLiteral [.num 1, .num 2], .listLiteral [.num 3, .num 4]])")],
                [".index (.index (.resolve \"x\") (.num 1)) (.num 0)"])),
        ("listIndexCapturedEq", "x = [[1, 2]]\ny = x:0\ny == [1, 2]",
            LProg(
                [LVal("x", "(.listLiteral [.listLiteral [.num 1, .num 2]])"),
                 "privateProp \"y\" (alg [] [] [] [.index (.resolve \"x\") (.num 0)])"],
                [".binary .eq (.resolve \"y\") (.listLiteral [.num 1, .num 2])"])),
        ("listIndexSelectedKindEqFalse", "[[1, 2]]:0 == (1, 2)",
            LProg([],
                [".binary .eq (.index (.listLiteral [.listLiteral [.num 1, .num 2]]) (.num 0)) (.block (alg [] [] [] [.num 1, .num 2]))"])),
        ("orderIndex0", "[3, 1, 2].order:0",
            LProg([],
                [".index (.dotCall (.listLiteral [.num 3, .num 1, .num 2]) \"order\" none) (.num 0)"])),
        ("nestedWrittenArg", "F(a, b) = a\nF(((1, 2)), 3)",
            LProg(["privateProp \"F\" (alg [\"a\", \"b\"] [] [] [.param \"a\"])"],
                [LCall("F", "(.block (alg [] [] [] [(.block (alg [] [] [] [.num 1, .num 2]))]))", ".num 3")])),
        ("writtenSlotArity", "F(a, b) = a + b\nF(((1, 2)))",
            LProg(["privateProp \"F\" (alg [\"a\", \"b\"] [] [] [.binary .add (.param \"a\") (.param \"b\")])"],
                [LCall("F", "(.block (alg [] [] [] [(.block (alg [] [] [] [.num 1, .num 2]))]))")])),
        ("mixedSingleGrouped", "F(x, *y, z) = y\nA = (1, 2, 3, 4)\nF(A)",
            LProg(
                ["privateProp \"F\" (algWithParameters [{ name := \"x\" }, { name := \"y\", kind := .collecting }, { name := \"z\" }] [] [] [.param \"y\"])",
                 LVal("A", "(.block (alg [] [] [] [.num 1, .num 2, .num 3, .num 4]))")],
                [LCall("F", ".resolve \"A\"")])),
        ("sumEmpty", "sum(())", LProg([], [LCall("sum", ".emptySequence 0")])),
        // Spread-with-sibling slots inside a written sequence literal, and the
        // same shape observed through the non-counted evaluation paths (value
        // position of ==, spread operand, root rows). These pin the July 2026
        // fix that made Lean's evalAlgOutputCore the value projection of the
        // counted core (spread slots splice; a written `()` slot stays visible).
        ("spreadWithSiblingSeqLiteral", "x = (1, 2)\n(x*, 99)",
            LProg([LVal("x", Pair12)],
                [".block (alg [] [] [] [.sequenceSpread (.resolve \"x\"), .num 99])"])),
        ("spreadEmptyBetween", "(1*, (), 2*)",
            LProg([], [".block (alg [] [] [] [.sequenceSpread (.num 1), .emptySequence 0, .sequenceSpread (.num 2)])"])),
        ("rootSpreadExtra", "A = (1, 2)\nA*, 99",
            LProg([LVal("A", Pair12)], [".sequenceSpread (.resolve \"A\")", ".num 99"])),
        ("spreadOfSpreadSeqLiteral", "A = (1, 2)\n((A*, 99))*",
            LProg([LVal("A", Pair12)],
                [".sequenceSpread (.block (alg [] [] [] [(.block (alg [] [] [] [.sequenceSpread (.resolve \"A\"), .num 99]))]))"])),
        ("eqSpreadSeqLiteral", "P = (1, 2)\n(P*, 99) == (1, 2, 99)",
            LProg([LVal("P", Pair12)],
                [".binary .eq (.block (alg [] [] [] [.sequenceSpread (.resolve \"P\"), .num 99])) (.block (alg [] [] [] [.num 1, .num 2, .num 99]))"])),
        ("loopSpreadHistoryFlat",
            "Step((*history), previous) = (history*, previous + 1), previous + 1\nStep.repeat(2, (1, 2), 2):0",
            LProg(
                ["privateProp \"Step\" (algWithParameterPatterns [.sequenceValue [.capture { name := \"history\", kind := .collecting }], .capture { name := \"previous\" }] [] [] [.block (alg [] [] [] [.sequenceSpread (.param \"history\"), .binary .add (.param \"previous\") (.num 1)]), .binary .add (.param \"previous\") (.num 1)])"],
                [".index (.dotCall (.resolve \"Step\") \"repeat\" (some (alg [] [] [] [.num 2, " + Pair12 + ", .num 2]))) (.num 0)"])),
        ("ifBranchSeq", "if(1, (1, 2), 3)",
            LProg([], [LCall("if", ".num 1", "(.block (alg [] [] [] [.num 1, .num 2]))", ".num 3")])),
        ("divZero", "1 / 0", LProg([], [".binary .div (.num 1) (.num 0)"])),
        ("negativeResult", "0 - 1", LProg([], [".binary .sub (.num 0) (.num 1)"])),
        ("strEq", "'ab' == 'ab'", LProg([], [".binary .eq (.stringLiteral \"ab\") (.stringLiteral \"ab\")"])),
        ("strCount", "count('ab')", LProg([], [LCall("count", "(.stringLiteral \"ab\")")])),
        ("strCapture", "x = 'ab'\nx", LProg([LVal("x", "(.stringLiteral \"ab\")")], [".resolve \"x\""])),
        // Exact list values: spread inside list literals, list/sequence kind
        // distinctions, empty-list-spread neutrality, and list arguments at
        // call boundaries. These pin the July 2026 list-value semantics.
        ("listSpreadOfSeqProp", "A = 1, 2, 3\n[A*]",
            LProg(["privateProp \"A\" (alg [] [] [] [.num 1, .num 2, .num 3])"],
                [".listLiteral [.sequenceSpread (.resolve \"A\")]"])),
        ("listSpreadBetween", "A = 1, 2, 3\n[0, A*, 4]",
            LProg(["privateProp \"A\" (alg [] [] [] [.num 1, .num 2, .num 3])"],
                [".listLiteral [.num 0, .sequenceSpread (.resolve \"A\"), .num 4]"])),
        ("listOfLists", "A = [1, 2]\nB = [3, 4]\n[A, B]",
            LProg([LVal("A", List12), LVal("B", List34)],
                [".listLiteral [.resolve \"A\", .resolve \"B\"]"])),
        ("listSpreadConcat", "A = [1, 2]\nB = [3, 4]\n[A*, B*]",
            LProg([LVal("A", List12), LVal("B", List34)],
                [".listLiteral [.sequenceSpread (.resolve \"A\"), .sequenceSpread (.resolve \"B\")]"])),
        ("listMixedSpread", "A = [1, 2]\nB = [3, 4]\n[A, B*]",
            LProg([LVal("A", List12), LVal("B", List34)],
                [".listLiteral [.resolve \"A\", .sequenceSpread (.resolve \"B\")]"])),
        ("listEmptyListSpreadBetween", "[1, []*, 2]",
            LProg([], [".listLiteral [.num 1, .sequenceSpread (.listLiteral []), .num 2]"])),
        ("listEmptySeqSpreadBetween", "[1, ()*, 2]",
            LProg([], [".listLiteral [.num 1, .sequenceSpread (.emptySequence 0), .num 2]"])),
        ("listNeSeq", "[1, 2] == (1, 2)",
            LProg([], [".binary .eq (.listLiteral [.num 1, .num 2]) (.block (alg [] [] [] [.num 1, .num 2]))"])),
        ("listEmptyNeEmptySeq", "[] == ()",
            LProg([], [".binary .eq (.listLiteral []) (.emptySequence 0)"])),
        ("listSingletonNeItem", "[7] == 7",
            LProg([], [".binary .eq (.listLiteral [.num 7]) (.num 7)"])),
        ("listWrapCanonicalizes", "([1, 2]) == [1, 2]",
            LProg([], [".binary .eq (.block (alg [] [] [] [.listLiteral [.num 1, .num 2]])) (.listLiteral [.num 1, .num 2])"])),
        ("listSpreadCaptureRoundTrip", "A = [1, 2, 3]\nB = A*\nB == (1, 2, 3)",
            LProg(
                [LVal("A", "(.listLiteral [.num 1, .num 2, .num 3])"),
                 "privateProp \"B\" (alg [] [] [] [.sequenceSpread (.resolve \"A\")])"],
                [".binary .eq (.resolve \"B\") (.block (alg [] [] [] [.num 1, .num 2, .num 3]))"])),
        ("listCollectingNotSequenceKind", "x, *rest = [1, 2, 3]\nrest == (2, 3)",
            LProg(
                [LDecon("(.listLiteral [.num 1, .num 2, .num 3])", ["x", "rest"], 1, "rest")],
                [".binary .eq (.resolve \"rest\") (.block (alg [] [] [] [.num 2, .num 3]))"])),
        ("listCollectingCollectsExactList", "x, *rest = [1, 2, 3]\nrest == [2, 3]",
            LProg(
                [LDecon("(.listLiteral [.num 1, .num 2, .num 3])", ["x", "rest"], 1, "rest")],
                [".binary .eq (.resolve \"rest\") (.listLiteral [.num 2, .num 3])"])),
        ("implicitForwardOrdinarySource", "Target(*items) = items\nUse(items) = Target\nUse([1, 2])",
            LProg(
                ["privateProp \"Target\" (algWithParameters [{ name := \"items\", kind := .collecting }] [] [] [.param \"items\"])",
                 "privateProp \"Use\" (alg [\"items\"] [] [] [.call (.resolve \"Target\") (alg [] [] [] [.param \"items\"])])"],
                [LCall("Use", "(.listLiteral [.num 1, .num 2])")])),
        ("callbackSingleCollectingMap", "Collect(*items) = items\n[7].map(Collect)",
            LProg(
                ["privateProp \"Collect\" (algWithParameters [{ name := \"items\", kind := .collecting }] [] [] [.param \"items\"])"],
                [".dotCall (.listLiteral [.num 7]) \"map\" (some (alg [] [] [] [.resolve \"Collect\"]))"])),
        ("callbackMixedCollectingRow", "F(first, *middle, last) = middle\n[(1, 2, 3, 4)].map(F)",
            LProg(
                ["privateProp \"F\" (algWithParameters [{ name := \"first\" }, { name := \"middle\", kind := .collecting }, { name := \"last\" }] [] [] [.param \"middle\"])"],
                [".dotCall (.listLiteral [.block (alg [] [] [] [.num 1, .num 2, .num 3, .num 4])]) \"map\" (some (alg [] [] [] [.resolve \"F\"]))"])),
        ("listInSeqSpreadKeepsList", "A = [1, 2]\n(A, 9)*",
            LProg([LVal("A", List12)],
                [".sequenceSpread (.block (alg [] [] [] [.resolve \"A\", .num 9]))"])),
        ("listFixedCallBoundary", "F(a, b) = a\nF([1, 2], 3)",
            LProg(["privateProp \"F\" (alg [\"a\", \"b\"] [] [] [.param \"a\"])"],
                [LCall("F", List12, ".num 3")])),
        ("listCollectingSpreadCall", "F(*a) = a\nA = [1, 2]\nF(A*, 9)",
            LProg([LCollectingF, LVal("A", List12)],
                [LCall("F", ".sequenceSpread (.resolve \"A\")", ".num 9")])),
        // C#-only parse-level cases (no comparable Lean program).
        ("trailingComma", "(3,)", null),
        ("spreadAsBinaryOperand", "A = (1, 2)\nA* == A*", null),
        ("semicolonSeparator", "1 ; 2", null),
        ("listUnterminated", "[1, 2", null),
        ("listDefinitionInside", "[x = 1]", null),
        ("listLoneCollectingAssignment", "*items = [1, 2, 3]",
            LProg(
                [LDecon("(.listLiteral [.num 1, .num 2, .num 3])", ["items"], 0, "items")],
                [])),
    ];

    private const string PairOfPairs =
        "(.block (alg [] [] [] [(.block (alg [] [] [] [.num 1, .num 2])), (.block (alg [] [] [] [.num 3, .num 4]))]))";

    private const string Pair12 = "(.block (alg [] [] [] [.num 1, .num 2]))";

    private const string List12 = "(.listLiteral [.num 1, .num 2])";

    private const string List34 = "(.listLiteral [.num 3, .num 4])";

    // ----- Direct internal-node cases (Expr.SequenceConstruct) -----------------
    //
    // Expr.SequenceConstruct is an INTERNAL node: the parser never produces it
    // (see SequenceConstructContainmentTests), and its value evaluation drops
    // `()` leaves — unlike written parentheses, which always keep a non-spread
    // `()` visible. These cases pin that internal behavior on both sides of
    // the Lean/C# differential and declare, per case, whether it matches the
    // equivalent surface program. A "differs" case becoming equal means the
    // internal semantics leaked into surface syntax (or vice versa).

    private static Expr ScNum(int n) => new Expr.Num(n);
    private static Expr ScEmpty() => new Expr.EmptySequence(0);

    private static Expr ScBlock(params Expr[] outputs) => new Expr.Block(new Algorithm.User(
        Parent: null, Parameters: [], Opens: [], Properties: [], Output: outputs));

    private static Expr Sc(params Expr[] leaves)
        => leaves.Aggregate((left, right) => new Expr.SequenceConstruct(left, right));

    private static Expr ScCall(string builtin, params Expr[] args) => new Expr.Call(
        new Expr.Resolve(builtin),
        new Algorithm.User(Parent: null, Parameters: [], Opens: [], Properties: [], Output: [.. args]));

    private const string LScPair12 = "(.block (alg [] [] [] [.num 1, .num 2]))";

    public static IReadOnlyList<InternalNodeCase> InternalNodeCases() =>
    [
        new("sc_e_1", "SequenceConstruct[(), 1] drops the () leaf and singleton-collapses",
            () => Sc(ScEmpty(), ScNum(1)),
            ".sequenceConstruct (.emptySequence 0) (.num 1)",
            "((), 1)", InternalNodeRelation.IntentionallyDifferent),
        new("sc_1_e", "SequenceConstruct[1, ()] drops the () leaf and singleton-collapses",
            () => Sc(ScNum(1), ScEmpty()),
            ".sequenceConstruct (.num 1) (.emptySequence 0)",
            "(1, ())", InternalNodeRelation.IntentionallyDifferent),
        new("sc_e_e", "SequenceConstruct[(), ()] drops both () leaves to the empty sequence",
            () => Sc(ScEmpty(), ScEmpty()),
            ".sequenceConstruct (.emptySequence 0) (.emptySequence 0)",
            "((), ())", InternalNodeRelation.IntentionallyDifferent),
        new("sc_p12_e", "SequenceConstruct[(1,2), ()] drops () and collapses to the pair",
            () => Sc(ScBlock(ScNum(1), ScNum(2)), ScEmpty()),
            $".sequenceConstruct {LScPair12} (.emptySequence 0)",
            "((1, 2), ())", InternalNodeRelation.IntentionallyDifferent),
        new("sc_e_p12", "SequenceConstruct[(), (1,2)] drops () and collapses to the pair",
            () => Sc(ScEmpty(), ScBlock(ScNum(1), ScNum(2))),
            $".sequenceConstruct (.emptySequence 0) {LScPair12}",
            "((), (1, 2))", InternalNodeRelation.IntentionallyDifferent),
        new("sc_1_2", "SequenceConstruct[1, 2] matches written (1, 2)",
            () => Sc(ScNum(1), ScNum(2)),
            ".sequenceConstruct (.num 1) (.num 2)",
            "(1, 2)", InternalNodeRelation.IntentionallyEqual),
        new("sc_p12_p34", "SequenceConstruct of two pairs preserves nested structure",
            () => Sc(ScBlock(ScNum(1), ScNum(2)), ScBlock(ScNum(3), ScNum(4))),
            $".sequenceConstruct {LScPair12} (.block (alg [] [] [] [.num 3, .num 4]))",
            "((1, 2), (3, 4))", InternalNodeRelation.IntentionallyEqual),
        new("sc_spread_3", "SequenceConstruct[(1,2)*, 3] splices the spread leaf",
            () => Sc(new Expr.SequenceSpread(ScBlock(ScNum(1), ScNum(2))), ScNum(3)),
            $".sequenceConstruct (.sequenceSpread {LScPair12}) (.num 3)",
            "((1, 2)*, 3)", InternalNodeRelation.IntentionallyEqual),
        new("sc_count_arg", "count of the internal node observes the ()-dropped value",
            () => ScCall("count", Sc(ScEmpty(), ScNum(1))),
            ".call (.resolve \"count\") (alg [] [] [] [.sequenceConstruct (.emptySequence 0) (.num 1)])",
            "count(((), 1))", InternalNodeRelation.IntentionallyDifferent),
        new("sc_take_collection", "a SequenceConstruct collection argument binds like the grouped surface form",
            () => ScCall("take", Sc(ScNum(1), ScNum(2), ScNum(5)), ScNum(2)),
            ".call (.resolve \"take\") (alg [] [] [] [.sequenceConstruct (.sequenceConstruct (.num 1) (.num 2)) (.num 5), .num 2])",
            "take((1, 2, 5), 2)", InternalNodeRelation.IntentionallyEqual),
        new("sc_take_collection_empty", "() leaf vanishes from a SequenceConstruct collection argument (written parens keep it)",
            () => ScCall("take", Sc(ScEmpty(), ScNum(1), ScNum(2)), ScNum(2)),
            ".call (.resolve \"take\") (alg [] [] [] [.sequenceConstruct (.sequenceConstruct (.emptySequence 0) (.num 1)) (.num 2), .num 2])",
            "take(((), 1, 2), 2)", InternalNodeRelation.IntentionallyDifferent),
        new("sc_take_block_leaf", "a nested pair inside a SequenceConstruct collection argument stays one item",
            () => ScCall("take", Sc(ScNum(1), ScBlock(ScNum(2), ScNum(5))), ScNum(2)),
            ".call (.resolve \"take\") (alg [] [] [] [.sequenceConstruct (.num 1) (.block (alg [] [] [] [.num 2, .num 5])), .num 2])",
            "take((1, (2, 5)), 2)", InternalNodeRelation.IntentionallyEqual),
        new("sc_sum_arg", "sum of the internal node matches the grouped surface form",
            () => ScCall("sum", Sc(ScNum(1), ScNum(2))),
            ".call (.resolve \"sum\") (alg [] [] [] [.sequenceConstruct (.num 1) (.num 2)])",
            "sum((1, 2))", InternalNodeRelation.IntentionallyEqual),
    ];

    /// <summary>All generated cases (template x value cross product plus specials).</summary>
    public static IReadOnlyList<ExplorerCase> AllCases()
    {
        var cases = new List<ExplorerCase>();
        foreach (var template in Templates)
        {
            foreach (var (valueId, value) in Values)
            {
                cases.Add(new ExplorerCase(
                    $"{template.Id}__{valueId}",
                    template.Id,
                    valueId,
                    template.Source(value),
                    template.Lean(value)));
            }
        }

        foreach (var (id, source, lean) in Specials)
            cases.Add(new ExplorerCase($"special__{id}", "special", id, source, lean));

        return cases;
    }
}
