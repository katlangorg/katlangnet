namespace KatLang.Tests;

/// <summary>
/// Structural description of a generated semantic-explorer corpus value: the
/// written KatLang source form only. The equivalent Lean AST construction is
/// no longer authored here — every case's Lean program is derived from the
/// source's real elaborated AST through <see cref="LeanAstEncoder"/> (see
/// <see cref="SemanticExplorerCorpus.AllCases"/>), so parser rules such as
/// redundant-parenthesis normalization are never re-implemented in test code.
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
}

/// <summary>
/// One generated explorer case: a receiver template applied to a value.
/// <see cref="LeanProgram"/> is DERIVED — the Lean encoding of the source's
/// real elaborated AST (<see cref="LeanAstEncoder.EncodeProgram"/>), never
/// authored by hand — and is <c>null</c> exactly for the deliberate
/// parse-error probes (Lean has no surface parser).
/// </summary>
public sealed record ExplorerCase(
    string Id,
    string TemplateId,
    string ValueId,
    string Source,
    string? LeanProgram,
    string? LeanExclusionReason);

/// <summary>
/// One direct internal-AST-node case: a program constructed without the
/// parser (no KatLang source form exists for it). Used to pin the behavior of
/// internal nodes such as <see cref="Expr.SequenceConstruct"/> on both sides
/// of the Lean/C# differential, and to detect accidental exposure of internal
/// node semantics to surface syntax via the declared surface counterpart.
/// The Lean text for the case is derived from the SAME constructed AST the C#
/// side observes (<see cref="LeanAstEncoder.EncodeExpr"/>), so the two sides
/// cannot drift apart.
/// </summary>
public sealed record InternalNodeCase(
    string Id,
    string Description,
    Func<Expr> RootOutput,
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
    private static ExplorerValue S(params ExplorerValue[] items) =>
        new ExplorerValue.Seq(Array.AsReadOnly(items));
    private static ExplorerValue W(ExplorerValue inner) => new ExplorerValue.Wrap(inner);
    private static ExplorerValue L(params ExplorerValue[] items) =>
        new ExplorerValue.ListOf(Array.AsReadOnly(items));

    /// <summary>The bounded value space (deduplicated by source form).</summary>
    public static readonly IReadOnlyList<(string Id, ExplorerValue Value)> Values =
        Array.AsReadOnly<(string Id, ExplorerValue Value)>(
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
    ]);

    // ----- Receiver templates ------------------------------------------------
    //
    // Templates declare SOURCE text only. The Lean program of every case is
    // derived from the source's real elaborated AST by LeanAstEncoder in
    // AllCases(); a template with a LeanExclusionReason is a deliberate
    // parse-error probe with no comparable Lean program.

    private sealed record Template(
        string Id,
        Func<ExplorerValue, string> Source,
        string? LeanExclusionReason = null);

    private static readonly IReadOnlyList<Template> Templates =
    [
        new("root",
            v => v.Source),
        new("capture",
            v => $"x = {v.Source}\nx"),
        new("captureCall",
            v => $"x = {v.Source}\nx()"),
        new("dotAccess",
            v => $"A = {{\n    X = {v.Source}\n}}\nA.X"),
        new("dotAccessCall",
            v => $"A = {{\n    X = {v.Source}\n}}\nA.X()"),
        new("fixed",
            v => $"F(a) = a\nF({v.Source})"),
        new("fixedSpread",
            v => $"F(a) = a\nF({v.Source}*)"),
        new("collecting",
            v => $"F(*a) = a\nF({v.Source})"),
        new("collectingSpread",
            v => $"F(*a) = a\nF({v.Source}*)"),
        new("collectingViaProp",
            v => $"F(*a) = a\nx = {v.Source}\nF(x)"),
        new("mixed_h",
            v => $"F(h, *t) = h\nF({v.Source}*)"),
        new("mixed_t",
            v => $"F(h, *t) = t\nF({v.Source}*)"),
        new("mixedBack_t",
            v => $"F(*t, z) = t\nF({v.Source}*)"),
        new("mixedBack_z",
            v => $"F(*t, z) = z\nF({v.Source}*)"),
        new("deconPair_x",
            v => $"x, y = {v.Source}\nx"),
        new("deconPair_y",
            v => $"x, y = {v.Source}\ny"),
        new("deconPairSpread_x",
            v => $"x, y = {v.Source}*\nx"),
        new("deconCollect_t",
            v => $"h, *t = {v.Source}\nt"),
        new("deconCollectSpread_t",
            v => $"h, *t = {v.Source}*\nt"),
        new("deconPrefix_p",
            v => $"*p, z = {v.Source}\np"),
        new("deconPrefix_z",
            v => $"*p, z = {v.Source}\nz"),
        new("seqWrapPair",
            v => $"({v.Source}, 99)"),
        new("seqWrapSolo",
            v => $"({v.Source})"),
        new("spreadRoot",
            v => $"{v.Source}*"),
        new("spreadInSeq",
            v => $"({v.Source}*, 99)"),
        new("count",
            v => $"count({v.Source})"),
        new("countSpread",
            v => $"count({v.Source}*)"),
        new("dotCount",
            v => $"x = {v.Source}\nx.count"),
        new("literalDotCount",
            v => $"({v.Source}).count"),
        new("index0",
            v => $"x = {v.Source}\nx:0"),
        new("index1",
            v => $"x = {v.Source}\nx:1"),
        new("indexBig",
            v => $"x = {v.Source}\nx:9"),
        // `x:-1` is a C#-parser-level rejection (a negative selector never forms);
        // there is no comparable Lean program, so this case is C#-only.
        new("indexNeg",
            v => $"x = {v.Source}\nx:-1",
            LeanExclusionReason:
                "Negative selectors are rejected by KatLang's surface parser; Lean models only the elaborated AST."),
        new("eqSelf",
            v => $"x = {v.Source}\nx == x"),
        new("neqSelf",
            v => $"x = {v.Source}\nx != x"),
        new("eqIdentity",
            v => $"I(a) = a\nx = {v.Source}\nx == I(x)"),
        new("identity",
            v => $"I(a) = a\nx = {v.Source}\nI(x)"),
        new("identityTwice",
            v => $"I(a) = a\nx = {v.Source}\nI(I(x))"),
        new("propChain",
            v => $"P = {v.Source}\nQ = P\nQ"),
        new("take1",
            v => $"take({v.Source}, 1)"),
        new("take9",
            v => $"take({v.Source}, 9)"),
        new("skip1",
            v => $"skip({v.Source}, 1)"),
        new("distinct",
            v => $"distinct({v.Source})"),
        new("order",
            v => $"order({v.Source})"),
        new("mapId",
            v => $"M(a) = a\nmap({v.Source}, M)"),
        new("filterKeep",
            v => $"T(a) = 1\nfilter({v.Source}, T)"),
        new("atoms",
            v => $"atoms({v.Source})"),
        new("takeCapture",
            v => $"x = take({v.Source}, 1)\nx"),
        new("takeIdentity",
            v => $"I(a) = a\nI(take({v.Source}, 1))"),
        new("takeCount",
            v => $"count(take({v.Source}, 1))"),
        new("takeCollecting",
            v => $"G(*a) = a\nG(take({v.Source}, 1))"),
        // Stacked (repeated) spread `value**`: each extra written star crosses
        // one ordinary capture boundary (`items ∘ capture` per layer), so a
        // multi-item first spread is a fixed point and only a lone structured
        // item opens one more boundary. These three templates differentially
        // pin the repeated-spread chain at the root-emission, collecting-call,
        // and capture receivers across every corpus value (the hand-written
        // stackedSpread* CoreTests guards pin the law on selected values only).
        new("spreadRootStacked",
            v => $"{v.Source}**"),
        new("collectingStacked",
            v => $"F(*a) = a\nF({v.Source}**)"),
        new("captureStacked",
            v => $"x = {v.Source}**\nx"),
    ];

    // ----- Specials -----------------------------------------------------------
    //
    // Specials declare SOURCE text only (Lean programs are encoder-derived in
    // AllCases, like the templates); leanExclusionReason marks a deliberate
    // parse-error probe with no comparable Lean program and states why.

    private static (string Id, string Source, string? LeanExclusionReason) Special(
        string id, string source, string? leanExclusionReason = null) => (id, source, leanExclusionReason);

    private static readonly IReadOnlyList<(string Id, string Source, string? LeanExclusionReason)> Specials =
    [
        Special("multiProp", "P = 1, 2, 3\nP"),
        Special("multiPropCall", "P = 1, 2, 3\nP()"),
        Special("multiPropCount", "P = 1, 2, 3\ncount(P)"),
        Special("multiPropDotCount", "P = 1, 2, 3\nP.count"),
        Special("multiPropDot", "A = {\n    X = 1, 2, 3\n}\nA.X"),
        // The `dotAccess*` templates use a PRIVATE member (that is what
        // `A = { X = ... }` elaborates to). These pin the public spelling of the
        // same access so a change that made structural dot access exposure-sensitive
        // on one side alone cannot pass unnoticed.
        Special("dotAccessPublicMember", "A = {\n    public X = 1, 2, 3\n}\nA.X"),
        Special("dotAccessCallPublicMember", "A = {\n    public X = 1, 2, 3\n}\nA.X()"),
        Special("multiPropIndex0", "P = 1, 2, 3\nP:0"),
        Special("multiPropEq", "P = 1, 2, 3\nP == (1, 2, 3)"),
        Special("multiCollecting", "F(*a) = a\nF(1, 2, 3)"),
        Special("multiCollectingCount", "F(*a) = a\ncount(F(1, 2, 3))"),
        Special("collectingEmptyCall", "F(*a) = a\nF()"),
        Special("collectingFwdSum", "F(*a) = sum(a)\nF(1, 2, 3)"),
        Special("collectingFwdSpread", "F(*a) = G(a*)\nG(*b) = b\nF(1, 2, 3)"),
        Special("collectingJoin", "F(*a) = a\nF((1, 2)*, (3, 4)*)"),
        Special("range13", "range(1, 3)"),
        Special("rangeCapture", "x = range(1, 3)\nx"),
        Special("rangeCount", "count(range(1, 3))"),
        Special("rangeIndex0", "range(1, 3):0"),
        Special("takeOneSurvivorPair", "take(((1, 2), (3, 4)), 1)"),
        Special("takeOneSurvivorPairCount", "count(take(((1, 2), (3, 4)), 1))"),
        Special("takeOneSurvivorPairEq", "take(((1, 2), (3, 4)), 1) == (1, 2)"),
        Special("skipToOnePair", "skip(((1, 2), (3, 4)), 1)"),
        Special("distinctEmpties", "distinct((), ())"),
        Special("distinctPairsToOne", "distinct((1, 2), (1, 2))"),
        Special("takeEmpties", "take((), (), 2)"),
        Special("filterOneSurvivor", "Big(a) = a > 2\nfilter((1, 2, 3), Big)"),
        Special("filterOneSurvivorCount", "Big(a) = a > 2\ncount(filter((1, 2, 3), Big))"),
        Special("filterZeroSurvivors", "No(a) = 0\nfilter((1, 2, 3), No)"),
        Special("mapPairSwap", "Swap(a, b) = b, a\nmap(((1, 2), (3, 4)), Swap)"),
        Special("mapPairSwapOk", "Swap(a, b) = (b, a)\nmap(((1, 2), (3, 4)), Swap)"),
        Special("mapToOne", "M(a) = a\nmap((7), M)"),
        Special("orderSingle", "order(5)"),
        Special("orderEmpty", "order(())"),
        Special("atomsNested", "atoms(((1, 2), (3, 4)))"),
        Special("emptyOpGreater", "() > 1"),
        Special("emptyOpPlus", "() + 1"),
        Special("emptyOpBoth", "() + ()"),
        Special("emptyEqEmpty", "() == ()"),
        Special("emptyEqNestedEmpty", "() == (())"),
        Special("emptyNeNestedEmpty", "() != (())"),
        Special("propBodyEmptySlot", "P = (), 99\nP"),
        Special("rootEmptySlots", "(), 99"),
        Special("seqOfSpreadEmpty", "((()*), 1)"),
        Special("indexPairInSeq", "x = ((1, 2), (3, 4))\n(x:0, 99)"),
        Special("indexEmptyItemRoot", "x = ((), ())\nx:0"),
        Special("indexCapturedEq", "x = ((1, 2), (3, 4))\ny = x:0\ny == (1, 2)"),
        Special("chainedListIndex", "x = [[1, 2], [3, 4]]\nx:1:0"),
        Special("listIndexCapturedEq", "x = [[1, 2]]\ny = x:0\ny == [1, 2]"),
        Special("listIndexSelectedKindEqFalse", "[[1, 2]]:0 == (1, 2)"),
        Special("orderIndex0", "[3, 1, 2].order:0"),
        Special("nestedWrittenArg", "F(a, b) = a\nF(((1, 2)), 3)"),
        Special("writtenSlotArity", "F(a, b) = a + b\nF(((1, 2)))"),
        Special("mixedSingleGrouped", "F(x, *y, z) = y\nA = (1, 2, 3, 4)\nF(A)"),
        Special("sumEmpty", "sum(())"),
        // Spread-with-sibling slots inside a written sequence literal, and the
        // same shape observed through the non-counted evaluation paths (value
        // position of ==, spread operand, root rows). These pin the July 2026
        // fix that made Lean's evalAlgOutputCore the value projection of the
        // counted core (spread slots splice; a written `()` slot stays visible).
        Special("spreadWithSiblingSeqLiteral", "x = (1, 2)\n(x*, 99)"),
        Special("spreadEmptyBetween", "(1*, (), 2*)"),
        Special("rootSpreadExtra", "A = (1, 2)\nA*, 99"),
        Special("spreadOfSpreadSeqLiteral", "A = (1, 2)\n((A*, 99))*"),
        Special("eqSpreadSeqLiteral", "P = (1, 2)\n(P*, 99) == (1, 2, 99)"),
        Special("loopSpreadHistoryFlat",
            "Step((*history), previous) = (history*, previous + 1), previous + 1\nStep.repeat(2, (1, 2), 2):0"),
        Special("ifBranchSeq", "if(1, (1, 2), 3)"),
        Special("divZero", "1 / 0"),
        Special("negativeResult", "0 - 1"),
        Special("strEq", "'ab' == 'ab'"),
        Special("strCount", "count('ab')"),
        Special("strCapture", "x = 'ab'\nx"),
        // Exact list values: spread inside list literals, list/sequence kind
        // distinctions, empty-list-spread neutrality, and list arguments at
        // call boundaries. These pin the July 2026 list-value semantics.
        Special("listSpreadOfSeqProp", "A = 1, 2, 3\n[A*]"),
        Special("listSpreadBetween", "A = 1, 2, 3\n[0, A*, 4]"),
        Special("listOfLists", "A = [1, 2]\nB = [3, 4]\n[A, B]"),
        Special("listSpreadConcat", "A = [1, 2]\nB = [3, 4]\n[A*, B*]"),
        Special("listMixedSpread", "A = [1, 2]\nB = [3, 4]\n[A, B*]"),
        Special("listEmptyListSpreadBetween", "[1, []*, 2]"),
        Special("listEmptySeqSpreadBetween", "[1, ()*, 2]"),
        Special("listNeSeq", "[1, 2] == (1, 2)"),
        Special("listEmptyNeEmptySeq", "[] == ()"),
        Special("listSingletonNeItem", "[7] == 7"),
        Special("listWrapCanonicalizes", "([1, 2]) == [1, 2]"),
        Special("listSpreadCaptureRoundTrip", "A = [1, 2, 3]\nB = A*\nB == (1, 2, 3)"),
        Special("listCollectingNotSequenceKind", "x, *rest = [1, 2, 3]\nrest == (2, 3)"),
        Special("listCollectingCollectsExactList", "x, *rest = [1, 2, 3]\nrest == [2, 3]"),
        Special("implicitForwardOrdinarySource", "Target(*items) = items\nUse(items) = Target\nUse([1, 2])"),
        Special("callbackSingleCollectingMap", "Collect(*items) = items\n[7].map(Collect)"),
        Special("callbackMixedCollectingRow", "F(first, *middle, last) = middle\n[(1, 2, 3, 4)].map(F)"),
        Special("listInSeqSpreadKeepsList", "A = [1, 2]\n(A, 9)*"),
        Special("listFixedCallBoundary", "F(a, b) = a\nF([1, 2], 3)"),
        Special("listCollectingSpreadCall", "F(*a) = a\nA = [1, 2]\nF(A*, 9)"),
        // Spread of a DIRECT written block whose output is missing: the
        // operand stays syntactically a Block, so evaluation takes the
        // specialized Block arm of the spread-operand evaluator on both
        // sides (Lean `evalSequenceSpreadOperandItems` `.algorithmExpr`; C#
        // `EvalSequenceSpreadOperandItems`). Pinned as the spread-specific
        // error at every spread position, identical to the resolved-name
        // spelling (T4-2 — this arm was previously uncovered).
        Special("spreadNoOutputBlockRoot", "{A = 1}*"),
        Special("spreadNoOutputBlockList", "[{A = 1}*]"),
        Special("spreadNoOutputBlockCallArg", "F(a) = a\nF({A = 1}*)"),
        Special("spreadNoOutputResolved", "X = {A = 1}\nX*"),
        // C#-only parse-level cases (no comparable Lean program).
        Special("trailingComma", "(3,)",
            "A trailing comma is a KatLang surface-parser diagnostic; Lean models only the elaborated AST."),
        Special("spreadAsBinaryOperand", "A = (1, 2)\nA* == A*",
            "A spread used as a binary operand is a KatLang surface-parser diagnostic; Lean models only the elaborated AST."),
        Special("semicolonSeparator", "1 ; 2",
            "Semicolon separation is a KatLang surface-parser diagnostic; Lean models only the elaborated AST."),
        Special("listUnterminated", "[1, 2",
            "An unterminated list is a KatLang surface-parser diagnostic; Lean models only the elaborated AST."),
        Special("listDefinitionInside", "[x = 1]",
            "A definition inside a list is a KatLang surface-parser diagnostic; Lean models only the elaborated AST."),
        Special("listLoneCollectingAssignment", "*items = [1, 2, 3]"),
        // ── Builtins that had Lean guards and C# tests but no SHARED case ────
        // `while`, `first`, `last`, `min`, `max`, and `orderDesc` were the only
        // builtins with no Lean/C# differential pin at all (the receiver
        // templates cover count/take/skip/distinct/order/map/filter/atoms, and
        // the language spec covers if/repeat/reduce/sum/avg/range/contains).
        // Each is pinned here across the boundaries that distinguish them:
        // sequence vs exact list vs scalar collection, the empty-collection
        // policy, the item-shape constraint, and the dot spelling.
        Special("minSeq", "min((3, 1, 2))"),
        Special("minList", "min([3, 1])"),
        Special("minScalar", "min(7)"),
        Special("minEmpty", "min(())"),
        Special("minNestedItem", "min(((1, 2), 3))"),
        Special("minDot", "x = 3, 1, 2\nx.min"),
        Special("maxSeq", "max((3, 1, 2))"),
        Special("maxList", "max([3, 1])"),
        Special("maxEmpty", "max(())"),
        Special("maxDot", "x = 3, 1, 2\nx.max"),
        Special("firstSeq", "first((1, 2, 3))"),
        Special("firstScalar", "first(7)"),
        Special("firstListElementStaysExact", "first([[1, 2], 3])"),
        Special("firstEmptyItem", "first(((), 1))"),
        Special("firstEmpty", "first(())"),
        Special("firstDot", "x = 1, 2, 3\nx.first"),
        Special("lastSeq", "last((1, 2, 3))"),
        Special("lastListElementStaysExact", "last([1, [2, 3]])"),
        Special("lastEmpty", "last(())"),
        Special("orderDescSeq", "orderDesc((1, 3, 2))"),
        Special("orderDescList", "orderDesc([2, 1])"),
        Special("orderDescDuplicates", "orderDesc((2, 1, 2))"),
        Special("orderDescScalar", "orderDesc(7)"),
        Special("orderDescEmpty", "orderDesc(())"),
        Special("orderDescString", "orderDesc(('b', 'a'))"),
        Special("orderDescDot", "x = 1, 3, 2\nx.orderDesc"),
        Special("whileCountdown", "S(a) = a - 1, a > 1\nwhile(S, 3)"),
        Special("whileZeroIterations", "S(a) = a, 0\nwhile(S, 5)"),
        Special("whileTwoSlotState", "S(a, b) = a + 1, b * 2, a < 3\nwhile(S, 1, 1)"),
        Special("whileEmptyInitialState", "S(a) = a, 0\nwhile(S, ())"),
        Special("whileNonNumericContinuation", "S(a) = a, ()\nwhile(S, 1)"),
        Special("whileDot", "S(a) = a - 1, a > 1\nS.while(3)"),
        Special("containsSequenceItem", "contains(((1, 2), 3), (1, 2))"),
        Special("containsListItem", "contains([[1, 2], 3], [1, 2])"),
        Special("containsEmptyItem", "contains(((), 1), ())"),
        Special("containsScalarCollection", "contains(7, 7)"),
        Special("containsAcrossKinds", "contains(([1, 2], 3), (1, 2))"),

        // ----- open / visibility (Track 10) -----------------------------------
        // Name resolution, `open`, and visibility had ZERO cases in either
        // generated differential artifact before this family, even though Lean
        // models ownership-first lookup, public-only exposure through `open`,
        // provider ambiguity, and open-target dedup in full.
        //
        // Every Lean program in the corpus is now encoder-derived, but THIS
        // family's derived encodings are additionally pinned against manually
        // reviewed golden text in OpenVisibilityCorpusFidelityTests, because
        // exposure metadata (public / private / local-only) and
        // implicit-parameter promotion ARE the semantics under test here — the
        // Track 9 fidelity defect this family is most exposed to.
        Special("openPublicMember", "Lib = {\n    public X = 101\n}\nA = {\n    open Lib\n    X\n}\nA"),

        // `open` never exposes a private member, so `X` is unresolvable and the
        // front end promotes it to an implicit parameter of `A`.
        Special("openPrivateMemberHidden", "Lib = {\n    X = 101\n}\nA = {\n    open Lib\n    X\n}\nA(707)"),

        // Public but NOT exported: the member depends on its owner's parameter.
        Special("openLocalOnlyCapturedParamsHidden",
            "Lib(p) = {\n    public X = p + 101\n    X\n}\nA = {\n    open Lib\n    X\n}\nA"),

        Special("openTwoProvidersAmbiguous",
            "L1 = {\n    public X = 101\n}\nL2 = {\n    public X = 202\n}\nA = {\n    open L1, L2\n    X\n}\nA"),

        // Duplicate NAMED targets deduplicate first-occurrence-wins, so they are
        // one provider and never a spurious ambiguity (Lean: resolveAllOpens).
        Special("openDuplicateTargetDedup", "Lib = {\n    public X = 101\n}\nA = {\n    open Lib, Lib\n    X\n}\nA"),

        Special("openDuplicateDottedTargetDedup",
            "Lib = {\n    public S = {\n        public X = 101\n    }\n}\nA = {\n    open Lib.S, Lib.S\n    X\n}\nA"),

        // Inline blocks get positional keys and are NEVER deduplicated, so two
        // structurally identical blocks really are two providers.
        Special("openDuplicateInlineBlocksAmbiguous",
            "A = {\n    open { public X = 101 }, { public X = 202 }\n    X\n}\nA"),

        Special("openInlineBlock", "A = {\n    open { public X = 101 }\n    X\n}\nA"),

        Special("openInlineBlockPrivateHidden", "A = {\n    open { X = 101 }\n    X\n}\nA(707)"),

        Special("openDottedPath",
            "Lib = {\n    public S = {\n        public X = 101\n    }\n}\nA = {\n    open Lib.S\n    X\n}\nA"),

        // A dotted open path requires every member after the lexical head to be
        // public, so a private intermediate provides nothing.
        Special("openDottedPathPrivateIntermediate",
            "Lib = {\n    S = {\n        public X = 101\n    }\n}\nA = {\n    open Lib.S\n    X\n}\nA(707)"),

        // Ownership-first: an owned property always beats an opened one.
        Special("openLocalShadowsOpenedName",
            "Lib = {\n    public X = 101\n}\nA = {\n    open Lib\n    X = 202\n    X\n}\nA"),

        Special("openAncestorPropertyWins",
            "Lib = {\n    public X = 101\n}\nA = {\n    X = 202\n    Inner = {\n        open Lib\n        X\n    }\n    Inner\n}\nA"),

        // A nested `open` is visible to descendants but never leaks outward.
        Special("openParentScopeReachesChild",
            "Lib = {\n    public X = 101\n}\nA = {\n    open Lib\n    Inner = {\n        X\n    }\n    Inner\n}\nA"),

        Special("openNestedDoesNotLeakOutward",
            "Lib = {\n    public X = 101\n}\nA = {\n    Inner = {\n        open Lib\n        X\n    }\n    X\n}\nA(707)"),

        // The open head resolves by direct lexical lookup, which sees a private
        // sibling defined later in the same body.
        Special("openHeadDefinedLater", "A = {\n    open Lib\n    X\n}\nLib = {\n    public X = 101\n}\nA"),

        // The prelude is the outermost lexical scope, so ownership-first reaches
        // the builtin before opens are consulted.
        Special("openBuiltinNameCollision",
            "Lib = {\n    public count = 101\n}\nA = {\n    open Lib\n    count([1, 2, 3])\n}\nA"),

        // A builtin is never a legal open target; validation runs over the whole
        // open list before any name is resolved through it.
        Special("openBuiltinTargetIsIllegal",
            "Lib = {\n    public X = 101\n}\nA = {\n    open count, Lib\n    X\n}\nA"),

        // Structural dot access deliberately ignores visibility; `open` does not.
        // Pinning both spellings keeps the two rules from collapsing into one.
        Special("structuralDotSeesPrivateMember", "Lib = {\n    X = 101\n}\nLib.X"),

        // A member `open` must not expose cannot become a SECOND provider.
        // The single-provider spelling cannot see this: the front end has
        // already turned the unresolvable name into an implicit parameter, so
        // the evaluator's exposure filter is never consulted. Pairing the hidden
        // member with a visible one makes the filter decide between "resolves"
        // and "ambiguous" (Track 11 mutants A5-A8 survived the whole suite
        // without these).
        Special("openPrivateMemberIsNotASecondProvider",
            "Pub = {\n    public X = 101\n}\nLib = {\n    X = 202\n}\nA = {\n    open Pub, Lib\n    X\n}\nA"),

        Special("openLocalOnlyMemberIsNotASecondProvider",
            "Pub = {\n    public X = 101\n}\nLib(p) = {\n    public X = p + 202\n    X\n}\nA = {\n    open Pub, Lib\n    X\n}\nA"),
    ];

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

    // Written-group leaves are Capture nodes since the OutputBundle split
    // (Lean-side: `.capture [...]`).
    private static Expr ScBlock(params Expr[] outputs) => new Expr.Capture(new OutputBundle(outputs));

    private static Expr Sc(params Expr[] leaves)
        => leaves.Aggregate((left, right) => new Expr.SequenceConstruct(left, right));

    private static Expr ScCall(string builtin, params Expr[] args) => new Expr.Call(
        new Expr.Resolve(builtin),
        args);

    public static IReadOnlyList<InternalNodeCase> InternalNodeCases() =>
    [
        new("sc_e_1", "SequenceConstruct[(), 1] drops the () leaf and singleton-collapses",
            () => Sc(ScEmpty(), ScNum(1)),
            "((), 1)", InternalNodeRelation.IntentionallyDifferent),
        new("sc_1_e", "SequenceConstruct[1, ()] drops the () leaf and singleton-collapses",
            () => Sc(ScNum(1), ScEmpty()),
            "(1, ())", InternalNodeRelation.IntentionallyDifferent),
        new("sc_e_e", "SequenceConstruct[(), ()] drops both () leaves to the empty sequence",
            () => Sc(ScEmpty(), ScEmpty()),
            "((), ())", InternalNodeRelation.IntentionallyDifferent),
        new("sc_p12_e", "SequenceConstruct[(1,2), ()] drops () and collapses to the pair",
            () => Sc(ScBlock(ScNum(1), ScNum(2)), ScEmpty()),
            "((1, 2), ())", InternalNodeRelation.IntentionallyDifferent),
        new("sc_e_p12", "SequenceConstruct[(), (1,2)] drops () and collapses to the pair",
            () => Sc(ScEmpty(), ScBlock(ScNum(1), ScNum(2))),
            "((), (1, 2))", InternalNodeRelation.IntentionallyDifferent),
        new("sc_1_2", "SequenceConstruct[1, 2] matches written (1, 2)",
            () => Sc(ScNum(1), ScNum(2)),
            "(1, 2)", InternalNodeRelation.IntentionallyEqual),
        new("sc_p12_p34", "SequenceConstruct of two pairs preserves nested structure",
            () => Sc(ScBlock(ScNum(1), ScNum(2)), ScBlock(ScNum(3), ScNum(4))),
            "((1, 2), (3, 4))", InternalNodeRelation.IntentionallyEqual),
        new("sc_spread_3", "SequenceConstruct[(1,2)*, 3] splices the spread leaf",
            () => Sc(new Expr.SequenceSpread(ScBlock(ScNum(1), ScNum(2))), ScNum(3)),
            "((1, 2)*, 3)", InternalNodeRelation.IntentionallyEqual),
        new("sc_count_arg", "count of the internal node observes the ()-dropped value",
            () => ScCall("count", Sc(ScEmpty(), ScNum(1))),
            "count(((), 1))", InternalNodeRelation.IntentionallyDifferent),
        new("sc_take_collection", "a SequenceConstruct collection argument binds like the grouped surface form",
            () => ScCall("take", Sc(ScNum(1), ScNum(2), ScNum(5)), ScNum(2)),
            "take((1, 2, 5), 2)", InternalNodeRelation.IntentionallyEqual),
        new("sc_take_collection_empty", "() leaf vanishes from a SequenceConstruct collection argument (written parens keep it)",
            () => ScCall("take", Sc(ScEmpty(), ScNum(1), ScNum(2)), ScNum(2)),
            "take(((), 1, 2), 2)", InternalNodeRelation.IntentionallyDifferent),
        new("sc_take_block_leaf", "a nested pair inside a SequenceConstruct collection argument stays one item",
            () => ScCall("take", Sc(ScNum(1), ScBlock(ScNum(2), ScNum(5))), ScNum(2)),
            "take((1, (2, 5)), 2)", InternalNodeRelation.IntentionallyEqual),
        new("sc_sum_arg", "sum of the internal node matches the grouped surface form",
            () => ScCall("sum", Sc(ScNum(1), ScNum(2))),
            "sum((1, 2))", InternalNodeRelation.IntentionallyEqual),
        // Call-FUNCTION position: the internal node cannot resolve to an
        // algorithm (structured payload "sequence construct expression",
        // Lean-aligned — T4-3), while the surface control calls a zero-parameter
        // property (whose body is the written pair) with one argument and therefore
        // gets an ordinary arity error — the error KINDS intentionally differ.
        new("sc_call_function", "SequenceConstruct in call-function position is notAnAlgorithm",
            () => new Expr.Call(
                Sc(ScNum(1), ScNum(2)),
                [ScNum(3)]),
            "X = (1, 2)\nX(3)", InternalNodeRelation.IntentionallyDifferent),
    ];

    /// <summary>
    /// All generated cases (template x value cross product plus specials),
    /// with each Lean-comparable case's Lean program DERIVED from the source's
    /// real elaborated AST through <see cref="LeanAstEncoder"/>. Derivation is
    /// fail-loud: a case not flagged C#-only must parse cleanly and encode, so
    /// a parser regression or an encoder coverage regression fails corpus
    /// construction naming the case instead of silently shrinking the
    /// differential corpus. The corpus is deterministic and immutable, so it
    /// is built once per process.
    /// </summary>
    public static IReadOnlyList<ExplorerCase> AllCases() => LazyCases.Value;

    private static readonly Lazy<IReadOnlyList<ExplorerCase>> LazyCases = new(BuildCases);

    private static IReadOnlyList<ExplorerCase> BuildCases()
    {
        var cases = new List<ExplorerCase>();
        foreach (var template in Templates)
        {
            foreach (var (valueId, value) in Values)
            {
                var id = $"{template.Id}__{valueId}";
                var source = template.Source(value);
                ValidateExclusionReason(id, template.LeanExclusionReason);
                cases.Add(new ExplorerCase(
                    id,
                    template.Id,
                    valueId,
                    source,
                    template.LeanExclusionReason is null ? DeriveLeanProgram(id, source) : null,
                    template.LeanExclusionReason));
            }
        }

        foreach (var (id, source, leanExclusionReason) in Specials)
        {
            var caseId = $"special__{id}";
            ValidateExclusionReason(caseId, leanExclusionReason);
            cases.Add(new ExplorerCase(
                caseId, "special", id, source,
                leanExclusionReason is null ? DeriveLeanProgram(caseId, source) : null,
                leanExclusionReason));
        }

        return cases.AsReadOnly();
    }

    private static void ValidateExclusionReason(string caseId, string? reason)
    {
        if (reason is not null && string.IsNullOrWhiteSpace(reason))
        {
            throw new InvalidOperationException(
                $"Semantic-explorer case '{caseId}' has a blank LeanExclusionReason; " +
                "an exclusion must state the reviewed parser/model boundary it exercises.");
        }
    }

    private static string DeriveLeanProgram(string caseId, string source)
    {
        var parsed = Parser.Parse(source);
        if (parsed.HasErrors)
        {
            throw new InvalidOperationException(
                $"Semantic-explorer case '{caseId}' is not flagged C#-only but its source does not parse cleanly: "
                + string.Join(" | ", parsed.Diagnostics.Select(d => d.Message.Split('\n')[0]))
                + $"\nSource:\n{source}");
        }

        try
        {
            return LeanAstEncoder.EncodeProgram(parsed.Root);
        }
        catch (NotSupportedException ex)
        {
            throw new InvalidOperationException(
                $"Semantic-explorer case '{caseId}' cannot be Lean-encoded; either extend LeanAstEncoder "
                + $"deliberately or flag the case C#-only with a reviewed reason. Encoder said: {ex.Message}"
                + $"\nSource:\n{source}", ex);
        }
    }
}
