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

    public sealed record Bool(bool Value) : ExplorerValue;

    /// <summary>The empty sequence value literal <c>()</c>.</summary>
    public sealed record Empty : ExplorerValue;

    /// <summary>A parenthesized list literal with two or more items.</summary>
    public sealed record Seq(IReadOnlyList<ExplorerValue> Items) : ExplorerValue;

    /// <summary>Redundant parentheses around one written value: <c>(x)</c>.</summary>
    public sealed record Wrap(ExplorerValue Inner) : ExplorerValue;

    /// <summary>A list literal <c>[a, b]</c> (any element count).</summary>
    public sealed record ListOf(IReadOnlyList<ExplorerValue> Items) : ExplorerValue;

    public string Source => this switch
    {
        Num n => n.Value.ToString(System.Globalization.CultureInfo.InvariantCulture),
        Bool b => b.Value ? "true" : "false",
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
        ("bt", new ExplorerValue.Bool(true)),
        ("bf", new ExplorerValue.Bool(false)),
        ("pbt", W(new ExplorerValue.Bool(true))),
        ("pbt_e", S(new ExplorerValue.Bool(true), E)),
        ("pbt_1", S(new ExplorerValue.Bool(true), N(1))),
        ("lbt", L(new ExplorerValue.Bool(true))),
        ("lbt_bf", L(new ExplorerValue.Bool(true), new ExplorerValue.Bool(false))),
        ("lpbt_1", L(S(new ExplorerValue.Bool(true), N(1)))),
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
        // List values: empty, singleton, multi, list-in-list,
        // sequence-in-list, list-in-sequence, and wrapped list (redundant
        // parens around a list still normalize away).
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
        // DOT-CALL PASSES A VALUE: the extension-call receiver is the ordinary
        // leading argument, so `x.F` is `F(x)` and `(v).F` is `F((v))` — which,
        // PARENTHESES GROUPING SYNTAX, is `F(v)` — one argument that the lone
        // collector collects as one item whatever its value (THE EXACT COLLECTOR
        // LAW) — while the fluent spread `x*.F` — `F(x*)` — supplies the value's
        // items. The three templates differentially pin the rule, per value,
        // against the written spellings `collectingViaProp` / `collecting` /
        // `collectingSpread`.
        new("dotCollectingViaProp",
            v => $"F(*a) = a\nx = {v.Source}\nx.F"),
        new("literalDotCollecting",
            v => $"F(*a) = a\n({v.Source}).F"),
        new("fluentSpreadCollecting",
            v => $"F(*a) = a\nx = {v.Source}\nx*.F"),
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
            v => $"x, y = ({v.Source}*)\nx"),
        new("deconCollect_t",
            v => $"h, *t = {v.Source}\nt"),
        new("deconCollectSpread_t",
            v => $"h, *t = ({v.Source}*)\nt"),
        new("deconPrefix_p",
            v => $"*p, z = {v.Source}\np"),
        new("deconPrefix_z",
            v => $"*p, z = {v.Source}\nz"),
        new("seqWrapPair",
            v => $"({v.Source}, 99)"),
        new("seqWrapSolo",
            v => $"({v.Source})"),
        new("spreadRoot",
            v => $"{v.Source}*, 997"),
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
            v => $"x = {v.Source}\nx[0]"),
        new("index1",
            v => $"x = {v.Source}\nx[1]"),
        new("indexBig",
            v => $"x = {v.Source}\nx[9]"),
        // A selector is an ordinary expression: `-1` is a number naming no position
        // (BadIndex), never from-the-end selection.
        new("indexNeg",
            v => $"x = {v.Source}\nx[-1]"),
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
        // S3 (September 2026): a callback binds its ONE supplied value exactly as the
        // ordinary call binds it. Each template of the direct/callback pairs is pinned
        // against Lean per value — a nested head-plus-collector pattern and a nested fixed
        // pair, of BOTH structural kinds: a sequence pattern opens sequence values only and a
        // list pattern list values only, every other value being the pattern's kind mismatch
        // — so a Lean/C# divergence in either binder shows up against its own spelling;
        // CallbackNestedPatternBindingTests
        // .ExplorerTemplatePairs_MapEveryValueExactlyAsTheDirectCall relates the two
        // spellings of each pair value by value.
        new("patternHead",
            v => $"P((h, *t)) = [h, t]\nP({v.Source})"),
        new("patternHeadMap",
            v => $"P((h, *t)) = [h, t]\nmap([{v.Source}], P)"),
        new("patternPair",
            v => $"P((x, y)) = [x, y]\nP({v.Source})"),
        new("patternPairMap",
            v => $"P((x, y)) = [x, y]\nmap([{v.Source}], P)"),
        new("listPatternHead",
            v => $"P([h, *t]) = [h, t]\nP({v.Source})"),
        new("listPatternHeadMap",
            v => $"P([h, *t]) = [h, t]\nmap([{v.Source}], P)"),
        new("listPatternPair",
            v => $"P([x, y]) = [x, y]\nP({v.Source})"),
        new("listPatternPairMap",
            v => $"P([x, y]) = [x, y]\nmap([{v.Source}], P)"),
        new("filterKeep",
            v => $"T(a) = true\nfilter({v.Source}, T)"),
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
            v => $"{v.Source}**, 997"),
        new("collectingStacked",
            v => $"F(*a) = a\nF({v.Source}**)"),
        new("captureStacked",
            v => $"x = ({v.Source}**)\nx"),
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
        Special("multiPropIndex0", "P = 1, 2, 3\nP[0]"),
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
        Special("rangeIndex0", "range(1, 3)[0]"),
        Special("takeOneSurvivorPair", "take(((1, 2), (3, 4)), 1)"),
        Special("takeOneSurvivorPairCount", "count(take(((1, 2), (3, 4)), 1))"),
        Special("takeOneSurvivorPairEq", "take(((1, 2), (3, 4)), 1) == (1, 2)"),
        Special("skipToOnePair", "skip(((1, 2), (3, 4)), 1)"),
        Special("distinctEmpties", "distinct((), ())"),
        Special("distinctPairsToOne", "distinct((1, 2), (1, 2))"),
        Special("takeEmpties", "take((), (), 2)"),
        Special("filterOneSurvivor", "Big(a) = a > 2\nfilter((1, 2, 3), Big)"),
        Special("filterOneSurvivorCount", "Big(a) = a > 2\ncount(filter((1, 2, 3), Big))"),
        Special("filterZeroSurvivors", "No(a) = false\nfilter((1, 2, 3), No)"),
        Special("mapPairSwap", "Swap(a, b) = b, a\nmap(((1, 2), (3, 4)), Swap)"),
        // A callback element is ONE ordinary argument: the structural pattern opens
        // each pair explicitly, while a flat two-parameter callee is the ordinary
        // arity error of `Swap((1, 2))`.
        Special("mapPairSwapOk", "Swap((a, b)) = (b, a)\nmap(((1, 2), (3, 4)), Swap)"),
        Special("mapPairSwapFlatIsArity", "Swap(a, b) = (b, a)\nmap(((1, 2), (3, 4)), Swap)"),
        Special("mapToOne", "M(a) = a\nmap((7), M)"),
        Special("orderSingle", "order(5)"),
        Special("orderEmpty", "order(())"),
        Special("atomsNested", "atoms(((1, 2), (3, 4)))"),
        // SYN-01: `()` is an ordinary non-scalar operand for the non-equality
        // operators, on either side. These pin the Lean/C# agreement on the
        // FAILURE, exactly as the equality cases below pin it on success.
        Special("emptyOpGreater", "() > 1"),
        Special("emptyOpPlus", "() + 1"),
        Special("emptyOpPlusRight", "1 + ()"),
        Special("emptyOpDivRight", "10 / ()"),
        Special("emptyOpAnd", "() and 7"),
        Special("emptyOpString", "() + 'text'"),
        Special("emptyOpBoth", "() + ()"),
        Special("emptyUnaryMinus", "-()"),
        Special("emptyUnaryNot", "not ()"),
        Special("emptyEqEmpty", "() == ()"),
        Special("emptyEqNestedEmpty", "() == (())"),
        Special("emptyNeNestedEmpty", "() != (())"),
        Special("propBodyEmptySlot", "P = (), 99\nP"),
        Special("rootEmptySlots", "(), 99"),
        Special("seqOfSpreadEmpty", "((()*), 1)"),
        Special("indexPairInSeq", "x = ((1, 2), (3, 4))\n(x[0], 99)"),
        Special("indexEmptyItemRoot", "x = ((), ())\nx[0]"),
        Special("indexCapturedEq", "x = ((1, 2), (3, 4))\ny = x[0]\ny == (1, 2)"),
        Special("chainedListIndex", "x = [[1, 2], [3, 4]]\nx[1][0]"),
        Special("listIndexCapturedEq", "x = [[1, 2]]\ny = x[0]\ny == [1, 2]"),
        Special("listIndexSelectedKindEqFalse", "[[1, 2]][0] == (1, 2)"),
        Special("orderIndex0", "[3, 1, 2].order[0]"),
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
        Special("spreadOfSpreadSeqLiteral", "A = (1, 2)\n((A*, 99))*, 997"),
        Special("eqSpreadSeqLiteral", "P = (1, 2)\n(P*, 99) == (1, 2, 99)"),
        Special("loopSpreadHistoryFlat",
            "Step((*history), previous) = (history*, previous + 1), previous + 1\nStep((1, 2), 2).repeat(2)[0]"),
        Special("ifBranchSeq", "if(true, (1, 2), 3)"),
        Special("divZero", "1 / 0"),
        Special("negativeResult", "0 - 1"),
        Special("strEq", "'ab' == 'ab'"),
        // Comparison chains (September 2026): one chainable tier with adjacent-pair
        // links, incremental exactly-once operand evaluation, eager past `false`,
        // stopped by an error. These pin the chain AST derived from real source against
        // Lean's `evalComparisonCounted`.
        Special("chainAllTrue", "1 < 2 < 3"),
        Special("chainMixed", "1 < 2 <= 2 == 2 != 3"),
        Special("chainFalseMiddle", "1 < 3 < 2 < 4"),
        Special("chainFalseLast", "1 < 2 < 2"),
        Special("chainEqOnly", "1 == 1 == 1"),
        Special("chainNeAdjacent", "1 != 2 != 1"),
        Special("chainNeAdjacentFalse", "1 != 1 != 1"),
        Special("chainEqThenLt", "1 == 1 < 2"),
        Special("chainBoolEqMixed", "1 < 2 == true"),
        Special("chainSeqEq", "(1, 2) == (1, 2) == (1, 2)"),
        Special("chainStrEq", "'a' == 'a' != 'b'"),
        Special("chainParenFirst", "(1 < 2) == true"),
        Special("chainParenRight", "1 < (2 == 2)"),
        Special("chainParenBoth", "(1 < 2) == (3 < 4)"),
        Special("chainUnderNot", "not 1 < 2 < 3"),
        Special("chainUnderAnd", "1 < 2 < 3 and 4 < 5"),
        Special("chainArithmeticOperands", "1 + 1 < 3 * 1 <= 4 - 1"),
        Special("chainInvalidLater", "3 < 2 < true"),
        Special("chainErrorFirstOperand", "1 / 0 < true < 1"),
        Special("chainErrorAfterFalse", "3 < 2 < 1 / 0"),
        Special("chainPropertyOperands", "P = 2\n1 < P < 3, P == P == 2"),
        Special("chainCallOperands", "F(x) = x + 1\nF(0) < F(1) < F(2)"),
        // The comparison-chain hostile audit (September 2026): the chains a downstream review's
        // "`a < b == c` is false" wording questioned. Each one's value differs from the
        // left-associated reading `(a op b) op c` (a different Boolean, or an ordering rejection),
        // so the derived Lean guard pins adjacent-pair semantics on the parsed chain itself.
        Special("chainLtThenEq", "1 < 2 == 2"),
        Special("chainLtThenGt", "1 < 2 > 1"),
        Special("chainNeThenLt", "1 != 2 < 3"),
        Special("chainFalseFirstThenEqFalse", "2 < 1 == false"),
        // The final comparison-chain review (September 2026): the precedence neighbours of the
        // tier, parentheses on either side, an operand's own error between links, and a grouped
        // chain as a postfix receiver — each Lean program derived from the parsed tree.
        Special("chainGroupedNotOperand", "(not true) == false"),
        Special("chainParenLeftUnderOrdering", "(1 < 2) < 3"),
        Special("chainNegatedBasePower", "(-2) ^ 2 < -3"),
        Special("chainNegatedPowerOperand", "1 < -2 ^ 2"),
        Special("chainGroupedNegatedBasePowerOperand", "1 < (-2) ^ 2"),
        Special("chainArithmeticTiers", "1 + 1 < 2 * 2 == 2 ^ 2"),
        Special("chainMiddleOperandError", "1 < 1 / 0 < true"),
        Special("chainGroupedSelectionReceiver", "(1 < 2 < 3)[0] == true"),
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
        Special("listSpreadCaptureRoundTrip", "A = [1, 2, 3]\nB = { A* }\nB == (1, 2, 3)"),
        Special("listCollectingNotSequenceKind", "x, *rest = [1, 2, 3]\nrest == (2, 3)"),
        Special("listCollectingCollectsExactList", "x, *rest = [1, 2, 3]\nrest == [2, 3]"),
        // The lone row under a written list is bare forwarding: Use's same-named bindings supply
        // Target's `tag` and `*items` (FWD-02).
        Special("implicitForwardOrdinarySource", "Target(tag, *items) = items\nUse(tag, items) = Target\nUse(0, [1, 2])"),
        Special("callbackSingleCollectingMap", "Collect(*items) = items\n[7].map(Collect)"),
        Special("callbackMixedCollectingRow", "F(first, *middle, last) = middle\n[(1, 2, 3, 4)].map(F)"),
        Special("callbackMixedCollectingRowPattern", "F((first, *middle, last)) = middle\n[(1, 2, 3, 4)].map(F)"),
        Special("callbackCollectingElementIsOneArgument", "Cnt(*xs) = xs.count\nmap([(10, 7), [10, 7], 20], Cnt)"),
        // Q-03 hostile review: a callable that accepts zero supplied arguments is a VALUE
        // at a collector, so its failed read surfaces its own error, never the callable
        // typeMismatch (callable-shaped is the zero-argument law's verdict, not "declares
        // parameters").
        Special("collectorZeroArgumentCallableFailureIsItsOwn", "Bad(*xs) = 1 / 0\nColl(*ys) = ys\nColl(Bad)"),
        Special("listInSeqSpreadKeepsList", "A = [1, 2]\n(A, 9)*, 997"),
        Special("listFixedCallBoundary", "F(a, b) = a\nF([1, 2], 3)"),
        Special("listCollectingSpreadCall", "F(*a) = a\nA = [1, 2]\nF(A*, 9)"),
        // Spread of a DIRECT written block whose output is missing: the
        // operand stays syntactically a Block, so evaluation takes the
        // specialized Block arm of the spread-operand evaluator on both
        // sides (Lean `evalSequenceSpreadOperandValue` `.algorithmExpr`; C#
        // `EvalSequenceSpreadOperandValue`). Pinned as the spread-specific
        // error at every spread position, identical to the resolved-name
        // spelling (T4-2 — this arm was previously uncovered).
        Special("spreadNoOutputBlockRoot", "{A = 1}*, 997"),
        Special("spreadNoOutputBlockList", "[{A = 1}*]"),
        Special("spreadNoOutputBlockCallArg", "F(a) = a\nF({A = 1}*)"),
        Special("spreadNoOutputResolved", "X = {A = 1}\nX*, 997"),
        // X-29 / Q-36 (decided 2026-10-24): only the operand's OWN missing output is the spread's
        // report; a missing output nested in the operand's dependencies, arguments, rows or
        // construction keeps its category. Lean `spreadOperandFailure`; C# `SpreadOperandFailure`.
        Special("spreadNestedDependency", "G = {A = 1}\nH = G + 1\nH*, 997"),
        Special("spreadNestedDependencyCall", "G = {A = 1}\nH = G + 1\nH()*, 997"),
        Special("spreadOwnInvoked", "G = {A = 1}\nG()*, 997"),
        Special("spreadNestedArgument", "F(x) = x\nF({A = 1})*, 997"),
        Special("spreadNestedRow", "G = {A = 1}\n{ G }*, 997"),
        Special("spreadNestedCapture", "G = {A = 1}\n(G, 1)*, 997"),
        Special("spreadNestedList", "G = {A = 1}\n[G]*, 997"),
        Special("spreadNestedBuiltinArgument", "G = {A = 1}\ncount(G)*, 997"),
        Special("spreadNestedFamilyMatch", "G = {A = 1}\nK(0) = 1\nK(n) = 2\nK(G)*, 997"),
        Special("spreadNestedPatternBinding", "G = {A = 1}\nQ((a, b)) = a\nQ(G)*, 997"),
        Special("spreadNestedStringReceiver", "G = {A = 1}\nG.string*, 997"),
        Special("spreadInnerOwnKept", "({A = 1}*)*, 997"),
        Special("spreadOrdinaryFailureKept", "(1 / 0)*, 997"),
        Special("spreadNestedSupplySlot", "G = {A = 1}\nH = G + 1\ncount(1, H*)"),
        Special("spreadNestedCallbackSlot", "G = {A = 1}\nH = G + 1\nmap([], H*)"),
        Special("spreadForwardedOwn", "P(x) = x*\nP({A = 1})"),
        Special("spreadForwardedNested", "G = {A = 1}\nH = G + 1\nP(x) = x*\nP(H)"),
        Special("spreadCollectorElement", "G = {}\nC(*xs) = xs*\nC(G)"),
        Special("spreadForwardedCollectorElement", "G = {}\nP(x) = x*\nC(*xs) = P(xs)\nC(G)"),
        // C#-only parse-level cases (no comparable Lean program).
        Special("trailingComma", "(3,)",
            "A trailing comma is a KatLang surface-parser diagnostic; Lean models only the elaborated AST."),
        Special("spreadAsBinaryOperand", "A = (1, 2)\nA* == A*, 997",
            "A spread used as a binary operand is a KatLang surface-parser diagnostic; Lean models only the elaborated AST."),
        Special("semicolonSeparator", "1 ; 2",
            "Semicolon separation is a KatLang surface-parser diagnostic; Lean models only the elaborated AST."),
        Special("listUnterminated", "[1, 2",
            "An unterminated list is a KatLang surface-parser diagnostic; Lean models only the elaborated AST."),
        Special("listDefinitionInside", "[x = 1]",
            "A definition inside a list is a KatLang surface-parser diagnostic; Lean models only the elaborated AST."),
        // STR-03 (November 2026): KatLang has one string literal form, raw single-quoted text. A
        // double quote outside a comment or a single-quoted string is rejected by the LEXER, which
        // exists in C# only, so both probes are C#-only by construction: no Lean equivalent exists
        // and none is fabricated.
        Special("doubleQuotedStringRejected", "\"abc\"",
            "A double-quoted string is a KatLang lexer diagnostic (STR-03, UnsupportedDoubleQuotedString); lexing is implemented in C# only, and Lean models only the elaborated AST."),
        Special("doubleQuotedInterpolationRejected", "x = 1\n\"Total: {x}\"",
            "String interpolation is not KatLang syntax: its double-quoted run is a KatLang lexer diagnostic (STR-03, UnsupportedDoubleQuotedString); lexing is implemented in C# only, and Lean models only the elaborated AST."),
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
        Special("whileCountdown", "S(a) = a - 1, a > 1\nwhile(S(3))"),
        Special("whileZeroIterations", "S(a) = a, 0\nwhile(S(5))"),
        Special("whileTwoSlotState", "S(a, b) = a + 1, b * 2, a < 3\nwhile(S(1, 1))"),
        Special("whileEmptyInitialState", "S(a) = a, 0\nwhile(S(()))"),
        Special("whileNonNumericContinuation", "S(a) = a, ()\nwhile(S(1))"),
        Special("whileDot", "S(a) = a - 1, a > 1\nS(3).while"),
        // The loop cardinality law (Q-24 + Q-26, October 2026): patterns bind, rows produce, `*` opens.
        Special("loopResultIsOneRow", "Fibonacci(a, b) = b, a + b\nFibonacci(0, 1).repeat(10)"),
        Special("loopResultBesideAnotherRow", "Fibonacci(a, b) = b, a + b\nFibonacci(0, 1).repeat(10), 7"),
        Special("loopResultSpreadOpensIt", "Fibonacci(a, b) = b, a + b\nFibonacci(0, 1).repeat(10)*, 997"),
        Special("loopZeroSlotResult", "Drop(*xs) = { ()* }\nrepeat(Drop(5), 1), repeat(Drop(5), 1)*, 9"),
        Special("repeatedNameStepSpreadRowIsTwoSlots", "Dup(x, x) = { (x + 1, x + 1)* }\nDup(1, 1).repeat(2)"),
        Special("repeatedNameStepDivergingRowsRebindFails", "Dup(x, x) = { x + 1, x + 2 }\nDup(1, 1).repeat(2)"),
        Special("structuralStepSpreadRowSuppliesItems", "Step2((a, b)) = { (b, a + b)* }\nrepeat(Step2((0, 1)), 1), Step2((0, 1))"),
        Special("structuralStepSpreadRowCannotRebind", "Step2((a, b)) = { (b, a + b)* }\nStep2((0, 1)).repeat(2)"),
        Special("historyStepSpreadRowEqualsDirectCall", "P((*h), n) = { h*, n + 1 }\nrepeat(P((1, 2), 0), 1) == P((1, 2), 0)"),
        Special("nestedLoopStepRowIsOneSlot", "Fibonacci(a, b) = b, a + b\nTwo(a, b) = repeat(Fibonacci(a, b), 2)\nTwo(0, 1).repeat(3)"),
        Special("nestedLoopStepRowSpread", "Fibonacci(a, b) = b, a + b\nTwo(a, b) = { repeat(Fibonacci(a, b), 2)* }\nTwo(0, 1).repeat(3)"),
        Special("callbackBodyLoopIsOneValue", "Fib(x, y) = y, x + y\n[0, 1].map({ repeat(Fib(x, 1), 2) })"),
        // Q-23 (October 2026): a loop step is an ordinary callable invoked over the current state supply —
        // family dispatch, builtin argument roles and alias targets exactly as the ordinary call; a builtin's
        // one result value is one next-state row; a value is still no step; zero iterations never project it.
        Special("loopStepClauseFamily", "Step(0) = 0\nStep(n) = n - 1\nrepeat(Step(3), 2), Step(3).repeat(5), Step(Step(3))"),
        Special("loopStepFamilyWhile", "Countdown(0) = 0, false\nCountdown(n) = n - 1, true\nwhile(Countdown(3))"),
        Special("loopStepFamilyMultiSlot", "Gcd(a, 0) = a, 0, false\nGcd(a, b) = b, a mod b, true\nwhile(Gcd(48, 18))"),
        Special("loopStepFamilyRowsAreTheNextState", "Two(0) = 9, 9\nTwo(n) = n, n\nrepeat(Two(1), 2)"),
        Special("loopStepFamilyNoMatch", "F(0) = 1\nF(1) = 2\nrepeat(F(5), 1)"),
        Special("loopStepFamilyClauseOrder", "F(x) = 1\nF(0) = 2\nrepeat(F(0), 1), F(0)"),
        Special("loopStepFamilyStructural", "Sw((a, b)) = (b, a)\nSw([a, b]) = [b, a]\nrepeat(Sw((1, 2)), 1), repeat(Sw([1, 2]), 1)"),
        Special("loopStepFamilyRepeatedName", "E(x, x) = 0, 0\nE(a, b) = a + 1, b\nrepeat(E(0, 2), 3)"),
        Special("loopStepBuiltinOneRow", "C(c) = count(c)\nrepeat(count([1, 2]), 1), repeat(C([1, 2]), 1), repeat(take([1, 2, 3], 2), 1)"),
        Special("loopStepBuiltinCollectionNextArity", "repeat(take([1, 2, 3], 2), 2)"),
        Special("loopStepBuiltinEmptyResultIsTheFlag", "while(first([()]))"),
        Special("loopStepBuiltinLazyIf", "repeat(if(false, 1 / 0, 2), 1)"),
        Special("loopStepAliasOfFamilyAndBuiltin", "Step(0) = 0\nStep(n) = n - 1\nA = Step\nC = count\nrepeat(A(3), 2), repeat(C([1, 2]), 1)"),
        Special("loopStepForwardedFamily", "Step(0) = 0\nStep(n) = n - 1\nRun(f, *s) = repeat(f(s*), 2)\nRun(Step, 3)"),
        Special("loopStepValueRejected", "Run(f) = repeat(f(0), 1)\nRun(5)"),
        Special("loopStepZeroIterationsNeverProject", "Run(f, s) = repeat(f(s), 0)\nRun(5, 1), Run(1 / 0, 5)"),
        Special("loopMetaValueRefused", "repeat(5, 1)"),
        Special("loopMetaPropertyReadRefused", "Step(x) = x + 1, x < 3\nStart = Step(0)\nStart.while"),
        Special("loopMetaPlainAndDot", "Step(x) = x + 1, x < 3\nInc(x) = x + 1\nwhile(Step(0)), Step(0).while, Step(0).while(), repeat(Inc(0), 5), Inc(0).repeat(5)"),
        Special("loopMetaZeroState", "Z = false\nZ().while, Z().repeat(0)"),
        Special("loopMetaSpreadBeforeCount", "Inc(x) = x + 1\nInc([1][5]*).repeat(1 / 0)"),
        Special("loopMetaExactArity", "Step(x) = x + 1, x < 3\nwhile(Step, 0)"),
        Special("loopMetaQualifiedCalleeCaptured", "Box = { S(x) = x + 1, x < 3 }\nBox.S(0).while"),
        Special("loopMetaBareMemberPathRefused", "Box = { S(x) = x + 1, x < 3 }\nBox.S.while"),
        Special("loopMetaRebuiltProjectedStep", "Step(x) = x + 1, x < 3\nLoop(meta op) = op.Algorithm(op.Arguments*).while\nStep(0).Loop"),
        Special("metaExtensionReceiverIsSupplied", "Add(a, b) = a + b\nCapture(meta op) = op\nR = Capture(5.Add(1))\nR.Arguments.count, R.Invoke()"),
        Special("loopMetaNamedAlias", "Box = { S(x) = x + 1, x < 3 }\nS = Box.S\nS(0).while"),
        Special("loopStepLoopBuiltinAsStep", "Step = { x + 1 }\nrepeat(repeat(Step(0), 2), 1)"),
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

        // Public but local-only: the member depends on the enclosing `Outer`'s parameter.
        // Inside `Outer` — whose activation binds that parameter — `open Lib` provides it
        // (K1-08, September 2026); outside `Outer` the same member is selected and refused
        // at the access, never given an invented meaning.
        Special("openLocalOnlyCapturedParamsInsideOwner",
            "Outer(p) = {\n    open Lib\n    Lib = {\n        public X = p + 101\n    }\n    X\n}\nOuter(1)"),

        Special("openLocalOnlyCapturedParamsOutsideOwner",
            "Outer(p) = {\n    public Lib = {\n        public X = p + 101\n    }\n    0\n}\nA = {\n    open Outer.Lib\n    X\n}\nA"),

        // A parameterized algorithm is not an open provider at all: `open` never creates the
        // activation its members would read, so the target is refused by the front end
        // (and by both evaluators at open resolution). Parse-level, hence C#-only.
        Special("providerRequiringArgumentsCannotBeOpened",
            "Lib(p) = {\n    public X = p + 101\n    X\n}\nA = {\n    open Lib\n    X\n}\nA",
            "Front-end rejection (DiagnosticCode.IllegalInOpen): the elaborated tree is a recovery tree; the evaluators refuse the same open with illegalInOpen."),

        // Q-29 A-U (decided 2026-10-06): a WRITTEN name two different providers supply is
        // invalid source, so this case is a parse-level C#-only probe; the run-time ambiguity
        // both evaluators keep — a lookup only evaluation decides — is pinned by the
        // `...AtRuntime` twin below (a dot fallback the receiver decides).
        Special("openTwoProvidersAmbiguous",
            "L1 = {\n    public X = 101\n}\nL2 = {\n    public X = 202\n}\nA = {\n    open L1, L2\n    X\n}\nA",
            "Front-end rejection (DiagnosticCode.AmbiguousOpen, Q-29 A-U): a written name two different providers supply is invalid source; the elaborated tree is a recovery tree. The run-time ambiguity is pinned by openTwoProvidersAmbiguousAtRuntime."),

        Special("openTwoProvidersAmbiguousAtRuntime",
            "L1 = {\n    public X(v) = v + 101\n}\nL2 = {\n    public X(v) = v + 202\n}\nK(p) = {\n    open L1, L2\n    p.X\n}\nK(10)"),

        // Duplicate NAMED targets are one provider and never a spurious ambiguity
        // (Q-19 D-I: providers are counted by identity; Lean: resolveAllOpens).
        Special("openDuplicateTargetDedup", "Lib = {\n    public X = 101\n}\nA = {\n    open Lib, Lib\n    X\n}\nA"),

        Special("openDuplicateDottedTargetDedup",
            "Lib = {\n    public S = {\n        public X = 101\n    }\n}\nA = {\n    open Lib.S, Lib.S\n    X\n}\nA"),

        // Q-19 D-I: two spellings of ONE declaration are one provider.
        Special("openTwoSpellingsOneProvider",
            "Lib = {\n    public Sub = {\n        public X = 101\n    }\n    public R = {\n        open Sub, Lib.Sub\n        X\n    }\n}\nLib.R"),

        // Two written blocks are two declarations, so two providers even when structurally
        // identical; a written X they both supply is invalid source (Q-29 A-U), and the
        // run-time twin pins the evaluators' ambiguity.
        Special("openDuplicateInlineBlocksAmbiguous",
            "A = {\n    open { public X = 101 }, { public X = 202 }\n    X\n}\nA",
            "Front-end rejection (DiagnosticCode.AmbiguousOpen, Q-29 A-U): a written name two different providers supply is invalid source; the elaborated tree is a recovery tree. The run-time ambiguity is pinned by openDuplicateInlineBlocksAmbiguousAtRuntime."),

        Special("openDuplicateInlineBlocksAmbiguousAtRuntime",
            "K(p) = {\n    open { public X(v) = v + 101 }, { public X(v) = v + 101 }\n    p.X\n}\nK(10)"),

        Special("openInlineBlock", "A = {\n    open { public X = 101 }\n    X\n}\nA"),

        Special("openInlineBlockPrivateHidden", "A = {\n    open { X = 101 }\n    X\n}\nA(707)"),

        Special("openDottedPath",
            "Lib = {\n    public S = {\n        public X = 101\n    }\n}\nA = {\n    open Lib.S\n    X\n}\nA"),

        // A dotted open path requires every member after the lexical head to be
        // public. Since the name-resolution audit (#8, September 2026) a target that
        // resolves to nothing is refused STATICALLY by the front end, whether or not a
        // lookup consults it (before, it silently provided nothing and `X` became an
        // implicit parameter), so the case is parse-level and C#-only; both evaluators
        // still refuse the path (notPublicProperty) as soon as a lookup demands the opens.
        Special("openDottedPathPrivateIntermediate",
            "Lib = {\n    S = {\n        public X = 101\n    }\n}\nA = {\n    open Lib.S\n    X\n}\nA(707)",
            "Front-end rejection (DiagnosticCode.UnresolvedOpenTarget): a private dotted open step provides no algorithm, so the target is refused before evaluation; the elaborated tree is a recovery tree, and both evaluators refuse the same path with notPublicProperty when a lookup demands the opens."),

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

        // A builtin is never a legal open target. Since the final audit (September 2026)
        // the front end refuses it eagerly like a parameterized provider (a builtin's
        // arity lives in registry metadata, so it is refused by kind), so the case is
        // parse-level and C#-only; both evaluators still refuse the target with
        // illegalInOpen at open resolution (Lean `resolveAlgForOpen`, CoreTests), and
        // DiagnosticProvenanceTests pins the runtime refusal over the recovery tree.
        Special("openBuiltinTargetIsIllegal",
            "Lib = {\n    public X = 101\n}\nA = {\n    open count, Lib\n    X\n}\nA",
            "Front-end rejection (DiagnosticCode.IllegalInOpen): a prelude builtin is refused as an open target before evaluation; the elaborated tree is a recovery tree, and both evaluators refuse the same open with illegalInOpen."),

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

        // A public local-only member IS provided by its open — selection is by visibility,
        // accessibility is checked on the selected member afterwards — so beside another
        // provider of the same name it is a genuine second provider (K1-08, September 2026).
        Special("openLocalOnlyMemberIsASecondProvider",
            "Pub = {\n    public X = 101\n}\nOuter(p) = {\n    public Lib = {\n        public X = p + 202\n    }\n    0\n}\nA = {\n    open Pub, Outer.Lib\n    X\n}\nA",
            "Front-end rejection (DiagnosticCode.AmbiguousOpen, Q-29 A-U): the local-only member is a genuine second provider, so the written X is invalid source; the elaborated tree is a recovery tree. The run-time selection is pinned by openLocalOnlyMemberIsASecondProviderAtRuntime."),

        Special("openLocalOnlyMemberIsASecondProviderAtRuntime",
            "Pub = {\n    public X(v) = v + 101\n}\nOuter(p) = {\n    public Lib = {\n        public X(v) = v + p\n    }\n    0\n}\nA(q) = {\n    open Pub, Outer.Lib\n    q.X\n}\nA(5)"),

        // F9: a builtin VALUE slot and the `.string` receiver demand their algorithm
        // through the ONE zero-argument demand law. A selected parameterized
        // algorithm is the arity rejection — never `unknownName x` from inside its
        // body, pinned on both sides of the differential — the unselected slot is
        // never demanded, a zero-parameter algorithm is a value, and callback
        // slots are untouched. Under the unified formula-lifting law (September 30
        // 2026) these value positions LIFT in an inferring body, so the runtime
        // demand is pinned under a closed list (`Probe(u) = ...`); the lifting itself
        // is pinned by the `formulaLifting*` specials below.
        Special("ifSelectedParameterizedBranchIsArity", "Inc(x) = x + 1\nProbe(u) = if(true, Inc, 0)\nProbe(0)"),
        Special("ifSelectedParameterizedFalseBranchIsArity", "Inc(x) = x + 1\nProbe(u) = if(false, 0, Inc)\nProbe(0)"),
        Special("ifParameterizedConditionIsArity", "Inc(x) = x + 1\nProbe(u) = if(Inc, 1, 0)\nProbe(0)"),
        Special("ifUnselectedParameterizedBranchStaysLazy", "Inc(x) = x + 1\nProbe(u) = if(false, Inc, 7)\nProbe(0)"),
        Special("ifZeroParameterBranchIsValue", "A = 7\nif(true, A, 0)"),
        Special("ifParameterIgnoringBodyStillArity", "K(x) = 5\nProbe(u) = if(true, K, 0)\nProbe(0)"),
        // September 2026: zero-argument value demand follows ACTUAL call arity, so a
        // collecting parameter (which requires no supplied argument) is demandable while a
        // required fixed parameter beside it still is not — and a nested pattern still
        // consumes its one supplied slot.
        Special("ifCollectingCallableSlotIsCollectedValue", "Collect(*xs) = xs\nif(true, Collect, 0)"),
        Special("ifCollectingCallableExplicitCallIsSameValue", "Collect(*xs) = xs\nif(true, Collect(), 0)"),
        Special("bareCollectingCallableIsAValue", "Only(*xs) = xs\nOnly"),
        Special("bareCollectingCallableCountAgreesWithDottedForm", "Only(*xs) = xs\ncount(Only), Only.count"),
        Special("ifRequiredPrefixBesideCollectorIsArity", "Head(x, *rest) = x\nProbe(u) = if(true, Head, 0)\nProbe(0)"),
        Special("ifRequiredSuffixBesideCollectorIsArity", "Tail(*rest, z) = z\nProbe(u) = if(true, Tail, 0)\nProbe(0)"),
        Special("ifNestedCollectingPatternIsArity", "P((x, *rest)) = x\nProbe(u) = if(true, P, 0)\nProbe(0)"),
        Special("collectingCallableStaysACallbackAlgorithm", "Only(*xs) = xs\nmap((1, 2), Only)"),
        Special("ifAlgorithmChannelParameterSlotIsArity", "Inc(x) = x + 1\nApply(g) = if(true, g, 0)\nApply(Inc)"),
        Special("repeatInitialParameterizedSlotIsArity", "Inc(x) = x + 1\nStep(s) = s + 1\nProbe(u) = repeat(Step(Inc), 1)\nProbe(0)"),
        Special("repeatCountParameterizedSlotIsArity", "Inc(x) = x + 1\nStep(s) = s + 1\nProbe(u) = repeat(Step(0), Inc)\nProbe(0)"),
        Special("whileInitialParameterizedSlotIsArity", "Inc(x) = x + 1\nDown(s) = s - 1, s\nProbe(u) = while(Down(Inc))\nProbe(0)"),
        Special("atomsParameterizedSlotIsArity", "Inc(x) = x + 1\nProbe(u) = atoms(Inc)\nProbe(0)"),
        Special("rangeParameterizedSlotIsArity", "Inc(x) = x + 1\nProbe(u) = range(1, Inc)\nProbe(0)"),
        Special("dotStringParameterizedReceiverIsArity", "Inc(x) = x + 1\nProbe(u) = Inc.string\nProbe(0)"),
        Special("dotStringNavigatedParameterizedMemberIsArity", "Lib = { Sub(x) = x }\nProbe(u) = Lib.Sub.string\nProbe(0)"),
        Special("reduceParameterIgnoringInitialStillRejected", "K(x) = 5\nAdd(e, a) = e + a\nProbe(u) = reduce([1, 2], Add, K)\nProbe(0)"),
        Special("repeatParameterizedStepIsCallback", "Inc(x) = x + 1\nrepeat(Inc(0), 2)"),
        // THE UNIFIED FORMULA-LIFTING LAW (September 30 2026): a reference in a VALUE position
        // lifts, whatever callable it resolves to and however it was reached, and the role is the
        // immediate consumer's — recursive and blind to laziness — while callbacks and whole user
        // arguments keep the callable. Pinned against Lean on the elaborated (lifted) trees.
        Special("formulaLiftingIfBranchLiftsWhileStayingLazy", "Inc(x) = x + 1\nG = if(false, Inc, 7)\nG(4)"),
        Special("formulaLiftingRootValuePositionNeedsTheParameter", "Inc(x) = x + 1\nif(true, Inc, 0)"),
        Special("formulaLiftingBuiltinValueSlot", "Inc(x) = x + 1\nG = count(Inc)\nG(4)"),
        Special("formulaLiftingBuiltinSignature", "G = count + 0\nG((1, 2, 3))"),
        Special("formulaLiftingLoopSignature", "Step(s) = s + 1\nG = repeat + 0\nG(Step, 2, 0)"),
        Special("formulaLiftingDottedMember", "Lib = {\n    public Inc(x) = x + 1\n}\nG = Lib.Inc + 0\nG(4)"),
        Special("formulaLiftingOpenedMember", "Lib = {\n    public Inc(x) = x + 1\n}\nG = {\n    open Lib\n    Inc + 0\n}\nG(4)"),
        Special("formulaLiftingClauseFamily", "E(0) = 100\nE(n) = n\nG = E + 1\nG(0), G(5)"),
        Special("formulaLiftingCaptureElement", "Inc(x) = x + 1\nG = (Inc, 0)\nG(4)"),
        Special("formulaLiftingStringReceiver", "Inc(x) = x + 1\nG = Inc.string\nG(3000)"),
        Special("formulaLiftingNestedInUserArgument", "Inc(x) = x + 1\nId(v) = v\nG = Id(Inc + 0)\nG(4)"),
        Special("formulaLiftingKeepsCallbacks", "Inc(x) = x + 1\nG = map([1, 2], Inc)\nG"),
        Special("formulaLiftingKeepsUserArguments", "Inc(x) = x + 1\nApply(f) = f(10)\nG = Apply(Inc)\nG"),
        // Q-05 (September 29 2026): REPEATED NAMES ARE CONSTRAINTS, NOT MERGES. Every occurrence
        // of a repeated parameter name supplies its own value, so a callable-only or failed
        // argument is its own failure in either position — never a binding that pairs one
        // argument's value with another's callable — while a callable still accompanies an
        // equal value its own argument supplied. Pinned against Lean on the parsed trees.
        Special("repeatedNameCallableThenValue", "Inc(y) = y + 1\nP(x, x) = x, x(5)\nP(Inc, 1)"),
        Special("repeatedNameValueThenCallable", "Inc(y) = y + 1\nP(x, x) = x, x(5)\nP(1, Inc)"),
        Special("repeatedNameFailedThenValue", "Bad = 1 / 0\nQ(x, x) = x\nQ(Bad, 7)"),
        Special("repeatedNameValueThenFailed", "Bad = 1 / 0\nQ(x, x) = x\nQ(7, Bad)"),
        Special("repeatedNameAcrossCollectorCallable", "Inc(y) = y + 1\nC(x, *r, x) = x\nC(Inc, 9, 1)"),
        Special("repeatedNameAcrossNestedGroupFailed", "Bad = 1 / 0\nN(x, (x, y)) = y\nN(Bad, (7, 8))"),
        Special("repeatedNameForwardedCallable", "Inc(y) = y + 1\nP(x, x) = x, x(5)\nFwd(a, b) = P(a, b)\nFwd(1, Inc)"),
        Special("repeatedNameDotReceiverFailed", "Bad = 1 / 0\nQ(x, x) = x\nBad.Q(7)"),
        Special("repeatedNameValuelessBeforeVerdict", "Bad = 1 / 0\nQ2(x, x, y, y) = 0\nQ2(Bad, 7, 1, 2)"),
        Special("repeatedNameAccompanyingChannel", "A = 5\nP(f, f) = f, f()\nP(5, A)"),
        // Formula lifting is by binding name (September 29 2026, reversing the Q-72 refusal): a
        // callee a formula USES that repeats a name — at the top level, inside one group, across
        // groups, beside a collector, under a closed list that binds it — receives the caller's ONE
        // binding at every occurrence (`Some = [P][0]` is `Some(x) = [P(x, x)][0]`), exactly as a name
        // shared across callees does; a failed or callable-only argument stays its own failure.
        // Pinned against Lean on the elaborated trees.
        Special("forwardByNameAlias", "P(x, x) = x\nSome = [P][0]\nSome(7)"),
        Special("forwardByNameThreeOccurrences", "P(x, x, x) = x\nSome = [P][0]\nSome(7)"),
        Special("forwardByNameNestedGroup", "P((x, a), x) = a\nSome = [P][0]\nSome((7, 8))"),
        Special("forwardByNameAcrossGroup", "P(x, (x, a)) = a\nSome = [P][0]\nSome(7, 8)"),
        Special("forwardByNameInsideOneGroup", "P((x, x)) = x\nSome = [P][0]\nSome(7)"),
        Special("forwardByNameBesideCollector", "P(x, *rest, x) = rest\nSome = [P][0]\nSome(7, 1, 2)"),
        Special("forwardByNameClosedList", "P(x, x) = x\nQ(x) = [P][0]\nQ(7)"),
        Special("forwardByNameAcrossCallees", "P(x, x) = x\nF(x) = x + 1\nH = P + F\nH(3)"),
        Special("forwardByNameFailedArgument", "Bad = 1 / 0\nP(x, x) = x\nSome = [P][0]\nSome(Bad)"),
        Special("forwardByNameCallableArgument", "Inc(y) = y + 1\nP(x, x) = x, x(5)\nSome = [P][0]\nSome(Inc)"),
        // FWD-02 (September 29–30 2026; binding indirection October 1 2026): a body whose ONE row
        // is a bare callable that declares parameterized structure is a CALLABLE ALIAS (an open
        // body: `Algorithm.alias`, whose every callable use is the target's own — no wrapper, no
        // copied signature) or BARE FORWARDING (a written list or a clause branch: each callee
        // parameter supplied BY NAME from an existing compatible binding — never renamed, never
        // positional, never added), and a written call infers only the names it writes. Pinned
        // against Lean on the elaborated trees (Lean resolves each `.alias` in its own scope); the
        // rejected forms are front-end diagnostics, pinned by the spec corpus's
        // `bare-forwarding-*` cases and by Lean's `bareForwardingRow` / `bareForwardingRowOf`.
        Special("aliasKeepsRepeatedSignature", "P(x, x) = x\nA = P\nA(7, 7)"),
        Special("aliasKeepsRepeatedConstraint", "P(x, x) = x\nA = P\nA(7, 8)"),
        Special("aliasKeepsListPattern", "Single([x]) = x\nA = Single\nA([7]), A([[7]])"),
        Special("aliasKeepsListPatternRejection", "Single([x]) = x\nA = Single\nA(7)"),
        Special("aliasKeepsBinderlessSignature", "E((), []) = 1\nA = E\nA((), [])"),
        Special("aliasOfCollectorKeepsSignature", "C(*xs) = xs\nA = C\nA(1, 2)"),
        Special("aliasChainKeepsSignature", "Single([x]) = x\nA = Single\nB = A\nC = B\nC([[7]])"),
        // Every builtin, every clause family (an unnameable one included) is an alias target, and a
        // call through the alias is the target's own: the builtin adapter, `if`'s laziness, a callback
        // slot's non-demand, a loop's minimum arity, family dispatch; roles, callable identity,
        // bare forwarding and formula lifting all read the normalized target.
        Special("aliasOfBuiltinCount", "C = count\nC([1, 2, 3])"),
        Special("aliasOfIfIsLazy", "I = if\nI(true, 1, 1 / 0)"),
        Special("aliasOfMapDemandsNoCallback", "Bad(x) = x / 0\nM = map\nM([], Bad)"),
        Special("aliasOfRepeatKeepsMinimumArity", "Inc(x) = x + 1\nR = repeat\nR(Inc)"),
        Special("aliasChainOfBuiltin", "A = count\nB = A\nC = B\nC([1, 2])"),
        Special("aliasOfFamilyDispatches", "Fact(0) = 1\nFact(n) = n * Fact(n - 1)\nF = Fact\nF(4)"),
        Special("aliasOfFamilyNoMatchingBranch", "Fact(0) = 1\nFact(n) = n * Fact(n - 1)\nF = Fact\nF(1, 2)"),
        Special("aliasOfUnnameableFamily", "S(1) = 1\nS(-1) = -1\nSA = S\nSA(-1)"),
        Special("aliasRolesAreTargetRoles", "Inc(x) = x + 1\nI = if\nK = I(c, Inc, 0)\nK(true, 4)"),
        Special("aliasCallableIdentityIsTarget", "P(f, f) = f(7)\nOnly(*xs) = 0\nA = Only\nP(A, Only)"),
        Special("aliasPassedAsCallableNavigatesTarget", "Lib(x) = {\n  K = 5\n  x\n}\nA = Lib\nNavigate(f) = f.K\nNavigate(A)"),
        Special("bareForwardingThroughAlias", "C = count\nW(collection) = C\nW([1, 2])"),
        Special("formulaLiftingThroughAlias", "C = count\nK = C + 1\nK([1, 2])"),
        Special("bareForwardingSameName", "Double(x) = x * 2\nForward(x) = Double\nForward(5)"),
        Special("bareForwardingIsNotPositional", "Sub(y, x) = y - x\nG(x, y) = Sub\nG(10, 3)"),
        Special("bareForwardingIgnoresUnusedParameter", "Double(x) = x * 2\nForward(x, unused) = Double\nForward(5, 999)"),
        Special("bareForwardingOfAZeroParameterTarget", "Ten = 10\nAlways(p) = Ten\nAlways(999)"),
        Special("bareForwardingSamePattern", "Single([x]) = x\nG([x]) = Single\nG([7]), G([[7]])"),
        Special("bareForwardingRespreadsItsCollector", "Coll(*vs) = vs\nG(*vs) = Coll\nG(1, 2)"),
        Special("bareForwardingBranchForwardsItsBinder", "F(n) = n * 10\nG(0) = 0\nG(n) = F\nG(0), G(3)"),
        Special("bareForwardingReusesEnclosingBinding", "A = y + 1\nG = {\n  F(x) = A\n  F(1) + y\n}\nG(10)"),
        Special("bareForwardingRepeatedName", "P(x, x) = x\nQ(x) = P\nQ(7)"),
        Special("writtenCallInfersWrittenNames", "Add((a, b)) = a + b\nG = Add((x, y))\nG(2, 3)"),
        Special("writtenCallIgnoresCalleeBinderNames", "Add((left, right)) = left + right\nG = Add((x, y))\nG(2, 3)"),
        // Bug hunt 2026-11-20 (Lean differential): adversarial programs on which C# and Lean agree.
        Special("huntGenLoopsAG0000", "H(x) = x * 2 + 1\nG(x, y) = x - y\nSq(x) = x * x\nPick(x) = [10, 20, 30][x mod 3]\nNeg(x) = -x\nCl(0) = 100\nCl(x) = x + 1\nTwo(x) = x, x + 1\nBox = {\n  public K = 7\n  public F(x) = x + 3\n}\nn0 = 4\nStep(n, acc) = {\n  T0 = Sq((max((n, 1))) mod 5)\n  n + 1, (G(n * T0, acc)) mod 1000\n}\nrepeat(Step(0, 3), 3), n0"),
        Special("huntGenLoopsAG0001", "H(x) = x * 2 + 1\nG(x, y) = x - y\nSq(x) = x * x\nPick(x) = [10, 20, 30][x mod 3]\nNeg(x) = -x\nCl(0) = 100\nCl(x) = x + 1\nTwo(x) = x, x + 1\nBox = {\n  public K = 7\n  public F(x) = x + 3\n}\nn0 = 4\nStep(n, acc) = {\n  T0 = 0 + acc\n  n + 1, (Cl(if(acc < 3, acc, n))) mod 1000\n}\nStep(0, 0).repeat(5), n0"),
        Special("huntGenLoopsAG0002", "H(x) = x * 2 + 1\nG(x, y) = x - y\nSq(x) = x * x\nPick(x) = [10, 20, 30][x mod 3]\nNeg(x) = -x\nCl(0) = 100\nCl(x) = x + 1\nTwo(x) = x, x + 1\nBox = {\n  public K = 7\n  public F(x) = x + 3\n}\nStep(n, acc) = n + 1, (acc + n) mod 1000\nStep(2, 3).repeat(2), Step(1, 1)"),
        Special("huntGenLoopsAG0003", "H(x) = x * 2 + 1\nG(x, y) = x - y\nSq(x) = x * x\nPick(x) = [10, 20, 30][x mod 3]\nNeg(x) = -x\nCl(0) = 100\nCl(x) = x + 1\nTwo(x) = x, x + 1\nBox = {\n  public K = 7\n  public F(x) = x + 3\n}\nn0 = 4\nStep(n, acc) = {\n  T0 = (5) div 3\n  T1 = (7) div 1\n  T2 = 5 + max((5 - n, (5) mod 4))\n  n + 1, (G(n, 8) - max((acc, 2))) mod 1000\n}\nrepeat(Step(1, -1), 2), n0"),
        Special("huntGenLoopsAG0004", "H(x) = x * 2 + 1\nG(x, y) = x - y\nSq(x) = x * x\nPick(x) = [10, 20, 30][x mod 3]\nNeg(x) = -x\nCl(0) = 100\nCl(x) = x + 1\nTwo(x) = x, x + 1\nBox = {\n  public K = 7\n  public F(x) = x + 3\n}\nn0 = 4\nStep(n, acc) = {\n  T0 = [acc, acc, 5].sum\n  n + 1, (6 + 6) mod 1000\n}\nrepeat(Step(1, -1), 2), n0"),
        Special("huntGenLoopsAG0005", "H(x) = x * 2 + 1\nG(x, y) = x - y\nSq(x) = x * x\nPick(x) = [10, 20, 30][x mod 3]\nNeg(x) = -x\nCl(0) = 100\nCl(x) = x + 1\nTwo(x) = x, x + 1\nBox = {\n  public K = 7\n  public F(x) = x + 3\n}\nStep(n, acc) = {\n  T0 = Sq((2) mod 5)\n  n + 1, (H(acc)) mod 1000\n}\nrepeat(Step(1, 3), 0), Step(1, 1)"),
        Special("huntGenLoopsAG0006", "H(x) = x * 2 + 1\nG(x, y) = x - y\nSq(x) = x * x\nPick(x) = [10, 20, 30][x mod 3]\nNeg(x) = -x\nCl(0) = 100\nCl(x) = x + 1\nTwo(x) = x, x + 1\nBox = {\n  public K = 7\n  public F(x) = x + 3\n}\nStep(n, acc) = {\n  T0 = if((n) mod 2 == 0 and -1 > 0, acc, Box.K)\n  n + 1, (Pick(7)) mod 1000\n}\nrepeat(Step(0, -1), 3), Step(1, 1)"),
        Special("huntGenLoopsAG0007", "H(x) = x * 2 + 1\nG(x, y) = x - y\nSq(x) = x * x\nPick(x) = [10, 20, 30][x mod 3]\nNeg(x) = -x\nCl(0) = 100\nCl(x) = x + 1\nTwo(x) = x, x + 1\nBox = {\n  public K = 7\n  public F(x) = x + 3\n}\nStep(n, acc) = {\n  T0 = H(8)\n  T1 = [acc, if(acc < 4, n, T0), 5].sum\n  n + 1, (max((T1 + 9, -1))) mod 1000, n < 5\n}\nStep(2, 3).while"),
        Special("huntGenLoopsAG0008", "H(x) = x * 2 + 1\nG(x, y) = x - y\nSq(x) = x * x\nPick(x) = [10, 20, 30][x mod 3]\nNeg(x) = -x\nCl(0) = 100\nCl(x) = x + 1\nTwo(x) = x, x + 1\nBox = {\n  public K = 7\n  public F(x) = x + 3\n}\nStep(n, acc) = n + 1, (max((n, acc)) + n) mod 1000\nStep(1, -1).repeat(5), Step(1, 1)"),
        Special("huntGenLoopsAG0009", "H(x) = x * 2 + 1\nG(x, y) = x - y\nSq(x) = x * x\nPick(x) = [10, 20, 30][x mod 3]\nNeg(x) = -x\nCl(0) = 100\nCl(x) = x + 1\nTwo(x) = x, x + 1\nBox = {\n  public K = 7\n  public F(x) = x + 3\n}\nStep(n, acc) = n + 1, ((-1) mod 2) mod 1000\nrepeat(Step(0, -2), 1), Step(1, 1)"),
        Special("huntGenLoopsAG0010", "H(x) = x * 2 + 1\nG(x, y) = x - y\nSq(x) = x * x\nPick(x) = [10, 20, 30][x mod 3]\nNeg(x) = -x\nCl(0) = 100\nCl(x) = x + 1\nTwo(x) = x, x + 1\nBox = {\n  public K = 7\n  public F(x) = x + 3\n}\nn0 = 4\nStep(n, acc) = {\n  T0 = -3 - n\n  n + 1, (n + T0) mod 1000, n < 6\n}\nwhile(Step(2, -2)), n0"),
        Special("huntGenLoopsAG0011", "H(x) = x * 2 + 1\nG(x, y) = x - y\nSq(x) = x * x\nPick(x) = [10, 20, 30][x mod 3]\nNeg(x) = -x\nCl(0) = 100\nCl(x) = x + 1\nTwo(x) = x, x + 1\nBox = {\n  public K = 7\n  public F(x) = x + 3\n}\nn0 = 4\nStep(n, acc) = {\n  T0 = n + H(n)\n  T1 = Cl(3)\n  T2 = G(0, acc)\n  n + 1, ([acc, 4, 5].sum) mod 1000\n}\nrepeat(Step(1, -2), 1), n0"),
        Special("huntGenLoopsAG0012", "H(x) = x * 2 + 1\nG(x, y) = x - y\nSq(x) = x * x\nPick(x) = [10, 20, 30][x mod 3]\nNeg(x) = -x\nCl(0) = 100\nCl(x) = x + 1\nTwo(x) = x, x + 1\nBox = {\n  public K = 7\n  public F(x) = x + 3\n}\nStep(n, acc) = n + 1, (H(-3)) mod 1000\nrepeat(Step(0, 0), 4), Step(1, 1)"),
        Special("huntGenLoopsAG0013", "H(x) = x * 2 + 1\nG(x, y) = x - y\nSq(x) = x * x\nPick(x) = [10, 20, 30][x mod 3]\nNeg(x) = -x\nCl(0) = 100\nCl(x) = x + 1\nTwo(x) = x, x + 1\nBox = {\n  public K = 7\n  public F(x) = x + 3\n}\nStep(n, acc) = {\n  T0 = max((1, -2 + n))\n  T1 = n + acc\n  n + 1, (T1 - acc) mod 1000, n < 6\n}\nwhile(Step(1, 1))"),
        Special("huntGenLoopsAG0014", "H(x) = x * 2 + 1\nG(x, y) = x - y\nSq(x) = x * x\nPick(x) = [10, 20, 30][x mod 3]\nNeg(x) = -x\nCl(0) = 100\nCl(x) = x + 1\nTwo(x) = x, x + 1\nBox = {\n  public K = 7\n  public F(x) = x + 3\n}\nn0 = 4\nStep(n, acc) = {\n  T0 = if((1) mod 2 == 0 and [if((n) mod 2 == 0 and -3 > 0, acc, Box.K), 6, 5].sum > 0, acc, Box.K)\n  n + 1, (3 + acc) mod 1000\n}\nrepeat(Step(2, -2), 5), n0"),
        Special("huntGenLoopsAG0015", "H(x) = x * 2 + 1\nG(x, y) = x - y\nSq(x) = x * x\nPick(x) = [10, 20, 30][x mod 3]\nNeg(x) = -x\nCl(0) = 100\nCl(x) = x + 1\nTwo(x) = x, x + 1\nBox = {\n  public K = 7\n  public F(x) = x + 3\n}\nStep(n, acc) = {\n  T0 = Pick((Sq((5) mod 5)) div 4)\n  T1 = (6 * n) div 3\n  n + 1, (if((T0) mod 2 == 0 and 6 > 0, if(8 < 0, acc, T1 - acc), Box.K)) mod 1000\n}\nrepeat(Step(1, 1), 3)"),
        Special("huntGenLoopsAG0016", "H(x) = x * 2 + 1\nG(x, y) = x - y\nSq(x) = x * x\nPick(x) = [10, 20, 30][x mod 3]\nNeg(x) = -x\nCl(0) = 100\nCl(x) = x + 1\nTwo(x) = x, x + 1\nBox = {\n  public K = 7\n  public F(x) = x + 3\n}\nStep(n, acc) = {\n  T0 = Pick(n - acc)\n  n + 1, (if(([n, T0, 5].sum) div 3 < T0, n, 1)) mod 1000\n}\nStep(2, 1).repeat(1), Step(1, 1)"),
        Special("huntGenLoopsAG0017", "H(x) = x * 2 + 1\nG(x, y) = x - y\nSq(x) = x * x\nPick(x) = [10, 20, 30][x mod 3]\nNeg(x) = -x\nCl(0) = 100\nCl(x) = x + 1\nTwo(x) = x, x + 1\nBox = {\n  public K = 7\n  public F(x) = x + 3\n}\nn0 = 4\nStep(n, acc) = {\n  T0 = acc + (acc) div 4\n  n + 1, (acc + n * 8) mod 1000\n}\nrepeat(Step(0, 3), 4), n0"),
        Special("huntGenLoopsAG0018", "H(x) = x * 2 + 1\nG(x, y) = x - y\nSq(x) = x * x\nPick(x) = [10, 20, 30][x mod 3]\nNeg(x) = -x\nCl(0) = 100\nCl(x) = x + 1\nTwo(x) = x, x + 1\nBox = {\n  public K = 7\n  public F(x) = x + 3\n}\nStep(n, acc) = n + 1, ((Sq((H(n)) mod 5)) mod 4) mod 1000\nrepeat(Step(2, 2), 1), Step(1, 1)"),
        Special("huntGenLoopsAG0019", "H(x) = x * 2 + 1\nG(x, y) = x - y\nSq(x) = x * x\nPick(x) = [10, 20, 30][x mod 3]\nNeg(x) = -x\nCl(0) = 100\nCl(x) = x + 1\nTwo(x) = x, x + 1\nBox = {\n  public K = 7\n  public F(x) = x + 3\n}\nStep(n, acc) = {\n  T0 = (acc) div 2 - acc\n  T1 = [2, -3, 5].sum\n  T2 = Pick(9)\n  n + 1, (G(max((acc, acc)) + T2, acc)) mod 1000\n}\nStep(2, 0).repeat(2), Step(1, 1)"),
        Special("huntGenLoopsAG0020", "H(x) = x * 2 + 1\nG(x, y) = x - y\nSq(x) = x * x\nPick(x) = [10, 20, 30][x mod 3]\nNeg(x) = -x\nCl(0) = 100\nCl(x) = x + 1\nTwo(x) = x, x + 1\nBox = {\n  public K = 7\n  public F(x) = x + 3\n}\nn0 = 4\nStep(n, acc) = n + 1, (Pick(-3)) mod 1000\nrepeat(Step(2, 1), 5), n0"),
        Special("huntGenLoopsAG0021", "H(x) = x * 2 + 1\nG(x, y) = x - y\nSq(x) = x * x\nPick(x) = [10, 20, 30][x mod 3]\nNeg(x) = -x\nCl(0) = 100\nCl(x) = x + 1\nTwo(x) = x, x + 1\nBox = {\n  public K = 7\n  public F(x) = x + 3\n}\nStep(n, acc) = {\n  T0 = Pick(8)\n  T1 = if((0) mod 2 == 0 and n > 0, acc, Box.K)\n  n + 1, (if((T0) div 3 < T0, acc, n)) mod 1000\n}\nrepeat(Step(2, -2), 4)"),
        Special("huntGenLoopsAG0022", "H(x) = x * 2 + 1\nG(x, y) = x - y\nSq(x) = x * x\nPick(x) = [10, 20, 30][x mod 3]\nNeg(x) = -x\nCl(0) = 100\nCl(x) = x + 1\nTwo(x) = x, x + 1\nBox = {\n  public K = 7\n  public F(x) = x + 3\n}\nStep(n, acc) = {\n  T0 = Cl(acc)\n  T1 = Cl(Cl(acc))\n  n + 1, (T1 * n + acc) mod 1000, n < 2\n}\nStep(0, 2).while"),
        Special("huntGenLoopsAG0023", "H(x) = x * 2 + 1\nG(x, y) = x - y\nSq(x) = x * x\nPick(x) = [10, 20, 30][x mod 3]\nNeg(x) = -x\nCl(0) = 100\nCl(x) = x + 1\nTwo(x) = x, x + 1\nBox = {\n  public K = 7\n  public F(x) = x + 3\n}\nStep(n, acc) = {\n  T0 = (4) mod 1\n  T1 = H(n)\n  n + 1, (-(T1)) mod 1000\n}\nrepeat(Step(1, 2), 5), Step(1, 1)"),
        Special("huntGenLoopsAG0024", "H(x) = x * 2 + 1\nG(x, y) = x - y\nSq(x) = x * x\nPick(x) = [10, 20, 30][x mod 3]\nNeg(x) = -x\nCl(0) = 100\nCl(x) = x + 1\nTwo(x) = x, x + 1\nBox = {\n  public K = 7\n  public F(x) = x + 3\n}\nStep(n, acc) = n + 1, (n - (acc) mod 1) mod 1000, n < 5\nwhile(Step(0, 1))"),
        Special("huntGenFusionAU0000", "Inc(x) = x + 1\nEven(x) = x mod 2 == 0\nBig(x) = x > 3\nPair((a, b)) = a < b\nL = [1, 2, 3, 4, 5, 6]\nS = 1, 2, 3, 4\nE = []\nNested = [(1, 2), (3, 1), (2, 5)]\nAliasEven = Even\nBad = 1 / 0\nPos = { x > 0 }\nT = tick()\nmap(L, { x * 3 }).filter({ false }).count, tick()"),
        Special("huntGenFusionAU0001", "Inc(x) = x + 1\nEven(x) = x mod 2 == 0\nBig(x) = x > 3\nPair((a, b)) = a < b\nL = [1, 2, 3, 4, 5, 6]\nS = 1, 2, 3, 4\nE = []\nNested = [(1, 2), (3, 1), (2, 5)]\nAliasEven = Even\nBad = 1 / 0\nPos = { x > 0 }\nT = tick()\nfilter(range(1, 8), { x mod 3 == 0 }).count"),
        Special("huntGenFusionAU0002", "Inc(x) = x + 1\nEven(x) = x mod 2 == 0\nBig(x) = x > 3\nPair((a, b)) = a < b\nL = [1, 2, 3, 4, 5, 6]\nS = 1, 2, 3, 4\nE = []\nNested = [(1, 2), (3, 1), (2, 5)]\nAliasEven = Even\nBad = 1 / 0\nPos = { x > 0 }\nT = tick()\nfilter([], { x > T }).count(), 1"),
        Special("huntGenFusionAU0003", "Inc(x) = x + 1\nEven(x) = x mod 2 == 0\nBig(x) = x > 3\nPair((a, b)) = a < b\nL = [1, 2, 3, 4, 5, 6]\nS = 1, 2, 3, 4\nE = []\nNested = [(1, 2), (3, 1), (2, 5)]\nAliasEven = Even\nBad = 1 / 0\nPos = { x > 0 }\nT = tick()\nF = (L*, 7).filter(AliasEven)\nF.count, F"),
        Special("huntGenFusionAU0004", "Inc(x) = x + 1\nEven(x) = x mod 2 == 0\nBig(x) = x > 3\nPair((a, b)) = a < b\nL = [1, 2, 3, 4, 5, 6]\nS = 1, 2, 3, 4\nE = []\nNested = [(1, 2), (3, 1), (2, 5)]\nAliasEven = Even\nBad = 1 / 0\nPos = { x > 0 }\nT = tick()\ncount([T, T + 1, T + 2].filter(Big)) + count([T, T + 1, T + 2])"),
        Special("huntGenFusionAU0005", "Inc(x) = x + 1\nEven(x) = x mod 2 == 0\nBig(x) = x > 3\nPair((a, b)) = a < b\nL = [1, 2, 3, 4, 5, 6]\nS = 1, 2, 3, 4\nE = []\nNested = [(1, 2), (3, 1), (2, 5)]\nAliasEven = Even\nBad = 1 / 0\nPos = { x > 0 }\nT = tick()\ncount(range(0, 5).filter({ count([x]) == 1 })) + count(range(0, 5))"),
        Special("huntGenFusionAU0006", "Inc(x) = x + 1\nEven(x) = x mod 2 == 0\nBig(x) = x > 3\nPair((a, b)) = a < b\nL = [1, 2, 3, 4, 5, 6]\nS = 1, 2, 3, 4\nE = []\nNested = [(1, 2), (3, 1), (2, 5)]\nAliasEven = Even\nBad = 1 / 0\nPos = { x > 0 }\nT = tick()\n(range(0, 5).filter({ x mod 3 == 0 })).count"),
        Special("huntGenFusionAU0007", "Inc(x) = x + 1\nEven(x) = x mod 2 == 0\nBig(x) = x > 3\nPair((a, b)) = a < b\nL = [1, 2, 3, 4, 5, 6]\nS = 1, 2, 3, 4\nE = []\nNested = [(1, 2), (3, 1), (2, 5)]\nAliasEven = Even\nBad = 1 / 0\nPos = { x > 0 }\nT = tick()\nS.filter(Pos).count"),
        Special("huntGenFusionAU0008", "Inc(x) = x + 1\nEven(x) = x mod 2 == 0\nBig(x) = x > 3\nPair((a, b)) = a < b\nL = [1, 2, 3, 4, 5, 6]\nS = 1, 2, 3, 4\nE = []\nNested = [(1, 2), (3, 1), (2, 5)]\nAliasEven = Even\nBad = 1 / 0\nPos = { x > 0 }\nT = tick()\ncount(L.take(3).filter(AliasEven)) + count(L.take(3))"),
        Special("huntGenFusionAU0009", "Inc(x) = x + 1\nEven(x) = x mod 2 == 0\nBig(x) = x > 3\nPair((a, b)) = a < b\nL = [1, 2, 3, 4, 5, 6]\nS = 1, 2, 3, 4\nE = []\nNested = [(1, 2), (3, 1), (2, 5)]\nAliasEven = Even\nBad = 1 / 0\nPos = { x > 0 }\nT = tick()\n([1, 2, 3].filter({ x > tick() })).count"),
        Special("huntGenFusionAU0010", "Inc(x) = x + 1\nEven(x) = x mod 2 == 0\nBig(x) = x > 3\nPair((a, b)) = a < b\nL = [1, 2, 3, 4, 5, 6]\nS = 1, 2, 3, 4\nE = []\nNested = [(1, 2), (3, 1), (2, 5)]\nAliasEven = Even\nBad = 1 / 0\nPos = { x > 0 }\nT = tick()\ncount(filter((1, 2, 3), { x == x }))"),
        Special("huntGenFusionAU0011", "Inc(x) = x + 1\nEven(x) = x mod 2 == 0\nBig(x) = x > 3\nPair((a, b)) = a < b\nL = [1, 2, 3, 4, 5, 6]\nS = 1, 2, 3, 4\nE = []\nNested = [(1, 2), (3, 1), (2, 5)]\nAliasEven = Even\nBad = 1 / 0\nPos = { x > 0 }\nT = tick()\ncount([3, -1, 4, -1, 5].filter({ x })) + count([3, -1, 4, -1, 5])"),
        Special("huntGenFusionAU0012", "Inc(x) = x + 1\nEven(x) = x mod 2 == 0\nBig(x) = x > 3\nPair((a, b)) = a < b\nL = [1, 2, 3, 4, 5, 6]\nS = 1, 2, 3, 4\nE = []\nNested = [(1, 2), (3, 1), (2, 5)]\nAliasEven = Even\nBad = 1 / 0\nPos = { x > 0 }\nT = tick()\nfilter([3, -1, 4, -1, 5], { true }).count"),
        Special("huntGenFusionAU0013", "Inc(x) = x + 1\nEven(x) = x mod 2 == 0\nBig(x) = x > 3\nPair((a, b)) = a < b\nL = [1, 2, 3, 4, 5, 6]\nS = 1, 2, 3, 4\nE = []\nNested = [(1, 2), (3, 1), (2, 5)]\nAliasEven = Even\nBad = 1 / 0\nPos = { x > 0 }\nT = tick()\ncount(range(3, 3).filter(Even)) + count(range(3, 3))"),
        Special("huntGenFusionAU0014", "Inc(x) = x + 1\nEven(x) = x mod 2 == 0\nBig(x) = x > 3\nPair((a, b)) = a < b\nL = [1, 2, 3, 4, 5, 6]\nS = 1, 2, 3, 4\nE = []\nNested = [(1, 2), (3, 1), (2, 5)]\nAliasEven = Even\nBad = 1 / 0\nPos = { x > 0 }\nT = tick()\nfilter(S, Pair).count(), 1"),
        Special("huntGenFusionAU0015", "Inc(x) = x + 1\nEven(x) = x mod 2 == 0\nBig(x) = x > 3\nPair((a, b)) = a < b\nL = [1, 2, 3, 4, 5, 6]\nS = 1, 2, 3, 4\nE = []\nNested = [(1, 2), (3, 1), (2, 5)]\nAliasEven = Even\nBad = 1 / 0\nPos = { x > 0 }\nT = tick()\n(range(1, 8).filter(Even)).count"),
        Special("huntGenFusionAU0016", "Inc(x) = x + 1\nEven(x) = x mod 2 == 0\nBig(x) = x > 3\nPair((a, b)) = a < b\nL = [1, 2, 3, 4, 5, 6]\nS = 1, 2, 3, 4\nE = []\nNested = [(1, 2), (3, 1), (2, 5)]\nAliasEven = Even\nBad = 1 / 0\nPos = { x > 0 }\nT = tick()\nfilter([1, 'a', 3], Pos).count"),
        Special("huntGenFusionAU0017", "Inc(x) = x + 1\nEven(x) = x mod 2 == 0\nBig(x) = x > 3\nPair((a, b)) = a < b\nL = [1, 2, 3, 4, 5, 6]\nS = 1, 2, 3, 4\nE = []\nNested = [(1, 2), (3, 1), (2, 5)]\nAliasEven = Even\nBad = 1 / 0\nPos = { x > 0 }\nT = tick()\n([1, 2, 3].filter({ x })).count"),
        Special("huntGenFusionAU0018", "Inc(x) = x + 1\nEven(x) = x mod 2 == 0\nBig(x) = x > 3\nPair((a, b)) = a < b\nL = [1, 2, 3, 4, 5, 6]\nS = 1, 2, 3, 4\nE = []\nNested = [(1, 2), (3, 1), (2, 5)]\nAliasEven = Even\nBad = 1 / 0\nPos = { x > 0 }\nT = tick()\ncount(filter([], Even))"),
        Special("huntGenFusionAU0019", "Inc(x) = x + 1\nEven(x) = x mod 2 == 0\nBig(x) = x > 3\nPair((a, b)) = a < b\nL = [1, 2, 3, 4, 5, 6]\nS = 1, 2, 3, 4\nE = []\nNested = [(1, 2), (3, 1), (2, 5)]\nAliasEven = Even\nBad = 1 / 0\nPos = { x > 0 }\nT = tick()\ncount(filter(range(1, 8), Even))"),
        Special("huntGenFaultsAF0000", "Bad = 1 / 0\nInc(x) = x + 1\nId(v) = v\nTwo(a, b) = a * 10 + b\nBox = { public K = 5 }\nUse(a, b) = a + b\nFst(a, b) = a\nSnd(a, b) = b\nColl(*xs) = xs\nApply(f, v) = f(v)\nStep(n, acc) = n + 1, acc + n, n < 3\nColl(Box.K, ([1, 2][5])*)"),
        Special("huntGenFaultsAF0001", "Bad = 1 / 0\nInc(x) = x + 1\nId(v) = v\nTwo(a, b) = a * 10 + b\nBox = { public K = 5 }\nUse(a, b) = a + b\nFst(a, b) = a\nSnd(a, b) = b\nColl(*xs) = xs\nApply(f, v) = f(v)\nStep(n, acc) = n + 1, acc + n, n < 3\n'a' * 2 < 1 / 0 < 2"),
        Special("huntGenFaultsAF0002", "Bad = 1 / 0\nInc(x) = x + 1\nId(v) = v\nTwo(a, b) = a * 10 + b\nBox = { public K = 5 }\nUse(a, b) = a + b\nFst(a, b) = a\nSnd(a, b) = b\nColl(*xs) = xs\nApply(f, v) = f(v)\nStep(n, acc) = n + 1, acc + n, n < 3\nUse(Bad, Box.K)"),
        Special("huntGenFaultsAF0003", "Bad = 1 / 0\nInc(x) = x + 1\nId(v) = v\nTwo(a, b) = a * 10 + b\nBox = { public K = 5 }\nUse(a, b) = a + b\nFst(a, b) = a\nSnd(a, b) = b\nColl(*xs) = xs\nApply(f, v) = f(v)\nStep(n, acc) = n + 1, acc + n, n < 3\nUse('a' * 2, (1 + true))"),
        Special("huntGenFaultsAF0004", "Bad = 1 / 0\nInc(x) = x + 1\nId(v) = v\nTwo(a, b) = a * 10 + b\nBox = { public K = 5 }\nUse(a, b) = a + b\nFst(a, b) = a\nSnd(a, b) = b\nColl(*xs) = xs\nApply(f, v) = f(v)\nStep(n, acc) = n + 1, acc + n, n < 3\nreduce([1, 2], { a + b * 0 + 'a' * 2 }, Box.Nope)"),
        Special("huntGenFaultsAF0005", "Bad = 1 / 0\nInc(x) = x + 1\nId(v) = v\nTwo(a, b) = a * 10 + b\nBox = { public K = 5 }\nUse(a, b) = a + b\nFst(a, b) = a\nSnd(a, b) = b\nColl(*xs) = xs\nApply(f, v) = f(v)\nStep(n, acc) = n + 1, acc + n, n < 3\n[tick(), 20][[1, 2][5], first(())]"),
        Special("huntGenFaultsAF0006", "Bad = 1 / 0\nInc(x) = x + 1\nId(v) = v\nTwo(a, b) = a * 10 + b\nBox = { public K = 5 }\nUse(a, b) = a + b\nFst(a, b) = a\nSnd(a, b) = b\nColl(*xs) = xs\nApply(f, v) = f(v)\nStep(n, acc) = n + 1, acc + n, n < 3\nTwo(if(3, 1, 2))"),
        Special("huntGenFaultsAF0007", "Bad = 1 / 0\nInc(x) = x + 1\nId(v) = v\nTwo(a, b) = a * 10 + b\nBox = { public K = 5 }\nUse(a, b) = a + b\nFst(a, b) = a\nSnd(a, b) = b\nColl(*xs) = xs\nApply(f, v) = f(v)\nStep(n, acc) = n + 1, acc + n, n < 3\nUse(Two(1), 2)"),
        Special("huntGenFaultsAF0008", "Bad = 1 / 0\nInc(x) = x + 1\nId(v) = v\nTwo(a, b) = a * 10 + b\nBox = { public K = 5 }\nUse(a, b) = a + b\nFst(a, b) = a\nSnd(a, b) = b\nColl(*xs) = xs\nApply(f, v) = f(v)\nStep(n, acc) = n + 1, acc + n, n < 3\nTwo(1, 2) < 0 < 'a' * 2 < Two(1)"),
        Special("huntGenFaultsAF0009", "Bad = 1 / 0\nInc(x) = x + 1\nId(v) = v\nTwo(a, b) = a * 10 + b\nBox = { public K = 5 }\nUse(a, b) = a + b\nFst(a, b) = a\nSnd(a, b) = b\nColl(*xs) = xs\nApply(f, v) = f(v)\nStep(n, acc) = n + 1, acc + n, n < 3\n'a' * 2.Inc + Id(1, 2)"),
        Special("huntGenFaultsAF0010", "Bad = 1 / 0\nInc(x) = x + 1\nId(v) = v\nTwo(a, b) = a * 10 + b\nBox = { public K = 5 }\nUse(a, b) = a + b\nFst(a, b) = a\nSnd(a, b) = b\nColl(*xs) = xs\nApply(f, v) = f(v)\nStep(n, acc) = n + 1, acc + n, n < 3\nmap([1, 2], { x * 0 + Box.Nope }) + Id(4)"),
        Special("huntGenFaultsAF0011", "Bad = 1 / 0\nInc(x) = x + 1\nId(v) = v\nTwo(a, b) = a * 10 + b\nBox = { public K = 5 }\nUse(a, b) = a + b\nFst(a, b) = a\nSnd(a, b) = b\nColl(*xs) = xs\nApply(f, v) = f(v)\nStep(n, acc) = n + 1, acc + n, n < 3\nFst(min([]), Inc)"),
        Special("huntGenFaultsAF0012", "Bad = 1 / 0\nInc(x) = x + 1\nId(v) = v\nTwo(a, b) = a * 10 + b\nBox = { public K = 5 }\nUse(a, b) = a + b\nFst(a, b) = a\nSnd(a, b) = b\nColl(*xs) = xs\nApply(f, v) = f(v)\nStep(n, acc) = n + 1, acc + n, n < 3\nmap([1, 2], { x * 0 + if(3, 1, 2) }) + Two(1, 2)"),
        Special("huntGenFaultsAF0013", "Bad = 1 / 0\nInc(x) = x + 1\nId(v) = v\nTwo(a, b) = a * 10 + b\nBox = { public K = 5 }\nUse(a, b) = a + b\nFst(a, b) = a\nSnd(a, b) = b\nColl(*xs) = xs\nApply(f, v) = f(v)\nStep(n, acc) = n + 1, acc + n, n < 3\nStep(Box.K, 1 / 0).while"),
        Special("huntGenFaultsAF0014", "Bad = 1 / 0\nInc(x) = x + 1\nId(v) = v\nTwo(a, b) = a * 10 + b\nBox = { public K = 5 }\nUse(a, b) = a + b\nFst(a, b) = a\nSnd(a, b) = b\nColl(*xs) = xs\nApply(f, v) = f(v)\nStep(n, acc) = n + 1, acc + n, n < 3\nStep(min([]), Box.Nope).while"),
        Special("huntGenFaultsAF0015", "Bad = 1 / 0\nInc(x) = x + 1\nId(v) = v\nTwo(a, b) = a * 10 + b\nBox = { public K = 5 }\nUse(a, b) = a + b\nFst(a, b) = a\nSnd(a, b) = b\nColl(*xs) = xs\nApply(f, v) = f(v)\nStep(n, acc) = n + 1, acc + n, n < 3\nId(1, 2).Inc + (1 + true)"),
        Special("huntGenFaultsAF0016", "Bad = 1 / 0\nInc(x) = x + 1\nId(v) = v\nTwo(a, b) = a * 10 + b\nBox = { public K = 5 }\nUse(a, b) = a + b\nFst(a, b) = a\nSnd(a, b) = b\nColl(*xs) = xs\nApply(f, v) = f(v)\nStep(n, acc) = n + 1, acc + n, n < 3\nTwo(0 ^ -1, Id(4), tick())"),
        Special("huntGenFaultsAF0017", "Bad = 1 / 0\nInc(x) = x + 1\nId(v) = v\nTwo(a, b) = a * 10 + b\nBox = { public K = 5 }\nUse(a, b) = a + b\nFst(a, b) = a\nSnd(a, b) = b\nColl(*xs) = xs\nApply(f, v) = f(v)\nStep(n, acc) = n + 1, acc + n, n < 3\nId(1, 2) + first(())"),
        Special("huntGenFaultsAF0018", "Bad = 1 / 0\nInc(x) = x + 1\nId(v) = v\nTwo(a, b) = a * 10 + b\nBox = { public K = 5 }\nUse(a, b) = a + b\nFst(a, b) = a\nSnd(a, b) = b\nColl(*xs) = xs\nApply(f, v) = f(v)\nStep(n, acc) = n + 1, acc + n, n < 3\nUse(Id(1, 2), 2)"),
        Special("huntGenFaultsAF0019", "Bad = 1 / 0\nInc(x) = x + 1\nId(v) = v\nTwo(a, b) = a * 10 + b\nBox = { public K = 5 }\nUse(a, b) = a + b\nFst(a, b) = a\nSnd(a, b) = b\nColl(*xs) = xs\nApply(f, v) = f(v)\nStep(n, acc) = n + 1, acc + n, n < 3\nColl(Two(1), Inc(3)).count"),
        Special("huntGenInferAI0000Base", "D0 = s - s + q + s\nD1 = D0\nD1(1, 10), D0(1, 10)"),
        Special("huntGenInferAI0001Base", "D0 = w + q - q\nD1 = if(1 > 0, D0 - w + v + s, 0)\nD2 = [r + D1, 0][0]\nD3 = if(1 > 0, D0 + q + D2 - ~u, 0)\nD4 = D3 + q~\nD0(1, 10), D3(1, 10, 100, 1000, 10000, 100000)"),
        Special("huntGenInferAI0002Base", "D0 = z - u - r\nD1 = D0\nD2 = D0\nD0(1, 10, 100), D1(1, 10, 100)"),
        Special("huntGenInferAI0003Base", "D0(p, q) = [q + p + q, 0][0]\nD1 = D0 + D0 - D0 + D0\nD2 = D1 - 1\nD3 = D1\nD2(1, 10), D1(1, 10)"),
        Special("huntGenInferAI0004Base", "D0 = [v - 4, 0][0]\nD1 = q + D0 - s + D0\nD2 = D0 + 4\nD3(s, q, v) = if(1 > 0, D1 + D1 - 9, 0)\nD4 = D0\nD5 = if(1 > 0, D4 + D4 + u, 0)\nD5(1, 10), D2(1)"),
        Special("huntGenInferAI0005Base", "D0 = r - q + p - s\nD1 = D0\nD2(v, q, p) = [p + v + q, 0][0]\nD3 = q - q~ + v - r\nD4(p, v, r, s, q) = D0 - p + s - D3\nD0(1, 10, 100, 1000), D1(1, 10, 100, 1000)"),
        Special("huntGenInferAI0006Base", "D0 = if(1 > 0, v + q + ~s, 0)\nD1(q, w) = if(1 > 0, q + 2 - w, 0)\nD2 = if(1 > 0, u - p + ~p, 0)\nD1(1, 10), D0(1, 10, 100)"),
        Special("huntGenInferAI0007Base", "D0 = v + s - q~ + q\nD1 = D0\nD2 = [D1 + D0, 0][0]\nD3 = 3 + ~r - 5\nD4 = p - 7 + s - s\nD5 = D2\nD0(1, 10, 100), D3(1)"),
        Special("huntGenInferAI0008Base", "D0 = s + q - 5 + 6\nD1 = v + D0\nD1(1, 10, 100), D0(1, 10)"),
        Special("huntGenInferAI0009Base", "D0 = [s - q - r + r~, 0][0]\nD1(q, s, r) = D0 + D0\nD2 = r + D0 + u\nD3 = if(1 > 0, D2 - D1 - D2, 0)\nD4 = D0 + p + u + s\nD5 = D0\nD4(1, 10, 100, 1000, 10000), D3(1, 10, 100, 1000)"),
        Special("huntGenInferAI0010Base", "D0 = w + p + r + p\nD1 = D0 + q + 5\nD2(p, w, q, v, r) = if(1 > 0, v - 7 - D1 + D0, 0)\nD3(r) = 3 + r\nD4(q, u, r) = if(1 > 0, u + q - r + q, 0)\nD0(1, 10, 100), D4(1, 10, 100)"),
        Special("huntGenInferAI0011Base", "D0 = w - 6\nD1 = D0\nD2 = [~q + p + D1, 0][0]\nD1(1), D2(1, 10, 100)"),
        Special("huntGenInferAI0012Base", "D0(r) = r - 1\nD1 = if(1 > 0, D0 + D0 + D0, 0)\nD0(1), D1(1)"),
        Special("huntGenInferAI0013Base", "D0 = if(1 > 0, u + q, 0)\nD1 = if(1 > 0, 9 - ~z, 0)\nD2 = D0\nD2(1, 10), D0(1, 10)"),
        Special("huntGenInferAI0014Base", "D0 = [~p - s, 0][0]\nD1 = if(1 > 0, D0 + q~ - D0 + D0, 0)\nD2 = r + s + u\nD3(v, u, p, q) = u - q - v + p\nD1(1, 10, 100), D0(1, 10)"),
        Special("huntGenInferAI0015Base", "D0 = w + q + 2 + p~\nD1 = D0\nD2 = D1 + D1 - q + 8\nD3 = s - D2 + ~s + D1\nD2(1, 10, 100), D3(1, 10, 100, 1000)"),
        Special("huntGenInferAI0016Base", "D0(u, p) = [p - u, 0][0]\nD1 = if(1 > 0, D0 - D0 + 3 + D0, 0)\nD2 = u + s - p\nD1(1, 10), D2(1, 10, 100)"),
        Special("huntGenInferAI0017Base", "D0 = if(1 > 0, 8 + r - v, 0)\nD1 = if(1 > 0, p - D0 + D0 + D0, 0)\nD2 = [q + 5 - D1, 0][0]\nD1(1, 10, 100), D0(1, 10)"),
        Special("huntGenInferAI0018Base", "D0 = [p - 8, 0][0]\nD1(p, q, u) = [q + u + p + D0, 0][0]\nD2 = if(1 > 0, s + p + 7 - D1, 0)\nD3 = p + D2\nD4 = if(1 > 0, D3 - 6 - ~r, 0)\nD2(1, 10, 100, 1000), D0(1)"),
        Special("huntGenInferAI0019Base", "D0 = v + r + p - p\nD1 = 1 + q\nD2(q, u) = u + u + q\nD3 = if(1 > 0, 1 + D1, 0)\nD2(1, 10), D1(1)"),
        Special("huntGenEqAQ0000", "Same(x, x) = 1\nP0 = 'a'\nP1 = (P0, P0, -1)\nP2 = [P1, P0, true]\nP3 = ([], 'a', P0)\nP4 = (P3, P3, P2)\nP5 = (P0, P3, false)\nP6 = P1\nP1 == P0, P5 == P2, [P0, P0] != [P0, P0], [P1, P1] != [P1, P1], P3 == P3"),
        Special("huntGenEqAQ0001", "Same(x, x) = 1\nP0 = [1, true, 'a']\nP1 = P0\nP2 = ('b', 2, P1, 'a')\nP3 = -1\n[P3, P2] != [P2, P3], Same(P2, P3)"),
        Special("huntGenEqAQ0002", "Same(x, x) = 1\nP0 = (-1, 0, -1, 1)\nP1 = (true, false)\nP2 = [P0, 0, true]\nP3 = P1\nP4 = (true, P2)\nP2 == P3, P0 == P0"),
        Special("huntGenEqAQ0003", "Same(x, x) = 1\nP0 = [false, []]\nP1 = (P0, -1, true)\nP2 = (P0, P0, P0)\nP3 = P1\nP4 = P0\nP5 = ((), P2, 'a')\nP6 = [P0, P1, P1]\nP7 = (P3, P0, false, P1)\n[P6, P4] != [P4, P6], P4 == P5"),
        Special("huntGenEqAQ0004", "Same(x, x) = 1\nP0 = (1, 2, ())\nP1 = (P0, 2, P0)\nP2 = (P1, [], P0)\nP3 = P0\nP4 = [1]\n[P4, P3] != [P3, P4], P2 == P4, P3 == P2, contains([P3, P3, P1, P2], P0)"),
        Special("huntGenEqAQ0005", "Same(x, x) = 1\nP0 = [-1, false, true, []]\nP1 = 1\nP2 = P1\nP3 = 'b'\nP4 = [P0, P1]\nP3 == P4, distinct([P2, P3]).count"),
        Special("huntGenEqAQ0006", "Same(x, x) = 1\nP0 = (2, 'b', 'b')\nP1 = [P0, P0]\nP2 = [P0]\nP3 = (P2, 'b', [], P1)\nP4 = [P1, P3, 2, P1]\n[P1, P2] != [P2, P1], P4 == P1"),
        Special("huntGenEqAQ0007", "Same(x, x) = 1\nP0 = ('a', 1, 0, -1)\nP1 = [-1, P0]\nP2 = [P0, P0, true, 'b']\nP3 = [2, P2]\nP4 = [P3]\nP5 = [P2, 0]\nP6 = [P2]\nP7 = (P4, false, P5)\nP8 = P6\nP3 == P8, P4 == P0, [P7, P0] != [P0, P7]"),
        Special("huntGenEqAQ0008", "Same(x, x) = 1\nP0 = ('a', -1, 1)\nP1 = false\nP2 = (false, P0, 1, P1)\nP3 = (P1, P1, P2, P1)\nP4 = P1\nP5 = (1, 'a', P2, P3)\nSame(P4, P1), P3 == P1, distinct([P1, P4, P0]).count"),
        Special("huntGenEqAQ0009", "Same(x, x) = 1\nP0 = ('b', 'a', (), 2)\nP1 = (P0, P0, P0)\nP2 = (P1, P1, P0, 1)\nP3 = [[]]\nP4 = [P3]\nP5 = [0, P1, false, P0]\nP6 = (-1, true)\nP7 = []\nP8 = []\n[P2, P0] != [P0, P2], P5 == P1, contains([P1, P4, P5], P2), Same(P2, P5), contains([P8], P0)"),
        Special("huntGenEqAQ0010", "Same(x, x) = 1\nP0 = ((), 'a', 'b')\nP1 = ['b', P0, P0, P0]\nP2 = [P1]\nP3 = P0\nP4 = P0\nP5 = [1, P2, P3, P1]\nP6 = 1\n[P0, P3] != [P3, P0], [P6, P4] != [P4, P6], P6 == P5, P4 == P3, distinct([P3, P5]).count"),
        Special("huntGenEqAQ0011", "Same(x, x) = 1\nP0 = 1\nP1 = P0\nP2 = [P0, P0]\nP3 = [()]\nP4 = [P2, P3, 1]\nP5 = [P3, P1, 2]\ndistinct([P2, P0, P0, P5, P5]).count, contains([P1, P4, P5, P3, P5], P5), [P5, P3] != [P3, P5], P0 == P4"),
        Special("huntGenEqAQ0012", "Same(x, x) = 1\nP0 = 'b'\nP1 = P0\nP2 = [P1]\nP1 == P2, distinct([P1, P0, P1, P2, P0]).count, Same(P2, P0), contains([P2, P0, P0, P0], P0)"),
        Special("huntGenEqAQ0013", "Same(x, x) = 1\nP0 = (true, false)\nP1 = (P0, P0, P0, [])\nP2 = P0\nP3 = P2\nP4 = [P0, P1, false]\ncontains([P4, P1, P4], P3), distinct([P4, P2, P4, P0]).count, P3 == P1, [P0, P0] != [P0, P0], P0 == P1"),
        Special("huntGenEqAQ0014", "Same(x, x) = 1\nP0 = [false]\nP1 = P0\nP2 = (P0, 'b')\nP3 = ['a', P0]\nP4 = ('a', -1, P3, 'a')\nP5 = (false, 'a')\nP6 = (P3, P4, ())\n[P6, P1] != [P1, P6], P1 == P1, P5 == P2, P5 == P0"),
        Special("huntGenExpoAX0000Pair", "F(y) = {\n  K1(0) = map([1, 2], { x * 4 })[1]\n  K1(m) = m + 8 * 2\n  H2(z) = z + 1 * [3, 9][0]\n  P3 = y + y\n  H4(z) = z + P3\n  P5 = H2(P3 * y) + 0\n  P3 + P5 + P5\n}\nF(1), F(2)"),
        Special("huntGenExpoAX0001Pair", "F(y) = {\n  P1 = y + [y, y][0] + 0\n  P2 = y + map([1, 2], { x * 7 })[1]\n  a3, b4 = P1 * 5, if(y > 4, [P1, y][0], y)\n  H5(z) = z + P2 - { public Q = y }.Q\n  P6 = 7 + [4, y][1] + 0\n  P7 = y * y\n  P2\n}\nF(1), F(2)"),
        Special("huntGenExpoAX0002Pair", "F(y) = {\n  N1 = {\n    public V = if(7 > 4, y + 4, y)\n    public W = V * 2\n  }\n  C2 = { y }\n  N1.W + N1.V + C2\n}\nF(1), F(2)"),
        Special("huntGenExpoAX0003Pair", "F(y) = {\n  P1 = [y, y][0]\n  N2 = {\n    public V = P1 * { public Q = y }.Q\n    public W = V * 2\n  }\n  a3, b4 = map([1, 2], { x * N2.V })[1], y + { public Q = P1 }.Q\n  P5 = [y, b4][1] + 0\n  A6 = a3\n  P7 = y - { public Q = b4 }.Q + 0\n  N2.V + b4 + a3\n}\nF(1), F(2)"),
        Special("huntGenExpoAX0004Pair", "F(y) = {\n  P1 = y - map([1, 2], { x * y })[1] + 0\n  P2 = y * P1\n  C3 = { P1 }\n  P2 + C3\n}\nF(1), F(2)"),
        Special("huntGenExpoAX0005Pair", "F(y) = {\n  N1 = {\n    public V = 1 - if(1 > 4, y, 8)\n    public W = V * 2\n  }\n  P2 = 2\n  P3 = map([1, 2], { x * P2 })[1]\n  P4 = P2 - N1.V - N1.V\n  H5(z) = z + P3\n  N6 = {\n    public V = N1.V + P3 * 8\n    public W = V * 2\n  }\n  P3 + N6.W\n}\nF(1), F(2)"),
        Special("huntGenExpoAX0006Pair", "F(y) = {\n  open B4\n  K1(0) = 2 - y * y\n  K1(m) = m + 8\n  P2 = 3 * y + 0\n  P3 = if(P2 > 4, map([1, 2], { x * P2 })[1], 5)\n  B4 = {\n    public Q = [P2, P3][0]\n    public R = Q + y\n  }\n  H5(z) = z + B4.Q + B4.Q + B4.R\n  B4.Q + R + Q\n}\nF(1), F(2)"),
        Special("huntGenExpoAX0007Pair", "F(y) = {\n  P1 = 1\n  P2 = P1 + 0\n  P1 + P1 + P2\n}\nF(1), F(2)"),
        Special("huntGenExpoAX0008Pair", "F(y) = {\n  P1 = 1 * 9 * 6 + 0\n  P2 = y - y\n  P2\n}\nF(1), F(2)"),
        Special("huntGenExpoAX0009Pair", "F(y) = {\n  P1 = y - { public Q = 9 }.Q\n  K2(0) = P1\n  K2(m) = m + [P1, y][1]\n  P1\n}\nF(1), F(2)"),
        Special("huntGenExpo2AY0000Pair", "Step(n) = n + 1\nF(y) = {\n  FK1(0) = { public Q = y - y }.Q\n  FK1(m) = m + Step(y).repeat(2)\n  FK2(0) = FK1(Step(6).repeat(2))\n  FK2(m) = m + if(y > 4, Step(y).repeat(2), 5)\n  FP3 = 5 + if(8 > 4, 4, y) + 0\n  FB4 = {\n    public Q = y * FP3 - FP3\n    public R = Q + FP3\n  }\n  G(z) = {\n    GH1(w) = w + map([1, 2], { x * FB4.R })[1]\n    GP2 = if(FB4.R > 4, y + FB4.R, FB4.R) + 0\n    FB4.R + FB4.R + FB4.Q\n  }\n  G(1), G(3)\n}\nF(1), F(2)"),
        Special("huntGenExpo2AY0001Pair", "Step(n) = n + 1\nF(y) = {\n  FP1 = if(y > 4, Step(7).repeat(2), 8)\n  FP2 = y * y\n  FA3 = FP1\n  FP4 = [y, FP1][1]\n  G(z) = {\n    GA1 = FP1\n    GK2(0) = Step(z).repeat(2)\n    GK2(m) = m + z - [z, z][0]\n    GP3 = z\n    Ga4, Gb5 = z, y - { public Q = FA3 }.Q\n    FP1\n  }\n  G(1), G(3)\n}\nF(1), F(2)"),
        Special("huntGenExpo2AY0002Pair", "Step(n) = n + 1\nF(y) = {\n  FK1(0) = map([1, 2], { x * y })[1]\n  FK1(m) = m + [8, y][1]\n  FK2(0) = y - 2 - 7\n  FK2(m) = m + [9, 4][0]\n  G(z) = {\n    GP1 = if(y > 4, Step(y).repeat(2), 2)\n    GP2 = 9 + GP1\n    GP2\n  }\n  G(1), G(3)\n}\nF(1), F(2)"),
        Special("huntGenExpo2AY0003Pair", "Step(n) = n + 1\nF(y) = {\n  FP1 = Step(6).repeat(2) + 0\n  FK2(0) = Step(FP1).repeat(2)\n  FK2(m) = m + y + y + FP1\n  G(z) = {\n    GA1 = FP1\n    GC2 = { FP1 }\n    GP3 = FK2(FK2(FP1)) + 0\n    GP4 = 5 - map([1, 2], { x * 5 })[1] + 0\n    GP4 + GP3 + GP3\n  }\n  G(1), G(3)\n}\nF(1), F(2)"),
        Special("huntGenExpo2AY0004Pair", "Step(n) = n + 1\nF(y) = {\n  FH1(w) = w + map([1, 2], { x * y })[1]\n  FP2 = y - 6 + 0\n  FP3 = if(y > 4, FH1(FP2), y)\n  FK4(0) = FH1(FP2 * FP3)\n  FK4(m) = m + map([1, 2], { x * 1 })[1]\n  G(z) = {\n    GP1 = y * if(FP2 > 4, FP2, z) + 0\n    GP2 = y + map([1, 2], { x * y })[1]\n    GK3(0) = 1 + GP1 * 9\n    GK3(m) = m + if(9 > 4, map([1, 2], { x * y })[1], 9)\n    GP4 = y * Step(GP2).repeat(2) + 0\n    GK5(0) = 9 * GP4 - y\n    GK5(m) = m + z - GP4 - z\n    GP4 + FP2 + GP1\n  }\n  G(1), G(3)\n}\nF(1), F(2)"),
        Special("huntGenExpo2AY0005Pair", "Step(n) = n + 1\nF(y) = {\n  Fa1, Fb2 = 8 - y + y, [y, 7][1]\n  FH3(w) = w + Fb2\n  G(z) = {\n    GC1 = { Fa1 }\n    GP2 = map([1, 2], { x * GC1 })[1]\n    GP3 = z + 0\n    GA4 = Fb2\n    GA5 = GP3\n    GP3 + Fb2 + GP2\n  }\n  G(1), G(3)\n}\nF(1), F(2)"),
        Special("huntGenChaosGZ0000", "Cap(meta r) = r\nD0x, D0y = tick(), 's'.string\nD1 = D0x((D0x)(), count(D0.Invoke()))\nmap(D0y(D1 + 6, D0y.Arguments.count), { x + D0x.Arguments.count }), D1.K"),
        Special("huntGenChaosGZ0001", "Cap(meta r) = r\nD0x, D0y = b~, (b*).Q(7, (a.Arguments.count, 9[]), { public Q = count(6) }.Q)\nD1 = D0().D0y.string\nD2 = {\n  public K0 = { 1 * D0x }\n  public K1 = filter(if(D0 > 4, 2, D0), { x > 3 < 1 <= D0 }).count\n  [D1.Algorithm(-1), Cap(D0y())][0, 1]\n}\nD3 = D1.Arguments.count\nD4(s) = ('s')\nif('s' > D1.Invoke(), D1(D1, count(D4)).while, D3(8, map(D0x, { x + D3 }))), D4.D3 * (D2)(7, D4, 6) < (D0y)() <= count(8 div 3), reduce(-1, D2, map(D1, { x + D0 })).string"),
        Special("huntGenChaosGZ0002", "Cap(meta r) = r\nD0* = c.Invoke()\nD1(meta m) = {\n  count(7.string.string)\n}\nD2x, D2y = ~c, { public Q = D0(Cap(b(b, 8, 9))).repeat(2) }.Q\nD2y * 3 div 1 * (D2x*), D0"),
        Special("huntGenChaosGZ0005", "Cap(meta r) = r\nD0 = {\n  c(['s', 7 * a][0, 1]*)\n}\nD1 = [4, a][0, 1].a.D0.D0\nfirst(reduce(D1.string, D0, first(9)))"),
        Special("huntGenChaosGZ0006", "Cap(meta r) = r\nD0 = { reduce(c(2), b, a().while) }\nD1x, D1y = (D0().while, a~), ~c\nD0"),
        Special("huntGenChaosGZ0010", "Cap(meta r) = r\nD0(meta m) = [(m*), map((m).string, { x + { 0 }.m })][0, 1]\nD1(s, p) = (p)(if(D0.Arguments[2] > p, tick(), 3 * s)).D0(s)\nD0.D1[].D1"),
        Special("huntGenChaosGZ0013", "Cap(meta r) = r\nD0 = a.Algorithm(a*)\nD1* = D0[~a][D0.Invoke()] < D0 <= filter((a*) < a.Algorithm <= tick(), { x > D0.Algorithm(a.Algorithm, c(a, 8, a).repeat(2)) }).count\nD2(q, s) = q.Algorithm\nD2.K.D0(Cap(D2(count(5), D2().while))), (D2)(D0.Arguments[2] div 2, D2(map(0, { x + D2 })).repeat(2)), []"),
        Special("huntGenChaosGZ0015", "Cap(meta r) = r\nD0((p, q)) = {\n  { a(2.Q(7)*) }\n}\nD1(p)* = tick()\nD2(q) = first(Cap(D1(tick(), D0.Algorithm, D0.string)))\nD3(*r) = first((D2*, reduce(D0(D1*), D1, map(D0, { x + D1 }))))\n1.string, filter(map(D1*, { x + (D0)(D2, D1) }), { x > D1.Algorithm }).count"),
        Special("huntGenChaosGZ0017", "Cap(meta r) = r\nD0(s) = s\nD1 = {\n  if(6 > D0, D0*, ({ public Q = 7 }.Q))\n}\nD2((p, q)) = q\nD3x, D3y = count(D1 + 9) < reduce([0], D2, u~) <= 3, D0\nD4 = 's' div 3 * count(a*)[D3(1*).D1]\n(D2)([D1(), (D2, D2)][0, 1]), (Cap(D0([D2, 7][0, 1])))"),
        Special("huntGenChaosGZ0020", "Cap(meta r) = r\nD0 = {\n  public K0 = a()\n  public K1 = [[9], 0.Arguments.count][0, 1]\n  public K2 = a.string\n  tick()\n}\nD1 = {\n  open D0\n  D0*\n}\nD2 = D1.Q\nnot (D1(D0) == { D2.string }), reduce(7, D0, (D1)())"),
        Special("huntA1Expo1E01Direct", "F(y) = {\n  A = y * 10\n  A + 0\n}\nF(1), F(2), map([3, 4], F)"),
        Special("huntA1Expo1E02Member", "F(y) = {\n  B = { public Q = y * 10 }\n  B.Q + 0\n}\nF(1), F(2), map([3, 4], F)"),
        Special("huntA1Expo1E05Alias", "F(y) = {\n  B = y * 10\n  A = B\n  R = A + 0\n  R\n}\nF(1), F(2), map([3, 4], F)"),
        Special("huntA1Expo1E07RuntimeAliasParam", "F(y) = {\n  A = y\n  R = A * 10\n  R\n}\nF(1), F(2), map([3, 4], F)"),
        Special("huntA1Expo1E09DeconBoth", "F(y) = {\n  a, b = y * 10, y\n  a + b\n}\nF(1), F(2), map([3, 4], F)"),
        Special("huntA1Expo1E10ClauseBinder", "F(0) = 0\nF(n) = {\n  A = n * 10\n  A + 0\n}\nF(1), F(2), map([3, 4], F)"),
        Special("huntA2Need1N01UndemandedSecond", "F(x, y) = x\nF(tick(), tick())"),
        Special("huntA2Need1N02DemandOrder", "F(x, y) = y + x\nF(tick(), tick() * 10)"),
        Special("huntA2Need1N03AtMostOnce", "F(x) = x + x + x\nF(tick())"),
        Special("huntA2Need1N04NeverDemanded", "F(x) = 5\nF(1 / 0)"),
        Special("huntA2Need1N05ForwardingNoForce", "G(v) = 7\nF(x) = G(x)\nF(1 / 0)"),
        Special("huntA2Need1N06CardinalityFirst", "F(x, y) = x\nF(1 / 0)"),
        Special("huntA2Need2T01MemberPathTransport", "Coll(*ys) = ys.count\nF(*xs) = {\n  B = { public P = xs }\n  Coll(B.P*)\n}\nF(1 / 0, 2)"),
        Special("huntA2Need2T02AliasChainTransport", "Coll(*ys) = ys.count\nF(*xs) = {\n  A = xs\n  B = A\n  C = B\n  Coll(C*)\n}\nF(1 / 0, 2, 3)"),
        Special("huntA2Need2T03ParamHoldingReference", "Coll(*ys) = ys.count\nPass(v) = Coll(v*)\nF(*xs) = {\n  A = xs\n  Pass(A)\n}\nF(1 / 0)"),
        Special("huntA2Need2T04CountThroughAlias", "F(*xs) = {\n  A = xs\n  A.count\n}\nF(1 / 0, 1 / 0)"),
        Special("huntA2Need2T05FirstThroughAlias", "F(*xs) = {\n  A = xs\n  first(A)\n}\nF(7, 1 / 0)"),
        Special("huntA2Need2T06SelectThroughMember", "F(*xs) = {\n  B = { public P = xs }\n  B.P[1]\n}\nF(1 / 0, 8)"),
        Special("huntA3Cache1C01ReentrantQ37", "A = if(tick() < 3, A + 1, 0)\nA, A"),
        Special("huntA3Cache1C02CollectingAliasOnce", "Only(*xs) = tick()\nA = Only\nA, Only, A"),
        Special("huntA3Cache1C03AliasRead", "P = tick()\nA = P\nA, P, A"),
        Special("huntA3Cache1C04AliasCallEstablishes", "P = tick()\nA = P\nA(), P"),
        Special("huntA3Cache1C06CarrierCalls", "P = tick()\nB = { P }\nB(), B(), P()"),
        Special("huntA3Cache1C07RuntimeMemberValueOnly", "G(o) = tick()\nUse(b) = {\n  A = b.G\n  A(), A, A(), A\n}\nUse(5)"),
        Special("huntA3Cache2C203FormulaOwnerReadFirst", "F(y) = {\n  O = {\n    public V = y * 0 + tick()\n    V + 0\n  }\n  O, O.V, O()\n}\nF(1)"),
        Special("huntA3Cache2C204ExportedOwner", "O = {\n  public V = tick()\n  V + 0\n}\nO(), O, O.V"),
        Special("huntA3Cache2C205CallbackMemberRead", "F(y) = {\n  O = {\n    public V = y * 0 + tick()\n    V + 0\n  }\n  map([1, 2], { x * 0 + O.V }), O.V\n}\nF(1)"),
        Special("huntA3Cache2C206AliasCellExported", "Cap(meta r) = r\nMul(t) = t * 10\nPick(t) = Cap(Mul(t))\nF(k) = {\n  A = Pick(tick()).Algorithm\n  A(k)\n}\nF(1), F(2), F(1), tick()"),
        Special("huntA3Cache2C207AliasCellLocal", "Cap(meta r) = r\nMul(t) = t * 10\nPick(t) = Cap(Mul(t))\nF(k) = {\n  A = Pick(tick() + k * 0).Algorithm\n  A(k)\n}\nF(1), F(2), F(1), tick()"),
        Special("huntA3Cache2C208AliasCellInLoopStep", "Cap(meta r) = r\nMul(t) = t * 10\nStep(n, acc) = {\n  A = Cap(Mul(tick())).Algorithm\n  n + 1, acc + A(n), n < 3\n}\nStep(0, 0).while, tick()"),
        Special("huntA3Cache3C301tPropertyTwinExported", "Cap(meta r) = r\nMul(t) = t * 10\nPick(t) = if(t > 0, Cap(Mul(t)), Cap(Mul(0)))\nF(k) = {\n  P = Pick(tick())\n  P.Algorithm(k)\n}\nF(1), F(2), F(1), tick()"),
        Special("huntA3Cache3C302tPropertyTwinLocal", "Cap(meta r) = r\nMul(t) = t * 10\nPick(t) = if(t > 0, Cap(Mul(t)), Cap(Mul(0)))\nF(k) = {\n  P = Pick(tick() + k * 0)\n  P.Algorithm(k)\n}\nF(1), F(2), F(1), tick()"),
        Special("huntA3Cache3C303AliasCellLoop", "Cap(meta r) = r\nMul(t) = t * 10\nPick(t) = if(t > 0, Cap(Mul(t)), Cap(Mul(0)))\nStep(n, acc) = {\n  A = Pick(tick()).Algorithm\n  n + 1, acc + A(n), n < 3\n}\nStep(0, 0).while, tick()"),
        Special("huntA3Cache3C303tPropertyTwinLoop", "Cap(meta r) = r\nMul(t) = t * 10\nPick(t) = if(t > 0, Cap(Mul(t)), Cap(Mul(0)))\nStep(n, acc) = {\n  P = Pick(tick())\n  n + 1, acc + P.Algorithm(n), n < 3\n}\nStep(0, 0).while, tick()"),
        Special("huntA3Cache3C304tPropertyTwinLocalLoop", "Cap(meta r) = r\nMul(t) = t * 10\nPick(t) = if(t > 0, Cap(Mul(t)), Cap(Mul(0)))\nStep(n, acc) = {\n  P = Pick(tick() + n * 0)\n  n + 1, acc + P.Algorithm(n), n < 3\n}\nStep(0, 0).while, tick()"),
        Special("huntA3Cache3C305AliasCellReadAndCall", "Cap(meta r) = r\nK(t) = t\nPick(t) = if(t > 0, Cap(K(t)), Cap(K(0)))\nF(k) = {\n  A = Pick(tick() + k * 0).Algorithm\n  A(k), A(k + 1)\n}\nF(5), F(6), tick()"),
        Special("huntA4Loops1L01WhileBasic", "Step(n, acc) = n - 1, acc + n, n > 1\nStep(5, 0).while"),
        Special("huntA4Loops1L08FamilyStep", "Coll(0, acc) = 0, acc\nColl(n, acc) = n - 1, acc + n\nColl(4, 0).repeat(3)"),
        Special("huntA4Loops1L10AliasStep", "Inc(x) = x + 1\nA = Inc\nA(5).repeat(3)"),
        Special("huntA4Loops1L13LoopOneValue", "F(x, y) = x + 1, y\nR = F(0, 5).repeat(2)\nR, count(R)"),
        Special("huntA4Loops1L14ForwardStep", "W(step) = while(step)\nStep(n) = n + 1, n < 3\nW(Step(0))"),
        Special("huntA4Loops1L16QualifiedStep", "Box = { public S(n) = n + 1, n < 3 }\nBox.S(0).while"),
        Special("huntA5Select1S03StringCount", "count('abc')"),
        Special("huntA5Select1S04EmptyStringSelect", "''[0]"),
        Special("huntA5Select1S05StringOnePosition", "'abc'[1]"),
        Special("huntA5Select1S06ScalarSelf", "5[0]"),
        Special("huntA5Select1S07ScalarOut", "5[1]"),
        Special("huntA6Spread1P01CollTable", "Coll(*xs) = xs\nColl(()), Coll((1, 2)), Coll((1, 2)*), (1, 2).Coll, Coll(), Coll([1, 2]), Coll([1, 2]*), Coll([(1, 2)]*), Coll([()]*), Coll((), 3)"),
        Special("huntA6Spread1P02Cnt", "Cnt(*xs) = xs.count\nCnt((10, 7)), Cnt((10, 7)*)"),
        Special("huntA6Spread1P03CntValue", "CntValue(x) = x.count\nCntValue((10, 7))"),
        Special("huntA6Spread1P04Withhead", "WithHead(x, *rest) = rest\nF(*xs, z) = xs\nWithHead(0, (1, 2)), F((1, 2), 3)"),
        Special("huntA6Spread1P05IdPair", "Id(v) = v\nId((1, 2))"),
        Special("huntA6Spread1P06AddPair", "Add(a, b) = a + b\nAdd((1, 2))"),
        Special("huntA7Dot1D01ChainFallback", "A(x) = x * 10\nB(x) = x + 1\n3.A.B"),
        Special("huntA7Dot1D02DeclaredString", "Box = { public string = 7 }\nBox.string"),
        Special("huntA7Dot1D03LexicalStringIgnored", "string(x) = 99\n3.string, string(3)"),
        Special("huntA7Dot1D04BranchMember", "F(0) = {\n  public X = 1\n  X\n}\nF(n) = n\nF.X"),
        Special("huntA7Dot1D05PrivateStructural", "Box = {\n  X = 5\n  public Y = 6\n}\nBox.X"),
        Special("huntA7Dot1D06SpreadReceiver", "F(a, b, c) = a * 100 + b * 10 + c\nR = 1, 2\nR*.F(3)"),
        Special("huntA7Anchor1H01StatedCarriedContainer", "F(b, y) = {\n  p = {\n    Q = y\n    1\n  }\n  G(g, y) = g.Q\n  G(b, 99)\n}\nF(F.p, 5)"),
        Special("huntA7Anchor1H05OpenHeadBetween", "Outer(p) = {\n  Mid = {\n    Lib = { public X = p }\n    Inner = {\n      open Lib\n      X\n    }\n    Inner\n  }\n  Mid\n}\nOuter(1), Outer(2)"),
        Special("huntA7Anchor1H06CarriedViaCallback", "F(b, y) = {\n  p = {\n    Q = y * 10\n    1\n  }\n  map([1, 2], { x * 0 + b.Q })\n}\nF(F.p, 3)"),
        Special("huntA7Anchor1H08CarriedThroughParamChain", "F(b, y) = {\n  p = {\n    Q = y * 10\n    1\n  }\n  G(g) = g.Q\n  G(b)\n}\nF(F.p, 7)"),
        Special("huntA7Anchor1H09ContainerReadAtRoot", "F(b, y) = {\n  p = {\n    Q = y\n    1\n  }\n  b.Q\n}\nF.p.Q"),
        Special("huntA7Anchor1H11ContainerThroughLoopState", "F(b, y) = {\n  p = {\n    Q = y\n    1\n  }\n  S(c, n) = c, n + c.Q, n < 10\n  S(b, 0).while[1]\n}\nF(F.p, 4)"),
        Special("huntA8Alias1X01CarrierForwards", "B = {\n  public F(x) = x * x\n  public Q = 99\n  F\n}\nB(3), B.Q"),
        Special("huntA8Alias1X02CarrierZeroCall", "B = {\n  public F(x) = x * x\n  F\n}\nB()"),
        Special("huntA8Alias1X05TransparentMember", "A = B\nB = {\n  public X = 1\n  7\n}\nA.X, A"),
        Special("huntA8Alias1X06CarrierNotTargetIdentity", "A = 7\nC = { A }\nSame(x, x) = 0\nSame(C, A)"),
        Special("huntA9Meta1M02InvokeFresh", "Cap(meta r) = r\nR = Cap(tick())\nR.Invoke(), R.Invoke()"),
        Special("huntA9Meta1M05ArgumentsSelect", "Cap(meta r) = r\nAdd(a, b) = a + b\nR = Cap(Add(1 / 0, 2))\nR.Arguments[1]"),
        Special("huntA9Meta1M06ArgumentsSelectFail", "Cap(meta r) = r\nAdd(a, b) = a + b\nR = Cap(Add(1 / 0, 2))\nR.Arguments[0]"),
        Special("huntA9Meta1M08ArgumentsEmpty", "Cap(meta r) = r\nAdd(a, b) = a + b\nR = Cap(Add(1 / 0, 2))\nR.Arguments[]"),
        Special("huntA9Meta1M09AlgorithmFresh", "Cap(meta r) = r\nAdd(a, b) = a + b\nR = Cap(Add(1, 2))\nR.Algorithm(10, 20)"),
        Special("huntA9Meta1M10Identity", "Cap(meta r) = r\nF(x) = x\nR = Cap(F(1))\nR2 = Cap(F(1))\nR == R, R == R2"),
        Special("huntA9Meta2M202ArgumentsCycle", "Cap(meta r) = r\nF(x) = x + 1\nR = Cap(F(R.Arguments[0]))\nR.Invoke()"),
        Special("huntA9Meta2M204MultiSelectView", "Cap(meta r) = r\nF(a, b, c) = 0\nR = Cap(F(10, 20, 30))\nR.Arguments[0, 2], R.Arguments[(1, 0)*]"),
        Special("huntA9Meta2M205RebuildCall", "Cap(meta r) = r\nSub(a, b) = a - b\nR = Cap(Sub(tick(), 10))\nR.Algorithm(R.Arguments*), R.Invoke(), R.Arguments[0]"),
        Special("huntA9Meta2M206SameRefs", "Cap(meta r) = r\nF(x) = x\nR = Cap(F(1))\nSame(x, x) = 1\nSame(R, R)"),
        Special("huntA9Meta2M207SameDifferentRefs", "Cap(meta r) = r\nF(x) = x\nR1 = Cap(F(1))\nR2 = Cap(F(1))\nSame(x, x) = 1\nSame(R1, R2)"),
        Special("huntA9Meta2M208ForwardedReference", "Cap(meta r) = r\nF(x) = x * 2\nFw(meta r) = Inner(r)\nInner(q) = q.Invoke()\nFw(F(21))"),
        Special("huntA10Fe1F01CountFormula", "C = count + 0\nC((1, 2, 3))"),
        Special("huntA10Fe1F02IfFormula", "G = if + 0\nG(true, 5, 7), G(false, 5, 7)"),
        Special("huntA10Fe1F03RepeatFormula", "Inc(x) = x + 1\nG = repeat + 0\nG(Inc(1), 2)"),
        Special("huntA10Fe1F05rMutualLiftReordered", "B = A + z\nA = if(tick() > 3, x + y, B + 1)\nA(1, 2, 3)"),
        Special("huntA10Fe1F07WhileRepeatFormula", "S(n) = n + 1, n < 3\nK = while + repeat\nK(S(0), 0)"),
        Special("huntA10Fe1F08BareForwardSameName", "F(p) = p * 2\nA(p) = F\nA(5)"),
        Special("huntA10Spread1W01ArgSlot", "A(x, y)* = x, y\nF(a, b, c) = a * 100 + b * 10 + c\nF(A(1, 2), 3)"),
        Special("huntA10Spread1W01xArgSlotExplicit", "A(x, y) = x, y\nF(a, b, c) = a * 100 + b * 10 + c\nF(A(1, 2)*, 3)"),
        Special("huntA10Spread1W02List", "A(x, y)* = x, y\n[A(1, 2), 3]"),
        Special("huntA10Spread1W03Group", "A(x, y)* = x, y\n(A(1, 2), 3)"),
        Special("huntA10Spread1W04RootRow", "A(x, y)* = x, y\nA(1, 2)"),
        Special("huntA10Spread1W04xRootRowExplicit", "A(x, y) = x, y\nA(1, 2)*"),
        Special("huntA10Fwd1Fw08ForwardCollectorIntoCollector", "Coll(*xs) = xs\nA(*xs) = Coll\nA((1, 2))"),
        Special("huntA10Fwd1Fw15ForwardingChain", "F(x) = x * 2\nG(x) = F\nH(x) = G\nH(4)"),
        Special("huntA10Fwd1Fw18ForwardIf", "G(condition, whenTrue, whenFalse) = if\nG(true, 1, 2), G(false, 1, 2)"),
        Special("huntA10Fwd1Fw19AliasOfMap", "M = map\nM([1, 2], { x * 3 })"),
        Special("huntA10Fwd1Fw20ClosedFormulaBuiltin", "K(collection) = count + 1\nK([1])"),
        Special("huntA11Cmp1K03TotalEquality", "true == 1"),
        Special("huntA11Cmp1K04IfNumber", "if(1, 2, 3)"),
        Special("huntA11Cmp1K05TickOnce", "tick() < tick() < tick()"),
        Special("huntA11Cmp1K06TickEq", "tick() == tick()"),
        Special("huntA12Builtins1B01IfLazy", "if(true, 1, 1 / 0), if(false, 1 / 0, 2)"),
        Special("huntA12Builtins1B02IfCondFail", "if(1 / 0, 1, 2)"),
        Special("huntA12Builtins1B04MapTwoRows", "map([1, 2], { x, x })"),
        Special("huntA12Builtins1B05MapEmptyRow", "map([1, 2], { if(x > 0, (), ()) })"),
        Special("huntA12Builtins1B06FilterNonbool", "filter([1, 2], { x })"),
        Special("huntA12Edge2G01WhileEmptySpreadOnly", "Step(n) = ()*\nStep(0).while"),
        Special("huntA12Edge2G02WhileEmptyRow", "Step(n) = ()\nStep(0).while"),
        Special("huntA12Edge2G03WhileListFlag", "Step(n) = n + 1, [true]\nStep(0).while"),
        Special("huntA12Edge2G04RepeatZeroRowStep", "Step(n) = ()*\nStep(0).repeat(1)"),
        Special("huntA12Edge2G05RepeatEmptyState", "Z(*xs) = xs.count\nZ().repeat(2)"),
        Special("huntA12Edge2G06FamilyBool", "F(true) = 1\nF(false) = 0\nF(1 > 0), F(1 < 0)"),
        Special("huntA12Shadow1Sh01UserFilterCount", "filter(xs, p) = [100, 200, 300]\ncount(x) = 7\n[1, 2, 3].filter({ x > 1 }).count"),
        Special("huntA12Shadow1Sh02UserFilterBuiltinCount", "filter(xs, p) = [100, 200, 300]\n[1, 2, 3].filter({ x > 1 }).count"),
        Special("huntA12Shadow1Sh03BuiltinFilterUserCount", "count(x) = 7\nfilter([1, 2, 3], { x > 1 }).count"),
        Special("huntA12Shadow1Sh04UserCountCallForm", "count(x) = 7\ncount(filter([1, 2, 3], { x > 1 }))"),
        Special("huntA12Shadow1Sh05UserRange", "range(a, b) = [a * 10, b * 10]\nrange(1, 3).filter({ x > 15 }).count"),
        Special("huntA12Shadow1Sh06UserIfInLoop", "if(c, a, b) = a * 1000\nStep(n, acc) = n + 1, acc + if(n > 1, 1, 2), n < 3\nStep(0, 0).while"),
        Special("huntA13Arith1R01DivSigns", "-7 div 2, -7 mod 2, 7 div -2, 7 mod -2, -7 div -2, -7 mod -2"),
        Special("huntA13Arith1R02ExactDiv", "6 / 3, -12 / 4, 0 / 5"),
        Special("huntA13Arith1R03Pow", "2 ^ 10, (-2) ^ 3, -2 ^ 2, 0 ^ 0"),
        Special("huntA13Arith1R04ZeroNegPow", "0 ^ -1"),
        Special("huntA13Arith1R05ModZero", "10 mod 0"),
        Special("huntA13Arith1R06DivZero", "5 div 0"),
        Special("huntA14Open1O01SameProviderTwice", "open M, M\nM = { public X = 1 }\nX"),
        Special("huntA14Open1O02SameProviderGrouped", "open M, (M)\nM = { public X = 1 }\nX"),
        Special("huntA14Open1O03AliasProviderSame", "open Sub, Lib.Sub\nLib = { public Sub = { public X = 2 } }\nSub = Lib.Sub\nX"),
        Special("huntA14Open1O05CountShadow", "count = 5\ncount"),
        Special("huntA14Open1O06CountUserCallable", "count(x) = x * 2\ncount(3), 5.count"),
        Special("huntA14Open1O09OpenPrivateNotProvided", "open Box\nBox = { X = 5 }\nX"),
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
        // A spread leaf supplies exactly its spread items, one boundary per written
        // star: a LONE structured item stays whole and a lone spread-produced `()`
        // stays an item (the join drops only a NON-spread `()` leaf).
        new("sc_spread_lone_list", "SequenceConstruct[[[7]]*, 3] keeps the lone list item whole",
            () => Sc(new Expr.SequenceSpread(new Expr.ListLiteral([new Expr.ListLiteral([ScNum(7)])])), ScNum(3)),
            "([[7]]*, 3)", InternalNodeRelation.IntentionallyEqual),
        new("sc_spread_lone_empty", "SequenceConstruct[[()]*, 3] keeps the spread-produced () item",
            () => Sc(new Expr.SequenceSpread(new Expr.ListLiteral([ScEmpty()])), ScNum(3)),
            "([()]*, 3)", InternalNodeRelation.IntentionallyEqual),
        new("sc_spread_lone_pair", "SequenceConstruct[[(1,2)]*, 3] keeps the lone pair item whole",
            () => Sc(new Expr.SequenceSpread(new Expr.ListLiteral([new Expr.Capture([ScNum(1), ScNum(2)])])), ScNum(3)),
            "([(1, 2)]*, 3)", InternalNodeRelation.IntentionallyEqual),
        new("sc_spread_stacked_lone", "SequenceConstruct[[[[7]]]**, 3] opens one boundary per written star",
            () => Sc(new Expr.SequenceSpread(new Expr.SequenceSpread(
                new Expr.ListLiteral([new Expr.ListLiteral([new Expr.ListLiteral([ScNum(7)])])]))), ScNum(3)),
            "([[[7]]]**, 3)", InternalNodeRelation.IntentionallyEqual),
        new("sc_spread_missing_output", "SequenceConstruct[{A = 1}*, 3] fails like the spread anywhere else",
            () => Sc(new Expr.SequenceSpread(new Expr.AlgorithmExpr(new Algorithm.User(
                Parent: null, ParameterPatterns: [], Opens: [],
                Properties: [new Property("A", new Algorithm.User(null, [], [], [], [ScNum(1)]))],
                Output: []))), ScNum(3)),
            "({A = 1}*, 3)", InternalNodeRelation.IntentionallyEqual),
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
