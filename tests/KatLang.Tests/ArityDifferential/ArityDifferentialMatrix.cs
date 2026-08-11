namespace KatLang.Tests.ArityDifferential;

using static AlgebraOracle;

/// <summary>
/// Deterministic generator of the arity-differential campaign: the executable
/// matrix (shape × receiver × form × spread multiplicity), the relational
/// equivalence families, the diagnostic matrix, and the exclusion ledger that
/// accounts for every theoretical cell that has no executable case.
///
/// Every expectation is computed through <see cref="AlgebraOracle"/> only —
/// never through production helpers — and rendered in the neutral encoding
/// shared with the generated Lean guards.
/// </summary>
public static class ArityDifferentialMatrix
{
    // ----- Value-shape catalog -------------------------------------------------

    /// <summary>
    /// Representative stored operands. One numeric skin per structural shape —
    /// additional literals would duplicate cells without adding structure.
    /// </summary>
    public static readonly IReadOnlyList<ValueShape> Shapes =
    [
        new("atom", "7", OracleVal.Atom(7),
            "scalar atom; spread is total (supplies itself), repeated spread neutral"),
        new("written-singleton-seq", "(7)", OracleVal.Atom(7),
            "written singleton sequence; canonicalizes to the atom at the defining capture boundary"),
        new("empty-seq", "()", OracleVal.Seq(),
            "empty sequence value; visible unspread, zero-item spread"),
        new("multi-seq", "(1, 2)", OracleVal.Seq(OracleVal.Atom(1), OracleVal.Atom(2)),
            "canonical two-item sequence value"),
        new("nested-seq", "((1, 2), 3)", OracleVal.Seq(OracleVal.Seq(OracleVal.Atom(1), OracleVal.Atom(2)), OracleVal.Atom(3)),
            "sequence with a structured member; one-boundary spread must keep the inner pair intact"),
        new("empty-list", "[]", OracleVal.List(),
            "empty exact list; visible unspread value, zero-item spread"),
        new("singleton-list", "[7]", OracleVal.List(OracleVal.Atom(7)),
            "singleton exact list; never canonicalized away; lone-ATOM spread is repeated-spread neutral"),
        new("multi-list", "[1, 2]", OracleVal.List(OracleVal.Atom(1), OracleVal.Atom(2)),
            "two-item exact list; spread-then-capture converts to the sequence world"),
        new("lone-seq-row", "[(1, 2)]", OracleVal.List(OracleVal.Seq(OracleVal.Atom(1), OracleVal.Atom(2))),
            "singleton list holding a sequence row; lone STRUCTURED item — repeated spread opens one more boundary; deconstruction capture-boundary counterexample"),
        new("lone-list", "[[1, 2]]", OracleVal.List(OracleVal.List(OracleVal.Atom(1), OracleVal.Atom(2))),
            "singleton list holding a list; the list twin of lone-seq-row"),
        new("mixed-list-seq", "[(1, 2), 3]", OracleVal.List(OracleVal.Seq(OracleVal.Atom(1), OracleVal.Atom(2)), OracleVal.Atom(3)),
            "mixed list (sequence member + scalar); multi-item fixed point must not open the member"),
        new("mixed-list-atom", "[[1, 2], 3]", OracleVal.List(OracleVal.List(OracleVal.Atom(1), OracleVal.Atom(2)), OracleVal.Atom(3)),
            "mixed list (list member + scalar); mirrors stackedSpreadMixedSupplyStaysUnopened"),
        new("list-of-lists", "[[1, 2], [3, 4]]",
            OracleVal.List(OracleVal.List(OracleVal.Atom(1), OracleVal.Atom(2)), OracleVal.List(OracleVal.Atom(3), OracleVal.Atom(4))),
            "two structured members; mirrors stackedSpreadMultiItemFixedPoint / repeated_spread_multi_item_fixed_point"),
        new("deep-lone-list", "[[[7]]]", OracleVal.List(OracleVal.List(OracleVal.List(OracleVal.Atom(7)))),
            "triple-nested lone list; each spread chain layer opens exactly one boundary"),
    ];

    public static readonly IReadOnlyDictionary<string, ValueShape> ShapesById =
        Shapes.ToDictionary(s => s.Id, StringComparer.Ordinal);

    private static readonly IReadOnlyList<SpreadMultiplicity> AllMults =
        [SpreadMultiplicity.Zero, SpreadMultiplicity.One, SpreadMultiplicity.Repeated];

    /// <summary>Theoretical combination space: every (receiver, form, shape, multiplicity) cell.</summary>
    public static int TheoreticalCellCount =>
        Enum.GetValues<ReceiverKind>().Length * Enum.GetValues<BindingForm>().Length * Shapes.Count * AllMults.Count;

    // ----- Shared program fragments --------------------------------------------

    private const string GatherDef = "Gather(*items) = items";
    private const string Probe1Def = "Probe1(x) = [x]";
    private const string Pair2Def = "Pair2(x, y) = [x, y]";
    private const string Mid3Def = "Mid3(first, *mid, last) = [first, mid, last]";
    private const string Suffix2Def = "Suffix2(*init, last) = [init, last]";

    private static string ArgText(SpreadMultiplicity m) => m switch
    {
        SpreadMultiplicity.Zero => "V",
        SpreadMultiplicity.One => "V*",
        _ => "V**",
    };

    /// <summary>The argument-slot supply a written V / V* / V** contributes (one written slot, or the spread-chain supply).</summary>
    private static IReadOnlyList<OracleVal> ArgSupply(ValueShape shape, SpreadMultiplicity m) =>
        m == SpreadMultiplicity.Zero ? [shape.Value] : SpreadSupply(shape.Value, (int)m);

    private static string SupplyNeutral(IReadOnlyList<OracleVal> supply) =>
        $"[{string.Join(", ", supply.Select(v => v.Neutral))}]";

    private static List<string> SupplyTrace(ValueShape shape, SpreadMultiplicity m)
    {
        var trace = new List<string> { $"V = {shape.Value.Neutral} (stored canonical value)" };
        switch (m)
        {
            case SpreadMultiplicity.Zero:
                trace.Add($"written slot V -> one argument value {shape.Value.Neutral}");
                break;
            case SpreadMultiplicity.One:
                trace.Add($"items(V) = {SupplyNeutral(Items(shape.Value))}   [spread : Value -> Supply]");
                break;
            default:
                trace.Add($"items(V) = {SupplyNeutral(Items(shape.Value))}");
                trace.Add($"capture(items V) = {Capture(Items(shape.Value)).Neutral}   [second star crosses the ordinary capture boundary]");
                trace.Add($"items(capture(items V)) = {SupplyNeutral(SpreadSupply(shape.Value, 2))}   [repeated_spread_cardinality]");
                break;
        }

        return trace;
    }

    /// <summary>Rewrites an oracle value back to a KatLang literal (used by the spread-vs-literal-items relation).</summary>
    private static string LiteralOf(OracleVal value) => value switch
    {
        OracleVal.AtomVal a => a.Value.ToString(System.Globalization.CultureInfo.InvariantCulture),
        OracleVal.SeqVal s => $"({string.Join(", ", s.Items.Select(LiteralOf))})",
        OracleVal.ListVal l => $"[{string.Join(", ", l.Items.Select(LiteralOf))}]",
        _ => throw new InvalidOperationException($"Unrenderable oracle value {value}"),
    };

    private static ExpectedObservation Ok(OracleVal value, int emitted) => new() { Neutral = OkNeutral(value, emitted) };
    private static ExpectedObservation Err(string category) => new() { Neutral = ErrNeutral(category) };
    private const string Arity = "arity";

    // ----- Matrix generation ----------------------------------------------------

    private sealed record Cell(ReceiverKind Receiver, BindingForm Form, string ShapeId, SpreadMultiplicity Multiplicity);

    private sealed class Builder
    {
        public List<DifferentialCase> Cases { get; } = [];
        public HashSet<Cell> Covered { get; } = [];

        public void Add(
            string template, ReceiverKind receiver, BindingForm form, ValueShape shape, SpreadMultiplicity m,
            string source, ReceiverLaw law, ExpectedObservation expected, IEnumerable<string> trace, string? notes = null)
        {
            Cases.Add(new DifferentialCase
            {
                Id = $"ad-{template}--{shape.Id}--s{(int)m}",
                Receiver = receiver,
                Form = form,
                ShapeId = shape.Id,
                Multiplicity = m,
                Source = source,
                PrimaryLaw = law,
                Expected = expected,
                AlgebraTrace = trace.ToArray(),
                Notes = notes,
            });
            Covered.Add(new Cell(receiver, form, shape.Id, m));
        }
    }

    private static readonly Lazy<(IReadOnlyList<DifferentialCase> Cases, IReadOnlyList<ExcludedCombination> Excluded)> Generated =
        new(Generate, LazyThreadSafetyMode.ExecutionAndPublication);

    public static IReadOnlyList<DifferentialCase> MatrixCases() => Generated.Value.Cases;
    public static IReadOnlyList<ExcludedCombination> ExcludedCells() => Generated.Value.Excluded;

    /// <summary>Regenerates everything from scratch (bypassing the caches) so tests can verify clean-regeneration determinism.</summary>
    internal static (IReadOnlyList<DifferentialCase> Matrix, IReadOnlyList<ExcludedCombination> Excluded,
        IReadOnlyList<RelationalCase> Relational, IReadOnlyList<DiagnosticCase> Diagnostics) GenerateFresh()
    {
        var (cases, excluded) = Generate();
        return (cases, excluded, GenerateRelational(), GenerateDiagnostics());
    }

    private static IEnumerable<ValueShape> GeneralShapes =>
        Shapes.Where(s => s.Id != "written-singleton-seq");

    private static ReceiverLaw SupplyLaw(SpreadMultiplicity m, ReceiverLaw zeroAndDefault) => m switch
    {
        SpreadMultiplicity.Repeated => ReceiverLaw.REPEATED_SPREAD_CAPTURE_COMPOSITION,
        SpreadMultiplicity.One => ReceiverLaw.SPREAD_CONTRIBUTES_ITEMS,
        _ => zeroAndDefault,
    };

    private static (IReadOnlyList<DifferentialCase>, IReadOnlyList<ExcludedCombination>) Generate()
    {
        var b = new Builder();

        foreach (var shape in GeneralShapes)
        {
            foreach (var m in AllMults)
            {
                AddDirectCallCases(b, shape, m);
                AddDottedCallCases(b, shape, m);
                AddAssignmentCases(b, shape, m);
                AddPropertyCases(b, shape, m);
                AddCallbackCases(b, shape, m);
                AddLoopStepCases(b, shape, m);
            }
        }

        AddWrittenSingletonCases(b);
        AddWhileCases(b);

        var excluded = AccountForUncoveredCells(b.Covered);
        return (b.Cases, excluded);
    }

    // ----- Direct calls ---------------------------------------------------------

    private static void AddDirectCallCases(Builder b, ValueShape shape, SpreadMultiplicity m)
    {
        var supply = ArgSupply(shape, m);
        var arg = ArgText(m);
        var baseTrace = SupplyTrace(shape, m);

        // T1: single collecting parameter — the exact-supply observation window.
        var collected = Collect(supply);
        b.Add("call-collect", ReceiverKind.DirectCall, BindingForm.Collect, shape, m,
            $"V = {shape.Literal}\n{GatherDef}\nGather({arg})",
            SupplyLaw(m, ReceiverLaw.COLLECT_PRESERVES_EXACT_SUPPLY),
            Ok(collected, 1),
            baseTrace.Append($"bindArgs [*items] -> items = collect(supply) = {collected.Neutral}; call result is one value (n=1)"));

        // T2: fixed unary — written boundaries and ordinary arity after spreading.
        if (supply.Count == 1)
        {
            var bound = OracleVal.List(supply[0]);
            b.Add("call-fixed-unary", ReceiverKind.DirectCall, BindingForm.Capture, shape, m,
                $"V = {shape.Literal}\n{Probe1Def}\nProbe1({arg})",
                SupplyLaw(m, ReceiverLaw.CALL_PRESERVES_WRITTEN_BOUNDARIES),
                Ok(bound, 1),
                baseTrace.Append($"bindArgs [x] over 1 slot -> x = {supply[0].Neutral}; body [x] = {bound.Neutral}"));
        }
        else
        {
            b.Add("call-fixed-unary", ReceiverKind.DirectCall, BindingForm.Capture, shape, m,
                $"V = {shape.Literal}\n{Probe1Def}\nProbe1({arg})",
                SupplyLaw(m, ReceiverLaw.CALL_PRESERVES_WRITTEN_BOUNDARIES),
                Err(Arity),
                baseTrace.Append($"bindArgs [x] over {supply.Count} slots -> arity mismatch (spread supplies ordinary slots before arity checking)"));
        }

        // T3: fixed pair with a trailing written anchor — the spread/comma slot boundary.
        var pairSlots = supply.Append(OracleVal.Atom(9)).ToArray();
        if (pairSlots.Length == 2)
        {
            var bound = OracleVal.List(pairSlots[0], pairSlots[1]);
            b.Add("call-fixed-pair", ReceiverKind.DirectCall, BindingForm.Capture, shape, m,
                $"V = {shape.Literal}\n{Pair2Def}\nPair2({arg}, 9)",
                SupplyLaw(m, ReceiverLaw.CALL_PRESERVES_WRITTEN_BOUNDARIES),
                Ok(bound, 1),
                baseTrace.Append($"slots = supply ++ [9]; bindArgs [x, y] -> {bound.Neutral}"));
        }
        else
        {
            b.Add("call-fixed-pair", ReceiverKind.DirectCall, BindingForm.Capture, shape, m,
                $"V = {shape.Literal}\n{Pair2Def}\nPair2({arg}, 9)",
                SupplyLaw(m, ReceiverLaw.CALL_PRESERVES_WRITTEN_BOUNDARIES),
                Err(Arity),
                baseTrace.Append($"slots = supply ++ [9] ({pairSlots.Length} slots) vs 2 fixed parameters -> arity mismatch"));
        }

        // T4: mixed fixed/collecting/fixed — exact middle-segment allocation.
        var midCollected = Collect(supply);
        var midResult = OracleVal.List(OracleVal.Atom(0), midCollected, OracleVal.Atom(9));
        b.Add("call-mixed-collecting", ReceiverKind.DirectCall, BindingForm.Collect, shape, m,
            $"V = {shape.Literal}\n{Mid3Def}\nMid3(0, {arg}, 9)",
            m == SpreadMultiplicity.Repeated
                ? ReceiverLaw.REPEATED_SPREAD_CAPTURE_COMPOSITION
                : ReceiverLaw.COLLECT_SEGMENT_ALLOCATION,
            Ok(midResult, 1),
            baseTrace.Append($"bindPats [first, *mid, last] over [0] ++ supply ++ [9] -> mid = collect(supply) = {midCollected.Neutral}"));

        // T1b: the SAME value spread twice into one surrounding supply —
        // provenance independence of collection (each marker contributes its
        // own items; nothing is deduplicated or merged).
        if (m == SpreadMultiplicity.One)
        {
            var doubled = Items(shape.Value).Concat(Items(shape.Value)).ToArray();
            var doubledCollected = Collect(doubled);
            b.Add("call-collect-twice", ReceiverKind.DirectCall, BindingForm.Collect, shape, m,
                $"V = {shape.Literal}\n{GatherDef}\nGather(V*, V*)",
                ReceiverLaw.SPREAD_CONTRIBUTES_ITEMS,
                Ok(doubledCollected, 1),
                baseTrace.Append($"each spread contributes its own items: collect(items(V) ++ items(V)) = {doubledCollected.Neutral}"),
                notes: "Provenance independence (collectSegment_spread_concat_exact): the same value spread twice supplies its items twice.");
        }

        // T1c: a triple-star chain — each written star crosses one more
        // ordinary capture boundary, never more than one boundary at a time.
        if (m == SpreadMultiplicity.Repeated && shape.Id is "deep-lone-list" or "list-of-lists")
        {
            var tripleSupply = SpreadSupply(shape.Value, 3);
            var tripleCollected = Collect(tripleSupply);
            b.Add("call-collect-triple", ReceiverKind.DirectCall, BindingForm.Collect, shape, m,
                $"V = {shape.Literal}\n{GatherDef}\nGather(V***)",
                ReceiverLaw.REPEATED_SPREAD_CAPTURE_COMPOSITION,
                Ok(tripleCollected, 1),
                baseTrace
                    .Append($"third star: items(capture(...)) once more -> {SupplyNeutral(tripleSupply)}")
                    .Append($"collect -> {tripleCollected.Neutral}"),
                notes: "Triple chain: one boundary per star (CoreArityAlgebraProofs triple-chain examples), never recursive flattening.");
        }

        // T25: spread of a call RESULT — the one-value result boundary re-opened.
        if (m != SpreadMultiplicity.Zero)
        {
            var callValue = Collect([shape.Value]); // Gather(V) collects the one grouped argument
            var rowSupply = SpreadSupply(callValue, (int)m);
            var rowValue = Capture(rowSupply);
            b.Add("call-result-spread", ReceiverKind.DirectCall, BindingForm.Spread, shape, m,
                $"V = {shape.Literal}\n{GatherDef}\nGather(V){new string('*', (int)m)}",
                m == SpreadMultiplicity.Repeated
                    ? ReceiverLaw.REPEATED_SPREAD_CAPTURE_COMPOSITION
                    : ReceiverLaw.SPREAD_CONTRIBUTES_ITEMS,
                Ok(rowValue, rowSupply.Count),
                new[]
                {
                    $"Gather(V) = collect([V]) = {callValue.Neutral} (call result: ONE value boundary)",
                    $"spread chain over the call result -> supply {SupplyNeutral(rowSupply)}",
                    $"root spread row emits the supply: raw {rowValue.Neutral}, n={rowSupply.Count}",
                },
                notes: "Spread applies to the call's one result value (the A*.F* row of the value/supply table).");
        }
    }

    // ----- Dotted calls ---------------------------------------------------------

    private static void AddDottedCallCases(Builder b, ValueShape shape, SpreadMultiplicity m)
    {
        var baseTrace = SupplyTrace(shape, m);

        if (m == SpreadMultiplicity.Zero)
        {
            // T9: dotted zero-arg on a collecting callee — the receiver is one
            // leading segment; the collector allocated the segment consumes
            // its evaluated top-level supply. A stored property receiver
            // supplies its value-boundary count: one item, or zero for `()`.
            var segmentSupply = StoredReceiverSegmentSupply(shape.Value);
            var collected = Collect(segmentSupply);
            b.Add("dot-collect", ReceiverKind.DottedCall, BindingForm.Collect, shape, m,
                $"V = {shape.Literal}\n{GatherDef}\nV.Gather",
                ReceiverLaw.COLLECTOR_CONSUMES_ALLOCATED_SEGMENT_SUPPLY,
                Ok(collected, 1),
                baseTrace.Append(
                    $"receiver segment: value {shape.Value.Neutral}, stored-value supply {SupplyNeutral(segmentSupply)} (valueCount view); "
                    + $"collector consumes the supply: {collected.Neutral}"));

            // T12: dotted fixed-arity with an extra argument.
            var pair = OracleVal.List(shape.Value, OracleVal.Atom(9));
            b.Add("dot-fixed-pair", ReceiverKind.DottedCall, BindingForm.Capture, shape, m,
                $"V = {shape.Literal}\n{Pair2Def}\nV.Pair2(9)",
                ReceiverLaw.DOTTED_CALL_EQUALS_DIRECT_REWRITE,
                Ok(pair, 1),
                baseTrace.Append($"V.Pair2(9) = Pair2(V, 9) -> {pair.Neutral} (receiver is ONE leading argument boundary)"));

            AddDotReceiverSegmentCases(b, shape);
            return;
        }

        var stars = new string('*', (int)m);
        var supply = SpreadSupply(shape.Value, (int)m);

        // T10: fluent spread receiver — the supply stays a supply.
        var fluentCollected = Collect(supply);
        b.Add("dot-fluent-spread", ReceiverKind.DottedCall, BindingForm.Spread, shape, m,
            $"V = {shape.Literal}\n{GatherDef}\nV{stars}.Gather",
            ReceiverLaw.FLUENT_SPREAD_RECEIVER_IS_LEXICAL_CALL,
            Ok(fluentCollected, 1),
            baseTrace.Append($"V{stars}.Gather lowers to Gather(V{stars}); collect(supply) = {fluentCollected.Neutral}"));

        // T11: grouped spread receiver on a FIXED callee — parentheses capture
        // the supply and the receiver stays one argument boundary.
        var captured = Capture(supply);
        var groupedPair = OracleVal.List(captured, OracleVal.Atom(9));
        b.Add("dot-grouped-capture", ReceiverKind.DottedCall, BindingForm.Capture, shape, m,
            $"V = {shape.Literal}\n{Pair2Def}\n(V{stars}).Pair2(9)",
            ReceiverLaw.GROUPED_SPREAD_RECEIVER_CAPTURES,
            Ok(groupedPair, 1),
            baseTrace
                .Append($"(V{stars}) captures the supply as ONE value {captured.Neutral}")
                .Append($"fixed receiver parameters keep the receiver one boundary: Pair2({captured.Neutral}, 9) -> {groupedPair.Neutral}"));

        // T11b: grouped spread receiver on a collecting callee — the general
        // segment rule: the written capture receiver's raw supply is the
        // spread chain's items, and the collector allocated the segment
        // consumes exactly that supply. Same outcome as the fluent form, with
        // no callee inspection and no spelling recognition.
        b.Add("dot-grouped-collecting", ReceiverKind.DottedCall, BindingForm.Collect, shape, m,
            $"V = {shape.Literal}\n{GatherDef}\n(V{stars}).Gather",
            ReceiverLaw.COLLECTOR_CONSUMES_ALLOCATED_SEGMENT_SUPPLY,
            Ok(fluentCollected, 1),
            baseTrace
                .Append($"(V{stars}) is one receiver segment: value {Capture(supply).Neutral}, raw row supply {SupplyNeutral(supply)}")
                .Append($"the collector allocated the segment consumes the supply: collect(supply) = {fluentCollected.Neutral}"),
            notes: "General segment rule (no receiver-spelling recognition, no callee inspection): "
                + "a written group receiver supplies its raw row emission to an allocated collector.");
    }

    /// <summary>
    /// T13 family: WRITTEN inline receiver segments at zero spread
    /// multiplicity — the general segment rule observed from every side:
    /// inline group supply consumption, nested-group boundary preservation,
    /// empty receiver, exact-list opacity, and allocation-before-consumption
    /// with fixed prefix/suffix parameters.
    /// </summary>
    private static void AddDotReceiverSegmentCases(Builder b, ValueShape shape)
    {
        var m = SpreadMultiplicity.Zero;

        // T13a: inline group receiver — the capture's raw row supply reaches
        // the collector. Each non-spread written row is ONE slot even when its
        // value is the empty sequence (the visible-empty row rule,
        // RootNonSpreadRow), so the stored-V row contributes V itself.
        var inlineSupply = new[] { shape.Value, OracleVal.Atom(9) };
        var inlineCollected = Collect(inlineSupply);
        b.Add("dot-inline-collect", ReceiverKind.DottedCall, BindingForm.Collect, shape, m,
            $"V = {shape.Literal}\n{GatherDef}\n(V, 9).Gather",
            ReceiverLaw.COLLECTOR_CONSUMES_ALLOCATED_SEGMENT_SUPPLY,
            Ok(inlineCollected, 1),
            [
                $"V = {shape.Value.Neutral} (stored canonical value)",
                $"inline receiver (V, 9): raw row supply {SupplyNeutral(inlineSupply)} (each non-spread row is one visible slot)",
                $"collector consumes the segment supply: {inlineCollected.Neutral}",
            ]);

        // T13b: nested group receiver — the inner written group reifies to ONE
        // item of the outer supply; nesting adds exactly one boundary.
        var innerCaptured = Capture(inlineSupply);
        var nestedCollected = Collect([innerCaptured]);
        b.Add("dot-nested-collect", ReceiverKind.DottedCall, BindingForm.Collect, shape, m,
            $"V = {shape.Literal}\n{GatherDef}\n((V, 9)).Gather",
            ReceiverLaw.COLLECTOR_CONSUMES_ALLOCATED_SEGMENT_SUPPLY,
            Ok(nestedCollected, 1),
            [
                $"inner group (V, 9) reifies to ONE outer row item {innerCaptured.Neutral}",
                $"outer receiver supply [{innerCaptured.Neutral}]; collector consumes it: {nestedCollected.Neutral}",
            ]);

        // T13c: exact-list literal receiver — a list is one opaque supply item
        // (only explicit spread opens it), so the collector collects the list.
        var listReceiver = OracleVal.List(shape.Value, OracleVal.Atom(9));
        var listCollected = Collect([listReceiver]);
        b.Add("dot-list-literal-collect", ReceiverKind.DottedCall, BindingForm.Collect, shape, m,
            $"V = {shape.Literal}\n{GatherDef}\n[V, 9].Gather",
            ReceiverLaw.COLLECTOR_CONSUMES_ALLOCATED_SEGMENT_SUPPLY,
            Ok(listCollected, 1),
            [
                $"list-literal receiver [V, 9] = {listReceiver.Neutral}: one value, supply of one opaque item",
                $"collect([{listReceiver.Neutral}]) = {listCollected.Neutral} (lists never open implicitly)",
            ]);

        // T13d: allocation before consumption, fixed prefix — the receiver
        // segment allocated to the FIXED first parameter binds its one
        // captured value; its supply view is ignored.
        var prefixResult = OracleVal.List(innerCaptured, OracleVal.List(), OracleVal.Atom(2));
        b.Add("dot-seg-fixed-prefix", ReceiverKind.DottedCall, BindingForm.Capture, shape, m,
            $"V = {shape.Literal}\n{Mid3Def}\n(V, 9).Mid3(2)",
            ReceiverLaw.COLLECTOR_CONSUMES_ALLOCATED_SEGMENT_SUPPLY,
            Ok(prefixResult, 1),
            [
                $"segments [receiver, 2]; fixed first takes the receiver's one captured value {innerCaptured.Neutral}",
                $"mid collects the empty middle segment; last = 2 -> {prefixResult.Neutral}",
            ]);

        // T13e/T13f: suffix allocation from the back — with only the receiver
        // segment, the fixed suffix binds the receiver's captured value
        // (supply ignored); with one extra argument, the suffix takes the
        // extra and the collector consumes the receiver segment's supply.
        var suffixWhole = OracleVal.List(OracleVal.List(), innerCaptured);
        b.Add("dot-seg-suffix-whole", ReceiverKind.DottedCall, BindingForm.Capture, shape, m,
            $"V = {shape.Literal}\n{Suffix2Def}\n(V, 9).Suffix2",
            ReceiverLaw.COLLECTOR_CONSUMES_ALLOCATED_SEGMENT_SUPPLY,
            Ok(suffixWhole, 1),
            [
                $"one segment; suffix last binds the receiver's one captured value {innerCaptured.Neutral} (supply ignored at a fixed position)",
                $"init collects the empty middle segment -> {suffixWhole.Neutral}",
            ]);

        var suffixConsumed = OracleVal.List(Collect(inlineSupply), OracleVal.Atom(5));
        b.Add("dot-seg-suffix-consumed", ReceiverKind.DottedCall, BindingForm.Collect, shape, m,
            $"V = {shape.Literal}\n{Suffix2Def}\n(V, 9).Suffix2(5)",
            ReceiverLaw.COLLECTOR_CONSUMES_ALLOCATED_SEGMENT_SUPPLY,
            Ok(suffixConsumed, 1),
            [
                "segments [receiver, 5]; suffix last = 5 from the back BEFORE any supply consumption",
                $"the collector is allocated the receiver segment and consumes its supply {SupplyNeutral(inlineSupply)} -> {suffixConsumed.Neutral}",
            ]);

        // T13g: the empty written group receiver supplies ZERO items (pinned
        // once, on the empty-seq shape — the source has no V occurrence).
        if (shape.Id == "empty-seq")
        {
            b.Add("dot-empty-collect", ReceiverKind.DottedCall, BindingForm.Collect, shape, m,
                $"V = {shape.Literal}\n{GatherDef}\n().Gather",
                ReceiverLaw.COLLECTOR_CONSUMES_ALLOCATED_SEGMENT_SUPPLY,
                Ok(Collect([]), 1),
                [
                    "() receiver: value S[], supply [] (emitted count 0)",
                    "collector consumes the zero-item supply: L[]",
                ]);
        }
    }

    // ----- Assignment (capture + deconstruction) --------------------------------

    private static void AddAssignmentCases(Builder b, ValueShape shape, SpreadMultiplicity m)
    {
        var supply = ArgSupply(shape, m);
        var arg = ArgText(m);
        var baseTrace = SupplyTrace(shape, m);

        // T5: ordinary capture (single-target assignment / property definition).
        var captured = Capture(supply);
        var (rootValue, emitted) = RootNonSpreadRow(captured, ValueCount(captured));
        b.Add("assign-capture", ReceiverKind.Assignment, BindingForm.Capture, shape, m,
            $"V = {shape.Literal}\nX = {arg}\nX",
            SupplyLaw(m, ReceiverLaw.CAPTURE_CANONICALIZES_SUPPLY),
            Ok(rootValue, emitted),
            baseTrace.Append($"X = capture(supply) = {captured.Neutral}; access re-counts to valueCount, root keeps a non-spread row visible (n={emitted})"));

        // Deconstruction templates share the RHS capture boundary: the written
        // right-hand side is evaluated once into one shared value.
        var shared = Capture(supply);
        var sharedTrace = baseTrace
            .Append($"deconstruction RHS captured once: shared = capture(supply) = {shared.Neutral}")
            .Append($"openLoneStructure([shared]) = {SupplyNeutral(OpenLoneStructure([shared]))}")
            .ToArray();
        var opened = OpenLoneStructure([shared]);

        var deconLaw = m switch
        {
            SpreadMultiplicity.Zero => ReceiverLaw.DECONSTRUCTION_OPENS_LONE_STRUCTURE,
            SpreadMultiplicity.One => ReceiverLaw.DECONSTRUCTION_RHS_CAPTURE_BOUNDARY,
            _ => ReceiverLaw.REPEATED_SPREAD_CAPTURE_COMPOSITION,
        };

        // T6: lone-collecting deconstruction.
        var loneCollect = Collect(opened);
        b.Add("assign-collect-lone", ReceiverKind.Assignment, BindingForm.Collect, shape, m,
            $"V = {shape.Literal}\n*R = {arg}\nR",
            deconLaw,
            Ok(loneCollect, 1),
            sharedTrace.Append($"*R collects the opened supply: R = {loneCollect.Neutral}"));

        // T7: two fixed deconstruction targets.
        var pairEnv = BindPats([OraclePat.Fixed("x"), OraclePat.Fixed("y")], opened);
        if (pairEnv is null)
        {
            b.Add("assign-decon-pair", ReceiverKind.Assignment, BindingForm.Capture, shape, m,
                $"V = {shape.Literal}\nx, y = {arg}\n[x, y]",
                deconLaw,
                Err(Arity),
                sharedTrace.Append($"bindPats [x, y] over {opened.Count} opened item(s) -> arity mismatch"));
        }
        else
        {
            var pairList = OracleVal.List(pairEnv[0].Value, pairEnv[1].Value);
            b.Add("assign-decon-pair", ReceiverKind.Assignment, BindingForm.Capture, shape, m,
                $"V = {shape.Literal}\nx, y = {arg}\n[x, y]",
                deconLaw,
                Ok(pairList, 1),
                sharedTrace.Append($"bindPats [x, y] -> {pairList.Neutral}"));
        }

        // T8: fixed head + collecting tail deconstruction.
        var mixedEnv = BindPats([OraclePat.Fixed("a"), OraclePat.Collect("r")], opened);
        if (mixedEnv is null)
        {
            b.Add("assign-decon-mixed", ReceiverKind.Assignment, BindingForm.Collect, shape, m,
                $"V = {shape.Literal}\na, *r = {arg}\n[a, r]",
                deconLaw,
                Err(Arity),
                sharedTrace.Append($"bindPats [a, *r] over {opened.Count} opened item(s) -> arity mismatch (fixed captures set the minimum)"));
        }
        else
        {
            var mixedList = OracleVal.List(mixedEnv[0].Value, mixedEnv[1].Value);
            b.Add("assign-decon-mixed", ReceiverKind.Assignment, BindingForm.Collect, shape, m,
                $"V = {shape.Literal}\na, *r = {arg}\n[a, r]",
                deconLaw,
                Ok(mixedList, 1),
                sharedTrace.Append($"bindPats [a, *r] -> a = {mixedEnv[0].Value.Neutral}, r = {mixedEnv[1].Value.Neutral}"));
        }
    }

    // ----- Property receiver ----------------------------------------------------

    private static void AddPropertyCases(Builder b, ValueShape shape, SpreadMultiplicity m)
    {
        var supply = ArgSupply(shape, m);
        var arg = ArgText(m);
        var baseTrace = SupplyTrace(shape, m);

        // T13: multi-row body reified as one value at the access boundary.
        var bodySupply = new[] { OracleVal.Atom(0) }.Concat(supply).ToArray();
        var reified = Capture(bodySupply);
        b.Add("prop-reify", ReceiverKind.Property, BindingForm.Capture, shape, m,
            $"V = {shape.Literal}\nP = 0, {arg}\nP",
            m == SpreadMultiplicity.Repeated
                ? ReceiverLaw.REPEATED_SPREAD_CAPTURE_COMPOSITION
                : ReceiverLaw.PROPERTY_REIFIES_OUTPUT,
            Ok(reified, 1),
            baseTrace.Append($"body supply [0] ++ supply -> P observed as ONE value {reified.Neutral}; access re-counts (n=1)"));

        // T14: property access and explicit call observe the same value.
        if (m != SpreadMultiplicity.Repeated)
        {
            var parity = OracleVal.List(reified, reified);
            b.Add("prop-call-parity", ReceiverKind.Property, BindingForm.Capture, shape, m,
                $"V = {shape.Literal}\nP = 0, {arg}\n[P, P()]",
                ReceiverLaw.PROPERTY_CALL_EQUIVALENT_VALUE,
                Ok(parity, 1),
                baseTrace.Append($"P and P() observe the same value {reified.Neutral} (cache vs bypass is behavioral only)"));
        }

        // T24: spreading a stored property value at root — spread rows emit the supply.
        if (m != SpreadMultiplicity.Zero)
        {
            var stars = new string('*', (int)m);
            var rowSupply = SpreadSupply(shape.Value, (int)m);
            var rowValue = Capture(rowSupply);
            b.Add("prop-spread-root", ReceiverKind.Property, BindingForm.Spread, shape, m,
                $"V = {shape.Literal}\nP = V\nP{stars}",
                m == SpreadMultiplicity.Repeated
                    ? ReceiverLaw.REPEATED_SPREAD_CAPTURE_COMPOSITION
                    : ReceiverLaw.SPREAD_CONTRIBUTES_ITEMS,
                Ok(rowValue, rowSupply.Count),
                baseTrace.Append($"root spread row P{stars} emits the supply: raw {rowValue.Neutral}, n={rowSupply.Count} (zero items emit nothing)"),
                notes: "Root output is not a value boundary: an explicit spread row contributes exactly its items.");
        }
    }

    // ----- Callback receiver ----------------------------------------------------

    private static void AddCallbackCases(Builder b, ValueShape shape, SpreadMultiplicity m)
    {
        var baseTrace = new List<string> { $"collection [{shape.Literal}] holds ONE element: {shape.Value.Neutral}" };

        if (m == SpreadMultiplicity.Zero)
        {
            // T15: unary fixed callback — element binds whole.
            var mappedUnary = OracleVal.List(OracleVal.List(shape.Value));
            b.Add("cb-map-unary", ReceiverKind.Callback, BindingForm.Capture, shape, m,
                $"IdF(x) = [x]\n[{shape.Literal}].map(IdF)",
                ReceiverLaw.CALLBACK_ELEMENT_IS_ONE_INVOCATION_VALUE,
                Ok(mappedUnary, 1),
                baseTrace.Append($"unary callback binds the element whole -> mapped [x] = {OracleVal.List(shape.Value).Neutral}; map materializes {mappedUnary.Neutral}"));

            // T16: single-collecting callback — element collected as one slot.
            var mappedCollecting = OracleVal.List(OracleVal.List(shape.Value));
            b.Add("cb-map-collecting", ReceiverKind.Callback, BindingForm.Collect, shape, m,
                $"GatherCb(*items) = items\n[{shape.Literal}].map(GatherCb)",
                ReceiverLaw.CALLBACK_COLLECTING_COLLECTS_ONE_SLOT,
                Ok(mappedCollecting, 1),
                baseTrace.Append($"collecting callback collects the element as ONE slot: items = {OracleVal.List(shape.Value).Neutral}"));

            // T17: flat binary callback — sequence rows open, everything else arity-errors.
            var rowItems = shape.Value is OracleVal.SeqVal seq ? seq.Items : null;
            if (rowItems is { Count: 2 })
            {
                var mappedPair = OracleVal.List(OracleVal.List(rowItems[0], rowItems[1]));
                b.Add("cb-map-flat-binary", ReceiverKind.Callback, BindingForm.Capture, shape, m,
                    $"PairCb(x, y) = [x, y]\n[{shape.Literal}].map(PairCb)",
                    ReceiverLaw.CALLBACK_FLAT_ROW_CONVENTION,
                    Ok(mappedPair, 1),
                    baseTrace.Append($"flat binary callee opens the lone SEQUENCE row into slots {SupplyNeutral(rowItems)} -> {mappedPair.Neutral}"));
            }
            else
            {
                b.Add("cb-map-flat-binary", ReceiverKind.Callback, BindingForm.Capture, shape, m,
                    $"PairCb(x, y) = [x, y]\n[{shape.Literal}].map(PairCb)",
                    ReceiverLaw.CALLBACK_FLAT_ROW_CONVENTION,
                    Err(Arity),
                    baseTrace.Append(shape.Value is OracleVal.SeqVal openable
                        ? $"sequence row opens to {openable.Items.Count} slot(s) vs 2 fixed parameters -> arity mismatch"
                        : "non-sequence element stays ONE opaque invocation value vs 2 fixed parameters -> arity mismatch (lists never open in flat binding)"));
            }

            // T18: nested sequence-value pattern — opens ONE boundary of either
            // kind. The counted (callback) matcher is deliberately strict on
            // scalar elements: the scalar fallback exists only for
            // single-capture patterns (callback deconstruction is deferred),
            // so a scalar element under the two-capture pattern is rejected.
            var structure = StructureItems(shape.Value);
            if (structure is null)
            {
                b.Add("cb-map-nested-pattern", ReceiverKind.Callback, BindingForm.Capture, shape, m,
                    $"NestedCb((x, *y)) = [x, y]\n[{shape.Literal}].map(NestedCb)",
                    ReceiverLaw.CALLBACK_NESTED_PATTERN_OPENS_ONE_BOUNDARY,
                    Err(Arity),
                    baseTrace.Append(
                        "scalar element: the counted callback matcher's scalar fallback is singleton-pattern-only "
                        + "(KatLang.lean bindCountedParameterPattern: `if items.length == 1`), so the two-capture pattern rejects"),
                    notes: "Callback deconstruction for scalar elements is intentionally deferred (documented strictness).");
                return;
            }

            var patternSupply = structure;
            var patternEnv = BindPats([OraclePat.Fixed("x"), OraclePat.Collect("y")], patternSupply);
            if (patternEnv is null)
            {
                b.Add("cb-map-nested-pattern", ReceiverKind.Callback, BindingForm.Capture, shape, m,
                    $"NestedCb((x, *y)) = [x, y]\n[{shape.Literal}].map(NestedCb)",
                    ReceiverLaw.CALLBACK_NESTED_PATTERN_OPENS_ONE_BOUNDARY,
                    Err(Arity),
                    baseTrace.Append($"pattern (x, *y) over opened supply {SupplyNeutral(patternSupply)} -> arity mismatch (x needs one item)"));
            }
            else
            {
                var mappedPattern = OracleVal.List(OracleVal.List(patternEnv[0].Value, patternEnv[1].Value));
                b.Add("cb-map-nested-pattern", ReceiverKind.Callback, BindingForm.Capture, shape, m,
                    $"NestedCb((x, *y)) = [x, y]\n[{shape.Literal}].map(NestedCb)",
                    ReceiverLaw.CALLBACK_NESTED_PATTERN_OPENS_ONE_BOUNDARY,
                    Ok(mappedPattern, 1),
                    baseTrace.Append($"pattern opens ONE boundary: {SupplyNeutral(patternSupply)} -> x = {patternEnv[0].Value.Neutral}, y = {patternEnv[1].Value.Neutral}"));
            }

            return;
        }

        // T19 (multiplicity >= 1): the reduce initial accumulator is one written slot.
        var supply = ArgSupply(shape, m);
        var arg = ArgText(m);
        var reduceTrace = SupplyTrace(shape, m);
        if (supply.Count == 1)
        {
            var initial = supply[0];
            var (rootValue, emitted) = RootNonSpreadRow(initial, ValueCount(initial));
            b.Add("cb-reduce-initial", ReceiverKind.Callback, BindingForm.Capture, shape, m,
                $"V = {shape.Literal}\nRf(acc, x) = acc + x\nreduce([], Rf, {arg})",
                ReceiverLaw.REDUCE_INITIAL_IS_WRITTEN_VALUE_SLOT,
                Ok(rootValue, emitted),
                reduceTrace.Append($"reduce([], Rf, ...) binds initial = {initial.Neutral}; empty reduction returns it as ONE re-counted value"));
        }
        else
        {
            b.Add("cb-reduce-initial", ReceiverKind.Callback, BindingForm.Capture, shape, m,
                $"V = {shape.Literal}\nRf(acc, x) = acc + x\nreduce([], Rf, {arg})",
                ReceiverLaw.REDUCE_INITIAL_IS_WRITTEN_VALUE_SLOT,
                Err(Arity),
                reduceTrace.Append($"reduce has 3 fixed parameters; spread supplies {supply.Count} slot(s) for the initial position -> {2 + supply.Count} arguments -> arity mismatch"));
        }
    }

    // ----- Loop-step receiver -----------------------------------------------------

    private static void AddLoopStepCases(Builder b, ValueShape shape, SpreadMultiplicity m)
    {
        // T20: collecting snapshot step — init args are written slots.
        var initSlots = ArgSupply(shape, m);
        var arg = ArgText(m);
        if (initSlots.Count == 0)
        {
            b.Add("loop-init-snapshot", ReceiverKind.LoopStep, BindingForm.Collect, shape, m,
                $"V = {shape.Literal}\nSnap(*slots) = slots\nSnap.repeat(1, {arg})",
                SupplyLaw(m, ReceiverLaw.LOOP_INIT_ARGS_ARE_WRITTEN_SLOTS),
                Err(Arity),
                SupplyTrace(shape, m)
                    .Append("the zero-item spread leaves repeat with no initial state slot")
                    .Append("repeat(step, count, init1, ...) requires at least one init argument — an ordinary arity floor after spreading"));
        }
        else
        {
            var snapped = Collect(initSlots);
            b.Add("loop-init-snapshot", ReceiverKind.LoopStep, BindingForm.Collect, shape, m,
                $"V = {shape.Literal}\nSnap(*slots) = slots\nSnap.repeat(1, {arg})",
                SupplyLaw(m, ReceiverLaw.LOOP_INIT_ARGS_ARE_WRITTEN_SLOTS),
                Ok(snapped, 1),
                SupplyTrace(shape, m)
                    .Append($"initial state slots = {SupplyNeutral(initSlots)} (each written init argument is one slot)")
                    .Append($"step collects the slots -> final state is the one list {snapped.Neutral}"));
        }

        // T21 (chain multiplicity One / Repeated): flat step re-spreads its output spread into state slots.
        // The written chain is: [optional init spread] -> collect -> step-output spread.
        if (m != SpreadMultiplicity.Repeated)
        {
            var chainMult = m == SpreadMultiplicity.Zero ? SpreadMultiplicity.One : SpreadMultiplicity.Repeated;
            var initial = ArgSupply(shape, m);
            if (initial.Count == 0)
            {
                b.Add("loop-flat-respread", ReceiverKind.LoopStep, BindingForm.Spread, shape, chainMult,
                    $"V = {shape.Literal}\nGrow(*slots) = slots*, 0\nGrow.repeat(1, {arg})",
                    ReceiverLaw.LOOP_STATE_SLOTS_ARE_NOT_A_VALUE_BOUNDARY,
                    Err(Arity),
                    SupplyTrace(shape, m)
                        .Append("the zero-item spread leaves repeat with no initial state slot")
                        .Append("repeat(step, count, init1, ...) requires at least one init argument — an ordinary arity floor after spreading"),
                    notes: "Chain multiplicity counts the step-output spread plus any init spread.");
            }
            else
            {
                var state = initial.Append(OracleVal.Atom(0)).ToArray();
                var loopResult = Capture(state);
                b.Add("loop-flat-respread", ReceiverKind.LoopStep, BindingForm.Spread, shape, chainMult,
                    $"V = {shape.Literal}\nGrow(*slots) = slots*, 0\nGrow.repeat(1, {arg})",
                    ReceiverLaw.LOOP_STATE_SLOTS_ARE_NOT_A_VALUE_BOUNDARY,
                    Ok(loopResult, state.Length),
                    SupplyTrace(shape, m)
                        .Append($"initial state slots = {SupplyNeutral(initial)}")
                        .Append($"flat step output `slots*, 0` re-spreads the collected list into separate state slots: {SupplyNeutral(state)}")
                        .Append($"loop result keeps the multi-slot count: raw {loopResult.Neutral}, n={state.Length}"),
                    notes: "Chain multiplicity counts the step-output spread plus any init spread; loop state is not a value boundary.");
            }
        }

        // T22 (chain multiplicity One / Repeated): patterned step packs its top-level output spread.
        if (m != SpreadMultiplicity.Repeated)
        {
            var chainMult = m == SpreadMultiplicity.Zero ? SpreadMultiplicity.One : SpreadMultiplicity.Repeated;
            var initSupply = ArgSupply(shape, m).Append(OracleVal.Atom(10)).ToArray();
            var trace = SupplyTrace(shape, m)
                .Append($"initial state slots = {SupplyNeutral(initSupply)} (pattern step needs exactly 2)")
                .ToList();

            ExpectedObservation expected;
            if (initSupply.Length != 2)
            {
                expected = Err(Arity);
                trace.Add($"patterned step has 2 parameters but the state has {initSupply.Length} slot(s) -> loop arity mismatch");
            }
            else
            {
                var state = initSupply;
                var failed = false;
                for (var iteration = 1; iteration <= 2 && !failed; iteration++)
                {
                    if (state.Length != 2)
                    {
                        failed = true;
                        trace.Add($"iteration {iteration}: {state.Length} state slot(s) vs 2 parameters -> loop arity mismatch");
                        break;
                    }

                    var openedHistory = StructureItems(state[0]) ?? [state[0]];
                    var counter = ((OracleVal.AtomVal)state[1]).Value;
                    var nextSlots = new List<OracleVal>();
                    if (openedHistory.Count > 0)
                        nextSlots.Add(Capture(openedHistory)); // packed: ONE next-state slot
                    nextSlots.Add(OracleVal.Atom(counter + 1));
                    trace.Add(openedHistory.Count > 0
                        ? $"iteration {iteration}: (*h) opens {SupplyNeutral(openedHistory)}; packed h* slot = {Capture(openedHistory).Neutral}; p+1 = {counter + 1}"
                        : $"iteration {iteration}: (*h) collects zero items; the zero-item packed spread contributes NO slot; p+1 = {counter + 1}");
                    state = nextSlots.ToArray();
                }

                if (failed)
                {
                    expected = Err(Arity);
                }
                else
                {
                    var loopResult = Capture(state);
                    expected = Ok(loopResult, state.Length);
                    trace.Add($"loop result: raw {loopResult.Neutral}, n={state.Length}");
                }
            }

            b.Add("loop-patterned-packed", ReceiverKind.LoopStep, BindingForm.Capture, shape, chainMult,
                $"V = {shape.Literal}\nPackStep((*h), p) = h*, p + 1\nPackStep.repeat(2, {arg}, 10)",
                ReceiverLaw.LOOP_PATTERNED_STEP_PACKS_TOPLEVEL_SPREAD,
                expected,
                trace,
                notes: "Patterned step output keeps a top-level spread as ONE packed next-state slot; zero-item spread contributes none.");
        }
    }

    // ----- Written-singleton special family ---------------------------------------

    private static void AddWrittenSingletonCases(Builder b)
    {
        var shape = ShapesById["written-singleton-seq"];

        b.Add("assign-capture", ReceiverKind.Assignment, BindingForm.Capture, shape, SpreadMultiplicity.Zero,
            "X = (7)\nX",
            ReceiverLaw.CAPTURE_CANONICALIZES_SUPPLY,
            Ok(OracleVal.Atom(7), 1),
            new[]
            {
                "written (7) is a singleton capture: capture([7]) = 7",
                "the stored value is the atom — no runtime singleton sequence exists (orphanFree_normalize)",
            });

        b.Add("prop-reify", ReceiverKind.Property, BindingForm.Capture, shape, SpreadMultiplicity.Zero,
            "P = 0, (7)\nP",
            ReceiverLaw.PROPERTY_REIFIES_OUTPUT,
            Ok(OracleVal.Seq(OracleVal.Atom(0), OracleVal.Atom(7)), 1),
            new[] { "body supply [0, capture([7])] = [0, 7]; P observed as S[0, 7]" });
    }

    // ----- while receiver (numeric-flag hand family) -------------------------------

    private static void AddWhileCases(Builder b)
    {
        var atom = ShapesById["atom"];

        b.Add("loop-while-flag", ReceiverKind.LoopStep, BindingForm.Capture, atom, SpreadMultiplicity.Zero,
            "Dec = x - 1, x > 1\nDec.while(3)",
            ReceiverLaw.WHILE_LAST_SLOT_IS_CONTINUE_FLAG,
            Ok(OracleVal.Atom(1), 1),
            new[]
            {
                "state 3 -> step (2, 3>1=1) commits 2; state 2 -> (1, 1) commits 1; state 1 -> (0, 0) flag 0 is never committed",
                "pre-check semantics return the last committed state: 1",
            },
            notes: "The while flag family is numeric by necessity; state-shape laws are exercised through repeat.");

        b.Add("loop-while-state", ReceiverKind.LoopStep, BindingForm.Capture, atom, SpreadMultiplicity.Zero,
            "Sum = a + 1, total + a, a < 3\nSum.while(1, 0)",
            ReceiverLaw.WHILE_LAST_SLOT_IS_CONTINUE_FLAG,
            Ok(OracleVal.Seq(OracleVal.Atom(3), OracleVal.Atom(3)), 2),
            new[]
            {
                "all outputs except the last form the working state; the last output is the continue flag",
                "(1,0) -> (2, 1, 1); (2,1) -> (3, 3, 1); (3,3) -> (4, 6, 0) discarded -> result (3, 3), n=2",
            });
    }

    // ----- Exclusion accounting -----------------------------------------------------

    private sealed record ExclusionRule(Func<Cell, bool> Applies, string Reason);

    private static IReadOnlyList<ExclusionRule> ExclusionRules =>
    [
        new(c => c.ShapeId == "written-singleton-seq",
            "The written singleton sequence (7) canonicalizes to the atom at its defining capture boundary "
            + "(CAPTURE_CANONICALIZES_SUPPLY); no distinct stored value exists to feed other receivers, so every "
            + "runtime-reachable cell coincides with the atom shape. Pinned by the two dedicated capture cases."),
        new(c => c.Form == BindingForm.Spread && c.Multiplicity == SpreadMultiplicity.Zero,
            "A spread-form observation requires at least one written spread marker; with zero markers the cell "
            + "is definitionally empty."),
        new(c => c.Receiver == ReceiverKind.Assignment && c.Form == BindingForm.Spread,
            "Assignment always materializes through capture (single target) or collect (collecting target); a "
            + "spread marker on the RHS is the operand mechanism of those forms (the multiplicity dimension), "
            + "not a separate assignment form."),
        new(c => c.Receiver == ReceiverKind.Property && c.Form == BindingForm.Collect,
            "A property definition has no collecting-binding form; collecting at a name is the lone-collecting "
            + "deconstruction, which is an Assignment-receiver cell (*R = ...)."),
        new(c => c.Receiver == ReceiverKind.Callback && c.Form == BindingForm.Collect && c.Multiplicity != SpreadMultiplicity.Zero,
            "Callback invocations are runtime-driven: no written spread marker exists at the invocation boundary. "
            + "Written-spread interaction with the callback receiver is exercised through the reduce-initial "
            + "written slot (Capture form) and the collection-argument arity diagnostics."),
        new(c => c.Receiver == ReceiverKind.Callback && c.Form == BindingForm.Spread,
            "The callback result contract is strict single-value (map transform / reduce step must return exactly "
            + "one value), so no spread-form observation exists at this receiver; spread in a callback body is "
            + "ordinary body-row behavior covered by the Property and DirectCall receivers."),
        new(c => c.Receiver == ReceiverKind.LoopStep && c.Form == BindingForm.Capture && c.Multiplicity == SpreadMultiplicity.Zero,
            "The zero-marker loop-step capture observations are the while-flag family, whose flag arithmetic "
            + "requires numeric state (pinned on the atom shape); the packed-slot capture observation requires "
            + "the step-output spread marker (One/Repeated cells), and zero-marker state assembly is covered by "
            + "the Collect-form init-slot cells."),
    ];

    private static IReadOnlyList<ExcludedCombination> AccountForUncoveredCells(HashSet<Cell> covered)
    {
        var excluded = new List<ExcludedCombination>();
        foreach (var receiver in Enum.GetValues<ReceiverKind>())
        foreach (var form in Enum.GetValues<BindingForm>())
        foreach (var shape in Shapes)
        foreach (var m in AllMults)
        {
            var cell = new Cell(receiver, form, shape.Id, m);
            if (covered.Contains(cell))
                continue;

            var rule = ExclusionRules.FirstOrDefault(r => r.Applies(cell))
                ?? throw new InvalidOperationException(
                    $"Silent matrix omission: cell ({receiver}, {form}, {shape.Id}, {m}) is neither covered by a "
                    + "generated case nor matched by an exclusion rule. Add a case or a documented exclusion.");
            excluded.Add(new ExcludedCombination(receiver, form, shape.Id, m, rule.Reason));
        }

        return excluded;
    }

    // ----- Relational families --------------------------------------------------------

    private static readonly Lazy<IReadOnlyList<RelationalCase>> RelationalGenerated =
        new(GenerateRelational, LazyThreadSafetyMode.ExecutionAndPublication);

    public static IReadOnlyList<RelationalCase> RelationalCases() => RelationalGenerated.Value;

    private static IReadOnlyList<RelationalCase> GenerateRelational()
    {
        var cases = new List<RelationalCase>();

        foreach (var shape in GeneralShapes)
        {
            foreach (var m in AllMults)
            {
                var supply = ArgSupply(shape, m);
                var arg = ArgText(m);
                var trace = SupplyTrace(shape, m);

                // R1a: direct vs dotted, collecting callee. Under the segment
                // rule the two spellings coincide except for the zero-supply
                // stored receiver: a written argument slot reifies `()` to one
                // collected item, while the receiver segment's evaluated
                // supply is empty.
                var dotted = m == SpreadMultiplicity.Zero ? "V.Gather" : $"V{new string('*', (int)m)}.Gather";
                var collected = Ok(Collect(supply), 1);
                var dottedCollected = m == SpreadMultiplicity.Zero
                    ? Ok(Collect(StoredReceiverSegmentSupply(shape.Value)), 1)
                    : collected;
                cases.Add(new RelationalCase
                {
                    Id = $"adr-direct-vs-dotted-collect--{shape.Id}--s{(int)m}",
                    Family = "direct-vs-dotted",
                    ShapeId = shape.Id,
                    Multiplicity = m,
                    LeftSource = $"V = {shape.Literal}\n{GatherDef}\nGather({arg})",
                    RightSource = $"V = {shape.Literal}\n{GatherDef}\n{dotted}",
                    ExpectAgreement = collected.Neutral == dottedCollected.Neutral,
                    PrimaryLaw = m == SpreadMultiplicity.Zero
                        ? ReceiverLaw.COLLECTOR_CONSUMES_ALLOCATED_SEGMENT_SUPPLY
                        : ReceiverLaw.DOTTED_CALL_EQUALS_DIRECT_REWRITE,
                    ExpectedLeft = collected,
                    ExpectedRight = dottedCollected,
                    AlgebraTrace = trace
                        .Append($"written slot: collect(supply) = {Collect(supply).Neutral}; dotted receiver segment supply = {(m == SpreadMultiplicity.Zero ? SupplyNeutral(StoredReceiverSegmentSupply(shape.Value)) : SupplyNeutral(supply))}")
                        .ToArray(),
                });

                // R1b: direct vs dotted, fixed callee with a trailing anchor.
                var pairSlots = supply.Append(OracleVal.Atom(9)).ToArray();
                var pairExpected = pairSlots.Length == 2
                    ? Ok(OracleVal.List(pairSlots[0], pairSlots[1]), 1)
                    : Err(Arity);
                var dottedPair = m == SpreadMultiplicity.Zero ? "V.Pair2(9)" : $"V{new string('*', (int)m)}.Pair2(9)";
                cases.Add(new RelationalCase
                {
                    Id = $"adr-direct-vs-dotted-fixed--{shape.Id}--s{(int)m}",
                    Family = "direct-vs-dotted",
                    ShapeId = shape.Id,
                    Multiplicity = m,
                    LeftSource = $"V = {shape.Literal}\n{Pair2Def}\nPair2({arg}, 9)",
                    RightSource = $"V = {shape.Literal}\n{Pair2Def}\n{dottedPair}",
                    ExpectAgreement = true,
                    PrimaryLaw = ReceiverLaw.DOTTED_CALL_EQUALS_DIRECT_REWRITE,
                    ExpectedLeft = pairExpected,
                    ExpectedRight = pairExpected,
                    AlgebraTrace = trace.Append($"receiver/spread supplies the same leading slots either way; diagnostics must also agree").ToArray(),
                });

                // R6: collecting-parameter forwarding is ordinary list spread.
                cases.Add(new RelationalCase
                {
                    Id = $"adr-forward-round-trip--{shape.Id}--s{(int)m}",
                    Family = "forward-round-trip",
                    ShapeId = shape.Id,
                    Multiplicity = m,
                    LeftSource = $"V = {shape.Literal}\n{GatherDef}\nFwd(*xs) = Gather(xs*)\nFwd({arg})",
                    RightSource = $"V = {shape.Literal}\n{GatherDef}\nGather({arg})",
                    ExpectAgreement = true,
                    PrimaryLaw = ReceiverLaw.COLLECT_SPREAD_ROUND_TRIP,
                    ExpectedLeft = collected,
                    ExpectedRight = collected,
                    AlgebraTrace = trace.Append("items(collect(xs)) = xs, so forwarding re-supplies exactly the collected slots").ToArray(),
                });
            }

            // R2: stacked spelling agrees with the grouped compositional form (repeated only).
            var repeated = SpreadSupply(shape.Value, 2);
            var repeatedExpected = Ok(Collect(repeated), 1);
            cases.Add(new RelationalCase
            {
                Id = $"adr-stacked-vs-grouped--{shape.Id}--s2",
                Family = "stacked-vs-grouped",
                ShapeId = shape.Id,
                Multiplicity = SpreadMultiplicity.Repeated,
                LeftSource = $"V = {shape.Literal}\n{GatherDef}\nGather(V**)",
                RightSource = $"V = {shape.Literal}\n{GatherDef}\nGather((V*)*)",
                ExpectAgreement = true,
                PrimaryLaw = ReceiverLaw.REPEATED_SPREAD_CAPTURE_COMPOSITION,
                ExpectedLeft = repeatedExpected,
                ExpectedRight = repeatedExpected,
                AlgebraTrace = SupplyTrace(shape, SpreadMultiplicity.Repeated)
                    .Append("V** and (V*)* are the same composition items ∘ capture ∘ items")
                    .ToArray(),
            });

            // R2b: the complete fixed-point characterization, both directions.
            var once = Items(shape.Value);
            var fixedPoint = SupplyNeutral(repeated) == SupplyNeutral(once);
            cases.Add(new RelationalCase
            {
                Id = $"adr-repeated-fixed-iff--{shape.Id}--s2",
                Family = "repeated-fixed-iff",
                ShapeId = shape.Id,
                Multiplicity = SpreadMultiplicity.Repeated,
                LeftSource = $"V = {shape.Literal}\n{GatherDef}\nGather(V**)",
                RightSource = $"V = {shape.Literal}\n{GatherDef}\nGather(V*)",
                ExpectAgreement = fixedPoint,
                PrimaryLaw = ReceiverLaw.REPEATED_SPREAD_CAPTURE_COMPOSITION,
                ExpectedLeft = repeatedExpected,
                ExpectedRight = Ok(Collect(once), 1),
                AlgebraTrace = new[]
                {
                    $"items(V) = {SupplyNeutral(once)}; items(capture(items V)) = {SupplyNeutral(repeated)}",
                    fixedPoint
                        ? "fixed point (repeated_spread_fixed_iff: non-singleton supply, or lone atom item)"
                        : "NOT a fixed point: the lone structured item opens one more boundary through singleton capture",
                },
            });

            // R3: an explicit spread equals writing the value's items as literal slots.
            cases.Add(new RelationalCase
            {
                Id = $"adr-spread-vs-literal-items--{shape.Id}--s1",
                Family = "spread-vs-literal-items",
                ShapeId = shape.Id,
                Multiplicity = SpreadMultiplicity.One,
                LeftSource = $"V = {shape.Literal}\n{GatherDef}\nGather(V*)",
                RightSource = $"{GatherDef}\nGather({string.Join(", ", Items(shape.Value).Select(LiteralOf))})",
                ExpectAgreement = true,
                PrimaryLaw = ReceiverLaw.SPREAD_CONTRIBUTES_ITEMS,
                ExpectedLeft = Ok(Collect(once), 1),
                ExpectedRight = Ok(Collect(once), 1),
                AlgebraTrace = new[] { $"items(V) = {SupplyNeutral(once)}, each item supplied as one written slot" },
            });

            // R4: bare deconstruction binds exactly what a call binds on the item view.
            var itemViewEnv = BindArgs([OraclePat.Fixed("x"), OraclePat.Fixed("y")], once);
            var itemViewExpected = itemViewEnv is null
                ? Err(Arity)
                : Ok(OracleVal.List(itemViewEnv[0].Value, itemViewEnv[1].Value), 1);
            cases.Add(new RelationalCase
            {
                Id = $"adr-decon-item-view--{shape.Id}--s0",
                Family = "decon-item-view",
                ShapeId = shape.Id,
                Multiplicity = SpreadMultiplicity.Zero,
                LeftSource = $"V = {shape.Literal}\nx, y = V\n[x, y]",
                RightSource = $"V = {shape.Literal}\n{Pair2Def}\nPair2(V*)",
                ExpectAgreement = true,
                PrimaryLaw = ReceiverLaw.DECONSTRUCTION_OPENS_LONE_STRUCTURE,
                ExpectedLeft = itemViewExpected,
                ExpectedRight = itemViewExpected,
                AlgebraTrace = new[]
                {
                    $"bindDeconstruct ps [V] = bindArgs ps (items V) (deconstruct_singleton_eq_args_items); items(V) = {SupplyNeutral(once)}",
                },
            });

            // R4b: a WRITTEN spread RHS passes the capture boundary first — agreement is shape-dependent.
            var rhsOpened = OpenLoneStructure([Capture(once)]);
            var deconSpreadEnv = BindPats([OraclePat.Fixed("x"), OraclePat.Fixed("y")], rhsOpened);
            var deconSpreadExpected = deconSpreadEnv is null
                ? Err(Arity)
                : Ok(OracleVal.List(deconSpreadEnv[0].Value, deconSpreadEnv[1].Value), 1);
            cases.Add(new RelationalCase
            {
                Id = $"adr-decon-rhs-capture--{shape.Id}--s1",
                Family = "decon-rhs-capture",
                ShapeId = shape.Id,
                Multiplicity = SpreadMultiplicity.One,
                LeftSource = $"V = {shape.Literal}\nx, y = V*\n[x, y]",
                RightSource = $"V = {shape.Literal}\n{Pair2Def}\nPair2(V*)",
                ExpectAgreement = deconSpreadExpected.Neutral == itemViewExpected.Neutral,
                PrimaryLaw = ReceiverLaw.DECONSTRUCTION_RHS_CAPTURE_BOUNDARY,
                ExpectedLeft = deconSpreadExpected,
                ExpectedRight = itemViewExpected,
                AlgebraTrace = new[]
                {
                    $"deconstruction RHS: capture(items V) = {Capture(once).Neutral}, then openLoneStructure -> {SupplyNeutral(rhsOpened)}",
                    $"call side: items(V) = {SupplyNeutral(once)} directly (no capture boundary)",
                },
            });

            // R7: the dot-receiver segment rule, from four sides.
            var itemsOnce = Items(shape.Value);
            var capturedOnce = Capture(itemsOnce);
            var fluentResult = Ok(Collect(itemsOnce), 1);

            // R7a: the grouped and fluent spread receivers coincide on a
            // collecting callee — by the GENERAL segment rule: the fluent form
            // supplies the spread items as argument slots, while the grouped
            // form is one receiver segment whose raw supply is those same
            // items, consumed by the allocated collector.
            cases.Add(new RelationalCase
            {
                Id = $"adr-grouped-vs-fluent-collecting--{shape.Id}--s1",
                Family = "grouped-receiver-exception",
                ShapeId = shape.Id,
                Multiplicity = SpreadMultiplicity.One,
                LeftSource = $"V = {shape.Literal}\n{GatherDef}\n(V*).Gather",
                RightSource = $"V = {shape.Literal}\n{GatherDef}\nV*.Gather",
                ExpectAgreement = true,
                PrimaryLaw = ReceiverLaw.COLLECTOR_CONSUMES_ALLOCATED_SEGMENT_SUPPLY,
                ExpectedLeft = fluentResult,
                ExpectedRight = fluentResult,
                AlgebraTrace = new[]
                {
                    $"(V*) is one receiver segment with raw supply {SupplyNeutral(itemsOnce)}; the allocated collector consumes it",
                    $"V*.Gather lowers to Gather(V*): the same items as ordinary argument slots — both {fluentResult.Neutral}",
                },
            });

            // R7b: receiver segments and written argument slots stay
            // different receivers — the same grouped spread WRITTEN AS AN
            // ARGUMENT reifies to one captured value.
            var writtenArgResult = Ok(Collect([capturedOnce]), 1);
            cases.Add(new RelationalCase
            {
                Id = $"adr-grouped-receiver-vs-written-arg--{shape.Id}--s1",
                Family = "grouped-receiver-exception",
                ShapeId = shape.Id,
                Multiplicity = SpreadMultiplicity.One,
                LeftSource = $"V = {shape.Literal}\n{GatherDef}\n(V*).Gather",
                RightSource = $"V = {shape.Literal}\n{GatherDef}\nGather((V*))",
                ExpectAgreement = fluentResult.Neutral == writtenArgResult.Neutral,
                PrimaryLaw = ReceiverLaw.COLLECTOR_CONSUMES_ALLOCATED_SEGMENT_SUPPLY,
                ExpectedLeft = fluentResult,
                ExpectedRight = writtenArgResult,
                AlgebraTrace = new[]
                {
                    $"receiver segment supply {SupplyNeutral(itemsOnce)} is consumed; the written argument slot reifies to ONE value {capturedOnce.Neutral}",
                    "the two coincide exactly on singleton supplies (capture of one item is the item)",
                },
            });

            // R7c: the segment supply is the receiver's EVALUATED emission —
            // a STORED capture of the same supply evaluates at its value
            // boundary (one item, or zero for `()`), while the written group
            // receiver emits its raw row supply.
            var storedSupply = StoredReceiverSegmentSupply(capturedOnce);
            var storedReceiverResult = Ok(Collect(storedSupply), 1);
            cases.Add(new RelationalCase
            {
                Id = $"adr-grouped-receiver-vs-stored-capture--{shape.Id}--s1",
                Family = "grouped-receiver-exception",
                ShapeId = shape.Id,
                Multiplicity = SpreadMultiplicity.One,
                LeftSource = $"V = {shape.Literal}\n{GatherDef}\nX = (V*)\nX.Gather",
                RightSource = $"V = {shape.Literal}\n{GatherDef}\n(V*).Gather",
                ExpectAgreement = storedReceiverResult.Neutral == fluentResult.Neutral,
                PrimaryLaw = ReceiverLaw.COLLECTOR_CONSUMES_ALLOCATED_SEGMENT_SUPPLY,
                ExpectedLeft = storedReceiverResult,
                ExpectedRight = fluentResult,
                AlgebraTrace = new[]
                {
                    $"X stores the capture {capturedOnce.Neutral}; a stored receiver's segment supply is its valueCount view {SupplyNeutral(storedSupply)}",
                    $"the written group receiver emits its raw row supply {SupplyNeutral(itemsOnce)} — emission, not spelling, decides",
                },
            });

            // R7d: a NON-leading collecting callee allocates the receiver
            // segment to the FIXED first parameter, which binds the captured
            // value and ignores the supply view — so the grouped receiver and
            // the written grouped argument agree.
            var mid3Result = Ok(OracleVal.List(capturedOnce, OracleVal.List(), OracleVal.Atom(9)), 1);
            cases.Add(new RelationalCase
            {
                Id = $"adr-grouped-receiver-non-leading--{shape.Id}--s1",
                Family = "grouped-receiver-exception",
                ShapeId = shape.Id,
                Multiplicity = SpreadMultiplicity.One,
                LeftSource = $"V = {shape.Literal}\n{Mid3Def}\n(V*).Mid3(9)",
                RightSource = $"V = {shape.Literal}\n{Mid3Def}\nMid3((V*), 9)",
                ExpectAgreement = true,
                PrimaryLaw = ReceiverLaw.GROUPED_SPREAD_RECEIVER_CAPTURES,
                ExpectedLeft = mid3Result,
                ExpectedRight = mid3Result,
                AlgebraTrace = new[]
                {
                    "the receiver segment is allocated to the FIXED first parameter, which binds the one captured value (supply ignored)",
                    $"Mid3({capturedOnce.Neutral}, 9): first = {capturedOnce.Neutral}, mid = L[], last = 9",
                },
            });

            // R5: capture and collect of the same supply are intentionally different values.
            cases.Add(new RelationalCase
            {
                Id = $"adr-capture-vs-collect--{shape.Id}--s1",
                Family = "capture-vs-collect",
                ShapeId = shape.Id,
                Multiplicity = SpreadMultiplicity.One,
                LeftSource = $"V = {shape.Literal}\n[(V*)]",
                RightSource = $"V = {shape.Literal}\n{GatherDef}\n[Gather(V*)]",
                ExpectAgreement = false,
                PrimaryLaw = ReceiverLaw.CAPTURE_AND_COLLECT_ARE_DIFFERENT_OPERATIONS,
                ExpectedLeft = Ok(OracleVal.List(Capture(once)), 1),
                ExpectedRight = Ok(OracleVal.List(Collect(once)), 1),
                AlgebraTrace = new[]
                {
                    $"capture(items V) = {Capture(once).Neutral} (canonical sequence construction)",
                    $"collect(items V) = {Collect(once).Neutral} (exact list, boundary never erased)",
                },
            });
        }

        return cases;
    }

    // ----- Diagnostic matrix ------------------------------------------------------------

    private static readonly Lazy<IReadOnlyList<DiagnosticCase>> DiagnosticGenerated =
        new(GenerateDiagnostics, LazyThreadSafetyMode.ExecutionAndPublication);

    public static IReadOnlyList<DiagnosticCase> DiagnosticCases() => DiagnosticGenerated.Value;

    private static IReadOnlyList<DiagnosticCase> GenerateDiagnostics()
    {
        var cases = new List<DiagnosticCase>
        {
            new()
            {
                Id = "add-collect-marker-unattached",
                Family = "collect-marker-structure",
                Source = "F(* items) = items\nF(1)",
                PrimaryLaw = ReceiverLaw.COLLECT_MARKER_IS_BINDING_ONLY,
                ExpectedParseDiagnosticFragment = "collect marker",
            },
            new()
            {
                Id = "add-collect-marker-repeated",
                Family = "collect-marker-structure",
                Source = "F(**items) = items\nF(1)",
                PrimaryLaw = ReceiverLaw.COLLECT_MARKER_IS_BINDING_ONLY,
                ExpectedParseDiagnosticFragment = "collect marker",
            },
            new()
            {
                Id = "add-two-collecting-params",
                Family = "collect-marker-structure",
                Source = "F(*a, *b) = a\nF(1, 2)",
                PrimaryLaw = ReceiverLaw.COLLECT_MARKER_IS_BINDING_ONLY,
                ExpectedParseDiagnosticFragment = "collecting",
            },
            new()
            {
                Id = "add-two-collecting-decon",
                Family = "collect-marker-structure",
                Source = "*a, *b = 1, 2\na",
                PrimaryLaw = ReceiverLaw.COLLECT_MARKER_IS_BINDING_ONLY,
                ExpectedParseDiagnosticFragment = "collecting",
            },
            new()
            {
                Id = "add-collect-marker-expression-position",
                Family = "collect-marker-structure",
                Source = "*(1, 2)",
                PrimaryLaw = ReceiverLaw.COLLECT_MARKER_IS_BINDING_ONLY,
                ExpectedParseDiagnosticFragment = "collect marker",
            },
            new()
            {
                Id = "add-spread-binary-operand",
                Family = "spread-placement",
                Source = "V = (1, 2)\n1 + V*",
                PrimaryLaw = ReceiverLaw.SPREAD_IS_SLOT_ONLY,
                ExpectedParseDiagnosticFragment = "scalar operand",
            },
            new()
            {
                Id = "add-spread-index-target",
                Family = "spread-placement",
                Source = "V = (1, 2)\nV*:0",
                PrimaryLaw = ReceiverLaw.SPREAD_IS_SLOT_ONLY,
                ExpectedParseDiagnosticFragment = "spread",
            },
            new()
            {
                Id = "add-spread-then-multiplication",
                Family = "spread-placement",
                Source = "V = (1, 2)\nV** 3",
                PrimaryLaw = ReceiverLaw.SPREAD_IS_SLOT_ONLY,
                ExpectedParseDiagnosticFragment = "scalar operand",
            },
            new()
            {
                Id = "add-spread-semicolon",
                Family = "spread-placement",
                Source = "V = (1, 2)\nV* ; 3",
                PrimaryLaw = ReceiverLaw.SPREAD_IS_SLOT_ONLY,
                ExpectedParseDiagnosticFragment = "Semicolon is not supported",
            },
        };

        // Arity-after-spread at fixed-arity boundaries, over two representative
        // multi-item shapes (error categories are shape-independent).
        foreach (var shapeId in new[] { "multi-seq", "multi-list" })
        {
            var shape = ShapesById[shapeId];
            cases.Add(new DiagnosticCase
            {
                Id = $"add-builtin-collection-spread--{shape.Id}",
                Family = "arity-after-spread",
                Source = $"V = {shape.Literal}\ncount(V*)",
                PrimaryLaw = ReceiverLaw.SPREAD_CONTRIBUTES_ITEMS,
                ExpectedErrorCategory = Arity,
            });
            cases.Add(new DiagnosticCase
            {
                Id = $"add-map-collection-spread--{shape.Id}",
                Family = "arity-after-spread",
                Source = $"IdF(x) = [x]\nV = {shape.Literal}\nmap(V*, IdF)",
                PrimaryLaw = ReceiverLaw.SPREAD_CONTRIBUTES_ITEMS,
                ExpectedErrorCategory = Arity,
            });
        }

        cases.Add(new DiagnosticCase
        {
            Id = "add-decon-undersupply",
            Family = "arity-after-spread",
            Source = "x, y, z = (1, 2)\n[x, y, z]",
            PrimaryLaw = ReceiverLaw.DECONSTRUCTION_OPENS_LONE_STRUCTURE,
            ExpectedErrorCategory = Arity,
        });
        cases.Add(new DiagnosticCase
        {
            Id = "add-loop-patterned-wrong-slots",
            Family = "arity-after-spread",
            Source = "PackStep((*h), p) = h*, p + 1\nPackStep.repeat(1, 7, 8, 9)",
            PrimaryLaw = ReceiverLaw.LOOP_PATTERNED_STEP_PACKS_TOPLEVEL_SPREAD,
            ExpectedErrorCategory = Arity,
        });

        return cases;
    }
}
