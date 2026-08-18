namespace KatLang.Tests.CountedMatrix;

/// <summary>
/// The multi-output CONSUMER a matrix case exercises: a language/runtime
/// construct where a producer's emitted top-level count (0, 1, 2, N) is
/// consumed, propagated, captured, collected, or re-counted. Each value names
/// one semantic boundary; the corpus must cover every member for every
/// <see cref="ProducerCardinality"/> (enforced by
/// <c>CountedMatrixTests.EveryConsumer_HasExplicitCardinalityCoverage</c>).
/// Adding a new multi-output consumer to the language means adding a member
/// here plus its rows in <see cref="CountedMatrixCorpus"/>.
/// </summary>
public enum CountedConsumer
{
    /// <summary>Root program output rows (Lean <c>evalOutputRowsPreparedCore</c>): a
    /// non-spread row is one visible slot (emitted clamps up to 1, so a `()` row is
    /// visible); a spread row contributes its true supply count; index projections and
    /// loop results re-emit multi-counts through a single row.</summary>
    RootOutputRows,

    /// <summary>Property definition bodies: body rows accumulate like output rows, and
    /// the NAMED reference is a value boundary (`Result.valueCount` re-count in Lean
    /// <c>evalCounted .resolve</c>), so N body rows become one sequence value.</summary>
    DefinitionBodyCapture,

    /// <summary>Written parentheses (`Expr.Capture`): ordered written slots, each
    /// non-spread slot exactly ONE value (a `()` slot stays visible), spread slots
    /// splice; the capture is a value boundary (Lean <c>evalCaptureValue</c> +
    /// <c>Result.valueCount</c>).</summary>
    CaptureBoundary,

    /// <summary>Zero-parameter brace algorithm in value position (Lean
    /// <c>evalCounted .algorithmExpr</c>): output demanded, then re-counted to one
    /// value.</summary>
    BraceValueBoundary,

    /// <summary>The spread marker `expr*` (Lean <c>evalSequenceSpreadCounted</c>):
    /// opens exactly one sequence OR list boundary; atoms/strings supply themselves;
    /// chained `**` is compositional, never recursive flattening.</summary>
    SpreadSupply,

    /// <summary>Shared call argument-slot assembly (Lean
    /// <c>collectVariadicCallItems</c>): every non-spread written slot reifies to ONE
    /// argument, every spread slot expands one value boundary BEFORE arity checking,
    /// for every callable shape.</summary>
    CallArgumentSlots,

    /// <summary>Fixed-arity parameter binding over the assembled slots: slot count
    /// must equal parameter count; each parameter binds one slot value.</summary>
    FixedArityBinding,

    /// <summary>Collecting parameter `*items` (Lean <c>collectSegment</c>): collects
    /// exactly the assigned argument slots as ONE exact list (never erased, count 1).</summary>
    CollectingParameter,

    /// <summary>Mixed prefix/collecting/suffix parameter lists (Lean
    /// <c>bindParameterPatternList</c>): fixed ends bind front/back, the collecting
    /// middle takes what remains (possibly zero).</summary>
    MixedParameterList,

    /// <summary>Collected-list forwarding: `Fwd(*items) = Target(items*)` re-supplies
    /// exactly the collected slots (Lean law <c>spreadItems (collectSegment xs) = xs</c>);
    /// unspread forwarding passes ONE list argument.</summary>
    CollectingForwarding,

    /// <summary>Assignment deconstruction `x, *y, z = RHS` (Lean
    /// <c>Result.structureItems?</c>): opens one lone sequence/list boundary of the
    /// shared RHS value and matches items element-by-element.</summary>
    DeconstructionBinding,

    /// <summary>Sequence-value parameter patterns `F((a, *b))`: open ONE received
    /// value through the same structure view; scalars use the one-item rule.</summary>
    SequenceValuePattern,

    /// <summary>Multi-clause conditional dispatch: clause selection happens AFTER
    /// spread expansion; each clause result is a value boundary (Lean
    /// <c>evalConditionalCallCounted</c> + <c>reCountValueBoundary</c>).</summary>
    ClauseFamilyDispatch,

    /// <summary>Ordinary lexical dot-call receiver: ONE leading argument segment; a
    /// WRITTEN group/brace receiver carries its raw row emission as segment supply, a
    /// NAMED receiver supplies `valueCount` items (zero for `()`); only a flat
    /// top-level collecting parameter allocated the segment consumes the supply (Lean
    /// <c>evalVariadicCallItemCounted</c> + <c>collectingSegmentCount?</c>).</summary>
    DotReceiverSegment,

    /// <summary>Fluent spread receiver `A*.F`: parse-time lowering to the lexical
    /// call `F(A*)` — the receiver is an item supply, not a segment.</summary>
    FluentSpreadReceiver,

    /// <summary>Indexing `:` (Lean <c>Result.select?</c>): the target opens through
    /// <c>projectionItems</c>; the selected element re-emits its projected item count
    /// (a selected list element stays one opaque list).</summary>
    IndexProjection,

    /// <summary>Post-binding builtin collection view (Lean
    /// <c>builtinCollectionItems</c>): the ONE bound collection argument opens one
    /// lone sequence/list boundary; any other value is a one-element collection;
    /// argument boundaries are never altered before binding.</summary>
    BuiltinCollectionView,

    /// <summary>Collection-producing builtins (Lean <c>makeCollectionListResult</c>):
    /// kept/projected items materialize as ONE exact list, emitted count always 1,
    /// single kept items never erased.</summary>
    CollectionBuiltinResult,

    /// <summary>Higher-order callback contracts: map/reduce callbacks must emit
    /// exactly one value (Lean <c>expectSingleValueWith</c>); filter predicates one
    /// atomic truth value; flat multi-parameter callbacks open sequence rows while
    /// list elements stay opaque; collecting callbacks keep the element as one slot.</summary>
    CallbackContract,

    /// <summary>`while`/`repeat` loop state (Lean <c>applyBuiltinCounted</c> loop
    /// arms): initial arguments are one slot each (spread args expand first), step
    /// output slots are the next state, and the loop RESULT emits
    /// <c>finalSlots.length</c> — a genuine multi-count boundary.</summary>
    LoopStateSlots,

    /// <summary>The `if` builtin: the chosen branch is observed at a value boundary
    /// (`Result.valueCount` re-count); the condition needs exactly one atomic truth
    /// value; spread arguments expand before the builtin arity check.</summary>
    IfBoundary,

    /// <summary>List literal `[...]` element slots (Lean
    /// <c>evalListLiteralCounted</c>): one exact element per non-spread slot (a `()`
    /// element stays), spread slots splice, result always one list value.</summary>
    ListLiteralSlots,

    /// <summary>Binary operator operand positions: value boundaries with the
    /// empty-sequence transparent-passthrough rule for non-equality operators.</summary>
    OperatorOperandBoundary,

    /// <summary>The higher-order algorithm channel: brace/named algorithms passed as
    /// arguments and invoked by the callee; capture suppresses callable identity.</summary>
    HigherOrderChannel,
}

/// <summary>
/// The producer-output cardinality axis a case exercises (how many outputs the
/// case's primary producer emits). <see cref="Combo"/> marks multi-producer
/// combination rows, which supplement — but do not satisfy — the required
/// 0/1/2/N coverage.
/// </summary>
public enum ProducerCardinality
{
    Zero,
    One,
    Two,
    Many,
    Combo,
}

/// <summary>How the producer's outputs reach the consumer.</summary>
public enum SupplyForm
{
    /// <summary>Multi-output written directly (rows / adjacent slots).</summary>
    WrittenRows,

    /// <summary>Through a named zero-parameter producer reference (a value boundary).</summary>
    NamedReference,

    /// <summary>Through an explicit spread marker `expr*`.</summary>
    SpreadMarker,

    /// <summary>Through an explicit `(...)` capture boundary.</summary>
    CaptureWrapped,

    /// <summary>Through a `{...}` zero-parameter brace algorithm boundary.</summary>
    BraceWrapped,

    /// <summary>A nesting-matrix case (inner/outer boundary combinations).</summary>
    Nested,
}

/// <summary>
/// One counted known-answer case. The expected answer is HAND-WRITTEN from the
/// Lean semantics (each case's <see cref="Rule"/> names the governing rule and
/// Lean anchor) — never recorded from observed implementation behavior.
/// Exactly one expectation field group is set:
/// <list type="bullet">
/// <item><see cref="ExpectedShape"/> + <see cref="ExpectedEmitted"/> — structural
/// cardinality skeleton (atoms erased to <c>#</c>, strings to <c>$</c>) plus the
/// root emitted count. The default counted-only assertion.</item>
/// <item><see cref="ExpectedRaw"/> + <see cref="ExpectedEmitted"/> — full neutral
/// raw structure (harness encoding). Used where the atom values ARE the semantic
/// counts (in-language count probes) or where order is the invariant under test
/// (order sentinels).</item>
/// <item><see cref="ExpectedErrorCategory"/> — the innermost evaluation error
/// category (harness/Lean shared taxonomy, e.g. "arity", "branch", "index").</item>
/// </list>
/// </summary>
public sealed record CountedMatrixCase
{
    public required string Id { get; init; }

    public required CountedConsumer Consumer { get; init; }

    public required ProducerCardinality Cardinality { get; init; }

    public required SupplyForm Form { get; init; }

    /// <summary>Complete standalone KatLang program ("\n" separators). Must parse cleanly.</summary>
    public required string Source { get; init; }

    /// <summary>One-line statement of the counted rule this case pins, with its Lean anchor.</summary>
    public required string Rule { get; init; }

    public string? ExpectedShape { get; init; }

    public string? ExpectedRaw { get; init; }

    public int? ExpectedEmitted { get; init; }

    public string? ExpectedErrorCategory { get; init; }

    public static CountedMatrixCase Shape(
        string id, CountedConsumer consumer, ProducerCardinality cardinality, SupplyForm form,
        string source, string expectedShape, int expectedEmitted, string rule)
        => new()
        {
            Id = id,
            Consumer = consumer,
            Cardinality = cardinality,
            Form = form,
            Source = source,
            ExpectedShape = expectedShape,
            ExpectedEmitted = expectedEmitted,
            Rule = rule,
        };

    public static CountedMatrixCase Raw(
        string id, CountedConsumer consumer, ProducerCardinality cardinality, SupplyForm form,
        string source, string expectedRaw, int expectedEmitted, string rule)
        => new()
        {
            Id = id,
            Consumer = consumer,
            Cardinality = cardinality,
            Form = form,
            Source = source,
            ExpectedRaw = expectedRaw,
            ExpectedEmitted = expectedEmitted,
            Rule = rule,
        };

    public static CountedMatrixCase Err(
        string id, CountedConsumer consumer, ProducerCardinality cardinality, SupplyForm form,
        string source, string expectedErrorCategory, string rule)
        => new()
        {
            Id = id,
            Consumer = consumer,
            Cardinality = cardinality,
            Form = form,
            Source = source,
            ExpectedErrorCategory = expectedErrorCategory,
            Rule = rule,
        };

    /// <summary>
    /// Structural cardinality skeleton of a result: atom → <c>#</c>, string →
    /// <c>$</c>, sequence → <c>S[...]</c>, list → <c>L[...]</c>. Erasing atom and
    /// string content keeps the assertion counted-only (slot counts and nesting
    /// boundaries) while staying precise about structure kind at every level.
    /// </summary>
    public static string ShapeOf(Result result) => result switch
    {
        Result.Atom => "#",
        Result.Str => "$",
        Result.SequenceValue g => "S[" + string.Join(", ", g.Items.Select(ShapeOf)) + "]",
        Result.ListValue l => "L[" + string.Join(", ", l.Items.Select(ShapeOf)) + "]",
        _ => "?",
    };
}
