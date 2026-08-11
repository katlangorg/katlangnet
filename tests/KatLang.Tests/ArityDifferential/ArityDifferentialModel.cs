namespace KatLang.Tests.ArityDifferential;

/// <summary>Receiver dimension of the differential matrix.</summary>
public enum ReceiverKind
{
    DirectCall,
    DottedCall,
    Assignment,
    Callback,
    LoopStep,
    Property,
}

/// <summary>
/// Transformation/binding form observed by a case: which of the three
/// receiver-purpose operations of the algebra the receiver applies to the
/// supplied items (capture : Supply → Value, collect : Supply → ListValue,
/// spread : Value → Supply as the observed operation itself).
/// </summary>
public enum BindingForm
{
    Capture,
    Collect,
    Spread,
}

/// <summary>
/// Number of written postfix spread markers in the case's observed dataflow
/// chain. Repeated means two or more chained markers — the stacked spelling
/// <c>V**</c>, the grouped spelling <c>(V*)*</c>, or a cross-receiver chain
/// (spread, capture/collect at a boundary, spread again).
/// </summary>
public enum SpreadMultiplicity
{
    Zero = 0,
    One = 1,
    Repeated = 2,
}

/// <summary>
/// Primary receiver laws. Every generated executable case names exactly ONE
/// law that justifies its expected outcome; supporting algebra steps are
/// recorded in the case's trace. <see cref="ReceiverLaws.LeanReference"/> maps
/// each law to the Lean definition/theorem that pins it.
/// </summary>
public enum ReceiverLaw
{
    /// <summary>Every non-spread written slot is exactly one argument value; calls never open stored structure.</summary>
    CALL_PRESERVES_WRITTEN_BOUNDARIES,

    /// <summary>An explicit spread contributes items(value) as ordinary slots of the surrounding supply, before any arity check.</summary>
    SPREAD_CONTRIBUTES_ITEMS,

    /// <summary>Each extra written star crosses one ordinary capture boundary: value** ≡ (value*)* ≡ items(capture(items v)).</summary>
    REPEATED_SPREAD_CAPTURE_COMPOSITION,

    /// <summary>Ordinary value capture canonicalizes the supply: () for zero items, singleton erasure, one sequence value otherwise.</summary>
    CAPTURE_CANONICALIZES_SUPPLY,

    /// <summary>A collecting binding collects exactly the assigned supply as one exact immutable list — no erasure, no canonicalization.</summary>
    COLLECT_PRESERVES_EXACT_SUPPLY,

    /// <summary>Mixed fixed/collecting parameter lists bind front and back fixed captures and collect exactly the middle segment.</summary>
    COLLECT_SEGMENT_ALLOCATION,

    /// <summary>
    /// a.F(b, …) injects a as ONE leading argument segment of F(a, b, …):
    /// same allocation, same diagnostics, receiver evaluated once. It
    /// coincides exactly with the written direct call except where
    /// <see cref="COLLECTOR_CONSUMES_ALLOCATED_SEGMENT_SUPPLY"/> applies —
    /// a written direct-call slot always reifies to one value, while a
    /// receiver segment also carries its evaluated top-level supply.
    /// </summary>
    DOTTED_CALL_EQUALS_DIRECT_REWRITE,

    /// <summary>A spread receiver keeps the supply: operand*.F lowers to the lexical call F(operand*).</summary>
    FLUENT_SPREAD_RECEIVER_IS_LEXICAL_CALL,

    /// <summary>Parentheses around a spread are the capture receiver: (A*).F dot-calls F on ONE captured sequence value.</summary>
    GROUPED_SPREAD_RECEIVER_CAPTURES,

    /// <summary>
    /// The general dot-receiver segment rule: a lexical dot-call receiver is
    /// ONE leading segment for arity checking and fixed prefix/suffix
    /// allocation (its item count never satisfies arity), and a flat
    /// top-level collecting parameter that is allocated the segment consumes
    /// the segment's evaluated top-level supply — one level, never recursive.
    /// A fixed parameter allocated the segment binds its one captured value.
    /// Receiver assembly never inspects the callee or recognizes a spelling;
    /// a written group's supply is its raw row emission, a stored property's
    /// supply is its value-boundary count (zero items for `()`, else one).
    /// </summary>
    COLLECTOR_CONSUMES_ALLOCATED_SEGMENT_SUPPLY,

    /// <summary>Assignment deconstruction opens one lone sequence/list boundary of its single shared RHS value before matching.</summary>
    DECONSTRUCTION_OPENS_LONE_STRUCTURE,

    /// <summary>A written spread on a deconstruction RHS first passes the ordinary capture boundary; singleton capture can expose one more boundary.</summary>
    DECONSTRUCTION_RHS_CAPTURE_BOUNDARY,

    /// <summary>A property observes its body's output supply as ONE value; access re-counts to the structural value count.</summary>
    PROPERTY_REIFIES_OUTPUT,

    /// <summary>Property-style access A and explicit call A() observe the same value (the cache distinction is behavioral only).</summary>
    PROPERTY_CALL_EQUIVALENT_VALUE,

    /// <summary>Each map/filter iterated element is supplied to the callback as one invocation value; a unary callee binds it whole.</summary>
    CALLBACK_ELEMENT_IS_ONE_INVOCATION_VALUE,

    /// <summary>A single-collecting callback collects the one iterated element as ONE collected slot.</summary>
    CALLBACK_COLLECTING_COLLECTS_ONE_SLOT,

    /// <summary>A multi-parameter flat callee opens a lone SEQUENCE element into row slots; exact-list elements stay opaque and arity-error.</summary>
    CALLBACK_FLAT_ROW_CONVENTION,

    /// <summary>A nested sequence-value parameter pattern opens exactly one boundary of a sequence OR list element.</summary>
    CALLBACK_NESTED_PATTERN_OPENS_ONE_BOUNDARY,

    /// <summary>The reduce initial accumulator is one written value slot, reified at the value boundary before reduction.</summary>
    REDUCE_INITIAL_IS_WRITTEN_VALUE_SLOT,

    /// <summary>Each explicit loop init argument is one initial state slot; spread supplies slots like every written slot context.</summary>
    LOOP_INIT_ARGS_ARE_WRITTEN_SLOTS,

    /// <summary>Loop state is a multi-slot supply, not a value boundary: flat step output spread re-spreads into separate state slots.</summary>
    LOOP_STATE_SLOTS_ARE_NOT_A_VALUE_BOUNDARY,

    /// <summary>In a sequence-value-patterned step's output, a top-level spread contributes ONE packed next-state slot (zero-item spread contributes none).</summary>
    LOOP_PATTERNED_STEP_PACKS_TOPLEVEL_SPREAD,

    /// <summary>The while step's last output slot is the continue flag; remaining slots are the committed state (pre-check semantics).</summary>
    WHILE_LAST_SLOT_IS_CONTINUE_FLAG,

    /// <summary>spread(collect(xs)) = xs: collecting-parameter forwarding is ordinary list spread.</summary>
    COLLECT_SPREAD_ROUND_TRIP,

    /// <summary>capture and collect are intentionally different operations on every supply (kind and singleton behavior differ).</summary>
    CAPTURE_AND_COLLECT_ARE_DIFFERENT_OPERATIONS,

    /// <summary>The prefix collect marker exists only in binding positions and must be directly attached; misuse is a targeted parse error.</summary>
    COLLECT_MARKER_IS_BINDING_ONLY,

    /// <summary>A spread expression is legal only as a whole expression-list slot, spread operand, or fluent receiver; other positions are targeted parse errors.</summary>
    SPREAD_IS_SLOT_ONLY,
}

public static class ReceiverLaws
{
    /// <summary>Lean definition/theorem anchors for every law (formal artifact names, for failure output and the design doc).</summary>
    public static readonly IReadOnlyDictionary<ReceiverLaw, string> LeanReference = new Dictionary<ReceiverLaw, string>
    {
        [ReceiverLaw.CALL_PRESERVES_WRITTEN_BOUNDARIES] =
            "CoreArityAlgebraProofs: args_fixed_single_sequence_rejected / args_fixed_single_list_rejected; KatLangArityLaws: call_fixed_single_sequence_rejected, call_fixed_single_list_rejected, call_variadic_single_list_preserved",
        [ReceiverLaw.SPREAD_CONTRIBUTES_ITEMS] =
            "CoreArityAlgebra: items (spread : Value -> Supply); KatLangArityLaws: spreadItems_sequenceValue, spreadItems_listValue, spreadItems_empty_list",
        [ReceiverLaw.REPEATED_SPREAD_CAPTURE_COMPOSITION] =
            "CoreArityAlgebraProofs: repeated_spread_cardinality, repeated_spread_fixed_iff, repeated_spread_multi_item_fixed_point, repeated_spread_not_recursive_flattening; CoreTests: stackedSpreadAgreesWithGroupedCompositionalForm, stackedSpreadMultiItemFixedPoint, stackedSpreadMixedSupplyStaysUnopened",
        [ReceiverLaw.CAPTURE_CANONICALIZES_SUPPLY] =
            "CoreArityAlgebra: capture; CoreArityAlgebraProofs: capture_singleton, capture_items_of_canonical, capture_items_of_list; KatLangArityLaws: capture_spreadItems_of_canonical_non_list, capture_spreadItems_of_list",
        [ReceiverLaw.COLLECT_PRESERVES_EXACT_SUPPLY] =
            "CoreArityAlgebra: collect; CoreArityAlgebraProofs: collect_is_list, collect_singleton, variadic_collect_value_grouped/_spread; KatLangArityLaws: collectSegment_eq_listValue, collectSegment_singleton, bindParameterPatternList_single_collecting_binds_collect",
        [ReceiverLaw.COLLECT_SEGMENT_ALLOCATION] =
            "CoreArityAlgebraProofs: bindPats_collect_exact, bindPats_middle_collecting; KatLangArityLaws: bindParameterPatternList_middle_collecting_binds_collect (leading/trailing twins)",
        [ReceiverLaw.DOTTED_CALL_EQUALS_DIRECT_REWRITE] =
            "AGENTS.md dotted-call equivalence rule; KatLang.lean evalDotCall* receiver-as-one-leading-argument; C# DottedReceiverEvaluationTests (receiver charged once)",
        [ReceiverLaw.FLUENT_SPREAD_RECEIVER_IS_LEXICAL_CALL] =
            "AGENTS.md: operand*.Member(...) lowers to Member(operand*, ...); C# parser fluent dot-chain lowering (spread receiver becomes the leading argument slot)",
        [ReceiverLaw.GROUPED_SPREAD_RECEIVER_CAPTURES] =
            "CoreArityAlgebra: capture; tutorial spec spread-capture-count ((A*).count = 3); KatLangArityLaws: capture_spreadItems_of_list",
        [ReceiverLaw.COLLECTOR_CONSUMES_ALLOCATED_SEGMENT_SUPPLY] =
            "KatLang.lean collectVariadicCallItems (injectedDotReceiverLeading segment keeps collectingSegmentCount?) + "
            + "bindParameterPatternList collectValues (countedTopLevelValues supply expansion at the collecting position); "
            + "KatLangArityLaws: dot_receiver_segment_supply_consumed / dot_receiver_segment_fixed_binds_value / dot_receiver_segment_count_never_satisfies_arity; "
            + "C# Evaluator.BuildCallArgumentInputs (ParameterPatternInput.CollectingSegmentEmittedCount) + BindParameterPatternList; "
            + "StarSyntaxTests.SpreadInsideAGroup_IsACaptureReceiver_NotAFluentSupply (grouped and fluent spread receivers coincide on a collector by the general rule)",
        [ReceiverLaw.DECONSTRUCTION_OPENS_LONE_STRUCTURE] =
            "CoreArityAlgebra: openLoneStructure/bindDeconstruct; CoreArityAlgebraProofs: deconstruct_fixed_single_sequence_opens, deconstruct_singleton_eq_args_items; KatLangArityLaws: deconstruct_fixed_single_list_opens, deconstruct_collecting_single_list_opens",
        [ReceiverLaw.DECONSTRUCTION_RHS_CAPTURE_BOUNDARY] =
            "CoreArityAlgebraProofs: deconstruct_spread_capture_can_open_further (bare [(1,2)] fails two fixed targets; spread RHS captures then opens)",
        [ReceiverLaw.PROPERTY_REIFIES_OUTPUT] =
            "KatLang.lean reCountValueBoundary at zero-arg property access; KatLangArityLaws: reCountValueBoundary_recounts, valueCount_le_one; LanguageSpec case property-value-boundary",
        [ReceiverLaw.PROPERTY_CALL_EQUIVALENT_VALUE] =
            "AGENTS.md A vs A() cache rule (same value, cache bypass only); C# ZeroArgPropertyResultCacheTests.ExplicitZeroArgCallBypassesCache",
        [ReceiverLaw.CALLBACK_ELEMENT_IS_ONE_INVOCATION_VALUE] =
            "KatLang.lean countedSequenceCallbackItem (Result.projectSelectedContent); tutorial map contract (item behaves like S:i, nested values stay intact)",
        [ReceiverLaw.CALLBACK_COLLECTING_COLLECTS_ONE_SLOT] =
            "KatLang.lean bindCountedCallbackParameterPatternList (lone element stays one collected slot); sequence-boundary audit: [7].map(Collect) collects items = [7]",
        [ReceiverLaw.CALLBACK_FLAT_ROW_CONVENTION] =
            "KatLang.lean bindCountedCallbackParams + unpackArgs (final-arg unpack; lists stay one item); AGENTS.md flat-callback row convention",
        [ReceiverLaw.CALLBACK_NESTED_PATTERN_OPENS_ONE_BOUNDARY] =
            "KatLang.lean bindCountedParameterPattern .sequenceValue branch (Result.structureItems? with lone-item fallback)",
        [ReceiverLaw.REDUCE_INITIAL_IS_WRITTEN_VALUE_SLOT] =
            "KatLang.lean reduceLoop (reCountValueBoundary initOut); AGENTS.md written-slot reification incl. reduce initial accumulator",
        [ReceiverLaw.LOOP_INIT_ARGS_ARE_WRITTEN_SLOTS] =
            "KatLang.lean evalInitialLoopStateSlots (each explicit init argument is one initial state slot); tutorial repeat/while init-slot rule",
        [ReceiverLaw.LOOP_STATE_SLOTS_ARE_NOT_A_VALUE_BOUNDARY] =
            "KatLang.lean evalAlgOutputSlots (flat mode expands spread rows into state slots) + loopStateResult; AGENTS.md non-value-boundary list",
        [ReceiverLaw.LOOP_PATTERNED_STEP_PACKS_TOPLEVEL_SPREAD] =
            "KatLang.lean evalAlgOutputSlots preserveSequenceSpreadExpressionBoundaries branch; C# ShouldPreserveLoopStepSequenceSpreadExpressionBoundaries; tutorial loop-step packed-slot exception",
        [ReceiverLaw.WHILE_LAST_SLOT_IS_CONTINUE_FLAG] =
            "KatLang.lean splitContSlots; tutorial while pre-check semantics",
        [ReceiverLaw.COLLECT_SPREAD_ROUND_TRIP] =
            "CoreArityAlgebraProofs: items_collect (spread ∘ collect = id); KatLangArityLaws: spreadItems_collectSegment",
        [ReceiverLaw.CAPTURE_AND_COLLECT_ARE_DIFFERENT_OPERATIONS] =
            "CoreArityAlgebraProofs: collect_singleton_ne_item, collect_singleton_atom_ne_capture; KatLangArityLaws: capture_and_collect_differ_on_pairs, collectSegment_singleton_ne_item",
        [ReceiverLaw.COLLECT_MARKER_IS_BINDING_ONLY] =
            "AGENTS.md star-role rule (prefix marker binding-only, exact attachment); C# Parser targeted collect-marker diagnostics",
        [ReceiverLaw.SPREAD_IS_SLOT_ONLY] =
            "AGENTS.md spread placement rule; C# Parser MisplacedSpreadDiagnostic / SpreadSelectionDiagnostic / semicolon diagnostic",
    };
}

/// <summary>One representative operand value: a stored canonical KatLang value with its algebra counterpart.</summary>
/// <param name="Id">Stable kebab-case shape id.</param>
/// <param name="Literal">KatLang source literal producing the stored value (assigned to a property).</param>
/// <param name="Value">The canonical oracle value the literal stores.</param>
/// <param name="Description">Why this representative is in the catalog.</param>
public sealed record ValueShape(string Id, string Literal, OracleVal Value, string Description);

/// <summary>Expected outcome of a generated case, in the shared neutral encoding.</summary>
public sealed record ExpectedObservation
{
    /// <summary>"ok raw=... n=..." or "err CATEGORY" (SemanticExplorerHarness taxonomy).</summary>
    public required string Neutral { get; init; }

    public bool IsError => Neutral.StartsWith("err ", StringComparison.Ordinal);
}

/// <summary>One generated matrix case: a complete program plus its oracle-computed expectation.</summary>
public sealed record DifferentialCase
{
    public required string Id { get; init; }
    public required ReceiverKind Receiver { get; init; }
    public required BindingForm Form { get; init; }
    public required string ShapeId { get; init; }
    public required SpreadMultiplicity Multiplicity { get; init; }
    public required string Source { get; init; }
    public required ReceiverLaw PrimaryLaw { get; init; }
    public required ExpectedObservation Expected { get; init; }

    /// <summary>Algebra steps that produced the expectation (oracle operations with intermediate neutrals).</summary>
    public required IReadOnlyList<string> AlgebraTrace { get; init; }

    public string? Notes { get; init; }
}

/// <summary>
/// One relational case: two complete programs the formal model says must agree
/// (or must differ), plus oracle-computed absolute expectations for each side.
/// </summary>
public sealed record RelationalCase
{
    public required string Id { get; init; }
    public required string Family { get; init; }
    public required string ShapeId { get; init; }
    public required SpreadMultiplicity Multiplicity { get; init; }
    public required string LeftSource { get; init; }
    public required string RightSource { get; init; }
    public required bool ExpectAgreement { get; init; }
    public required ReceiverLaw PrimaryLaw { get; init; }
    public required ExpectedObservation ExpectedLeft { get; init; }
    public required ExpectedObservation ExpectedRight { get; init; }
    public required IReadOnlyList<string> AlgebraTrace { get; init; }
}

/// <summary>One generated diagnostic case: a program that must be rejected, with the stable rejection identity.</summary>
public sealed record DiagnosticCase
{
    public required string Id { get; init; }
    public required string Family { get; init; }
    public required string Source { get; init; }
    public required ReceiverLaw PrimaryLaw { get; init; }

    /// <summary>Non-null for parse-level rejections: a stable fragment of the targeted diagnostic message.</summary>
    public string? ExpectedParseDiagnosticFragment { get; init; }

    /// <summary>Non-null for evaluation-level rejections: the shared harness/Lean error category.</summary>
    public string? ExpectedErrorCategory { get; init; }
}

/// <summary>One (receiver, form, shape, multiplicity) cell excluded from the executable matrix, with its reason.</summary>
public sealed record ExcludedCombination(
    ReceiverKind Receiver,
    BindingForm Form,
    string ShapeId,
    SpreadMultiplicity Multiplicity,
    string Reason);
