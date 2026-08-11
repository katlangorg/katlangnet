using System.Globalization;

namespace KatLang.Tests.ArityDifferential;

/// <summary>
/// Test-only executable oracle for the Core Arity Algebra.
///
/// This is a deliberately small, independent mirror of the Lean extraction in
/// <c>lean/CoreArityAlgebra.lean</c> (definitions) and the bridge fragments of
/// <c>lean/KatLangArityLaws.lean</c> that the differential campaign needs. It
/// references NOTHING from <c>src/KatLang</c>: expectations computed here are
/// compared against production behavior only through the neutral observation
/// encoding shared with the Lean guards (<c>S[..]</c>/<c>L[..]</c>/atom text),
/// so the runtime and the oracle cannot share helper code by construction.
///
/// Correspondence table (each member's doc comment repeats its anchor):
///
/// <code>
/// OracleVal.Atom / Seq / List      CoreArityAlgebra.Val (atom | seq | list)
/// Items                            CoreArityAlgebra.items        (= Result.spreadItems)
/// Normalize                        CoreArityAlgebra.normalize    (= Result.normalize)
/// Capture                          CoreArityAlgebra.capture      (= normalize ∘ sequenceValue)
/// Collect                          CoreArityAlgebra.collect      (= collectSegment / Result.listValue)
/// StructureItems                   CoreArityAlgebra.structureItems? (= Result.structureItems?)
/// OpenLoneStructure                CoreArityAlgebra.openLoneStructure
/// IsLoneStructure                  CoreArityAlgebra.loneStructure
/// BindPats / BindArgs              CoreArityAlgebra.bindPats / bindArgs
/// BindDeconstruct                  CoreArityAlgebra.bindDeconstruct
/// SpreadSupply (stars >= 1)        items, then (stars-1) × (items ∘ capture)
///                                  — CoreArityAlgebraProofs.repeated_spread_cardinality,
///                                    KatLang.lean evalSequenceSpreadCounted
/// ValueCount                       KatLang.lean Result.valueCount (KatLangArityLaws.valueCount_le_one)
/// RootNonSpreadRow                 KatLang.lean evalAlgOutputCountedCore non-spread slot rule
///                                  (a non-spread output row is one visible slot even when empty)
/// </code>
///
/// The oracle models only the Int-atom / sequence / list fragment the campaign
/// exercises. It is NOT a second interpreter: no expressions, no environments,
/// no builtins — only the supply/value operations of the algebra.
/// </summary>
public abstract class OracleVal : IEquatable<OracleVal>
{
    private protected OracleVal(string neutral) => Neutral = neutral;

    /// <summary>
    /// Rendering in the neutral observation encoding shared with the Lean
    /// guards and <c>SemanticExplorerHarness.Neutral</c>: atom → invariant
    /// integer text, sequence → <c>S[a, b]</c>, exact list → <c>L[a, b]</c>.
    /// The encoding is injective on this fragment, so it doubles as the
    /// structural-equality key.
    /// </summary>
    public string Neutral { get; }

    public sealed class AtomVal : OracleVal
    {
        public AtomVal(int value) : base(value.ToString(CultureInfo.InvariantCulture)) => Value = value;
        public int Value { get; }
    }

    public sealed class SeqVal : OracleVal
    {
        public SeqVal(IReadOnlyList<OracleVal> items)
            : base($"S[{string.Join(", ", items.Select(i => i.Neutral))}]") => Items = items;
        public IReadOnlyList<OracleVal> Items { get; }
    }

    public sealed class ListVal : OracleVal
    {
        public ListVal(IReadOnlyList<OracleVal> items)
            : base($"L[{string.Join(", ", items.Select(i => i.Neutral))}]") => Items = items;
        public IReadOnlyList<OracleVal> Items { get; }
    }

    public static OracleVal Atom(int value) => new AtomVal(value);
    public static OracleVal Seq(params OracleVal[] items) => new SeqVal(items);
    public static OracleVal Seq(IReadOnlyList<OracleVal> items) => new SeqVal(items);
    public static OracleVal List(params OracleVal[] items) => new ListVal(items);
    public static OracleVal List(IReadOnlyList<OracleVal> items) => new ListVal(items);

    public bool Equals(OracleVal? other) => other is not null && Neutral == other.Neutral;
    public override bool Equals(object? obj) => obj is OracleVal other && Equals(other);
    public override int GetHashCode() => Neutral.GetHashCode(StringComparison.Ordinal);
    public override string ToString() => Neutral;
}

/// <summary>One fixed or collecting binding pattern (CoreArityAlgebra.Pat).</summary>
/// <param name="Name">Binding name (Pat.key).</param>
/// <param name="Collecting">True for a collecting binding (Pat.collecting), false for a fixed capture (Pat.name).</param>
public sealed record OraclePat(string Name, bool Collecting)
{
    public static OraclePat Fixed(string name) => new(name, false);
    public static OraclePat Collect(string name) => new(name, true);
}

public static class AlgebraOracle
{
    /// <summary>
    /// Lean: <c>CoreArityAlgebra.items</c> (full model: <c>Result.spreadItems</c>).
    /// The total item view of a value — the formal meaning of the surface
    /// spread marker <c>expr*</c>. Opens exactly one sequence OR list
    /// boundary; an atom supplies itself as one item. Never recursive.
    /// (Theorems: items_seq, items_list, items_eq_nil_iff.)
    /// </summary>
    public static IReadOnlyList<OracleVal> Items(OracleVal value) => value switch
    {
        OracleVal.SeqVal seq => seq.Items,
        OracleVal.ListVal list => list.Items,
        _ => [value],
    };

    /// <summary>
    /// Lean: <c>CoreArityAlgebra.normalize</c> (full model: <c>Result.normalize</c>).
    /// Recursively erases redundant singleton SEQUENCE boundaries; list
    /// boundaries never collapse, but list elements normalize.
    /// (Theorems: normalize_singleton, normalize_list_exact, normalize_idempotent.)
    /// </summary>
    public static OracleVal Normalize(OracleVal value)
    {
        switch (value)
        {
            case OracleVal.SeqVal seq:
                var normalized = seq.Items.Select(Normalize).ToArray();
                return normalized.Length == 1 ? normalized[0] : OracleVal.Seq(normalized);
            case OracleVal.ListVal list:
                return OracleVal.List(list.Items.Select(Normalize).ToArray());
            default:
                return value;
        }
    }

    /// <summary>
    /// Lean: <c>CoreArityAlgebra.capture</c> = <c>normalize (Val.seq xs)</c>
    /// (full model: <c>Result.normalize (Result.sequenceValue xs)</c>,
    /// KatLangArityLaws <c>captureForArityLaw</c>). The canonicalizing
    /// ORDINARY value-capture boundary: zero items capture as <c>()</c>, one
    /// item captures as itself (singleton erasure), many as one sequence value.
    /// (Theorems: capture_empty, capture_singleton, capture_pair.)
    /// </summary>
    public static OracleVal Capture(IReadOnlyList<OracleVal> supply) =>
        Normalize(OracleVal.Seq(supply));

    /// <summary>
    /// Lean: <c>CoreArityAlgebra.collect</c> = <c>Val.list xs</c> (full model:
    /// <c>collectSegment</c> / <c>Result.listValue</c>). Exact segment
    /// collection — the collecting-binding operation. Never erases a
    /// singleton, never canonicalizes the boundary.
    /// (Theorems: collect_is_list, collect_singleton_ne_item, items_collect.)
    /// </summary>
    public static OracleVal Collect(IReadOnlyList<OracleVal> supply) => OracleVal.List(supply);

    /// <summary>
    /// Lean: <c>CoreArityAlgebra.structureItems?</c> (full model:
    /// <c>Result.structureItems?</c>). The deconstruction-openable structure
    /// view: a sequence or list value projects to its items; an atom is not an
    /// openable structure.
    /// </summary>
    public static IReadOnlyList<OracleVal>? StructureItems(OracleVal value) => value switch
    {
        OracleVal.SeqVal seq => seq.Items,
        OracleVal.ListVal list => list.Items,
        _ => null,
    };

    /// <summary>
    /// Lean: <c>CoreArityAlgebra.openLoneStructure</c>. Deconstruction-specific
    /// supply preparation: a supply consisting of exactly one openable
    /// structure is opened one boundary; every other supply is unchanged.
    /// (Theorems: openLoneStructure_singleSeq/_singleList/_singleAtom,
    /// openLoneStructure_singleton = items on one-value supplies.)
    /// </summary>
    public static IReadOnlyList<OracleVal> OpenLoneStructure(IReadOnlyList<OracleVal> supply) =>
        supply.Count == 1 ? StructureItems(supply[0]) ?? supply : supply;

    /// <summary>Lean: <c>CoreArityAlgebra.loneStructure</c> — exactly the supplies OpenLoneStructure rewrites.</summary>
    public static bool IsLoneStructure(IReadOnlyList<OracleVal> supply) =>
        supply.Count == 1 && StructureItems(supply[0]) is not null;

    /// <summary>
    /// Lean: <c>CoreArityAlgebra.bindPats</c> — the shared fixed/collecting
    /// binder. Zero collecting patterns: exact-length fixed zip. One
    /// collecting pattern: fixed front/back captures with the collecting
    /// binding bound to <c>Collect</c> of exactly the middle supply
    /// (bindPats_collect_exact). Returns null on arity failure (or on more
    /// than one collecting pattern, which surface KatLang rejects earlier).
    /// </summary>
    public static IReadOnlyList<(string Name, OracleVal Value)>? BindPats(
        IReadOnlyList<OraclePat> patterns, IReadOnlyList<OracleVal> supply)
    {
        var collectingCount = patterns.Count(p => p.Collecting);
        if (collectingCount == 0)
        {
            if (patterns.Count != supply.Count)
                return null;
            return patterns.Select((p, i) => (p.Name, supply[i])).ToArray();
        }

        if (collectingCount > 1)
            return null;

        var index = patterns.ToList().FindIndex(p => p.Collecting);
        if (supply.Count < patterns.Count - 1)
            return null;

        var front = patterns.Take(index).ToArray();
        var back = patterns.Skip(index + 1).ToArray();
        var frontVals = supply.Take(index).ToArray();
        var backVals = supply.Skip(supply.Count - back.Length).ToArray();
        var midVals = supply.Skip(index).Take(supply.Count - back.Length - index).ToArray();

        return front.Select((p, i) => (p.Name, frontVals[i]))
            .Append((patterns[index].Name, Collect(midVals)))
            .Concat(back.Select((p, i) => (p.Name, backVals[i])))
            .ToArray();
    }

    /// <summary>Lean: <c>CoreArityAlgebra.bindArgs</c> — function-call binding consumes the supply exactly as supplied.</summary>
    public static IReadOnlyList<(string Name, OracleVal Value)>? BindArgs(
        IReadOnlyList<OraclePat> patterns, IReadOnlyList<OracleVal> supply) => BindPats(patterns, supply);

    /// <summary>
    /// Lean: <c>CoreArityAlgebra.bindDeconstruct</c> — assignment
    /// deconstruction applies lone-structure opening before the shared binder.
    /// (Theorems: deconstruct_fixed_single_sequence_opens,
    /// deconstruct_fixed_single_list_opens, receivers_agree_outside_lone_structure.)
    /// </summary>
    public static IReadOnlyList<(string Name, OracleVal Value)>? BindDeconstruct(
        IReadOnlyList<OraclePat> patterns, IReadOnlyList<OracleVal> supply) =>
        BindPats(patterns, OpenLoneStructure(supply));

    /// <summary>
    /// The supply of a written spread chain with <paramref name="stars"/>
    /// attached postfix markers on a stored canonical value: the first star is
    /// <c>items</c>, and each further star crosses one ordinary capture
    /// boundary — <c>items ∘ capture</c> per extra layer.
    ///
    /// Lean: <c>CoreArityAlgebraProofs.repeated_spread_cardinality</c> (both
    /// spellings <c>value**</c> and <c>(value*)*</c> mean
    /// <c>items (capture (items v))</c>); authoritative evaluator:
    /// <c>KatLang.lean evalSequenceSpreadCounted</c> (operand evaluated once,
    /// then <c>spreadItems ∘ (normalize ∘ sequenceValue)</c> per extra layer);
    /// C#: <c>Evaluator.EvalSequenceSpreadCounted</c>.
    /// </summary>
    public static IReadOnlyList<OracleVal> SpreadSupply(OracleVal value, int stars)
    {
        if (stars < 1)
            throw new ArgumentOutOfRangeException(nameof(stars), "A spread chain has at least one star.");
        var supply = Items(value);
        for (var layer = 1; layer < stars; layer++)
            supply = Items(Capture(supply));
        return supply;
    }

    /// <summary>
    /// Lean: <c>Result.valueCount</c> (KatLangArityLaws
    /// <c>valueCount_le_one</c>, <c>valueCount_empty_list</c>): the structural
    /// emitted count of ONE value — 0 for the empty sequence value, otherwise
    /// 1 (the empty list <c>[]</c> is a visible exact value). This is what
    /// every property/call/builtin RESULT boundary re-counts to
    /// (<c>reCountValueBoundary_recounts</c>).
    /// </summary>
    public static int ValueCount(OracleVal value) =>
        value is OracleVal.SeqVal { Items.Count: 0 } ? 0 : 1;

    /// <summary>
    /// Root-row observation of a NON-SPREAD output row carrying one value with
    /// the given boundary count: the row is always one visible slot, even when
    /// the value is the invisible-count empty sequence (<c>()</c> stays a
    /// visible row at root). Lean: <c>evalAlgOutputCountedCore</c> — “A
    /// non-spread output is always one visible slot … only an explicit spread
    /// can contribute zero items.”
    /// </summary>
    public static (OracleVal Value, int Emitted) RootNonSpreadRow(OracleVal value, int boundaryCount) =>
        (value, boundaryCount == 0 ? 1 : boundaryCount);

    /// <summary>
    /// The evaluated top-level supply of an injected lexical dot-call receiver
    /// segment holding a STORED value: a named property receiver evaluates at
    /// its value boundary, so the segment supply is <see cref="ValueCount"/>
    /// items — zero items for the empty sequence value, otherwise the one
    /// stored value. (A WRITTEN inline group/block receiver instead emits its
    /// raw row supply; matrix cases model that supply directly from the
    /// written rows.) This is what a flat top-level collecting parameter
    /// consumes when the receiver segment is allocated to it
    /// (COLLECTOR_CONSUMES_ALLOCATED_SEGMENT_SUPPLY); fixed parameters bind
    /// the segment's one value and ignore this view.
    /// Lean: <c>collectVariadicCallItems</c> receiver segment
    /// (<c>collectingSegmentCount?</c>) consumed by
    /// <c>bindParameterPatternList</c> via <c>countedTopLevelValues</c>;
    /// C#: <c>ParameterPatternInput.CollectingSegmentEmittedCount</c>.
    /// </summary>
    public static IReadOnlyList<OracleVal> StoredReceiverSegmentSupply(OracleVal value) =>
        ValueCount(value) == 0 ? [] : [value];

    /// <summary>Neutral observation string for a successful single-row program, matching <c>ExplorerObservation.Neutral</c>.</summary>
    public static string OkNeutral(OracleVal value, int emitted) => $"ok raw={value.Neutral} n={emitted}";

    /// <summary>Neutral observation string for an evaluation failure, matching <c>ExplorerObservation.Neutral</c>.</summary>
    public static string ErrNeutral(string category) => $"err {category}";
}
