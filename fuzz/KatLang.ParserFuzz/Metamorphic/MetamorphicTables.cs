using System.Collections.Immutable;
using System.Globalization;

namespace KatLang.ParserFuzz;

/// <summary>How a trusted collection builtin's arguments continue after the receiver.</summary>
internal enum MetamorphicSuffixKind
{
    /// <summary>`F(receiver)` / `receiver.F` — the zero-suffix extension form.</summary>
    None,

    /// <summary>`take`/`skip`: one whole-number control argument.</summary>
    WholeNumber,

    /// <summary>`contains`: one ordinary value argument.</summary>
    Value,

    /// <summary>`map`/`filter`: one callback invoked with ONE value per element.</summary>
    Callback1,

    /// <summary>`reduce`: one callback invoked with TWO values, plus an initial accumulator.</summary>
    Callback2Initial,
}

/// <summary>What a trusted builtin returns, used for fingerprint features and chain construction.</summary>
internal enum MetamorphicResultKind
{
    Scalar,
    Collection,
}

/// <summary>One trusted collection builtin: a callable whose FIRST fixed parameter is the receiver.</summary>
/// <param name="CallbackArity">
/// The arity at which this builtin may itself be supplied as a CALLBACK, or 0 when it is
/// excluded from that role. A builtin can only serve a consumer that supplies exactly its fixed
/// arity, so this always equals the production fixed arity — except for the higher-order
/// builtins (<c>map</c>, <c>filter</c>, <c>reduce</c>), which take a callback themselves and are
/// deliberately excluded: nesting them as callbacks obscures what a pair is testing without
/// exercising any additional callback machinery.
/// </param>
internal sealed record MetamorphicBuiltin(
    string Name,
    MetamorphicSuffixKind SuffixKind,
    MetamorphicResultKind ResultKind,
    int CallbackArity)
{
    /// <summary>True when this builtin may itself be supplied as a callback of the given arity.</summary>
    public bool IsCallbackOfArity(int arity) => CallbackArity != 0 && CallbackArity == arity;
}

/// <summary>One trusted receiver/input value, with the item count its collection view presents.</summary>
internal sealed record MetamorphicValueShape(string Id, string Source, int CollectionItemCount);

/// <summary>How a callback wrapper binds the values its consumer supplies per invocation.</summary>
internal enum MetamorphicWrapperProjection
{
    /// <summary>`MmWrap(a, b, ...) = builtin(a, b, ...)` — fixed parameters matching the consumer's callback arity.</summary>
    OrdinaryFixed,

    /// <summary>`MmWrap(a, ...) = a.builtin(...)` — the same binding written as a dotted call.</summary>
    DottedFixed,

    /// <summary>`MmWrap(xs...) = ...` — a REST parameter. Never equivalent; always rejected.</summary>
    Rest,

    /// <summary>Fixed parameters at the WRONG arity for the consumer. Never equivalent; always rejected.</summary>
    ArityMismatched,
}

/// <summary>
/// The reviewed tables Phase 2's trusted templates draw from.
///
/// <para>Nothing here was assumed: every entry was verified against the repository — the
/// builtin set and its fixed arities come from <c>BuiltinRegistry</c>, the extension-style
/// dotted contract from <c>AGENTS.md</c> and <c>DottedReceiverEvaluationTests</c>, and every
/// (builtin x receiver) and (consumer x callback x input) combination below was measured to
/// agree on semantics, materialized items, and materialized string units before being
/// admitted. Combinations that were measured NOT to agree — rest and arity-mismatched
/// callback projections — are represented too, as explicitly REJECTED cases.</para>
///
/// <para>All tables are immutable: the harness has no static mutable state.</para>
/// </summary>
internal static class MetamorphicTables
{
    /// <summary>
    /// Prefix for every user-defined name a template generates. Builtins are all lowercase and
    /// template-local names never start with this, so a generated name cannot collide.
    /// </summary>
    internal const string NamePrefix = "Mm";

    internal const string ReceiverProperty = NamePrefix + "R";
    internal const string RowsProperty = NamePrefix + "Rows";
    internal const string ExtensionFunction = NamePrefix + "F";
    internal const string WrapperFunction = NamePrefix + "Wrap";

    /// <summary>Callback helpers emitted in a template preamble when a suffix or chain link needs one.</summary>
    internal const string DoubleCallback = NamePrefix + "Double";
    internal const string BigCallback = NamePrefix + "Big";
    internal const string AddCallback = NamePrefix + "Add";

    internal const string CallbackPreamble =
        DoubleCallback + "(x) = x * 2\n" +
        BigCallback + "(x) = x > 2\n" +
        AddCallback + "(a, b) = a + b\n";

    /// <summary>
    /// Collection builtins that genuinely support both `F(receiver, ...)` and
    /// `receiver.F(...)`. Every entry is a FIXED-arity callable whose first parameter is the
    /// receiver (`BuiltinRegistry.Sequence(...)` plus the one-argument `atoms`), so the dotted
    /// rewrite `A.F(B, C)` -> `F(A, B, C)` preserves argument boundaries exactly.
    ///
    /// <para>Deliberately EXCLUDED: `if`, `while`, `repeat` (control flow, non-fixed arity, no
    /// receiver-shaped first parameter) and `range`. `range` parses and evaluates perfectly well
    /// in dotted form — `1.range(5)` is `[1, 2, 3, 4, 5]` — but its first parameter is a scalar
    /// range BOUND, not a collection, so a `receiver.range(...)` pair would not be an instance of
    /// the Group A receiver contract these tables exist to exercise. Nothing about it is
    /// unparsable; it is simply a different shape.</para>
    /// </summary>
    internal static readonly ImmutableArray<MetamorphicBuiltin> Builtins =
    [
        new("count", MetamorphicSuffixKind.None, MetamorphicResultKind.Scalar, CallbackArity: 1),
        new("sum", MetamorphicSuffixKind.None, MetamorphicResultKind.Scalar, CallbackArity: 1),
        new("first", MetamorphicSuffixKind.None, MetamorphicResultKind.Scalar, CallbackArity: 1),
        new("last", MetamorphicSuffixKind.None, MetamorphicResultKind.Scalar, CallbackArity: 1),
        new("min", MetamorphicSuffixKind.None, MetamorphicResultKind.Scalar, CallbackArity: 1),
        new("max", MetamorphicSuffixKind.None, MetamorphicResultKind.Scalar, CallbackArity: 1),
        new("avg", MetamorphicSuffixKind.None, MetamorphicResultKind.Scalar, CallbackArity: 1),
        new("order", MetamorphicSuffixKind.None, MetamorphicResultKind.Collection, CallbackArity: 1),
        new("orderDesc", MetamorphicSuffixKind.None, MetamorphicResultKind.Collection, CallbackArity: 1),
        new("distinct", MetamorphicSuffixKind.None, MetamorphicResultKind.Collection, CallbackArity: 1),
        new("atoms", MetamorphicSuffixKind.None, MetamorphicResultKind.Collection, CallbackArity: 1),
        new("take", MetamorphicSuffixKind.WholeNumber, MetamorphicResultKind.Collection, CallbackArity: 2),
        new("skip", MetamorphicSuffixKind.WholeNumber, MetamorphicResultKind.Collection, CallbackArity: 2),
        new("contains", MetamorphicSuffixKind.Value, MetamorphicResultKind.Scalar, CallbackArity: 2),
        new("map", MetamorphicSuffixKind.Callback1, MetamorphicResultKind.Collection, CallbackArity: 0),
        new("filter", MetamorphicSuffixKind.Callback1, MetamorphicResultKind.Collection, CallbackArity: 0),
        new("reduce", MetamorphicSuffixKind.Callback2Initial, MetamorphicResultKind.Scalar, CallbackArity: 0),
    ];

    /// <summary>
    /// Compact receiver values spanning every KatLang value kind the collection view
    /// distinguishes. <c>CollectionItemCount</c> is the post-binding one-level view size and is
    /// pinned against the runtime by a deterministic test.
    /// </summary>
    internal static readonly ImmutableArray<MetamorphicValueShape> ReceiverShapes =
    [
        new("atom", "7", 1),
        new("string", "'ab'", 1),
        new("emptySequence", "()", 0),
        new("sequence", "(1, 2, 3)", 3),
        new("emptyList", "[]", 0),
        new("singletonList", "[7]", 1),
        new("list", "[1, 2, 3]", 3),
        new("nestedList", "[[1, 2], [3, 4]]", 2),
        new("listOfSequences", "[(1, 2), (3, 4)]", 2),
        new("sequenceOfLists", "([1, 2], [3, 4])", 2),
        new("stringList", "['ab', 'cd']", 2),
        new("rangeCall", "range(1, 4)", 4),
    ];

    /// <summary>Callback INPUT rows for Group D. Non-scalar shapes come first: they are the ones
    /// that expose accidental rematerialization of a prepared callback value.</summary>
    internal static readonly ImmutableArray<MetamorphicValueShape> CallbackInputShapes =
    [
        new("nestedList", "[[1, 2], [3]]", 2),
        new("listOfSequenceRows", "[(1, 2), (3, 4)]", 2),
        new("listOfMixedRow", "[(1, [2, 3])]", 1),
        new("stringList", "['abc', 'de']", 2),
        new("singletonNestedList", "[[1, 2]]", 1),
        new("emptyRow", "[()]", 1),
        new("mixedList", "[1, 'ab', [2, 3]]", 3),
        new("scalarList", "[1, 2, 3]", 3),
        new("emptyList", "[]", 0),
    ];

    /// <summary>Ordinary values used where a builtin takes a plain value argument (`contains`).</summary>
    internal static readonly ImmutableArray<string> ValueSuffixArguments = ["3", "1", "'ab'", "[1, 2]", "()"];

    /// <summary>Callback arguments for `map`/`filter`: two user callbacks plus a builtin-as-callback.</summary>
    internal static readonly ImmutableArray<string> Callback1SuffixArguments = [DoubleCallback, BigCallback, "count"];

    /// <summary>`reduce` suffixes: reducer plus initial accumulator, written as one suffix list.</summary>
    internal static readonly ImmutableArray<string> Callback2SuffixArguments =
        [AddCallback + ", 0", AddCallback + ", 10", "contains, [1, 2]"];

    /// <summary>Higher-order consumers whose callback contract Phase 2 can guarantee.</summary>
    internal static readonly ImmutableArray<string> CallbackConsumers = ["map", "filter", "reduce"];

    /// <summary>Values the callback-wrapper projection dimension can take.</summary>
    internal static readonly ImmutableArray<MetamorphicWrapperProjection> WrapperProjections =
    [
        MetamorphicWrapperProjection.DottedFixed,
        MetamorphicWrapperProjection.OrdinaryFixed,
        MetamorphicWrapperProjection.Rest,
        MetamorphicWrapperProjection.ArityMismatched,
    ];

    /// <summary>How many values a consumer supplies to its callback per invocation.</summary>
    internal static int CallbackArityOf(string consumer) => consumer switch
    {
        "map" or "filter" => 1,
        "reduce" => 2,
        _ => 0,
    };

    /// <summary>The initial-accumulator argument a consumer needs after its callback, or "".</summary>
    internal static string ConsumerTrailingArgument(string consumer) => consumer switch
    {
        "reduce" => ", [1, 2]",
        _ => "",
    };

    /// <summary>
    /// Boundary-relevant whole-number suffix values for `take`/`skip`, derived from the
    /// receiver's own item count: zero, one, one below, exactly at, one above, and a negative.
    /// </summary>
    internal static string WholeNumberSuffixArgument(int variant, int itemCount)
    {
        var value = (variant % 6) switch
        {
            0 => 0,
            1 => 1,
            2 => itemCount - 1,
            3 => itemCount,
            4 => itemCount + 1,
            _ => -1,
        };

        return value.ToString(CultureInfo.InvariantCulture);
    }

    /// <summary>Number of suffix variants a builtin's suffix kind offers.</summary>
    internal static int SuffixVariantCount(MetamorphicSuffixKind kind) => kind switch
    {
        MetamorphicSuffixKind.None => 1,
        MetamorphicSuffixKind.WholeNumber => 6,
        MetamorphicSuffixKind.Value => ValueSuffixArguments.Length,
        MetamorphicSuffixKind.Callback1 => Callback1SuffixArguments.Length,
        MetamorphicSuffixKind.Callback2Initial => Callback2SuffixArguments.Length,
        _ => 1,
    };

    /// <summary>The written suffix-argument list for one builtin/variant, or "" for none.</summary>
    internal static string SuffixArguments(MetamorphicBuiltin builtin, int variant, int receiverItemCount)
        => builtin.SuffixKind switch
        {
            MetamorphicSuffixKind.None => "",
            MetamorphicSuffixKind.WholeNumber => WholeNumberSuffixArgument(variant, receiverItemCount),
            MetamorphicSuffixKind.Value => ValueSuffixArguments[variant % ValueSuffixArguments.Length],
            MetamorphicSuffixKind.Callback1 => Callback1SuffixArguments[variant % Callback1SuffixArguments.Length],
            MetamorphicSuffixKind.Callback2Initial => Callback2SuffixArguments[variant % Callback2SuffixArguments.Length],
            _ => "",
        };

    /// <summary>True when the builtin's suffix needs the callback preamble emitted.</summary>
    internal static bool NeedsCallbackPreamble(MetamorphicBuiltin builtin, string suffixArguments)
        => builtin.SuffixKind is MetamorphicSuffixKind.Callback1 or MetamorphicSuffixKind.Callback2Initial
            && suffixArguments.Contains(NamePrefix, StringComparison.Ordinal);
}
