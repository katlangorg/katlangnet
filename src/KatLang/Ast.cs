using System.Numerics;

namespace KatLang;

// ── Operators (Lean: BinaryOp, ComparisonOp, UnaryOp) ───────────────────────

/// <summary>
/// Binary operators. Arithmetic (<c>Add</c>…<c>Pow</c>) takes numeric scalar operands
/// and yields a number. <c>And</c>/<c>Or</c>/<c>Xor</c> take Boolean operands only and
/// yield a Boolean — there is no numeric truthiness. The six comparison operators are
/// NOT binary operators: they form the one chainable comparison tier
/// (<see cref="ComparisonOp"/>, <see cref="Expr.Comparison"/>).
/// </summary>
public enum BinaryOp { Add, Sub, Mul, Div, IDiv, Mod, Pow, And, Or, Xor }

/// <summary>
/// The six comparison operators of the ONE comparison precedence tier. The ordering
/// comparisons (<c>Lt</c>…<c>Ge</c>) take numeric scalar operands; <c>Eq</c>/<c>Ne</c>
/// are total structural equality over every value kind. Every comparison yields a
/// <see cref="Result.Bool"/>. Unparenthesized comparisons at one syntactic level form
/// one <see cref="Expr.Comparison"/> chain. Lean: <c>ComparisonOp</c>.
/// </summary>
public enum ComparisonOp { Lt, Gt, Le, Ge, Eq, Ne }

/// <summary><c>Minus</c> negates a number; <c>Not</c> negates a Boolean value.</summary>
public enum UnaryOp { Minus, Not }

/// <summary>
/// One link of a comparison chain: the operator that compares the PREVIOUS operand of
/// the chain with <paramref name="Operand"/>. Lean: <c>ComparisonLink</c>.
/// </summary>
public sealed record ComparisonLink(ComparisonOp Op, Expr Operand);

// ── Built-in identifiers (Lean: Builtin) ────────────────────────────────────

/// <summary>
/// <c>if</c> uses the fixed 3-argument form <c>if(cond, then, else)</c>.
/// Collection builtins are ordinary fixed-arity callables: exactly one fixed
/// <c>collection</c> argument followed by fixed control arguments such as
/// <c>predicate</c>, <c>mapper</c>, or <c>count</c>, bound after argument
/// evaluation and explicit spread with nothing opened before binding. The
/// post-binding builtin collection view then opens exactly one outer boundary
/// of the bound sequence or exact-list value (any other value is a
/// one-element collection); nested grouped values stay intact. Dot-call
/// receivers fill the <c>collection</c> argument.
/// <c>range(start, stop)</c> materializes the inclusive integer span as one
/// list value.
/// <c>atoms(value)</c> recursively collects numeric atoms depth-first, left to
/// right, through both sequence and exact-list boundaries (strings and other
/// non-numeric leaves contribute no atoms) and materializes them as one
/// list value; it does not use the post-binding collection view, and Boolean
/// values are not atoms either.
/// <c>filter(collection, predicate)</c> keeps the original top-level sequence
/// items whose predicate returns the Boolean value <c>true</c> (a number,
/// string, sequence, or list predicate result is a value-kind error); each
/// callback item is a SELECTED value that crosses the same ordinary value
/// boundary as <c>S:i</c> (one value, never opened), and the kept items are
/// materialized as one exact list value.
/// <c>map(collection, mapper)</c> maps top-level sequence items left to right;
/// each callback item is a selected value under the same value-boundary rule
/// as <c>S:i</c>, <c>mapper(element)</c> must return exactly one mapped
/// element, and sequence/list mapped outputs are preserved whole as exact
/// elements of one list result.
/// <c>count(collection)</c> counts the top-level sequence items exposed by direct
/// sequence consumption; sequence-value top-level elements still count as one element.
/// <c>contains(collection, item)</c> returns <c>true</c> when any top-level sequence
/// item equals <c>item</c> under ordinary KatLang value equality, otherwise
/// <c>false</c>; sequence values compare as sequence values and are not searched
/// recursively.
/// <c>order(collection)</c> sorts top-level numeric sequence items in ascending
/// order into one exact list value; duplicates are preserved, sequence/list
/// values are not flattened, strings are invalid, and empty input yields <c>[]</c>.
/// <c>orderDesc(collection)</c> sorts top-level numeric sequence items in
/// descending order into one exact list value; duplicates are preserved,
/// sequence/list values are not flattened, strings are invalid, and empty
/// input yields <c>[]</c>.
/// <c>first(collection)</c> returns the first preserved top-level sequence item
/// unchanged; atoms, strings, and sequence values each count as one element,
/// and sequence values stay intact.
/// <c>last(collection)</c> returns the last preserved top-level sequence item
/// unchanged; atoms, strings, and sequence values each count as one element,
/// and sequence values stay intact.
/// <c>distinct(collection)</c> removes later duplicate top-level sequence items
/// while preserving the original order of first occurrence and returns one
/// exact list value; nested values stay intact and duplicate detection follows
/// ordinary KatLang value semantics.
/// <c>take(collection, count)</c> returns the first <c>count</c> extracted
/// top-level sequence items unchanged as one exact list value; non-positive
/// counts return <c>[]</c>, oversized counts return a list of all items, and
/// nested values stay intact.
/// <c>skip(collection, count)</c> returns the extracted top-level sequence items
/// after the first <c>count</c> as one exact list value; non-positive counts
/// keep all items, oversized counts return <c>[]</c>, and nested values stay
/// intact.
/// <c>min(collection)</c> compares top-level numeric sequence items left to
/// right; the sequence must be non-empty, each item must be exactly one
/// atomic numeric value, and sequence values are not flattened.
/// <c>max(collection)</c> compares top-level numeric sequence items left to
/// right; the sequence must be non-empty, each item must be exactly one
/// atomic numeric value, and sequence values are not flattened.
/// <c>sum(collection)</c> adds preserved top-level numeric sequence items left to
/// right; each item must be exactly one atomic numeric value, and sequence
/// values are not flattened.
/// <c>avg(collection)</c> averages top-level numeric sequence items left to
/// right and returns the decimal arithmetic mean (total / count); each item
/// must be exactly one atomic numeric value, and sequence values are not
/// flattened. (Lean's Int-only core approximates the mean with truncation
/// toward zero.)
/// <c>reduce(collection, reducer, initial)</c> folds top-level sequence items left
/// to right; the current callback item is a selected value under the same
/// value-boundary rule as <c>S:i</c>, <c>reducer(element, accumulator)</c> must return exactly
/// one next accumulator value, and sequence-value accumulators are preserved whole.
/// </summary>
public enum BuiltinId { @if, @while, @repeat, @atoms, @range, @filter, @map, @order, @orderDesc, @count, @contains, @first, @last, @distinct, @take, @skip, @min, @max, @sum, @avg, @reduce }

// ── Source span: SourceSpan.cs (SourcePosition, SourceSpan) ──────────────────

// ── OutputBundle (Lean: OutputBundle) ───────────────────────────────────────

/// <summary>
/// An ordered sequence of original written <see cref="Expr"/> slots with no
/// lexical ownership of its own: no parent scope, no parameters, no
/// properties, no <c>open</c>, and no declaration namespace. It is intensional
/// syntax — how the slots contribute values or items is determined entirely by
/// the RECEIVER that consumes the bundle:
/// <list type="bullet">
///   <item>Algorithm output evaluation preserves per-row emitted-count
///     semantics (<see cref="Algorithm.User.Output"/>).</item>
///   <item><see cref="Expr.Capture"/> performs canonical sequence capture
///     (singleton/empty normalization) over the bundle.</item>
///   <item><see cref="Expr.ListLiteral"/> collects the slots as one exact
///     immutable list value.</item>
/// </list>
/// It deliberately does NOT encode a fixed runtime consumption policy and is
/// NOT a list of evaluated results.
/// <para>OWNERSHIP: a bundle snapshots its ordered expression membership at
/// construction (the contained <see cref="Expr"/> records are shared, not
/// deep-cloned) and never exposes mutable backing storage, so
/// <c>Count</c>, indexing, and enumeration order are stable for the bundle's
/// lifetime — mirroring Lean's persistent <c>List Expr</c>. Bundle equality
/// is reference identity, like every other AST collection.</para>
/// Lean: <c>OutputBundle := List Expr</c>.
/// </summary>
[System.Runtime.CompilerServices.CollectionBuilder(typeof(OutputBundle), nameof(Create))]
public sealed class OutputBundle : IReadOnlyList<Expr>
{
    /// <summary>The shared empty bundle (membership-stable like every bundle).</summary>
    public static OutputBundle Empty { get; } = new([], ownedStorage: true);

    // Exclusively bundle-owned storage: no caller-supplied collection is ever
    // aliased, and no public member hands this array out, so the bundle's
    // ordered membership cannot change after construction.
    private readonly Expr[] _items;

    /// <summary>
    /// Snapshots the ordered slot membership of <paramref name="items"/> at
    /// construction. Mutating the source collection afterwards never changes
    /// this bundle; the <see cref="Expr"/> instances themselves are shared,
    /// not deep-cloned (they are immutable records). An existing
    /// <see cref="OutputBundle"/> input shares its already-stable storage
    /// without copying. Membership is materialized eagerly, so a virtual
    /// collection is fully enumerated here, once.
    /// </summary>
    public OutputBundle(IReadOnlyList<Expr> items)
        => _items = items is OutputBundle bundle ? bundle._items : [.. items];

    private OutputBundle(Expr[] items, bool ownedStorage)
    {
        System.Diagnostics.Debug.Assert(ownedStorage);
        _items = items;
    }

    /// <summary>Collection-expression builder (<c>[a, b]</c> literals); copies the span.</summary>
    public static OutputBundle Create(ReadOnlySpan<Expr> items)
        => items.Length == 0 ? Empty : new(items.ToArray(), ownedStorage: true);

    /// <summary>
    /// Returns <paramref name="items"/> itself when it already is a bundle
    /// (its membership is already stable — no copy); otherwise snapshots it
    /// like the constructor.
    /// </summary>
    public static OutputBundle From(IReadOnlyList<Expr> items)
        => items as OutputBundle ?? (items.Count == 0 ? Empty : new(items));

    /// <summary>
    /// TRUSTED zero-copy construction over a freshly built array whose
    /// exclusive ownership transfers to the bundle: the caller must hold no
    /// other reference and must never mutate the array afterwards. Mirrors
    /// <see cref="Result.ListValue.TakeOwnership"/>; used only by runtime
    /// reification paths that build a private array per call.
    /// </summary>
    internal static OutputBundle TakeOwnership(Expr[] items)
        => items.Length == 0 ? Empty : new(items, ownedStorage: true);

    public static implicit operator OutputBundle(List<Expr> items) => From(items);

    public static implicit operator OutputBundle(Expr[] items)
        => items.Length == 0 ? Empty : new(items.AsSpan().ToArray(), ownedStorage: true);

    public int Count => _items.Length;

    public Expr this[int index] => _items[index];

    public IEnumerator<Expr> GetEnumerator() => ((IEnumerable<Expr>)_items).GetEnumerator();

    System.Collections.IEnumerator System.Collections.IEnumerable.GetEnumerator() => _items.GetEnumerator();
}

/// <summary>
/// Algorithm parameter metadata.
/// Source spans are populated for explicit clause binders that elaborate to an
/// ordinary <see cref="Algorithm.User"/>. Implicit parameters inferred later by
/// the front end's parameter-detection pass have no source declaration span; a capture
/// LIFTED from a callee by implicit-argument resolution is the callee's declaration and
/// keeps its span, so a span never decides whether an owner's list was written
/// (<see cref="Algorithm.User.HasExplicitParameterList"/> does).
/// </summary>
public enum ParameterKind
{
    Normal,
    Collecting,
}

public sealed record ParameterDeclaration(string Name, SourceSpan? Span = null, ParameterKind Kind = ParameterKind.Normal)
{
    private readonly RuntimeStateSlot<ImplicitParameterProvenance?> _inferredProvenance;

    /// <summary>Exact span of the source prefix <c>*</c> collect marker, when source-backed.</summary>
    public SourceSpan? CollectMarkerSpan { get; init; }

    /// <summary>
    /// Diagnostic-only provenance for an implicit parameter that the front
    /// end's parameter-detection pass inferred from an unresolved identifier;
    /// <c>null</c> for every explicitly declared or host-built parameter.
    /// Carries the unresolved name's first semantic source occurrence and an
    /// optional conservative near-miss suggestion. It never participates in
    /// name resolution, binding, arity, or evaluation — it only enriches
    /// eventual arity/unresolved-parameter diagnostics — and has no Lean
    /// counterpart (wording/provenance metadata, like
    /// <see cref="EvalError.ArityMismatch.Signature"/>).
    /// Carried in an equality-transparent slot: every <c>with</c> copy and the
    /// pattern/declaration conversions (<see cref="ToPattern"/>,
    /// <see cref="ParameterPattern.Captures"/>) reference the SAME note object
    /// (the sharing that <see cref="ImplicitParameterProvenance"/> defines),
    /// and record equality, hashing, and printing ignore it.
    /// </summary>
    internal ImplicitParameterProvenance? InferredProvenance
    {
        get => _inferredProvenance.Value;
        init => _inferredProvenance = new(value);
    }

    public string DisplayName => Kind switch
    {
        ParameterKind.Collecting => $"*{Name}",
        _ => Name,
    };

    /// <summary>
    /// This declaration as a capture leaf (Lean: <c>ParameterPattern.capture</c>). The leaf
    /// HOLDS this very declaration — no copy, so the pattern and the declaration it came
    /// from share one provenance note and one identity.
    /// </summary>
    public CaptureParameterPattern ToPattern() => new(this);
}

/// <summary>
/// Recursive explicit parameter pattern for ordinary user-call binding.
/// Capture nodes bind names; sequence-value nodes preserve one parent-level
/// slot and destructure that slot's immediate sequence elements.
/// A C# <c>closed</c> hierarchy: <see cref="CaptureParameterPattern"/> and
/// <see cref="SequenceValueParameterPattern"/> (top-level records of this
/// assembly) are its only variants, no other assembly can derive from it, and a
/// switch EXPRESSION naming both is compiler-exhaustive with no catch-all arm
/// (the signature/binding planners are written that way).
/// </summary>
public closed record ParameterPattern
{
    private protected ParameterPattern() { }

    public abstract string DisplayName { get; }

    /// <summary>
    /// The capture declarations this pattern binds, left to right and depth first
    /// (Lean: <c>ParameterPattern.captures</c>). A capture leaf yields the declaration it
    /// holds; a sequence-value pattern yields the flattened captures of its items. Never a
    /// cache: a host that mutates a retained <see cref="SequenceValueParameterPattern.Items"/>
    /// list sees the current captures on the next read.
    /// </summary>
    public abstract IReadOnlyList<ParameterDeclaration> Captures { get; }

    public bool ContainsCollectingCapture => Captures.Any(static capture => capture.Kind == ParameterKind.Collecting);

    /// <summary>One capture leaf per declaration (Lean: <c>ParameterPattern.fromParameters</c>).</summary>
    public static IReadOnlyList<ParameterPattern> FromDeclarations(IEnumerable<ParameterDeclaration> parameters)
        => parameters.Select(static parameter => (ParameterPattern)parameter.ToPattern()).ToList();

    /// <summary>
    /// Left-to-right depth-first capture flatten of a pattern list (Lean:
    /// <c>patterns.flatMap ParameterPattern.captures</c>), returning the declarations the
    /// capture leaves hold. Walked with an explicit stack that is allocated only when a
    /// sequence-value pattern is met: parameter patterns are host-constructible to arbitrary
    /// depth, and this public helper must not recurse on the caller's stack.
    /// </summary>
    public static IReadOnlyList<ParameterDeclaration> FlattenCaptures(IEnumerable<ParameterPattern> patterns)
    {
        var captures = new List<ParameterDeclaration>();
        Stack<ParameterPattern>? pending = null;
        foreach (var pattern in patterns)
            AppendCaptures(pattern, captures, ref pending);
        return captures;
    }

    /// <summary>
    /// The number of captures a pattern list binds — <c>FlattenCaptures(patterns).Count</c>
    /// without materializing the list (Lean: <c>(patterns.flatMap captures).length</c>).
    /// Allocation-free for a flat list of capture leaves; a nested sequence-value pattern is
    /// walked with an explicit stack like <see cref="FlattenCaptures"/>.
    /// </summary>
    internal static int CountCaptures(IReadOnlyList<ParameterPattern> patterns)
    {
        var count = 0;
        Stack<ParameterPattern>? pending = null;
        for (var index = 0; index < patterns.Count; index++)
        {
            switch (patterns[index])
            {
                case CaptureParameterPattern:
                    count++;
                    break;
                case SequenceValueParameterPattern group:
                    pending ??= new Stack<ParameterPattern>();
                    PushItems(pending, group);
                    while (pending.Count > 0)
                    {
                        switch (pending.Pop())
                        {
                            case CaptureParameterPattern:
                                count++;
                                break;
                            case SequenceValueParameterPattern nested:
                                PushItems(pending, nested);
                                break;
                            case var unhandled:
                                throw UnhandledPattern(unhandled);
                        }
                    }
                    break;
                case var unhandled:
                    throw UnhandledPattern(unhandled);
            }
        }

        return count;
    }

    private static void AppendCaptures(
        ParameterPattern pattern,
        List<ParameterDeclaration> captures,
        ref Stack<ParameterPattern>? pending)
    {
        switch (pattern)
        {
            case CaptureParameterPattern capture:
                captures.Add(capture.Parameter);
                return;
            case SequenceValueParameterPattern group:
                pending ??= new Stack<ParameterPattern>();
                PushItems(pending, group);
                while (pending.Count > 0)
                {
                    switch (pending.Pop())
                    {
                        case CaptureParameterPattern capture:
                            captures.Add(capture.Parameter);
                            break;
                        case SequenceValueParameterPattern nested:
                            PushItems(pending, nested);
                            break;
                        case var unhandled:
                            throw UnhandledPattern(unhandled);
                    }
                }
                return;
            case var unhandled:
                throw UnhandledPattern(unhandled);
        }
    }

    // Items are pushed last-first so the pop order is the written left-to-right order.
    private static void PushItems(Stack<ParameterPattern> pending, SequenceValueParameterPattern group)
    {
        var items = group.Items;
        for (var index = items.Count - 1; index >= 0; index--)
            pending.Push(items[index]);
    }

    // The runtime guard of the statement-form walks above: the hierarchy is closed, so this
    // is unreachable until a variant is added — and then it fails loudly here.
    private static InvalidOperationException UnhandledPattern(ParameterPattern pattern)
        => new($"Unhandled parameter pattern: {pattern.GetType().Name}");

    public static bool HasCollectingCaptureAtCurrentLevel(IEnumerable<ParameterPattern> patterns)
        => patterns.Count(static pattern => pattern is CaptureParameterPattern { Kind: ParameterKind.Collecting }) > 0;

    /// <summary>
    /// The MINIMUM number of supplied argument slots a parameter-pattern list accepts —
    /// the ONE rule <see cref="Evaluator"/>'s <c>BindParameterPatternList</c> enforces,
    /// factored out here so no other layer re-derives it:
    /// <list type="bullet">
    ///   <item>every pattern consumes exactly ONE supplied slot, whatever it contains — a
    ///   sequence-value group is one slot that the binder opens afterwards, so nested
    ///   structure never changes the count at this level;</item>
    ///   <item>a collecting capture at THIS level consumes NONE: it collects whatever
    ///   slots are left after the fixed prefix and suffix bind, and an empty leftover is
    ///   the exact empty list.</item>
    /// </list>
    /// So <c>Only(*xs)</c> accepts zero supplied slots while <c>Head(x, *rest)</c>,
    /// <c>Tail(*rest, z)</c>, <c>P((x, *rest))</c> and <c>Pair(x, y)</c> each require at
    /// least one. This is deliberately NOT
    /// <see cref="CallableArityFacts.MinTopLevelArgumentCount"/>, whose item-supply
    /// classification excludes signatures that mix a group with a collector; the binder,
    /// not that classification, is the authority here.
    /// Lean: <c>ParameterPattern.minimumSuppliedSlots</c>.
    /// </summary>
    internal static int MinimumSuppliedSlots(IReadOnlyList<ParameterPattern> patterns)
        => patterns.Count - (HasCollectingCaptureAtCurrentLevel(patterns) ? 1 : 0);

    public static bool HasMultipleCollectingCapturesAtAnyLevel(IReadOnlyList<ParameterPattern> patterns)
    {
        // Iterative per-level scan: patterns are host-constructible to arbitrary
        // depth, and this public helper must not recurse on the caller's stack.
        var pending = new Stack<IReadOnlyList<ParameterPattern>>();
        pending.Push(patterns);

        while (pending.Count > 0)
        {
            var level = pending.Pop();
            var collectingAtLevel = 0;
            foreach (var pattern in level)
            {
                if (pattern is CaptureParameterPattern { Kind: ParameterKind.Collecting })
                {
                    if (++collectingAtLevel > 1)
                        return true;
                }
                else if (pattern is SequenceValueParameterPattern group)
                {
                    pending.Push(group.Items);
                }
            }
        }

        return false;
    }

    public static bool HasRepeatedCaptureNames(IEnumerable<ParameterPattern> patterns)
    {
        var seen = new HashSet<string>(StringComparer.Ordinal);
        return FlattenCaptures(patterns).Any(capture => !seen.Add(capture.Name));
    }

    public static bool HasRepeatedCaptureNameIncludingCollecting(IEnumerable<ParameterPattern> patterns)
        => FlattenCaptures(patterns)
            .GroupBy(static capture => capture.Name, StringComparer.Ordinal)
            .Any(static captures => captures.Count() > 1
                && captures.Any(static capture => capture.Kind == ParameterKind.Collecting));
}

/// <summary>
/// A capture leaf: binds ONE name (Lean: <c>ParameterPattern.capture : CallableParameter →
/// ParameterPattern</c>). The leaf HOLDS its <see cref="Parameter"/> declaration — name, span,
/// kind, collect-marker span, and the diagnostic provenance note — so flattening a pattern
/// list into declarations (<see cref="ParameterPattern.Captures"/>,
/// <see cref="Algorithm.User.Parameters"/>) returns the stored declarations instead of
/// allocating copies, and a user algorithm's flat parameter view is a projection of its
/// stored patterns with no second parameter channel. Structural equality, hashing, and
/// printing are those of the held declaration.
/// </summary>
public sealed record CaptureParameterPattern(ParameterDeclaration Parameter) : ParameterPattern
{
    /// <summary>A normal or collecting capture of <paramref name="Name"/>, holding a fresh declaration.</summary>
    public CaptureParameterPattern(string Name, SourceSpan? Span = null, ParameterKind Kind = ParameterKind.Normal)
        : this(new ParameterDeclaration(Name, Span, Kind))
    {
    }

    public string Name => Parameter.Name;

    public SourceSpan? Span => Parameter.Span;

    public ParameterKind Kind => Parameter.Kind;

    /// <summary>Exact span of the source prefix <c>*</c> collect marker, when source-backed.</summary>
    public SourceSpan? CollectMarkerSpan
    {
        get => Parameter.CollectMarkerSpan;
        init => Parameter = Parameter with { CollectMarkerSpan = value };
    }

    /// <summary>
    /// Diagnostic-only provenance when this capture was inferred from an
    /// unresolved identifier; see <see cref="ParameterDeclaration.InferredProvenance"/>.
    /// The inferred capture is the note's FIRST carrier
    /// (<see cref="Algorithm.MergeParameterPatterns"/>), and implicit argument
    /// resolution lifts this very record into every transitive caller's
    /// signature, so the callers share the note by construction.
    /// </summary>
    internal ImplicitParameterProvenance? InferredProvenance
    {
        get => Parameter.InferredProvenance;
        init => Parameter = Parameter with { InferredProvenance = value };
    }

    public override string DisplayName => Parameter.DisplayName;

    public override IReadOnlyList<ParameterDeclaration> Captures => [Parameter];
}

public sealed record SequenceValueParameterPattern(IReadOnlyList<ParameterPattern> Items)
    : ParameterPattern
{
    public override string DisplayName => $"({string.Join(", ", Items.Select(static item => item.DisplayName))})";

    /// <summary>
    /// Left-to-right depth-first capture flatten of <see cref="Items"/>
    /// (<see cref="ParameterPattern.FlattenCaptures"/>): the declarations the nested capture
    /// leaves hold, in written order, duplicates included.
    /// </summary>
    public override IReadOnlyList<ParameterDeclaration> Captures => FlattenCaptures(Items);
}

// ── Expressions (Lean: Expr) ────────────────────────────────────────────────

/// <summary>
/// The KatLang expression hierarchy: a C# <c>closed</c> record whose direct
/// descendants are exactly the sealed nested records below, mirroring the Lean
/// <c>Expr</c> forms plus front-end/native-only forms. Because the hierarchy is closed, a switch
/// expression that handles every nested variant is compiler-exhaustive with no
/// catch-all arm, and adding a variant is a compile error at every such dispatch
/// until the new case is decided (<c>CS8509</c> is an error in this project).
/// Variants are kept nested here by repository convention. The private parameterless
/// constructor does not prevent same-assembly derivation through the synthesized
/// protected copy constructor; <c>closed</c> prevents derivation from other assemblies.
/// </summary>
public closed record Expr
{
    /// <summary>Source location of this expression, populated by the parser.</summary>
    public SourceSpan? Span { get; init; }

    private Expr() { }

    /// <summary>Refers to a parameter declared in the enclosing algorithm.</summary>
    public sealed record Param(string Name) : Expr;

    /// <summary>Numeric literal.</summary>
    public sealed record Num(Decimal128 Value) : Expr;

    /// <summary>String literal. Evaluates to <c>Result.Str</c> (first-class string value).
    /// Also used for compile-time directives (e.g. load URLs) which are eliminated by elaboration.</summary>
    public sealed record StringLiteral(string Value) : Expr;

    /// <summary>
    /// The reserved Boolean literal <c>true</c> / <c>false</c>. Evaluates to
    /// <see cref="Result.Bool"/>. The literals are lexer keywords, never identifiers, so
    /// they can be neither declared nor shadowed and never become implicit parameters.
    /// Lean: <c>Expr.boolLiteral</c>.
    /// </summary>
    public sealed record BoolLiteral(bool Value) : Expr;

    /// <summary>Numeric negation or Boolean negation.</summary>
    public sealed record Unary(UnaryOp Op, Expr Operand) : Expr;

    /// <summary>Binary arithmetic or logical expression (never a comparison — see <see cref="Comparison"/>).</summary>
    public sealed record Binary(BinaryOp Op, Expr Left, Expr Right) : Expr;

    /// <summary>
    /// A COMPARISON CHAIN: <c>First op1 x1 op2 x2 …</c>, the ONE representation of
    /// every comparison, whether it has one link (<c>a &lt; b</c>) or many
    /// (<c>a &lt; b &lt;= c == d != e</c>). Unparenthesized comparison operators at one
    /// syntactic level form one chain; a parenthesized comparison is an ordinary
    /// operand (<c>(a &lt; b) == c</c> is a one-link chain whose first operand is a
    /// chain). Each link compares the PREVIOUS operand with its own — adjacent-pair
    /// semantics, so <c>1 != 2 != 1</c> is <c>1 != 2</c> and <c>2 != 1</c> — and the
    /// chain is <c>true</c> iff every link holds. Evaluation is incremental and left to
    /// right: every operand is evaluated EXACTLY ONCE (the previous operand's VALUE is
    /// reused, never its expression), each link is compared as soon as its operand is
    /// available, a <c>false</c> link never stops the chain (KatLang's eager Boolean
    /// composition, so a later invalid comparison is still reported), and an error
    /// terminates it (later operands are not evaluated). A host-built chain with no
    /// links evaluates its first operand and is <c>true</c>. Lean: <c>Expr.comparison</c>.
    /// </summary>
    public sealed record Comparison(Expr First, IReadOnlyList<ComparisonLink> Links) : Expr;

    /// <summary>Output selection. <c>Index(a, i)</c> selects top-level item <c>i</c> of the evaluated target <c>a</c> and returns it as ONE value (selection is a value boundary: the item is never opened; <c>*</c> opens it).</summary>
    public sealed record Index(Expr Target, Expr Selector) : Expr;

    /// <summary>
    /// INTERNAL sequence-join node retained for semantic AST compatibility
    /// with the Lean model. Surface spreading is the attached postfix
    /// spread marker <c>expr*</c> (<see cref="SequenceSpread"/>), never
    /// this node.
    ///
    /// This is NOT the AST representation of written sequence-value syntax:
    /// the parser and all production transformations have ZERO ORIGIN SITES
    /// for it — surviving parenthesized lists parse to <see cref="Capture"/>
    /// and <c>()</c> to <see cref="EmptySequence"/>; elaboration visitors may REBUILD an
    /// existing node but cannot introduce one into an AST that did not
    /// already contain it. This public constructor (with the public
    /// <c>Evaluator.Run(Expr)</c>) is the intentional EXTERNAL origin
    /// mechanism. Its value evaluation DROPS <c>()</c> leaves (join
    /// semantics: an empty contribution adds no items), which written
    /// parentheses never do, so routing surface syntax through this node
    /// would silently violate the visible-empty rule;
    /// <c>SequenceConstructContainmentTests</c> and the semantic explorer's
    /// internal-node cases enforce that surface syntax and elaboration keep
    /// zero origin sites and that its semantics stay pinned and Lean-aligned.
    /// Lean: <c>Expr.sequenceConstruct</c>.
    /// </summary>
    public sealed record SequenceConstruct(Expr Left, Expr Right) : Expr;

    /// <summary>
    /// Empty sequence value <c>()</c>. Repeated ordinary parentheses around the
    /// empty sequence are useful-structure normalized back to <c>()</c>.
    /// Lean: <c>emptySequence : Nat -> Expr</c>.
    /// </summary>
    public sealed record EmptySequence(int Depth) : Expr;

    /// <summary>
    /// Spread expression. The one surface spelling — the postfix spread
    /// marker <c>operand*</c>, a star directly attached to a completed
    /// expression — lowers to this ONE node at parse time, so there is a
    /// single evaluation path and the spelling never crosses an ordinary
    /// call/property value boundary. <c>SequenceSpread(operand)</c> evaluates
    /// its operand exactly once and contributes the operand's item view to the
    /// surrounding item supply; it does not return or materialize a sequence
    /// or list itself (the receiver decides what the supplied items become).
    /// The fluent dot continuation <c>operand*.Target(...)</c> lowers to the
    /// ordinary lexical call <c>Target(operand*, ...)</c> at parse time, so a
    /// spread node itself never appears as a dot-call target.
    /// Lean: <c>sequenceSpread : Expr → Expr</c>.
    /// </summary>
    public sealed record SequenceSpread(Expr Operand) : Expr
    {
        /// <summary>
        /// Exact span of the source postfix <c>*</c> spread-marker token when
        /// the parser has source information for it. Chained spreads carry
        /// one distinct marker span per written star. Synthetic spreads
        /// (e.g. collecting-parameter forwarding) stay spanless.
        /// </summary>
        public SourceSpan? SpreadMarkerSpan { get; init; }
    }

    /// <summary>
    /// Surface list literal <c>[e1, ..., en]</c>. Evaluates to exactly ONE
    /// list value (<see cref="Result.ListValue"/>). The
    /// element slots form a transparent <see cref="OutputBundle"/> — the same
    /// expression-list body language as written parentheses (an explicit
    /// spread slot opens its operand's immediate items, a non-spread <c>()</c>
    /// slot stays one visible element; free identifiers belong to the
    /// enclosing algorithm) — but the LIST RECEIVER collects the elements
    /// EXACTLY: no singleton erasure and no empty-nesting collapse, so
    /// <c>[7]</c>, <c>[[7]]</c>, and <c>[]</c> are all distinct values.
    /// Lean: <c>listLiteral : OutputBundle → Expr</c>.
    /// </summary>
    public sealed record ListLiteral(OutputBundle Items) : Expr;

    /// <summary>Resolves a named algorithm by lexical lookup.</summary>
    public sealed record Resolve(string Name) : Expr;

    /// <summary>
    /// Dot-call syntax. <c>DotCall(a, "f", args?)</c> represents <c>a.f</c> or <c>a.f(args)</c>
    /// with smart resolution: property access when f has 0 params, otherwise call with receiver.
    /// <c>Args</c> is an ordered <see cref="OutputBundle"/> of the original written
    /// argument expressions, evaluated transparently in the caller's lexical
    /// context. <c>null</c> means NO argument-list syntax (property-style access
    /// <c>a.f</c>); <see cref="OutputBundle.Empty"/> means an explicit empty
    /// list (<c>a.f()</c>) — the two remain distinct.
    /// <para><b>Resolution:</b> a dot edge tries structural member lookup on
    /// the resolved receiver first and uses the lexical fallback only on a
    /// structural miss. Written Grace composes with this ordinary edge:
    /// <c>a~.f</c> carries postfix Grace on the receiver occurrence, while
    /// <c>a.~f</c> carries prefix Grace on the fallback/name occurrence.
    /// Parameter detection consumes either annotation; Grace changes inferred
    /// parameter ORDER only and never selects a different resolution.</para>
    /// <para><b>Lexical fallback identity:</b> <see cref="LexicalFallback"/>
    /// carries the member's lexical-fallback callee as an ordinary
    /// elaboratable name expression — <see cref="Expr.Resolve"/>, or
    /// <see cref="Expr.Param"/> once front-end elaboration decides the name is
    /// a parameter reference — so every runtime consumer CONSUMES the
    /// front-end's Param-vs-Resolve decision instead of reconstructing it.
    /// <c>null</c> means the unelaborated default <c>Resolve(Name)</c>
    /// (host-built trees keep plain lexical-fallback semantics). Elaborated
    /// producers must store only Resolve/Param nodes here; a raw
    /// parser tree may temporarily store the documented Grace wrapper, and any
    /// other expression is outside the elaborated contract (host-built
    /// defensive evaluation still follows that expression's ordinary
    /// <c>ResolveAlg</c> behavior).</para>
    /// Lean: <c>dotMember : Expr → Ident → Expr → Option OutputBundle → Expr</c>
    /// (with <c>Expr.dotCall</c> kept as the ordinary/lexical smart constructor).
    /// </summary>
    public sealed record DotCall(Expr Target, string Name, OutputBundle? Args = null) : Expr
    {
        private readonly RuntimeStateSlot<ImplicitParameterProvenance?> _inferredFallbackProvenance;

        /// <summary>
        /// Exact span of the member identifier to the right of the dot when the
        /// parser has source information for it.
        /// </summary>
        public SourceSpan? MemberSpan { get; init; }

        /// <summary>
        /// The member's lexical-fallback callee identity as an ordinary name
        /// expression (<see cref="Expr.Resolve"/> or <see cref="Expr.Param"/>),
        /// decided once by front-end elaboration. A raw parser tree may temporarily
        /// carry <see cref="Expr.Grace"/> around its Resolve when prefix Grace is
        /// written on the member occurrence (<c>a.~f</c>); elaboration consumes
        /// that wrapper. <c>null</c> means the unelaborated default
        /// <c>Resolve(Name)</c>.
        /// </summary>
        public Expr? LexicalFallback { get; init; }

        /// <summary>
        /// The effective lexical-fallback callee: the stored elaborated
        /// identity, or the unelaborated default <c>Resolve(Name)</c> spanned
        /// at the member identifier.
        /// </summary>
        public Expr EffectiveLexicalFallback
            => LexicalFallback ?? new Resolve(Name) { Span = MemberSpan };

        /// <summary>
        /// The front end's SCOPE-AWARE verdict on whether the stored lexical
        /// fallback can be the selected resolution at runtime
        /// (<see cref="LexicalFallbackSelection"/>), stamped by parameter
        /// detection from the receiver's elaborated static structural-member
        /// provider — the same classification implicit-signature inference acts
        /// on. Exposure rechecks structural-winner proofs as local-only open
        /// providers are removed. The dependency summary consumes it through
        /// <see cref="AstHelpers.LexicalFallbackMayBeSelected"/>, so a fallback
        /// that names an enclosing owner's parameter is charged exactly when
        /// the runtime may take it. <c>null</c> on an unelaborated tree (a raw
        /// parser tree or a host-built one), where consumers fall back to the
        /// receiver expression's raw shape classification.
        /// </summary>
        internal LexicalFallbackSelection? ElaboratedFallbackSelection { get; init; }

        /// <summary>
        /// Diagnostic-only: the provenance note of the implicit parameter that
        /// THIS edge's lexical-fallback occurrence promoted — the same note
        /// object the owner's inferred capture carries — stamped by parameter
        /// detection when the receiver is a statically known algorithm that
        /// provably lacks the member (<see cref="ImplicitParameterProvenance.DotMemberOrigin"/>);
        /// <c>null</c> for a bare or opaque receiver, a fallback that resolved,
        /// a raw parser tree, and a host-built one. It exists so the
        /// post-exposure provenance walk (<see cref="DotMemberProvenanceFinalizer"/>)
        /// can re-examine the edge against the completed tree and update the
        /// shared note in place; it never takes part in resolution. Carried in an
        /// equality-transparent slot, so every <c>with</c> copy of the edge — the
        /// resolver's, completion's, and exposure's rewrites — keeps it while
        /// record equality, hashing, and printing ignore it.
        /// </summary>
        internal ImplicitParameterProvenance? InferredFallbackProvenance
        {
            get => _inferredFallbackProvenance.Value;
            init => _inferredFallbackProvenance = new(value);
        }
    }

    /// <summary>
    /// Grace weight annotation on exactly ONE bare parameter/name occurrence.
    /// Prefix <c>~x</c> → weight -1 (one position earlier), postfix
    /// <c>x~</c> → weight +1 (one position later); repeated markers and
    /// repeated graced occurrences of the same name sum. SOURCE-VALID Grace
    /// wraps a single <see cref="Resolve"/> occurrence — the parser produces
    /// it only for written identifier Grace: this includes postfix Grace on a
    /// receiver before an ordinary dot (<c>a~.f</c>) and prefix Grace on the
    /// dot member's fallback/name occurrence (<c>a.~f</c>). Repeated markers
    /// still decorate that same one occurrence (<c>a~~.f</c>). Grace is NOT an
    /// expression operator: it
    /// never distributes a weight through a compound operand (complex
    /// operands are parse errors; a host-built one is handled defensively
    /// with no reordering effect).
    /// Grace affects implicit parameter ordering ONLY: front-end elaboration
    /// consumes the weight and strips the wrapper, so no elaborated tree
    /// contains one and evaluation semantics never observe it.
    /// Not part of the Lean specification.
    /// </summary>
    public sealed record Grace(Expr Inner, int Weight) : Expr;

    /// <summary>
    /// An algorithm used in expression position, exposing ALGORITHM IDENTITY:
    /// the contained algorithm owns its lexical scope (parameters, properties,
    /// <c>open</c>, declaration namespace) according to ordinary algorithm
    /// rules, and the expression participates in value interpretation,
    /// algorithm/callable interpretation, and namespace/<c>open</c>
    /// interpretation. Surface forms are <c>{ }</c> brace algorithm literals;
    /// front-end elaboration also uses it for elaborated modules and synthetic
    /// scoped helpers, and parser error recovery uses it to retain rejected
    /// algorithm-level declarations written inside parentheses.
    /// Lean: <c>Expr.algorithmExpr</c>.
    /// </summary>
    public sealed record AlgorithmExpr(Algorithm Algorithm) : Expr;

    /// <summary>
    /// A surviving parenthesized capture boundary over an
    /// <see cref="OutputBundle"/>: the normalized value/output boundary that
    /// written parentheses perform (<c>capture : Supply → Value</c>). The
    /// bundle owns no lexical scope — free identifiers inside it belong to the
    /// nearest enclosing scope-owning algorithm — and CAPTURE IS NOT ALGORITHM
    /// IDENTITY: resolving a capture on the algorithm channel yields only a
    /// zero-parameter output thunk over the bundle, never the algorithm
    /// identity of any inner expression. Redundant parentheses normalize away
    /// at parse time; only meaningful boundaries survive as this node
    /// (multi-slot groups, spread groups, grouped references, and nested
    /// captures).
    /// Lean: <c>Expr.capture</c>.
    /// </summary>
    public sealed record Capture(OutputBundle Body) : Expr;

    /// <summary>
    /// Algorithm application. <c>Call(f, args)</c> applies <c>f</c> to the
    /// argument slots of <c>args</c> — an ordered <see cref="OutputBundle"/> of
    /// the original written argument expressions. The bundle owns no lexical
    /// scope: each slot is evaluated transparently in the caller's context, and
    /// each original expression can independently participate in the value
    /// channel and, where permitted, the algorithm channel (dual-view binding).
    /// Lean: <c>call : Expr → OutputBundle → Expr</c>.
    /// </summary>
    public sealed record Call(Expr Function, OutputBundle Args) : Expr;

    /// <summary>
    /// Native function call. Evaluates a C# function using parameter values from the environment.
    /// Used internally by built-in Math functions. Not produced by the parser.
    /// Not part of the Lean specification.
    /// </summary>
    public sealed record NativeCall(string FnName, IReadOnlyList<string> ArgNames) : Expr;
}

// ── Patterns (Lean: Pattern — for clause heads and conditional algorithms) ──

/// <summary>
/// Pattern language for clause heads and conditional algorithm branch matching.
/// Conditional patterns match against <see cref="Result"/> values at call time.
/// Lean: <c>Pattern</c> inductive.
///
/// Surface clause-definition elaboration uses these patterns too:
/// a same-name clause group elaborates as ordinary
/// <see cref="Algorithm.User"/> only when it contains exactly one clause and
/// that sole head is a supported recursive explicit parameter pattern; multi-clause
/// families and literal/mixed heads elaborate as <see cref="Algorithm.Conditional"/>.
///
/// A C# <c>closed</c> hierarchy, like the Lean inductive: <see cref="Bind"/>,
/// <see cref="LitInt"/>, <see cref="LitString"/>, <see cref="LitBool"/>, and
/// <see cref="SequenceValue"/> are its only variants, no other assembly can derive from
/// it, and a switch EXPRESSION naming all five is compiler-exhaustive with no catch-all
/// arm — the evaluator's
/// pattern matchers are written that way, so a new pattern kind fails the build
/// there until decided; statement-form pattern walks need separate coverage review.
/// </summary>
public closed record Pattern
{
    private Pattern() { }

    /// <summary>Matches any Result and binds it to the given name.</summary>
    public sealed record Bind(string Name) : Pattern
    {
        /// <summary>Exact span of the binder identifier when available.</summary>
        public SourceSpan? NameSpan { get; init; }

        /// <summary>Parameter binding kind when this binder elaborates to an ordinary explicit parameter.</summary>
        public ParameterKind ParameterKind { get; init; } = ParameterKind.Normal;

        /// <summary>Exact span of the source prefix <c>*</c> collect marker, when source-backed.</summary>
        public SourceSpan? CollectMarkerSpan { get; init; }
    }

    /// <summary>Matches only <c>Result.Atom(n)</c> where n equals <see cref="Value"/>.</summary>
    public sealed record LitInt(Decimal128 Value) : Pattern;

    /// <summary>Matches only <c>Result.Str(s)</c> where s equals <see cref="Value"/> (exact string equality).</summary>
    public sealed record LitString(string Value) : Pattern;

    /// <summary>
    /// Matches only <c>Result.Bool(b)</c> where b equals <see cref="Value"/> — the reserved
    /// literals <c>true</c> / <c>false</c> in a clause head. A Boolean is never a number, so
    /// <c>F(1)</c> and <c>F(true)</c> are different clauses. Lean: <c>Pattern.litBool</c>.
    /// </summary>
    public sealed record LitBool(bool Value) : Pattern;

    /// <summary>Matches <c>Result.SequenceValue(items)</c> with same arity, each sub-pattern matching.</summary>
    public sealed record SequenceValue(IReadOnlyList<Pattern> Items) : Pattern;

    /// <summary>
    /// Collect all binder names in this pattern (left-to-right). Walked with an
    /// explicit stack: patterns are host-constructible to arbitrary depth, and this
    /// public convenience must not recurse on the caller's stack.
    /// </summary>
    public IReadOnlyList<string> BoundNames()
    {
        var names = new List<string>();
        var pending = new Stack<Pattern>();
        pending.Push(this);

        while (pending.Count > 0)
        {
            switch (pending.Pop())
            {
                case Bind(var name):
                    names.Add(name);
                    break;
                case SequenceValue(var items):
                    for (var i = items.Count - 1; i >= 0; i--)
                        pending.Push(items[i]);
                    break;
            }
        }

        return names;
    }

    /// <summary>
    /// Compute the top-level arity of a pattern.
    /// Lean: <c>Pattern.topLevelArity</c>.
    /// <list type="bullet">
    ///   <item><c>SequenceValue [p1, ..., pn]</c> → n</item>
    ///   <item>Any non-sequence-value pattern -> 1</item>
    /// </list>
    /// This defines the outer call interface of a conditional algorithm branch.
    /// All branches of the same conditional algorithm must have the same
    /// top-level pattern arity. Nested substructure may vary.
    /// </summary>
    public int TopLevelArity() => this switch
    {
        SequenceValue(var items) => items.Count,
        _ => 1,
    };

    /// <summary>
    /// Returns declared parameter names only for the strict flat multi-binder
    /// core subset: a top-level flat sequence-value pattern of multiple plain binders.
    ///
    /// This is intentionally narrower than the full surface clause
    /// elaboration rule. It is kept for evaluator compatibility fallback over
    /// manually constructed conditional ASTs.
    /// </summary>
    internal IReadOnlyList<string>? TryGetFlatMultiBinderParams()
    {
        var binders = TryGetFlatMultiBinderBindings();
        if (binders is null)
            return null;

        return binders.Select(binder => binder.Name).ToList();
    }

    internal IReadOnlyList<Bind>? TryGetFlatMultiBinderBindings()
    {
        if (this is not SequenceValue(var items) || items.Count <= 1)
            return null;

        var binders = new List<Bind>(items.Count);
        foreach (var item in items)
        {
            if (item is not Bind binder)
                return null;
            binders.Add(binder);
        }

        return binders;
    }

    /// <summary>
    /// Returns declared parameter names when a sole surface clause head
    /// consists only of recursive binder/sequence-value parameter patterns.
    ///
    /// This is only an eligibility helper for the whole same-name
    /// clause-group rule. Front-ends must still classify at the family level:
    /// a same-name clause group elaborates as ordinary only if it contains
    /// exactly one clause and that sole head qualifies here.
    ///
    /// Accepted shapes:
    /// <list type="bullet">
    ///   <item><c>Bind(x)</c>, corresponding to <c>F(x) = ...</c></item>
    ///   <item><c>SequenceValue [Bind(x), Bind(y), ...]</c></item>
    ///   <item>Nested binder-only sequence-value patterns such as <c>F((head, *tail))</c></item>
    /// </list>
    ///
    /// Rejected on purpose:
    /// <list type="bullet">
    ///   <item>Literal or mixed non-binder pattern structure</item>
    /// </list>
    /// </summary>
    public IReadOnlyList<string>? TryGetOrdinaryClauseParams()
        => TryGetOrdinaryClauseParameters()?.Select(static parameter => parameter.Name).ToList();

    internal IReadOnlyList<Bind>? TryGetOrdinaryClauseBindings()
        => this switch
        {
            Bind binder => [binder],
            _ => TryGetFlatMultiBinderBindings(),
        };

    private static bool TryCreateOrdinaryClauseParameterPattern(
        Pattern pattern,
        [System.Diagnostics.CodeAnalysis.NotNullWhen(true)] out ParameterPattern? parameterPattern)
    {
        if (pattern is Bind binder)
        {
            parameterPattern = new CaptureParameterPattern(binder.Name, binder.NameSpan, binder.ParameterKind)
            {
                CollectMarkerSpan = binder.CollectMarkerSpan,
            };
            return true;
        }

        if (pattern is SequenceValue(var items))
        {
            var childPatterns = new List<ParameterPattern>(items.Count);
            foreach (var item in items)
            {
                if (!TryCreateOrdinaryClauseParameterPattern(item, out var childPattern))
                {
                    parameterPattern = null;
                    return false;
                }

                childPatterns.Add(childPattern);
            }

            parameterPattern = new SequenceValueParameterPattern(childPatterns);
            return true;
        }

        parameterPattern = null;
        return false;
    }

    /// <summary>
    /// Returns declared parameters for ordinary explicit clause heads.
    /// In addition to flat binders, this accepts recursive sequence-value parameter patterns.
    /// </summary>
    internal IReadOnlyList<ParameterPattern>? TryGetOrdinaryClauseParameterPatterns()
    {
        if (this is Bind binder)
            return
            [
                new CaptureParameterPattern(binder.Name, binder.NameSpan, binder.ParameterKind)
                {
                    CollectMarkerSpan = binder.CollectMarkerSpan,
                }
            ];

        if (this is not SequenceValue(var items))
            return null;

        var parameterPatterns = new List<ParameterPattern>(items.Count);
        foreach (var item in items)
        {
            if (!TryCreateOrdinaryClauseParameterPattern(item, out var parameterPattern))
                return null;

            parameterPatterns.Add(parameterPattern);
        }

        return parameterPatterns;
    }

    internal IReadOnlyList<ParameterDeclaration>? TryGetOrdinaryClauseParameters()
        => TryGetOrdinaryClauseParameterPatterns() is { } patterns
            ? ParameterPattern.FlattenCaptures(patterns)
            : null;

    /// <summary>
    /// True when a sole clause head requires conditional whole-argument
    /// semantics instead of ordinary user-call binding. Front-ends must still
    /// classify at the whole same-name clause-group level, because a plain
    /// binder head can still belong to a multi-clause family that remains
    /// conditional.
    /// </summary>
    public bool RequiresConditionalClauseSemantics()
        => TryGetOrdinaryClauseParameterPatterns() is null;

    /// <summary>
    /// Check whether two patterns are match-equivalent, i.e., they match
    /// the same set of inputs. Binder spelling is irrelevant, but repeated
    /// binder names impose equality constraints whose position must agree.
    /// </summary>
    internal bool IsMatchEquivalent(Pattern other)
    {
        var leftToRight = new Dictionary<string, string>(StringComparer.Ordinal);
        var rightToLeft = new Dictionary<string, string>(StringComparer.Ordinal);

        bool Match(Pattern left, Pattern right)
        {
            switch (left, right)
            {
                case (Bind leftBind, Bind rightBind):
                    if (leftToRight.TryGetValue(leftBind.Name, out var mappedName))
                        return string.Equals(mappedName, rightBind.Name, StringComparison.Ordinal);
                    if (rightToLeft.ContainsKey(rightBind.Name))
                        return false;

                    leftToRight[leftBind.Name] = rightBind.Name;
                    rightToLeft[rightBind.Name] = leftBind.Name;
                    return true;

                // Structural numeric equality (Decimal128.Equals), matching runtime
                // LitInt matching and the value-consistent fingerprint below: NaN is
                // one value and quantum is ignored, so a LitInt(NaN) pattern stays
                // match-equivalent to itself and hashed clause-family comparers keep
                // a reflexive equality.
                case (LitInt leftInt, LitInt rightInt):
                    return leftInt.Value.Equals(rightInt.Value);

                case (LitString leftString, LitString rightString):
                    return string.Equals(leftString.Value, rightString.Value, StringComparison.Ordinal);

                case (LitBool leftBool, LitBool rightBool):
                    return leftBool.Value == rightBool.Value;

                case (SequenceValue leftGroup, SequenceValue rightGroup):
                    if (leftGroup.Items.Count != rightGroup.Items.Count)
                        return false;

                    for (var index = 0; index < leftGroup.Items.Count; index++)
                    {
                        if (!Match(leftGroup.Items[index], rightGroup.Items[index]))
                            return false;
                    }

                    return true;

                default:
                    return false;
            }
        }

        return Match(this, other);
    }

    /// <summary>
    /// Equality comparer whose equality is exactly <see cref="IsMatchEquivalent"/> and whose
    /// hash is a deterministic structural fingerprint consistent with it: match-equivalent
    /// patterns always hash equally, so a hashed set/dictionary groups an equivalence class
    /// into one bucket and resolves any unrelated hash collision through the exact comparison.
    /// This turns clause-family duplicate detection from an all-pairs O(clauses^2) scan into an
    /// O(clauses) hashed lookup while preserving branch order, diagnostics, and spans, which
    /// stay owned by the ordered branch list.
    ///
    /// <para>The fingerprint ignores exactly what match-equivalence ignores — binder spelling
    /// (only first-occurrence position matters) and source spans — and includes literal values
    /// and sequence-value shape. It uses an FNV-1a fold rather than <see cref="HashCode"/> so it
    /// is process-stable, not a per-run randomized value; the set is still purely in-memory and
    /// run-local, and no fingerprint is persisted.</para>
    ///
    /// <para>This shared instance carries NO observer, so it has no mutable state and is safe to
    /// share across concurrent parses and the runtime duplicate-branch guard. A test that needs to
    /// count exact comparisons of ONE indexed operation passes an explicit
    /// <see cref="PatternComparisonObservations"/> to <see cref="CreateMatchEquivalenceComparer"/>
    /// instead; that observer belongs to that one operation and is never static.</para>
    /// </summary>
    internal static IEqualityComparer<Pattern> MatchEquivalenceComparer { get; } = new MatchEquivalenceComparerImpl(observations: null);

    /// <summary>
    /// Returns a match-equivalence comparer bound to <paramref name="observations"/>: the shared
    /// observer-less instance when it is <c>null</c> (production parser and runtime paths), otherwise
    /// a fresh comparer that records one exact comparison per <see cref="IsMatchEquivalent"/> call it
    /// performs. The observer is passive — it changes neither equality, hashing, nor bucket layout —
    /// and belongs to a single parse or measured operation, so counts never cross operations or runs.
    /// </summary>
    internal static IEqualityComparer<Pattern> CreateMatchEquivalenceComparer(PatternComparisonObservations? observations)
        => observations is null ? MatchEquivalenceComparer : new MatchEquivalenceComparerImpl(observations);

    private sealed class MatchEquivalenceComparerImpl(PatternComparisonObservations? observations) : IEqualityComparer<Pattern>
    {
        public bool Equals(Pattern? x, Pattern? y)
        {
            if (ReferenceEquals(x, y))
                return true;
            if (x is null || y is null)
                return false;

            // Record only when an actual exact comparison is performed (never on the reference or
            // null short-circuits), so the count is exactly the IsMatchEquivalent calls this
            // comparer makes for its owning indexed operation.
            observations?.RecordExactComparison();
            return x.IsMatchEquivalent(y);
        }

        public int GetHashCode(Pattern pattern)
        {
            const uint fnvOffset = 2166136261;
            const uint fnvPrime = 16777619;
            var hash = fnvOffset;

            void Mix(uint value)
            {
                hash = (hash ^ (value & 0xFF)) * fnvPrime;
                hash = (hash ^ ((value >> 8) & 0xFF)) * fnvPrime;
                hash = (hash ^ ((value >> 16) & 0xFF)) * fnvPrime;
                hash = (hash ^ ((value >> 24) & 0xFF)) * fnvPrime;
            }

            // First-occurrence (De Bruijn-style) binder numbering: two match-equivalent
            // patterns visit binders in the same pre-order and share the same repeat
            // structure, so they mix the same index sequence regardless of spelling.
            var firstOccurrence = new Dictionary<string, int>(StringComparer.Ordinal);

            void Visit(Pattern node)
            {
                switch (node)
                {
                    case Bind bind:
                        Mix(1);
                        if (!firstOccurrence.TryGetValue(bind.Name, out var index))
                        {
                            index = firstOccurrence.Count;
                            firstOccurrence[bind.Name] = index;
                        }
                        Mix((uint)index);
                        break;
                    case LitInt litInt:
                        Mix(2);
                        // Value hash, not representation bits: IsMatchEquivalent compares
                        // literal patterns by numeric VALUE (quantum-insensitive), so the
                        // fingerprint must not distinguish equal values spelled with
                        // different quanta. Decimal128.GetHashCode is exactly that
                        // value-consistent hash.
                        Mix(unchecked((uint)litInt.Value.GetHashCode()));
                        break;
                    case LitString litString:
                        Mix(3);
                        Mix((uint)litString.Value.Length);
                        foreach (var ch in litString.Value)
                            Mix(ch);
                        break;
                    case LitBool litBool:
                        Mix(5);
                        Mix(litBool.Value ? 1u : 0u);
                        break;
                    case SequenceValue sequence:
                        Mix(4);
                        Mix((uint)sequence.Items.Count);
                        foreach (var item in sequence.Items)
                            Visit(item);
                        break;
                }
            }

            Visit(pattern);
            return unchecked((int)hash);
        }
    }
}

/// <summary>
/// A branch of a conditional algorithm: a pattern and a body algorithm.
/// Lean: <c>CondBranch</c> structure.
/// The pattern is the complete input specification of the branch.
/// Branch bodies receive bindings only from the matched pattern (plus ordinary
/// lexical resolution). No extra implicit parameters are inferred.
/// Grace <c>~</c> is not permitted in branch patterns or bodies.
/// </summary>
public sealed record CondBranch(Pattern Pattern, Algorithm Body)
{
    /// <summary>
    /// Compute the top-level output arity of this branch body.
    /// Lean: <c>Algorithm.topLevelOutputArity</c> / <c>body.output.length</c>.
    /// This is the number of top-level output expressions in the branch body.
    /// All branches of the same conditional algorithm must have the same
    /// top-level output arity. Nested internal output structure may vary.
    /// </summary>
    public int TopLevelOutputArity() => Body.Output.Count;
}

// ── Algorithm (Lean: Algorithm — discriminated union) ───────────────────────

/// <summary>
/// Exposure classification of a property, computed by the C# front end
/// (<c>PropertyExposureResolver</c>) and consumed as an INPUT by every lookup.
/// Lean: <c>PropExposure</c>. The classification is a fact about the property's VALUE,
/// never about where the declaration is written. Selection never depends on it:
/// <c>open</c> selects public members and structural dot access selects declared members;
/// whether the selected member may be USED at an access site is the separate
/// accessibility question below, which both evaluators decide AFTER selection.
/// The evaluator also trusts this classification for zero-parameter caching:
/// exported results are shared across the run; local-only results retain binding
/// context. Publicly constructed ASTs must supply accurate exposure themselves
/// (including <see cref="Property.RequiredAncestorParameters"/>); Evaluator.Run*
/// performs preflight but does not elaborate or reclassify them.
/// </summary>
public enum PropertyExposure
{
    /// <summary>Self-contained: evaluable wherever the property can be reached.</summary>
    Exported,

    /// <summary>
    /// The value (transitively) requires an input that only an enclosing owner's call binds —
    /// a parameter of an enclosing parameterized algorithm, or a pattern binder of an
    /// enclosing conditional branch — named by <see cref="Property.RequiredAncestorParameters"/>.
    /// Such a member is LOCAL-CONTEXT-DEPENDENT, not universally hidden: it may be used
    /// (by name, through <c>open</c>, or through dot access) from any lexical context that
    /// lies inside the owner of every required input, because that owner's activation is
    /// then the one the inherited environments carry; from a context outside such an owner
    /// the access is refused (<c>EvalError.LocalOnlyProperty</c>), never given an invented
    /// meaning. The owner is selected at the capturing reference; transitive dependencies
    /// retain that owner across intervening same-named binders (Lean: <c>memberAccessible?</c>).
    /// </summary>
    LocalOnlyCapturedAncestorParameters,

    /// <summary>
    /// The family-level reachability reason, never assigned to a property by classification:
    /// a conditional family exposes no structural members, so a name access into one of its
    /// branch bodies (<c>F.Helper</c>, <c>open F.Helper</c>) is refused with this reason
    /// (Lean: <c>conditionalBranchesDefineProperty</c>). Inside the branch, its declarations
    /// classify exactly like declarations in any other body.
    /// </summary>
    LocalOnlyConditionalAlgorithm,
}

/// <summary>
/// A named property within an algorithm, with visibility metadata.
/// Lean: PropDef { name, alg, isPublic, exposure }.
/// </summary>
public sealed record Property(
    string Name,
    Algorithm Value,
    bool IsPublic = false,
    PropertyExposure Exposure = PropertyExposure.Exported)
{
    /// <summary>
    /// Exact source spans of this property's declared name occurrences.
    /// Conditional clause families may contribute more than one declaration span.
    /// </summary>
    public IReadOnlyList<SourceSpan> DeclarationSpans { get; init; } = [];

    /// <summary>
    /// For <see cref="PropertyExposure.LocalOnlyCapturedAncestorParameters"/>: the names of
    /// the inputs the value requires that only an enclosing owner's call binds (sorted,
    /// distinct). Elaborated properties also retain exact owner positions internally so
    /// transitive captures survive shadowing. Host-built properties supplying names alone
    /// use the nearest binding owner. Access requires that owner's exact lexical activation
    /// (Lean: the diagnostic payload of
    /// <c>PropExposure.localCapturedAncestorParams</c>). Empty for exported properties. A
    /// host-built local-only property that names no required parameter states no
    /// requirement and is therefore accessible everywhere while keeping the local-only
    /// (per-binding-context) cache scope.
    /// </summary>
    public IReadOnlyList<string> RequiredAncestorParameters { get; init; } = [];

    // The diagnostic names alone cannot identify a transitive capture across a
    // same-named intervening binder. Depth is relative to this property's declaring
    // scope; null metadata preserves the nearest-owner convention of host-built trees.
    internal IReadOnlyList<CapturedParameterRequirement>? CaptureRequirements { get; init; }
}

/// <summary>
/// Represents a KatLang algorithm — the fundamental building block.
/// Discriminated union matching the Lean specification:
/// <c>Algorithm.mk</c> (user-defined), <c>Algorithm.builtin</c> (built-in operation),
/// and <c>Algorithm.conditional</c> (conditional algorithm with pattern branches).
///
/// <para><b>Variant-owned payload.</b> The base type carries NO payload: every stored
/// fact belongs to the variant that owns it, exactly as each Lean constructor carries its
/// own fields — <see cref="User"/> owns its parent, parameter patterns, opens, properties,
/// and output; <see cref="Conditional"/> owns its parent, opens, and branches; a
/// <see cref="Builtin"/> owns only its identity. Because no payload member exists on the
/// base, no <c>with</c> expression or object initializer over a base-typed value can give
/// an algorithm payload its variant does not have (a builtin with properties, a family with
/// an output, a user algorithm with branches): those states are unrepresentable in Lean's
/// inductive and are compile-time errors here. Code that holds a base-typed value
/// pattern-matches to read or update variant payload; the implementation additionally has
/// INTERNAL total read accessors (<c>AlgorithmAccessors</c>: the Lean <c>parent</c>,
/// <c>parameterPatterns</c>, <c>parameters</c>, <c>params</c>, <c>opens</c>, <c>props</c>,
/// <c>output</c>, <c>branches</c> functions), which read and never write.</para>
///
/// <para>A C# <c>closed</c> hierarchy, like the Lean inductive: <see cref="User"/>,
/// <see cref="Builtin"/>, and <see cref="Conditional"/> are its only variants, no other
/// assembly can derive from it, and a switch EXPRESSION naming all three is
/// compiler-exhaustive with no catch-all arm — the Lean-mirroring dispatches
/// (<c>withParent</c>, <c>isFunctionShaped</c>, signature and exposure classification,
/// the <c>WithParams</c> family here, the internal total accessors) name the variants a
/// case applies to instead of hiding them under <c>_</c>, so a new variant fails the build
/// there until decided.</para>
///
/// <para><b>Declaration identity.</b> Every <see cref="User"/> and <see cref="Conditional"/>
/// CONSTRUCTED with <c>new</c> is one written declaration and carries its own
/// <see cref="Declaration"/> token (Lean: <c>Algorithm.declarationId</c>, assigned once per
/// declaration at run preparation). A <c>with</c> copy is a VIEW of that same declaration —
/// the evaluator's parent wiring, the front end's elaboration passes, and a host's own
/// copies alike — and keeps the token through the record copy constructor, so no copy can
/// become a new declaration by accident and no copy needs any registration step. Two
/// declarations with identical bodies are distinct because they were constructed separately.
/// The private storage slot excludes the token from structural record equality and printing;
/// equal algorithms still hash alike. The token itself has ordinary reference equality.</para>
///
/// <para><b>Deferred-region state.</b> The one other equality-transparent fact an algorithm
/// value carries is <see cref="DeferredRegion"/>: the deferred module-elaboration region a
/// branch-body PLACEHOLDER stands for (B2c; null for every ordinary algorithm). It lives in
/// the same kind of slot, so a <c>with</c> copy of a placeholder is a view of the same
/// region with no registration step, while the front-end passes install a forked region
/// (the same loader facts plus their own context) on the output view they produce. Region
/// identity is NOT declaration identity: two placeholders cloned from one shared raw body
/// share a declaration and have two independent regions.</para>
/// </summary>
public closed record Algorithm
{
    private readonly RuntimeStateSlot<DeclarationIdentity?> _declaration;
    private readonly RuntimeStateSlot<DeferredModuleRegion?> _deferredRegion;

    private Algorithm(DeclarationIdentity? declaration)
    {
        _declaration = new(declaration);
    }

    /// <summary>
    /// The identity of the written declaration this algorithm value represents: shared by
    /// every <c>with</c> copy of one constructed <see cref="User"/> or <see cref="Conditional"/>,
    /// distinct for every separately constructed one, and null for a <see cref="Builtin"/>
    /// (Lean: <c>Algorithm.declarationId</c>, <c>none</c> for <c>.builtin</c>). Compared by
    /// reference. Runtime-only: it takes no part in record equality.
    /// </summary>
    internal DeclarationIdentity? Declaration => _declaration.Value;

    /// <summary>
    /// [HOST] B2c: the deferred module-elaboration region this algorithm value is the
    /// placeholder body of, or null for every ordinary algorithm (Lean has no counterpart:
    /// its input model has no external modules and no demand timing). Set by the module
    /// loader when it defers a load-bearing branch body, and REPLACED — never registered
    /// anywhere — by each front-end pass on the output view it produces for that placeholder
    /// (<see cref="DeferredModuleRegion.WithDetection"/> and its siblings fork the region
    /// with the pass's own context). Every <c>with</c> copy of a placeholder carries the same
    /// region object through the record copy constructor: the evaluator's parent wiring and
    /// the flat-binder equivalent of a one-clause family read the very state machine the
    /// branch body carries, so one materialization serves them all. Takes no part in record
    /// equality, hashing, or printing, and is not a structural child: no traversal follows it.
    /// </summary>
    internal DeferredModuleRegion? DeferredRegion
    {
        get => _deferredRegion.Value;
        init => _deferredRegion = new(value);
    }

    // Both slots are the ONE equality-transparent storage shape for carried state
    // (RuntimeStateSlot<T>): the record copy constructor copies the one-reference value
    // automatically, and only the PRIVATE SLOT is transparent, never the value exposed
    // above (a declaration token's ordinary Equals, dictionaries, and LINQ all retain
    // reference identity).

    /// <summary>
    /// Replace the parameter list of a user-defined algorithm by name, keeping the existing
    /// patterns of names already present and appending fresh captures for new names.
    /// Clause elaboration uses this to preserve ignored binders such as
    /// <c>K(a, b) = a</c>, where <c>b</c> must remain part of the ordinary call
    /// interface even though it is unused in the body.
    /// Lean: <c>Algorithm.withParams</c> — a TOTAL functional update that is the identity on
    /// <c>.builtin</c> and <c>.conditional</c>, which have no parameter list (this is the
    /// modeled behavior, not a fallback).
    /// </summary>
    public Algorithm WithParams(IReadOnlyList<string> parameters) => this switch
    {
        User user => user with { ParameterPatterns = MergeParameterPatterns(user.ParameterPatterns, parameters) },
        Builtin or Conditional => this,
    };

    /// <summary>
    /// <see cref="WithParams(IReadOnlyList{string})"/> with diagnostic-only
    /// provenance for the parameters that were inferred from unresolved
    /// identifiers (see <see cref="ImplicitParameterProvenance"/>). Only
    /// newly created captures consult the map; existing declared patterns are
    /// preserved untouched, so provenance can never attach to an explicit
    /// parameter.
    /// </summary>
    internal Algorithm WithParams(
        IReadOnlyList<string> parameters,
        IReadOnlyDictionary<string, ImplicitParameterProvenance>? inferredProvenance) => this switch
        {
            User user => user with
            {
                ParameterPatterns = MergeParameterPatterns(user.ParameterPatterns, parameters, inferredProvenance),
            },
            Builtin or Conditional => this,
        };

    /// <summary>
    /// Replace a user-defined algorithm's parameter list with one flat capture per
    /// declaration (Lean: <c>withParameterPatterns (ParameterPattern.fromParameters ps)</c>);
    /// the identity on <see cref="Builtin"/> and <see cref="Conditional"/>.
    /// </summary>
    public Algorithm WithParameters(IReadOnlyList<ParameterDeclaration> parameters)
        => this switch
        {
            User user => user with { ParameterPatterns = ParameterPattern.FromDeclarations(parameters) },
            Builtin or Conditional => this,
        };

    /// <summary>
    /// Replace a user-defined algorithm's stored parameter patterns — its ONE parameter
    /// channel, from which <see cref="User.Parameters"/> and <see cref="User.Params"/> are
    /// derived. Lean: <c>Algorithm.withParameterPatterns</c>, the identity on
    /// <c>.builtin</c> and <c>.conditional</c>.
    /// </summary>
    public Algorithm WithParameterPatterns(IReadOnlyList<ParameterPattern> parameterPatterns) => this switch
    {
        User user => user with { ParameterPatterns = parameterPatterns },
        Builtin or Conditional => this,
    };

    /// <summary>One flat normal capture per name. Lean: <c>Algorithm.normalParameters</c>.</summary>
    internal static IReadOnlyList<ParameterPattern> NormalParameters(IEnumerable<string> names)
        => names.Select(static name => (ParameterPattern)new CaptureParameterPattern(name)).ToList();

    internal static IReadOnlyList<ParameterPattern> MergeParameterPatterns(
        IReadOnlyList<ParameterPattern> oldPatterns,
        IReadOnlyList<string> newParameterNames,
        IReadOnlyDictionary<string, ImplicitParameterProvenance>? inferredProvenance = null)
    {
        var oldCaptures = ParameterPattern.FlattenCaptures(oldPatterns);
        if (newParameterNames.Take(oldCaptures.Count).SequenceEqual(oldCaptures.Select(static capture => capture.Name)))
        {
            var merged = oldPatterns.ToList();
            foreach (var name in newParameterNames.Skip(oldCaptures.Count))
                merged.Add(CreateMergedCapture(name, inferredProvenance));
            return merged;
        }

        // Lean's parameterForName? selects the first capture of a repeated name.
        // Host-built patterns can repeat names; total parameter updates must not throw.
        var existingByName = new Dictionary<string, ParameterDeclaration>(StringComparer.Ordinal);
        foreach (var parameter in oldCaptures)
            existingByName.TryAdd(parameter.Name, parameter);
        return newParameterNames
            .Select(name => existingByName.TryGetValue(name, out var parameter)
                ? (ParameterPattern)parameter.ToPattern()
                : CreateMergedCapture(name, inferredProvenance))
            .ToList();
    }

    private static CaptureParameterPattern CreateMergedCapture(
        string name,
        IReadOnlyDictionary<string, ImplicitParameterProvenance>? inferredProvenance)
        => new(new ParameterDeclaration(name)
        {
            InferredProvenance = inferredProvenance is not null && inferredProvenance.TryGetValue(name, out var provenance)
                ? provenance
                : null,
        });

    /// <summary>
    /// Elaborate a whole same-name clause family after all of its clauses are
    /// known. This is the real ordinary-vs-conditional decision boundary.
    ///
    /// A same-name clause group elaborates as ordinary only when it contains
    /// exactly one clause and that sole head is a supported explicit parameter pattern.
    /// Otherwise the whole family remains conditional. This is intentional:
    /// later clauses may force the entire family to stay conditional, for
    /// example <c>F(0) = 0</c> followed by <c>F(x) = 1</c>.
    /// </summary>
    public static Algorithm ElaborateClauseGroup(IReadOnlyList<CondBranch> clauses)
    {
        if (clauses.Count == 1 && clauses[0].Pattern.TryGetOrdinaryClauseParameterPatterns() is { } explicitParameterPatterns)
        {
            // Lean: `branch.body.withParameterPatterns patterns` — the written head becomes the
            // body's CLOSED explicit parameter list. The update is total: a body that is not a
            // user algorithm has no parameter list and is returned as it is (Lean's
            // withParameterPatterns is the identity on .builtin and .conditional).
            return clauses[0].Body switch
            {
                User body => body with
                {
                    ParameterPatterns = explicitParameterPatterns,
                    HasExplicitParameterList = true,
                },
                Builtin or Conditional => clauses[0].Body,
            };
        }

        if (clauses.Count == 0)
            return new Conditional(Parent: null, Opens: [], Branches: []);

        // Open ownership for a clause family is BRANCH-OWNED: an `open` written inside a
        // clause body stays owned by that branch body, which is the location every
        // consumer (parameter detection, implicit-argument resolution, exposure, and
        // evaluator lookup) actually resolves through.
        //
        // The conditional previously ALSO received `clauses[0].Body.Opens`, so clause 0's
        // open expressions stayed reachable through BOTH Conditional.Opens and
        // Branches[0].Body.Opens. That second path was redundant — emptying it changes no
        // observable behaviour — but it was actively harmful: an open target can itself
        // contain a nested algorithm (notably under malformed recovery such as an
        // unclosed `(open(...`), so the duplicate ownership made the same subtree
        // reachable by two paths per nesting level. ImplicitArgumentResolver and
        // PropertyExposureResolver rebuild each path independently, so a linear-size
        // reference DAG unfolded into an exponential (2^depth) tree.
        //
        // Giving every source-derived open exactly one owner removes the duplication at
        // its source rather than memoizing it away in every frontend visitor.
        var parent = clauses[0].Body.Parent;
        var conditionalBranches = clauses
            .Select(branch => new CondBranch(branch.Pattern, branch.Body.WithParams([])))
            .ToList();

        return new Conditional(
            parent,
            Opens: [],
            conditionalBranches);
    }

    /// <summary>
    /// Convenience wrapper for an already-known single-clause group.
    /// Front-ends must not use this while parsing a same-name clause family
    /// incrementally; they should first collect the full group and then call
    /// <see cref="ElaborateClauseGroup(IReadOnlyList{CondBranch})"/>.
    /// </summary>
    public static Algorithm ElaborateClauseDefinition(Pattern pattern, Algorithm body)
        => ElaborateClauseGroup([new CondBranch(pattern, body)]);

    /// <summary>
    /// User-defined algorithm. Corresponds to <c>Algorithm.mk</c> in the Lean specification
    /// and owns exactly its fields: <see cref="Parent"/>, <see cref="ParameterPatterns"/>,
    /// <see cref="Opens"/>, <see cref="Properties"/>, and <see cref="Output"/>.
    ///
    /// <para><b>One parameter channel.</b> <see cref="ParameterPatterns"/> is the ONE stored
    /// parameter representation (Lean's <c>parameterPatterns</c> field). The flat
    /// declaration list <see cref="Parameters"/> (Lean <c>parameters</c>) and the name list
    /// <see cref="Params"/> (Lean <c>params</c>) are LIVE projections computed from it on
    /// every read, never stored: they cannot diverge from the patterns, and a host that
    /// keeps and later mutates the caller-owned pattern list (or a nested
    /// <see cref="SequenceValueParameterPattern.Items"/> list) sees the current state through
    /// every projection and every <c>with</c> copy. Whether that list was WRITTEN as an
    /// explicit, closed parameter list is the one further fact,
    /// <see cref="HasExplicitParameterList"/>.</para>
    ///
    /// Parser elaboration may also predeclare parameters here for recursive
    /// capture/sequence-value clause syntax such as <c>Apply(f) = f(4)</c>,
    /// <c>PairSum((x, y)) = x + y</c>, or
    /// <c>CountSequenceValue((*values)) = values.count</c>.
    /// </summary>
    public sealed record User : Algorithm
    {
        public User(
            ScopeCtx? Parent,
            IReadOnlyList<ParameterPattern> ParameterPatterns,
            IReadOnlyList<Expr> Opens,
            IReadOnlyList<Property> Properties,
            OutputBundle Output)
            : base(new DeclarationIdentity())
        {
            this.Parent = Parent;
            this.ParameterPatterns = ParameterPatterns;
            this.Opens = Opens;
            this.Properties = Properties;
            this.Output = Output;
        }

        /// <summary>Lean: the <c>parent</c> field of <c>Algorithm.mk</c>.</summary>
        public ScopeCtx? Parent { get; init; }

        /// <summary>
        /// The stored top-level recursive parameter patterns for ordinary call binding —
        /// the algorithm's ONE parameter channel (Lean: the <c>parameterPatterns</c> field of
        /// <c>Algorithm.mk</c>). <see cref="Parameters"/> and <see cref="Params"/> derive from
        /// it. The list instance is caller-owned and read through on every projection.
        /// </summary>
        public IReadOnlyList<ParameterPattern> ParameterPatterns { get; init; }

        /// <summary>
        /// The flat capture declarations of <see cref="ParameterPatterns"/>, left to right and
        /// depth first, duplicates included (Lean: <c>Algorithm.parameters a =
        /// (parameterPatterns a).flatMap ParameterPattern.captures</c>). A fresh projection of
        /// the CURRENT patterns on every read, never a cache: an empty stored pattern list
        /// returns the shared empty list; flat captures use one array of stored declarations,
        /// and nested groups use the iterative flatten. Count-only consumers read
        /// <see cref="ParameterCount"/> without allocating a flattened projection (flat lists
        /// allocate nothing; nested groups use an explicit traversal stack).
        /// </summary>
        public IReadOnlyList<ParameterDeclaration> Parameters
        {
            get
            {
                var patterns = ParameterPatterns;
                var count = patterns.Count;
                if (count == 0)
                    return [];

                // Fast path for the overwhelmingly common flat list: one array of the stored
                // declarations. A nested sequence-value pattern takes the general flatten.
                var declarations = new ParameterDeclaration[count];
                for (var index = 0; index < declarations.Length; index++)
                {
                    if (patterns[index] is not CaptureParameterPattern capture)
                        return ParameterPattern.FlattenCaptures(patterns);
                    declarations[index] = capture.Parameter;
                }

                return declarations;
            }
        }

        /// <summary>
        /// The parameter names, in order, duplicates included: exactly
        /// <c>Parameters.Select(parameter => parameter.Name)</c> (Lean: <c>Algorithm.params</c>).
        /// A fresh projection of the CURRENT <see cref="ParameterPatterns"/> on every read,
        /// never a cache: a host-built algorithm keeps its caller-owned pattern list and this
        /// reads through to it (<c>LoopStrategyPreparationTests.HostOwnedCallableMetadata_*</c>),
        /// which no stored derived copy could honor. The cost stays where the evaluator pays
        /// it: an empty stored pattern list returns the shared empty list without allocating,
        /// and a flat capture list allocates one array per read. Nested groups use the
        /// iterative flatten plus a name array; they do not share the flat allocation bound.
        /// </summary>
        public IReadOnlyList<string> Params
        {
            get
            {
                var patterns = ParameterPatterns;
                var count = patterns.Count;
                if (count == 0)
                    return [];

                var names = new string[count];
                for (var index = 0; index < names.Length; index++)
                {
                    if (patterns[index] is not CaptureParameterPattern capture)
                        return NamesOf(ParameterPattern.FlattenCaptures(patterns));
                    names[index] = capture.Parameter.Name;
                }

                return names;
            }
        }

        private static string[] NamesOf(IReadOnlyList<ParameterDeclaration> parameters)
        {
            var names = new string[parameters.Count];
            for (var index = 0; index < names.Length; index++)
                names[index] = parameters[index].Name;
            return names;
        }

        /// <summary>
        /// <c>Parameters.Count</c> without materializing the projection (Lean:
        /// <c>(Algorithm.params a).length</c>): the capture count of the CURRENT
        /// <see cref="ParameterPatterns"/>, allocation-free for a flat pattern list.
        /// </summary>
        internal int ParameterCount => ParameterPattern.CountCaptures(ParameterPatterns);

        /// <summary>Lean: the <c>opens</c> field of <c>Algorithm.mk</c>.</summary>
        public IReadOnlyList<Expr> Opens { get; init; }

        /// <summary>Lean: the <c>properties</c> field of <c>Algorithm.mk</c>.</summary>
        public IReadOnlyList<Property> Properties { get; init; }

        /// <summary>
        /// The algorithm's output as an <see cref="OutputBundle"/> — ordered
        /// original written expression rows. The algorithm is the scope-owning
        /// DEFINITION of this bundle; the bundle itself owns no scope.
        /// Lean: the <c>output</c> field of <c>Algorithm.mk</c>.
        /// </summary>
        public OutputBundle Output { get; init; }

        /// <summary>
        /// True when <see cref="ParameterPatterns"/> is a WRITTEN explicit parameter list
        /// (<c>F(a, (b, c), *rest) = …</c>, or an assignment deconstruction's target helper):
        /// a CLOSED direct-call interface — the front end lifts no implicit parameter into
        /// it, reports an unresolved name inside the body as undeclared instead, and
        /// classifies every capture as an explicit parameter (<see cref="CallableParameterSource.Explicit"/>).
        /// False for an inferred (implicit) signature, whose captures were promoted from the
        /// body's unresolved names or lifted from a callee. A lifted declaration can retain
        /// the callee's source span; explicitness belongs to this owner, not the capture. Set by
        /// <see cref="ElaborateClauseGroup"/> when a single ordinary clause head becomes the
        /// body's parameter list. A front-end fact with no Lean counterpart (Lean's tree is
        /// already elaborated); it replaces the former parallel <c>ExplicitParameters</c> /
        /// <c>ExplicitParameterPatterns</c> lists, which were always either empty or equal to
        /// the stored parameter channel.
        /// </summary>
        public bool HasExplicitParameterList { get; init; }

        /// <summary>
        /// Check whether the property list contains duplicate property names.
        /// Returns the first duplicate name found, or null if all names are unique.
        /// Lean: Algorithm.findDuplicatePropName (the <c>.mk</c> case; the other
        /// constructors have no properties).
        /// </summary>
        public string? FindDuplicatePropName()
        {
            var seen = new HashSet<string>();
            foreach (var p in Properties)
            {
                if (!seen.Add(p.Name))
                    return p.Name;
            }
            return null;
        }

        private readonly object? _assignmentGroup;
        private readonly int _assignmentTargetIndex;

        /// <summary>
        /// Non-null exactly for the synthetic inline helper the parser elaborates ONE
        /// target of an assignment deconstruction (<c>x, *y, z = RHS</c>) into: the
        /// deconstruction group the helper belongs to and the index of the target it
        /// projects, as one unit (see <see cref="KatLang.AssignmentDeconstructionTarget"/>).
        /// Null for every other algorithm. Its compact private storage is copied by
        /// <c>with</c>, so record transformations preserve it without allocating metadata
        /// objects or enlarging every ordinary algorithm with a nullable struct field.
        /// Not part of the Lean model:
        /// the group and index drive a run-scoped reuse mechanism (the shared bind of
        /// the group's N targets), and the helper identity is diagnostics-only
        /// (binding failures are phrased against the written assignment pattern instead
        /// of the anonymous helper call — wording only, the structured error kind is
        /// unchanged).
        /// </summary>
        internal AssignmentDeconstructionTarget? AssignmentDeconstructionTarget
        {
            get => _assignmentGroup is { } group ? new(group, _assignmentTargetIndex) : null;
            init
            {
                if (value is { Group: null })
                    throw new ArgumentException("A deconstruction target requires a group identity.", nameof(value));
                _assignmentGroup = value?.Group;
                _assignmentTargetIndex = value?.Index ?? 0;
            }
        }

        /// <summary>
        /// Non-null exactly for the parser-synthesized <c>$deconstruct$N</c> property that
        /// hoists an assignment deconstruction's right-hand side (<c>x, *y, z = RHS</c>) so it
        /// is evaluated once and shared by the target helpers: the number of output rows the
        /// ENCLOSING body had written when the deconstruction was parsed, i.e. the right-hand
        /// side is written before that body's output row of this index (equal to the row
        /// count when it follows every row). The right-hand side is written as an expression
        /// of the enclosing body, so the front end elaborates this algorithm's output rows
        /// as rows of the enclosing algorithm IN WRITTEN ORDER (<c>AstHelpers.WrittenRows</c>
        /// merges them by this index — never by source spans, which an imported module view
        /// does not carry) — its free names become that algorithm's implicit parameters
        /// (read back through the inherited value environment) and its sibling references
        /// lift in that algorithm's context — and the property itself stays a zero-parameter
        /// shared source. Not part of the Lean model (the elaborated tree is an ordinary
        /// zero-parameter property).
        /// </summary>
        internal int? AssignmentDeconstructionRowIndex { get; init; }

        /// <summary>True for the hoisted right-hand side of an assignment deconstruction; see <see cref="AssignmentDeconstructionRowIndex"/>.</summary>
        internal bool IsAssignmentDeconstructionSource => AssignmentDeconstructionRowIndex is not null;

        /// <summary>
        /// True for a module root spliced into the tree by load elaboration — the mark of
        /// an IMPORT VIEW. The spliced module is LOCATIONLESS (<c>ModuleLoader.ToImportView</c>
        /// clears every source location of the fetched module's tree, whose spans were
        /// positioned in the MODULE's text and mean nothing in the loading document), so
        /// this mark is what the front end and the semantic model recognize an import by:
        /// a front-end diagnostic raised against imported content is positioned at the
        /// import site the pass reached the view through (<see cref="ImportSite"/>), and
        /// the semantic model treats the whole marked subtree — at every nesting depth,
        /// modules opened by the module included — as module-provided: it emits no scope
        /// regions, declaration occurrences, reference sites, or classification sites for
        /// it, and a document reference to one of its members resolves to a locationless
        /// target. When this algorithm itself is the semantic model's root, its own mark is
        /// ignored (it still carries no positions) and only nested imports are suppressed.
        /// Not part of the Lean model — no observable evaluation semantics depend on it.
        /// </summary>
        internal bool IsModuleElaborated { get; init; }
    }

    /// <summary>
    /// Built-in algorithm. Corresponds to <c>Algorithm.builtin</c> in the Lean specification
    /// and owns exactly its identity. A builtin is not a written declaration and has no
    /// <see cref="Declaration"/> token; it has no scope, parameters, properties, or output.
    /// </summary>
    public sealed record Builtin(BuiltinId Id) : Algorithm(declaration: null);

    /// <summary>
    /// Conditional algorithm with ordered pattern branches.
    /// Corresponds to <c>Algorithm.conditional</c> in the Lean specification and owns
    /// exactly its fields: <see cref="Parent"/>, <see cref="Opens"/>, and <see cref="Branches"/>
    /// (a family has no parameter list, properties, or output of its own — its branch bodies do).
    /// At call time, arguments are evaluated and matched against branch patterns
    /// in source order. The first matching branch body is evaluated.
    /// If no branch matches, evaluation fails with <c>NoMatchingBranch</c>.
    ///
    /// <para><b>Full-input-specification rule</b>: each branch pattern <c>Name(...)</c>
    /// is the complete input specification of that branch. Branch bodies do NOT
    /// infer additional implicit parameters from free identifiers. All branch inputs
    /// must appear in the pattern. Unused bound names are allowed. Grace <c>~</c> is
    /// not permitted in branch patterns or bodies.</para>
    ///
    /// <para><b>Uniform top-level arity invariant</b>: all branches of the same
    /// conditional algorithm must have the same top-level pattern arity
    /// (as defined by <see cref="Pattern.TopLevelArity"/>). Nested internal
    /// pattern structure may vary, but the outer number of inputs must remain
    /// consistent. This preserves a unified outer call interface.</para>
    ///
    /// <para><b>Uniform top-level output arity invariant</b>: all branches of the
    /// same conditional algorithm must have the same top-level output arity
    /// (as defined by <see cref="CondBranch.TopLevelOutputArity"/>). Nested
    /// internal output structure may vary, but the outer number of outputs must
    /// remain consistent. This preserves a unified output interface across
    /// branches. Conditional algorithms are not ad hoc overloading by varying
    /// result shape.</para>
    ///
    /// <para><b>Clause elaboration rule</b>: front-ends should call
    /// <see cref="ElaborateClauseGroup(IReadOnlyList{CondBranch})"/> when
    /// lowering <c>Name(pattern) = body</c>. The ordinary-vs-conditional split
    /// is decided for the whole same-name clause group, not per clause. A
    /// group elaborates to <see cref="User"/> only when it contains exactly
    /// one clause and that sole head is a supported explicit parameter pattern.
    /// Multi-clause families and literal/mixed heads such as
    /// <c>F(0) = 0</c> / <c>F(x) = 1</c> remain <see cref="Conditional"/>.</para>
    /// </summary>
    public sealed record Conditional : Algorithm
    {
        public Conditional(
            ScopeCtx? Parent,
            IReadOnlyList<Expr> Opens,
            IReadOnlyList<CondBranch> Branches)
            : base(new DeclarationIdentity())
        {
            this.Parent = Parent;
            this.Opens = Opens;
            this.Branches = Branches;
        }

        /// <summary>Lean: the <c>parent</c> field of <c>Algorithm.conditional</c>.</summary>
        public ScopeCtx? Parent { get; init; }

        /// <summary>Lean: the <c>opens</c> field of <c>Algorithm.conditional</c>.</summary>
        public IReadOnlyList<Expr> Opens { get; init; }

        /// <summary>Lean: the <c>branches</c> field of <c>Algorithm.conditional</c>.</summary>
        public IReadOnlyList<CondBranch> Branches { get; init; }

        /// <summary>
        /// Check whether the branch list contains match-equivalent patterns.
        /// Returns true if a duplicate is found.
        /// Lean: Algorithm.hasDuplicateBranchPatterns (the <c>.conditional</c> case; the
        /// other constructors have no branches).
        /// </summary>
        public bool HasDuplicateBranchPatterns()
        {
            // Single O(branches) pass: a branch duplicates an earlier one exactly when its
            // pattern fails to enter the match-equivalence set (the ordered branch list is
            // untouched). This replaces the former O(branches^2) all-pairs scan; the boolean
            // result is identical because match-equivalence is a genuine equivalence relation,
            // so one representative per class suffices for membership.
            var branches = Branches;
            if (branches.Count < 2)
                return false;

            var seen = new HashSet<Pattern>(Pattern.MatchEquivalenceComparer);
            foreach (var branch in branches)
            {
                if (!seen.Add(branch.Pattern))
                    return true;
            }
            return false;
        }
    }
}

/// <summary>
/// The assignment-deconstruction target a synthetic inline helper projects
/// (<see cref="Algorithm.User.AssignmentDeconstructionTarget"/>): <paramref name="Group"/>
/// is the stable identity token shared by all N target helpers of one
/// <c>x0, ..., x{N-1} = RHS</c> (a fresh token per deconstruction, minted at parse), by
/// which the run-scoped deconstruction binding cache binds the shared N-capture pattern
/// once per group per binding context instead of once per demanded target;
/// <paramref name="Index"/> is the zero-based position of this helper's target within
/// the group, i.e. the capture it projects out of the shared ordered bind. The two are
/// one unit because neither is meaningful without the other. Not part of the Lean model.
/// </summary>
internal readonly record struct AssignmentDeconstructionTarget(object Group, int Index);

/// <summary>
/// The identity of ONE written declaration (<see cref="Algorithm.Declaration"/>): minted by
/// the constructor of every <see cref="Algorithm.User"/> and <see cref="Algorithm.Conditional"/>
/// and carried unchanged by every record copy. Ordinary equality and hashing are REFERENCE
/// identity, including in collections. Algorithm's private storage slot excludes the token
/// from synthesized record equality; semantic consumers never see that slot. Lean:
/// <c>PropertyIdentity</c> as an <c>Algorithm.declarationId</c>, where the C# object reference
/// plays the role of the number assigned at run preparation.
/// </summary>
internal sealed class DeclarationIdentity
{
    public override string ToString()
        => $"declaration#{System.Runtime.CompilerServices.RuntimeHelpers.GetHashCode(this):x8}";
}

internal sealed record ExplicitParameterOutputViolation(SourceSpan? Span);

/// <summary>
/// One violation found by the shared pre-evaluation validation walk over a
/// preconstructed AST. Lean: the error cases of
/// <c>validateExplicitParamOutputInvariant</c> / <c>validateConditionalBranchArities</c>
/// in <c>lean/KatLang.lean</c>, which <c>runResultM</c> raises before any evaluation.
/// A C# <c>closed</c> record: its three sealed nested records are its only kinds, so the
/// evaluator's translation to <see cref="EvalError"/> names each one with no catch-all arm.
/// </summary>
internal closed record PreEvaluationAstViolation
{
    private PreEvaluationAstViolation() { }

    /// <summary>Lean: <c>Error.explicitParamsRequireOutput</c>.</summary>
    internal sealed record ExplicitParametersWithoutOutput(SourceSpan? Span) : PreEvaluationAstViolation;

    /// <summary>Lean: <c>Error.branchArityMismatch name expected actual</c>.</summary>
    internal sealed record ConditionalBranchArityMismatch(string AlgorithmName, int Expected, int Actual) : PreEvaluationAstViolation;

    /// <summary>Lean: <c>Error.branchOutputArityMismatch name expected actual</c>.</summary>
    internal sealed record ConditionalBranchOutputArityMismatch(string AlgorithmName, int Expected, int Actual) : PreEvaluationAstViolation;
}

internal static class AlgorithmValidation
{
    internal const string ExplicitParametersRequireOutputMessage =
        "This algorithm declares explicit parameters but does not define an output. Remove the algorithm parameters if it is only a container, declare parameters on the relevant property instead, or define an algorithm output.";

    public static IReadOnlyList<ExplicitParameterOutputViolation> FindExplicitParameterOutputViolations(Algorithm algorithm)
    {
        // The parser's post-parse walk reports only the explicit-parameter invariant:
        // clause elaboration already rejects conditional branch-arity mismatches with
        // richer source-positioned diagnostics, so a parsed tree cannot contain one.
        var walker = new PreEvaluationValidationWalker(stopAfterFirst: false, checkConditionalBranchArities: false);
        walker.VisitAlgorithm(algorithm);
        return [.. walker.Violations.Select(v =>
            new ExplicitParameterOutputViolation(((PreEvaluationAstViolation.ExplicitParametersWithoutOutput)v).Span))];
    }

    /// <summary>
    /// The pre-evaluation validation walk shared by every prebuilt-AST evaluator
    /// entry point. Mirrors the pass Lean's <c>runResultM</c> runs before evaluation
    /// (<c>validateExplicitParamOutputInvariantExpr</c>): one depth-first walk in
    /// Lean's traversal order that checks, at each node and in Lean's precedence,
    /// the explicit-parameters-require-output invariant and the uniform conditional
    /// branch input/output arity invariants. Returns the first violation, or
    /// <c>null</c> for a valid tree.
    /// </summary>
    public static PreEvaluationAstViolation? FindFirstPreEvaluationViolation(Expr expr)
    {
        var walker = new PreEvaluationValidationWalker(stopAfterFirst: true, checkConditionalBranchArities: true);
        walker.VisitExpr(expr);
        return walker.Violations.Count > 0 ? walker.Violations[0] : null;
    }

    private sealed class PreEvaluationValidationWalker(bool stopAfterFirst, bool checkConditionalBranchArities) : AstWalker
    {
        /// <summary>
        /// Lean's default diagnostic label for a conditional reached outside a
        /// property context (<c>validateExplicitParamOutputInvariant</c>'s
        /// <c>name := "conditional"</c> default).
        /// </summary>
        private const string AnonymousConditionalName = "conditional";

        public List<PreEvaluationAstViolation> Violations { get; } = [];

        // Nearest enclosing property name for conditional branch-arity diagnostics.
        // Lean threads it the same way: a property's directly-held algorithm (and a
        // conditional's branch bodies) inherit the property name, while any algorithm
        // reached through an EXPRESSION (block literal, call/dot-call arguments) is
        // validated by the nameless expression walker and gets the default label.
        private string _enclosingPropertyName = AnonymousConditionalName;

        // Reference-identity memo over visited algorithms and expressions. The public
        // AST is host-constructible with SHARED (acyclic) subtrees, and the violation
        // this walker detects is node-local — a shared subtree cannot contain a
        // different violation on a second visit — so revisits are pure waste: without
        // the memo a compact diamond-shaped DAG (each node referenced twice) makes
        // this pre-evaluation pass take time exponential in its depth. Walker
        // instances are per-call, so the memo is run-scoped and never shared.
        private readonly HashSet<object> _visited = new(ReferenceEqualityComparer.Instance);

        // This walker only inspects parameter COUNTS (via ParameterPatterns.Count below), never
        // individual declarations, so skip the per-declaration loop. That keeps validation of a wide
        // assignment deconstruction linear instead of O(N^2) across its N synthetic N-capture helpers.
        protected override bool VisitsExplicitParameterDeclarations => false;

        public override void VisitAlgorithm(Algorithm algorithm)
        {
            if (stopAfterFirst && Violations.Count > 0)
                return;

            if (!_visited.Add(algorithm))
                return;

            base.VisitAlgorithm(algorithm);
        }

        public override void VisitExpr(Expr expr)
        {
            if (stopAfterFirst && Violations.Count > 0)
                return;

            if (!_visited.Add(expr))
                return;

            // Expression descent is nameless in Lean, so any algorithm reached
            // below this point gets the default conditional label. Restore the
            // enclosing name afterwards: a conditional's opens are visited before
            // its branch bodies, and those bodies must keep the conditional's name.
            var enclosingName = _enclosingPropertyName;
            _enclosingPropertyName = AnonymousConditionalName;

            if (expr is Expr.SequenceConstruct or Expr.SequenceSpread)
                VisitFlatOutputExpr(expr);
            else
                base.VisitExpr(expr);

            _enclosingPropertyName = enclosingName;
        }

        private void VisitFlatOutputExpr(Expr expr)
        {
            var stack = new Stack<Expr>();
            stack.Push(expr);

            while (stack.Count != 0)
            {
                if (stopAfterFirst && Violations.Count > 0)
                    return;

                var current = stack.Pop();
                if (current is Expr.SequenceConstruct(var outputLeft, var outputRight))
                {
                    if (!ReferenceEquals(current, expr) && !_visited.Add(current))
                        continue;

                    stack.Push(outputRight);
                    stack.Push(outputLeft);
                    continue;
                }

                if (current is Expr.SequenceSpread(var spreadOperand))
                {
                    if (!ReferenceEquals(current, expr) && !_visited.Add(current))
                        continue;

                    stack.Push(spreadOperand);
                    continue;
                }

                VisitExpr(current);
            }
        }

        protected override void VisitUserAlgorithm(Algorithm.User algorithm)
        {
            // Test the STORED parameter-pattern list, Lean's actual Algorithm.mk field
            // (validateExplicitParamOutputInvariant checks !parameterPatterns.isEmpty):
            // a legal pattern may contain zero captures (SequenceValueParameterPattern([])),
            // so the flattened Parameters list can be empty while an explicit parameter
            // pattern exists. Not Params.Count either: Params is a computed property that
            // materializes a fresh O(N) name list on every access, so touching it once per
            // algorithm makes walking a wide assignment deconstruction's N synthetic helpers
            // O(N^2). ParameterPatterns is a stored list, so this stays an O(1) count check.
            if (algorithm.ParameterPatterns.Count > 0 && algorithm.Output.Count == 0)
            {
                // The diagnostic points at the first WRITTEN parameter; an inferred signature has no
                // source-backed declaration to point at.
                var span = algorithm.HasExplicitParameterList ? algorithm.Parameters.FirstOrDefault()?.Span : null;
                Violations.Add(new PreEvaluationAstViolation.ExplicitParametersWithoutOutput(span));
                if (stopAfterFirst)
                    return;
            }

            base.VisitUserAlgorithm(algorithm);
        }

        protected override void VisitProperty(Property property)
        {
            // Lean: validateExplicitParamOutputInvariant prop.alg prop.name — the
            // property's directly-held algorithm is validated under the property name.
            var enclosingName = _enclosingPropertyName;
            _enclosingPropertyName = property.Name;
            base.VisitProperty(property);
            _enclosingPropertyName = enclosingName;
        }

        protected override void VisitConditionalAlgorithm(Algorithm.Conditional algorithm)
        {
            // Lean: validateConditionalBranchArities runs BEFORE the conditional's
            // opens and branch bodies are walked.
            if (checkConditionalBranchArities)
                ValidateConditionalBranchArities(algorithm);

            if (stopAfterFirst && Violations.Count > 0)
                return;

            base.VisitConditionalAlgorithm(algorithm);
        }

        /// <summary>
        /// Lean: <c>Algorithm.validateBranchArities</c> then
        /// <c>Algorithm.validateBranchOutputArities</c> — expected comes from the
        /// first branch, actual from the first mismatching branch, and an input-arity
        /// mismatch suppresses the output-arity check for the same conditional.
        /// </summary>
        private void ValidateConditionalBranchArities(Algorithm.Conditional algorithm)
        {
            var branches = algorithm.Branches;
            if (branches.Count == 0)
                return;

            var expectedArity = branches[0].Pattern.TopLevelArity();
            for (var i = 1; i < branches.Count; i++)
            {
                var actualArity = branches[i].Pattern.TopLevelArity();
                if (actualArity != expectedArity)
                {
                    Violations.Add(new PreEvaluationAstViolation.ConditionalBranchArityMismatch(
                        _enclosingPropertyName, expectedArity, actualArity));
                    return;
                }
            }

            var expectedOutputArity = branches[0].TopLevelOutputArity();
            for (var i = 1; i < branches.Count; i++)
            {
                var actualOutputArity = branches[i].TopLevelOutputArity();
                if (actualOutputArity != expectedOutputArity)
                {
                    Violations.Add(new PreEvaluationAstViolation.ConditionalBranchOutputArityMismatch(
                        _enclosingPropertyName, expectedOutputArity, actualOutputArity));
                    return;
                }
            }
        }
    }
}

// ── ScopeCtx (Lean: ScopeCtx) ─────────────────────────────────────────────

/// <summary>
/// Scope context used during evaluation for name resolution.
/// Populated by the evaluator, not the parser.
/// <para><see cref="Parameters"/> are the parameter names the scope's algorithm binds — its
/// explicit and inferred parameters, or, on the family scope a conditional call wires the
/// selected branch body under, the matched pattern binders. They take no part in property
/// lookup; they let the accessibility check of a local-only member find the owner of each
/// required input by the same nearest-owner walk the front end elaborated the reference with
/// (Lean: <c>ScopeCtx.params</c>, <c>requiredParameterOwner?</c>).</para>
/// <para>An evaluator-wired scope additionally carries its runtime OWNERSHIP —
/// <see cref="Owner"/>, the algorithm it was wired from (and through it the
/// <see cref="Declaration"/> the scope is a level of), and <see cref="Activation"/>, the call
/// of that owner it belongs to, if any (Lean: <c>ScopeCtx.declarationId</c> and
/// <c>ScopeCtx.activation</c>, plus the owner's <c>output</c>/<c>branches</c> components).
/// Ownership is internal runtime state: a host-constructed scope has none, and structural
/// equality — the public positional components — never sees it.</para>
/// </summary>
public sealed record ScopeCtx(
    ScopeCtx? Parent,
    IReadOnlyList<Expr> Opens,
    IReadOnlyList<Property> Properties,
    IReadOnlyList<string> Parameters)
{
    /// <summary>A scope whose algorithm binds no parameters.</summary>
    public ScopeCtx(
        ScopeCtx? Parent,
        IReadOnlyList<Expr> Opens,
        IReadOnlyList<Property> Properties)
        : this(Parent, Opens, Properties, [])
    {
    }

    /// <summary>
    /// The algorithm this scope was wired from — the owner whose opens, properties, and
    /// parameters (or matched binders) the scope publishes — or null for a scope a host
    /// constructed directly. Every evaluator-created scope has one; the owner's
    /// <see cref="Algorithm.Declaration"/> is this scope's declaration identity.
    /// </summary>
    internal Algorithm? Owner { get; init; }

    /// <summary>
    /// The activation of the owner's call this scope belongs to: the parameter bindings
    /// captured when that call entered its body (or matched its clause), read by every
    /// captured-parameter reference and compared by identity by the accessibility law. Null
    /// for a static scope or a parameterless user-body entry. A matched clause always
    /// has an activation, including when its pattern binds no names.
    /// </summary>
    internal ParameterActivation? Activation { get; init; }

    /// <summary>The identity of the declaration this scope is a level of; null without an owner or for a builtin owner.</summary>
    internal DeclarationIdentity? Declaration => Owner?.Declaration;

    /// <summary>
    /// Structural equality over the positional components only. The runtime ownership
    /// members (<see cref="Owner"/>, <see cref="Activation"/>) are deliberately excluded:
    /// two rebuilt scopes of one declaring scope are equal whichever call they belong to.
    /// </summary>
    public bool Equals(ScopeCtx? other)
        => ReferenceEquals(this, other)
            || (other is not null
                && EqualityComparer<ScopeCtx?>.Default.Equals(Parent, other.Parent)
                && EqualityComparer<IReadOnlyList<Expr>>.Default.Equals(Opens, other.Opens)
                && EqualityComparer<IReadOnlyList<Property>>.Default.Equals(Properties, other.Properties)
                && EqualityComparer<IReadOnlyList<string>>.Default.Equals(Parameters, other.Parameters));

    public override int GetHashCode()
        => HashCode.Combine(Parent, Opens, Properties, Parameters);

    /// <summary>Preserves the original three-component deconstruction contract.</summary>
    public void Deconstruct(
        out ScopeCtx? Parent,
        out IReadOnlyList<Expr> Opens,
        out IReadOnlyList<Property> Properties)
    {
        Parent = this.Parent;
        Opens = this.Opens;
        Properties = this.Properties;
    }
}
