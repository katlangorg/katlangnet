namespace KatLang;

// ── Operators (Lean: BinaryOp, UnaryOp) ─────────────────────────────────────

public enum BinaryOp { Add, Sub, Mul, Div, IDiv, Mod, Pow, Lt, Gt, Le, Ge, Eq, Ne, And, Or, Xor }

public enum UnaryOp { Minus, Not }

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
/// exact immutable list value.
/// <c>atoms(value)</c> recursively collects numeric atoms depth-first, left to
/// right, through both sequence and exact-list boundaries (strings and other
/// non-numeric leaves contribute no atoms) and materializes them as one exact
/// immutable list value; it does not use the post-binding collection view and
/// it does not define truthiness — truth testing stays list-opaque.
/// <c>filter(collection, predicate)</c> keeps the original top-level sequence
/// items whose predicate returns exactly one atomic numeric truth value after
/// seeing each callback item through the same one-level projection rule as
/// <c>S:i</c>, then materializes the kept items as one exact list value.
/// <c>map(collection, mapper)</c> maps top-level sequence items left to right;
/// each callback item follows the same one-level projection rule as
/// <c>S:i</c>, <c>mapper(element)</c> must return exactly one mapped
/// element, and sequence/list mapped outputs are preserved whole as exact
/// elements of one list result.
/// <c>count(collection)</c> counts the top-level sequence items exposed by direct
/// sequence consumption; sequence-value top-level elements still count as one element.
/// <c>contains(collection, item)</c> returns <c>1</c> when any top-level sequence
/// item equals <c>item</c> under ordinary KatLang value equality, otherwise
/// <c>0</c>; sequence values compare as sequence values and are not searched
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
/// to right; the current callback item follows the same one-level projection
/// rule as <c>S:i</c>, <c>reducer(element, accumulator)</c> must return exactly
/// one next accumulator value, and sequence-value accumulators are preserved whole.
/// </summary>
public enum BuiltinId { @if, @while, @repeat, @atoms, @range, @filter, @map, @order, @orderDesc, @count, @contains, @first, @last, @distinct, @take, @skip, @min, @max, @sum, @avg, @reduce }

// ── Source span ──────────────────────────────────────────────────────────────

/// <summary>
/// Source location of an expression or error. Lines and columns are 1-based,
/// and end positions are inclusive.
/// </summary>
public sealed record SourceSpan(
    int StartLineNumber, int StartColumn,
    int EndLineNumber, int EndColumn);

/// <summary>
/// Algorithm parameter metadata.
/// Source spans are populated for explicit clause binders that elaborate to an
/// ordinary <see cref="Algorithm.User"/>. Implicit parameters inferred later by
/// <see cref="ParameterDetector"/> have no source declaration span.
/// </summary>
public enum ParameterKind
{
    Normal,
    Collecting,
}

public sealed record ParameterDeclaration(string Name, SourceSpan? Span = null, ParameterKind Kind = ParameterKind.Normal)
{
    /// <summary>Exact span of the source prefix <c>*</c> collect marker, when source-backed.</summary>
    public SourceSpan? CollectMarkerSpan { get; init; }

    public string DisplayName => Kind switch
    {
        ParameterKind.Collecting => $"*{Name}",
        _ => Name,
    };

    public CaptureParameterPattern ToPattern() => new(Name, Span, Kind)
    {
        CollectMarkerSpan = CollectMarkerSpan,
    };
}

/// <summary>
/// Recursive explicit parameter pattern for ordinary user-call binding.
/// Capture nodes bind names; sequence-value nodes preserve one parent-level
/// slot and destructure that slot's immediate sequence elements.
/// </summary>
public abstract record ParameterPattern
{
    private protected ParameterPattern() { }

    public abstract string DisplayName { get; }

    public abstract IReadOnlyList<ParameterDeclaration> Captures { get; }

    public bool ContainsCollectingCapture => Captures.Any(static capture => capture.Kind == ParameterKind.Collecting);

    public static IReadOnlyList<ParameterPattern> FromDeclarations(IEnumerable<ParameterDeclaration> parameters)
        => parameters.Select(static parameter => parameter.ToPattern()).ToList();

    public static IReadOnlyList<ParameterDeclaration> FlattenCaptures(IEnumerable<ParameterPattern> patterns)
        => patterns.SelectMany(static pattern => pattern.Captures).ToList();

    public static bool HasCollectingCaptureAtCurrentLevel(IEnumerable<ParameterPattern> patterns)
        => patterns.Count(static pattern => pattern is CaptureParameterPattern { Kind: ParameterKind.Collecting }) > 0;

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

public sealed record CaptureParameterPattern(string Name, SourceSpan? Span = null, ParameterKind Kind = ParameterKind.Normal)
    : ParameterPattern
{
    /// <summary>Exact span of the source prefix <c>*</c> collect marker, when source-backed.</summary>
    public SourceSpan? CollectMarkerSpan { get; init; }

    public override string DisplayName => Kind == ParameterKind.Collecting ? $"*{Name}" : Name;

    public override IReadOnlyList<ParameterDeclaration> Captures =>
    [
        new(Name, Span, Kind)
        {
            CollectMarkerSpan = CollectMarkerSpan,
        }
    ];
}

public sealed record SequenceValueParameterPattern(IReadOnlyList<ParameterPattern> Items)
    : ParameterPattern
{
    public override string DisplayName => $"({string.Join(", ", Items.Select(static item => item.DisplayName))})";

    /// <summary>
    /// Left-to-right depth-first capture flatten, walked with an explicit stack:
    /// parameter patterns are host-constructible to arbitrary depth, and this public
    /// convenience must not recurse on the caller's stack (a recursive flatten
    /// overflowed the process on deep host-built patterns). Capture order, duplicate
    /// names, and the produced declarations are identical to the recursive flatten.
    /// </summary>
    public override IReadOnlyList<ParameterDeclaration> Captures
    {
        get
        {
            var captures = new List<ParameterDeclaration>();
            var pending = new Stack<ParameterPattern>();
            for (var i = Items.Count - 1; i >= 0; i--)
                pending.Push(Items[i]);

            while (pending.Count > 0)
            {
                switch (pending.Pop())
                {
                    case CaptureParameterPattern capture:
                        captures.Add(new ParameterDeclaration(capture.Name, capture.Span, capture.Kind)
                        {
                            CollectMarkerSpan = capture.CollectMarkerSpan,
                        });
                        break;
                    case SequenceValueParameterPattern group:
                        for (var i = group.Items.Count - 1; i >= 0; i--)
                            pending.Push(group.Items[i]);
                        break;
                }
            }

            return captures;
        }
    }
}

// ── Expressions (Lean: Expr) ────────────────────────────────────────────────

/// <summary>
/// Abstract base for all KatLang expressions.
/// Each sealed nested record corresponds to a constructor in the Lean <c>Expr</c> inductive.
/// </summary>
public abstract record Expr
{
    /// <summary>Source location of this expression, populated by the parser.</summary>
    public SourceSpan? Span { get; init; }

    private Expr() { }

    /// <summary>Refers to a parameter declared in the enclosing algorithm.</summary>
    public sealed record Param(string Name) : Expr;

    /// <summary>Numeric literal.</summary>
    public sealed record Num(decimal Value) : Expr;

    /// <summary>String literal. Evaluates to <c>Result.Str</c> (first-class string value).
    /// Also used for compile-time directives (e.g. load URLs) which are eliminated by elaboration.</summary>
    public sealed record StringLiteral(string Value) : Expr;

    /// <summary>Unary expression (currently only minus).</summary>
    public sealed record Unary(UnaryOp Op, Expr Operand) : Expr;

    /// <summary>Binary arithmetic or comparison expression.</summary>
    public sealed record Binary(BinaryOp Op, Expr Left, Expr Right) : Expr;

    /// <summary>Output selection. <c>Index(a, i)</c> selects top-level item <c>i</c> from evaluated output of <c>a</c> and projects that item's content one level.</summary>
    public sealed record Index(Expr Target, Expr Selector) : Expr;

    /// <summary>
    /// INTERNAL sequence-join node retained for semantic AST compatibility
    /// with the Lean model. Surface spreading is the attached postfix
    /// spread marker <c>expr*</c> (<see cref="SequenceSpread"/>), never
    /// this node.
    ///
    /// This is NOT the AST representation of written sequence-value syntax:
    /// the parser and all production transformations have ZERO ORIGIN SITES
    /// for it — parenthesized lists parse to <see cref="Block"/> and <c>()</c>
    /// to <see cref="EmptySequence"/>; elaboration visitors may REBUILD an
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
    /// empty sequence are useful-structure canonicalized back to <c>()</c>.
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
    /// exact immutable list value (<see cref="Result.ListValue"/>). Element
    /// slots follow the same expression-list rules as written parentheses (an
    /// explicit spread slot opens its operand's immediate items, a non-spread
    /// <c>()</c> slot stays one visible element), but the collected elements
    /// are stored EXACTLY: no singleton erasure and no empty canonicalization,
    /// so <c>[7]</c>, <c>[[7]]</c>, and <c>[]</c> are all distinct values.
    /// Lean: <c>listLiteral : List Expr → Expr</c>.
    /// </summary>
    public sealed record ListLiteral(IReadOnlyList<Expr> Items) : Expr;

    /// <summary>Resolves a named algorithm by lexical lookup.</summary>
    public sealed record Resolve(string Name) : Expr;

    /// <summary>
    /// Extension call syntax. <c>DotCall(a, "f", args?)</c> represents <c>a.f</c> or <c>a.f(args)</c>
    /// with smart resolution: property access when f has 0 params, otherwise call with receiver.
    /// Lean: <c>dotCall : Expr → Ident → Option Algorithm → Expr</c>.
    /// </summary>
    public sealed record DotCall(Expr Target, string Name, Algorithm? Args = null) : Expr
    {
        /// <summary>
        /// Exact span of the member identifier to the right of the dot when the
        /// parser has source information for it.
        /// </summary>
        public SourceSpan? MemberSpan { get; init; }
    }

    /// <summary>
    /// Grace weight annotation. <c>Grace(inner, w)</c> marks an identifier with reordering weight.
    /// Prefix <c>~x</c> → weight -1, postfix <c>x~</c> → weight +1. Consumed by ParameterDetector.
    /// Not part of the Lean specification.
    /// </summary>
    public sealed record Grace(Expr Inner, int Weight) : Expr;

    /// <summary>Anonymous algorithm literal.</summary>
    public sealed record Block(Algorithm Algorithm) : Expr;

    /// <summary>Algorithm application. <c>Call(f, args)</c> applies <c>f</c> to outputs of <c>args</c>.</summary>
    public sealed record Call(Expr Function, Algorithm Args) : Expr;

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
/// </summary>
public abstract record Pattern
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
    public sealed record LitInt(decimal Value) : Pattern;

    /// <summary>Matches only <c>Result.Str(s)</c> where s equals <see cref="Value"/> (exact string equality).</summary>
    public sealed record LitString(string Value) : Pattern;

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

                case (LitInt leftInt, LitInt rightInt):
                    return leftInt.Value == rightInt.Value;

                case (LitString leftString, LitString rightString):
                    return string.Equals(leftString.Value, rightString.Value, StringComparison.Ordinal);

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
                        foreach (var component in decimal.GetBits(litInt.Value))
                            Mix((uint)component);
                        break;
                    case LitString litString:
                        Mix(3);
                        Mix((uint)litString.Value.Length);
                        foreach (var ch in litString.Value)
                            Mix(ch);
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
/// A named property within an algorithm, with visibility metadata.
/// Lean: PropDef { name, alg, isPublic }.
/// </summary>
public enum PropertyExposure
{
    Exported,
    LocalOnlyCapturedAncestorParameters,
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
}

/// <summary>
/// Represents a KatLang algorithm — the fundamental building block.
/// Discriminated union matching the Lean specification:
/// <c>Algorithm.mk</c> (user-defined), <c>Algorithm.builtin</c> (built-in operation),
/// and <c>Algorithm.conditional</c> (conditional algorithm with pattern branches).
///
/// Virtual properties provide Lean-style accessors that return defaults for Builtin variant
/// (null/[] as appropriate), matching Lean's Algorithm.parent, Algorithm.parameters, etc.
/// </summary>
public abstract record Algorithm
{
    private Algorithm() { }

    /// <summary>Lean: Algorithm.parent. Returns null for Builtin.</summary>
    public virtual ScopeCtx? Parent { get; init; }

    /// <summary>Lean: Algorithm.parameters. Returns [] for Builtin.</summary>
    public virtual IReadOnlyList<ParameterDeclaration> Parameters { get; init; } = [];

    /// <summary>Top-level recursive parameter patterns for ordinary call binding.</summary>
    public virtual IReadOnlyList<ParameterPattern> ParameterPatterns { get; init; } = [];

    /// <summary>Lean: Algorithm.params. Derived parameter names; returns [] for Builtin.</summary>
    public virtual IReadOnlyList<string> Params => ParameterNames(Parameters);

    /// <summary>Lean: Algorithm.opens. Returns [] for Builtin.</summary>
    public virtual IReadOnlyList<Expr> Opens { get; init; } = [];

    /// <summary>Lean: Algorithm.props. Returns [] for Builtin.</summary>
    public virtual IReadOnlyList<Property> Properties { get; init; } = [];

    /// <summary>Lean: Algorithm.output. Returns [] for Builtin and Conditional.</summary>
    public virtual IReadOnlyList<Expr> Output { get; init; } = [];

    /// <summary>Lean: Algorithm.branches. Returns [] for non-Conditional algorithms.</summary>
    public virtual IReadOnlyList<CondBranch> Branches { get; init; } = [];

    /// <summary>
    /// Source-backed metadata for explicit parameters already represented in
    /// <see cref="Parameters"/>. This is not an alternate call interface;
    /// implicit parameters inferred later have no source declaration here.
    /// </summary>
    public virtual IReadOnlyList<ParameterDeclaration> ExplicitParameters { get; init; } = [];

    /// <summary>Source-backed explicit top-level parameter patterns.</summary>
    public virtual IReadOnlyList<ParameterPattern> ExplicitParameterPatterns { get; init; } = [];

    /// <summary>
    /// Check whether the property list contains duplicate property names.
    /// Returns the first duplicate name found, or null if all names are unique.
    /// Lean: Algorithm.findDuplicatePropName.
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

    /// <summary>
    /// Check whether the branch list contains match-equivalent patterns.
    /// Returns true if a duplicate is found.
    /// Lean: Algorithm.hasDuplicateBranchPatterns.
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

    /// <summary>
    /// Parser annotation: true when this algorithm should have parameters detected
    /// (property bodies, <c>{}</c> blocks, root algorithm).
    /// Not part of the Lean specification.
    /// </summary>
    internal virtual bool IsParametrized { get; init; }

    /// <summary>
    /// Replace the explicit parameter list of a user-defined algorithm.
    /// Clause elaboration uses this to preserve ignored binders such as
    /// <c>K(a, b) = a</c>, where <c>b</c> must remain part of the ordinary call
    /// interface even though it is unused in the body.
    /// </summary>
    public Algorithm WithParams(IReadOnlyList<string> parameters) => this switch
    {
        User user => user.WithParameterPatternList(MergeParameterPatterns(user.ParameterPatterns, parameters)),
        _ => this,
    };

    public Algorithm WithParameters(IReadOnlyList<ParameterDeclaration> parameters) => this switch
    {
        User user => user.WithParameterPatternList(ParameterPattern.FromDeclarations(parameters)),
        _ => this,
    };

    public Algorithm WithParameterPatterns(IReadOnlyList<ParameterPattern> parameterPatterns) => this switch
    {
        User user => user.WithParameterPatternList(parameterPatterns),
        _ => this,
    };

    internal static IReadOnlyList<ParameterDeclaration> NormalParameters(IEnumerable<string> names)
        => names.Select(static name => new ParameterDeclaration(name)).ToList();

    private static IReadOnlyList<string> ParameterNames(IEnumerable<ParameterDeclaration> parameters)
        => parameters.Select(static parameter => parameter.Name).ToList();

    internal static IReadOnlyList<ParameterDeclaration> MergeParameters(
        IReadOnlyList<ParameterDeclaration> oldParameters,
        IReadOnlyList<string> newParameterNames)
    {
        var existingByName = oldParameters.ToDictionary(
            static parameter => parameter.Name,
            StringComparer.Ordinal);
        return newParameterNames
            .Select(name => existingByName.TryGetValue(name, out var parameter)
                ? parameter
                : new ParameterDeclaration(name))
            .ToList();
    }

    internal static IReadOnlyList<ParameterPattern> MergeParameterPatterns(
        IReadOnlyList<ParameterPattern> oldPatterns,
        IReadOnlyList<string> newParameterNames)
    {
        var oldCaptures = ParameterPattern.FlattenCaptures(oldPatterns);
        if (newParameterNames.Take(oldCaptures.Count).SequenceEqual(oldCaptures.Select(static capture => capture.Name)))
        {
            var merged = oldPatterns.ToList();
            foreach (var name in newParameterNames.Skip(oldCaptures.Count))
                merged.Add(new CaptureParameterPattern(name));
            return merged;
        }

        var existingByName = oldCaptures.ToDictionary(
            static parameter => parameter.Name,
            StringComparer.Ordinal);
        return newParameterNames
            .Select(name => existingByName.TryGetValue(name, out var parameter)
                ? parameter.ToPattern()
                : new CaptureParameterPattern(name))
            .ToList();
    }

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
            var explicitParameters = ParameterPattern.FlattenCaptures(explicitParameterPatterns);
            return clauses[0].Body.WithParameterPatterns(explicitParameterPatterns) with
            {
                ExplicitParameterPatterns = explicitParameterPatterns,
                ExplicitParameters = explicitParameters,
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
    /// User-defined algorithm. Corresponds to <c>Algorithm.mk</c> in the Lean specification.
    /// Parser elaboration may also predeclare parameters here for recursive
    /// capture/sequence-value clause syntax such as <c>Apply(f) = f(4)</c>,
    /// <c>PairSum((x, y)) = x + y</c>, or
    /// <c>CountSequenceValue((*values)) = values.count</c>.
    /// </summary>
    public sealed record User : Algorithm
    {
        public User(
            ScopeCtx? Parent,
            IReadOnlyList<ParameterDeclaration> Parameters,
            IReadOnlyList<Expr> Opens,
            IReadOnlyList<Property> Properties,
            IReadOnlyList<Expr> Output)
        {
            this.Parent = Parent;
            this.Parameters = Parameters;
            this.ParameterPatterns = ParameterPattern.FromDeclarations(Parameters);
            this.Opens = Opens;
            this.Properties = Properties;
            this.Output = Output;
        }

        public override ScopeCtx? Parent { get; init; }
        public override IReadOnlyList<ParameterDeclaration> Parameters { get; init; } = [];
        public override IReadOnlyList<ParameterPattern> ParameterPatterns { get; init; } = [];
        public override IReadOnlyList<string> Params => ParameterNames(Parameters);
        public override IReadOnlyList<Expr> Opens { get; init; } = [];
        public override IReadOnlyList<Property> Properties { get; init; } = [];
        public override IReadOnlyList<Expr> Output { get; init; } = [];
        internal override bool IsParametrized { get; init; }

        /// <summary>
        /// True for the synthetic inline helper the parser elaborates an
        /// assignment deconstruction (<c>x, *y, z = RHS</c>) into.
        /// Diagnostics-only metadata: binding failures are phrased against the
        /// written assignment pattern instead of the anonymous helper call.
        /// Never encoded to the Lean model (wording-only, the structured error
        /// kind is unchanged).
        /// </summary>
        internal bool IsAssignmentDeconstructionHelper { get; init; }

        /// <summary>
        /// Stable per-deconstruction identity token shared by all N target helpers of one
        /// <c>x0, ..., x{N-1} = RHS</c> (a fresh token per deconstruction, assigned at parse).
        /// The run-scoped deconstruction binding cache groups the N helpers by this token so the
        /// shared N-capture pattern is bound once per group per binding context instead of once
        /// per demanded target. It is a plain reference field copied by <c>with</c>, so record
        /// transformations provably preserve it; only meaningful when
        /// <see cref="IsAssignmentDeconstructionHelper"/> is true. Not part of the Lean model
        /// (a run-scoped reuse mechanism, no observable-semantics effect).
        /// </summary>
        internal object? AssignmentDeconstructionGroup { get; init; }

        /// <summary>
        /// Zero-based position of this helper's target within its deconstruction group, i.e. the
        /// capture index this helper projects out of the shared ordered bind. Only meaningful
        /// when <see cref="IsAssignmentDeconstructionHelper"/> is true.
        /// </summary>
        internal int AssignmentDeconstructionTargetIndex { get; init; }

        internal User WithParameterPatternList(IReadOnlyList<ParameterPattern> parameterPatterns)
            => this with
            {
                ParameterPatterns = parameterPatterns,
                Parameters = ParameterPattern.FlattenCaptures(parameterPatterns),
            };
    }

    /// <summary>
    /// Built-in algorithm. Corresponds to <c>Algorithm.builtin</c> in the Lean specification.
    /// </summary>
    public sealed record Builtin(BuiltinId Id) : Algorithm;

    /// <summary>
    /// Conditional algorithm with ordered pattern branches.
    /// Corresponds to <c>Algorithm.conditional</c> in the Lean specification.
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
        {
            this.Parent = Parent;
            this.Opens = Opens;
            this.Branches = Branches;
        }

        public override ScopeCtx? Parent { get; init; }
        public override IReadOnlyList<Expr> Opens { get; init; } = [];
        public override IReadOnlyList<CondBranch> Branches { get; init; } = [];
    }
}

internal sealed record ExplicitParameterOutputViolation(SourceSpan? Span);

/// <summary>
/// One violation found by the shared pre-evaluation validation walk over a
/// preconstructed AST. Lean: the error cases of
/// <c>validateExplicitParamOutputInvariant</c> / <c>validateConditionalBranchArities</c>
/// in <c>lean/KatLang.lean</c>, which <c>runResultM</c> raises before any evaluation.
/// </summary>
internal abstract record PreEvaluationAstViolation
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

        // This walker only inspects parameter COUNTS (via Parameters.Count below), never individual
        // declarations, so skip the per-declaration loop. That keeps validation of a wide assignment
        // deconstruction linear instead of O(N^2) across its N synthetic N-capture helpers.
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
            // Use Parameters.Count, not Params.Count: Params is a computed property that
            // materializes a fresh O(N) name list on every access, so touching it once per
            // algorithm makes walking a wide assignment deconstruction's N synthetic helpers
            // O(N^2). Params is derived from Parameters, so the counts are always equal.
            if (algorithm.Parameters.Count > 0 && algorithm.Output.Count == 0)
            {
                var span = algorithm.ExplicitParameters.FirstOrDefault()?.Span;
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
/// </summary>
public sealed record ScopeCtx(
    ScopeCtx? Parent,
    IReadOnlyList<Expr> Opens,
    IReadOnlyList<Property> Properties);
