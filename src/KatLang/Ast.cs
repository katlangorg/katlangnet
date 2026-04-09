namespace KatLang;

// ── Operators (Lean: BinaryOp, UnaryOp) ─────────────────────────────────────

public enum BinaryOp { Add, Sub, Mul, Div, IDiv, Mod, Pow, Lt, Gt, Le, Ge, Eq, Ne, And, Or, Xor }

public enum UnaryOp { Minus, Not }

// ── Built-in identifiers (Lean: Builtin) ────────────────────────────────────

/// <summary>
/// <c>if</c> supports both 2-arg (conditional output) and 3-arg (if-then-else).
/// 2-arg: <c>if(cond, value)</c> — true returns value, false returns empty output (<c>Result.Group([])</c>).
/// 3-arg: <c>if(cond, then, else)</c> — standard conditional.
/// <c>filter(collection, predicate)</c> keeps the original top-level collection
/// elements whose predicate returns exactly one atomic numeric truth value;
/// grouped elements are preserved whole and rejected elements are omitted entirely.
/// <c>map(collection, transform)</c> maps top-level collection elements left to
/// right; <c>transform(element)</c> must return exactly one mapped element, and
/// grouped input/output elements are preserved whole.
/// <c>count(collection)</c> counts top-level collection elements left to right;
/// each atom, string, or grouped value counts as one element, grouped values
/// are not flattened, and empty collections return <c>0</c>.
/// <c>min(collection)</c> compares top-level numeric collection elements left
/// to right; the collection must be non-empty, each element must be exactly one
/// atomic numeric value, and grouped values are not flattened.
/// <c>max(collection)</c> compares top-level numeric collection elements left
/// to right; the collection must be non-empty, each element must be exactly one
/// atomic numeric value, and grouped values are not flattened.
/// <c>sum(collection)</c> adds top-level collection elements left to right;
/// each element must be exactly one atomic numeric value, grouped values are
/// not flattened, and empty collections return <c>0</c>.
/// <c>avg(collection)</c> averages top-level collection elements left to
/// right; the collection must be non-empty, each element must be exactly one
/// atomic numeric value, and grouped values are not flattened.
/// <c>reduce(collection, step, initial)</c> folds top-level collection elements
/// left to right; <c>step(element, accumulator)</c> must return exactly one
/// next accumulator value, and grouped elements/accumulators are preserved whole.
/// </summary>
public enum BuiltinId { @if, @while, @repeat, @atoms, @range, @filter, @map, @count, @min, @max, @sum, @avg, @reduce }

// ── Source span ──────────────────────────────────────────────────────────────

/// <summary>
/// Source location of an expression or error. All values are 1-based.
/// </summary>
public sealed record SourceSpan(
    int StartLineNumber, int StartColumn,
    int EndLineNumber, int EndColumn);

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

    /// <summary>Output selection. <c>Index(a, i)</c> selects element <c>i</c> from evaluated output of <c>a</c>.</summary>
    public sealed record Index(Expr Target, Expr Selector) : Expr;

    /// <summary>Combines two algorithms into one (structural combination via <c>;</c>).</summary>
    public sealed record Combine(Expr Left, Expr Right) : Expr;

    /// <summary>Resolves a named algorithm by lexical lookup.</summary>
    public sealed record Resolve(string Name) : Expr;

    /// <summary>
    /// Extension call syntax. <c>DotCall(a, "f", args?)</c> represents <c>a.f</c> or <c>a.f(args)</c>
    /// with smart resolution: property access when f has 0 params, otherwise call with receiver.
    /// Lean: <c>dotCall : Expr → Ident → Option Algorithm → Expr</c>.
    /// </summary>
    public sealed record DotCall(Expr Target, string Name, Algorithm? Args = null) : Expr;

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

// ── Patterns (Lean: Pattern — for conditional algorithms) ──────────────────

/// <summary>
/// Pattern language for conditional algorithm branch matching.
/// Patterns match against <see cref="Result"/> values at call time.
/// Lean: <c>Pattern</c> inductive.
///
/// Surface clause-definition elaboration uses these patterns too:
/// a same-name clause group elaborates as ordinary
/// <see cref="Algorithm.User"/> only when it contains exactly one clause and
/// that sole head is a top-level plain binder list; multi-clause families and
/// structured heads elaborate as <see cref="Algorithm.Conditional"/>.
/// </summary>
public abstract record Pattern
{
    private Pattern() { }

    /// <summary>Matches any Result and binds it to the given name.</summary>
    public sealed record Bind(string Name) : Pattern;

    /// <summary>Matches only <c>Result.Atom(n)</c> where n equals <see cref="Value"/>.</summary>
    public sealed record LitInt(decimal Value) : Pattern;

    /// <summary>Matches only <c>Result.Str(s)</c> where s equals <see cref="Value"/> (exact string equality).</summary>
    public sealed record LitString(string Value) : Pattern;

    /// <summary>Matches <c>Result.Group(items)</c> with same arity, each sub-pattern matching.</summary>
    public sealed record Group(IReadOnlyList<Pattern> Items) : Pattern;

    /// <summary>Collect all binder names in this pattern (left-to-right).</summary>
    public IReadOnlyList<string> BoundNames() => this switch
    {
        Bind(var name) => [name],
        LitInt _ => [],
        LitString _ => [],
        Group(var items) => items.SelectMany(p => p.BoundNames()).ToList(),
        _ => [],
    };

    /// <summary>Check whether this pattern contains duplicate binder names.</summary>
    public bool HasDuplicateBinds()
    {
        var names = BoundNames();
        return names.Count != names.Distinct().Count();
    }

    /// <summary>
    /// Compute the top-level arity of a pattern.
    /// Lean: <c>Pattern.topLevelArity</c>.
    /// <list type="bullet">
    ///   <item><c>Group [p1, ..., pn]</c> → n</item>
    ///   <item>Any non-group pattern → 1</item>
    /// </list>
    /// This defines the outer call interface of a conditional algorithm branch.
    /// All branches of the same conditional algorithm must have the same
    /// top-level pattern arity. Nested substructure may vary.
    /// </summary>
    public int TopLevelArity() => this switch
    {
        Group(var items) => items.Count,
        _ => 1,
    };

    /// <summary>
    /// Returns declared parameter names only for the strict flat multi-binder
    /// core subset: a top-level flat group of multiple plain binders.
    ///
    /// This is intentionally narrower than the full surface clause
    /// elaboration rule. It is kept for evaluator compatibility fallback over
    /// manually constructed conditional ASTs.
    /// </summary>
    internal IReadOnlyList<string>? TryGetFlatMultiBinderParams()
    {
        if (this is not Group(var items) || items.Count <= 1)
            return null;

        var names = new List<string>(items.Count);
        foreach (var item in items)
        {
            if (item is not Bind(var name))
                return null;
            names.Add(name);
        }

        return names;
    }

    /// <summary>
    /// Returns declared parameter names when a sole surface clause head
    /// consists only of top-level plain binders.
    ///
    /// This is only an eligibility helper for the whole same-name
    /// clause-group rule. Front-ends must still classify at the family level:
    /// a same-name clause group elaborates as ordinary only if it contains
    /// exactly one clause and that sole head qualifies here.
    ///
    /// Accepted shapes:
    /// <list type="bullet">
    ///   <item><c>Bind(x)</c>, corresponding to <c>F(x) = ...</c></item>
    ///   <item><c>Group [Bind(x), Bind(y), ...]</c> with arity greater than 1</item>
    /// </list>
    ///
    /// Rejected on purpose:
    /// <list type="bullet">
    ///   <item><c>Group [Bind(x)]</c>, corresponding to grouped singleton <c>F((x)) = ...</c></item>
    ///   <item>Nested, literal, or mixed pattern structure</item>
    /// </list>
    /// </summary>
    public IReadOnlyList<string>? TryGetOrdinaryClauseParams()
        => this switch
        {
            Bind(var name) => [name],
            _ => TryGetFlatMultiBinderParams(),
        };

    /// <summary>
    /// True when a sole clause head requires conditional whole-argument
    /// semantics instead of ordinary user-call binding. Front-ends must still
    /// classify at the whole same-name clause-group level, because a plain
    /// binder head can still belong to a multi-clause family that remains
    /// conditional.
    /// </summary>
    public bool RequiresConditionalClauseSemantics()
        => TryGetOrdinaryClauseParams() is null;

    /// <summary>
    /// Check whether two patterns are match-equivalent, i.e., they match
    /// the same set of inputs. Binder names are irrelevant for matching.
    /// </summary>
    internal bool IsMatchEquivalent(Pattern other) => (this, other) switch
    {
        (Bind, Bind) => true,
        (LitInt a, LitInt b) => a.Value == b.Value,
        (LitString a, LitString b) => a.Value == b.Value,
        (Group a, Group b) => a.Items.Count == b.Items.Count &&
            a.Items.Zip(b.Items).All(pair => pair.First.IsMatchEquivalent(pair.Second)),
        _ => false,
    };
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
public sealed record Property(string Name, Algorithm Value, bool IsPublic = false);

/// <summary>
/// Represents a KatLang algorithm — the fundamental building block.
/// Discriminated union matching the Lean specification:
/// <c>Algorithm.mk</c> (user-defined), <c>Algorithm.builtin</c> (built-in operation),
/// and <c>Algorithm.conditional</c> (conditional algorithm with pattern branches).
///
/// Virtual properties provide Lean-style accessors that return defaults for Builtin variant
/// (null/[] as appropriate), matching Lean's Algorithm.parent, Algorithm.params, etc.
/// </summary>
public abstract record Algorithm
{
    private Algorithm() { }

    /// <summary>Lean: Algorithm.parent. Returns null for Builtin.</summary>
    public virtual ScopeCtx? Parent { get; init; }

    /// <summary>Lean: Algorithm.params. Returns [] for Builtin.</summary>
    public virtual IReadOnlyList<string> Params { get; init; } = [];

    /// <summary>Lean: Algorithm.opens. Returns [] for Builtin.</summary>
    public virtual IReadOnlyList<Expr> Opens { get; init; } = [];

    /// <summary>Lean: Algorithm.props. Returns [] for Builtin.</summary>
    public virtual IReadOnlyList<Property> Properties { get; init; } = [];

    /// <summary>Lean: Algorithm.output. Returns [] for Builtin and Conditional.</summary>
    public virtual IReadOnlyList<Expr> Output { get; init; } = [];

    /// <summary>Lean: Algorithm.branches. Returns [] for non-Conditional algorithms.</summary>
    public virtual IReadOnlyList<CondBranch> Branches { get; init; } = [];

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
        var branches = Branches;
        for (int i = 0; i < branches.Count; i++)
        {
            for (int j = i + 1; j < branches.Count; j++)
            {
                if (branches[i].Pattern.IsMatchEquivalent(branches[j].Pattern))
                    return true;
            }
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
        User user => user with { Params = parameters },
        _ => this,
    };

    /// <summary>
    /// Elaborate a whole same-name clause family after all of its clauses are
    /// known. This is the real ordinary-vs-conditional decision boundary.
    ///
    /// A same-name clause group elaborates as ordinary only when it contains
    /// exactly one clause and that sole head is a plain top-level binder list.
    /// Otherwise the whole family remains conditional. This is intentional:
    /// later clauses may force the entire family to stay conditional, for
    /// example <c>F(0) = 0</c> followed by <c>F(x) = 1</c>.
    /// </summary>
    public static Algorithm ElaborateClauseGroup(IReadOnlyList<CondBranch> clauses)
    {
        if (clauses.Count == 1 && clauses[0].Pattern.TryGetOrdinaryClauseParams() is { } paramNames)
            return clauses[0].Body.WithParams(paramNames);

        if (clauses.Count == 0)
            return new Conditional(Parent: null, Opens: [], Branches: []);

        var parent = clauses[0].Body.Parent;
        var opens = clauses[0].Body.Opens;
        var conditionalBranches = clauses
            .Select(branch => new CondBranch(branch.Pattern, branch.Body.WithParams([])))
            .ToList();

        return new Conditional(
            parent,
            opens,
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
    /// Parser elaboration may also predeclare params here for plain-binder
    /// clause syntax such as <c>Apply(f) = f(4)</c> or
    /// <c>Filter(x, predicate) = if(predicate(x), x)</c>.
    /// </summary>
    public sealed record User : Algorithm
    {
        public User(
            ScopeCtx? Parent,
            IReadOnlyList<string> Params,
            IReadOnlyList<Expr> Opens,
            IReadOnlyList<Property> Properties,
            IReadOnlyList<Expr> Output)
        {
            this.Parent = Parent;
            this.Params = Params;
            this.Opens = Opens;
            this.Properties = Properties;
            this.Output = Output;
        }

        public override ScopeCtx? Parent { get; init; }
        public override IReadOnlyList<string> Params { get; init; } = [];
        public override IReadOnlyList<Expr> Opens { get; init; } = [];
        public override IReadOnlyList<Property> Properties { get; init; } = [];
        public override IReadOnlyList<Expr> Output { get; init; } = [];
        internal override bool IsParametrized { get; init; }
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
    /// one clause and that sole head is a plain binder list. Multi-clause
    /// families, grouped heads, and literal heads such as
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

// ── ScopeCtx (Lean: ScopeCtx) ─────────────────────────────────────────────

/// <summary>
/// Scope context used during evaluation for name resolution.
/// Populated by the evaluator, not the parser.
/// </summary>
public sealed record ScopeCtx(
    ScopeCtx? Parent,
    IReadOnlyList<Expr> Opens,
    IReadOnlyList<Property> Properties);
