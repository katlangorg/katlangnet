namespace KatLang;

/// <summary>
/// KatLang 0.75 evaluator matching the Lean specification.
/// Uses <see cref="EvalResult{T}"/> (<c>EvalM := Except Error</c>) for structured errors
/// instead of nullable returns.
/// Ownership-first lookup: local → parent chain structural → opens fallback across chain.
/// Property visibility: opens only expose PUBLIC properties; structural lookup sees all.
///
/// Builtins (If, While, Repeat, Atoms) are injected via a prelude algorithm in the initial
/// call stack, matching Lean's <c>preludeAlg</c>. Call dispatch switches on Algorithm kind:
/// <c>Algorithm.Builtin</c> → lazy arg resolution + <c>applyBuiltin</c>;
/// <c>Algorithm.User</c> → dual-view argument binding via <c>evalUserCall</c>.
///
/// Higher-order algorithm parameters use dual-view semantics:
/// - AlgEnv: algorithm meaning (callable/structural), resolved via <c>tryResolveArgAlgs</c>
/// - ValEnv: value meaning, resolved via independent per-expression eager evaluation
/// - <c>Eval(Param(x))</c>: checks ValEnv first, then AlgEnv as fallback
///   (0-param algorithm → auto-evaluate; multi-param → arity mismatch)
/// - <c>ResolveAlg(Param(x))</c>: checks AlgEnv before returning NotAnAlgorithm
/// </summary>
public static class Evaluator
{
    // ── EvalCtx (Lean: EvalCtx) ─────────────────────────────────────────────

    /// <summary>
    /// Evaluation context threaded through resolution and evaluation.
    /// Wraps the algorithm chain (current algorithm + enclosing callers) used for
    /// both lexical resolution and runtime dispatch.
    /// AlgEnv carries algorithm-typed parameter bindings for higher-order dispatch.
    /// Lean: structure EvalCtx where callStack : List Algorithm; algEnv : AlgEnv := [].
    /// </summary>
    private readonly record struct EvalCtx(
        IReadOnlyList<Algorithm> CallStack,
        IReadOnlyList<(string Name, Algorithm Value)> AlgEnv)
    {
        public static readonly EvalCtx Empty = new([], []);

        /// <summary>Lean: EvalCtx.push — prepend an algorithm to the call stack.</summary>
        public EvalCtx Push(Algorithm alg) => new(Prepend(alg, CallStack), AlgEnv);

        /// <summary>Lean: EvalCtx.head? — first algorithm in the call stack.</summary>
        public Algorithm? Head => CallStack.Count > 0 ? CallStack[0] : null;

        /// <summary>Lean: EvalCtx.withAlgEnv — replace the algorithm environment.</summary>
        public EvalCtx WithAlgEnv(IReadOnlyList<(string, Algorithm)> algEnv) => new(CallStack, algEnv);
    }

    // ── Environment types ────────────────────────────────────────────────────

    /// <summary>Value environment: maps parameter names to results. Lean: lookupVal (Option).</summary>
    private static Result? LookupVal(IReadOnlyList<(string Name, Result Value)> env, string name)
    {
        foreach (var (n, v) in env)
            if (n == name) return v;
        return null;
    }

    /// <summary>Algorithm environment: maps parameter names to algorithms. Lean: AlgEnv.lookup.</summary>
    private static Algorithm? LookupAlg(IReadOnlyList<(string Name, Algorithm Value)> env, string name)
    {
        foreach (var (n, v) in env)
            if (n == name) return v;
        return null;
    }

    // ── Algorithm helpers ────────────────────────────────────────────────────

    /// <summary>
    /// Lean: Algorithm.withParent. No-op for Builtin variant.
    /// </summary>
    private static Algorithm WithParent(Algorithm alg, ScopeCtx? parent) => alg switch
    {
        Algorithm.Builtin => alg,
        _ => alg with { Parent = parent },
    };

    private static ScopeCtx AsScopeCtx(Algorithm alg)
        => new(alg.Parent, alg.Opens, alg.Properties);

    /// <summary>Lean: Algorithm.childOf — wire a child algorithm to its parent's scope context.</summary>
    private static Algorithm ChildOf(Algorithm parent, Algorithm child)
        => WithParent(child, AsScopeCtx(parent));

    /// <summary>
    /// Create a temporary algorithm from a ScopeCtx for open resolution.
    /// Lean: Algorithm.forOpens.
    /// </summary>
    private static Algorithm ForOpens(ScopeCtx sc)
        => new Algorithm.User(
            Parent: sc, Params: [], Opens: sc.Opens,
            Properties: [], Output: []);

    /// <summary>Lean: Algorithm.lookupProp (any visibility).</summary>
    private static Algorithm? LookupProp(Algorithm alg, string name)
    {
        foreach (var prop in alg.Properties)
            if (prop.Name == name) return prop.Value;
        return null;
    }

    /// <summary>Lean: Algorithm.lookupPublicProp (public only).</summary>
    private static Algorithm? LookupPublicProp(Algorithm alg, string name)
    {
        foreach (var prop in alg.Properties)
            if (prop.Name == name && prop.IsPublic) return prop.Value;
        return null;
    }

    /// <summary>
    /// Checks if a property exists (any visibility) in the algorithm.
    /// Used to distinguish "missing" from "exists but private" in error reporting.
    /// </summary>
    private static bool HasPropAny(Algorithm alg, string name)
    {
        foreach (var prop in alg.Properties)
            if (prop.Name == name) return true;
        return false;
    }

    /// <summary>
    /// Human-readable constructor kind for diagnostics.
    /// Lean: Expr.kind.
    /// </summary>
    private static string ExprKind(Expr e) => e switch
    {
        Expr.Param => "param",
        Expr.Num => "num",
        Expr.StringLiteral => "stringLiteral",
        Expr.Unary => "unary",
        Expr.Binary => "binary",
        Expr.Index => "index",
        Expr.Combine => "combine",
        Expr.Resolve => "resolve",
        Expr.Block => "block",
        Expr.Call => "call",
        Expr.DotCall => "dotCall",
        Expr.Grace => "grace",
        Expr.NativeCall => "nativeCall",
        _ => "unknown",
    };

    /// <summary>
    /// Predicate defining which expression forms are allowed in open position.
    /// Only structural references to libraries are permitted.
    /// Lean: Expr.isOpenForm.
    /// </summary>
    private static bool IsOpenForm(Expr e) => e is
        Expr.Combine or Expr.Block or Expr.Resolve or Expr.DotCall(_, _, null);

    /// <summary>
    /// Extract a descriptive name from an open expression for error messages.
    /// Lean: openExprName.
    /// </summary>
    private static string OpenExprName(Expr e) => e switch
    {
        Expr.Resolve(var n) => n,
        Expr.DotCall(var o, var n, _) => OpenExprName(o) + "." + n,
        Expr.Block => "(inline library)",
        Expr.Combine(var a, var b) => OpenExprName(a) + " + " + OpenExprName(b),
        _ => $"({ExprKind(e)})",
    };

    // ── Context string helpers (Lean: CtxMsg.openMsg, CtxMsg.call, CtxMsg.dotCall) ─

    private static string CtxOpen(string key) => $"while resolving open: {key}";
    private static string CtxCall(Expr f) => $"while evaluating call to {OpenExprName(f)}";
    private static string CtxDotCall(Expr obj, string name) => $"while evaluating dotCall .{name} of {OpenExprName(obj)}";

    // ── Error context helper ────────────────────────────────────────────────

    /// <summary>
    /// Attach context to any error raised by the given result.
    /// Lean: withCtx.
    /// </summary>
    private static EvalResult<T> WithCtx<T>(string context, EvalResult<T> result) =>
        result.IsError
            ? new EvalError.WithContext(context, result.Error) { Span = result.Error.Span }
            : result;

    private static EvalResult<T> WithSpan<T>(SourceSpan? span, EvalResult<T> result) =>
        result.IsError && result.Error.Span is null
            ? (result.Error with { Span = span })
            : result;

    /// <summary>Returns the <see cref="SourceSpan"/> of the first output expression that has one.</summary>
    private static SourceSpan? FirstSpan(IReadOnlyList<Expr> output)
    {
        foreach (var e in output)
            if (e.Span is { } s) return s;
        return null;
    }

    // ── Lexical lookup (direct — no opens, used for open resolution) ────────

    /// <summary>Lean: lookupInParentsDirect (Option).</summary>
    private static Algorithm? LookupInParentsDirect(ScopeCtx sc, string name)
    {
        foreach (var prop in sc.Properties)
        {
            if (prop.Name == name)
                return WithParent(prop.Value, sc);
        }

        return sc.Parent is { } parent ? LookupInParentsDirect(parent, name) : null;
    }

    /// <summary>
    /// Direct lexical lookup: local properties + parent chain only (no opens).
    /// Lean: lookupLexicalDirect (Option).
    /// </summary>
    private static Algorithm? LookupLexicalDirect(Algorithm alg, string name)
    {
        var local = LookupProp(alg, name);
        if (local is not null)
            return ChildOf(alg, local);

        return alg.Parent is { } sc ? LookupInParentsDirect(sc, name) : null;
    }

    /// <summary>
    /// Unwired parent-chain lookup: returns algorithm as stored at its definition site,
    /// without rewiring parent. Used by open resolution to enforce isolation.
    /// Lean: lookupInParentsDirectUnwired.
    /// </summary>
    private static Algorithm? LookupInParentsDirectUnwired(ScopeCtx sc, string name)
    {
        foreach (var prop in sc.Properties)
        {
            if (prop.Name == name)
                return prop.Value; // no wiring
        }
        return sc.Parent is { } parent ? LookupInParentsDirectUnwired(parent, name) : null;
    }

    /// <summary>
    /// Unwired direct lexical lookup: same search path as LookupLexicalDirect
    /// but returns algorithms without rewiring to the caller.
    /// Lean: lookupLexicalDirectUnwired.
    /// </summary>
    private static Algorithm? LookupLexicalDirectUnwired(Algorithm alg, string name)
    {
        var local = LookupProp(alg, name);
        if (local is not null)
            return local; // no wiring
        return alg.Parent is { } sc ? LookupInParentsDirectUnwired(sc, name) : null;
    }

    /// <summary>
    /// Public-only unwired parent-chain lookup: returns public properties only, unwired.
    /// Lean: lookupInParentsDirectUnwiredPublic.
    /// </summary>
    private static Algorithm? LookupInParentsDirectUnwiredPublic(ScopeCtx sc, string name)
    {
        foreach (var prop in sc.Properties)
        {
            if (prop.Name == name && prop.IsPublic)
                return prop.Value; // no wiring, public only
        }
        return sc.Parent is { } parent ? LookupInParentsDirectUnwiredPublic(parent, name) : null;
    }

    /// <summary>
    /// Public-only unwired direct lexical lookup: searches local then parent chain
    /// for public properties only, returning algorithms unwired (definition-site parent preserved).
    /// Lean: lookupLexicalDirectUnwiredPublic.
    /// </summary>
    private static Algorithm? LookupLexicalDirectUnwiredPublic(Algorithm alg, string name)
    {
        var local = LookupPublicProp(alg, name);
        if (local is not null)
            return local; // no wiring, public only
        return alg.Parent is { } sc ? LookupInParentsDirectUnwiredPublic(sc, name) : null;
    }

    // ── Open resolution ─────────────────────────────────────────────────────

    /// <summary>
    /// Resolves an open expression to a library algorithm.
    /// Lean: resolveOpen → EvalM Algorithm.
    /// </summary>
    private static EvalResult<Algorithm> ResolveOpen(Expr openExpr, EvalCtx ctx)
        => ResolveAlgForOpen(openExpr, ctx);

    /// <summary>
    /// A resolved open: its canonical dedup key, original expression, and resolved algorithm.
    /// Lean: ResolvedOpen (key, expr, lib).
    /// </summary>
    private readonly record struct ResolvedOpen(string Key, Expr Expr, Algorithm Lib);

    /// <summary>
    /// A single hit from open lookup: which provider supplied it, the library, and the child algorithm.
    /// Lean: OpenHit (provider, lib, child).
    /// </summary>
    private readonly record struct OpenHit(string Provider, Algorithm Lib, Algorithm Child);

    /// <summary>
    /// Resolve all opens of an algorithm upfront.
    /// Deduplicates named opens by <c>openExprName</c> (first occurrence wins) to avoid
    /// repeated resolution and spurious ambiguity from duplicate opens.
    /// Inline blocks are never deduplicated (each gets a unique positional key).
    /// Validates all open expressions first for fail-fast diagnostics.
    /// Lean: resolveAllOpens → EvalM (List ResolvedOpen).
    /// </summary>
    private static EvalResult<IReadOnlyList<ResolvedOpen>> ResolveAllOpens(
        Algorithm alg, EvalCtx ctx)
    {
        if (alg.Opens.Count == 0)
            return EvalResult<IReadOnlyList<ResolvedOpen>>.Ok([]);

        // Deduplicate by key (first occurrence wins); inline blocks use positional keys
        var seen = new HashSet<string>();
        var deduped = new List<(string Key, Expr Expr)>();
        for (var i = 0; i < alg.Opens.Count; i++)
        {
            var openExpr = alg.Opens[i];
            var key = openExpr is Expr.Block
                ? $"(inline#{i})"  // unique per original position, never deduped
                : OpenExprName(openExpr);
            if (seen.Add(key))
                deduped.Add((key, openExpr));
        }

        // Validate all open expressions first (fail-fast with clear errors)
        foreach (var (key, openExpr) in deduped)
        {
            if (!IsOpenForm(openExpr))
                return new EvalError.BadOpenForm($"{ExprKind(openExpr)}: {key}");
        }

        // Then resolve (each open wrapped with context using its dedup key)
        var result = new List<ResolvedOpen>(deduped.Count);
        foreach (var (key, openExpr) in deduped)
        {
            var libResult = WithCtx(
                CtxOpen(key),
                ResolveOpen(openExpr, ctx));
            if (libResult.IsError) return libResult.Error;
            result.Add(new ResolvedOpen(key, openExpr, libResult.Value));
        }
        return EvalResult<IReadOnlyList<ResolvedOpen>>.Ok(result);
    }

    /// <summary>
    /// Searches opened namespaces for a name using public-only property lookup.
    /// Returns Ok(null) if no open provides the name publicly.
    /// Returns Ok(alg) if exactly one open provides it publicly.
    /// Returns Err(AmbiguousOpen) if multiple opens provide it publicly.
    /// Lean: lookupOpens → EvalM (Option Algorithm).
    /// </summary>
    private static EvalResult<Algorithm?> LookupOpens(
        Algorithm alg, string name, EvalCtx ctx)
    {
        if (alg.Opens.Count == 0) return EvalResult<Algorithm?>.Ok(null);

        var innerCtx = ctx.Push(alg);
        var resolvedResult = ResolveAllOpens(alg, innerCtx);
        if (resolvedResult.IsError) return resolvedResult.Error;

        var hits = new List<OpenHit>();

        // Public-only filtering: only public properties visible through opens
        foreach (var ri in resolvedResult.Value)
        {
            var child = LookupPublicProp(ri.Lib, name);
            if (child is not null)
                hits.Add(new OpenHit(ri.Key, ri.Lib, child));
        }

        if (hits.Count == 0)
            return EvalResult<Algorithm?>.Ok(null);
        if (hits.Count == 1)
            return EvalResult<Algorithm?>.Ok(ChildOf(hits[0].Lib, hits[0].Child));
        return new EvalError.AmbiguousOpen(name, hits.Select(h => h.Provider).ToList());
    }

    // ── Lexical resolution (ownership-first) ────────────────────────────────

    /// <summary>
    /// Open-based lookup in parent chain (helper for LookupOpensInChain).
    /// Checks opens at each level of the parent chain as fallback.
    /// Lean: lookupOpensInParentChain → EvalM (Option Algorithm).
    /// </summary>
    private static EvalResult<Algorithm?> LookupOpensInParentChain(
        ScopeCtx sc, string name, EvalCtx ctx)
    {
        var tempAlg = ForOpens(sc);
        var openResult = LookupOpens(tempAlg, name, ctx);
        if (openResult.IsError) return openResult.Error;
        if (openResult.Value is not null)
            return EvalResult<Algorithm?>.Ok(openResult.Value);

        return sc.Parent is { } parent
            ? LookupOpensInParentChain(parent, name, ctx)
            : EvalResult<Algorithm?>.Ok(null);
    }

    /// <summary>
    /// Open-based lookup across the algorithm chain (current first, then parents).
    /// Checks opens at each level of the parent chain as fallback.
    /// Lean: lookupOpensInChain → EvalM (Option Algorithm).
    /// </summary>
    private static EvalResult<Algorithm?> LookupOpensInChain(
        Algorithm alg, string name, EvalCtx ctx)
    {
        // Try opens at current level
        var openResult = LookupOpens(alg, name, ctx);
        if (openResult.IsError) return openResult.Error;
        if (openResult.Value is not null)
            return EvalResult<Algorithm?>.Ok(openResult.Value);

        // Try parent chain
        return alg.Parent is { } sc
            ? LookupOpensInParentChain(sc, name, ctx)
            : EvalResult<Algorithm?>.Ok(null);
    }

    /// <summary>
    /// Full lexical lookup with ownership-first model:
    /// 1. Local properties (owned by this algorithm — any visibility)
    /// 2. Parent chain structural properties (owned by ancestors — any visibility, no opens)
    /// 3. Opens as fallback across the entire chain (public only)
    /// Structural ownership always takes precedence over opens.
    /// Lean: lookupLexical → EvalM Algorithm.
    /// </summary>
    private static EvalResult<Algorithm> LookupLexical(
        Algorithm alg, string name, EvalCtx ctx)
    {
        // 1. Local properties (any visibility)
        var local = LookupProp(alg, name);
        if (local is not null)
            return EvalResult<Algorithm>.Ok(ChildOf(alg, local));

        // 2. Parent chain structural only (any visibility, no opens)
        if (alg.Parent is { } sc)
        {
            var structural = LookupInParentsDirect(sc, name);
            if (structural is not null)
                return EvalResult<Algorithm>.Ok(structural);
        }

        // 3. Opens fallback across the entire chain (public only)
        var opensResult = LookupOpensInChain(alg, name, ctx);
        if (opensResult.IsError) return opensResult.Error;
        if (opensResult.Value is not null)
            return EvalResult<Algorithm>.Ok(opensResult.Value);

        return new EvalError.UnknownName(name);
    }

    // ── Wire parent ─────────────────────────────────────────────────────────

    /// <summary>Lean: wireToCaller.</summary>
    private static Algorithm WireToCaller(EvalCtx ctx, Algorithm alg)
    {
        if (ctx.CallStack.Count > 0)
            return ChildOf(ctx.CallStack[0], alg);
        return alg;
    }

    /// <summary>Coerce a Result to decimal, or raise TypeMismatch for strings, BadArity otherwise. Lean: expectInt.</summary>
    private static EvalResult<decimal> ExpectInt(Result r)
    {
        if (r is Result.Str)
            return new EvalError.TypeMismatch("Expected a number, got a string");
        var v = r.AsNum();
        return v is not null
            ? EvalResult<decimal>.Ok(v.Value)
            : new EvalError.BadArity();
    }

    /// <summary>
    /// Split a step result into (state, continue-flag).
    /// Convention: the last atom is the continue flag (nonzero = keep going).
    /// Lean: splitCont.
    /// </summary>
    private static EvalResult<(Result Next, decimal Cont)> SplitCont(Result output)
    {
        switch (output)
        {
            case Result.Atom(var n):
                return EvalResult<(Result, decimal)>.Ok((new Result.Atom(n), n));
            case Result.Group(var items) when items.Count > 0:
            {
                var lastR = ExpectInt(items[^1]);
                if (lastR.IsError) return lastR.Error;
                var state = new Result.Group(items.Take(items.Count - 1).ToList()).Normalize();
                return EvalResult<(Result, decimal)>.Ok((state, lastR.Value));
            }
            default:
                return new EvalError.BadArity();
        }
    }

    // ── Bind parameters ─────────────────────────────────────────────────────

    /// <summary>Lean: bindParams → EvalM ValEnv. Errors with ArityMismatch.</summary>
    private static EvalResult<IReadOnlyList<(string, Result)>> BindParams(
        IReadOnlyList<string> paramNames,
        IReadOnlyList<Result> values)
    {
        if (paramNames.Count != values.Count)
            return new EvalError.ArityMismatch(paramNames.Count, values.Count);

        var result = new List<(string, Result)>(paramNames.Count);
        for (var i = 0; i < paramNames.Count; i++)
            result.Add((paramNames[i], values[i]));
        return EvalResult<IReadOnlyList<(string, Result)>>.Ok(result);
    }

    /// <summary>
    /// Argument passing rule: a single atom is wrapped in a one-element list;
    /// a group is unpacked into its elements. Lean: unpackArgs.
    /// </summary>
    private static IReadOnlyList<Result> UnpackArgs(Result r) => r switch
    {
        Result.Atom(var n) => [new Result.Atom(n)],
        Result.Str _ => [r],
        Result.Group(var items) => items,
        _ => [],
    };

    // ── Result helpers ────────────────────────────────────────────────────────

    /// <summary>
    /// Extract top-level items from a result into a list.
    /// Atom → [Atom]; Group → its items. Lean: Result.toItems.
    /// </summary>
    private static void ResultItems(List<Result> into, Result r)
    {
        switch (r)
        {
            case Result.Atom:
            case Result.Str:
                into.Add(r);
                break;
            case Result.Group(var items):
                into.AddRange(items);
                break;
        }
    }

    // ── Pattern matching (for conditional algorithms) ────────────────────────

    /// <summary>
    /// Match a pattern against a Result, returning accumulated bindings on success.
    /// Lean: matchPattern.
    /// </summary>
    private static IReadOnlyList<(string, Result)>? MatchPattern(Pattern pattern, Result result)
    {
        switch (pattern)
        {
            case Pattern.Bind(var name):
                return [(name, result)];

            case Pattern.LitInt(var n):
                return result is Result.Atom(var v) && v == n
                    ? []
                    : null;

            case Pattern.LitString(var s):
                return result is Result.Str(var sv) && sv == s
                    ? []
                    : null;

            case Pattern.Group(var items):
                // Result.normalize collapses group [x] → x, so a singleton
                // group pattern (e.g. "(b)") must also match a non-group result
                // by treating it as if it were group [result].
                if (result is Result.Group(var rs))
                {
                    if (rs.Count != items.Count) return null;
                }
                else if (items.Count == 1)
                {
                    rs = [result];
                }
                else
                {
                    return null;
                }
                var bindings = new List<(string, Result)>();
                for (var i = 0; i < items.Count; i++)
                {
                    var sub = MatchPattern(items[i], rs[i]);
                    if (sub is null) return null;
                    bindings.AddRange(sub);
                }
                return bindings;

            default:
                return null;
        }
    }

    /// <summary>
    /// Try branches in order. Returns the first matching branch and its bindings.
    /// Lean: matchBranches.
    /// </summary>
    private static (CondBranch Branch, IReadOnlyList<(string, Result)> Bindings)? MatchBranches(
        IReadOnlyList<CondBranch> branches, Result arg)
    {
        foreach (var branch in branches)
        {
            var bindings = MatchPattern(branch.Pattern, arg);
            if (bindings is not null)
                return (branch, bindings);
        }
        return null;
    }

    // ── Combine algorithms ──────────────────────────────────────────────────

    /// <summary>
    /// Policy controlling how opens are handled when combining two algorithms.
    /// Lean: OpenPolicy inductive.
    /// </summary>
    private enum OpenPolicy
    {
        /// <summary>Merge opens from both algorithms (a.opens ++ b.opens).</summary>
        Merge,
        /// <summary>Discard all opens (result has opens = []).
        /// Enforces isolation: libraries cannot smuggle in transitive opens.</summary>
        Closed
    }

    /// <summary>
    /// Lean: combineAlg. Merges params, properties, output.
    /// Opens handling is controlled by <paramref name="openPolicy"/>:
    /// <c>Merge</c> concatenates opens; <c>Closed</c> discards them.
    /// </summary>
    private static Algorithm CombineAlg(Algorithm a, Algorithm b, OpenPolicy openPolicy = OpenPolicy.Merge)
    {
        var opens = openPolicy switch
        {
            OpenPolicy.Merge => a.Opens.Concat(b.Opens).ToList(),
            OpenPolicy.Closed => new List<Expr>(),
            _ => throw new InvalidOperationException($"Unknown OpenPolicy: {openPolicy}")
        };
        return new Algorithm.User(
            Parent: null, // wired later by ResolveAlg
            Params: a.Params.Concat(b.Params).ToList(),
            Opens: opens,
            Properties: a.Properties.Concat(b.Properties).ToList(),
            Output: [new Expr.Block(a), new Expr.Block(b)]);
    }

    // ── Built-in prelude ────────────────────────────────────────────────────

    private static Property MathConstant(string name, decimal value) =>
        new(name, new Algorithm.User(Parent: null, Params: [], Opens: [],
            Properties: [], Output: [new Expr.Num(value)]), IsPublic: true);

    private static Property MathFn1(string name) =>
        new(name, new Algorithm.User(Parent: null, Params: ["x"], Opens: [],
            Properties: [], Output: [new Expr.NativeCall(name, ["x"])]), IsPublic: true);

    private static Property MathFn2(string name) =>
        new(name, new Algorithm.User(Parent: null, Params: ["x", "y"], Opens: [],
            Properties: [], Output: [new Expr.NativeCall(name, ["x", "y"])]), IsPublic: true);

    private static readonly Algorithm MathAlgorithm = new Algorithm.User(
        Parent: null,
        Params: [],
        Opens: [],
        Properties:
        [
            // Use high-precision decimal literals instead of (decimal)Math.PI/E
            // to avoid double→decimal truncation (15 sig digits vs decimal's 28-29).
            // This ensures decimal→double roundtrip in EvalNativeCall preserves full
            // double precision, critical near singularities like tan(π/2).
            MathConstant("Pi", 3.1415926535897932384626433833m),
            MathConstant("E",  2.7182818284590452353602874714m),
            MathFn1("Abs"),
            MathFn1("Ceil"),
            MathFn1("Floor"),
            MathFn1("Round"),
            MathFn1("Sign"),
            MathFn1("Sqrt"),
            MathFn1("Ln"),
            MathFn1("Lg"),
            MathFn1("Sin"),
            MathFn1("Asin"),
            MathFn1("Cos"),
            MathFn1("Acos"),
            MathFn1("Tan"),
            MathFn1("Atan"),
            MathFn2("Pow"),
            MathFn2("Log"),
        ],
        Output: []);

    /// <summary>
    /// Prelude algorithm providing builtin operations in scope by default.
    /// Lean: preludeAlg. Builtins are injected into the initial call stack.
    /// All builtins and Math are public for use in opened contexts.
    /// </summary>
    private static readonly Algorithm PreludeAlg = new Algorithm.User(
        Parent: null,
        Params: [],
        Opens: [],
        Properties:
        [
            new("if",     new Algorithm.Builtin(BuiltinId.@if),     IsPublic: true),
            new("while",  new Algorithm.Builtin(BuiltinId.@while),  IsPublic: true),
            new("repeat", new Algorithm.Builtin(BuiltinId.@repeat), IsPublic: true),
            new("atoms",  new Algorithm.Builtin(BuiltinId.@atoms),  IsPublic: true),
            new("Math",   MathAlgorithm,                           IsPublic: true),
        ],
        Output: []);

    /// <summary>Lean: builtinAcceptsArity. ifBuiltin accepts 2 or 3 args.</summary>
    private static bool BuiltinAcceptsArity(BuiltinId b, int n) => (b, n) switch
    {
        (BuiltinId.@if, 2) => true,
        (BuiltinId.@if, 3) => true,
        (BuiltinId.@while, 2) => true,
        (BuiltinId.@repeat, 3) => true,
        (BuiltinId.@atoms, 1) => true,
        _ => false,
    };

    /// <summary>Lean: builtinArityDesc. Human-readable expected arity for error messages.</summary>
    private static string BuiltinArityDesc(BuiltinId b) => b switch
    {
        BuiltinId.@if => "2 or 3",
        BuiltinId.@while => "2",
        BuiltinId.@repeat => "3",
        BuiltinId.@atoms => "1",
        _ => "?",
    };

    // ── Intrinsics ──────────────────────────────────────────────────────────

    /// <summary>
    /// Lean: isIntrinsic. Predicate for intrinsic (non-builtin) property names.
    /// These are handled specially in resolveAlg / evalDotCall.
    /// Intrinsic kinds:
    /// - "length": structural — returns the count of output expressions (no evaluation needed)
    /// - "string": value-based — evaluates the algorithm output, converts numeric result to string
    /// </summary>
    private static bool IsIntrinsic(string name) => name is "length" or "string";

    /// <summary>
    /// Lean: evalStructuralIntrinsic?. Evaluate a structural intrinsic property on a resolved algorithm.
    /// Returns a result if name is a recognized structural intrinsic, null otherwise.
    /// Value-based intrinsics (e.g. "string") are handled inside EvalDotCall
    /// because they require evaluation context.
    /// </summary>
    private static EvalResult<Result>? EvalStructuralIntrinsic(Algorithm targetAlg, string name)
    {
        if (name == "length")
            return EvalResult<Result>.Ok(new Result.Atom(targetAlg.Output.Count));
        return null;
    }

    /// <summary>
    /// Lean: resultToString. Convert a numeric Result to its canonical string representation.
    /// Only atomic numeric values are supported; other forms raise typeMismatch.
    /// Canonical representation: culture-invariant decimal string.
    /// Examples: 123 → "123", -5 → "-5", 0 → "0", 1.20 → "1.20".
    /// </summary>
    private static EvalResult<Result> ResultToString(Result r)
    {
        if (r is Result.Atom(var n))
            return EvalResult<Result>.Ok(new Result.Str(n.ToString(System.Globalization.CultureInfo.InvariantCulture)));
        return new EvalError.TypeMismatch("builtin property `string` expects a numeric receiver");
    }

    // ── Open resolution ───────────────────────────────────────────────────

    /// <summary>
    /// Algorithm resolution using only direct lexical lookup (no opens).
    /// Used for resolving open expressions to avoid circularity.
    /// Does NOT wire to parent — opens are isolated modules.
    /// Only <c>Expr.openForm?</c> forms are permitted
    /// (structural references to libraries only).
    /// Builtins are rejected: they are not valid open targets.
    /// <para>
    /// Visibility rule: <c>open</c> never requires the opened algorithm itself to be public.
    /// It only requires the algorithm to be available (resolvable) in the current context.
    /// <c>open</c> imports only public members of that algorithm (enforced by <see cref="LookupOpens"/>).
    /// </para>
    /// Property access in open paths (<c>open A.B</c>) still requires intermediate
    /// properties to be public (normal dot-access visibility).
    /// Lean: resolveAlgForOpen → EvalM Algorithm.
    /// </summary>
    private static EvalResult<Algorithm> ResolveAlgForOpen(Expr expr, EvalCtx ctx)
    {
        switch (expr)
        {
            case Expr.Combine(var e1, var e2):
            {
                var aResult = ResolveAlgForOpen(e1, ctx);
                if (aResult.IsError) return aResult.Error;
                var bResult = ResolveAlgForOpen(e2, ctx);
                if (bResult.IsError) return bResult.Error;
                return EvalResult<Algorithm>.Ok(CombineAlg(aResult.Value, bResult.Value, OpenPolicy.Closed));
            }

            case Expr.Block(var alg):
                return EvalResult<Algorithm>.Ok(alg); // no wiring for opens

            case Expr.Resolve(var name):
            {
                // open never requires the opened algorithm itself to be public.
                // It only requires the algorithm to be available in the current context.
                // open imports only public members (enforced later by LookupOpens).
                if (ctx.CallStack.Count > 0)
                {
                    var found = LookupLexicalDirectUnwired(ctx.CallStack[0], name);
                    if (found is not null)
                        return found is Algorithm.Builtin
                            ? new EvalError.IllegalInOpen($"builtin '{name}'") { Span = expr.Span }
                            : EvalResult<Algorithm>.Ok(found); // unwired: preserves definition-site parent chain
                }
                return new EvalError.UnknownName(name) { Span = expr.Span };
            }

            case Expr.DotCall(var target, var propName, null):
                return WithSpan(expr.Span, ResolveOpenPropAccess(target, propName, ctx));

            default:
                // Not an open form — reject with informative error
                return new EvalError.BadOpenForm($"{ExprKind(expr)}: {OpenExprName(expr)}") { Span = expr.Span };
        }
    }

    /// <summary>
    /// Shared logic for resolving property access in open expressions.
    /// Used by DotCall(target, name, null) in ResolveAlgForOpen.
    /// </summary>
    private static EvalResult<Algorithm> ResolveOpenPropAccess(
        Expr target, string propName, EvalCtx ctx)
    {
        var targetResult = ResolveAlgForOpen(target, ctx);
        if (targetResult.IsError) return targetResult.Error;

        // First check if property exists at all (any visibility)
        var prop = LookupProp(targetResult.Value, propName);
        if (prop is not null)
        {
            if (prop is Algorithm.Builtin)
                return new EvalError.IllegalInOpen(
                    $"builtin not allowed in open: {OpenExprName(target)}.{propName}");

            // Property exists; check if it's public
            var publicProp = LookupPublicProp(targetResult.Value, propName);
            if (publicProp is not null)
                return EvalResult<Algorithm>.Ok(publicProp); // no wiring (pure resolution)

            return new EvalError.NotPublicProperty(OpenExprName(target), propName);
        }
        return new EvalError.UnknownProperty(OpenExprName(target), propName);
    }

    // ── Algorithm resolution (full — with opens) ─────────────────────────────

    /// <summary>Lean: resolveAlg → EvalM Algorithm.</summary>
    private static EvalResult<Algorithm> ResolveAlg(Expr expr, EvalCtx ctx)
    {
        switch (expr)
        {
            case Expr.Combine(var e1, var e2):
            {
                var aResult = ResolveAlg(e1, ctx);
                if (aResult.IsError) return aResult.Error;
                var bResult = ResolveAlg(e2, ctx);
                if (bResult.IsError) return bResult.Error;
                return EvalResult<Algorithm>.Ok(
                    WireToCaller(ctx, CombineAlg(aResult.Value, bResult.Value)));
            }

            case Expr.Block(var alg):
                return EvalResult<Algorithm>.Ok(WireToCaller(ctx, alg));

            case Expr.Resolve(var name):
            {
                if (ctx.CallStack.Count > 0)
                {
                    var r = LookupLexical(ctx.CallStack[0], name, ctx);
                    if (r.IsError && r.Error.Span is null)
                        return r.Error with { Span = expr.Span };
                    return r;
                }
                return new EvalError.UnknownName(name) { Span = expr.Span };
            }

            case Expr.DotCall:
            {
                // Lean: resolveAlg (.dotCall o n args) — lift to wrapper algorithm;
                // evalDotCall handles all semantics (length intrinsic, structural, lexical fallback)
                var wrapper = new Algorithm.User(
                    Parent: null, Params: [], Opens: [],
                    Properties: [], Output: [expr]);
                return EvalResult<Algorithm>.Ok(WireToCaller(ctx, wrapper));
            }

            // Algorithm resolution for parameters (Lean: resolveAlg Param(x)):
            // Check AlgEnv first — if x is bound to an algorithm, return it.
            // Otherwise NotAnAlgorithm (parameters are not structurally algorithms).
            case Expr.Param(var x):
            {
                var algBound = LookupAlg(ctx.AlgEnv, x);
                if (algBound is not null)
                    return EvalResult<Algorithm>.Ok(algBound);
                return new EvalError.NotAnAlgorithm($"param({x})") { Span = expr.Span };
            }
            case Expr.Num(var n):
                return new EvalError.NotAnAlgorithm($"num({n})") { Span = expr.Span };
            case Expr.Unary:
                return new EvalError.NotAnAlgorithm("unary expression") { Span = expr.Span };
            case Expr.Binary:
                return new EvalError.NotAnAlgorithm("binary expression") { Span = expr.Span };
            case Expr.Index:
                return new EvalError.NotAnAlgorithm("index expression") { Span = expr.Span };
            case Expr.Call:
                return new EvalError.NotAnAlgorithm("call expression") { Span = expr.Span };
            case Expr.NativeCall:
                return new EvalError.NotAnAlgorithm("native call") { Span = expr.Span };
            case Expr.Grace:
                return new EvalError.NotAnAlgorithm("grace expression") { Span = expr.Span };
            case Expr.StringLiteral:
                return new EvalError.NotAnAlgorithm("string literal") { Span = expr.Span };

            default:
                throw new InvalidOperationException($"Unhandled Expr type in ResolveAlg: {expr.GetType().Name}");
        }
    }

    // ── Algorithm output evaluation ─────────────────────────────────────────

    /// <summary>
    /// Evaluate an algorithm's output expressions and collect into a single Result.
    /// Normalization invariant: outputs are always normalized at algorithm boundaries.
    /// Lean: evalAlgOutput → EvalM Result.
    /// </summary>
    private static EvalResult<Result> EvalAlgOutput(
        Algorithm alg,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var dupProp = alg.FindDuplicatePropName();
        if (dupProp is not null)
            return new EvalError.DuplicateProperty(dupProp);

        var innerCtx = ctx.Push(alg);
        var results = new List<Result>();

        foreach (var expr in alg.Output)
        {
            var r = Eval(expr, innerCtx, valEnv);
            if (r.IsError) return r.Error;
            results.Add(r.Value);
        }

        return EvalResult<Result>.Ok(Result.FromItems(results));
    }

    /// <summary>Evaluate an expression and coerce to decimal. Lean: evalInt.</summary>
    private static EvalResult<decimal> EvalInt(
        Expr expr, EvalCtx ctx, IReadOnlyList<(string, Result)> valEnv)
    {
        var r = Eval(expr, ctx, valEnv);
        if (r.IsError) return r.Error;
        return ExpectInt(r.Value);
    }

    /// <summary>Run a step algorithm with the given state bound to its params. Lean: runStep.</summary>
    private static EvalResult<Result> RunStep(
        Algorithm step, EvalCtx ctx, IReadOnlyList<(string, Result)> valEnv, Result state)
    {
        var boundR = BindParams(step.Params, UnpackArgs(state));
        if (boundR.IsError) return boundR.Error;
        return EvalAlgOutput(step, ctx, Concat(boundR.Value, valEnv));
    }

    // ── Builtins ─────────────────────────────────────────────────────────────

    /// <summary>
    /// Applies a builtin operation to lazily-resolved argument algorithms.
    /// Lean: applyBuiltin → EvalM Result.
    /// </summary>
    private static EvalResult<Result> ApplyBuiltin(
        BuiltinId builtin,
        IReadOnlyList<Algorithm> args,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        switch (builtin, args.Count)
        {
            // if(cond, thenBranch, elseBranch): standard 3-arg conditional.
            case (BuiltinId.@if, 3):
            {
                var condR = EvalAlgOutput(args[0], ctx, valEnv);
                if (condR.IsError) return condR.Error;
                var condAtoms = condR.Value.ToAtoms();
                if (condAtoms.Count == 0) return new EvalError.BadArity();
                return condAtoms[0] == 0
                    ? EvalAlgOutput(args[2], ctx, valEnv)
                    : EvalAlgOutput(args[1], ctx, valEnv);
            }

            // if(cond, value): 2-arg conditional output / emit-on-true.
            // True → evaluate and return value. False → no output (empty group).
            case (BuiltinId.@if, 2):
            {
                var condR = EvalAlgOutput(args[0], ctx, valEnv);
                if (condR.IsError) return condR.Error;
                var condAtoms = condR.Value.ToAtoms();
                if (condAtoms.Count == 0) return new EvalError.BadArity();
                return condAtoms[0] == 0
                    ? EvalResult<Result>.Ok(new Result.Group([]))
                    : EvalAlgOutput(args[1], ctx, valEnv);
            }

            // while(step, init)
            case (BuiltinId.@while, 2):
            {
                var initR = EvalAlgOutput(args[1], ctx, valEnv);
                if (initR.IsError) return initR.Error;
                return WhileLoop(args[0], initR.Value, ctx, valEnv);
            }

            // repeat(step, count, init)
            case (BuiltinId.@repeat, 3):
            {
                var countR = EvalAlgOutput(args[1], ctx, valEnv);
                if (countR.IsError) return countR.Error;
                var nR = ExpectInt(countR.Value);
                if (nR.IsError) return nR.Error;
                if (nR.Value != Math.Floor(nR.Value))
                    return new EvalError.IllegalInEval("Repeat count must be an integer");
                var n = (long)nR.Value;
                if (n < 0) return new EvalError.IllegalInEval("Repeat count must be >= 0");
                var repeatInitR = EvalAlgOutput(args[2], ctx, valEnv);
                if (repeatInitR.IsError) return repeatInitR.Error;
                return RepeatLoop(args[0], n, repeatInitR.Value, ctx, valEnv);
            }

            // atoms(alg) — flatten to atoms
            case (BuiltinId.@atoms, 1):
            {
                var atomsR = EvalAlgOutput(args[0], ctx, valEnv);
                if (atomsR.IsError) return atomsR.Error;
                var atoms = atomsR.Value.ToAtoms();
                return EvalResult<Result>.Ok(
                    Result.FromItems(atoms.Select(n => new Result.Atom(n))));
            }

            default:
            {
                return new EvalError.WithContext(
                    $"expected {BuiltinArityDesc(builtin)} arguments",
                    new EvalError.ArityMismatch(0, args.Count));
            }
        }
    }

    /// <summary>Lean: While loop → EvalM Result.</summary>
    private static EvalResult<Result> WhileLoop(
        Algorithm step,
        Result state,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        while (true)
        {
            var outR = RunStep(step, ctx, valEnv, state);
            if (outR.IsError) return outR.Error;
            var splitR = SplitCont(outR.Value);
            if (splitR.IsError) return splitR.Error;
            var (next, cont) = splitR.Value;
            if (cont == 0) return EvalResult<Result>.Ok(state);
            state = next;
        }
    }

    /// <summary>Lean: Repeat loop → EvalM Result.</summary>
    private static EvalResult<Result> RepeatLoop(
        Algorithm step,
        long count,
        Result state,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        for (var k = 0; k < count; k++)
        {
            var outR = RunStep(step, ctx, valEnv, state);
            if (outR.IsError) return outR.Error;
            state = outR.Value;
        }
        return EvalResult<Result>.Ok(state);
    }

    // ── Main eval ───────────────────────────────────────────────────────────

    /// <summary>Lean: eval → EvalM Result.</summary>
    private static EvalResult<Result> Eval(
        Expr expr,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        switch (expr)
        {
            case Expr.Num(var n):
                return EvalResult<Result>.Ok(new Result.Atom(n));

            case Expr.StringLiteral(var s):
                return EvalResult<Result>.Ok(new Result.Str(s));

            case Expr.Param(var name):
            {
                // Dual-view parameter evaluation (Lean: eval Param(x)):
                // 1. ValEnv first (value meaning)
                // 2. AlgEnv fallback (algorithm meaning):
                //    - 0-param algorithm → auto-evaluate (thunk semantics)
                //    - multi-param algorithm → arityMismatch (needs explicit call)
                var val = LookupVal(valEnv, name);
                if (val is not null) return EvalResult<Result>.Ok(val);
                var algBound = LookupAlg(ctx.AlgEnv, name);
                if (algBound is not null)
                {
                    if (algBound.Params.Count == 0)
                        return EvalAlgOutput(algBound, ctx, valEnv);
                    return new EvalError.ArityMismatch(algBound.Params.Count, 0) { Span = expr.Span };
                }
                return new EvalError.UnknownName(name) { Span = expr.Span };
            }

            case Expr.Unary(var unaryOp, var operand):
            {
                // Empty result propagation: if(false, v) produces Group([]) (2-arg form).
                var operandR = Eval(operand, ctx, valEnv);
                if (operandR.IsError) return operandR.Error;
                if (operandR.Value is Result.Group(var uItems) && uItems.Count == 0)
                    return EvalResult<Result>.Ok(new Result.Group([]));
                if (operandR.Value is Result.Str)
                    return new EvalError.TypeMismatch("Unary operator is not supported for strings") { Span = expr.Span };
                var vR = ExpectInt(operandR.Value);
                if (vR.IsError) return vR.Error;
                var unaryResult = unaryOp switch
                {
                    UnaryOp.Minus => -vR.Value,
                    UnaryOp.Not => vR.Value == 0 ? 1m : 0m,
                    _ => 0m,
                };
                return EvalResult<Result>.Ok(new Result.Atom(unaryResult));
            }

            case Expr.Binary(var op, var left, var right):
            {
                // Evaluate both sides as Result first to handle empty results from 2-arg if.
                var lR = Eval(left, ctx, valEnv);
                if (lR.IsError) return lR.Error;
                var rR = Eval(right, ctx, valEnv);
                if (rR.IsError) return rR.Error;
                // Empty result handling: if(false, v) produces Group([]) (2-arg form).
                // Empty results are transparent in binary expressions.
                var lEmpty = lR.Value is Result.Group(var lItems) && lItems.Count == 0;
                var rEmpty = rR.Value is Result.Group(var rItems) && rItems.Count == 0;
                if (lEmpty && rEmpty) return EvalResult<Result>.Ok(new Result.Group([]));
                if (lEmpty) return EvalResult<Result>.Ok(rR.Value);
                if (rEmpty) return EvalResult<Result>.Ok(lR.Value);
                // String equality/inequality: both operands must be strings.
                if (lR.Value is Result.Str(var ls) && rR.Value is Result.Str(var rs2))
                {
                    return op switch
                    {
                        BinaryOp.Eq => EvalResult<Result>.Ok(new Result.Atom(ls == rs2 ? 1 : 0)),
                        BinaryOp.Ne => EvalResult<Result>.Ok(new Result.Atom(ls != rs2 ? 1 : 0)),
                        _ => new EvalError.TypeMismatch("Strings only support == and != operators") { Span = expr.Span },
                    };
                }
                // Mixed string/non-string: fail for any operator
                if (lR.Value is Result.Str || rR.Value is Result.Str)
                    return new EvalError.TypeMismatch("Cannot apply operator to string and non-string operands") { Span = expr.Span };
                // Normal arithmetic: coerce both to int.
                var xR = ExpectInt(lR.Value);
                if (xR.IsError) return xR.Error;
                var yR = ExpectInt(rR.Value);
                if (yR.IsError) return yR.Error;
                decimal x = xR.Value, y = yR.Value;
                if ((op is BinaryOp.Div or BinaryOp.IDiv or BinaryOp.Mod) && y == 0)
                    return new EvalError.DivByZero() { Span = expr.Span };
                decimal result;
                try
                {
                    result = op switch
                    {
                        BinaryOp.Add => x + y,
                        BinaryOp.Sub => x - y,
                        BinaryOp.Mul => x * y,
                        BinaryOp.Div => x / y,
                        BinaryOp.IDiv => Math.Truncate(x / y),
                        BinaryOp.Mod => x % y,
                        BinaryOp.Pow => y < 0 ? 0 : DecimalPow(x, y),
                        BinaryOp.Lt => x < y ? 1 : 0,
                        BinaryOp.Gt => x > y ? 1 : 0,
                        BinaryOp.Le => x <= y ? 1 : 0,
                        BinaryOp.Ge => x >= y ? 1 : 0,
                        BinaryOp.Eq => x == y ? 1 : 0,
                        BinaryOp.Ne => x != y ? 1 : 0,
                        BinaryOp.And => x != 0 && y != 0 ? 1 : 0,
                        BinaryOp.Or => x != 0 || y != 0 ? 1 : 0,
                        BinaryOp.Xor => (x != 0) != (y != 0) ? 1 : 0,
                        _ => 0,
                    };
                }
                catch (OverflowException)
                {
                    return new EvalError.NumericOverflow() { Span = expr.Span };
                }
                return EvalResult<Result>.Ok(new Result.Atom(result));
            }

            case Expr.Combine(var e1, var e2):
            {
                var r1 = Eval(e1, ctx, valEnv);
                if (r1.IsError) return r1.Error;
                var r2 = Eval(e2, ctx, valEnv);
                if (r2.IsError) return r2.Error;
                var items = new List<Result>();
                ResultItems(items, r1.Value);
                ResultItems(items, r2.Value);
                return EvalResult<Result>.Ok(Result.FromItems(items));
            }

            case Expr.Block(var alg):
            {
                var wired = WireToCaller(ctx, alg);
                if (wired.Params.Count == 0)
                    return EvalAlgOutput(wired, ctx, valEnv);
                var blockSpan = expr.Span ?? FirstSpan(wired.Output);
                return new EvalError.UnresolvedImplicitParams(wired.Params) { Span = blockSpan };
            }

            case Expr.Resolve(var name):
            {
                var resolvedR = ResolveAlg(expr, ctx);
                if (resolvedR.IsError)
                {
                    var err = resolvedR.Error;
                    return err.Span is null ? err with { Span = expr.Span } : err;
                }
                return WithSpan(expr.Span, EvalAlgOutput(resolvedR.Value, ctx, valEnv));
            }

            case Expr.DotCall(var dotTarget, var dotName, var dotArgs):
                // Lean: eval (.dotCall o n argsOpt) => withCtx (CtxMsg.dotCall o n) do evalDotCall
                return WithSpan(expr.Span, WithCtx(CtxDotCall(dotTarget, dotName),
                    EvalDotCall(dotTarget, dotName, dotArgs, ctx, valEnv)));

            case Expr.Call(var func, var argsAlg):
                return WithSpan(expr.Span, WithCtx(CtxCall(func),
                    EvalCall(func, argsAlg, ctx, valEnv)));

            case Expr.Index(var target, var selector):
            {
                var targetR = Eval(target, ctx, valEnv);
                if (targetR.IsError) return targetR.Error;
                var nR = EvalInt(selector, ctx, valEnv);
                if (nR.IsError) return nR.Error;
                var n = nR.Value;
                if (n < 0 || n != Math.Floor(n))
                    return new EvalError.BadIndex() { Span = expr.Span };
                var indexed = targetR.Value.Index((int)n);
                if (indexed is null) return new EvalError.BadIndex() { Span = expr.Span };
                return EvalResult<Result>.Ok(indexed);
            }

            case Expr.NativeCall(var fnName, var argNames):
                return EvalNativeCall(fnName, argNames, valEnv);

            // Catch-all: uses Expr.kind for clear diagnostics
            default:
                return new EvalError.IllegalInEval(ExprKind(expr)) { Span = expr.Span };
        }
    }

    private static EvalResult<Result> EvalNativeCall(
        string fnName,
        IReadOnlyList<string> argNames,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var args = new decimal[argNames.Count];
        for (var i = 0; i < argNames.Count; i++)
        {
            var val = LookupVal(valEnv, argNames[i]);
            if (val is null) return new EvalError.UnknownName(argNames[i]);
            var num = val.AsNum();
            if (num is null)
                return val is Result.Str
                    ? new EvalError.TypeMismatch("Expected a number, got a string")
                    : new EvalError.BadArity();
            args[i] = num.Value;
        }

        decimal result;
        try
        {
            switch (fnName)
            {
                case "Abs": result = Math.Abs(args[0]); break;
                case "Ceil": result = Math.Ceiling(args[0]); break;
                case "Floor": result = Math.Floor(args[0]); break;
                case "Round": result = Math.Round(args[0]); break;
                case "Sign": result = (decimal)Math.Sign(args[0]); break;
                case "Sqrt": result = (decimal)Math.Sqrt((double)args[0]); break;
                case "Ln": result = (decimal)Math.Log((double)args[0]); break;
                case "Lg": result = (decimal)Math.Log10((double)args[0]); break;
                case "Sin": result = (decimal)Math.Sin((double)args[0]); break;
                case "Asin": result = (decimal)Math.Asin((double)args[0]); break;
                case "Cos": result = (decimal)Math.Cos((double)args[0]); break;
                case "Acos": result = (decimal)Math.Acos((double)args[0]); break;
                case "Tan": result = (decimal)Math.Tan((double)args[0]); break;
                case "Atan": result = (decimal)Math.Atan((double)args[0]); break;
                case "Pow": result = (decimal)Math.Pow((double)args[0], (double)args[1]); break;
                case "Log": result = (decimal)Math.Log((double)args[0], (double)args[1]); break;
                default:
                    return new EvalError.IllegalInEval($"unknown native function: {fnName}");
            }
        }
        catch (OverflowException)
        {
            return new EvalError.NumericOverflow();
        }

        return EvalResult<Result>.Ok(new Result.Atom(result));
    }

    // ── Resolve argument expressions to algorithms (lazy) ───────────────────

    /// <summary>
    /// Resolve each output expression of args to sub-algorithms.
    /// Lean: resolveArgAlgs — wraps only liftable errors (notAnAlgorithm,
    /// illegalInEval) in trivial algorithms for lazy evaluation via evalAlgOutput.
    /// All other errors (unknownName, unknownProperty, ambiguousOpen, etc.)
    /// are propagated immediately to preserve precise diagnostics.
    /// </summary>
    private static EvalResult<IReadOnlyList<Algorithm>> ResolveArgAlgs(
        Algorithm argsAlg, EvalCtx ctx)
    {
        var result = new List<Algorithm>(argsAlg.Output.Count);
        foreach (var argExpr in argsAlg.Output)
        {
            var r = ResolveAlg(argExpr, ctx);
            if (r.IsOk)
            {
                result.Add(r.Value);
            }
            else if (IsLiftableError(r.Error))
            {
                // Wrap liftable non-resolvable expressions in a trivial algorithm.
                // evalAlgOutput will evaluate the expression lazily when needed.
                var wrapper = new Algorithm.User(
                    Parent: null, Params: [], Opens: [],
                    Properties: [], Output: [argExpr]);
                result.Add(WireToCaller(ctx, wrapper));
            }
            else
            {
                // Propagate genuine lookup/semantic failures immediately.
                return r.Error;
            }
        }
        return EvalResult<IReadOnlyList<Algorithm>>.Ok(result);
    }

    /// <summary>
    /// Errors that indicate an expression simply isn't an algorithm form and can
    /// safely be deferred to lazy evaluation (wrapping in Algorithm.ofExpr).
    /// </summary>
    private static bool IsLiftableError(EvalError error) => error switch
    {
        EvalError.NotAnAlgorithm => true,
        EvalError.IllegalInEval => true,
        EvalError.WithContext(_, var inner) => IsLiftableError(inner),
        _ => false,
    };

    /// <summary>
    /// Try to resolve each argument expression to an algorithm.
    /// Returns Some(alg) for expressions that resolve, null for those that don't.
    /// Lean: tryResolveArgAlgs.
    /// </summary>
    private static EvalResult<IReadOnlyList<Algorithm?>> TryResolveArgAlgs(
        Algorithm argsAlg, EvalCtx ctx)
    {
        var result = new List<Algorithm?>(argsAlg.Output.Count);
        foreach (var argExpr in argsAlg.Output)
        {
            var r = ResolveAlg(argExpr, ctx);
            if (r.IsOk)
            {
                result.Add(r.Value);
            }
            else if (IsLiftableError(r.Error))
            {
                result.Add(null);
            }
            else
            {
                return r.Error;
            }
        }
        return EvalResult<IReadOnlyList<Algorithm?>>.Ok(result);
    }

    /// <summary>
    /// Bind algorithm-typed parameters: zip parameter names with algorithms.
    /// Only includes entries where the argument resolved to an algorithm.
    /// Lean: bindAlgParams.
    /// </summary>
    private static IReadOnlyList<(string, Algorithm)> BindAlgParams(
        IReadOnlyList<string> paramNames,
        IReadOnlyList<Algorithm?> algs)
    {
        var result = new List<(string, Algorithm)>();
        var count = Math.Min(paramNames.Count, algs.Count);
        for (var i = 0; i < count; i++)
        {
            if (algs[i] is { } alg)
                result.Add((paramNames[i], alg));
        }
        return result;
    }

    // ── Call evaluation ─────────────────────────────────────────────────────

    /// <summary>
    /// Lean: evalCall → EvalM Result.
    /// 1. Resolve callee.
    /// 2. If builtin: resolve args lazily as algorithms, dispatch to applyBuiltin.
    /// 3. If user-defined: delegate to EvalUserCall (dual-view argument binding).
    /// </summary>
    private static EvalResult<Result> EvalCall(
        Expr func,
        Algorithm argsAlg,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        // 1. Resolve callee
        var calleeR = ResolveAlg(func, ctx);
        if (calleeR.IsError) return calleeR.Error;
        var callee = calleeR.Value;

        // 2. Dispatch on algorithm kind
        if (callee is Algorithm.Builtin(var builtinId))
        {
            // Builtin: resolve args lazily as algorithms
            var argAlgsR = ResolveArgAlgs(argsAlg, ctx);
            if (argAlgsR.IsError) return argAlgsR.Error;
            return ApplyBuiltin(builtinId, argAlgsR.Value, ctx, valEnv);
        }

        // 3. Conditional algorithm: dispatch to dedicated path (Lean: evalConditionalCall)
        if (callee is Algorithm.Conditional)
        {
            return EvalConditionalCall(callee, argsAlg, ctx, valEnv, OpenExprName(func));
        }

        // 4. User-defined: delegate to EvalUserCall (Lean: evalUserCall)
        return EvalUserCall(callee, argsAlg, ctx, valEnv);
    }

    // ── Conditional algorithm call (Lean: evalConditionalCall) ──────────────

    /// <summary>
    /// Evaluates a conditional algorithm call.
    /// 1. Evaluate argument expressions eagerly.
    /// 2. Assemble full argument Result shape (preserving grouping for pattern matching).
    /// 3. Try branches in order; first match wins.
    /// 4. Evaluate selected branch body with pattern bindings prepended to env.
    /// 5. If no branch matches, raise NoMatchingBranch error.
    ///
    /// <para><b>Full-input-specification rule</b>: the branch body receives input
    /// bindings ONLY from the matched pattern. No extra implicit parameters are
    /// inferred. Free identifiers in the body resolve through ordinary lexical /
    /// property / open / builtin lookup, or produce unknownName at runtime.</para>
    ///
    /// <para><b>Assumes uniform output arity</b>: after validation
    /// (<see cref="CondBranch.TopLevelOutputArity"/>), all branches produce the
    /// same top-level output arity. The evaluator does not re-check this at
    /// runtime.</para>
    ///
    /// Lean: evalConditionalCall.
    /// </summary>
    private static EvalResult<Result> EvalConditionalCall(
        Algorithm callee, Algorithm args,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv,
        string calleeName = "conditional")
    {
        if (callee.HasDuplicateBranchPatterns())
            return new EvalError.DuplicateBranchPattern();

        var wiredArgs = WireToCaller(ctx, args);
        var argExprs = wiredArgs.Output;
        var argEvalCtx = ctx.Push(wiredArgs);

        // Evaluate all argument expressions eagerly
        var argResults = new List<Result>();
        foreach (var expr in argExprs)
        {
            var r = Eval(expr, argEvalCtx, valEnv);
            if (r.IsError) return r.Error;
            argResults.Add(r.Value);
        }

        // Assemble full argument shape: normalize for pattern matching
        var argShape = Result.FromItems(argResults);

        // Try branches in order
        var match = MatchBranches(callee.Branches, argShape);
        if (match is null)
            return new EvalError.NoMatchingBranch(calleeName);

        var (branch, bindings) = match.Value;

        // Wire the branch body to the callee's scope so it can access the enclosing
        // algorithm's properties (e.g. TomatoPrice, ApplePrice) via the parent chain.
        // Mirrors Algorithm.childOf semantics used for normal property lookup.
        var wiredBody = ChildOf(callee, branch.Body);

        // Evaluate the matched branch body with bindings prepended
        var newCtx = ctx.Push(callee);
        var newEnv = Concat(bindings, valEnv);
        return EvalAlgOutput(wiredBody, newCtx, newEnv);
    }

    // ── User-defined call (Lean: evalUserCall) ────────────────────────────

    /// <summary>
    /// Shared user-defined call binding logic (Lean: evalUserCall).
    /// Dual-view semantics: each original argument expression is independently
    /// interpreted in two ways:
    /// <list type="bullet">
    ///   <item>Structural algorithm resolution → AlgEnv (callable meaning)</item>
    ///   <item>Eager value evaluation → ValEnv (value meaning)</item>
    /// </list>
    /// If both succeed, the parameter gets both meanings (dual-view).
    /// If only algorithm resolution succeeds, only AlgEnv is bound.
    /// If only value evaluation succeeds, only ValEnv is bound.
    /// If both fail, the eager-evaluation error is propagated.
    ///
    /// Argument expressions may be fewer than parameters because a single
    /// eager value can unpack to multiple positional results, but an explicit
    /// argument list may not contain more expressions than the callee has
    /// parameters.
    /// </summary>
    private static EvalResult<Result> EvalUserCall(
        Algorithm callee, Algorithm args,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var wiredArgs = WireToCaller(ctx, args);
        var argExprs = wiredArgs.Output;
        var paramCount = callee.Params.Count;

        // Lean: if argExprs.length > paramCount then error (arityMismatch ...)
        if (argExprs.Count > paramCount)
            return new EvalError.ArityMismatch(paramCount, argExprs.Count);

        // Try to resolve each arg as algorithm (for AlgEnv bindings)
        var maybeAlgsR = TryResolveArgAlgs(wiredArgs, ctx);
        if (maybeAlgsR.IsError) return maybeAlgsR.Error;
        var maybeAlgs = maybeAlgsR.Value;
        var algBindings = BindAlgParams(callee.Params, maybeAlgs);

        // Lean: let argEvalCtx := EvalCtx.push wiredArgs ctx
        var argEvalCtx = ctx.Push(wiredArgs);

        // Lean: collectValues — per-expression independent evaluation.
        // For each (param, argExpr, maybeAlg) triple:
        //   eval succeeds → include (param, value) in value bindings
        //   eval fails + has algorithm → skip this param's value binding
        //   eval fails + no algorithm → propagate error
        var valueParams = new List<string>();
        var valueResults = new List<Result>();

        for (var i = 0; i < paramCount; i++)
        {
            if (i >= argExprs.Count)
            {
                // Lean: | ps, [], _ => pure (ps, []) — remaining params, no more exprs
                valueParams.Add(callee.Params[i]);
                continue;
            }

            var evalR = Eval(argExprs[i], argEvalCtx, valEnv);
            if (evalR.IsOk)
            {
                valueParams.Add(callee.Params[i]);
                valueResults.Add(evalR.Value);
            }
            else if (i < maybeAlgs.Count && maybeAlgs[i] is not null)
            {
                // Has algorithm binding → skip value binding for this param
            }
            else
            {
                // No algorithm → propagate eval error
                return evalR.Error;
            }
        }

        // Lean: unpackArgs (Result.normalize (Result.group valueResults))
        IReadOnlyList<Result> unpackedValueResults;
        if (valueResults.Count == 0)
        {
            unpackedValueResults = [];
        }
        else
        {
            unpackedValueResults = UnpackArgs(Result.FromItems(valueResults));
        }

        var argEnvR = BindParams(valueParams, unpackedValueResults);
        if (argEnvR.IsError) return argEnvR.Error;

        var newCtx = ctx.WithAlgEnv(Concat(algBindings, ctx.AlgEnv));
        var newEnv = Concat(argEnvR.Value, valEnv);
        return EvalAlgOutput(callee, newCtx, newEnv);
    }

    // ── DotCall evaluation ────────────────────────────────────────────────

    /// <summary>
    /// Evaluates dotCall: <c>a.f</c> or <c>a.f(args)</c>
    /// Smart dispatch:
    /// 1. Structural intrinsic (length) → output expression count of target
    /// 2. Value-based intrinsic (string) → evaluate target, convert numeric result to string
    /// 3. Structural property found (navigation-only):
    ///    - No args + 0-param → value access
    ///    - No args + has params → arity mismatch error
    ///    - Has args → delegate to EvalUserCall (dual-view binding, no receiver injection)
    /// 4. No property → lexical fallback (receiver injection via callLexicalWithReceiver)
    /// When resolveAlg returns notAnAlgorithm (e.g. numeric literal target),
    /// value-based intrinsics are checked before lexical fallback.
    /// Structural property calls use the same higher-order binding logic as normal
    /// user-defined calls (both delegate to EvalUserCall).
    /// Lean: evalDotCall.
    /// </summary>
    private static EvalResult<Result> EvalDotCall(
        Expr target, string name, Algorithm? argsOpt,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        // Lean: let targetAlg <- resolveAlg target ctx
        // Extension-property rule: if target is a value-producing expression (not an algorithm),
        // ResolveAlg returns NotAnAlgorithm — check value-based intrinsics first,
        // then fall back to lexical lookup so that
        //   e.P      → P(e)
        //   e.P(a,b) → P(e, a, b)
        // works for any receiver expression, including literals and parenthesized expressions.
        // Other errors (e.g. UnknownName) propagate as before.
        var targetResult = ResolveAlg(target, ctx);
        if (targetResult.IsError)
        {
            if (targetResult.Error is EvalError.NotAnAlgorithm)
            {
                // Value-only target (e.g. numeric literal): check value-based intrinsics
                if (name == "string")
                {
                    var val = Eval(target, ctx, valEnv);
                    if (val.IsError) return val.Error;
                    return ResultToString(val.Value);
                }
                return CallLexicalWithReceiver(name, target, argsOpt, ctx, valEnv);
            }
            return targetResult.Error;
        }
        var targetAlg = targetResult.Value;

        // Lean: evalStructuralIntrinsic? — structural intrinsics (length)
        var intrinsic = EvalStructuralIntrinsic(targetAlg, name);
        if (intrinsic is { } r) return r;

        // Value-based intrinsic: "string" — evaluate algorithm output and convert
        if (name == "string")
        {
            var val = EvalAlgOutput(targetAlg, ctx, valEnv);
            if (val.IsError) return val.Error;
            return ResultToString(val.Value);
        }

        // Structural: property of target (any visibility — dot access sees private)
        var prop = LookupProp(targetAlg, name);
        if (prop is not null)
        {
            var wired = ChildOf(targetAlg, prop);

            // Conditional algorithms: dedicated dispatch
            if (wired is Algorithm.Conditional)
            {
                if (argsOpt is null)
                    return new EvalError.NoMatchingBranch(name);
                return EvalConditionalCall(wired, argsOpt, ctx, valEnv, name);
            }

            if (argsOpt is null)
            {
                // No args: 0-param → value access, has params → arity error
                if (wired.Params.Count == 0)
                    return EvalAlgOutput(wired, ctx, valEnv);
                return new EvalError.ArityMismatch(wired.Params.Count, 0);
            }
            // Has args → navigation only: direct argument binding, no receiver
            // Lean: evalUserCall wired args ctx env
            return EvalUserCall(wired, argsOpt, ctx, valEnv);
        }

        // Lexical fallback (receiver injection via callLexicalWithReceiver)
        return CallLexicalWithReceiver(name, target, argsOpt, ctx, valEnv);
    }

    /// <summary>
    /// Resolves name lexically and calls with receiver prepended to args.
    /// Delegates to EvalCall to get builtin dispatch for free.
    ///
    /// For dotCall lexical fallback to "while" and "repeat", extra args beyond the
    /// builtin's expected explicit-arg count are packaged into a single Expr.Block
    /// init-state argument. This lowering cannot happen in the parser because dotCall
    /// must first check for structural properties (which shadow builtins).
    ///
    /// Packaging rules (explicit args = extraArgs.Output, receiver already prepended):
    ///   while:  0–1 explicit args → pass through (arity 2 already satisfied or error)
    ///           ≥2 explicit args  → package all explicit args as one block init
    ///   repeat: 0–2 explicit args → pass through (arity 3 already satisfied or error)
    ///           ≥3 explicit args  → first explicit = count, rest = block init
    ///
    /// Lean: callLexicalWithReceiver.
    /// </summary>
    private static EvalResult<Result> CallLexicalWithReceiver(
        string name, Expr receiver, Algorithm? extraArgs,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var outputExprs = new List<Expr> { receiver };
        if (extraArgs is not null)
            outputExprs.AddRange(extraArgs.Output);

        // Package multi-item init for while/repeat dotCall fallback.
        // receiver is already at index 0 (the step algorithm).
        var explicitCount = extraArgs?.Output.Count ?? 0;

        if (name == "while" && explicitCount >= 2)
        {
            // Step.while(s1, s2, ...) → while(Step, block([s1, s2, ...]))
            var initExprs = outputExprs.GetRange(1, outputExprs.Count - 1);
            outputExprs = [receiver, MakeInitBlock(initExprs)];
        }
        else if (name == "repeat" && explicitCount >= 3)
        {
            // Step.repeat(n, s1, s2, ...) → repeat(Step, n, block([s1, s2, ...]))
            var countExpr = outputExprs[1]; // first explicit arg = count
            var initExprs = outputExprs.GetRange(2, outputExprs.Count - 2);
            outputExprs = [receiver, countExpr, MakeInitBlock(initExprs)];
        }

        var combinedArgs = new Algorithm.User(
            Parent: null, Params: [], Opens: [],
            Properties: [], Output: outputExprs);

        return EvalCall(new Expr.Resolve(name), combinedArgs, ctx, valEnv);
    }

    /// <summary>
    /// Creates a zero-parameter block expression wrapping the given expressions.
    /// Used to package multi-item init state for while/repeat lowering.
    /// </summary>
    private static Expr.Block MakeInitBlock(IReadOnlyList<Expr> exprs) =>
        new(new Algorithm.User(
            Parent: null, Params: [], Opens: [],
            Properties: [], Output: exprs));

    // ── Entry points ────────────────────────────────────────────────────────

    /// <summary>
    /// Run evaluation on an expression with prelude in scope.
    /// Lean: runResult → EvalM Result.
    /// </summary>
    public static EvalResult<Result> Run(Expr expr)
        => Eval(expr, new EvalCtx([PreludeAlg], []), []);

    /// <summary>
    /// Run evaluation and flatten to atoms.
    /// Lean: runFlat → EvalM (List Int).
    /// </summary>
    public static EvalResult<IReadOnlyList<decimal>> RunFlat(Expr expr)
    {
        var r = Run(expr);
        if (r.IsError) return r.Error;
        return EvalResult<IReadOnlyList<decimal>>.Ok(r.Value.ToAtoms());
    }

    // ── Utility ──────────────────────────────────────────────────────────────

    /// <summary>
    /// Exact decimal exponentiation for non-negative integer exponents.
    /// Falls back to Math.Pow (via double) for fractional exponents.
    /// Lean: intPow b n = b * intPow b (n-1), base case intPow _ 0 = 1.
    /// </summary>
    private static decimal DecimalPow(decimal b, decimal exp)
    {
        if (exp != Math.Floor(exp))
            return (decimal)Math.Pow((double)b, (double)exp);

        var n = (long)exp;
        decimal result = 1;
        var baseVal = b;
        // Exponentiation by squaring
        while (n > 0)
        {
            if ((n & 1) == 1)
                result *= baseVal;
            baseVal *= baseVal;
            n >>= 1;
        }
        return result;
    }

    private static IReadOnlyList<T> Prepend<T>(T item, IReadOnlyList<T> list)
    {
        var result = new List<T>(list.Count + 1) { item };
        result.AddRange(list);
        return result;
    }

    private static IReadOnlyList<T> Concat<T>(IReadOnlyList<T> a, IReadOnlyList<T> b)
    {
        var result = new List<T>(a.Count + b.Count);
        result.AddRange(a);
        result.AddRange(b);
        return result;
    }
}
