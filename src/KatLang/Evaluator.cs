namespace KatLang;

/// <summary>
/// KatLang 0.75 evaluator matching the Lean specification.
/// Uses <see cref="EvalResult{T}"/> (<c>EvalM := Except Error</c>) for structured errors
/// instead of nullable returns.
/// Ownership-first lookup: local → parent chain structural → opens fallback across chain.
/// Property visibility: opens only expose PUBLIC properties; structural lookup sees all.
///
/// Builtins (If, While, Repeat, Atoms, Range, Filter, Map, Count, Min, Max, Sum, Reduce) are injected via a prelude algorithm in the initial
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
    internal readonly record struct MemoizationStats(
        int PropertyCacheHitCount,
        int PropertyCacheStoreCount,
        int PropertyCacheMissCount,
        int PropertyCacheBypassCount);

    private readonly record struct MemoizedPropertyResult(Result Value, int EmittedCount);

    private enum PropertyMemoLookup
    {
        Hit,
        Miss,
        InProgress,
    }

    private enum PropertyMemoKind
    {
        LexicalClosedResolve,
        LexicalContextualResolve,
        StructuralDot,
    }

    private static readonly object ClosedLexicalPropertyMemoContextToken = new();

    private readonly record struct PropertyMemoKey(
        PropertyMemoKind Kind,
        string Name,
        object CallStackToken,
        object AlgEnvToken,
        object ValEnvToken,
        object? BindingToken);

    private sealed class PropertyMemoKeyComparer : IEqualityComparer<PropertyMemoKey>
    {
        public static readonly PropertyMemoKeyComparer Instance = new();

        public bool Equals(PropertyMemoKey x, PropertyMemoKey y)
            => x.Kind == y.Kind
                && StringComparer.Ordinal.Equals(x.Name, y.Name)
                && ReferenceEquals(x.CallStackToken, y.CallStackToken)
                && ReferenceEquals(x.AlgEnvToken, y.AlgEnvToken)
                && ReferenceEquals(x.ValEnvToken, y.ValEnvToken)
                && ReferenceEquals(x.BindingToken, y.BindingToken);

        public int GetHashCode(PropertyMemoKey key)
        {
            var hash = new HashCode();
            hash.Add((int)key.Kind);
            hash.Add(key.Name, StringComparer.Ordinal);
            hash.Add(System.Runtime.CompilerServices.RuntimeHelpers.GetHashCode(key.CallStackToken));
            hash.Add(System.Runtime.CompilerServices.RuntimeHelpers.GetHashCode(key.AlgEnvToken));
            hash.Add(System.Runtime.CompilerServices.RuntimeHelpers.GetHashCode(key.ValEnvToken));
            hash.Add(key.BindingToken is null
                ? 0
                : System.Runtime.CompilerServices.RuntimeHelpers.GetHashCode(key.BindingToken));
            return hash.ToHashCode();
        }
    }

    private readonly record struct LexicalPropertyReference(
        Property Binding,
        ScopeCtx DefinitionScope);

    private readonly record struct ResolvedLexicalProperty(
        Algorithm ResolvedAlgorithm,
        LexicalPropertyReference Reference);

    private readonly record struct LexicalPropertyBinding(
        string Name,
        object BindingToken,
        bool IsClosedForMemoization);

    private sealed class EvaluatorRunState
    {
        private readonly Dictionary<PropertyMemoKey, MemoizedPropertyResult> _memoizedPropertyResults =
            new(PropertyMemoKeyComparer.Instance);

        private readonly HashSet<PropertyMemoKey> _memoizedPropertyResultsInProgress =
            new(PropertyMemoKeyComparer.Instance);

        private readonly Dictionary<Algorithm, LexicalPropertyBinding> _resolvedLexicalPropertyBindings =
            new(ReferenceEqualityComparer.Instance);

        private readonly Dictionary<LexicalPropertyReference, bool> _contextIndependentLexicalBindings =
            [];

        private int _propertyCacheHitCount;
        private int _propertyCacheStoreCount;
        private int _propertyCacheMissCount;
        private int _propertyCacheBypassCount;

        public MemoizationStats SnapshotStats()
            => new(
                _propertyCacheHitCount,
                _propertyCacheStoreCount,
                _propertyCacheMissCount,
                _propertyCacheBypassCount);

        public void RegisterResolvedLexicalPropertyBinding(
            Algorithm resolvedAlgorithm,
            LexicalPropertyBinding binding)
        {
            if (resolvedAlgorithm is Algorithm.Builtin)
                return;

            _resolvedLexicalPropertyBindings[resolvedAlgorithm] = binding;
        }

        public bool TryGetResolvedLexicalPropertyBinding(
            Algorithm resolvedAlgorithm,
            out LexicalPropertyBinding binding)
            => _resolvedLexicalPropertyBindings.TryGetValue(resolvedAlgorithm, out binding);

        public bool TryGetContextIndependentLexicalBinding(
            LexicalPropertyReference reference,
            out bool isContextIndependent)
            => _contextIndependentLexicalBindings.TryGetValue(reference, out isContextIndependent);

        public void StoreContextIndependentLexicalBinding(
            LexicalPropertyReference reference,
            bool isContextIndependent)
            => _contextIndependentLexicalBindings[reference] = isContextIndependent;

        public PropertyMemoLookup TryGetMemoizedPropertyResult(
            PropertyMemoKey key,
            out MemoizedPropertyResult result)
        {
            if (_memoizedPropertyResults.TryGetValue(key, out result))
            {
                _propertyCacheHitCount++;
                return PropertyMemoLookup.Hit;
            }

            if (_memoizedPropertyResultsInProgress.Contains(key))
            {
                _propertyCacheBypassCount++;
                result = default;
                return PropertyMemoLookup.InProgress;
            }

            _propertyCacheMissCount++;
            _memoizedPropertyResultsInProgress.Add(key);
            result = default;
            return PropertyMemoLookup.Miss;
        }

        public void StoreMemoizedPropertyResult(PropertyMemoKey key, MemoizedPropertyResult result)
        {
            _memoizedPropertyResultsInProgress.Remove(key);
            _memoizedPropertyResults[key] = result;
            _propertyCacheStoreCount++;
        }

        public void ClearMemoizedPropertyResult(PropertyMemoKey key)
            => _memoizedPropertyResultsInProgress.Remove(key);
    }

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
        IReadOnlyList<(string Name, Algorithm Value)> AlgEnv,
        EvaluatorRunState RunState)
    {
        public static readonly EvalCtx Empty = new([], [], new EvaluatorRunState());

        /// <summary>Lean: EvalCtx.push — prepend an algorithm to the call stack.</summary>
        public EvalCtx Push(Algorithm alg) => new(Prepend(alg, CallStack), AlgEnv, RunState);

        /// <summary>Lean: EvalCtx.head? — first algorithm in the call stack.</summary>
        public Algorithm? Head => CallStack.Count > 0 ? CallStack[0] : null;

        /// <summary>Lean: EvalCtx.withAlgEnv — replace the algorithm environment.</summary>
        public EvalCtx WithAlgEnv(IReadOnlyList<(string, Algorithm)> algEnv) => new(CallStack, algEnv, RunState);
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

    private static Property? LookupPropBinding(Algorithm alg, string name)
    {
        foreach (var prop in alg.Properties)
            if (prop.Name == name) return prop;
        return null;
    }

    /// <summary>Lean: Algorithm.lookupPublicProp (public only).</summary>
    private static Algorithm? LookupPublicProp(Algorithm alg, string name)
    {
        foreach (var prop in alg.Properties)
            if (prop.Name == name && prop.IsPublic) return prop.Value;
        return null;
    }

    private static Property? LookupPublicPropBinding(Algorithm alg, string name)
    {
        foreach (var prop in alg.Properties)
            if (prop.Name == name && prop.IsPublic) return prop;
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
        Expr.Param(var n) => n,
        Expr.Num(var n) => n.ToString(System.Globalization.CultureInfo.InvariantCulture),
        Expr.StringLiteral(var s) => $"'{s}'",
        Expr.Unary(var op, var operand) => op switch
        {
            UnaryOp.Minus => $"-{OpenExprUnaryOperandName(operand)}",
            UnaryOp.Not => $"not {OpenExprUnaryOperandName(operand)}",
            _ => $"({ExprKind(e)})",
        },
        Expr.Binary(var op, var left, var right) => $"({OpenExprName(left)} {OpenExprBinaryOp(op)} {OpenExprName(right)})",
        Expr.Index(var target, var selector) => $"{OpenExprName(target)}[{OpenExprName(selector)}]",
        Expr.DotCall(var o, var n, var argsOpt) => argsOpt is null
            ? OpenExprName(o) + "." + n
            : OpenExprName(o) + "." + n + "(...)",
        Expr.Call(var f, _) => OpenExprName(f) + "(...)",
        Expr.Grace(var inner, var weight) => weight < 0
            ? "~" + OpenExprName(inner)
            : OpenExprName(inner) + "~",
        Expr.Block => "(inline library)",
        Expr.Combine(var a, var b) => OpenExprName(a) + " + " + OpenExprName(b),
        _ => $"({ExprKind(e)})",
    };

    private static string OpenExprUnaryOperandName(Expr expr) => expr switch
    {
        Expr.Param or Expr.Resolve or Expr.Num or Expr.StringLiteral or Expr.DotCall or Expr.Index
            => OpenExprName(expr),
        _ => $"({OpenExprName(expr)})",
    };

    private static string OpenExprBinaryOp(BinaryOp op) => op switch
    {
        BinaryOp.Add => "+",
        BinaryOp.Sub => "-",
        BinaryOp.Mul => "*",
        BinaryOp.Div => "/",
        BinaryOp.IDiv => "div",
        BinaryOp.Mod => "mod",
        BinaryOp.Pow => "^",
        BinaryOp.Lt => "<",
        BinaryOp.Gt => ">",
        BinaryOp.Le => "<=",
        BinaryOp.Ge => ">=",
        BinaryOp.Eq => "==",
        BinaryOp.Ne => "!=",
        BinaryOp.And => "and",
        BinaryOp.Or => "or",
        BinaryOp.Xor => "xor",
        _ => "?",
    };

    // ── Context string helpers (Lean: CtxMsg.openMsg, CtxMsg.call, CtxMsg.dotCall) ─

    private static string CtxOpen(string key) => $"while resolving open: {key}";
    private static string CtxCall(Expr f) => $"while evaluating call to {OpenExprName(f)}";
    private static string CtxProperty(string name) => $"while evaluating property {name}";
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

    private static EvalResult<T> WithPropertyContextOnMissingOutput<T>(string name, SourceSpan? span, EvalResult<T> result)
    {
        if (result.IsError && result.Error is EvalError.MissingOutput)
            return WithSpan<T>(span, new EvalError.WithContext(CtxProperty(name), result.Error));

        return WithSpan(span, result);
    }

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

    private static LexicalPropertyReference? LookupInParentsDirectBinding(ScopeCtx sc, string name)
    {
        foreach (var prop in sc.Properties)
        {
            if (prop.Name == name)
                return new LexicalPropertyReference(prop, sc);
        }

        return sc.Parent is { } parent ? LookupInParentsDirectBinding(parent, name) : null;
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
    private readonly record struct OpenHit(string Provider, Algorithm Lib, Property Binding);

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
    private static EvalResult<ResolvedLexicalProperty?> LookupOpens(
        Algorithm alg, string name, EvalCtx ctx)
    {
        if (alg.Opens.Count == 0) return EvalResult<ResolvedLexicalProperty?>.Ok(null);

        var innerCtx = ctx.Push(alg);
        var resolvedResult = ResolveAllOpens(alg, innerCtx);
        if (resolvedResult.IsError) return resolvedResult.Error;

        var hits = new List<OpenHit>();

        // Public-only filtering: only public properties visible through opens
        foreach (var ri in resolvedResult.Value)
        {
            var binding = LookupPublicPropBinding(ri.Lib, name);
            if (binding is not null)
                hits.Add(new OpenHit(ri.Key, ri.Lib, binding));
        }

        if (hits.Count == 0)
            return EvalResult<ResolvedLexicalProperty?>.Ok(null);
        if (hits.Count == 1)
        {
            var hit = hits[0];
            return EvalResult<ResolvedLexicalProperty?>.Ok(
                new ResolvedLexicalProperty(
                    ChildOf(hit.Lib, hit.Binding.Value),
                    new LexicalPropertyReference(hit.Binding, AsScopeCtx(hit.Lib))));
        }
        return new EvalError.AmbiguousOpen(name, hits.Select(h => h.Provider).ToList());
    }

    // ── Lexical resolution (ownership-first) ────────────────────────────────

    /// <summary>
    /// Open-based lookup in parent chain (helper for LookupOpensInChain).
    /// Checks opens at each level of the parent chain as fallback.
    /// Lean: lookupOpensInParentChain → EvalM (Option Algorithm).
    /// </summary>
    private static EvalResult<ResolvedLexicalProperty?> LookupOpensInParentChain(
        ScopeCtx sc, string name, EvalCtx ctx)
    {
        var tempAlg = ForOpens(sc);
        var openResult = LookupOpens(tempAlg, name, ctx);
        if (openResult.IsError) return openResult.Error;
        if (openResult.Value is not null)
            return EvalResult<ResolvedLexicalProperty?>.Ok(openResult.Value);

        return sc.Parent is { } parent
            ? LookupOpensInParentChain(parent, name, ctx)
            : EvalResult<ResolvedLexicalProperty?>.Ok(null);
    }

    /// <summary>
    /// Open-based lookup across the algorithm chain (current first, then parents).
    /// Checks opens at each level of the parent chain as fallback.
    /// Lean: lookupOpensInChain → EvalM (Option Algorithm).
    /// </summary>
    private static EvalResult<ResolvedLexicalProperty?> LookupOpensInChain(
        Algorithm alg, string name, EvalCtx ctx)
    {
        // Try opens at current level
        var openResult = LookupOpens(alg, name, ctx);
        if (openResult.IsError) return openResult.Error;
        if (openResult.Value is not null)
            return EvalResult<ResolvedLexicalProperty?>.Ok(openResult.Value);

        // Try parent chain
        return alg.Parent is { } sc
            ? LookupOpensInParentChain(sc, name, ctx)
            : EvalResult<ResolvedLexicalProperty?>.Ok(null);
    }

    /// <summary>
    /// Full lexical lookup with ownership-first model:
    /// 1. Local properties (owned by this algorithm — any visibility)
    /// 2. Parent chain structural properties (owned by ancestors — any visibility, no opens)
    /// 3. Opens as fallback across the entire chain (public only)
    /// Structural ownership always takes precedence over opens.
    /// Lean: lookupLexical → EvalM Algorithm.
    /// </summary>
    private static EvalResult<ResolvedLexicalProperty> LookupLexical(
        Algorithm alg, string name, EvalCtx ctx)
    {
        // 1. Local properties (any visibility)
        var local = LookupPropBinding(alg, name);
        if (local is not null)
        {
            return EvalResult<ResolvedLexicalProperty>.Ok(
                new ResolvedLexicalProperty(
                    ChildOf(alg, local.Value),
                    new LexicalPropertyReference(local, AsScopeCtx(alg))));
        }

        // 2. Parent chain structural only (any visibility, no opens)
        if (alg.Parent is { } sc)
        {
            var structural = LookupInParentsDirectBinding(sc, name);
            if (structural is not null)
            {
                return EvalResult<ResolvedLexicalProperty>.Ok(
                    new ResolvedLexicalProperty(
                        WithParent(structural.Value.Binding.Value, structural.Value.DefinitionScope),
                        structural.Value));
            }
        }

        // 3. Opens fallback across the entire chain (public only)
        var opensResult = LookupOpensInChain(alg, name, ctx);
        if (opensResult.IsError) return opensResult.Error;
        if (opensResult.Value is { } openBinding)
            return EvalResult<ResolvedLexicalProperty>.Ok(openBinding);

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
    /// Require an exact integer-valued number for integer-only builtins.
    /// Lean's core uses <c>Int</c> directly, while C# allows decimals and must reject fractional values explicitly.
    /// </summary>
    private static EvalResult<decimal> ExpectWholeInt(Result r, string description)
    {
        var valueR = ExpectInt(r);
        if (valueR.IsError) return valueR.Error;
        if (valueR.Value != Math.Truncate(valueR.Value))
            return new EvalError.IllegalInEval($"{description} must be an integer");
        return valueR;
    }

    /// <summary>
    /// Build the inclusive integer result for <c>range(start, stop)</c>.
    /// Counts upward when <c>start &lt;= stop</c> and downward otherwise.
    /// </summary>
    private static Result BuildInclusiveRange(decimal start, decimal stop)
    {
        var items = new List<Result>();

        if (start <= stop)
        {
            for (var current = start; current <= stop; current += 1m)
                items.Add(new Result.Atom(current));
        }
        else
        {
            for (var current = start; current >= stop; current -= 1m)
                items.Add(new Result.Atom(current));
        }

        return Result.FromItems(items);
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

    /// <summary>
    /// Lean: <c>resultToExpr</c>. Reify a normalized result as an expression that
    /// evaluates back to the same shape.
    /// </summary>
    private static Expr EmptyResultExpr()
        => new Expr.Call(
            new Expr.Block(new Algorithm.Builtin(BuiltinId.@if)),
            new Algorithm.User(
                Parent: null,
                Params: [],
                Opens: [],
                Properties: [],
                Output: [new Expr.Num(0), new Expr.Num(0)]));

    private static Expr ResultToExpr(Result result) => result switch
    {
        Result.Atom(var n) => new Expr.Num(n),
        Result.Str(var s) => new Expr.StringLiteral(s),
        Result.Group(var items) when items.Count == 0 => EmptyResultExpr(),
        Result.Group(var items) => new Expr.Block(new Algorithm.User(
            Parent: null,
            Params: [],
            Opens: [],
            Properties: [],
            Output: items.Select(ResultToExpr).ToList())),
        _ => EmptyResultExpr(),
    };

    /// <summary>Lean: <c>Algorithm.ofExpr</c>.</summary>
    private static Algorithm AlgorithmOfExpr(Expr expr) => new Algorithm.User(
        Parent: null,
        Params: [],
        Opens: [],
        Properties: [],
        Output: [expr]);

    /// <summary>
    /// Counted evaluation result: the normalized value paired with the number of
    /// top-level values emitted at the current algorithm boundary.
    /// Lean: <c>CountedResult</c>.
    /// </summary>
    private readonly record struct CountedResult(Result Value, int EmittedCount);

    /// <summary>
    /// Validate the output shape required by counted builtins that must emit
    /// exactly one top-level value. Non-empty grouped values are valid; empty
    /// results and multiple top-level outputs are rejected.
    /// Lean: <c>expectSingleValueWith</c>.
    /// </summary>
    private static EvalResult<Result> ExpectSingleEmittedValue(CountedResult output, string errorMessage)
        => output.EmittedCount == 1
            ? EvalResult<Result>.Ok(output.Value)
            : new EvalError.WithContext(
                errorMessage,
                new EvalError.BadArity());

    /// <summary>
    /// Validate the output shape required by <c>reduce</c>.
    /// Lean: <c>expectSingleAccumulator</c>.
    /// </summary>
    private static EvalResult<Result> ExpectSingleAccumulator(CountedResult output)
        => ExpectSingleEmittedValue(output, "reduce step must return a single accumulator value");

    /// <summary>
    /// Validate the output shape required by <c>map</c>.
    /// Lean: <c>expectSingleMappedElement</c>.
    /// </summary>
    private static EvalResult<Result> ExpectSingleMappedElement(CountedResult output)
        => ExpectSingleEmittedValue(output, "map transform must return a single element");

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

    /// <summary>
    /// Compatibility fallback for manually constructed core conditionals.
    /// Surface clause elaboration should already classify whole same-name
    /// plain-binder clause groups as ordinary <see cref="Algorithm.User"/>
    /// values in the parser. This helper intentionally keeps only the stricter
    /// flat multi-binder raw <see cref="Algorithm.Conditional"/> core shape
    /// call-compatible with ordinary user-call semantics so evaluator fallback
    /// does not silently broaden to bare single-binder conditionals.
    /// </summary>
    private static Algorithm.User? TryGetFlatBinderUserEquivalent(Algorithm callee)
    {
        if (callee is not Algorithm.Conditional cond || cond.Branches.Count != 1)
            return null;

        var paramNames = cond.Branches[0].Pattern.TryGetFlatMultiBinderParams();
        if (paramNames is null)
            return null;

        return ChildOf(callee, cond.Branches[0].Body) is Algorithm.User body
            ? body with { Params = paramNames }
            : null;
    }

    /// <summary>
    /// Evaluate a conditional algorithm against an already-assembled argument
    /// shape. Used both for ordinary conditional calls and for builtins like
    /// <c>filter</c> and <c>map</c> that must pass one whole result without
    /// flattening it.
    /// Lean: <c>evalConditionalShape</c>.
    /// </summary>
    private static EvalResult<Result> EvalConditionalShape(
        Algorithm callee,
        Result argShape,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv,
        string calleeName = "conditional")
    {
        if (callee.HasDuplicateBranchPatterns())
            return new EvalError.DuplicateBranchPattern();

        var match = MatchBranches(callee.Branches, argShape);
        if (match is null)
            return new EvalError.NoMatchingBranch(calleeName);

        var (branch, bindings) = match.Value;
        var wiredBody = ChildOf(callee, branch.Body);
        var newCtx = ctx.Push(callee);
        var newEnv = Concat(bindings, valEnv);
        return EvalAlgOutput(wiredBody, newCtx, newEnv);
    }

    /// <summary>
    /// Evaluate a resolved algorithm on one whole result value.
    /// Grouped values are bound as a single input and are never unpacked into
    /// multiple positional arguments. This is required by <c>filter</c> and
    /// <c>map</c>, whose predicate / transform must inspect each collection
    /// element as a whole unit.
    /// Lean: <c>evalWholeArgCall</c>.
    /// </summary>
    private static EvalResult<Result> EvalWholeArgCall(
        Algorithm callee,
        Result arg,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv,
        string calleeName = "conditional")
    {
        switch (callee)
        {
            case Algorithm.Builtin(var builtin):
                return ApplyBuiltin(
                    builtin,
                    [AlgorithmOfExpr(ResultToExpr(arg))],
                    ctx,
                    valEnv);

            case Algorithm.Conditional:
                return EvalConditionalShape(callee, arg.Normalize(), ctx, valEnv, calleeName);

            default:
            {
                var argEnvR = BindParams(callee.Params, [arg]);
                if (argEnvR.IsError) return argEnvR.Error;
                return EvalAlgOutput(callee, ctx, Concat(argEnvR.Value, valEnv));
            }
        }
    }

    /// <summary>
    /// Evaluate a resolved algorithm on one whole result value while preserving
    /// the number of top-level values emitted by the callee.
    /// Lean: <c>evalWholeArgCallCounted</c>.
    /// </summary>
    private static EvalResult<CountedResult> EvalWholeArgCallCounted(
        Algorithm callee,
        Result arg,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv,
        string calleeName = "conditional")
    {
        switch (callee)
        {
            case Algorithm.Builtin(var builtin):
                return ApplyBuiltinCounted(
                    builtin,
                    [AlgorithmOfExpr(ResultToExpr(arg))],
                    ctx,
                    valEnv);

            case Algorithm.Conditional:
                return EvalConditionalShapeCounted(callee, arg.Normalize(), ctx, valEnv, calleeName);

            default:
            {
                var argEnvR = BindParams(callee.Params, [arg]);
                if (argEnvR.IsError) return argEnvR.Error;
                return EvalAlgOutputCounted(callee, ctx, Concat(argEnvR.Value, valEnv));
            }
        }
    }

    /// <summary>
    /// Evaluate an algorithm's output expressions and count how many top-level
    /// values they emitted at the current algorithm boundary.
    /// A grouped block expression counts as one value, while multiple top-level
    /// output expressions count separately.
    /// Lean: <c>evalAlgOutputCounted</c>.
    /// </summary>
    private static EvalResult<CountedResult> EvalAlgOutputCountedCore(
        Algorithm alg,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv,
        bool allowEmptyUserOutput)
    {
        var dupProp = alg.FindDuplicatePropName();
        if (dupProp is not null)
            return new EvalError.DuplicateProperty(dupProp);

        if (!allowEmptyUserOutput && alg is Algorithm.User { Output: { Count: 0 } })
            return new EvalError.MissingOutput();

        var innerCtx = ctx.Push(alg);
        var results = new List<Result>();
        var emittedCount = 0;

        foreach (var expr in alg.Output)
        {
            var countedR = EvalCounted(expr, innerCtx, valEnv);
            if (countedR.IsError) return countedR.Error;
            results.Add(countedR.Value.Value);
            emittedCount += countedR.Value.EmittedCount;
        }

        return EvalResult<CountedResult>.Ok(new CountedResult(Result.FromItems(results), emittedCount));
    }

    private static EvalResult<CountedResult> EvalAlgOutputCounted(
        Algorithm alg,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
        => EvalAlgOutputCountedCore(alg, ctx, valEnv, allowEmptyUserOutput: false);

    /// <summary>
    /// Evaluate a conditional algorithm against an already-assembled argument
    /// shape, preserving the selected branch's top-level emitted output count.
    /// Lean: <c>evalConditionalShapeCounted</c>.
    /// </summary>
    private static EvalResult<CountedResult> EvalConditionalShapeCounted(
        Algorithm callee,
        Result argShape,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv,
        string calleeName = "conditional")
    {
        if (callee.HasDuplicateBranchPatterns())
            return new EvalError.DuplicateBranchPattern();

        var match = MatchBranches(callee.Branches, argShape);
        if (match is null)
            return new EvalError.NoMatchingBranch(calleeName);

        var (branch, bindings) = match.Value;
        var wiredBody = ChildOf(callee, branch.Body);
        var newCtx = ctx.Push(callee);
        var newEnv = Concat(bindings, valEnv);
        return EvalAlgOutputCounted(wiredBody, newCtx, newEnv);
    }

    /// <summary>
    /// Evaluate a resolved algorithm on two whole result values.
    /// The collection element and current accumulator are each passed as a
    /// whole argument so grouped values stay grouped.
    /// Lean: <c>evalTwoWholeArgCallCounted</c>.
    /// </summary>
    private static EvalResult<CountedResult> EvalTwoWholeArgCallCounted(
        Algorithm callee,
        Result element,
        Result accumulator,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv,
        string calleeName = "conditional")
    {
        switch (callee)
        {
            case Algorithm.Builtin(var builtin):
                return ApplyBuiltinCounted(
                    builtin,
                    [AlgorithmOfExpr(ResultToExpr(element)), AlgorithmOfExpr(ResultToExpr(accumulator))],
                    ctx,
                    valEnv);

            case Algorithm.Conditional:
                return EvalConditionalShapeCounted(
                    callee,
                    Result.FromItems([element, accumulator]),
                    ctx,
                    valEnv,
                    calleeName);

            default:
            {
                var argEnvR = BindParams(callee.Params, [element, accumulator]);
                if (argEnvR.IsError) return argEnvR.Error;
                return EvalAlgOutputCounted(callee, ctx, Concat(argEnvR.Value, valEnv));
            }
        }
    }

    /// <summary>
    /// Evaluate <c>reduce(collection, step, initial)</c> while preserving the
    /// accumulator's emitted-value count for the empty-collection case.
    /// Lean: <c>evalReduceCounted</c>.
    /// </summary>
    private static EvalResult<CountedResult> EvalReduceCounted(
        Algorithm collectionAlg,
        Algorithm stepAlg,
        Algorithm initialAlg,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var collectionR = EvalMaybeMemoizedPropertyOutput(collectionAlg, ctx, valEnv);
        if (collectionR.IsError) return collectionR.Error;

        var initialR = EvalMaybeMemoizedPropertyOutputCounted(initialAlg, ctx, valEnv);
        if (initialR.IsError) return initialR.Error;

        var elements = new List<Result>();
        ResultItems(elements, collectionR.Value);

        var accumulator = initialR.Value;
        foreach (var item in elements)
        {
            var stepR = WithCtx(
                "while evaluating reduce step (reduce passes each collection item and accumulator as whole arguments)",
                EvalTwoWholeArgCallCounted(stepAlg, item, accumulator.Value, ctx, valEnv, "reduce step"));
            if (stepR.IsError) return stepR.Error;

            var nextR = ExpectSingleAccumulator(stepR.Value);
            if (nextR.IsError) return nextR.Error;

            accumulator = new CountedResult(nextR.Value, 1);
        }

        return EvalResult<CountedResult>.Ok(accumulator);
    }

    /// <summary>
    /// Evaluate <c>map(collection, transform)</c> while preserving the number of
    /// top-level mapped elements.
    /// Lean: <c>evalMapCounted</c>.
    /// </summary>
    private static EvalResult<CountedResult> EvalMapCounted(
        Algorithm collectionAlg,
        Algorithm transformAlg,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var collectionR = EvalMaybeMemoizedPropertyOutput(collectionAlg, ctx, valEnv);
        if (collectionR.IsError) return collectionR.Error;

        var elements = new List<Result>();
        ResultItems(elements, collectionR.Value);

        var mapped = new List<Result>(elements.Count);
        foreach (var item in elements)
        {
            var transformR = WithCtx(
                "while evaluating map transform (map passes each collection item as one argument to the transform)",
                EvalWholeArgCallCounted(transformAlg, item, ctx, valEnv, "map transform"));
            if (transformR.IsError) return transformR.Error;

            var mappedElementR = ExpectSingleMappedElement(transformR.Value);
            if (mappedElementR.IsError) return mappedElementR.Error;

            mapped.Add(mappedElementR.Value);
        }

        return EvalResult<CountedResult>.Ok(new CountedResult(Result.FromItems(mapped), mapped.Count));
    }

    /// <summary>
    /// Evaluate <c>count(collection)</c> by counting the top-level collection
    /// elements from left to right.
    /// Each atom, string, or grouped value counts as one top-level element;
    /// groups are not flattened or inspected recursively, and empty collections
    /// return <c>0</c>.
    /// Lean: <c>evalCountCounted</c>.
    /// </summary>
    private static EvalResult<CountedResult> EvalCountCounted(
        Algorithm collectionAlg,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var collectionR = EvalMaybeMemoizedPropertyOutput(collectionAlg, ctx, valEnv);
        if (collectionR.IsError) return collectionR.Error;

        var elements = new List<Result>();
        ResultItems(elements, collectionR.Value);

        return EvalResult<CountedResult>.Ok(new CountedResult(new Result.Atom(elements.Count), 1));
    }

    /// <summary>
    /// Evaluate <c>min(collection)</c> by comparing top-level collection
    /// elements from left to right and returning the smallest numeric element.
    /// The collection must be non-empty, and each top-level element must be
    /// exactly one atomic numeric value; groups are not flattened and strings
    /// are rejected.
    /// Lean: <c>evalMinCounted</c>.
    /// </summary>
    private static EvalResult<CountedResult> EvalMinCounted(
        Algorithm collectionAlg,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var collectionR = EvalMaybeMemoizedPropertyOutput(collectionAlg, ctx, valEnv);
        if (collectionR.IsError) return collectionR.Error;

        var elements = new List<Result>();
        ResultItems(elements, collectionR.Value);

        if (elements.Count == 0)
        {
            return new EvalError.WithContext(
                "min requires a non-empty collection",
                new EvalError.BadArity());
        }

        var firstNumeric = elements[0].SingleAtomicNumber();
        if (firstNumeric is null)
        {
            return new EvalError.WithContext(
                "min expects each collection element to be a single numeric value",
                new EvalError.BadArity());
        }

        var minimum = firstNumeric.Value;
        for (var i = 1; i < elements.Count; i++)
        {
            var numeric = elements[i].SingleAtomicNumber();
            if (numeric is null)
            {
                return new EvalError.WithContext(
                    "min expects each collection element to be a single numeric value",
                    new EvalError.BadArity());
            }

            if (numeric.Value < minimum)
                minimum = numeric.Value;
        }

        return EvalResult<CountedResult>.Ok(new CountedResult(new Result.Atom(minimum), 1));
    }

    /// <summary>
    /// Evaluate <c>max(collection)</c> by comparing top-level collection
    /// elements from left to right and returning the largest numeric element.
    /// The collection must be non-empty, and each top-level element must be
    /// exactly one atomic numeric value; groups are not flattened and strings
    /// are rejected.
    /// Lean: <c>evalMaxCounted</c>.
    /// </summary>
    private static EvalResult<CountedResult> EvalMaxCounted(
        Algorithm collectionAlg,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var collectionR = EvalMaybeMemoizedPropertyOutput(collectionAlg, ctx, valEnv);
        if (collectionR.IsError) return collectionR.Error;

        var elements = new List<Result>();
        ResultItems(elements, collectionR.Value);

        if (elements.Count == 0)
        {
            return new EvalError.WithContext(
                "max requires a non-empty collection",
                new EvalError.BadArity());
        }

        var firstNumeric = elements[0].SingleAtomicNumber();
        if (firstNumeric is null)
        {
            return new EvalError.WithContext(
                "max expects each collection element to be a single numeric value",
                new EvalError.BadArity());
        }

        var maximum = firstNumeric.Value;
        for (var i = 1; i < elements.Count; i++)
        {
            var numeric = elements[i].SingleAtomicNumber();
            if (numeric is null)
            {
                return new EvalError.WithContext(
                    "max expects each collection element to be a single numeric value",
                    new EvalError.BadArity());
            }

            if (numeric.Value > maximum)
                maximum = numeric.Value;
        }

        return EvalResult<CountedResult>.Ok(new CountedResult(new Result.Atom(maximum), 1));
    }

    /// <summary>
    /// Evaluate <c>sum(collection)</c> by adding the top-level collection
    /// elements from left to right.
    /// Each element must be exactly one atomic numeric value; groups are not
    /// flattened, strings are rejected, and empty collections return <c>0</c>.
    /// Lean: <c>evalSumCounted</c>.
    /// </summary>
    private static EvalResult<CountedResult> EvalSumCounted(
        Algorithm collectionAlg,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var collectionR = EvalMaybeMemoizedPropertyOutput(collectionAlg, ctx, valEnv);
        if (collectionR.IsError) return collectionR.Error;

        var elements = new List<Result>();
        ResultItems(elements, collectionR.Value);

        decimal total = 0;
        try
        {
            foreach (var item in elements)
            {
                var numeric = item.SingleAtomicNumber();
                if (numeric is null)
                {
                    return new EvalError.WithContext(
                        "sum expects each collection element to be a single numeric value",
                        new EvalError.BadArity());
                }

                total = checked(total + numeric.Value);
            }
        }
        catch (OverflowException)
        {
            return new EvalError.NumericOverflow();
        }

        return EvalResult<CountedResult>.Ok(new CountedResult(new Result.Atom(total), 1));
    }

    /// <summary>
    /// Evaluate <c>avg(collection)</c> by averaging the top-level collection
    /// elements from left to right.
    /// The collection must be non-empty, and each top-level element must be
    /// exactly one atomic numeric value; groups are not flattened and strings
    /// are rejected.
    /// Lean: <c>evalAvgCounted</c>.
    /// </summary>
    private static EvalResult<CountedResult> EvalAvgCounted(
        Algorithm collectionAlg,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var collectionR = EvalMaybeMemoizedPropertyOutput(collectionAlg, ctx, valEnv);
        if (collectionR.IsError) return collectionR.Error;

        var elements = new List<Result>();
        ResultItems(elements, collectionR.Value);

        if (elements.Count == 0)
        {
            return new EvalError.WithContext(
                "avg requires a non-empty collection",
                new EvalError.BadArity());
        }

        decimal total = 0;
        try
        {
            foreach (var item in elements)
            {
                var numeric = item.SingleAtomicNumber();
                if (numeric is null)
                {
                    return new EvalError.WithContext(
                        "avg expects each collection element to be a single numeric value",
                        new EvalError.BadArity());
                }

                total = checked(total + numeric.Value);
            }

            var average = total / elements.Count;
            return EvalResult<CountedResult>.Ok(new CountedResult(new Result.Atom(average), 1));
        }
        catch (OverflowException)
        {
            return new EvalError.NumericOverflow();
        }
    }

    /// <summary>
    /// Builtin application with counted output shape.
    /// Used by <c>reduce</c> so step validation can distinguish grouped
    /// accumulator values from multiple top-level outputs.
    /// Lean: <c>applyBuiltinCounted</c>.
    /// </summary>
    private static EvalResult<CountedResult> ApplyBuiltinCounted(
        BuiltinId builtin,
        IReadOnlyList<Algorithm> args,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        switch (builtin, args.Count)
        {
            case (BuiltinId.@if, 3):
            {
                var condR = EvalMaybeMemoizedPropertyOutput(args[0], ctx, valEnv);
                if (condR.IsError) return condR.Error;
                var truth = condR.Value.TruthValue();
                if (truth is null) return new EvalError.BadArity();
                return truth.Value
                    ? EvalMaybeMemoizedPropertyOutputCounted(args[1], ctx, valEnv)
                    : EvalMaybeMemoizedPropertyOutputCounted(args[2], ctx, valEnv);
            }

            case (BuiltinId.@while, 2):
            {
                var initR = EvalMaybeMemoizedPropertyOutput(args[1], ctx, valEnv);
                if (initR.IsError) return initR.Error;
                var loopR = WhileLoop(args[0], initR.Value, ctx, valEnv);
                if (loopR.IsError) return loopR.Error;
                return EvalResult<CountedResult>.Ok(new CountedResult(loopR.Value, loopR.Value.ValueCount()));
            }

            case (BuiltinId.@repeat, 3):
            {
                var countR = EvalMaybeMemoizedPropertyOutput(args[1], ctx, valEnv);
                if (countR.IsError) return countR.Error;
                var nR = ExpectWholeInt(countR.Value, "Repeat count");
                if (nR.IsError) return nR.Error;
                var n = (long)nR.Value;
                if (n < 0) return new EvalError.IllegalInEval("Repeat count must be >= 0");

                var initR = EvalMaybeMemoizedPropertyOutput(args[2], ctx, valEnv);
                if (initR.IsError) return initR.Error;
                var loopR = RepeatLoop(args[0], n, initR.Value, ctx, valEnv);
                if (loopR.IsError) return loopR.Error;
                return EvalResult<CountedResult>.Ok(new CountedResult(loopR.Value, loopR.Value.ValueCount()));
            }

            case (BuiltinId.@atoms, 1):
            {
                var atomsR = EvalMaybeMemoizedPropertyOutput(args[0], ctx, valEnv);
                if (atomsR.IsError) return atomsR.Error;
                var atoms = atomsR.Value.ToAtoms();
                var value = Result.FromItems(atoms.Select(n => new Result.Atom(n)));
                return EvalResult<CountedResult>.Ok(new CountedResult(value, atoms.Count));
            }

            case (BuiltinId.@range, 2):
            {
                var startR = EvalMaybeMemoizedPropertyOutput(args[0], ctx, valEnv);
                if (startR.IsError) return startR.Error;
                var startIntR = ExpectWholeInt(startR.Value, "range start");
                if (startIntR.IsError) return startIntR.Error;

                var stopR = EvalMaybeMemoizedPropertyOutput(args[1], ctx, valEnv);
                if (stopR.IsError) return stopR.Error;
                var stopIntR = ExpectWholeInt(stopR.Value, "range stop");
                if (stopIntR.IsError) return stopIntR.Error;

                var value = BuildInclusiveRange(startIntR.Value, stopIntR.Value);
                return EvalResult<CountedResult>.Ok(new CountedResult(value, value.ToAtoms().Count));
            }

            case (BuiltinId.@filter, 2):
            {
                var collectionR = EvalMaybeMemoizedPropertyOutput(args[0], ctx, valEnv);
                if (collectionR.IsError) return collectionR.Error;

                var elements = new List<Result>();
                ResultItems(elements, collectionR.Value);

                var kept = new List<Result>();
                foreach (var item in elements)
                {
                    var predicateR = WithCtx(
                        "while evaluating filter predicate (filter passes each collection item as one argument to the predicate)",
                        EvalWholeArgCall(args[1], item, ctx, valEnv, "filter predicate"));
                    if (predicateR.IsError) return predicateR.Error;

                    var truth = predicateR.Value.SingleAtomicTruthValue();
                    if (truth is null)
                    {
                        return new EvalError.WithContext(
                            "filter predicate must return exactly one atomic numeric value",
                            new EvalError.BadArity());
                    }

                    if (truth.Value)
                        kept.Add(item);
                }

                return EvalResult<CountedResult>.Ok(new CountedResult(Result.FromItems(kept), kept.Count));
            }

            case (BuiltinId.@map, 2):
                return EvalMapCounted(args[0], args[1], ctx, valEnv);

            case (BuiltinId.@count, 1):
                return EvalCountCounted(args[0], ctx, valEnv);

            case (BuiltinId.@min, 1):
                return EvalMinCounted(args[0], ctx, valEnv);

            case (BuiltinId.@max, 1):
                return EvalMaxCounted(args[0], ctx, valEnv);

            case (BuiltinId.@sum, 1):
                return EvalSumCounted(args[0], ctx, valEnv);

            case (BuiltinId.@avg, 1):
                return EvalAvgCounted(args[0], ctx, valEnv);

            case (BuiltinId.@reduce, 3):
                return EvalReduceCounted(args[0], args[1], args[2], ctx, valEnv);

            default:
                return WrongBuiltinArity(builtin, args.Count);
        }
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
            new("range",  new Algorithm.Builtin(BuiltinId.@range),  IsPublic: true),
            new("filter", new Algorithm.Builtin(BuiltinId.@filter), IsPublic: true),
            new("map",    new Algorithm.Builtin(BuiltinId.@map),    IsPublic: true),
            new("count",  new Algorithm.Builtin(BuiltinId.@count),  IsPublic: true),
            new("min",    new Algorithm.Builtin(BuiltinId.@min),    IsPublic: true),
            new("max",    new Algorithm.Builtin(BuiltinId.@max),    IsPublic: true),
            new("sum",    new Algorithm.Builtin(BuiltinId.@sum),    IsPublic: true),
            new("avg",    new Algorithm.Builtin(BuiltinId.@avg),    IsPublic: true),
            new("reduce", new Algorithm.Builtin(BuiltinId.@reduce), IsPublic: true),
            new("Math",   MathAlgorithm,                           IsPublic: true),
        ],
        Output: []);

    /// <summary>Lean: builtinAcceptsArity. ifBuiltin accepts exactly 3 args.</summary>
    private static bool BuiltinAcceptsArity(BuiltinId b, int n) => (b, n) switch
    {
        (BuiltinId.@if, 3) => true,
        (BuiltinId.@while, 2) => true,
        (BuiltinId.@repeat, 3) => true,
        (BuiltinId.@atoms, 1) => true,
        (BuiltinId.@range, 2) => true,
        (BuiltinId.@filter, 2) => true,
        (BuiltinId.@map, 2) => true,
        (BuiltinId.@count, 1) => true,
        (BuiltinId.@min, 1) => true,
        (BuiltinId.@max, 1) => true,
        (BuiltinId.@sum, 1) => true,
        (BuiltinId.@avg, 1) => true,
        (BuiltinId.@reduce, 3) => true,
        _ => false,
    };

    /// <summary>Lean: builtinArityDesc. Human-readable expected arity for error messages.</summary>
    private static string BuiltinArityDesc(BuiltinId b) => b switch
    {
        BuiltinId.@if => "3",
        BuiltinId.@while => "2",
        BuiltinId.@repeat => "3",
        BuiltinId.@atoms => "1",
        BuiltinId.@range => "2",
        BuiltinId.@filter => "2",
        BuiltinId.@map => "2",
        BuiltinId.@count => "1",
        BuiltinId.@min => "1",
        BuiltinId.@max => "1",
        BuiltinId.@sum => "1",
        BuiltinId.@avg => "1",
        BuiltinId.@reduce => "3",
        _ => "?",
    };

    private static EvalError WrongBuiltinArity(BuiltinId builtin, int actualCount)
        => builtin switch
        {
            BuiltinId.@if => new EvalError.WithContext(
                $"Builtin 'if' expects 3 arguments: condition, whenTrue, whenFalse. Got {actualCount}.",
                new EvalError.ArityMismatch(3, actualCount)),
            _ => new EvalError.WithContext(
                $"expected {BuiltinArityDesc(builtin)} arguments",
                new EvalError.ArityMismatch(0, actualCount)),
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
                    if (r.IsOk)
                    {
                        var binding = CreateLexicalPropertyBinding(r.Value.Reference, ctx.RunState);
                        ctx.RunState.RegisterResolvedLexicalPropertyBinding(
                            r.Value.ResolvedAlgorithm,
                            binding);
                    }
                    if (r.IsError && r.Error.Span is null)
                        return r.Error with { Span = expr.Span };
                    return r.IsError
                        ? r.Error
                        : EvalResult<Algorithm>.Ok(r.Value.ResolvedAlgorithm);
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
    /// User-defined algorithms may exist structurally without output, but forcing
    /// them in value position raises <see cref="EvalError.MissingOutput"/>.
    /// Lean: evalAlgOutput → EvalM Result.
    /// </summary>
    private static EvalResult<Result> EvalAlgOutputCore(
        Algorithm alg,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv,
        bool allowEmptyUserOutput)
    {
        var dupProp = alg.FindDuplicatePropName();
        if (dupProp is not null)
            return new EvalError.DuplicateProperty(dupProp);

        if (!allowEmptyUserOutput && alg is Algorithm.User { Output: { Count: 0 } })
            return new EvalError.MissingOutput();

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

    private static EvalResult<Result> EvalAlgOutput(
        Algorithm alg,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
        => EvalAlgOutputCore(alg, ctx, valEnv, allowEmptyUserOutput: false);

    private static EvalResult<Result> EvalProgramOutput(
        Algorithm alg,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
        => EvalAlgOutputCore(alg, ctx, valEnv, allowEmptyUserOutput: true);

    private static bool IsMemoizablePropertyResult(Algorithm alg)
        => alg is not Algorithm.Builtin && alg.Params.Count == 0;

    private static PropertyMemoLookup TryGetMemoizedPropertyResult(
        EvalCtx ctx,
        PropertyMemoKey key,
        out MemoizedPropertyResult result)
        => ctx.RunState.TryGetMemoizedPropertyResult(key, out result);

    private static void StoreMemoizedPropertyResult(
        EvalCtx ctx,
        PropertyMemoKey key,
        MemoizedPropertyResult result)
        => ctx.RunState.StoreMemoizedPropertyResult(key, result);

    private static ScopeCtx CreateLexicalScope(Algorithm alg, ScopeCtx? parentScope)
        => new(parentScope, alg.Opens, alg.Properties);

    private static bool HasOpenSensitiveLexicalScope(Algorithm alg, ScopeCtx? parentScope)
    {
        if (alg.Opens.Count > 0)
            return true;

        for (var scope = parentScope; scope is not null; scope = scope.Parent)
        {
            if (scope.Opens.Count > 0)
                return true;
        }

        return false;
    }

    private static bool TryLookupLexicalBindingWithoutOpens(
        Algorithm alg,
        ScopeCtx? parentScope,
        string name,
        out LexicalPropertyReference reference)
    {
        var local = LookupPropBinding(alg, name);
        if (local is not null)
        {
            reference = new LexicalPropertyReference(local, CreateLexicalScope(alg, parentScope));
            return true;
        }

        if (parentScope is not null)
        {
            var structural = LookupInParentsDirectBinding(parentScope, name);
            if (structural is not null)
            {
                reference = structural.Value;
                return true;
            }
        }

        reference = default;
        return false;
    }

    private static LexicalPropertyBinding CreateLexicalPropertyBinding(
        LexicalPropertyReference reference,
        EvaluatorRunState runState)
        => new(
            reference.Binding.Name,
            reference.Binding,
            IsClosedLexicalPropertyForMemoization(reference, runState));

    private static bool IsClosedLexicalPropertyForMemoization(
        LexicalPropertyReference reference,
        EvaluatorRunState runState)
    {
        if (reference.Binding.Value is Algorithm.Builtin)
            return false;

        if (reference.Binding.Value.Params.Count != 0)
            return false;

        return IsContextIndependentLexicalBinding(
            reference,
            runState,
            new HashSet<object>(ReferenceEqualityComparer.Instance));
    }

    private static bool IsContextIndependentLexicalBinding(
        LexicalPropertyReference reference,
        EvaluatorRunState runState,
        HashSet<object> activeBindings)
    {
        if (runState.TryGetContextIndependentLexicalBinding(reference, out var cached))
            return cached;

        if (!activeBindings.Add(reference.Binding))
            return false;

        var isContextIndependent = IsContextIndependentAlgorithm(
            reference.Binding.Value,
            reference.DefinitionScope,
            runState,
            activeBindings);

        activeBindings.Remove(reference.Binding);
        runState.StoreContextIndependentLexicalBinding(reference, isContextIndependent);
        return isContextIndependent;
    }

    private static bool IsContextIndependentAlgorithm(
        Algorithm alg,
        ScopeCtx? parentScope,
        EvaluatorRunState runState,
        HashSet<object> activeBindings)
    {
        if (alg is Algorithm.Builtin)
            return true;

        if (alg is Algorithm.Conditional)
            return false;

        if (HasOpenSensitiveLexicalScope(alg, parentScope))
            return false;

        foreach (var expr in alg.Output)
        {
            if (!IsContextIndependentExpression(expr, alg, parentScope, runState, activeBindings))
                return false;
        }

        return true;
    }

    private static bool IsContextIndependentExpression(
        Expr expr,
        Algorithm currentAlg,
        ScopeCtx? parentScope,
        EvaluatorRunState runState,
        HashSet<object> activeBindings)
    {
        switch (expr)
        {
            case Expr.Num:
            case Expr.StringLiteral:
                return true;

            case Expr.Param(var name):
                return currentAlg.Params.Contains(name);

            case Expr.Grace(var inner, _):
                return IsContextIndependentExpression(inner, currentAlg, parentScope, runState, activeBindings);

            case Expr.Unary(_, var operand):
                return IsContextIndependentExpression(operand, currentAlg, parentScope, runState, activeBindings);

            case Expr.Binary(_, var left, var right):
                return IsContextIndependentExpression(left, currentAlg, parentScope, runState, activeBindings)
                    && IsContextIndependentExpression(right, currentAlg, parentScope, runState, activeBindings);

            case Expr.Combine(var left, var right):
                return IsContextIndependentExpression(left, currentAlg, parentScope, runState, activeBindings)
                    && IsContextIndependentExpression(right, currentAlg, parentScope, runState, activeBindings);

            case Expr.Index(var target, var selector):
                return IsContextIndependentExpression(target, currentAlg, parentScope, runState, activeBindings)
                    && IsContextIndependentExpression(selector, currentAlg, parentScope, runState, activeBindings);

            case Expr.Resolve(var name):
            {
                if (!TryLookupLexicalBindingWithoutOpens(currentAlg, parentScope, name, out var reference))
                    return false;

                return reference.Binding.Value is Algorithm.Builtin
                    || IsContextIndependentLexicalBinding(reference, runState, activeBindings);
            }

            case Expr.Block(var alg):
                return IsContextIndependentAlgorithm(
                    alg,
                    CreateLexicalScope(currentAlg, parentScope),
                    runState,
                    activeBindings);

            case Expr.Call(var func, var args):
                return IsContextIndependentExpression(func, currentAlg, parentScope, runState, activeBindings)
                    && IsContextIndependentAlgorithm(
                        args,
                        CreateLexicalScope(currentAlg, parentScope),
                        runState,
                        activeBindings);

            case Expr.DotCall(var target, _, var argsOpt):
                return IsContextIndependentExpression(target, currentAlg, parentScope, runState, activeBindings)
                    && (argsOpt is null
                        || IsContextIndependentAlgorithm(
                            argsOpt,
                            CreateLexicalScope(currentAlg, parentScope),
                            runState,
                            activeBindings));

            case Expr.NativeCall(_, var argNames):
                return argNames.All(currentAlg.Params.Contains);

            default:
                return false;
        }
    }

    private static bool TryCreateLexicalPropertyMemoKey(
        Algorithm alg,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv,
        out PropertyMemoKey key)
    {
        key = default;

        if (!IsMemoizablePropertyResult(alg))
            return false;

        if (!ctx.RunState.TryGetResolvedLexicalPropertyBinding(alg, out var binding))
            return false;

        if (binding.IsClosedForMemoization && ctx.AlgEnv.Count == 0 && valEnv.Count == 0)
        {
            key = new(
                PropertyMemoKind.LexicalClosedResolve,
                binding.Name,
                ClosedLexicalPropertyMemoContextToken,
                ClosedLexicalPropertyMemoContextToken,
                ClosedLexicalPropertyMemoContextToken,
                binding.BindingToken);
            return true;
        }

        key = new(
            PropertyMemoKind.LexicalContextualResolve,
            binding.Name,
            ctx.CallStack,
            ctx.AlgEnv,
            valEnv,
            BindingToken: null);
        return true;
    }

    private static bool TryCreateStructuralPropertyMemoKey(
        Algorithm propertyBinding,
        string name,
        Algorithm wiredProperty,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv,
        out PropertyMemoKey key)
    {
        key = default;

        if (!IsMemoizablePropertyResult(wiredProperty))
            return false;

        key = new(
            PropertyMemoKind.StructuralDot,
            name,
            ctx.CallStack,
            ctx.AlgEnv,
            valEnv,
            propertyBinding);
        return true;
    }

    private static EvalResult<MemoizedPropertyResult> EvalAlgOutputAsMemoizedPropertyResult(
        Algorithm alg,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var countedR = EvalAlgOutputCounted(alg, ctx, valEnv);
        if (countedR.IsError) return countedR.Error;
        return EvalResult<MemoizedPropertyResult>.Ok(
            new MemoizedPropertyResult(countedR.Value.Value, countedR.Value.EmittedCount));
    }

    private static EvalResult<MemoizedPropertyResult> EvalMemoizedPropertyResult(
        PropertyMemoKey key,
        Algorithm alg,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var lookup = TryGetMemoizedPropertyResult(ctx, key, out var memoizedResult);
        if (lookup == PropertyMemoLookup.Hit)
            return EvalResult<MemoizedPropertyResult>.Ok(memoizedResult);

        if (lookup == PropertyMemoLookup.InProgress)
            return EvalAlgOutputAsMemoizedPropertyResult(alg, ctx, valEnv);

        var evaluatedResult = EvalAlgOutputAsMemoizedPropertyResult(alg, ctx, valEnv);
        if (evaluatedResult.IsOk)
            StoreMemoizedPropertyResult(ctx, key, evaluatedResult.Value);
        else
            ctx.RunState.ClearMemoizedPropertyResult(key);

        return evaluatedResult;
    }

    private static EvalResult<Result> EvalMaybeMemoizedPropertyOutput(
        Algorithm alg,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        if (!TryCreateLexicalPropertyMemoKey(alg, ctx, valEnv, out var key))
            return EvalAlgOutput(alg, ctx, valEnv);

        var memoizedResult = EvalMemoizedPropertyResult(key, alg, ctx, valEnv);
        return memoizedResult.IsError
            ? memoizedResult.Error
            : EvalResult<Result>.Ok(memoizedResult.Value.Value);
    }

    private static EvalResult<CountedResult> EvalMaybeMemoizedPropertyOutputCounted(
        Algorithm alg,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        if (!TryCreateLexicalPropertyMemoKey(alg, ctx, valEnv, out var key))
            return EvalAlgOutputCounted(alg, ctx, valEnv);

        var memoizedResult = EvalMemoizedPropertyResult(key, alg, ctx, valEnv);
        return memoizedResult.IsError
            ? memoizedResult.Error
            : EvalResult<CountedResult>.Ok(
                new CountedResult(memoizedResult.Value.Value, memoizedResult.Value.EmittedCount));
    }

    private static EvalResult<Result> EvalMaybeMemoizedStructuralPropertyOutput(
        Algorithm propertyBinding,
        string name,
        Algorithm wiredProperty,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        if (!TryCreateStructuralPropertyMemoKey(propertyBinding, name, wiredProperty, ctx, valEnv, out var key))
            return EvalAlgOutput(wiredProperty, ctx, valEnv);

        var memoizedResult = EvalMemoizedPropertyResult(key, wiredProperty, ctx, valEnv);
        return memoizedResult.IsError
            ? memoizedResult.Error
            : EvalResult<Result>.Ok(memoizedResult.Value.Value);
    }

    private static EvalResult<CountedResult> EvalMaybeMemoizedStructuralPropertyOutputCounted(
        Algorithm propertyBinding,
        string name,
        Algorithm wiredProperty,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        if (!TryCreateStructuralPropertyMemoKey(propertyBinding, name, wiredProperty, ctx, valEnv, out var key))
            return EvalAlgOutputCounted(wiredProperty, ctx, valEnv);

        var memoizedResult = EvalMemoizedPropertyResult(key, wiredProperty, ctx, valEnv);
        return memoizedResult.IsError
            ? memoizedResult.Error
            : EvalResult<CountedResult>.Ok(
                new CountedResult(memoizedResult.Value.Value, memoizedResult.Value.EmittedCount));
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
                var condR = EvalMaybeMemoizedPropertyOutput(args[0], ctx, valEnv);
                if (condR.IsError) return condR.Error;
                var truth = condR.Value.TruthValue();
                if (truth is null) return new EvalError.BadArity();
                return truth.Value
                    ? EvalMaybeMemoizedPropertyOutput(args[1], ctx, valEnv)
                    : EvalMaybeMemoizedPropertyOutput(args[2], ctx, valEnv);
            }

            // while(step, init)
            case (BuiltinId.@while, 2):
            {
                var initR = EvalMaybeMemoizedPropertyOutput(args[1], ctx, valEnv);
                if (initR.IsError) return initR.Error;
                return WhileLoop(args[0], initR.Value, ctx, valEnv);
            }

            // repeat(step, count, init)
            case (BuiltinId.@repeat, 3):
            {
                var countR = EvalMaybeMemoizedPropertyOutput(args[1], ctx, valEnv);
                if (countR.IsError) return countR.Error;
                var nR = ExpectWholeInt(countR.Value, "Repeat count");
                if (nR.IsError) return nR.Error;
                var n = (long)nR.Value;
                if (n < 0) return new EvalError.IllegalInEval("Repeat count must be >= 0");
                var repeatInitR = EvalMaybeMemoizedPropertyOutput(args[2], ctx, valEnv);
                if (repeatInitR.IsError) return repeatInitR.Error;
                return RepeatLoop(args[0], n, repeatInitR.Value, ctx, valEnv);
            }

            // atoms(alg) — flatten to atoms
            case (BuiltinId.@atoms, 1):
            {
                var atomsR = EvalMaybeMemoizedPropertyOutput(args[0], ctx, valEnv);
                if (atomsR.IsError) return atomsR.Error;
                var atoms = atomsR.Value.ToAtoms();
                return EvalResult<Result>.Ok(
                    Result.FromItems(atoms.Select(n => new Result.Atom(n))));
            }

            // range(start, stop) — inclusive integer sequence, ascending or descending.
            case (BuiltinId.@range, 2):
            {
                var startR = EvalMaybeMemoizedPropertyOutput(args[0], ctx, valEnv);
                if (startR.IsError) return startR.Error;
                var startIntR = ExpectWholeInt(startR.Value, "range start");
                if (startIntR.IsError) return startIntR.Error;

                var stopR = EvalMaybeMemoizedPropertyOutput(args[1], ctx, valEnv);
                if (stopR.IsError) return stopR.Error;
                var stopIntR = ExpectWholeInt(stopR.Value, "range stop");
                if (stopIntR.IsError) return stopIntR.Error;

                return EvalResult<Result>.Ok(BuildInclusiveRange(startIntR.Value, stopIntR.Value));
            }

            // filter(collection, predicate) — left-to-right selection over top-level
            // collection elements. The predicate must return exactly one atomic
            // numeric value: 0 rejects the item and any nonzero atom keeps it.
            // Grouped, multi-output, empty, or string predicate results are invalid.
            // Kept elements are preserved unchanged and in order; grouped elements
            // remain grouped and rejected elements are omitted.
            case (BuiltinId.@filter, 2):
            {
                var collectionR = EvalMaybeMemoizedPropertyOutput(args[0], ctx, valEnv);
                if (collectionR.IsError) return collectionR.Error;

                var elements = new List<Result>();
                ResultItems(elements, collectionR.Value);

                var kept = new List<Result>();
                foreach (var item in elements)
                {
                    var predicateR = WithCtx(
                        "while evaluating filter predicate (filter passes each collection item as one argument to the predicate)",
                        EvalWholeArgCall(args[1], item, ctx, valEnv, "filter predicate"));
                    if (predicateR.IsError) return predicateR.Error;

                    var truth = predicateR.Value.SingleAtomicTruthValue();
                    if (truth is null)
                    {
                        return new EvalError.WithContext(
                            "filter predicate must return exactly one atomic numeric value",
                            new EvalError.BadArity());
                    }

                    if (truth.Value)
                        kept.Add(item);
                }

                return EvalResult<Result>.Ok(Result.FromItems(kept));
            }

            // map(collection, transform) — left-to-right transformation over
            // top-level collection elements. transform(element) receives each
            // element as one whole value and must return exactly one mapped
            // element. Grouped input/output elements stay whole.
            case (BuiltinId.@map, 2):
            {
                var mapR = EvalMapCounted(args[0], args[1], ctx, valEnv);
                if (mapR.IsError) return mapR.Error;
                return EvalResult<Result>.Ok(mapR.Value.Value);
            }

            // count(collection) — count top-level collection elements from
            // left to right. Atoms, strings, and grouped values each count as
            // one element; groups are not flattened, and empty collections
            // return 0.
            case (BuiltinId.@count, 1):
            {
                var countR = EvalCountCounted(args[0], ctx, valEnv);
                if (countR.IsError) return countR.Error;
                return EvalResult<Result>.Ok(countR.Value.Value);
            }

            // min(collection) — compare top-level collection elements from
            // left to right. The collection must be non-empty and each element
            // must be one atomic numeric value; groups are not flattened and
            // strings are invalid.
            case (BuiltinId.@min, 1):
            {
                var minR = EvalMinCounted(args[0], ctx, valEnv);
                if (minR.IsError) return minR.Error;
                return EvalResult<Result>.Ok(minR.Value.Value);
            }

            // max(collection) — compare top-level collection elements from
            // left to right. The collection must be non-empty and each element
            // must be one atomic numeric value; groups are not flattened and
            // strings are invalid.
            case (BuiltinId.@max, 1):
            {
                var maxR = EvalMaxCounted(args[0], ctx, valEnv);
                if (maxR.IsError) return maxR.Error;
                return EvalResult<Result>.Ok(maxR.Value.Value);
            }

            // sum(collection) — left-to-right numeric aggregation over top-level
            // collection elements. Each element must be one atomic numeric value;
            // groups are not flattened, strings are invalid, and empty collections
            // return 0.
            case (BuiltinId.@sum, 1):
            {
                var sumR = EvalSumCounted(args[0], ctx, valEnv);
                if (sumR.IsError) return sumR.Error;
                return EvalResult<Result>.Ok(sumR.Value.Value);
            }

            // avg(collection) — left-to-right numeric averaging over top-level
            // collection elements. The collection must be non-empty and each
            // element must be one atomic numeric value; groups are not flattened
            // and strings are invalid.
            case (BuiltinId.@avg, 1):
            {
                var avgR = EvalAvgCounted(args[0], ctx, valEnv);
                if (avgR.IsError) return avgR.Error;
                return EvalResult<Result>.Ok(avgR.Value.Value);
            }

            // reduce(collection, step, initial) — left fold over the collection's
            // top-level elements. step(element, accumulator) receives each whole
            // element and current accumulator and must return exactly one next
            // accumulator value. Grouped input elements stay grouped, grouped
            // accumulator values are allowed, and empty collections return the
            // initial accumulator unchanged.
            case (BuiltinId.@reduce, 3):
            {
                var reduceR = EvalReduceCounted(args[0], args[1], args[2], ctx, valEnv);
                if (reduceR.IsError) return reduceR.Error;
                return EvalResult<Result>.Ok(reduceR.Value.Value);
            }

            default:
            {
                return WrongBuiltinArity(builtin, args.Count);
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
                        return WithSpan(expr.Span, EvalAlgOutput(algBound, ctx, valEnv));
                    return new EvalError.ArityMismatch(algBound.Params.Count, 0) { Span = expr.Span };
                }
                return new EvalError.UnknownName(name) { Span = expr.Span };
            }

            case Expr.Unary(var unaryOp, var operand):
            {
                // Empty result propagation through unary operators.
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
                // Evaluate both sides as Result first so empty results can propagate.
                var lR = Eval(left, ctx, valEnv);
                if (lR.IsError) return lR.Error;
                var rR = Eval(right, ctx, valEnv);
                if (rR.IsError) return rR.Error;
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

                if (op == BinaryOp.Pow)
                    return EvalPow(expr.Span, x, y);

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
                    return WithSpan(expr.Span ?? FirstSpan(wired.Output), EvalAlgOutput(wired, ctx, valEnv));
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

                if (resolvedR.Value.Params.Count != 0)
                {
                    return WithSpan<Result>(
                        expr.Span,
                        new EvalError.WithContext(
                            CtxProperty(name),
                            new EvalError.ArityMismatch(resolvedR.Value.Params.Count, 0)));
                }

                return WithPropertyContextOnMissingOutput(name, expr.Span,
                    EvalMaybeMemoizedPropertyOutput(resolvedR.Value, ctx, valEnv));
            }

            case Expr.DotCall(var dotTarget, var dotName, var dotArgs):
                // Lean: eval (.dotCall o n argsOpt) => withCtx (CtxMsg.dotCall o n) do evalDotCall
                return WithSpan(expr.Span, WithCtx(CtxDotCall(dotTarget, dotName),
                    EvalDotCall(dotTarget, dotName, dotArgs, ctx, valEnv)));

            case Expr.Call(var func, var argsAlg):
                return WithSpan(expr.Span,
                    EvalCallExpr(func, argsAlg, ctx, valEnv));

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

    /// <summary>
    /// Evaluate an expression together with the number of top-level values it
    /// emits at the current algorithm boundary.
    /// Calls and name resolution propagate the callee's emitted output count.
    /// Block expressions count as one grouped value when non-empty. Combine adds
    /// both sides because it concatenates top-level outputs. All other value
    /// expressions emit either zero values (empty result) or one value.
    /// Lean: <c>evalCounted</c>.
    /// </summary>
    private static EvalResult<CountedResult> EvalCounted(
        Expr expr,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        switch (expr)
        {
            case Expr.Param(var name):
            {
                var val = LookupVal(valEnv, name);
                if (val is not null)
                    return EvalResult<CountedResult>.Ok(new CountedResult(val, val.ValueCount()));

                var algBound = LookupAlg(ctx.AlgEnv, name);
                if (algBound is not null)
                {
                    if (algBound.Params.Count == 0)
                        return WithSpan(expr.Span, EvalAlgOutputCounted(algBound, ctx, valEnv));
                    return new EvalError.ArityMismatch(algBound.Params.Count, 0) { Span = expr.Span };
                }

                return new EvalError.UnknownName(name) { Span = expr.Span };
            }

            case Expr.Combine(var left, var right):
            {
                var leftR = EvalCounted(left, ctx, valEnv);
                if (leftR.IsError) return leftR.Error;
                var rightR = EvalCounted(right, ctx, valEnv);
                if (rightR.IsError) return rightR.Error;

                var items = new List<Result>();
                ResultItems(items, leftR.Value.Value);
                ResultItems(items, rightR.Value.Value);
                return EvalResult<CountedResult>.Ok(new CountedResult(
                    Result.FromItems(items),
                    leftR.Value.EmittedCount + rightR.Value.EmittedCount));
            }

            case Expr.Block(var alg):
            {
                var wired = WireToCaller(ctx, alg);
                if (wired.Params.Count == 0)
                {
                    var blockR = WithSpan(expr.Span ?? FirstSpan(wired.Output), EvalAlgOutput(wired, ctx, valEnv));
                    if (blockR.IsError) return blockR.Error;
                    return EvalResult<CountedResult>.Ok(new CountedResult(blockR.Value, blockR.Value.ValueCount()));
                }

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

                if (resolvedR.Value.Params.Count != 0)
                {
                    return WithSpan<CountedResult>(
                        expr.Span,
                        new EvalError.WithContext(
                            CtxProperty(name),
                            new EvalError.ArityMismatch(resolvedR.Value.Params.Count, 0)));
                }

                return WithPropertyContextOnMissingOutput(name, expr.Span,
                    EvalMaybeMemoizedPropertyOutputCounted(resolvedR.Value, ctx, valEnv));
            }

            case Expr.DotCall(var dotTarget, var dotName, var dotArgs):
                return WithSpan(expr.Span, WithCtx(CtxDotCall(dotTarget, dotName),
                    EvalDotCallCounted(dotTarget, dotName, dotArgs, ctx, valEnv)));

            case Expr.Call(var func, var argsAlg):
                return WithSpan(expr.Span,
                    EvalCallCountedExpr(func, argsAlg, ctx, valEnv));

            default:
            {
                var resultR = Eval(expr, ctx, valEnv);
                if (resultR.IsError) return resultR.Error;
                return EvalResult<CountedResult>.Ok(new CountedResult(resultR.Value, resultR.Value.ValueCount()));
            }
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
                case "Sqrt": result = NormalizeDoubleResult(Math.Sqrt((double)args[0])); break;
                case "Ln": result = NormalizeDoubleResult(Math.Log((double)args[0])); break;
                case "Lg": result = NormalizeDoubleResult(Math.Log10((double)args[0])); break;
                case "Sin": result = NormalizeDoubleResult(Math.Sin((double)args[0])); break;
                case "Asin": result = NormalizeDoubleResult(Math.Asin((double)args[0])); break;
                case "Cos": result = NormalizeDoubleResult(Math.Cos((double)args[0])); break;
                case "Acos": result = NormalizeDoubleResult(Math.Acos((double)args[0])); break;
                case "Tan": result = NormalizeDoubleResult(Math.Tan((double)args[0])); break;
                case "Atan": result = NormalizeDoubleResult(Math.Atan((double)args[0])); break;
                case "Pow": result = NormalizeDoubleResult(Math.Pow((double)args[0], (double)args[1])); break;
                case "Log": result = NormalizeDoubleResult(Math.Log((double)args[0], (double)args[1])); break;
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

    /// <summary>
    /// Normalize a double result from a native math function before converting to decimal.
    /// Rounds to 15 significant digits and snaps near-zero values to exactly 0.
    /// This eliminates floating-point residue (e.g. Sin(Pi) ≈ 1.2e-16 → 0).
    /// </summary>
    private static decimal NormalizeDoubleResult(double value)
    {
        if (double.IsNaN(value) || double.IsInfinity(value))
            throw new OverflowException(); // caught by caller → NumericOverflow

        if (value == 0.0)
            return 0m;

        int digits = 15 - 1 - (int)Math.Floor(Math.Log10(Math.Abs(value)));
        if (digits < 0) digits = 0;
        if (digits > 15) digits = 15;

        var rounded = Math.Round(value, digits);

        if (Math.Abs(rounded) < 1e-15)
            return 0m;

        return (decimal)rounded;
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
        var calleeR = ResolveAlg(func, ctx);
        if (calleeR.IsError) return calleeR.Error;
        return EvalResolvedCall(calleeR.Value, argsAlg, ctx, valEnv, OpenExprName(func));
    }

    /// <summary>
    /// Counted call evaluation for <c>reduce</c> step validation.
    /// Lean: <c>evalCallCounted</c>.
    /// </summary>
    private static EvalResult<CountedResult> EvalCallCounted(
        Expr func,
        Algorithm argsAlg,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var calleeR = ResolveAlg(func, ctx);
        if (calleeR.IsError) return calleeR.Error;
        return EvalResolvedCallCounted(calleeR.Value, argsAlg, ctx, valEnv, OpenExprName(func));
    }

    /// <summary>
    /// Context-aware call evaluation for expression position.
    /// </summary>
    private static EvalResult<Result> EvalCallExpr(
        Expr func,
        Algorithm argsAlg,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var calleeR = ResolveAlg(func, ctx);
        if (calleeR.IsError)
            return new EvalError.WithContext(CtxCall(func), calleeR.Error) { Span = calleeR.Error.Span };

        return WithCtx(CtxCall(func), EvalResolvedCall(calleeR.Value, argsAlg, ctx, valEnv, OpenExprName(func)));
    }

    /// <summary>
    /// Counted expression-position call evaluation mirroring <see cref="EvalCallExpr"/>.
    /// </summary>
    private static EvalResult<CountedResult> EvalCallCountedExpr(
        Expr func,
        Algorithm argsAlg,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var calleeR = ResolveAlg(func, ctx);
        if (calleeR.IsError)
            return new EvalError.WithContext(CtxCall(func), calleeR.Error) { Span = calleeR.Error.Span };

        return WithCtx(CtxCall(func), EvalResolvedCallCounted(calleeR.Value, argsAlg, ctx, valEnv, OpenExprName(func)));
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
        return EvalConditionalShape(callee, argShape, ctx, valEnv, calleeName);
    }

    /// <summary>
    /// Counted conditional call evaluation.
    /// The argument matching semantics are unchanged; only the selected branch's
    /// emitted top-level output count is preserved.
    /// Lean: <c>evalConditionalCallCounted</c>.
    /// </summary>
    private static EvalResult<CountedResult> EvalConditionalCallCounted(
        Algorithm callee, Algorithm args,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv,
        string calleeName = "conditional")
    {
        var wiredArgs = WireToCaller(ctx, args);
        var argExprs = wiredArgs.Output;
        var argEvalCtx = ctx.Push(wiredArgs);

        var argResults = new List<Result>();
        foreach (var expr in argExprs)
        {
            var r = Eval(expr, argEvalCtx, valEnv);
            if (r.IsError) return r.Error;
            argResults.Add(r.Value);
        }

        var argShape = Result.FromItems(argResults);
        return EvalConditionalShapeCounted(callee, argShape, ctx, valEnv, calleeName);
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

    /// <summary>
    /// Dispatches an already-resolved callee.
    /// </summary>
    private static EvalResult<Result> EvalResolvedCall(
        Algorithm callee,
        Algorithm argsAlg,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv,
        string calleeName)
    {
        if (callee is Algorithm.Builtin(var builtinId))
        {
            var argAlgsR = ResolveArgAlgs(argsAlg, ctx);
            if (argAlgsR.IsError) return argAlgsR.Error;
            return ApplyBuiltin(builtinId, argAlgsR.Value, ctx, valEnv);
        }

        if (TryGetFlatBinderUserEquivalent(callee) is { } simpleCallee)
            return EvalUserCall(simpleCallee, argsAlg, ctx, valEnv);

        if (callee is Algorithm.Conditional)
            return EvalConditionalCall(callee, argsAlg, ctx, valEnv, calleeName);

        return EvalUserCall(callee, argsAlg, ctx, valEnv);
    }

    /// <summary>
    /// Counted user-defined call evaluation.
    /// Call semantics are unchanged; only the final emitted output count of the
    /// callee is preserved.
    /// Lean: <c>evalUserCallCounted</c>.
    /// </summary>
    private static EvalResult<CountedResult> EvalUserCallCounted(
        Algorithm callee, Algorithm args,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var wiredArgs = WireToCaller(ctx, args);
        var argExprs = wiredArgs.Output;
        var paramCount = callee.Params.Count;

        if (argExprs.Count > paramCount)
            return new EvalError.ArityMismatch(paramCount, argExprs.Count);

        var maybeAlgsR = TryResolveArgAlgs(wiredArgs, ctx);
        if (maybeAlgsR.IsError) return maybeAlgsR.Error;
        var maybeAlgs = maybeAlgsR.Value;
        var algBindings = BindAlgParams(callee.Params, maybeAlgs);

        var argEvalCtx = ctx.Push(wiredArgs);
        var valueParams = new List<string>();
        var valueResults = new List<Result>();

        for (var i = 0; i < paramCount; i++)
        {
            if (i >= argExprs.Count)
            {
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
            }
            else
            {
                return evalR.Error;
            }
        }

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
        return EvalAlgOutputCounted(callee, newCtx, newEnv);
    }

    /// <summary>
    /// Counted dispatch for an already-resolved effective callee.
    /// </summary>
    private static EvalResult<CountedResult> EvalResolvedCallCounted(
        Algorithm callee,
        Algorithm argsAlg,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv,
        string calleeName)
    {
        if (callee is Algorithm.Builtin(var builtinId))
        {
            var argAlgsR = ResolveArgAlgs(argsAlg, ctx);
            if (argAlgsR.IsError) return argAlgsR.Error;
            return ApplyBuiltinCounted(builtinId, argAlgsR.Value, ctx, valEnv);
        }

        if (TryGetFlatBinderUserEquivalent(callee) is { } simpleCallee)
            return EvalUserCallCounted(simpleCallee, argsAlg, ctx, valEnv);

        if (callee is Algorithm.Conditional)
            return EvalConditionalCallCounted(callee, argsAlg, ctx, valEnv, calleeName);

        return EvalUserCallCounted(callee, argsAlg, ctx, valEnv);
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
        if (name == "Output")
            return new EvalError.SpecialOutputAccess();

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
            var val = EvalMaybeMemoizedPropertyOutput(targetAlg, ctx, valEnv);
            if (val.IsError) return val.Error;
            return ResultToString(val.Value);
        }

        // Structural: property of target (any visibility — dot access sees private)
        var prop = LookupProp(targetAlg, name);
        if (prop is not null)
        {
            var wired = ChildOf(targetAlg, prop);
            if (argsOpt is null)
            {
                var simpleCallee = TryGetFlatBinderUserEquivalent(wired);
                if (simpleCallee is not null)
                    return new EvalError.ArityMismatch(simpleCallee.Params.Count, 0);

                if (wired is Algorithm.Conditional)
                    return new EvalError.NoMatchingBranch(name);

                // No args: 0-param → value access, has params → arity error
                if (wired.Params.Count == 0)
                    return EvalMaybeMemoizedStructuralPropertyOutput(prop, name, wired, ctx, valEnv);
                return new EvalError.ArityMismatch(wired.Params.Count, 0);
            }

            return EvalResolvedCall(wired, argsOpt, ctx, valEnv, name);
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
    /// Counted dotCall evaluation for <c>reduce</c> step validation.
    /// Lean: <c>evalDotCallCounted</c>.
    /// </summary>
    private static EvalResult<CountedResult> EvalDotCallCounted(
        Expr target, string name, Algorithm? argsOpt,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        if (name == "Output")
            return new EvalError.SpecialOutputAccess();

        var targetResult = ResolveAlg(target, ctx);
        if (targetResult.IsError)
        {
            if (targetResult.Error is EvalError.NotAnAlgorithm)
            {
                if (name == "string")
                {
                    var val = Eval(target, ctx, valEnv);
                    if (val.IsError) return val.Error;
                    var outR = ResultToString(val.Value);
                    if (outR.IsError) return outR.Error;
                    return EvalResult<CountedResult>.Ok(new CountedResult(outR.Value, outR.Value.ValueCount()));
                }
                return CallLexicalWithReceiverCounted(name, target, argsOpt, ctx, valEnv);
            }

            return targetResult.Error;
        }

        var targetAlg = targetResult.Value;
        var intrinsic = EvalStructuralIntrinsic(targetAlg, name);
        if (intrinsic is { } r)
        {
            if (r.IsError) return r.Error;
            return EvalResult<CountedResult>.Ok(new CountedResult(r.Value, r.Value.ValueCount()));
        }

        if (name == "string")
        {
            var val = EvalMaybeMemoizedPropertyOutput(targetAlg, ctx, valEnv);
            if (val.IsError) return val.Error;
            var outR = ResultToString(val.Value);
            if (outR.IsError) return outR.Error;
            return EvalResult<CountedResult>.Ok(new CountedResult(outR.Value, outR.Value.ValueCount()));
        }

        var prop = LookupProp(targetAlg, name);
        if (prop is not null)
        {
            var wired = ChildOf(targetAlg, prop);
            if (argsOpt is null)
            {
                var simpleCallee = TryGetFlatBinderUserEquivalent(wired);
                if (simpleCallee is not null)
                    return new EvalError.ArityMismatch(simpleCallee.Params.Count, 0);

                if (wired is Algorithm.Conditional)
                    return new EvalError.NoMatchingBranch(name);

                if (wired.Params.Count == 0)
                    return EvalMaybeMemoizedStructuralPropertyOutputCounted(prop, name, wired, ctx, valEnv);
                return new EvalError.ArityMismatch(wired.Params.Count, 0);
            }

            return EvalResolvedCallCounted(wired, argsOpt, ctx, valEnv, name);
        }

        return CallLexicalWithReceiverCounted(name, target, argsOpt, ctx, valEnv);
    }

    /// <summary>
    /// Counted lexical fallback with receiver injection.
    /// Mirrors <see cref="CallLexicalWithReceiver"/>, including while/repeat
    /// init packaging.
    /// Lean: <c>callLexicalWithReceiverCounted</c>.
    /// </summary>
    private static EvalResult<CountedResult> CallLexicalWithReceiverCounted(
        string name, Expr receiver, Algorithm? extraArgs,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var outputExprs = new List<Expr> { receiver };
        if (extraArgs is not null)
            outputExprs.AddRange(extraArgs.Output);

        var explicitCount = extraArgs?.Output.Count ?? 0;

        if (name == "while" && explicitCount >= 2)
        {
            var initExprs = outputExprs.GetRange(1, outputExprs.Count - 1);
            outputExprs = [receiver, MakeInitBlock(initExprs)];
        }
        else if (name == "repeat" && explicitCount >= 3)
        {
            var countExpr = outputExprs[1];
            var initExprs = outputExprs.GetRange(2, outputExprs.Count - 2);
            outputExprs = [receiver, countExpr, MakeInitBlock(initExprs)];
        }

        var combinedArgs = new Algorithm.User(
            Parent: null, Params: [], Opens: [],
            Properties: [], Output: outputExprs);

        return EvalCallCounted(new Expr.Resolve(name), combinedArgs, ctx, valEnv);
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
        => RunWithMemoizationStats(expr).Result;

    internal static (EvalResult<Result> Result, MemoizationStats Stats) RunWithMemoizationStats(Expr expr)
    {
        var runState = new EvaluatorRunState();
        var ctx = new EvalCtx([PreludeAlg], [], runState);
        var result = expr is Expr.Block(var alg)
            ? EvalRootProgram(alg, expr.Span, ctx)
            : Eval(expr, ctx, []);
        return (result, runState.SnapshotStats());
    }

    private static EvalResult<Result> EvalRootProgram(Algorithm alg, SourceSpan? span, EvalCtx ctx)
    {
        var wired = WireToCaller(ctx, alg);
        if (wired.Params.Count == 0)
            return EvalProgramOutput(wired, ctx, []);

        var blockSpan = span ?? FirstSpan(wired.Output);
        return new EvalError.UnresolvedImplicitParams(wired.Params) { Span = blockSpan };
    }

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
    /// Integer exponents use exact decimal exponentiation by squaring.
    /// Negative integers are handled as a decimal reciprocal of the positive power.
    /// Non-integer exponents use approximate <see cref="Math.Pow(double, double)"/> via double,
    /// then normalize the result using the evaluator's standard floating-point cleanup.
    /// </summary>
    private static EvalResult<Result> EvalPow(SourceSpan? span, decimal b, decimal exp)
    {
        try
        {
            var powR = DecimalPow(b, exp);
            if (powR.IsError)
                return powR.Error with { Span = span };
            return EvalResult<Result>.Ok(new Result.Atom(powR.Value));
        }
        catch (OverflowException)
        {
            return new EvalError.NumericOverflow() { Span = span };
        }
    }

    private static EvalResult<decimal> DecimalPow(decimal b, decimal exp)
    {
        if (exp != decimal.Truncate(exp))
            return EvalResult<decimal>.Ok(NormalizeDoubleResult(Math.Pow((double)b, (double)exp)));

        var exponent = decimal.ToInt64(exp);
        if (exponent < 0)
        {
            if (b == 0)
                return new EvalError.IllegalInEval("zero cannot be raised to a negative integer exponent");

            var absExponent = exponent == long.MinValue
                ? (ulong)long.MaxValue + 1UL
                : (ulong)(-exponent);

            var positivePower = DecimalPowNonNegative(b, absExponent);
            if (positivePower == 0)
                throw new OverflowException();
            return EvalResult<decimal>.Ok(1m / positivePower);
        }

        return EvalResult<decimal>.Ok(DecimalPowNonNegative(b, (ulong)exponent));
    }

    private static decimal DecimalPowNonNegative(decimal b, ulong exponent)
    {
        decimal result = 1m;
        var baseVal = b;
        var remainingExponent = exponent;

        while (remainingExponent > 0)
        {
            if ((remainingExponent & 1UL) == 1UL)
                result = checked(result * baseVal);

            remainingExponent >>= 1;
            if (remainingExponent > 0)
                baseVal = checked(baseVal * baseVal);
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
