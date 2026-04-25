using System.Collections;
using System.Runtime.CompilerServices;
using KatLang.Evaluation.Caching;

namespace KatLang;

/// <summary>
/// KatLang 0.75 evaluator matching the Lean specification.
/// Uses <see cref="EvalResult{T}"/> (<c>EvalM := Except Error</c>) for structured errors
/// instead of nullable returns.
/// Ownership-first lookup: local → parent chain structural → opens fallback across chain.
/// Property visibility: opens only expose PUBLIC exported properties; structural lookup sees exported properties only.
///
/// Builtins (If, While, Repeat, Atoms, Range, Filter, Map, Count, Contains, First, Last, Distinct, Take, Skip, Min, Max, Sum, Avg, Reduce) are injected via a prelude algorithm in the initial
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
    private readonly record struct ResolvedLexicalProperty(
        Algorithm? Owner,
        Property Binding,
        Algorithm ResolvedAlgorithm);

    private static readonly ConditionalWeakTable<ScopeCtx, Algorithm> ScopeOwnerAlgorithms = new();

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
        IReadOnlyList<(string Name, CountedResult Value)> CountedParamEnv,
        IZeroArgPropertyResultCache ZeroArgPropertyResultCache)
    {
        public static readonly EvalCtx Empty = new([], [], [], UncachedZeroArgPropertyResultCache.Instance);

        /// <summary>Lean: EvalCtx.push — prepend an algorithm to the call stack.</summary>
        public EvalCtx Push(Algorithm alg)
            => new(Prepend(alg, CallStack), AlgEnv, CountedParamEnv, ZeroArgPropertyResultCache);

        /// <summary>Lean: EvalCtx.head? — first algorithm in the call stack.</summary>
        public Algorithm? Head => CallStack.Count > 0 ? CallStack[0] : null;

        /// <summary>Lean: EvalCtx.withAlgEnv — replace the algorithm environment.</summary>
        public EvalCtx WithAlgEnv(IReadOnlyList<(string, Algorithm)> algEnv)
            => new(CallStack, algEnv, CountedParamEnv, ZeroArgPropertyResultCache);

        /// <summary>Replace the counted callback-parameter environment.</summary>
        public EvalCtx WithCountedParamEnv(IReadOnlyList<(string, CountedResult)> countedParamEnv)
            => new(CallStack, AlgEnv, countedParamEnv, ZeroArgPropertyResultCache);
    }

    // ── Environment types ────────────────────────────────────────────────────

    /// <summary>Value environment: maps parameter names to results. Lean: lookupVal (Option).</summary>
    private static Result? LookupVal(IReadOnlyList<(string Name, Result Value)> env, string name)
    {
        foreach (var (n, v) in env)
            if (n == name) return v;
        return null;
    }

    /// <summary>
    /// Counted callback-parameter environment for projected higher-order items.
    /// These bindings preserve both the normalized value and the emitted
    /// top-level count so callback params behave like <c>S:i</c>.
    /// </summary>
    private static CountedResult? LookupCountedParam(IReadOnlyList<(string Name, CountedResult Value)> env, string name)
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
    {
        var scope = new ScopeCtx(alg.Parent, alg.Opens, alg.Properties);
        ScopeOwnerAlgorithms.Add(scope, alg);
        return scope;
    }

    private static Algorithm? TryGetScopeOwnerAlgorithm(ScopeCtx scope)
        => ScopeOwnerAlgorithms.TryGetValue(scope, out var owner)
            ? owner
            : null;

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

    private static bool IsExported(Property property)
        => property.Exposure == PropertyExposure.Exported;

    private static Algorithm? LookupExportedProp(Algorithm alg, string name)
    {
        foreach (var prop in alg.Properties)
        {
            if (prop.Name == name && IsExported(prop))
                return prop.Value;
        }

        return null;
    }

    private static Property? LookupExportedPropBinding(Algorithm alg, string name)
    {
        foreach (var prop in alg.Properties)
        {
            if (prop.Name == name && IsExported(prop))
                return prop;
        }

        return null;
    }

    /// <summary>Lean: Algorithm.lookupPublicProp (public only).</summary>
    private static Algorithm? LookupPublicProp(Algorithm alg, string name)
    {
        foreach (var prop in alg.Properties)
            if (prop.Name == name && prop.IsPublic && IsExported(prop)) return prop.Value;
        return null;
    }

    private static Property? LookupPublicPropBinding(Algorithm alg, string name)
    {
        foreach (var prop in alg.Properties)
            if (prop.Name == name && prop.IsPublic && IsExported(prop)) return prop;
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

    private static bool ConditionalBranchesDefineProperty(Algorithm alg, string name)
    {
        if (alg is not Algorithm.Conditional conditional)
            return false;

        foreach (var branch in conditional.Branches)
        {
            foreach (var prop in branch.Body.Properties)
            {
                if (prop.Name == name)
                    return true;
            }
        }

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

    // ── Error context helpers ──────────────────────────────────────────────

    private static ErrorContext CtxOpen(string key) => new OpenResolutionContext(key);
    private static ErrorContext CtxCall(Expr f) => new CallContext(OpenExprName(f));
    private static ErrorContext CtxProperty(string name) => new PropertyEvaluationContext(name);
    private static ErrorContext CtxDotCall(Expr obj, string name) => new DotCallContext(OpenExprName(obj), name);

    // ── Error context helper ────────────────────────────────────────────────

    /// <summary>
    /// Attach context to any error raised by the given result.
    /// Lean: withCtx.
    /// </summary>
    private static EvalResult<T> WithCtx<T>(ErrorContext context, EvalResult<T> result) =>
        result.IsError
            ? new EvalError.WithContext(context, result.Error) { Span = result.Error.Span }
            : result;

    private static EvalResult<T> WithCtx<T>(string context, EvalResult<T> result)
        => WithCtx(new TextErrorContext(context), result);

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

    private static EvalResult<T> MissingImplicitArguments<T>(IReadOnlyList<string> paramNames, SourceSpan? span)
    {
        var inner = new EvalError.UnresolvedImplicitParams(paramNames) { Span = span };
        return new EvalError.WithContext(new ImplicitParameterContext(paramNames, 0), inner) { Span = span };
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
            if (prop.Name == name && prop.IsPublic && IsExported(prop))
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
                    hit.Lib,
                    hit.Binding,
                    ChildOf(hit.Lib, hit.Binding.Value)));
        }
        return new EvalError.AmbiguousOpen(name, hits.Select(h => h.Provider).ToList());
    }

    private static ResolvedLexicalProperty? LookupInParentsDirectBinding(ScopeCtx sc, string name)
    {
        foreach (var prop in sc.Properties)
        {
            if (prop.Name == name)
            {
                return new ResolvedLexicalProperty(
                    TryGetScopeOwnerAlgorithm(sc),
                    prop,
                    WithParent(prop.Value, sc));
            }
        }

        return sc.Parent is { } parent
            ? LookupInParentsDirectBinding(parent, name)
            : null;
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
    /// Resolve-only open lookup for the hot <see cref="Expr.Resolve"/> path.
    /// This preserves the same public-only open and ambiguity rules as
    /// <see cref="LookupOpens"/>, but avoids carrying binding metadata when the
    /// caller only needs the wired algorithm.
    /// </summary>
    private static EvalResult<Algorithm?> LookupOpensResolvedAlgorithm(
        Algorithm alg, string name, EvalCtx ctx)
    {
        if (alg.Opens.Count == 0) return EvalResult<Algorithm?>.Ok(null);

        var innerCtx = ctx.Push(alg);
        var resolvedResult = ResolveAllOpens(alg, innerCtx);
        if (resolvedResult.IsError) return resolvedResult.Error;

        (Algorithm Lib, Algorithm Child)? firstHit = null;
        List<string>? providers = null;

        foreach (var resolvedOpen in resolvedResult.Value)
        {
            var child = LookupPublicProp(resolvedOpen.Lib, name);
            if (child is null)
                continue;

            providers ??= [];
            providers.Add(resolvedOpen.Key);
            firstHit ??= (resolvedOpen.Lib, child);
        }

        if (providers is null)
            return EvalResult<Algorithm?>.Ok(null);
        if (providers.Count == 1)
        {
            var (lib, child) = firstHit!.Value;
            return EvalResult<Algorithm?>.Ok(ChildOf(lib, child));
        }

        return new EvalError.AmbiguousOpen(name, providers);
    }

    private static EvalResult<Algorithm?> LookupOpensInParentChainResolvedAlgorithm(
        ScopeCtx sc, string name, EvalCtx ctx)
    {
        var tempAlg = ForOpens(sc);
        var openResult = LookupOpensResolvedAlgorithm(tempAlg, name, ctx);
        if (openResult.IsError) return openResult.Error;
        if (openResult.Value is not null)
            return EvalResult<Algorithm?>.Ok(openResult.Value);

        return sc.Parent is { } parent
            ? LookupOpensInParentChainResolvedAlgorithm(parent, name, ctx)
            : EvalResult<Algorithm?>.Ok(null);
    }

    private static EvalResult<Algorithm?> LookupOpensInChainResolvedAlgorithm(
        Algorithm alg, string name, EvalCtx ctx)
    {
        var openResult = LookupOpensResolvedAlgorithm(alg, name, ctx);
        if (openResult.IsError) return openResult.Error;
        if (openResult.Value is not null)
            return EvalResult<Algorithm?>.Ok(openResult.Value);

        return alg.Parent is { } sc
            ? LookupOpensInParentChainResolvedAlgorithm(sc, name, ctx)
            : EvalResult<Algorithm?>.Ok(null);
    }

    /// <summary>
    /// Resolve-only lexical lookup for hot algorithm-resolution paths.
    /// Mirrors <see cref="LookupLexical"/> semantics, but returns only the wired
    /// algorithm so plain <see cref="Expr.Resolve"/> callers avoid binding/owner packaging.
    /// </summary>
    private static EvalResult<Algorithm> LookupLexicalResolvedAlgorithm(
        Algorithm alg, string name, EvalCtx ctx)
    {
        var direct = LookupLexicalDirect(alg, name);
        if (direct is not null)
            return EvalResult<Algorithm>.Ok(direct);

        var opensResult = LookupOpensInChainResolvedAlgorithm(alg, name, ctx);
        if (opensResult.IsError) return opensResult.Error;
        if (opensResult.Value is { } openAlgorithm)
            return EvalResult<Algorithm>.Ok(openAlgorithm);

        return new EvalError.UnknownName(name);
    }

    /// <summary>
    /// Fast path for plain lexical name resolution.
    /// This keeps <see cref="ResolveAlg"/> semantics intact while letting nearby
    /// synthetic callers resolve a name without allocating an <see cref="Expr.Resolve"/> wrapper.
    /// </summary>
    private static EvalResult<Algorithm> ResolveNamedAlgorithm(
        string name, SourceSpan? span, EvalCtx ctx)
    {
        if (ctx.CallStack.Count == 0)
            return new EvalError.UnknownName(name) { Span = span };

        var result = LookupLexicalResolvedAlgorithm(ctx.CallStack[0], name, ctx);
        return result.IsError && result.Error.Span is null
            ? result.Error with { Span = span }
            : result;
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
            return EvalResult<ResolvedLexicalProperty>.Ok(
                new ResolvedLexicalProperty(
                    alg,
                    local,
                    ChildOf(alg, local.Value)));

        // 2. Parent chain structural only (any visibility, no opens)
        if (alg.Parent is { } sc)
        {
            var structural = LookupInParentsDirectBinding(sc, name);
            if (structural is not null)
                return EvalResult<ResolvedLexicalProperty>.Ok(structural.Value);
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
    /// Evaluate <c>target:selector</c> through the shared one-level projected
    /// selection semantics.
    /// Construction preserves structure; selection projects content.
    /// </summary>
    private static EvalResult<CountedResult> EvalIndexSelectionCounted(
        Expr target,
        Expr selector,
        SourceSpan? span,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var targetR = Eval(target, ctx, valEnv);
        if (targetR.IsError) return targetR.Error;

        var nR = EvalInt(selector, ctx, valEnv);
        if (nR.IsError) return nR.Error;

        var n = nR.Value;
        if (n < 0 || n != Math.Floor(n))
            return new EvalError.BadIndex() { Span = span };

        var selected = targetR.Value.SelectProjected((int)n);
        if (selected is null)
            return new EvalError.BadIndex() { Span = span };

        return EvalResult<CountedResult>.Ok(
            new CountedResult(selected.Value.Value, selected.Value.EmittedCount));
    }

    /// <summary>
    /// Lean: <c>resultToExpr</c>. Reify a normalized result as an expression that
    /// evaluates back to the same shape.
    /// </summary>
    private static Expr EmptyResultExpr()
        => new Expr.Call(
            new Expr.Block(new Algorithm.Builtin(BuiltinId.take)),
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
    /// Helpers whose names end in <c>Counted</c> preserve this pair instead of
    /// collapsing it to just <see cref="Result"/>.
    /// Lean: <c>CountedResult</c>.
    /// </summary>
    private readonly record struct CountedResult(Result Value, int EmittedCount);

    private readonly record struct SequenceIterationItem(Result Value, int EmittedCount);

    /// <summary>
    /// Collected sequence input keeps both the real per-input boundary view and
    /// the prepared outer-item stream used by the current builtin.
    /// </summary>
    private readonly record struct CollectedSequenceBuiltinInput(
        IReadOnlyList<IReadOnlyList<Result>> PerInputItems,
        IReadOnlyList<Result> FlattenedItems)
    {
        public int TotalItemCount => FlattenedItems.Count;

        public bool AnyInputEmpty => PerInputItems.Any(static items => items.Count == 0);
    }

    /// <summary>
    /// Prepared input for current sequence builtin handlers.
    /// Numeric builtins cache the flattened numeric projection of the collected
    /// top-level items.
    /// </summary>
    private readonly record struct PreparedSequenceBuiltinInput(
        CollectedSequenceBuiltinInput Collected,
        IReadOnlyList<decimal>? NumericItems = null)
    {
        public IReadOnlyList<Result> FlattenedItems => Collected.FlattenedItems;
    }

    private abstract record PreparedSequenceBuiltinTrailingArg
    {
        public sealed record AlgorithmArg(KatLang.Algorithm AlgorithmValue) : PreparedSequenceBuiltinTrailingArg;

        public sealed record ValueArg(Result ResultValue) : PreparedSequenceBuiltinTrailingArg;

        public sealed record WholeNumberArg(decimal WholeNumberValue) : PreparedSequenceBuiltinTrailingArg;
    }

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
    /// Match a top-level conditional call head against the explicit arguments
    /// supplied at the call site.
    ///
    /// Ordinary direct conditional calls preserve explicit argument slots at
    /// the top level: a non-group head expects exactly one explicit argument,
    /// while a group head expects one explicit argument per group item. Nested
    /// grouped structure is still matched through <see cref="MatchPattern"/>.
    /// </summary>
    private static IReadOnlyList<(string, Result)>? MatchCallPattern(
        Pattern pattern,
        IReadOnlyList<Result> explicitArgs)
    {
        if (pattern is Pattern.Group(var items))
        {
            if (items.Count != explicitArgs.Count)
                return null;

            var bindings = new List<(string, Result)>();
            for (var i = 0; i < items.Count; i++)
            {
                var sub = MatchPattern(items[i], explicitArgs[i]);
                if (sub is null)
                    return null;
                bindings.AddRange(sub);
            }

            return bindings;
        }

        return explicitArgs.Count == 1 ? MatchPattern(pattern, explicitArgs[0]) : null;
    }

    private static (CondBranch Branch, IReadOnlyList<(string, Result)> Bindings)? MatchCallBranches(
        IReadOnlyList<CondBranch> branches,
        IReadOnlyList<Result> explicitArgs)
    {
        foreach (var branch in branches)
        {
            var bindings = MatchCallPattern(branch.Pattern, explicitArgs);
            if (bindings is not null)
                return (branch, bindings);
        }

        return null;
    }

    private static IReadOnlyList<(string, CountedResult)>? MatchCountedPattern(
        Pattern pattern,
        CountedResult result)
    {
        switch (pattern)
        {
            case Pattern.Bind(var name):
                return [(name, result)];

            case Pattern.LitInt(var n):
                return result.Value is Result.Atom(var v) && v == n
                    ? []
                    : null;

            case Pattern.LitString(var s):
                return result.Value is Result.Str(var sv) && sv == s
                    ? []
                    : null;

            case Pattern.Group(var items):
                IReadOnlyList<Result> members;
                if (result.Value is Result.Group(var groupedMembers))
                {
                    if (groupedMembers.Count != items.Count)
                        return null;

                    members = groupedMembers;
                }
                else if (items.Count == 1)
                {
                    members = [result.Value];
                }
                else
                {
                    return null;
                }

                var bindings = new List<(string, CountedResult)>();
                for (var i = 0; i < items.Count; i++)
                {
                    var sub = MatchCountedPattern(items[i], new CountedResult(members[i], members[i].ValueCount()));
                    if (sub is null)
                        return null;

                    bindings.AddRange(sub);
                }

                return bindings;

            default:
                return null;
        }
    }

    private static IReadOnlyList<(string, CountedResult)>? MatchCountedCallPattern(
        Pattern pattern,
        IReadOnlyList<CountedResult> explicitArgs)
    {
        if (pattern is Pattern.Group(var items))
        {
            if (items.Count != explicitArgs.Count)
                return null;

            var bindings = new List<(string, CountedResult)>();
            for (var i = 0; i < items.Count; i++)
            {
                var sub = MatchCountedPattern(items[i], explicitArgs[i]);
                if (sub is null)
                    return null;

                bindings.AddRange(sub);
            }

            return bindings;
        }

        return explicitArgs.Count == 1 ? MatchCountedPattern(pattern, explicitArgs[0]) : null;
    }

    private static (CondBranch Branch, IReadOnlyList<(string, CountedResult)> Bindings)? MatchCountedCallBranches(
        IReadOnlyList<CondBranch> branches,
        IReadOnlyList<CountedResult> explicitArgs)
    {
        foreach (var branch in branches)
        {
            var bindings = MatchCountedCallPattern(branch.Pattern, explicitArgs);
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
    /// higher-order sequence callbacks after the iterated item has already
    /// been projected through the same one-level rule as <c>:</c>.
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
    /// Reify a pre-evaluated callback argument as a zero-parameter algorithm
    /// that preserves the same value and emitted top-level count.
    /// </summary>
    private static Algorithm CountedArgAlgorithm(CountedResult arg)
    {
        IReadOnlyList<Expr> output = arg.EmittedCount switch
        {
            0 => [EmptyResultExpr()],
            1 => [ResultToExpr(arg.Value)],
            _ => arg.Value.ToItems().Select(ResultToExpr).ToList(),
        };

        return new Algorithm.User(
            Parent: null,
            Params: [],
            Opens: [],
            Properties: [],
            Output: output);
    }

    /// <summary>
    /// Reify each counted top-level item as its own zero-parameter algorithm.
    /// Sequence-builtin dot-call receivers use this so the receiver contributes
    /// the top-level items it denotes, while each reified item still flows
    /// through the ordinary leading-argument boundary rule when the builtin
    /// runs.
    /// </summary>
    private static IReadOnlyList<Algorithm> CountedTopLevelItemAlgorithms(CountedResult arg)
        => CountedTopLevelValues(arg)
            .Select(item => CountedArgAlgorithm(new CountedResult(item, 1)))
            .ToList();

    /// <summary>
    /// Ordinary call-style unpacking for a pre-evaluated explicit callback
    /// argument. A final explicit arg may still unpack across the remaining
    /// parameters, matching <c>callee(S:i)</c>.
    /// </summary>
    private static IReadOnlyList<CountedResult> UnpackCountedArg(CountedResult arg)
        => UnpackArgs(arg.Value)
            .Select(value => new CountedResult(value, value.ValueCount()))
            .ToList();

    /// <summary>
    /// Bind callback parameters while preserving the projected emitted count of
    /// the iterated item. This keeps callback params behaving like <c>S:i</c>
    /// without making them callable algorithms.
    /// </summary>
    private static EvalResult<IReadOnlyList<(string, CountedResult)>> BindCountedCallbackParams(
        IReadOnlyList<string> paramNames,
        IReadOnlyList<CountedResult> args)
    {
        if (args.Count > paramNames.Count)
            return new EvalError.ArityMismatch(paramNames.Count, args.Count);

        var boundValues = new List<CountedResult>(paramNames.Count);
        for (var argIndex = 0; argIndex < args.Count; argIndex++)
        {
            var isFinalArg = argIndex == args.Count - 1;
            var remainingParams = paramNames.Count - boundValues.Count;

            if (isFinalArg && remainingParams > 1)
            {
                boundValues.AddRange(UnpackCountedArg(args[argIndex]));
                break;
            }

            boundValues.Add(args[argIndex]);
        }

        if (boundValues.Count != paramNames.Count)
            return new EvalError.ArityMismatch(paramNames.Count, boundValues.Count);

        var bindings = new List<(string, CountedResult)>(paramNames.Count);
        for (var i = 0; i < paramNames.Count; i++)
            bindings.Add((paramNames[i], boundValues[i]));

        return EvalResult<IReadOnlyList<(string, CountedResult)>>.Ok(bindings);
    }

    /// <summary>
    /// Higher-order callbacks keep the collected item value shape for pattern
    /// matching, while the counted callback-param view still uses the same
    /// one-level projection rule as <c>S:i</c> for callback param operations
    /// like <c>x.count</c>.
    /// </summary>
    private static CountedResult CountedSequenceCallbackItem(SequenceIterationItem item)
    {
        var projected = item.Value.ProjectIteratedContent();
        return new CountedResult(projected.Value, projected.EmittedCount);
    }

    /// <summary>
    /// Evaluate a resolved algorithm against pre-evaluated callback arguments
    /// that preserve their emitted top-level counts.
    /// </summary>
    private static EvalResult<CountedResult> EvalResolvedCallbackCallCounted(
        Algorithm callee,
        IReadOnlyList<CountedResult> args,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv,
        string calleeName = "conditional")
    {
        switch (callee)
        {
            case Algorithm.Builtin(var builtin):
                return ApplyBuiltinCounted(
                    builtin,
                    args.Select(CountedArgAlgorithm).ToList(),
                    ctx,
                    valEnv);

            case Algorithm.Conditional:
                if (TryGetFlatBinderUserEquivalent(callee) is { } simpleCallee)
                {
                    if (simpleCallee.Output.Count == 0)
                        return new EvalError.MissingOutput();

                    var countedEnvR = BindCountedCallbackParams(simpleCallee.Params, args);
                    if (countedEnvR.IsError) return countedEnvR.Error;

                    var newCtx = ctx.WithCountedParamEnv(Concat(countedEnvR.Value, ctx.CountedParamEnv));
                    return EvalAlgOutputCounted(simpleCallee, newCtx, valEnv);
                }

                return EvalConditionalCallbackCallCounted(callee, args, ctx, valEnv, calleeName);

            default:
            {
                if (callee.Output.Count == 0)
                    return new EvalError.MissingOutput();

                var countedEnvR = BindCountedCallbackParams(callee.Params, args);
                if (countedEnvR.IsError) return countedEnvR.Error;

                var newCtx = ctx.WithCountedParamEnv(Concat(countedEnvR.Value, ctx.CountedParamEnv));
                return EvalAlgOutputCounted(callee, newCtx, valEnv);
            }
        }
    }

    /// <summary>
    /// Non-counted wrapper for callback dispatch that still preserves projected
    /// item emitted counts internally where downstream operations depend on
    /// them.
    /// </summary>
    private static EvalResult<Result> EvalResolvedCallbackCall(
        Algorithm callee,
        IReadOnlyList<CountedResult> args,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv,
        string calleeName = "conditional")
    {
        var callbackR = EvalResolvedCallbackCallCounted(callee, args, ctx, valEnv, calleeName);
        return callbackR.IsError
            ? callbackR.Error
            : EvalResult<Result>.Ok(callbackR.Value.Value);
    }

    /// <summary>
    /// Evaluate a higher-order sequence callback on one iterated item.
    /// </summary>
    private static EvalResult<Result> EvalSequenceCallbackCall(
        Algorithm callee,
        SequenceIterationItem item,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv,
        string calleeName = "conditional")
        => EvalResolvedCallbackCall(callee, [CountedSequenceCallbackItem(item)], ctx, valEnv, calleeName);

    /// <summary>
    /// Counted variant of <see cref="EvalSequenceCallbackCall"/>.
    /// </summary>
    private static EvalResult<CountedResult> EvalSequenceCallbackCallCounted(
        Algorithm callee,
        SequenceIterationItem item,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv,
        string calleeName = "conditional")
        => EvalResolvedCallbackCallCounted(callee, [CountedSequenceCallbackItem(item)], ctx, valEnv, calleeName);

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

    private static EvalResult<ZeroArgPropertyResult> EvaluateZeroArgPropertyResult(
        Algorithm resolvedAlgorithm,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var countedR = EvalAlgOutputCounted(resolvedAlgorithm, ctx, valEnv);
        if (countedR.IsError)
            return countedR.Error;

        return EvalResult<ZeroArgPropertyResult>.Ok(
            new ZeroArgPropertyResult(countedR.Value.Value, countedR.Value.EmittedCount));
    }

    private static EvalResult<ZeroArgPropertyResult> GetOrEvaluateZeroArgPropertyResult(
        Algorithm? owner,
        Property binding,
        ZeroArgPropertyAccessKind accessKind,
        Algorithm resolvedAlgorithm,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        if (owner is null)
            return EvaluateZeroArgPropertyResult(resolvedAlgorithm, ctx, valEnv);

        return ctx.ZeroArgPropertyResultCache.GetOrEvaluate(
            new ZeroArgPropertyExecution(
                owner,
                binding,
                accessKind,
                valEnv,
                ctx.AlgEnv,
                ctx.CountedParamEnv),
            () => EvaluateZeroArgPropertyResult(resolvedAlgorithm, ctx, valEnv));
    }

    private static EvalResult<Result> EvalZeroArgPropertyAccess(
        Algorithm? owner,
        Property binding,
        ZeroArgPropertyAccessKind accessKind,
        Algorithm resolvedAlgorithm,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var propertyR = GetOrEvaluateZeroArgPropertyResult(owner, binding, accessKind, resolvedAlgorithm, ctx, valEnv);
        return propertyR.IsError
            ? propertyR.Error
            : EvalResult<Result>.Ok(propertyR.Value.Value);
    }

    private static EvalResult<Result> EvalZeroArgPropertyAccess(
        ResolvedLexicalProperty resolvedProperty,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
        => EvalZeroArgPropertyAccess(
            resolvedProperty.Owner,
            resolvedProperty.Binding,
            ZeroArgPropertyAccessKind.Lexical,
            resolvedProperty.ResolvedAlgorithm,
            ctx,
            valEnv);

    private static EvalResult<CountedResult> EvalZeroArgPropertyAccessCounted(
        Algorithm? owner,
        Property binding,
        ZeroArgPropertyAccessKind accessKind,
        Algorithm resolvedAlgorithm,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var propertyR = GetOrEvaluateZeroArgPropertyResult(owner, binding, accessKind, resolvedAlgorithm, ctx, valEnv);
        return propertyR.IsError
            ? propertyR.Error
            : EvalResult<CountedResult>.Ok(new CountedResult(propertyR.Value.Value, propertyR.Value.EmittedCount));
    }

    private static EvalResult<CountedResult> EvalZeroArgPropertyAccessCounted(
        ResolvedLexicalProperty resolvedProperty,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
        => EvalZeroArgPropertyAccessCounted(
            resolvedProperty.Owner,
            resolvedProperty.Binding,
            ZeroArgPropertyAccessKind.CountedLexical,
            resolvedProperty.ResolvedAlgorithm,
            ctx,
            valEnv);

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

    private static EvalResult<CountedResult> EvalConditionalCallbackCallCounted(
        Algorithm callee,
        IReadOnlyList<CountedResult> explicitArgs,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv,
        string calleeName = "conditional")
    {
        if (callee.HasDuplicateBranchPatterns())
            return new EvalError.DuplicateBranchPattern();

        var match = MatchCountedCallBranches(callee.Branches, explicitArgs);
        if (match is null)
            return new EvalError.NoMatchingBranch(calleeName);

        var (branch, bindings) = match.Value;
        var wiredBody = ChildOf(callee, branch.Body);
        var newCtx = ctx.Push(callee).WithCountedParamEnv(Concat(bindings, ctx.CountedParamEnv));
        var newEnv = Concat(bindings.Select(static binding => (binding.Item1, binding.Item2.Value)).ToList(), valEnv);
        return EvalAlgOutputCounted(wiredBody, newCtx, newEnv);
    }

    /// <summary>
    /// Evaluate a <c>reduce</c> step on one collected iteration item while the
    /// accumulator keeps ordinary explicit-argument semantics.
    /// </summary>
    private static EvalResult<CountedResult> EvalSequenceReduceStepCounted(
        Algorithm callee,
        SequenceIterationItem element,
        Result accumulator,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv,
        string calleeName = "conditional")
        => EvalResolvedCallbackCallCounted(
            callee,
            [CountedSequenceCallbackItem(element), new CountedResult(accumulator, accumulator.ValueCount())],
            ctx,
            valEnv,
            calleeName);

    /// <summary>
    /// Recover the top-level values emitted at one algorithm boundary from a
    /// counted result.
    /// A grouped value emitted as one top-level result stays grouped, while a
    /// multi-output result is expanded back to its top-level items.
    /// </summary>
    private static List<Result> CountedTopLevelValues(CountedResult output)
    {
        var items = new List<Result>();
        AddCountedTopLevelValues(items, output);
        return items;
    }

    private static void AddCountedTopLevelValues(List<Result> into, CountedResult output)
    {
        if (output.EmittedCount == 0)
            return;

        if (output.EmittedCount == 1)
        {
            into.Add(output.Value);
            return;
        }

        ResultItems(into, output.Value);
    }

    private static List<Expr> CombineLeaves(Expr expr)
    {
        var leaves = new List<Expr>();
        var stack = new Stack<Expr>();
        stack.Push(expr);

        while (stack.Count != 0)
        {
            var current = stack.Pop();
            if (current is Expr.Combine(var left, var right))
            {
                stack.Push(right);
                stack.Push(left);
                continue;
            }

            leaves.Add(current);
        }

        return leaves;
    }

    private static EvalResult<CountedResult> EvalCombineCounted(
        Expr expr,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var leaves = CombineLeaves(expr);
        var items = new List<Result>(leaves.Count);
        var emittedCount = 0;

        foreach (var leaf in leaves)
        {
            var leafR = EvalCounted(leaf, ctx, valEnv);
            if (leafR.IsError) return leafR.Error;

            AddCountedTopLevelValues(items, leafR.Value);
            emittedCount += leafR.Value.EmittedCount;
        }

        return EvalResult<CountedResult>.Ok(new CountedResult(
            Result.FromItems(items),
            emittedCount));
    }

    /// <summary>
    /// Explicit content projection for higher-order plain-call arguments.
    /// A selected value (<c>S:i</c>) and an explicit combine (<c>a; b</c>)
    /// still contribute their denoted top-level items when a builtin is using
    /// ordinary-argument outer iteration.
    /// </summary>
    private static bool UsesExplicitOuterSequenceContent(Algorithm collectionArg)
        => collectionArg is Algorithm.User { Params.Count: 0, Output.Count: 1 } user
            && user.Output[0] is Expr.Combine or Expr.Index;

    private static IReadOnlyList<Result> CollectSequenceBuiltinInputItems(
        SequenceBuiltinCollectionMode collectionMode,
        Algorithm collectionArg,
        CountedResult output)
    {
        if (collectionMode == SequenceBuiltinCollectionMode.FlattenedTopLevelItems
            || UsesExplicitOuterSequenceContent(collectionArg))
        {
            return CountedTopLevelValues(output);
        }

        return output.EmittedCount == 0
            ? []
            : [output.Value];
    }

    private static IReadOnlyList<SequenceIterationItem> CollectSequenceIterationItems(
        SequenceBuiltinCollectionMode collectionMode,
        Algorithm collectionArg,
        CountedResult output)
    {
        if (collectionMode == SequenceBuiltinCollectionMode.FlattenedTopLevelItems
            || UsesExplicitOuterSequenceContent(collectionArg))
        {
            return CountedTopLevelValues(output)
                .Select(item => new SequenceIterationItem(item, 1))
                .ToList();
        }

        return output.EmittedCount == 0
            ? []
            : [new SequenceIterationItem(output.Value, output.EmittedCount)];
    }

    private static (IReadOnlyList<Algorithm> SequenceArgs, IReadOnlyList<Algorithm> TrailingArgs)? SplitSequenceBuiltinArgs(
        SequenceBuiltinMetadata metadata,
        IReadOnlyList<Algorithm> args)
    {
        if (args.Count < metadata.TrailingArgCount)
            return null;

        var sequenceCount = args.Count - metadata.TrailingArgCount;
        if (!metadata.LeadingSequenceArity.Accepts(sequenceCount))
            return null;

        return (args.Take(sequenceCount).ToList(), args.Skip(sequenceCount).ToList());
    }

    /// <summary>
    /// Split leading sequence arguments away from a sequence builtin's fixed
    /// trailing arguments according to the builtin metadata.
    /// This validates only the call shape. Builtin-specific handlers remain
    /// free to decide when to evaluate or prepare the leading sequence inputs.
    /// </summary>
    private static EvalResult<CountedResult> ApplySequenceBuiltinCounted(
        BuiltinId builtin,
        SequenceBuiltinMetadata metadata,
        IReadOnlyList<Algorithm> args,
        Func<IReadOnlyList<Algorithm>, IReadOnlyList<Algorithm>, EvalResult<CountedResult>> handler)
    {
        var split = SplitSequenceBuiltinArgs(metadata, args);
        if (split is null)
            return WrongBuiltinArity(builtin, args.Count);

        return handler(split.Value.SequenceArgs, split.Value.TrailingArgs);
    }

    /// <summary>
    /// Evaluate the leading sequence arguments for a sequence builtin.
    /// Direct-consumption builtins read counted top-level items, while
    /// higher-order plain-call builtins can preserve each ordinary argument as
    /// one outer iteration item unless the argument explicitly projects or
    /// combines sequence content.
    /// Handlers call this explicitly so they can choose when leading sequence
    /// evaluation happens relative to any trailing-argument validation.
    /// </summary>
    private static EvalResult<CollectedSequenceBuiltinInput> EvalCountedSequenceInputs(
        SequenceBuiltinCollectionMode collectionMode,
        IReadOnlyList<Algorithm> collectionArgs,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var perInputItems = new List<IReadOnlyList<Result>>(collectionArgs.Count);
        var flattenedItems = new List<Result>();
        foreach (var collectionArg in collectionArgs)
        {
            var outputR = EvalAlgOutputCounted(collectionArg, ctx, valEnv);
            if (outputR.IsError) return outputR.Error;

            var items = CollectSequenceBuiltinInputItems(collectionMode, collectionArg, outputR.Value);
            perInputItems.Add(items);
            flattenedItems.AddRange(items);
        }

        return EvalResult<CollectedSequenceBuiltinInput>.Ok(
            new CollectedSequenceBuiltinInput(perInputItems, flattenedItems));
    }

    private static EvalResult<IReadOnlyList<SequenceIterationItem>> EvalSequenceIterationItems(
        SequenceBuiltinCollectionMode collectionMode,
        IReadOnlyList<Algorithm> collectionArgs,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var items = new List<SequenceIterationItem>();
        foreach (var collectionArg in collectionArgs)
        {
            var outputR = EvalAlgOutputCounted(collectionArg, ctx, valEnv);
            if (outputR.IsError) return outputR.Error;

            items.AddRange(CollectSequenceIterationItems(collectionMode, collectionArg, outputR.Value));
        }

        return EvalResult<IReadOnlyList<SequenceIterationItem>>.Ok(items);
    }

    private static EvalResult<CollectedSequenceBuiltinInput> ApplySequenceBuiltinEmptyPolicy(
        BuiltinId builtin,
        SequenceBuiltinMetadata metadata,
        CollectedSequenceBuiltinInput collected)
    {
        return metadata.EmptyPolicy switch
        {
            SequenceBuiltinEmptyPolicy.AllowEmpty => EvalResult<CollectedSequenceBuiltinInput>.Ok(collected),
            SequenceBuiltinEmptyPolicy.RequireAnyItem when collected.TotalItemCount == 0 => new EvalError.WithContext(
                $"{BuiltinDisplayName(builtin)} requires a non-empty collection",
                new EvalError.BadArity()),
            SequenceBuiltinEmptyPolicy.RequireEachInputNonEmpty when collected.AnyInputEmpty => new EvalError.WithContext(
                $"{BuiltinDisplayName(builtin)} requires each input collection to be non-empty",
                new EvalError.BadArity()),
            _ => EvalResult<CollectedSequenceBuiltinInput>.Ok(collected),
        };
    }

    private static string DescribeSequenceItem(Result item) => item switch
    {
        Result.Atom(var n) => $"numeric value {n}",
        Result.Str(var s) => $"string value \"{s}\"",
        Result.Group(var items) when items.Count == 0 => "empty grouped value",
        Result.Group => "grouped value",
        _ => "value",
    };

    private static string NumericSequenceItemErrorContext(BuiltinId builtin, int index, Result item)
        => $"{BuiltinDisplayName(builtin)} expects each collection element to be a single numeric value; item {index} was {DescribeSequenceItem(item)}";

    private static EvalError ReduceInitialAccumulatorRequiresValueError(Algorithm initialAlg)
        => new EvalError.WithContext(
            new ReduceInitialAccumulatorContext(initialAlg.Params.ToList()),
            new EvalError.BadArity());

    private static bool IsLikelyUnevaluatedParameterError(Algorithm algorithm, EvalError error)
    {
        if (algorithm.Params.Count == 0)
            return false;

        var parameterNames = algorithm.Params.ToHashSet(StringComparer.Ordinal);
        return ErrorReferencesAnyName(error, parameterNames);
    }

    private static bool ErrorReferencesAnyName(EvalError error, IReadOnlySet<string> names)
        => error switch
        {
            EvalError.UnknownName(var name) => names.Contains(name),
            EvalError.UnresolvedImplicitParams(var paramNames) => paramNames.Any(names.Contains),
            EvalError.WithContext(_, var inner) => ErrorReferencesAnyName(inner, names),
            _ => false,
        };

    /// <summary>
    /// Evaluate <c>reduce</c> over one or more leading sequence arguments while
    /// preserving the accumulator's emitted-value count for the empty-sequence
    /// case.
    /// The current item is passed exactly as collected for this iteration:
    /// ordinary plain-call boundaries stay whole, while explicit <c>;</c>,
    /// <c>:</c>, and dot-call receiver iteration provide content items.
    /// The accumulator keeps ordinary explicit-argument semantics.
    /// Lean: <c>evalReduceCounted</c>.
    /// </summary>
    private static EvalResult<CountedResult> EvalReduceCounted(
        IReadOnlyList<SequenceIterationItem> items,
        Algorithm stepAlg,
        Algorithm initialAlg,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var initialR = EvalAlgOutputCounted(initialAlg, ctx, valEnv);
        if (initialR.IsError)
        {
            if (IsLikelyUnevaluatedParameterError(initialAlg, initialR.Error))
                return ReduceInitialAccumulatorRequiresValueError(initialAlg);

            return initialR.Error;
        }

        var accumulator = initialR.Value;
        foreach (var item in items)
        {
            var stepR = WithCtx(
                "while evaluating reduce step (reduce passes each iterated collection item as collected; ordinary boundaries stay whole, explicit ;/: iterate content, and the accumulator is unchanged)",
                EvalSequenceReduceStepCounted(stepAlg, item, accumulator.Value, ctx, valEnv, "reduce step"));
            if (stepR.IsError) return stepR.Error;

            var nextR = ExpectSingleAccumulator(stepR.Value);
            if (nextR.IsError) return nextR.Error;

            accumulator = new CountedResult(nextR.Value, 1);
        }

        return EvalResult<CountedResult>.Ok(accumulator);
    }

    /// <summary>
    /// Evaluate <c>filter</c> over one or more leading sequence arguments.
    /// The final argument is the predicate.
    /// Each iterated item is passed exactly as collected for this iteration:
    /// ordinary plain-call boundaries stay whole, while explicit <c>;</c>,
    /// <c>:</c>, and dot-call receiver iteration provide content items.
    /// Kept outputs remain the original sequence items.
    /// </summary>
    private static EvalResult<CountedResult> EvalFilterCounted(
        IReadOnlyList<SequenceIterationItem> items,
        Algorithm predicateAlg,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var kept = new List<Result>();
        foreach (var item in items)
        {
            var predicateR = WithCtx(
                "while evaluating filter predicate (filter passes each iterated collection item as collected; ordinary boundaries stay whole and explicit ;/: iterate content)",
                EvalSequenceCallbackCall(predicateAlg, item, ctx, valEnv, "filter predicate"));
            if (predicateR.IsError)
            {
                if (ShouldTreatFilterCallbackFailureAsFalse(item, predicateR.Error))
                    continue;

                return predicateR.Error;
            }

            var truth = predicateR.Value.SingleAtomicTruthValue();
            if (truth is null)
            {
                return new EvalError.WithContext(
                    "filter predicate must return exactly one atomic numeric value",
                    new EvalError.BadArity());
            }

            if (truth.Value)
                kept.Add(item.Value);
        }

        return EvalResult<CountedResult>.Ok(new CountedResult(Result.FromItems(kept), kept.Count));
    }

    /// <summary>
    /// Evaluate <c>map</c> over one or more leading sequence arguments while
    /// preserving the number of top-level mapped elements.
    /// Each callback item is passed exactly as collected for this iteration:
    /// ordinary plain-call boundaries stay whole, while explicit <c>;</c>,
    /// <c>:</c>, and dot-call receiver iteration provide content items.
    /// Lean: <c>evalMapCounted</c>.
    /// </summary>
    private static EvalResult<CountedResult> EvalMapCounted(
        IReadOnlyList<SequenceIterationItem> items,
        Algorithm transformAlg,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var mapped = new List<Result>(items.Count);
        foreach (var item in items)
        {
            var transformR = WithCtx(
                "while evaluating map transform (map passes each iterated collection item as collected; ordinary boundaries stay whole and explicit ;/: iterate content)",
                EvalSequenceCallbackCallCounted(transformAlg, item, ctx, valEnv, "map transform"));
            if (transformR.IsError) return transformR.Error;

            var mappedElementR = ExpectSingleMappedElement(transformR.Value);
            if (mappedElementR.IsError) return mappedElementR.Error;

            mapped.Add(mappedElementR.Value);
        }

        return EvalResult<CountedResult>.Ok(new CountedResult(Result.FromItems(mapped), mapped.Count));
    }

    /// <summary>
    /// Collect top-level sequence items as single atomic numeric values.
    /// Used by numeric ordering and aggregation builtins that only accept
    /// clearly comparable numeric elements and reject strings or grouped values.
    /// Diagnostics include the 0-based item index after counted top-level
    /// extraction so numeric shape failures are easier to debug.
    /// </summary>
    private static EvalResult<List<decimal>> CollectSingleAtomicNumbers(
        BuiltinId builtin,
        IReadOnlyList<Result> elements)
    {
        var numbers = new List<decimal>(elements.Count);
        for (var index = 0; index < elements.Count; index++)
        {
            var item = elements[index];
            var numeric = item.SingleAtomicNumber();
            if (numeric is null)
            {
                return new EvalError.WithContext(
                    NumericSequenceItemErrorContext(builtin, index, item),
                    new EvalError.BadArity());
            }

            numbers.Add(numeric.Value);
        }

        return EvalResult<List<decimal>>.Ok(numbers);
    }

    private static EvalResult<PreparedSequenceBuiltinInput> PrepareSequenceBuiltinInput(
        BuiltinId builtin,
        SequenceBuiltinMetadata metadata,
        CollectedSequenceBuiltinInput collected)
    {
        var validatedItemsR = ApplySequenceBuiltinEmptyPolicy(builtin, metadata, collected);
        if (validatedItemsR.IsError) return validatedItemsR.Error;

        IReadOnlyList<decimal>? numericItems = null;
        switch (metadata.ItemShapeConstraint)
        {
            case SequenceBuiltinItemShapeConstraint.Any:
                break;

            case SequenceBuiltinItemShapeConstraint.SingleNumeric:
            {
                var numbersR = CollectSingleAtomicNumbers(builtin, validatedItemsR.Value.FlattenedItems);
                if (numbersR.IsError) return numbersR.Error;
                numericItems = numbersR.Value;
                break;
            }
        }

        return EvalResult<PreparedSequenceBuiltinInput>.Ok(
            new PreparedSequenceBuiltinInput(validatedItemsR.Value, numericItems));
    }

    /// <summary>
    /// Evaluate and prepare a sequence builtin's leading inputs according to the
    /// builtin metadata.
    /// Shared preparation is eager by design: once a handler opts into this
    /// helper, all leading sequence arguments are evaluated before builtin-
    /// specific processing continues. Handlers choose when to opt into that
    /// preparation relative to any trailing-argument validation.
    /// </summary>
    private static EvalResult<PreparedSequenceBuiltinInput> EvalPreparedSequenceBuiltinInput(
        BuiltinId builtin,
        SequenceBuiltinMetadata metadata,
        IReadOnlyList<Algorithm> collectionArgs,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var collectedR = EvalCountedSequenceInputs(metadata.CollectionMode, collectionArgs, ctx, valEnv);
        if (collectedR.IsError) return collectedR.Error;

        return PrepareSequenceBuiltinInput(builtin, metadata, collectedR.Value);
    }

    private static EvalError InnermostError(EvalError error)
    {
        while (error is EvalError.WithContext context)
            error = context.Inner;

        return error;
    }

    private static bool ShouldTreatFilterCallbackFailureAsFalse(SequenceIterationItem item, EvalError error)
        => item.EmittedCount > 1
            && item.Value is Result.Group
            && InnermostError(error) is EvalError.TypeMismatch or EvalError.NoMatchingBranch or EvalError.BadArity;

    private static string DescribeSequenceBuiltinTrailingArgRequirement(
        SequenceBuiltinTrailingArgKind kind)
        => kind switch
        {
            SequenceBuiltinTrailingArgKind.Algorithm => "an algorithm",
            SequenceBuiltinTrailingArgKind.Value => "exactly one value",
            SequenceBuiltinTrailingArgKind.WholeNumber => "exactly one whole-number value",
            _ => "a valid trailing argument",
        };

    private static string DescribeSequenceBuiltinTrailingArgKind(
        SequenceBuiltinTrailingArgKind kind)
        => kind switch
        {
            SequenceBuiltinTrailingArgKind.Algorithm => "algorithm",
            SequenceBuiltinTrailingArgKind.Value => "value",
            SequenceBuiltinTrailingArgKind.WholeNumber => "whole-number value",
            _ => "unknown",
        };

    private static string SequenceBuiltinTrailingArgErrorContext(
        BuiltinId builtin,
        SequenceBuiltinTrailingArgDescriptor descriptor)
        => $"{BuiltinDisplayName(builtin)} {descriptor.Label} must be {DescribeSequenceBuiltinTrailingArgRequirement(descriptor.Kind)}";

    private static EvalResult<T> InternalSequenceBuiltinTrailingArgMetadataError<T>(
        BuiltinId builtin,
        string detail)
        => new EvalError.WithContext(
            $"internal sequence metadata for {BuiltinDisplayName(builtin)} {detail}",
            new EvalError.BadArity());

    private static EvalResult<PreparedSequenceBuiltinTrailingArg> EvalPreparedSequenceBuiltinTrailingArg(
        BuiltinId builtin,
        SequenceBuiltinTrailingArgDescriptor descriptor,
        Algorithm arg,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        switch (descriptor.Kind)
        {
            case SequenceBuiltinTrailingArgKind.Algorithm:
                return EvalResult<PreparedSequenceBuiltinTrailingArg>.Ok(
                    new PreparedSequenceBuiltinTrailingArg.AlgorithmArg(arg));

            case SequenceBuiltinTrailingArgKind.Value:
            {
                var valueR = EvalAlgOutput(arg, ctx, valEnv);
                if (valueR.IsError) return valueR.Error;

                return EvalResult<PreparedSequenceBuiltinTrailingArg>.Ok(
                    new PreparedSequenceBuiltinTrailingArg.ValueArg(valueR.Value));
            }

            case SequenceBuiltinTrailingArgKind.WholeNumber:
            {
                var valueR = EvalAlgOutput(arg, ctx, valEnv);
                if (valueR.IsError) return valueR.Error;

                var numeric = valueR.Value.SingleAtomicNumber();
                if (numeric is null || numeric.Value != Math.Truncate(numeric.Value))
                {
                    return new EvalError.WithContext(
                        SequenceBuiltinTrailingArgErrorContext(builtin, descriptor),
                        new EvalError.BadArity());
                }

                return EvalResult<PreparedSequenceBuiltinTrailingArg>.Ok(
                    new PreparedSequenceBuiltinTrailingArg.WholeNumberArg(numeric.Value));
            }

            default:
                return InternalSequenceBuiltinTrailingArgMetadataError<PreparedSequenceBuiltinTrailingArg>(
                    builtin,
                    "used an unknown trailing-argument kind");
        }
    }

    /// <summary>
    /// Shared trailing-argument preparation path for sequence builtins.
    /// Metadata stays the source of truth for trailing count and kinds; callers
    /// use the typed ExpectPrepared... helpers below to extract prepared values.
    /// </summary>
    private static EvalResult<IReadOnlyList<PreparedSequenceBuiltinTrailingArg>> EvalPreparedSequenceBuiltinTrailingArgs(
        BuiltinId builtin,
        IReadOnlyList<SequenceBuiltinTrailingArgDescriptor> descriptors,
        IReadOnlyList<Algorithm> args,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        if (descriptors.Count != args.Count)
        {
            return InternalSequenceBuiltinTrailingArgMetadataError<IReadOnlyList<PreparedSequenceBuiltinTrailingArg>>(
                builtin,
                "mismatched trailing arguments");
        }

        var preparedArgs = new List<PreparedSequenceBuiltinTrailingArg>(args.Count);
        for (var index = 0; index < args.Count; index++)
        {
            var preparedArgR = EvalPreparedSequenceBuiltinTrailingArg(
                builtin,
                descriptors[index],
                args[index],
                ctx,
                valEnv);
            if (preparedArgR.IsError) return preparedArgR.Error;

            preparedArgs.Add(preparedArgR.Value);
        }

        return EvalResult<IReadOnlyList<PreparedSequenceBuiltinTrailingArg>>.Ok(preparedArgs);
    }

    private static EvalResult<T> ExpectPreparedSequenceBuiltinTrailingArgAt<T>(
        BuiltinId builtin,
        IReadOnlyList<SequenceBuiltinTrailingArgDescriptor> descriptors,
        IReadOnlyList<PreparedSequenceBuiltinTrailingArg> args,
        int index,
        SequenceBuiltinTrailingArgKind expectedKind,
        Func<SequenceBuiltinTrailingArgDescriptor, PreparedSequenceBuiltinTrailingArg, EvalResult<T>> projector)
    {
        if (descriptors.Count != args.Count)
        {
            return InternalSequenceBuiltinTrailingArgMetadataError<T>(
                builtin,
                "mismatched trailing arguments");
        }

        if ((uint)index >= (uint)descriptors.Count)
        {
            return InternalSequenceBuiltinTrailingArgMetadataError<T>(
                builtin,
                $"expected trailing argument {index + 1} to have metadata kind {DescribeSequenceBuiltinTrailingArgKind(expectedKind)}");
        }

        var descriptor = descriptors[index];
        if (descriptor.Kind != expectedKind)
        {
            return InternalSequenceBuiltinTrailingArgMetadataError<T>(
                builtin,
                $"expected trailing argument {index + 1} ({descriptor.Label}) to have metadata kind {DescribeSequenceBuiltinTrailingArgKind(expectedKind)}, but found {DescribeSequenceBuiltinTrailingArgKind(descriptor.Kind)}");
        }

        return projector(descriptor, args[index]);
    }

    private static EvalResult<Algorithm> ExpectPreparedAlgorithmTrailingArg(
        BuiltinId builtin,
        IReadOnlyList<SequenceBuiltinTrailingArgDescriptor> descriptors,
        IReadOnlyList<PreparedSequenceBuiltinTrailingArg> args,
        int index)
        => ExpectPreparedSequenceBuiltinTrailingArgAt(
            builtin,
            descriptors,
            args,
            index,
            SequenceBuiltinTrailingArgKind.Algorithm,
            (descriptor, arg) => arg is PreparedSequenceBuiltinTrailingArg.AlgorithmArg(var algorithm)
                ? EvalResult<Algorithm>.Ok(algorithm)
                : InternalSequenceBuiltinTrailingArgMetadataError<Algorithm>(
                    builtin,
                    $"prepared trailing argument {index + 1} ({descriptor.Label}) did not match metadata kind {DescribeSequenceBuiltinTrailingArgKind(SequenceBuiltinTrailingArgKind.Algorithm)}"));

    private static EvalResult<decimal> ExpectPreparedWholeNumberTrailingArg(
        BuiltinId builtin,
        IReadOnlyList<SequenceBuiltinTrailingArgDescriptor> descriptors,
        IReadOnlyList<PreparedSequenceBuiltinTrailingArg> args,
        int index)
        => ExpectPreparedSequenceBuiltinTrailingArgAt(
            builtin,
            descriptors,
            args,
            index,
            SequenceBuiltinTrailingArgKind.WholeNumber,
            (descriptor, arg) => arg is PreparedSequenceBuiltinTrailingArg.WholeNumberArg(var value)
                ? EvalResult<decimal>.Ok(value)
                : InternalSequenceBuiltinTrailingArgMetadataError<decimal>(
                    builtin,
                    $"prepared trailing argument {index + 1} ({descriptor.Label}) did not match metadata kind {DescribeSequenceBuiltinTrailingArgKind(SequenceBuiltinTrailingArgKind.WholeNumber)}"));

    private static EvalResult<Result> ExpectPreparedValueTrailingArg(
        BuiltinId builtin,
        IReadOnlyList<SequenceBuiltinTrailingArgDescriptor> descriptors,
        IReadOnlyList<PreparedSequenceBuiltinTrailingArg> args,
        int index)
        => ExpectPreparedSequenceBuiltinTrailingArgAt(
            builtin,
            descriptors,
            args,
            index,
            SequenceBuiltinTrailingArgKind.Value,
            (descriptor, arg) => arg is PreparedSequenceBuiltinTrailingArg.ValueArg(var value)
                ? EvalResult<Result>.Ok(value)
                : InternalSequenceBuiltinTrailingArgMetadataError<Result>(
                    builtin,
                    $"prepared trailing argument {index + 1} ({descriptor.Label}) did not match metadata kind {DescribeSequenceBuiltinTrailingArgKind(SequenceBuiltinTrailingArgKind.Value)}"));

    private static EvalResult<IReadOnlyList<decimal>> ExpectPreparedNumericItems(
        BuiltinId builtin,
        PreparedSequenceBuiltinInput prepared)
    {
        if (prepared.NumericItems is { } numbers)
            return EvalResult<IReadOnlyList<decimal>>.Ok(numbers);

        return new EvalError.WithContext(
            $"internal sequence metadata for {BuiltinDisplayName(builtin)} did not produce numeric items",
            new EvalError.BadArity());
    }

    /// <summary>
    /// Evaluate <c>order</c> over one or more leading sequence arguments by
    /// eagerly sorting the top-level numeric sequence items in ascending order.
    /// Duplicates are preserved, groups are not flattened, strings are
    /// rejected, and empty collections stay empty.
    /// </summary>
    private static EvalResult<CountedResult> EvalOrderCounted(
        IReadOnlyList<decimal> numbers)
    {
        var sorted = numbers.ToList();
        sorted.Sort();
        return EvalResult<CountedResult>.Ok(new CountedResult(
            Result.FromItems(sorted.Select(static value => new Result.Atom(value))),
            sorted.Count));
    }

    /// <summary>
    /// Evaluate <c>orderDesc</c> over one or more leading sequence arguments by
    /// eagerly sorting the top-level numeric sequence items in descending order.
    /// Duplicates are preserved, groups are not flattened, strings are
    /// rejected, and empty collections stay empty.
    /// </summary>
    private static EvalResult<CountedResult> EvalOrderDescCounted(
        IReadOnlyList<decimal> numbers)
    {
        var sorted = numbers.ToList();
        sorted.Sort(static (left, right) => right.CompareTo(left));
        return EvalResult<CountedResult>.Ok(new CountedResult(
            Result.FromItems(sorted.Select(static value => new Result.Atom(value))),
            sorted.Count));
    }

    /// <summary>
    /// Evaluate <c>count</c> over one or more leading sequence arguments by counting the top-level sequence
    /// elements from left to right.
    /// Each atom, string, or grouped value counts as one top-level element;
    /// groups are not flattened or inspected recursively, and empty collections
    /// return <c>0</c>.
    /// Lean: <c>evalCountCounted</c>.
    /// </summary>
    private static EvalResult<CountedResult> EvalCountCounted(
        IReadOnlyList<Result> items)
        => EvalResult<CountedResult>.Ok(new CountedResult(new Result.Atom(items.Count), 1));

    /// <summary>
    /// Evaluate <c>contains</c> over one or more leading sequence arguments by
    /// checking whether any extracted top-level item equals the searched item
    /// under ordinary KatLang value semantics.
    /// Search is top-level only: grouped values compare structurally as grouped
    /// items and are not searched recursively.
    /// </summary>
    private static EvalResult<CountedResult> EvalContainsCounted(
        IReadOnlyList<Result> items,
        Result searchedItem)
        => EvalResult<CountedResult>.Ok(new CountedResult(
            new Result.Atom(items.Any(item => Result.ValueComparer.Equals(item, searchedItem)) ? 1 : 0),
            1));

    /// <summary>
    /// Evaluate <c>distinct</c> over one or more leading sequence arguments by
    /// removing later duplicate top-level items while preserving the original
    /// order of first occurrence. Duplicate detection follows KatLang value
    /// semantics, so atoms compare by numeric value, strings by exact string
    /// value, and groups structurally by grouped contents.
    /// </summary>
    private static EvalResult<CountedResult> EvalDistinctCounted(
        IReadOnlyList<Result> items)
    {
        var distinctItems = new List<Result>(items.Count);
        var seen = new HashSet<Result>(Result.ValueComparer);
        foreach (var item in items)
        {
            if (seen.Add(item))
                distinctItems.Add(item);
        }

        return EvalResult<CountedResult>.Ok(new CountedResult(Result.FromItems(distinctItems), distinctItems.Count));
    }

    /// <summary>
    /// Evaluate <c>first</c> over one or more leading sequence arguments by returning the first top-level
    /// collection element unchanged.
    /// Atoms, strings, and grouped values each count as one top-level element;
    /// grouped values are preserved whole, and the collection must be non-empty.
    /// </summary>
    private static EvalResult<CountedResult> EvalFirstCounted(
        IReadOnlyList<Result> items)
    {
        if (items.Count == 0)
            return new EvalError.BadArity();

        return EvalResult<CountedResult>.Ok(new CountedResult(items[0], 1));
    }

    /// <summary>
    /// Evaluate <c>last</c> over one or more leading sequence arguments by returning the last top-level
    /// collection element unchanged.
    /// Atoms, strings, and grouped values each count as one top-level element;
    /// grouped values are preserved whole, and the collection must be non-empty.
    /// </summary>
    private static EvalResult<CountedResult> EvalLastCounted(
        IReadOnlyList<Result> items)
    {
        if (items.Count == 0)
            return new EvalError.BadArity();

        return EvalResult<CountedResult>.Ok(new CountedResult(items[^1], 1));
    }

    /// <summary>
    /// Evaluate <c>take</c> over one or more leading sequence arguments by
    /// returning the first <paramref name="count"/> extracted top-level items.
    /// Non-positive counts return an empty sequence, oversized counts return
    /// the whole sequence, grouped values stay grouped, and original order is
    /// preserved.
    /// </summary>
    private static EvalResult<CountedResult> EvalTakeCounted(
        IReadOnlyList<Result> items,
        decimal count)
    {
        IReadOnlyList<Result> taken = count <= 0
            ? []
            : items.Take((int)count).ToList();

        return EvalResult<CountedResult>.Ok(new CountedResult(Result.FromItems(taken), taken.Count));
    }

    /// <summary>
    /// Evaluate <c>skip</c> over one or more leading sequence arguments by
    /// returning the extracted top-level items after the first
    /// <paramref name="count"/> items. Non-positive counts leave the sequence
    /// unchanged, oversized counts return an empty sequence, grouped values
    /// stay grouped, and original order is preserved.
    /// </summary>
    private static EvalResult<CountedResult> EvalSkipCounted(
        IReadOnlyList<Result> items,
        decimal count)
    {
        IReadOnlyList<Result> remaining = count <= 0
            ? items.ToList()
            : items.Skip((int)count).ToList();

        return EvalResult<CountedResult>.Ok(new CountedResult(Result.FromItems(remaining), remaining.Count));
    }

    /// <summary>
    /// Evaluate <c>min</c> over one or more leading sequence arguments by comparing top-level sequence
    /// elements from left to right and returning the smallest numeric element.
    /// The collection must be non-empty, and each top-level element must be
    /// exactly one atomic numeric value; groups are not flattened and strings
    /// are rejected.
    /// Lean: <c>evalMinCounted</c>.
    /// </summary>
    private static EvalResult<CountedResult> EvalMinCounted(
        IReadOnlyList<decimal> numbers)
    {
        if (numbers.Count == 0)
            return new EvalError.BadArity();

        var minimum = numbers[0];
        for (var i = 1; i < numbers.Count; i++)
        {
            if (numbers[i] < minimum)
                minimum = numbers[i];
        }

        return EvalResult<CountedResult>.Ok(new CountedResult(new Result.Atom(minimum), 1));
    }

    /// <summary>
    /// Evaluate <c>max</c> over one or more leading sequence arguments by comparing top-level sequence
    /// elements from left to right and returning the largest numeric element.
    /// The collection must be non-empty, and each top-level element must be
    /// exactly one atomic numeric value; groups are not flattened and strings
    /// are rejected.
    /// Lean: <c>evalMaxCounted</c>.
    /// </summary>
    private static EvalResult<CountedResult> EvalMaxCounted(
        IReadOnlyList<decimal> numbers)
    {
        if (numbers.Count == 0)
            return new EvalError.BadArity();

        var maximum = numbers[0];
        for (var i = 1; i < numbers.Count; i++)
        {
            if (numbers[i] > maximum)
                maximum = numbers[i];
        }

        return EvalResult<CountedResult>.Ok(new CountedResult(new Result.Atom(maximum), 1));
    }

    /// <summary>
    /// Evaluate <c>sum</c> over one or more leading sequence arguments by adding the top-level sequence
    /// elements from left to right.
    /// Each element must be exactly one atomic numeric value; groups are not
    /// flattened, strings are rejected, and empty collections return <c>0</c>.
    /// Implementation note: Lean <c>Int</c> is unbounded, but the C# decimal
    /// runtime can overflow; that overflow remains an implementation-only
    /// concern and is reported as <see cref="EvalError.NumericOverflow"/>.
    /// Lean: <c>evalSumCounted</c>.
    /// </summary>
    private static EvalResult<decimal> SumNumbersChecked(IReadOnlyList<decimal> numbers)
    {
        decimal total = 0;
        try
        {
            foreach (var numeric in numbers)
            {
                total = checked(total + numeric);
            }

            return EvalResult<decimal>.Ok(total);
        }
        catch (OverflowException)
        {
            return new EvalError.NumericOverflow();
        }
    }

    /// <summary>
    /// Evaluate <c>sum</c> over one or more leading sequence arguments by
    /// adding the prepared numeric elements from left to right.
    /// Lean: <c>evalSumCounted</c>.
    /// </summary>
    private static EvalResult<CountedResult> EvalSumCounted(IReadOnlyList<decimal> numbers)
    {
        var totalR = SumNumbersChecked(numbers);
        if (totalR.IsError) return totalR.Error;

        return EvalResult<CountedResult>.Ok(new CountedResult(new Result.Atom(totalR.Value), 1));
    }

    /// <summary>
    /// Evaluate <c>avg</c> over one or more leading sequence arguments by averaging the top-level sequence
    /// elements from left to right.
    /// The collection must be non-empty, and each top-level element must be
    /// exactly one atomic numeric value; groups are not flattened and strings
    /// are rejected.
    /// Lean core still defines <c>avg</c> over <c>Int</c>, so the final quotient
    /// uses Lean's floor-style integer semantics even though C# stores runtime
    /// numbers as decimal.
    /// Implementation note: the intermediate decimal accumulation can still
    /// overflow in C#, which is reported as <see cref="EvalError.NumericOverflow"/>.
    /// Lean: <c>evalAvgCounted</c>.
    /// </summary>
    private static EvalResult<CountedResult> EvalAvgCounted(IReadOnlyList<decimal> numbers)
    {
        if (numbers.Count == 0)
            return new EvalError.BadArity();

        var totalR = SumNumbersChecked(numbers);
        if (totalR.IsError) return totalR.Error;

        var average = Math.Floor(totalR.Value / numbers.Count);
        return EvalResult<CountedResult>.Ok(new CountedResult(new Result.Atom(average), 1));
    }

    private static EvalResult<CountedResult> ApplyBuiltinCountedSequence(
        BuiltinId builtin,
        SequenceBuiltinMetadata metadata,
        IReadOnlyList<Algorithm> args,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        EvalResult<CountedResult> WithPreparedFlatItems(
            IReadOnlyList<Algorithm> collectionArgs,
            Func<IReadOnlyList<Result>, EvalResult<CountedResult>> handler)
        {
            var preparedR = EvalPreparedSequenceBuiltinInput(builtin, metadata, collectionArgs, ctx, valEnv);
            if (preparedR.IsError) return preparedR.Error;

            return handler(preparedR.Value.FlattenedItems);
        }

        EvalResult<CountedResult> WithPreparedNumericItems(
            IReadOnlyList<Algorithm> collectionArgs,
            Func<IReadOnlyList<decimal>, EvalResult<CountedResult>> handler)
        {
            var preparedR = EvalPreparedSequenceBuiltinInput(builtin, metadata, collectionArgs, ctx, valEnv);
            if (preparedR.IsError) return preparedR.Error;

            var numbersR = ExpectPreparedNumericItems(builtin, preparedR.Value);
            if (numbersR.IsError) return numbersR.Error;

            return handler(numbersR.Value);
        }

        EvalResult<CountedResult> WithPreparedTrailingArgs(
            IReadOnlyList<Algorithm> trailingArgs,
            Func<IReadOnlyList<PreparedSequenceBuiltinTrailingArg>, EvalResult<CountedResult>> handler)
        {
            var preparedArgsR = EvalPreparedSequenceBuiltinTrailingArgs(
                builtin,
                metadata.TrailingArgs,
                trailingArgs,
                ctx,
                valEnv);
            if (preparedArgsR.IsError) return preparedArgsR.Error;

            return handler(preparedArgsR.Value);
        }

        return ApplySequenceBuiltinCounted(
            builtin,
            metadata,
            args,
            (collectionArgs, trailingArgs) => builtin switch
            {
                BuiltinId.@filter => WithPreparedTrailingArgs(
                    trailingArgs,
                    preparedTrailingArgs =>
                    {
                        var predicateR = ExpectPreparedAlgorithmTrailingArg(
                            builtin,
                            metadata.TrailingArgs,
                            preparedTrailingArgs,
                            0);
                        if (predicateR.IsError) return predicateR.Error;

                        var itemsR = EvalSequenceIterationItems(metadata.CollectionMode, collectionArgs, ctx, valEnv);
                        if (itemsR.IsError) return itemsR.Error;

                        return EvalFilterCounted(itemsR.Value, predicateR.Value, ctx, valEnv);
                    }),
                BuiltinId.@map => WithPreparedTrailingArgs(
                    trailingArgs,
                    preparedTrailingArgs =>
                    {
                        var transformR = ExpectPreparedAlgorithmTrailingArg(
                            builtin,
                            metadata.TrailingArgs,
                            preparedTrailingArgs,
                            0);
                        if (transformR.IsError) return transformR.Error;

                        var itemsR = EvalSequenceIterationItems(metadata.CollectionMode, collectionArgs, ctx, valEnv);
                        if (itemsR.IsError) return itemsR.Error;

                        return EvalMapCounted(itemsR.Value, transformR.Value, ctx, valEnv);
                    }),
                BuiltinId.@order => WithPreparedNumericItems(collectionArgs, EvalOrderCounted),
                BuiltinId.@orderDesc => WithPreparedNumericItems(collectionArgs, EvalOrderDescCounted),
                BuiltinId.@count => WithPreparedFlatItems(collectionArgs, EvalCountCounted),
                BuiltinId.@contains => WithPreparedTrailingArgs(
                    trailingArgs,
                    preparedTrailingArgs =>
                    {
                        var searchedItemR = ExpectPreparedValueTrailingArg(
                            builtin,
                            metadata.TrailingArgs,
                            preparedTrailingArgs,
                            0);
                        if (searchedItemR.IsError) return searchedItemR.Error;

                        return WithPreparedFlatItems(collectionArgs, items => EvalContainsCounted(items, searchedItemR.Value));
                    }),
                BuiltinId.@distinct => WithPreparedFlatItems(collectionArgs, EvalDistinctCounted),
                BuiltinId.@first => WithPreparedFlatItems(collectionArgs, EvalFirstCounted),
                BuiltinId.@last => WithPreparedFlatItems(collectionArgs, EvalLastCounted),
                BuiltinId.@take => WithPreparedTrailingArgs(
                    trailingArgs,
                    preparedTrailingArgs =>
                    {
                        var countR = ExpectPreparedWholeNumberTrailingArg(
                            builtin,
                            metadata.TrailingArgs,
                            preparedTrailingArgs,
                            0);
                        if (countR.IsError) return countR.Error;

                        return WithPreparedFlatItems(collectionArgs, items => EvalTakeCounted(items, countR.Value));
                    }),
                BuiltinId.@skip => WithPreparedTrailingArgs(
                    trailingArgs,
                    preparedTrailingArgs =>
                    {
                        var countR = ExpectPreparedWholeNumberTrailingArg(
                            builtin,
                            metadata.TrailingArgs,
                            preparedTrailingArgs,
                            0);
                        if (countR.IsError) return countR.Error;

                        return WithPreparedFlatItems(collectionArgs, items => EvalSkipCounted(items, countR.Value));
                    }),
                BuiltinId.@min => WithPreparedNumericItems(collectionArgs, EvalMinCounted),
                BuiltinId.@max => WithPreparedNumericItems(collectionArgs, EvalMaxCounted),
                BuiltinId.@sum => WithPreparedNumericItems(collectionArgs, EvalSumCounted),
                BuiltinId.@avg => WithPreparedNumericItems(collectionArgs, EvalAvgCounted),
                BuiltinId.@reduce => WithPreparedTrailingArgs(
                    trailingArgs,
                    preparedTrailingArgs =>
                    {
                        var stepR = ExpectPreparedAlgorithmTrailingArg(
                            builtin,
                            metadata.TrailingArgs,
                            preparedTrailingArgs,
                            0);
                        if (stepR.IsError) return stepR.Error;

                        var initialR = ExpectPreparedAlgorithmTrailingArg(
                            builtin,
                            metadata.TrailingArgs,
                            preparedTrailingArgs,
                            1);
                        if (initialR.IsError) return initialR.Error;

                        var itemsR = EvalSequenceIterationItems(metadata.CollectionMode, collectionArgs, ctx, valEnv);
                        if (itemsR.IsError) return itemsR.Error;

                        return EvalReduceCounted(itemsR.Value, stepR.Value, initialR.Value, ctx, valEnv);
                    }),
                _ => WrongBuiltinArity(builtin, args.Count),
            });
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
        if (GetSequenceBuiltinMetadata(builtin) is { } metadata)
            return ApplyBuiltinCountedSequence(builtin, metadata, args, ctx, valEnv);

        switch (builtin, args.Count)
        {
            case (BuiltinId.@if, 3):
            {
                var condR = EvalAlgOutput(args[0], ctx, valEnv);
                if (condR.IsError) return condR.Error;
                var truth = condR.Value.TruthValue();
                if (truth is null) return new EvalError.BadArity();
                return truth.Value
                    ? EvalAlgOutputCounted(args[1], ctx, valEnv)
                    : EvalAlgOutputCounted(args[2], ctx, valEnv);
            }

            case (BuiltinId.@while, 2):
            {
                var initR = EvalAlgOutput(args[1], ctx, valEnv);
                if (initR.IsError) return initR.Error;
                var loopR = WhileLoop(args[0], initR.Value, ctx, valEnv);
                if (loopR.IsError) return loopR.Error;
                return EvalResult<CountedResult>.Ok(new CountedResult(loopR.Value, loopR.Value.ValueCount()));
            }

            case (BuiltinId.@repeat, 3):
            {
                var countR = EvalAlgOutput(args[1], ctx, valEnv);
                if (countR.IsError) return countR.Error;
                var nR = ExpectWholeInt(countR.Value, "Repeat count");
                if (nR.IsError) return nR.Error;
                var n = (long)nR.Value;
                if (n < 0) return new EvalError.IllegalInEval("Repeat count must be >= 0");

                var initR = EvalAlgOutput(args[2], ctx, valEnv);
                if (initR.IsError) return initR.Error;
                var loopR = RepeatLoop(args[0], n, initR.Value, ctx, valEnv);
                if (loopR.IsError) return loopR.Error;
                return EvalResult<CountedResult>.Ok(new CountedResult(loopR.Value, loopR.Value.ValueCount()));
            }

            case (BuiltinId.@atoms, 1):
            {
                var atomsR = EvalAlgOutput(args[0], ctx, valEnv);
                if (atomsR.IsError) return atomsR.Error;
                var atoms = atomsR.Value.ToAtoms();
                var value = Result.FromItems(atoms.Select(n => new Result.Atom(n)));
                return EvalResult<CountedResult>.Ok(new CountedResult(value, atoms.Count));
            }

            case (BuiltinId.@range, 2):
            {
                var startR = EvalAlgOutput(args[0], ctx, valEnv);
                if (startR.IsError) return startR.Error;
                var startIntR = ExpectWholeInt(startR.Value, "range start");
                if (startIntR.IsError) return startIntR.Error;

                var stopR = EvalAlgOutput(args[1], ctx, valEnv);
                if (stopR.IsError) return stopR.Error;
                var stopIntR = ExpectWholeInt(stopR.Value, "range stop");
                if (stopIntR.IsError) return stopIntR.Error;

                var value = BuildInclusiveRange(startIntR.Value, stopIntR.Value);
                return EvalResult<CountedResult>.Ok(new CountedResult(value, value.ToAtoms().Count));
            }

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

    private static readonly Algorithm.User MathAlgorithm = BuiltinRegistry.CreateMathAlgorithm(MathAlgorithmFlavor.Runtime);

    /// <summary>
    /// Prelude algorithm providing builtin operations in scope by default.
    /// Lean: preludeAlg. Builtins are injected into the initial call stack.
    /// All builtins and Math are public for use in opened contexts.
    /// </summary>
    private static readonly Algorithm.User PreludeAlg = BuiltinRegistry.CreateRuntimePreludeAlgorithm(MathAlgorithm);

    private static SequenceBuiltinMetadata? GetSequenceBuiltinMetadata(BuiltinId builtin)
        => BuiltinRegistry.TryGetSequenceMetadata(builtin, out var metadata) ? metadata : null;

    private static string BuiltinDisplayName(BuiltinId builtin)
        => BuiltinRegistry.GetBuiltin(builtin).Name;

    /// <summary>Lean: builtinAcceptsArity. Fixed-arity builtins stay exact; sequence builtins accept one or more leading sequence args.</summary>
    private static bool BuiltinAcceptsArity(BuiltinId builtin, int argumentCount)
        => BuiltinRegistry.GetBuiltin(builtin).AcceptsArity(argumentCount);

    /// <summary>Lean: builtinArityDesc. Human-readable expected arity for error messages.</summary>
    private static string BuiltinArityDesc(BuiltinId builtin)
        => BuiltinRegistry.GetBuiltin(builtin).DescribeArity();

    private static EvalError WrongBuiltinArity(BuiltinId builtin, int actualCount)
    {
        var descriptor = BuiltinRegistry.GetBuiltin(builtin);

        return builtin switch
        {
            BuiltinId.@if => new EvalError.WithContext(
                $"Builtin '{descriptor.Name}' expects {descriptor.FixedArity} arguments: {string.Join(", ", descriptor.PlainParameterNames)}. Got {actualCount}.",
                new EvalError.ArityMismatch(descriptor.FixedArity ?? 0, actualCount)),
            _ => new EvalError.WithContext(
                $"expected {BuiltinArityDesc(builtin)} arguments",
                new EvalError.ArityMismatch(0, actualCount)),
        };
    }

    // ── Dot-call helpers ───────────────────────────────────────────────────

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

        // First check if property exists at all so ownership still wins over opens.
        var prop = LookupPropBinding(targetResult.Value, propName);
        if (prop is not null)
        {
            if (prop.Value is Algorithm.Builtin)
                return new EvalError.IllegalInOpen(
                    $"builtin not allowed in open: {OpenExprName(target)}.{propName}");

            if (!IsExported(prop))
                return new EvalError.LocalOnlyProperty(OpenExprName(target), propName, prop.Exposure);

            // Property exists; check if it's public
            if (prop.IsPublic)
                return EvalResult<Algorithm>.Ok(prop.Value); // no wiring (pure resolution)

            return new EvalError.NotPublicProperty(OpenExprName(target), propName);
        }
        if (ConditionalBranchesDefineProperty(targetResult.Value, propName))
            return new EvalError.LocalOnlyProperty(OpenExprName(target), propName, PropertyExposure.LocalOnlyConditionalAlgorithm);

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
                return ResolveNamedAlgorithm(name, expr.Span, ctx);

            case Expr.DotCall:
            {
                // Lean: resolveAlg (.dotCall o n args) — lift to wrapper algorithm;
                // evalDotCall handles all semantics (builtin property special cases, structural lookup, lexical fallback)
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
        if (GetSequenceBuiltinMetadata(builtin) is { } metadata)
        {
            var countedR = ApplyBuiltinCountedSequence(builtin, metadata, args, ctx, valEnv);
            if (countedR.IsError) return countedR.Error;
            return EvalResult<Result>.Ok(countedR.Value.Value);
        }

        switch (builtin, args.Count)
        {
            // if(cond, thenBranch, elseBranch): standard 3-arg conditional.
            case (BuiltinId.@if, 3):
            {
                var condR = EvalAlgOutput(args[0], ctx, valEnv);
                if (condR.IsError) return condR.Error;
                var truth = condR.Value.TruthValue();
                if (truth is null) return new EvalError.BadArity();
                return truth.Value
                    ? EvalAlgOutput(args[1], ctx, valEnv)
                    : EvalAlgOutput(args[2], ctx, valEnv);
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
                var nR = ExpectWholeInt(countR.Value, "Repeat count");
                if (nR.IsError) return nR.Error;
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

            // range(start, stop) — inclusive integer sequence, ascending or descending.
            case (BuiltinId.@range, 2):
            {
                var startR = EvalAlgOutput(args[0], ctx, valEnv);
                if (startR.IsError) return startR.Error;
                var startIntR = ExpectWholeInt(startR.Value, "range start");
                if (startIntR.IsError) return startIntR.Error;

                var stopR = EvalAlgOutput(args[1], ctx, valEnv);
                if (stopR.IsError) return stopR.Error;
                var stopIntR = ExpectWholeInt(stopR.Value, "range stop");
                if (stopIntR.IsError) return stopIntR.Error;

                return EvalResult<Result>.Ok(BuildInclusiveRange(startIntR.Value, stopIntR.Value));
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
                // 1. Counted callback-param env (projected higher-order item meaning)
                // 2. ValEnv (ordinary value meaning)
                // 3. AlgEnv fallback (algorithm meaning):
                //    - 0-param algorithm → auto-evaluate (thunk semantics)
                //    - multi-param algorithm → arityMismatch (needs explicit call)
                var counted = LookupCountedParam(ctx.CountedParamEnv, name);
                if (counted is not null) return EvalResult<Result>.Ok(counted.Value.Value);

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

            case Expr.Combine:
            {
                var combineR = EvalCombineCounted(expr, ctx, valEnv);
                return combineR.IsError
                    ? combineR.Error
                    : EvalResult<Result>.Ok(combineR.Value.Value);
            }

            case Expr.Block(var alg):
            {
                var wired = WireToCaller(ctx, alg);
                if (wired.Params.Count == 0)
                    return WithSpan(expr.Span ?? FirstSpan(wired.Output), EvalAlgOutput(wired, ctx, valEnv));
                var blockSpan = expr.Span ?? FirstSpan(wired.Output);
                return MissingImplicitArguments<Result>(wired.Params, blockSpan);
            }

            case Expr.Resolve(var name):
            {
                if (ctx.CallStack.Count == 0)
                    return new EvalError.UnknownName(name) { Span = expr.Span };

                var resolvedR = LookupLexical(ctx.CallStack[0], name, ctx);
                if (resolvedR.IsError)
                {
                    var err = resolvedR.Error;
                    return err.Span is null ? err with { Span = expr.Span } : err;
                }

                if (resolvedR.Value.ResolvedAlgorithm.Params.Count != 0)
                {
                    return WithSpan<Result>(
                        expr.Span,
                        new EvalError.WithContext(
                            CtxProperty(name),
                            new EvalError.ArityMismatch(resolvedR.Value.ResolvedAlgorithm.Params.Count, 0)));
                }

                return WithPropertyContextOnMissingOutput(name, expr.Span,
                    EvalZeroArgPropertyAccess(resolvedR.Value, ctx, valEnv));
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
                var selectionR = EvalIndexSelectionCounted(target, selector, expr.Span, ctx, valEnv);
                return selectionR.IsError
                    ? selectionR.Error
                    : EvalResult<Result>.Ok(selectionR.Value.Value);
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
                var counted = LookupCountedParam(ctx.CountedParamEnv, name);
                if (counted is not null)
                    return EvalResult<CountedResult>.Ok(counted.Value);

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

            case Expr.Combine:
                return EvalCombineCounted(expr, ctx, valEnv);

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
                return MissingImplicitArguments<CountedResult>(wired.Params, blockSpan);
            }

            case Expr.Resolve(var name):
            {
                if (ctx.CallStack.Count == 0)
                    return new EvalError.UnknownName(name) { Span = expr.Span };

                var resolvedR = LookupLexical(ctx.CallStack[0], name, ctx);
                if (resolvedR.IsError)
                {
                    var err = resolvedR.Error;
                    return err.Span is null ? err with { Span = expr.Span } : err;
                }

                if (resolvedR.Value.ResolvedAlgorithm.Params.Count != 0)
                {
                    return WithSpan<CountedResult>(
                        expr.Span,
                        new EvalError.WithContext(
                            CtxProperty(name),
                            new EvalError.ArityMismatch(resolvedR.Value.ResolvedAlgorithm.Params.Count, 0)));
                }

                return WithPropertyContextOnMissingOutput(name, expr.Span,
                    EvalZeroArgPropertyAccessCounted(resolvedR.Value, ctx, valEnv));
            }

            case Expr.DotCall(var dotTarget, var dotName, var dotArgs):
                return WithSpan(expr.Span, WithCtx(CtxDotCall(dotTarget, dotName),
                    EvalDotCallCounted(dotTarget, dotName, dotArgs, ctx, valEnv)));

            case Expr.Call(var func, var argsAlg):
                return WithSpan(expr.Span,
                    EvalCallCountedExpr(func, argsAlg, ctx, valEnv));

            case Expr.Index(var target, var selector):
                return WithSpan(expr.Span,
                    EvalIndexSelectionCounted(target, selector, expr.Span, ctx, valEnv));

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
    /// <summary>
    /// Treat simple zero-parameter inline block expressions uniformly as
    /// value/output structures in argument position.
    /// This rule is shared by builtin lazy-argument preparation and higher-order
    /// probing; callability is not inferred from output count, so both
    /// <c>{123}</c> and <c>{1, 2}</c> stay on the value side. Blocks with
    /// parameters, properties, or opens may still resolve as algorithms.
    /// </summary>
    private static bool ShouldWrapArgExprAsValue(Expr expr) => expr switch
    {
        Expr.Block(var algorithm)
            when algorithm.Params.Count == 0
                && algorithm.Opens.Count == 0
                && algorithm.Properties.Count == 0 => true,
        _ => false,
    };

    private static Algorithm WrapArgExprAsValue(Expr expr, EvalCtx ctx)
        => WireToCaller(
            ctx,
            new Algorithm.User(
                Parent: null,
                Params: [],
                Opens: [],
                Properties: [],
                Output: [expr]));

    private static EvalResult<IReadOnlyList<Algorithm>> ResolveArgAlgs(
        Algorithm argsAlg, EvalCtx ctx)
    {
        var result = new List<Algorithm>(argsAlg.Output.Count);
        foreach (var argExpr in argsAlg.Output)
        {
            if (ShouldWrapArgExprAsValue(argExpr))
            {
                result.Add(WrapArgExprAsValue(argExpr, ctx));
                continue;
            }

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
    /// Simple zero-parameter inline blocks are intentionally treated as
    /// value/output structures here, regardless of whether they emit one value
    /// or many, so higher-order probing never grants them callable AlgEnv
    /// bindings based on output count.
    /// Lean: tryResolveArgAlgs.
    /// </summary>
    private static EvalResult<IReadOnlyList<Algorithm?>> TryResolveArgAlgs(
        Algorithm argsAlg, EvalCtx ctx)
    {
        var result = new List<Algorithm?>(argsAlg.Output.Count);
        foreach (var argExpr in argsAlg.Output)
        {
            if (ShouldWrapArgExprAsValue(argExpr))
            {
                result.Add(null);
                continue;
            }

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

        if (callee.HasDuplicateBranchPatterns())
            return new EvalError.DuplicateBranchPattern();

        var match = MatchCallBranches(callee.Branches, argResults);
        if (match is null)
            return new EvalError.NoMatchingBranch(calleeName);

        var (branch, bindings) = match.Value;
        var wiredBody = ChildOf(callee, branch.Body);
        var newCtx = ctx.Push(callee);
        var newEnv = Concat(bindings, valEnv);
        return EvalAlgOutput(wiredBody, newCtx, newEnv);
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

        if (callee.HasDuplicateBranchPatterns())
            return new EvalError.DuplicateBranchPattern();

        var match = MatchCallBranches(callee.Branches, argResults);
        if (match is null)
            return new EvalError.NoMatchingBranch(calleeName);

        var (branch, bindings) = match.Value;
        var wiredBody = ChildOf(callee, branch.Body);
        var newCtx = ctx.Push(callee);
        var newEnv = Concat(bindings, valEnv);
        return EvalAlgOutputCounted(wiredBody, newCtx, newEnv);
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
    /// If both fail, the eager-evaluation error is propagated. Zero-parameter
    /// inline block arguments are excluded from the AlgEnv side by
    /// <c>TryResolveArgAlgs</c>; they remain ordinary value/output structures
    /// regardless of output count.
    ///
    /// Argument expressions may be fewer than parameters because the final
    /// explicit eager value may unpack to multiple positional results, but an
    /// explicit argument list may not contain more expressions than the callee
    /// has parameters. Earlier explicit argument positions remain distinct on
    /// the eager value side even if some later arguments bind only through
    /// AlgEnv.
    /// </summary>
    private static EvalResult<Result> EvalUserCall(
        Algorithm callee, Algorithm args,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var wiredArgs = WireToCaller(ctx, args);
        var argExprs = wiredArgs.Output;

        if (callee.Output.Count == 0)
            return new EvalError.MissingOutput();

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

            var isFinalExplicitArg = i == argExprs.Count - 1;
            var evalR = Eval(argExprs[i], argEvalCtx, valEnv);
            if (evalR.IsOk)
            {
                if (isFinalExplicitArg)
                {
                    var remainingParams = paramCount - i;
                    if (remainingParams > 1)
                    {
                        for (var paramIndex = i; paramIndex < paramCount; paramIndex++)
                            valueParams.Add(callee.Params[paramIndex]);

                        foreach (var unpacked in UnpackArgs(evalR.Value))
                            valueResults.Add(unpacked);
                    }
                    else
                    {
                        valueParams.Add(callee.Params[i]);
                        valueResults.Add(evalR.Value);
                    }

                    break;
                }

                valueParams.Add(callee.Params[i]);
                valueResults.Add(evalR.Value);
            }
            else if (i < maybeAlgs.Count && maybeAlgs[i] is not null)
            {
                // Has algorithm binding → skip value binding for this param
                if (isFinalExplicitArg)
                {
                    for (var paramIndex = i + 1; paramIndex < paramCount; paramIndex++)
                        valueParams.Add(callee.Params[paramIndex]);

                    break;
                }
            }
            else
            {
                // No algorithm → propagate eval error
                return evalR.Error;
            }
        }

        var argEnvR = BindParams(valueParams, valueResults);
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

        if (callee.Output.Count == 0)
            return new EvalError.MissingOutput();

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

            var isFinalExplicitArg = i == argExprs.Count - 1;
            var evalR = Eval(argExprs[i], argEvalCtx, valEnv);
            if (evalR.IsOk)
            {
                if (isFinalExplicitArg)
                {
                    var remainingParams = paramCount - i;
                    if (remainingParams > 1)
                    {
                        for (var paramIndex = i; paramIndex < paramCount; paramIndex++)
                            valueParams.Add(callee.Params[paramIndex]);

                        foreach (var unpacked in UnpackArgs(evalR.Value))
                            valueResults.Add(unpacked);
                    }
                    else
                    {
                        valueParams.Add(callee.Params[i]);
                        valueResults.Add(evalR.Value);
                    }

                    break;
                }

                valueParams.Add(callee.Params[i]);
                valueResults.Add(evalR.Value);
            }
            else if (i < maybeAlgs.Count && maybeAlgs[i] is not null)
            {
                if (isFinalExplicitArg)
                {
                    for (var paramIndex = i + 1; paramIndex < paramCount; paramIndex++)
                        valueParams.Add(callee.Params[paramIndex]);

                    break;
                }
            }
            else
            {
                return evalR.Error;
            }
        }

        var argEnvR = BindParams(valueParams, valueResults);
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
    /// 1. Value-based intrinsic (string) → evaluate target, convert numeric result to string
    /// 2. Structural property found (navigation-only):
    ///    - No args + 0-param → value access
    ///    - No args + has params → arity mismatch error
    ///    - Has args → delegate to EvalUserCall (dual-view binding, no receiver injection)
    /// 3. No property → lexical fallback (receiver injection via callLexicalWithReceiver)
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

        // Value-based intrinsic: "string" — evaluate algorithm output and convert
        if (name == "string")
        {
            var val = EvalAlgOutput(targetAlg, ctx, valEnv);
            if (val.IsError) return val.Error;
            return ResultToString(val.Value);
        }

        // Structural: property of target (exported only; private export remains accessible)
        var prop = LookupPropBinding(targetAlg, name);
        if (prop is not null)
        {
            if (!IsExported(prop))
                return new EvalError.LocalOnlyProperty(OpenExprName(target), name, prop.Exposure);

            var wired = ChildOf(targetAlg, prop.Value);
            if (argsOpt is null)
            {
                var simpleCallee = TryGetFlatBinderUserEquivalent(wired);
                if (simpleCallee is not null)
                    return new EvalError.ArityMismatch(simpleCallee.Params.Count, 0);

                if (wired is Algorithm.Conditional)
                    return new EvalError.NoMatchingBranch(name);

                // No args: 0-param → value access, has params → arity error
                if (wired.Params.Count == 0)
                    return EvalZeroArgPropertyAccess(targetAlg, prop, ZeroArgPropertyAccessKind.Structural, wired, ctx, valEnv);
                return new EvalError.ArityMismatch(wired.Params.Count, 0);
            }

            return EvalResolvedCall(wired, argsOpt, ctx, valEnv, name);
        }

        if (ConditionalBranchesDefineProperty(targetAlg, name))
            return new EvalError.LocalOnlyProperty(OpenExprName(target), name, PropertyExposure.LocalOnlyConditionalAlgorithm);

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
    private readonly record struct SequenceBuiltinDotCall(
        BuiltinId Builtin,
        IReadOnlyList<Algorithm> Args);

    /// <summary>
    /// Sequence builtins in dot-call form consume the receiver's own counted
    /// top-level items.
    /// A direct inline receiver block first exposes its inner algorithm output
    /// count, which strips exactly one receiver-scoping block layer for forms
    /// like <c>(1, 2, 3).take(2)</c> while still keeping
    /// <c>((1, 2, 3)).take(2)</c> and named grouped helpers grouped.
    /// The resulting counted top-level items are then reified as one ordinary
    /// leading argument per item, and any extra dot-call arguments still
    /// follow the plain-call argument path.
    /// This keeps plain-call boundary preservation unchanged while making
    /// <c>receiver.builtin(...)</c> operate on the same top-level collection
    /// that <c>receiver:i</c> and higher-order callback projection observe.
    /// </summary>
    private static EvalResult<CountedResult> EvalSequenceBuiltinDotReceiverCounted(
        Expr receiver,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        if (receiver is Expr.Block(var algorithm))
        {
            var wired = WireToCaller(ctx, algorithm);
            if (wired.Params.Count == 0)
                return WithSpan(receiver.Span ?? FirstSpan(wired.Output), EvalAlgOutputCounted(wired, ctx, valEnv));
        }

        return EvalCounted(receiver, ctx, valEnv);
    }

    private static EvalResult<IReadOnlyList<Algorithm>> SequenceBuiltinDotReceiverArgs(
        Expr receiver,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var receiverR = EvalSequenceBuiltinDotReceiverCounted(receiver, ctx, valEnv);
        if (receiverR.IsError) return receiverR.Error;

        return EvalResult<IReadOnlyList<Algorithm>>.Ok(
            CountedTopLevelItemAlgorithms(receiverR.Value));
    }

    private static EvalResult<SequenceBuiltinDotCall?> TryBuildSequenceBuiltinDotCall(
        string name,
        Expr receiver,
        Algorithm? extraArgs,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var calleeR = ResolveNamedAlgorithm(name, span: null, ctx);
        if (calleeR.IsError
            || calleeR.Value is not Algorithm.Builtin(var builtin)
            || GetSequenceBuiltinMetadata(builtin) is null)
        {
            return EvalResult<SequenceBuiltinDotCall?>.Ok(null);
        }

        var receiverArgAlgsR = SequenceBuiltinDotReceiverArgs(receiver, ctx, valEnv);
        if (receiverArgAlgsR.IsError) return receiverArgAlgsR.Error;

        var argAlgs = new List<Algorithm>(receiverArgAlgsR.Value);

        if (extraArgs is not null)
        {
            var extraArgAlgsR = ResolveArgAlgs(extraArgs, ctx);
            if (extraArgAlgsR.IsError) return extraArgAlgsR.Error;
            argAlgs.AddRange(extraArgAlgsR.Value);
        }

        return EvalResult<SequenceBuiltinDotCall?>.Ok(
            new SequenceBuiltinDotCall(builtin, argAlgs));
    }

    private static EvalResult<Result> CallLexicalWithReceiver(
        string name, Expr receiver, Algorithm? extraArgs,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var sequenceDotCallR = TryBuildSequenceBuiltinDotCall(name, receiver, extraArgs, ctx, valEnv);
        if (sequenceDotCallR.IsError) return sequenceDotCallR.Error;
        if (sequenceDotCallR.Value is { } sequenceDotCall)
            return ApplyBuiltin(sequenceDotCall.Builtin, sequenceDotCall.Args, ctx, valEnv);

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

        var calleeR = ResolveNamedAlgorithm(name, span: null, ctx);
        if (calleeR.IsError) return calleeR.Error;
        return EvalResolvedCall(calleeR.Value, combinedArgs, ctx, valEnv, name);
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

        if (name == "string")
        {
            var val = EvalAlgOutput(targetAlg, ctx, valEnv);
            if (val.IsError) return val.Error;
            var outR = ResultToString(val.Value);
            if (outR.IsError) return outR.Error;
            return EvalResult<CountedResult>.Ok(new CountedResult(outR.Value, outR.Value.ValueCount()));
        }

        var prop = LookupPropBinding(targetAlg, name);
        if (prop is not null)
        {
            if (!IsExported(prop))
                return new EvalError.LocalOnlyProperty(OpenExprName(target), name, prop.Exposure);

            var wired = ChildOf(targetAlg, prop.Value);
            if (argsOpt is null)
            {
                var simpleCallee = TryGetFlatBinderUserEquivalent(wired);
                if (simpleCallee is not null)
                    return new EvalError.ArityMismatch(simpleCallee.Params.Count, 0);

                if (wired is Algorithm.Conditional)
                    return new EvalError.NoMatchingBranch(name);

                if (wired.Params.Count == 0)
                    return EvalZeroArgPropertyAccessCounted(targetAlg, prop, ZeroArgPropertyAccessKind.CountedStructural, wired, ctx, valEnv);
                return new EvalError.ArityMismatch(wired.Params.Count, 0);
            }

            return EvalResolvedCallCounted(wired, argsOpt, ctx, valEnv, name);
        }

        if (ConditionalBranchesDefineProperty(targetAlg, name))
            return new EvalError.LocalOnlyProperty(OpenExprName(target), name, PropertyExposure.LocalOnlyConditionalAlgorithm);

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
        var sequenceDotCallR = TryBuildSequenceBuiltinDotCall(name, receiver, extraArgs, ctx, valEnv);
        if (sequenceDotCallR.IsError) return sequenceDotCallR.Error;
        if (sequenceDotCallR.Value is { } sequenceDotCall)
            return ApplyBuiltinCounted(sequenceDotCall.Builtin, sequenceDotCall.Args, ctx, valEnv);

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

        var calleeR = ResolveNamedAlgorithm(name, span: null, ctx);
        if (calleeR.IsError) return calleeR.Error;
        return EvalResolvedCallCounted(calleeR.Value, combinedArgs, ctx, valEnv, name);
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
        => Run(expr, new RunScopedZeroArgPropertyResultCache());

    internal static EvalResult<Result> Run(
        Expr expr,
        IZeroArgPropertyResultCache zeroArgPropertyResultCache)
    {
        if (AlgorithmValidation.FindFirstExplicitParameterOutputViolation(expr) is { } violation)
            return new EvalError.ExplicitParametersRequireOutput() { Span = violation.Span };

        ArgumentNullException.ThrowIfNull(zeroArgPropertyResultCache);

        var ctx = new EvalCtx([PreludeAlg], [], [], zeroArgPropertyResultCache);
        return expr is Expr.Block(var alg)
            ? EvalRootProgram(alg, expr.Span, ctx)
            : Eval(expr, ctx, []);
    }

    private static EvalResult<Result> EvalRootProgram(Algorithm alg, SourceSpan? span, EvalCtx ctx)
    {
        var wired = WireToCaller(ctx, alg);
        if (wired.Params.Count == 0)
            return EvalProgramOutput(wired, ctx, []);

        var blockSpan = span ?? FirstSpan(wired.Output);
        return MissingImplicitArguments<Result>(wired.Params, blockSpan);
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
        => new PrependedReadOnlyList<T>(item, list);

    private sealed class PrependedReadOnlyList<T> : IReadOnlyList<T>
    {
        private readonly T _head;
        private readonly IReadOnlyList<T> _tail;

        public PrependedReadOnlyList(T head, IReadOnlyList<T> tail)
        {
            _head = head;
            _tail = tail;
            Count = tail.Count + 1;
        }

        public int Count { get; }

        public T this[int index]
            => index switch
            {
                0 => _head,
                > 0 when index <= _tail.Count => _tail[index - 1],
                _ => throw new ArgumentOutOfRangeException(nameof(index)),
            };

        public IEnumerator<T> GetEnumerator()
        {
            yield return _head;
            foreach (var item in _tail)
                yield return item;
        }

        IEnumerator IEnumerable.GetEnumerator()
            => GetEnumerator();
    }

    private static IReadOnlyList<T> Concat<T>(IReadOnlyList<T> a, IReadOnlyList<T> b)
    {
        var result = new List<T>(a.Count + b.Count);
        result.AddRange(a);
        result.AddRange(b);
        return result;
    }
}
