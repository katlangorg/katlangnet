using System.Collections;
using System.Runtime.CompilerServices;
using KatLang.Evaluation.Caching;
using KatLang.Optimizations.Loops;
using KatLang.Optimizations.Sequences;
using KatLang.Runtime;

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
    internal readonly record struct EvalCtx(
        IReadOnlyList<Algorithm> CallStack,
        IReadOnlyList<(string Name, Algorithm Value)> AlgEnv,
        IReadOnlyList<(string Name, CountedResult Value)> CountedParamEnv,
        IZeroArgPropertyResultCache ZeroArgPropertyResultCache,
        bool EnableLoopOptimization,
        LoopOptimizationDiagnostics? LoopDiagnostics,
        bool EnableSequencePipelineOptimization,
        SequencePipelineDiagnostics? SequenceDiagnostics)
    {
        public static readonly EvalCtx Empty = new([], [], [], UncachedZeroArgPropertyResultCache.Instance, true, null, true, null);

        /// <summary>Lean: EvalCtx.push — prepend an algorithm to the call stack.</summary>
        public EvalCtx Push(Algorithm alg)
            => new(
                Prepend(alg, CallStack),
                AlgEnv,
                CountedParamEnv,
                ZeroArgPropertyResultCache,
                EnableLoopOptimization,
                LoopDiagnostics,
                EnableSequencePipelineOptimization,
                SequenceDiagnostics);

        /// <summary>Lean: EvalCtx.head? — first algorithm in the call stack.</summary>
        public Algorithm? Head => CallStack.Count > 0 ? CallStack[0] : null;

        /// <summary>Lean: EvalCtx.withAlgEnv — replace the algorithm environment.</summary>
        public EvalCtx WithAlgEnv(IReadOnlyList<(string, Algorithm)> algEnv)
            => new(
                CallStack,
                algEnv,
                CountedParamEnv,
                ZeroArgPropertyResultCache,
                EnableLoopOptimization,
                LoopDiagnostics,
                EnableSequencePipelineOptimization,
                SequenceDiagnostics);

        /// <summary>Replace the counted callback-parameter environment.</summary>
        public EvalCtx WithCountedParamEnv(IReadOnlyList<(string, CountedResult)> countedParamEnv)
            => new(
                CallStack,
                AlgEnv,
                countedParamEnv,
                ZeroArgPropertyResultCache,
                EnableLoopOptimization,
                LoopDiagnostics,
                EnableSequencePipelineOptimization,
                SequenceDiagnostics);

        /// <summary>Replace the zero-argument property cache for a scoped evaluation subtree.</summary>
        public EvalCtx WithZeroArgPropertyResultCache(IZeroArgPropertyResultCache zeroArgPropertyResultCache)
            => new(
                CallStack,
                AlgEnv,
                CountedParamEnv,
                zeroArgPropertyResultCache,
                EnableLoopOptimization,
                LoopDiagnostics,
                EnableSequencePipelineOptimization,
                SequenceDiagnostics);
    }

    // ── Environment types ────────────────────────────────────────────────────

    private static object ValueEnvironmentCacheIdentity(IReadOnlyList<(string, Result)> valEnv)
        => valEnv is IValueEnvironmentCacheIdentityProvider provider
            ? provider.CacheIdentity
            : valEnv;

    /// <summary>Value environment: maps parameter names to results. Lean: ValEnv.lookup (Option).</summary>
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

    internal static IReadOnlyList<(string Name, CountedResult Value)> ShadowCountedParamEnv(
        IReadOnlyList<(string Name, CountedResult Value)> env,
        IEnumerable<string> shadowedNames)
    {
        if (env.Count == 0)
            return env;

        var shadowed = new HashSet<string>(shadowedNames);
        if (shadowed.Count == 0)
            return env;

        var filtered = new List<(string Name, CountedResult Value)>(env.Count);
        var removedAny = false;
        foreach (var binding in env)
        {
            if (shadowed.Contains(binding.Name))
            {
                removedAny = true;
                continue;
            }

            filtered.Add(binding);
        }

        return removedAny ? filtered : env;
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

    /// <summary>Best-effort algorithm path for internal diagnostics.</summary>
    internal static string? TryGetAlgorithmPath(Algorithm algorithm)
    {
        if (algorithm.Parent is not { } scope)
            return null;

        var name = TryGetAlgorithmNameInScope(algorithm, scope);
        if (name is null)
            return null;

        var owner = TryGetScopeOwnerAlgorithm(scope);
        var ownerPath = owner is null || ReferenceEquals(owner, algorithm)
            ? null
            : TryGetAlgorithmPath(owner);
        return ownerPath is null ? name : $"{ownerPath}.{name}";
    }

    private static string? TryGetAlgorithmNameInScope(Algorithm algorithm, ScopeCtx scope)
    {
        foreach (var property in scope.Properties)
        {
            if (WithParent(property.Value, scope).Equals(algorithm))
                return property.Name;
        }

        return null;
    }

    /// <summary>Lean: Algorithm.childOf â€” wire a child algorithm to its parent's scope context.</summary>
    private static Algorithm ChildOf(Algorithm parent, Algorithm child)
        => WithParent(child, AsScopeCtx(parent));

    /// <summary>
    /// Create a temporary algorithm from a ScopeCtx for open resolution.
    /// Lean: Algorithm.forOpens.
    /// </summary>
    private static Algorithm ForOpens(ScopeCtx sc)
        => new Algorithm.User(
            Parent: sc, Parameters: [], Opens: sc.Opens,
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
    internal static string ExprKind(Expr e) => e switch
    {
        Expr.Param => "param",
        Expr.Num => "num",
        Expr.StringLiteral => "stringLiteral",
        Expr.Unary => "unary",
        Expr.Binary => "binary",
        Expr.Index => "index",
        Expr.SequenceConstruct => "sequenceConstruct",
        Expr.EmptySequence => "emptySequence",
        Expr.SequenceSpread => "spread",
        Expr.ListLiteral => "listLiteral",
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
        Expr.Block or Expr.Resolve or Expr.DotCall(_, _, null);

    /// <summary>
    /// Extract a descriptive name from an open expression for error messages.
    /// Lean: openExprName.
    /// </summary>
    internal static string OpenExprName(Expr e) => e switch
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
        // Diagnostic expression names use KatLang source syntax: indexing is
        // postfix `target:selector`, never `target[selector]` (`[...]` is exact
        // list literal syntax, so bracket text would read back as adjacency).
        Expr.Index(var target, var selector)
            => $"{OpenExprIndexTargetName(target)}:{OpenExprIndexSelectorName(selector)}",
        Expr.DotCall(var o, var n, var argsOpt) => argsOpt is null
            ? OpenExprName(o) + "." + n
            : OpenExprName(o) + "." + n + "(...)",
        Expr.Call(var f, _) => OpenExprName(f) + "(...)",
        Expr.Grace(var inner, var weight) => weight < 0
            ? "~" + OpenExprName(inner)
            : OpenExprName(inner) + "~",
        Expr.Block => "(inline library)",
        // SequenceConstruct is an internal value node; ';' is not surface
        // syntax, so render it as one sequence value, never with ';'.
        Expr.SequenceConstruct(var a, var b) => "(" + OpenExprName(a) + ", " + OpenExprName(b) + ")",
        // Postfix spread renders as `a...` over its single operand.
        Expr.SequenceSpread(var a) => OpenExprName(a) + "...",
        // Exact list literal `[a, b, c]`.
        Expr.ListLiteral(var items) => "[" + string.Join(", ", items.Select(OpenExprName)) + "]",
        // Empty sequence core nodes render by depth for diagnostics; evaluation
        // canonicalizes repeated ordinary parentheses back to `()`.
        Expr.EmptySequence(var depth) => new string('(', depth + 1) + new string(')', depth + 1),
        _ => $"({ExprKind(e)})",
    };

    private static string OpenExprUnaryOperandName(Expr expr) => expr switch
    {
        Expr.Param or Expr.Resolve or Expr.Num or Expr.StringLiteral or Expr.DotCall or Expr.Index
            => OpenExprName(expr),
        _ => $"({OpenExprName(expr)})",
    };

    /// <summary>
    /// Parenthesize an index target when a bare rendering would rebind.
    /// Indexing is postfix and binds tighter than unary, so <c>-A:0</c> reads as
    /// <c>-(A:0)</c> and a unary target needs <c>(-A):0</c>. A binary target is
    /// already self-parenthesized by <see cref="OpenExprName"/>. Postfix targets
    /// (<c>A:0:1</c>, <c>A.B:0</c>, <c>f(...):0</c>) are left-associative and
    /// render faithfully bare.
    /// Lean: indexTargetNeedsParens.
    /// </summary>
    private static string OpenExprIndexTargetName(Expr expr) => expr switch
    {
        Expr.Unary => $"({OpenExprName(expr)})",
        _ => OpenExprName(expr),
    };

    /// <summary>
    /// Parenthesize an index selector when a bare rendering would rebind. The
    /// selector is a primary in source syntax, so any form that would continue
    /// the postfix chain rebinds to the target instead: <c>A:B.C</c> reads as
    /// <c>(A:B).C</c>, <c>A:B:C</c> as <c>(A:B):C</c>, <c>A:f(0)</c> as
    /// adjacency, and <c>A:B...</c> as a spread of the whole index. A bare
    /// negative literal (<c>A:-1</c>) is not selector syntax at all. A binary
    /// selector is already self-parenthesized by <see cref="OpenExprName"/>.
    /// Lean: indexSelectorNeedsParens.
    /// </summary>
    private static string OpenExprIndexSelectorName(Expr expr) => expr switch
    {
        Expr.Unary or Expr.Call or Expr.DotCall or Expr.Index or Expr.SequenceSpread
            => $"({OpenExprName(expr)})",
        Expr.Num(var value) when value < 0 => $"({OpenExprName(expr)})",
        _ => OpenExprName(expr),
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

    private static string ExprDiagnosticName(Expr expr) => expr switch
    {
        Expr.Block(var algorithm) when algorithm.Params.Count == 0
            && algorithm.Opens.Count == 0
            && algorithm.Properties.Count == 0
            => $"({string.Join(", ", algorithm.Output.Select(ExprDiagnosticName))})",
        Expr.Binary(var op, var left, var right) => $"{ExprDiagnosticName(left)} {OpenExprBinaryOp(op)} {ExprDiagnosticName(right)}",
        // Internal SequenceConstruct renders as one sequence value; ';' is not surface syntax.
        Expr.SequenceConstruct(var left, var right) => $"({ExprDiagnosticName(left)}, {ExprDiagnosticName(right)})",
        _ => OpenExprName(expr),
    };

    private static string BinaryExprDiagnosticName(BinaryOp op, Expr left, Expr right)
        => $"{ExprDiagnosticName(left)} {OpenExprBinaryOp(op)} {ExprDiagnosticName(right)}";

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

    internal static bool ResolvesToBuiltinAlgorithm(string name, BuiltinId builtinId, EvalCtx ctx)
    {
        var result = ResolveNamedAlgorithm(name, span: null, ctx);
        return !result.IsError
            && result.Value is Algorithm.Builtin(var resolvedBuiltinId)
            && resolvedBuiltinId == builtinId;
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

    /// <summary>Lean: wireOpenBlockToGlobalScope.</summary>
    private static Algorithm WireOpenBlockToGlobalScope(Algorithm alg, EvalCtx ctx)
    {
        if (alg.Parent is not null || ctx.CallStack.Count == 0)
            return alg;

        var globalScope = ctx.CallStack[^1];
        return ReferenceEquals(globalScope, alg)
            ? alg
            : ChildOf(globalScope, alg);
    }

    /// <summary>Coerce a Result to decimal, or raise TypeMismatch for strings, BadArity otherwise. Lean: expectInt.</summary>
    internal static EvalResult<decimal> ExpectInt(Result r)
    {
        if (r is Result.Str)
            return new EvalError.TypeMismatch("Expected a number, got a string");
        var v = r.AsNum();
        return v is not null
            ? EvalResult<decimal>.Ok(v.Value)
            : new EvalError.BadArity();
    }

    /// <summary>
    /// Structural KatLang value equality used by <c>==</c> and <c>!=</c>.
    /// Numbers compare by value, strings by exact value, and sequence values by
    /// length plus recursive pairwise equality. Different value kinds compare
    /// unequal rather than raising a type mismatch. This mirrors Lean's
    /// <c>resultValueEq</c> (the derived structural <c>BEq</c> on <c>Result</c>)
    /// and reuses <see cref="Result.ValueComparer"/>, the same value equality
    /// already used by builtins such as <c>contains</c> and <c>distinct</c>.
    /// </summary>
    private static bool ValueEquals(Result left, Result right)
        => Result.ValueComparer.Equals(left, right);

    private static EvalResult<decimal> RequireNumericScalarOperand(BinaryOp op, string side, Result value)
    {
        var number = value.AsNum();
        return number is not null
            ? EvalResult<decimal>.Ok(number.Value)
            : new EvalError.TypeMismatch(NumericScalarOperandMessage(OpenExprBinaryOp(op), side, value));
    }

    private static string NumericScalarOperandMessage(string operatorName, string side, Result value)
        => $"operator `{operatorName}` expects numeric scalar operands, but the {side} operand was {DescribeNumericScalarOperand(value)}";

    private static string DescribeNumericScalarOperand(Result value) => value switch
    {
        Result.SequenceValue(var items) => $"a sequence value with {items.Count} {Pluralize(items.Count, "sequence element")}: {FormatResultForDiagnostic(value)}",
        Result.Str(var text) => $"a string: '{text}'",
        Result.Atom(var number) => $"numeric value {number.ToString(System.Globalization.CultureInfo.InvariantCulture)}",
        Result.ListValue(var items) => $"a list value with {items.Count} {Pluralize(items.Count, "element")}: {FormatResultForDiagnostic(value)}",
        _ => $"a value: {FormatResultForDiagnostic(value)}",
    };

    private static string Pluralize(int count, string singular)
        => count == 1 ? singular : singular + "s";

    internal static string FormatResultForDiagnostic(Result value) => value switch
    {
        Result.Atom(var number) => number.ToString(System.Globalization.CultureInfo.InvariantCulture),
        Result.Str(var text) => $"'{text}'",
        Result.SequenceValue(var items) => $"({string.Join(", ", items.Select(FormatResultForDiagnostic))})",
        Result.ListValue(var items) => $"[{string.Join(", ", items.Select(FormatResultForDiagnostic))}]",
        _ => "value",
    };

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
    /// Evaluate and validate the arguments for <c>range(start, stop)</c>.
    /// This is the single range-boundary validation path used by both the
    /// builtin and sequence-pipeline direct range iteration.
    /// </summary>
    private static EvalResult<InclusiveRange> EvalBuiltinRangeArguments(
        IReadOnlyList<Algorithm> args,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        if (args.Count != 2)
            return WrongBuiltinArity(BuiltinId.@range, args.Count);

        var startR = EvalAlgOutput(args[0], ctx, valEnv);
        if (startR.IsError) return startR.Error;
        var startIntR = ExpectWholeInt(startR.Value, "range start");
        if (startIntR.IsError) return startIntR.Error;

        var stopR = EvalAlgOutput(args[1], ctx, valEnv);
        if (stopR.IsError) return stopR.Error;
        var stopIntR = ExpectWholeInt(stopR.Value, "range stop");
        if (stopIntR.IsError) return stopIntR.Error;

        return EvalResult<InclusiveRange>.Ok(new InclusiveRange(startIntR.Value, stopIntR.Value));
    }

    /// <summary>Enumerate the validated inclusive integer bounds for <c>range(start, stop)</c>.</summary>
    internal static IEnumerable<decimal> EnumerateInclusiveRangeValues(InclusiveRange range)
    {
        if (range.Start <= range.Stop)
        {
            for (var current = range.Start; current <= range.Stop; current += 1m)
                yield return current;
        }
        else
        {
            for (var current = range.Start; current >= range.Stop; current -= 1m)
                yield return current;
        }
    }

    /// <summary>Count the values that <see cref="EnumerateInclusiveRangeValues"/> would produce.</summary>
    internal static long CountInclusiveRangeValues(InclusiveRange range)
    {
        var count = Math.Abs(range.Stop - range.Start) + 1m;
        return count > long.MaxValue ? long.MaxValue : (long)count;
    }

    /// <summary>
    /// Build the inclusive integer result for <c>range(start, stop)</c> as one
    /// exact immutable list value. Counts upward when <c>start &lt;= stop</c>
    /// and downward otherwise (inclusive bounds always yield at least one
    /// element). The array is freshly materialized, so ownership transfer is
    /// safe.
    /// </summary>
    private static Result BuildInclusiveRange(InclusiveRange range)
        => Result.ListValue.TakeOwnership(
            EnumerateInclusiveRangeValues(range).Select(static value => (Result)new Result.Atom(value)).ToArray());

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
    /// a sequence value is unpacked into its elements. Exact list values are
    /// NOT unpacked: call-argument binding preserves a list as one argument;
    /// only explicit caller-site <c>...</c> opens it. Lean: unpackArgs.
    /// </summary>
    private static IReadOnlyList<Result> UnpackArgs(Result r) => r switch
    {
        Result.Atom(var n) => [new Result.Atom(n)],
        Result.Str _ => [r],
        Result.SequenceValue(var items) => items,
        Result.ListValue _ => [r],
        _ => [],
    };

    private static bool PreserveCallArgBoundary(IReadOnlyList<bool>? preserveArgBoundaries, int index) =>
        preserveArgBoundaries is not null
        && index < preserveArgBoundaries.Count
        && preserveArgBoundaries[index];

    private readonly record struct VariadicCallItem(
        Result? Value,
        Algorithm? Algorithm,
        EvalError? ValueError);

    private readonly record struct ResolvedArgumentAlgorithm(
        Algorithm Algorithm,
        bool SpreadsSequence);

    private readonly record struct UserCallBindings(
        IReadOnlyList<(string, Result)> ValueBindings,
        IReadOnlyList<(string, CountedResult)> CountedBindings,
        IReadOnlyList<(string, Algorithm)> AlgorithmBindings);

    private readonly record struct CountedParameterPatternBindings(
        IReadOnlyList<(string, CountedResult)> CountedBindings);

    private readonly record struct FlatFixedCallSlot(
        Result? Value,
        Algorithm? Algorithm,
        EvalError? ValueError);

    private readonly record struct FlatFixedUserCallBindings(
        EvalCtx Context,
        IReadOnlyList<(string, Result)> ValueEnvironment);

    private readonly record struct EvaluatedSlotBindings(
        IReadOnlyList<(string Name, Result Value)> ValueBindings,
        IReadOnlyList<(string Name, CountedResult Value)> CountedBindings);

    private enum GenericLoopStepBindingShape
    {
        Legacy,
        Patterned,
        FlatFixed,
        FlatVariadic,
    }

    private readonly record struct GenericLoopStepBindingSelection(
        GenericLoopStepBindingShape Shape,
        CallableBindingPlan? Plan);

    private readonly record struct CallableArgumentBindings<T>(
        IReadOnlyList<(string ParameterName, T Item)> NormalBindings,
        string? VariadicParameterName,
        IReadOnlyList<T> VariadicItems);

    private readonly record struct FlatVariadicBindingLayout(
        CallableSignature Signature,
        string VariadicName);

    private readonly record struct VariadicCapture(
        string Name,
        Result Value,
        CountedResult CountedValue);

    private readonly record struct ParameterPatternInput(
        Result? Value,
        Algorithm? Algorithm,
        EvalError? ValueError,
        IReadOnlyList<Result>? ExplicitSequenceValueItems);

    private static bool HasStructuredParameterPattern(Algorithm algorithm)
        => algorithm.ParameterPatterns.Any(static parameter => parameter is SequenceValueParameterPattern);

    // User-call routing uses CallableBindingPlan.RequiresPatternedBinding.
    // This helper remains for runtime paths that inspect Algorithm patterns
    // directly, including callbacks, evaluated loop slots, and loop fallbacks.
    private static bool UsesPatternBinding(Algorithm algorithm)
        => HasStructuredParameterPattern(algorithm)
            || ParameterPattern.HasRepeatedCaptureNames(algorithm.ParameterPatterns);

    private static CallableBindingPlan? TryCreateUserLoopStepBindingPlan(Algorithm step)
    {
        if (step is not Algorithm.User userStep)
            return null;

        try
        {
            var signature = CallableSignature.FromUserAlgorithm("loop step", userStep);
            return CallableBindingPlan.FromSignature(signature);
        }
        catch (InvalidOperationException)
        {
            return null;
        }
    }

    private static bool IsOptimizedLoopShapeEligible(
        Algorithm step,
        out string? fallbackReason)
    {
        var plan = TryCreateUserLoopStepBindingPlan(step);
        if (plan is null)
        {
            fallbackReason = null;
            return true;
        }

        if (plan.RequiresPatternedBinding || plan.HasTopLevelVariadic)
        {
            fallbackReason = "variadic loop step";
            return false;
        }

        fallbackReason = null;
        return true;
    }

    private static GenericLoopStepBindingSelection SelectGenericLoopStepBinding(Algorithm step)
    {
        var plan = TryCreateUserLoopStepBindingPlan(step);
        if (plan is null)
            return new GenericLoopStepBindingSelection(GenericLoopStepBindingShape.Legacy, Plan: null);

        if (plan.RequiresPatternedBinding)
            return new GenericLoopStepBindingSelection(GenericLoopStepBindingShape.Patterned, plan);

        if (plan.TryGetFlatVariadicLayout(out _, out _, out _))
            return new GenericLoopStepBindingSelection(GenericLoopStepBindingShape.FlatVariadic, plan);

        if (plan.TryGetFlatFixedLayout(out _))
            return new GenericLoopStepBindingSelection(GenericLoopStepBindingShape.FlatFixed, plan);

        return new GenericLoopStepBindingSelection(GenericLoopStepBindingShape.Legacy, plan);
    }

    private static bool ShouldPreserveLoopStepSequenceSpreadExpressionBoundaries(
        Algorithm step,
        GenericLoopStepBindingSelection bindingSelection)
        => bindingSelection.Shape switch
        {
            GenericLoopStepBindingShape.Patterned => true,
            GenericLoopStepBindingShape.Legacy => UsesPatternBinding(step),
            _ => false,
        };

    private static bool TryGetFlatVariadicBindingLayout(
        CallableBindingPlan plan,
        out FlatVariadicBindingLayout layout)
    {
        if (!plan.TryGetFlatVariadicLayout(out var prefix, out var variadic, out var suffix))
        {
            layout = default;
            return false;
        }

        layout = new FlatVariadicBindingLayout(
            plan.Signature,
            variadic.Name);
        return true;
    }

    private static bool TryGetLegacyFlatVariadicBindingLayout(
        Algorithm algorithm,
        string callableName,
        out FlatVariadicBindingLayout layout)
    {
        var parameters = algorithm.Parameters;
        for (var index = 0; index < parameters.Count; index++)
        {
            var parameter = parameters[index];
            if (parameter.Kind != ParameterKind.Variadic)
                continue;

            var signature = new CallableSignature(
                callableName,
                parameters
                    .Select(static parameter => new CallableParameter(parameter.Name, parameter.Kind))
                    .ToArray());
            layout = new FlatVariadicBindingLayout(
                signature,
                parameter.Name);
            return true;
        }

        layout = default;
        return false;
    }

    private static bool TryGetPlanDerivedFlatFixedParameterNames(
        CallableBindingPlan plan,
        out IReadOnlyList<string> parameterNames)
    {
        if (!plan.TryGetFlatFixedLayout(out var captures))
        {
            parameterNames = [];
            return false;
        }

        parameterNames = captures.Select(static capture => capture.Name).ToArray();
        return true;
    }

    private static EvalResult<CallableArgumentBindings<T>> BindCallableArguments<T>(
        CallableSignature signature,
        IReadOnlyList<T> items,
        Func<int, int, EvalError> arityMismatch,
        int? minimumItemCount = null)
    {
        if (signature.Validate() is { } validationError)
            return validationError;

        var variadicIndex = signature.VariadicParameterIndex;
        if (variadicIndex < 0)
        {
            if (items.Count != signature.Parameters.Count)
                return arityMismatch(signature.Parameters.Count, items.Count);

            return EvalResult<CallableArgumentBindings<T>>.Ok(new CallableArgumentBindings<T>(
                signature.Parameters.Zip(items, static (parameter, item) => (parameter.Name, item)).ToList(),
                VariadicParameterName: null,
                VariadicItems: []));
        }

        // The default minimum is the structural parameter count (loop-state binding,
        // where the rest is assigned at least one slot). Item-supply callers — user
        // calls — pass the fixed (non-variadic) count so the rest may collect
        // zero items. (Collection builtins no longer bind here: they are
        // ordinary fixed-arity callables bound in BindSequenceBuiltinArguments.)
        var requiredNormalItemCount = minimumItemCount ?? signature.RequiredNormalParameterCount;
        if (items.Count < requiredNormalItemCount)
            return arityMismatch(requiredNormalItemCount, items.Count);

        var suffixCount = signature.Parameters.Count - variadicIndex - 1;
        var suffixStart = items.Count - suffixCount;
        var normalBindings = new List<(string ParameterName, T Item)>(requiredNormalItemCount);

        for (var index = 0; index < variadicIndex; index++)
            normalBindings.Add((signature.Parameters[index].Name, items[index]));

        for (var suffixIndex = 0; suffixIndex < suffixCount; suffixIndex++)
        {
            var parameterIndex = variadicIndex + 1 + suffixIndex;
            var itemIndex = suffixStart + suffixIndex;
            normalBindings.Add((signature.Parameters[parameterIndex].Name, items[itemIndex]));
        }

        var variadicItems = items
            .Skip(variadicIndex)
            .Take(suffixStart - variadicIndex)
            .ToList();

        return EvalResult<CallableArgumentBindings<T>>.Ok(new CallableArgumentBindings<T>(
            normalBindings,
            signature.Parameters[variadicIndex].Name,
            variadicItems));
    }

    private static EvalResult<CallableArgumentBindings<BindingInputSlot>> BindItemsToFlatVariadicLayout(
        FlatVariadicBindingLayout layout,
        IReadOnlyList<BindingInputSlot> items,
        Func<int, int, EvalError> arityMismatch)
        => BindCallableArguments(layout.Signature, items, arityMismatch);

    /// <summary>
    /// Collect a rest-assigned item supply as ONE exact immutable list value.
    ///
    /// KatLang distinguishes three item-supply operations by receiver purpose:
    /// <c>capture</c> — ordinary value/output capture, the canonicalizing
    /// boundary (<see cref="Result.FromItems"/>, singleton erasure applies);
    /// <c>collect</c> — THIS operation: rest/variadic binding materializes
    /// exactly the assigned items as one exact immutable list
    /// (<c>CollectRest([]) == []</c>, <c>CollectRest([v]) == [v]</c>, never
    /// erased); and <c>open</c> — postfix spread
    /// (<see cref="Result.SpreadItems"/>), which opens one sequence OR list
    /// boundary. The round trip <c>SpreadItems(CollectRest(xs)) == xs</c>
    /// makes variadic forwarding ordinary list spread with no hidden
    /// raw-supply metadata. Snapshot construction: the public
    /// <see cref="Result.ListValue"/> constructor copies the supplied items,
    /// so no caller-retained buffer can mutate the collected value.
    /// Lean: <c>collectRest</c>.
    /// </summary>
    private static Result.ListValue CollectRest(IReadOnlyList<Result> capturedValues)
        => new(capturedValues);

    private static VariadicCapture CreateVariadicCapture(string name, IReadOnlyList<Result> capturedValues)
    {
        var capturedResult = CollectRest(capturedValues);
        // A list value is one visible value, so a rest binding always carries
        // emitted count 1 (including the empty rest `[]`).
        return new VariadicCapture(
            name,
            capturedResult,
            new CountedResult(capturedResult, 1));
    }

    private static EvalResult<IReadOnlyList<Result>?> TryGetExplicitSequenceValueItems(
        Expr argExpr,
        EvalCtx argEvalCtx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        if (argExpr is Expr.Block(var algorithm))
        {
            var wired = WireToCaller(argEvalCtx, algorithm);
            if (wired.Params.Count == 0)
            {
                var slotsR = EvalExplicitSequenceValueItems(wired, argEvalCtx, valEnv);
                if (slotsR.IsError) return slotsR.Error;
                return EvalResult<IReadOnlyList<Result>?>.Ok(slotsR.Value);
            }
        }

        return EvalResult<IReadOnlyList<Result>?>.Ok(null);
    }

    private static EvalResult<IReadOnlyList<Result>> EvalExplicitSequenceValueItems(
        Algorithm alg,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        if (alg is Algorithm.Builtin(var builtin))
        {
            var countedR = EvalBuiltinValueCounted(builtin);
            return countedR.IsError
                ? countedR.Error
                : EvalResult<IReadOnlyList<Result>>.Ok(CountedTopLevelValues(countedR.Value));
        }

        if (alg.FindDuplicatePropName() is { } duplicateName)
            return new EvalError.DuplicateProperty(duplicateName);

        if (ConditionalValueAccessError("conditional", alg) is { } conditionalError)
            return conditionalError;

        if (alg is Algorithm.User { Output.Count: 0 })
            return new EvalError.MissingOutput();

        var slots = new List<Result>();
        var pushedCtx = ctx.Push(alg);
        foreach (var expr in alg.Output)
        {
            var exprSlotsR = EvalExplicitSequenceValueExprSlots(expr, pushedCtx, valEnv);
            if (exprSlotsR.IsError) return exprSlotsR.Error;
            slots.AddRange(exprSlotsR.Value);
        }

        return EvalResult<IReadOnlyList<Result>>.Ok(slots);
    }

    private static EvalResult<IReadOnlyList<Result>> EvalExplicitSequenceValueExprSlots(
        Expr expr,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        if (expr is Expr.Block(var algorithm))
        {
            var wired = WireToCaller(ctx, algorithm);
            if (wired.Params.Count == 0)
            {
                // A nested zero-parameter block is one written grouping level: it
                // materializes exactly one item, combined with the same shallow
                // singleton-erasing rule as ordinary block evaluation
                // (CombineOutputSlots). A singleton group such as `(A)` IS its
                // single already-evaluated item and an all-spread-empty group is
                // `()` — never a literal-unwritable orphan such as `(5)`.
                var nestedItemsR = EvalExplicitSequenceValueItems(wired, ctx, valEnv);
                if (nestedItemsR.IsError) return nestedItemsR.Error;

                return EvalResult<IReadOnlyList<Result>>.Ok([CombineOutputSlots(nestedItemsR.Value)]);
            }
        }

        var countedR = EvalCounted(expr, ctx, valEnv);
        if (countedR.IsError) return countedR.Error;

        // Mirror the output-slot rule of the algorithm-output accumulator: a
        // non-spread item expression is one item even when it evaluates to the
        // empty sequence value `()`; only an explicit spread contributes zero items.
        return expr is not Expr.SequenceSpread && countedR.Value.EmittedCount == 0
            ? EvalResult<IReadOnlyList<Result>>.Ok([countedR.Value.Value])
            : EvalResult<IReadOnlyList<Result>>.Ok(CountedTopLevelValues(countedR.Value));
    }

    private static EvalResult<IReadOnlyList<Result>> GetSequenceValuePatternItems(ParameterPatternInput input)
    {
        if (input.ExplicitSequenceValueItems is not null)
            return EvalResult<IReadOnlyList<Result>>.Ok(input.ExplicitSequenceValueItems);

        // A received sequence value or exact list value opens to its immediate
        // items (Lean: Result.structureItems?): the deconstruction receiver
        // opens ONE lone structure boundary of either kind, so
        // `x, y, z = [1, 2, 3]` binds like `x, y, z = [1, 2, 3]...`.
        if (input.Value?.StructureItems() is { } structureItems)
            return EvalResult<IReadOnlyList<Result>>.Ok(structureItems);

        return input.ValueError ?? new EvalError.BadArity();
    }

    private static EvalResult<UserCallBindings> BindParameterPattern(
        ParameterPattern pattern,
        ParameterPatternInput input,
        bool allowAlgorithmBindings)
    {
        switch (pattern)
        {
            case CaptureParameterPattern { Kind: ParameterKind.Normal } capture:
            {
                var valueBindings = new List<(string, Result)>(1);
                var algorithmBindings = new List<(string, Algorithm)>(1);

                if (input.Value is not null)
                    valueBindings.Add((capture.Name, input.Value));

                if (allowAlgorithmBindings && input.Algorithm is not null)
                    algorithmBindings.Add((capture.Name, input.Algorithm));

                if (input.Value is null && (!allowAlgorithmBindings || input.Algorithm is null))
                    return input.ValueError ?? new EvalError.BadArity();

                return EvalResult<UserCallBindings>.Ok(new UserCallBindings(valueBindings, [], algorithmBindings));
            }

            case CaptureParameterPattern { Kind: ParameterKind.Variadic }:
                return new EvalError.BadArity();

            case SequenceValueParameterPattern group:
            {
                var itemsR = GetSequenceValuePatternItems(input);
                // A non-grouped scalar value is a one-item supply for the
                // prefix/rest/suffix matcher (the same normalization the function
                // deconstruction path applies via rule 4). This lets a scalar
                // right-hand side bind a rest pattern that captures zero items,
                // e.g. `first, tail... = 1` (first = 1, tail = []), instead of being
                // rejected before the matcher runs.
                if (itemsR.IsError && input.Value is not null)
                {
                    itemsR = EvalResult<IReadOnlyList<Result>>.Ok([input.Value]);
                }

                if (itemsR.IsError) return itemsR.Error;

                var nestedInputs = itemsR.Value
                    .Select(static item => new ParameterPatternInput(item, Algorithm: null, ValueError: null, ExplicitSequenceValueItems: null))
                    .ToList();
                return BindParameterPatternList(
                    group.Items,
                    nestedInputs,
                    allowAlgorithmBindings: false,
                    (required, actual) => new EvalError.ArityMismatch(required, actual));
            }

            default:
                return new EvalError.BadArity();
        }
    }

    private static EvalResult<UserCallBindings> BindParameterPatternList(
        IReadOnlyList<ParameterPattern> patterns,
        IReadOnlyList<ParameterPatternInput> inputs,
        bool allowAlgorithmBindings,
        Func<int, int, EvalError> arityMismatch)
    {
        var variadicIndex = -1;
        for (var index = 0; index < patterns.Count; index++)
        {
            if (patterns[index] is not CaptureParameterPattern { Kind: ParameterKind.Variadic })
                continue;

            if (variadicIndex >= 0)
                return new EvalError.BadArity();

            variadicIndex = index;
        }

        var valueBindings = new List<(string, Result)>();
        var countedBindings = new List<(string, CountedResult)>();
        var algorithmBindings = new List<(string, Algorithm)>();

        EvalResult<bool> AddBindings(UserCallBindings bindings)
        {
            var existingValueNames = valueBindings
                .Select(static binding => binding.Item1)
                .ToHashSet(StringComparer.Ordinal);
            var incomingValueNames = bindings.ValueBindings
                .Select(static binding => binding.Item1)
                .ToHashSet(StringComparer.Ordinal);

            foreach (var binding in bindings.ValueBindings)
            {
                var existing = LookupVal(valueBindings, binding.Item1);
                if (existing is not null)
                {
                    if (!Result.ValueComparer.Equals(existing, binding.Item2))
                        return new EvalError.BadArity();
                    continue;
                }

                valueBindings.Add(binding);
            }

            foreach (var binding in bindings.CountedBindings)
            {
                var existing = LookupCountedParam(countedBindings, binding.Item1);
                if (existing is not null)
                {
                    if (!Result.ValueComparer.Equals(existing.Value.Value, binding.Item2.Value))
                        return new EvalError.BadArity();
                    continue;
                }

                countedBindings.Add(binding);
            }

            foreach (var binding in bindings.AlgorithmBindings)
            {
                var existingIndex = algorithmBindings.FindIndex(
                    existing => string.Equals(existing.Item1, binding.Item1, StringComparison.Ordinal));
                if (existingIndex < 0)
                {
                    algorithmBindings.Add(binding);
                    continue;
                }

                if (!existingValueNames.Contains(binding.Item1) || !incomingValueNames.Contains(binding.Item1))
                {
                    return new EvalError.TypeMismatch(
                        "Repeated bind equality is not supported for algorithm-only arguments");
                }
            }

            return EvalResult<bool>.Ok(true);
        }

        EvalResult<bool> BindOne(int patternIndex, int inputIndex)
        {
            var boundR = BindParameterPattern(patterns[patternIndex], inputs[inputIndex], allowAlgorithmBindings);
            if (boundR.IsError) return boundR.Error;

            return AddBindings(boundR.Value);
        }

        if (variadicIndex < 0)
        {
            if (patterns.Count != inputs.Count)
                return arityMismatch(patterns.Count, inputs.Count);

            for (var index = 0; index < patterns.Count; index++)
            {
                var boundR = BindOne(index, index);
                if (boundR.IsError) return boundR.Error;
            }

            return EvalResult<UserCallBindings>.Ok(new UserCallBindings(valueBindings, countedBindings, algorithmBindings));
        }

        var requiredCount = patterns.Count - 1;
        if (inputs.Count < requiredCount)
            return arityMismatch(requiredCount, inputs.Count);

        for (var index = 0; index < variadicIndex; index++)
        {
            var boundR = BindOne(index, index);
            if (boundR.IsError) return boundR.Error;
        }

        var suffixCount = patterns.Count - variadicIndex - 1;
        var suffixInputStart = inputs.Count - suffixCount;
        for (var suffixIndex = 0; suffixIndex < suffixCount; suffixIndex++)
        {
            var boundR = BindOne(variadicIndex + 1 + suffixIndex, suffixInputStart + suffixIndex);
            if (boundR.IsError) return boundR.Error;
        }

        var variadicCapture = (CaptureParameterPattern)patterns[variadicIndex];
        var capturedValues = new List<Result>(suffixInputStart - variadicIndex);
        for (var inputIndex = variadicIndex; inputIndex < suffixInputStart; inputIndex++)
        {
            var input = inputs[inputIndex];
            if (input.Value is null)
                return input.ValueError ?? new EvalError.BadArity();

            capturedValues.Add(input.Value);
        }

        var capture = CreateVariadicCapture(variadicCapture.Name, capturedValues);
        var captureBindingsR = AddBindings(new UserCallBindings(
            [(capture.Name, capture.Value)],
            [(capture.Name, capture.CountedValue)],
            []));
        if (captureBindingsR.IsError) return captureBindingsR.Error;

        return EvalResult<UserCallBindings>.Ok(new UserCallBindings(valueBindings, countedBindings, algorithmBindings));
    }

    private static EvalResult<UserCallBindings> BindPatternedUserCall(
        Algorithm callee,
        Algorithm wiredArgs,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv,
        string? calleeName)
    {
        var argExprs = wiredArgs.Output;
        var signature = CallableSignature.FromAlgorithm(calleeName ?? "<anonymous>", callee);

        var maybeAlgsR = TryResolveArgAlgs(wiredArgs, ctx);
        if (maybeAlgsR.IsError) return maybeAlgsR.Error;

        var maybeAlgs = maybeAlgsR.Value;
        var argEvalCtx = ctx.Push(wiredArgs);
        var inputs = new List<ParameterPatternInput>(argExprs.Count);

        for (var index = 0; index < argExprs.Count; index++)
        {
            var argExpr = argExprs[index];
            var maybeAlg = index < maybeAlgs.Count ? maybeAlgs[index] : null;
            var evalR = Eval(argExpr, argEvalCtx, valEnv);
            IReadOnlyList<Result>? explicitSequenceValueItems = null;

            if (evalR.IsOk)
            {
                var explicitSequenceValueItemsR = TryGetExplicitSequenceValueItems(argExpr, argEvalCtx, valEnv);
                if (explicitSequenceValueItemsR.IsError) return explicitSequenceValueItemsR.Error;
                explicitSequenceValueItems = explicitSequenceValueItemsR.Value;
            }

            inputs.Add(new ParameterPatternInput(
                evalR.IsOk ? evalR.Value : null,
                maybeAlg,
                evalR.IsError ? evalR.Error : null,
                explicitSequenceValueItems));
        }

        return BindParameterPatternList(
            callee.ParameterPatterns,
            inputs,
            allowAlgorithmBindings: true,
            (required, actual) => new EvalError.ArityMismatch(required, actual)
            {
                Signature = signature,
            });
    }

    private static EvalResult<IReadOnlyList<BindingInputSlot>> BuildVariadicBindingInputSlots(
        Algorithm wiredArgs,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv,
        IReadOnlyList<bool>? preserveArgBoundaries = null)
    {
        var argExprs = wiredArgs.Output;
        var maybeAlgsR = TryResolveArgAlgs(wiredArgs, ctx);
        if (maybeAlgsR.IsError) return maybeAlgsR.Error;

        var maybeAlgs = maybeAlgsR.Value;
        var argEvalCtx = ctx.Push(wiredArgs);
        var items = new List<BindingInputSlot>();

        for (var index = 0; index < argExprs.Count; index++)
        {
            var argExpr = argExprs[index];
            var maybeAlg = index < maybeAlgs.Count ? maybeAlgs[index] : null;
            var preserveArgBoundary = PreserveCallArgBoundary(preserveArgBoundaries, index);
            var isDotReceiverSegment = IsInjectedDotCallReceiverSegment(preserveArgBoundaries, index);

            if (argExpr is Expr.SequenceSpread && !preserveArgBoundary)
            {
                var suppliedR = EvalCounted(argExpr, argEvalCtx, valEnv);
                if (suppliedR.IsError)
                    return suppliedR.Error;

                foreach (var value in CountedTopLevelValues(suppliedR.Value))
                    items.Add(BindingInputSlot.FromUserCallItem(value, algorithm: null, valueError: null));

                continue;
            }

            var evaluatedR = isDotReceiverSegment
                ? EvalDotReceiverCallSegmentCounted(argExpr, ctx, argEvalCtx, valEnv)
                : EvalCounted(argExpr, argEvalCtx, valEnv);
            if (evaluatedR.IsOk)
            {
                items.Add(BindingInputSlot.FromUserCallItem(
                    evaluatedR.Value.Value,
                    maybeAlg,
                    valueError: null));
                continue;
            }

            if (maybeAlg is not null)
            {
                items.Add(BindingInputSlot.FromUserCallItem(value: null, algorithm: maybeAlg, valueError: evaluatedR.Error));
                continue;
            }

            return evaluatedR.Error;
        }

        return EvalResult<IReadOnlyList<BindingInputSlot>>.Ok(items);
    }

    private static bool IsInjectedDotCallReceiverSegment(
        IReadOnlyList<bool>? preserveArgBoundaries,
        int index)
        => preserveArgBoundaries is not null
        && index == 0;

    private static EvalResult<CountedResult> EvalDotReceiverCallSegmentCounted(
        Expr receiver,
        EvalCtx ctx,
        EvalCtx argEvalCtx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        if (receiver is Expr.Block(var algorithm))
        {
            var wired = WireToCaller(ctx, algorithm);
            if (wired.Params.Count == 0)
                return WithSpan(receiver.Span ?? FirstSpan(wired.Output), EvalAlgOutputCounted(wired, ctx, valEnv));
        }

        return EvalCounted(receiver, argEvalCtx, valEnv);
    }

    private static EvalError VariadicBindingArityMismatch(
        string? calleeName,
        int requiredNormalItemCount,
        int actualItemCount,
        CallableSignature? signature = null)
        => string.IsNullOrWhiteSpace(calleeName)
            ? new EvalError.ArityMismatch(requiredNormalItemCount, actualItemCount)
            : new EvalError.VariadicArityMismatch(calleeName, requiredNormalItemCount, actualItemCount)
            {
                Signature = signature,
            };


    /// <summary>
    /// True when a callable's top-level parameter list captures the supplied call
    /// argument stream: any top-level variadic capture, including rest-only
    /// <c>name...</c> and mixed fixed/rest shapes such as <c>x, y..., z</c>.
    /// Checked only after patterned (sequence-value / repeated-name) binding has
    /// been ruled out.
    /// Lean: <c>Algorithm.usesItemSupplyBinding</c>.
    /// </summary>
    private static bool IsDeconstructionUserCallShape(CallableSignature signature)
        => signature.HasVariadicParameter;

    /// <summary>
    /// Builtin collection-item view of the bound collection argument: opens
    /// exactly one outer sequence or exact-list boundary to its immediate
    /// items; any other value supplies itself as one item (a scalar is a
    /// one-element collection). Never recursive — nested sequence values and
    /// nested list values stay intact as single items.
    /// Applied strictly AFTER ordinary fixed parameter binding, to the already
    /// bound <c>collection</c> parameter only — argument boundaries are never
    /// altered before binding. Shared by generic collection-builtin binding
    /// and by the sequence-pipeline optimizer's receiver mirror so both open
    /// collections identically.
    /// Lean: <c>builtinCollectionItems</c>.
    /// </summary>
    private static IReadOnlyList<Result> BuiltinCollectionItems(Result value)
        => value is Result.ListValue(var listItems) ? listItems : value.ToItems();

    /// <summary>
    /// Binds a call to an item-supply parameter list (any top-level variadic).
    /// The call argument stream is already the receiver for parameter binding:
    /// a plain sequence-valued argument contributes one item, while explicit
    /// spread contributes the opened items.
    /// Lean: <c>bindDeconstructionUserCall</c>.
    /// </summary>
    private static EvalResult<UserCallBindings> BindDeconstructionUserCall(
        Algorithm callee,
        Algorithm wiredArgs,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv,
        string? calleeName,
        IReadOnlyList<bool>? preserveArgBoundaries = null)
    {
        var itemsR = BuildVariadicBindingInputSlots(wiredArgs, ctx, valEnv, preserveArgBoundaries);
        if (itemsR.IsError) return itemsR.Error;

        var signature = CallableSignature.FromAlgorithm(calleeName ?? "<anonymous>", callee);
        var inputs = itemsR.Value
            .Select(static slot => new ParameterPatternInput(
                slot.Value, slot.Algorithm, slot.ValueError, ExplicitSequenceValueItems: null))
            .ToList();

        // A deconstruction parameter list always carries a rest binding, so a
        // too-few-items failure reports the fixed-binding minimum ("at least N")
        // rather than the exact-count wording used by strict callables.
        return BindParameterPatternList(
            callee.ParameterPatterns,
            inputs,
            allowAlgorithmBindings: true,
            (required, actual) => VariadicBindingArityMismatch(calleeName, required, actual, signature));
    }

    private static EvalCtx WithUserCallBindingEnvironments(
        EvalCtx ctx,
        UserCallBindings bindings,
        IEnumerable<string> shadowedNames)
    {
        var shadowed = shadowedNames.ToArray();
        return ctx
            .WithAlgEnv(Concat(bindings.AlgorithmBindings, ctx.AlgEnv))
            .WithCountedParamEnv(Concat(bindings.CountedBindings, ShadowCountedParamEnv(ctx.CountedParamEnv, shadowed)));
    }

    private static EvalCtx WithCountedParameterEnvironments(
        EvalCtx ctx,
        IReadOnlyList<(string, CountedResult)> countedBindings,
        IEnumerable<string> shadowedNames)
    {
        var shadowed = shadowedNames.ToArray();
        return ctx
            .WithCountedParamEnv(Concat(countedBindings, ShadowCountedParamEnv(ctx.CountedParamEnv, shadowed)));
    }

    private static EvalResult<FlatFixedUserCallBindings> BindFlatFixedUserCallArguments(
        CallableSignature signature,
        IReadOnlyList<string> parameterNames,
        Algorithm wiredArgs,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var argExprs = wiredArgs.Output;
        var paramCount = parameterNames.Count;

        // Try to resolve each arg as algorithm (for AlgEnv bindings)
        var maybeAlgsR = TryResolveArgAlgs(wiredArgs, ctx);
        if (maybeAlgsR.IsError) return maybeAlgsR.Error;
        var maybeAlgs = maybeAlgsR.Value;

        // Lean: let argEvalCtx := EvalCtx.push wiredArgs ctx
        var argEvalCtx = ctx.Push(wiredArgs);

        var slots = new List<FlatFixedCallSlot>(argExprs.Count);

        for (var i = 0; i < argExprs.Count; i++)
        {
            var argExpr = argExprs[i];
            if (argExpr is Expr.SequenceSpread)
            {
                // Flat fixed calls expand bare spread args. Dot-call
                // fixed receivers that must stay one boundary are wrapped before
                // this path, so they do not arrive here as Expr.SequenceSpread.
                var suppliedR = EvalCounted(argExpr, argEvalCtx, valEnv);
                if (suppliedR.IsError) return suppliedR.Error;

                foreach (var value in CountedTopLevelValues(suppliedR.Value))
                    slots.Add(new FlatFixedCallSlot(value, Algorithm: null, ValueError: null));

                continue;
            }

            var maybeAlg = i < maybeAlgs.Count ? maybeAlgs[i] : null;
            var evalR = Eval(argExpr, argEvalCtx, valEnv);
            if (evalR.IsOk)
            {
                slots.Add(new FlatFixedCallSlot(evalR.Value, maybeAlg, ValueError: null));
            }
            else if (maybeAlg is not null)
            {
                slots.Add(new FlatFixedCallSlot(Value: null, maybeAlg, evalR.Error));
            }
            else
            {
                return evalR.Error;
            }
        }

        if (slots.Count > paramCount)
            return new EvalError.ArityMismatch(paramCount, slots.Count) { Signature = signature };

        var algBindings = new List<(string, Algorithm)>();
        var valueParams = new List<string>();
        var valueResults = new List<Result>();

        for (var i = 0; i < paramCount; i++)
        {
            if (i >= slots.Count)
            {
                valueParams.Add(parameterNames[i]);
                continue;
            }

            var slot = slots[i];
            if (slot.Algorithm is not null)
                algBindings.Add((parameterNames[i], slot.Algorithm));

            if (slot.Value is not null)
            {
                valueParams.Add(parameterNames[i]);
                valueResults.Add(slot.Value);
            }
        }

        var argEnvR = BindParams(valueParams, valueResults);
        if (argEnvR.IsError)
        {
            if (argEnvR.Error is EvalError.ArityMismatch arityMismatch)
                return arityMismatch with { Signature = signature };

            return argEnvR.Error;
        }

        var boundCtx = ctx
            .WithAlgEnv(Concat(algBindings, ctx.AlgEnv))
            .WithCountedParamEnv(ShadowCountedParamEnv(ctx.CountedParamEnv, parameterNames));
        var boundEnv = Concat(argEnvR.Value, valEnv);
        return EvalResult<FlatFixedUserCallBindings>.Ok(new FlatFixedUserCallBindings(boundCtx, boundEnv));
    }

    // ── Result helpers ────────────────────────────────────────────────────────

    /// <summary>
    /// Extract top-level items from a result into a list.
    /// Atom/string -> singleton list; sequence value -> its items. A list
    /// value stays opaque (one item), matching <see cref="Result.ToItems"/>.
    /// Lean: Result.toItems.
    /// </summary>
    private static void ResultItems(List<Result> into, Result r)
    {
        switch (r)
        {
            case Result.Atom:
            case Result.Str:
            case Result.ListValue:
                into.Add(r);
                break;
            case Result.SequenceValue(var items):
                into.AddRange(items);
                break;
        }
    }

    /// <summary>
    /// Evaluate <c>target:selector</c> through the shared one-level projected
    /// selection semantics.
    /// Construction preserves structure; selection projects content.
    /// This helper is the single owner of index-expression error spans: every
    /// error it returns carries the full <c>target:selector</c> span unless it
    /// already carries a more specific inner one (<see cref="WithSpan"/> only
    /// fills a missing span, so a selector sub-expression such as
    /// <c>1 div 0</c> keeps its own). Callers therefore need no wrapping of
    /// their own, and plain and counted evaluation report identical spans.
    /// </summary>
    private static EvalResult<CountedResult> EvalIndexSelectionCounted(
        Expr target,
        Expr selector,
        SourceSpan? span,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var targetR = Eval(target, ctx, valEnv);
        if (targetR.IsError) return WithSpan<CountedResult>(span, targetR.Error);

        // ExpectInt reports TypeMismatch/BadArity from a Result and so has no
        // span of its own; the index expression is the nearest source location.
        var nR = EvalInt(selector, ctx, valEnv);
        if (nR.IsError) return WithSpan<CountedResult>(span, nR.Error);

        var n = nR.Value;
        if (n < 0 || n != Math.Floor(n))
            return new EvalError.BadIndex() { Span = span };

        // Lean models the selector as an unbounded integer and reports
        // badIndex for any position past the target's items; a selector
        // beyond int range can never be in range, so it is the same
        // out-of-range error rather than a host overflow.
        if (n > int.MaxValue)
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
        => new Expr.EmptySequence(0);

    private static Expr ResultToExpr(Result result) => result switch
    {
        Result.Atom(var n) => new Expr.Num(n),
        Result.Str(var s) => new Expr.StringLiteral(s),
        // Repeated ordinary parentheses around the empty sequence are redundant
        // surface structure, so any empty-sequence chain reifies as `()`.
        Result.SequenceValue when IsEmptySequenceChain(result)
            => new Expr.EmptySequence(0),
        Result.SequenceValue(var items) => new Expr.Block(new Algorithm.User(
            Parent: null,
            Parameters: [],
            Opens: [],
            Properties: [],
            Output: items.Select(ResultToExpr).ToList())),
        // Exact list values reify as list literals so they round-trip
        // losslessly (a reified `()` element stays one visible list element).
        Result.ListValue(var items) => new Expr.ListLiteral(items.Select(ResultToExpr).ToList()),
        _ => EmptyResultExpr(),
    };

    /// <summary>
    /// Builds the canonical empty sequence value for an <see cref="Expr.EmptySequence"/>.
    /// Repeated ordinary parentheses around <c>()</c> do not create higher-order
    /// empty sequence values.
    /// </summary>
    private static Result BuildEmptySequenceValue(int _)
        => Result.SequenceValue.TakeOwnership([]);

    /// <summary>
    /// Returns true when <paramref name="result"/> is the empty sequence value or
    /// a redundant chain of one-item sequences ending in it.
    /// </summary>
    private static bool IsEmptySequenceChain(Result result)
    {
        var current = result;
        while (true)
        {
            if (current is not Result.SequenceValue(var items))
                return false;
            if (items.Count == 0)
                return true;
            if (items.Count != 1)
                return false;
            current = items[0];
        }
    }

    /// <summary>Lean: <c>Algorithm.ofExpr</c>.</summary>
    private static Algorithm AlgorithmOfExpr(Expr expr) => new Algorithm.User(
        Parent: null,
        Parameters: [],
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
    internal readonly record struct CountedResult(Result Value, int EmittedCount);

    internal readonly record struct CountedRootProgramResult(
        CountedResult Output,
        CountedResult? TopLevelProperty);

    /// <summary>
    /// Evaluated bounds for the inclusive integer <c>range(start, stop)</c>
    /// builtin. The bounds have already passed range's whole-integer validation.
    /// </summary>
    internal readonly record struct InclusiveRange(decimal Start, decimal Stop);

    /// <summary>
    /// Collected collection input records the bound collection argument's
    /// viewed items plus the prepared outer-item supply used by the current
    /// builtin.
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

    private abstract record PreparedSequenceBuiltinSuffixArg
    {
        public sealed record AlgorithmArg(KatLang.Algorithm AlgorithmValue) : PreparedSequenceBuiltinSuffixArg;

        public sealed record ValueArg(Result ResultValue) : PreparedSequenceBuiltinSuffixArg;

        public sealed record WholeNumberArg(decimal WholeNumberValue) : PreparedSequenceBuiltinSuffixArg;
    }

    /// <summary>
    /// Validate the output shape required by counted builtins that must emit
    /// exactly one top-level value. Non-empty sequence values are valid; the empty
    /// sequence value <c>()</c> and multiple top-level outputs are rejected. (An
    /// empty-sequence output is a visible slot at the output boundary, but these
    /// builtins require a substantive single element.)
    /// Lean: <c>expectSingleValueWith</c>.
    /// </summary>
    private static EvalResult<Result> ExpectSingleEmittedValue(CountedResult output, string errorMessage)
        => output.EmittedCount == 1 && output.Value is not Result.SequenceValue { Items.Count: 0 }
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
    private static bool MatchPattern(
        Pattern pattern,
        Result result,
        List<(string, Result)> bindings)
    {
        switch (pattern)
        {
            case Pattern.Bind(var name):
            {
                var existing = LookupVal(bindings, name);
                if (existing is not null)
                    return Result.ValueComparer.Equals(existing, result);

                bindings.Add((name, result));
                return true;
            }

            case Pattern.LitInt(var n):
                return result is Result.Atom(var v) && v == n;

            case Pattern.LitString(var s):
                return result is Result.Str(var sv)
                    && string.Equals(sv, s, StringComparison.Ordinal);

            case Pattern.SequenceValue(var items):
                // Result.normalize collapses sequenceValue [x] -> x, so a
                // singleton sequence-value pattern (e.g. "(b)") must also
                // match a non-sequence-value result by treating it as if it
                // were sequenceValue [result].
                if (result is Result.SequenceValue(var rs))
                {
                    if (rs.Count != items.Count) return false;
                }
                else if (items.Count == 1)
                {
                    rs = [result];
                }
                else
                {
                    return false;
                }

                for (var i = 0; i < items.Count; i++)
                {
                    if (!MatchPattern(items[i], rs[i], bindings))
                        return false;
                }
                return true;

            default:
                return false;
        }
    }

    private static IReadOnlyList<(string, Result)>? MatchPattern(Pattern pattern, Result result)
    {
        var bindings = new List<(string, Result)>();
        return MatchPattern(pattern, result, bindings) ? bindings : null;
    }

    /// <summary>
    /// Match a top-level conditional call head against the explicit arguments
    /// supplied at the call site.
    ///
    /// Ordinary direct conditional calls preserve explicit argument slots at
    /// the top level: a non-sequence-value head expects exactly one explicit argument,
    /// while a sequence-value head expects one explicit argument per sequence element. Nested
    /// sequence-value structure is still matched through <see cref="MatchPattern"/>.
    /// </summary>
    private static IReadOnlyList<(string, Result)>? MatchCallPattern(
        Pattern pattern,
        IReadOnlyList<Result> explicitArgs)
    {
        if (pattern is Pattern.SequenceValue(var items))
        {
            if (items.Count != explicitArgs.Count)
                return null;

            var bindings = new List<(string, Result)>();
            for (var i = 0; i < items.Count; i++)
            {
                if (!MatchPattern(items[i], explicitArgs[i], bindings))
                    return null;
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

    private static bool MatchCountedPattern(
        Pattern pattern,
        CountedResult result,
        List<(string, CountedResult)> bindings)
    {
        switch (pattern)
        {
            case Pattern.Bind(var name):
            {
                var existing = LookupCountedParam(bindings, name);
                if (existing is not null)
                    return Result.ValueComparer.Equals(existing.Value.Value, result.Value);

                bindings.Add((name, result));
                return true;
            }

            case Pattern.LitInt(var n):
                return result.Value is Result.Atom(var v) && v == n;

            case Pattern.LitString(var s):
                return result.Value is Result.Str(var sv)
                    && string.Equals(sv, s, StringComparison.Ordinal);

            case Pattern.SequenceValue(var items):
                IReadOnlyList<Result> members;
                if (result.Value is Result.SequenceValue(var groupedMembers))
                {
                    if (groupedMembers.Count != items.Count)
                        return false;

                    members = groupedMembers;
                }
                else if (items.Count == 1)
                {
                    members = [result.Value];
                }
                else
                {
                    return false;
                }

                for (var i = 0; i < items.Count; i++)
                {
                    if (!MatchCountedPattern(
                        items[i],
                        new CountedResult(members[i], members[i].ValueCount()),
                        bindings))
                        return false;
                }

                return true;

            default:
                return false;
        }
    }

    private static IReadOnlyList<(string, CountedResult)>? MatchCountedPattern(
        Pattern pattern,
        CountedResult result)
    {
        var bindings = new List<(string, CountedResult)>();
        return MatchCountedPattern(pattern, result, bindings) ? bindings : null;
    }

    private static IReadOnlyList<(string, CountedResult)>? MatchCountedCallPattern(
        Pattern pattern,
        IReadOnlyList<CountedResult> explicitArgs)
    {
        if (pattern is Pattern.SequenceValue(var items))
        {
            if (items.Count != explicitArgs.Count)
                return null;

            var bindings = new List<(string, CountedResult)>();
            for (var i = 0; i < items.Count; i++)
            {
                if (!MatchCountedPattern(items[i], explicitArgs[i], bindings))
                    return null;
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
            ? (Algorithm.User)body.WithParameters(Algorithm.NormalParameters(paramNames))
            : null;
    }

    /// <summary>
    /// Value-position access to a conditional algorithm cannot select a branch,
    /// so it must fail instead of silently forcing the conditional's empty
    /// output list. Mirrors the no-argument dot-call dispatch: a flat
    /// multi-binder core equivalent reports its ordinary call arity, and any
    /// other conditional reports NoMatchingBranch. Returns null for
    /// non-conditional algorithms. Lean: <c>conditionalValueAccessError?</c>.
    /// </summary>
    private static EvalError? ConditionalValueAccessError(string name, Algorithm alg)
    {
        if (alg is not Algorithm.Conditional)
            return null;

        var simple = TryGetFlatBinderUserEquivalent(alg);
        if (simple is not null)
            return new EvalError.ArityMismatch(simple.Params.Count, 0);

        return new EvalError.NoMatchingBranch(name);
    }

    /// <summary>
    /// Reify a pre-evaluated counted argument as a zero-parameter algorithm
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
            Parameters: [],
            Opens: [],
            Properties: [],
            Output: output);
    }

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
    /// Callback binding for a flat callee whose top-level parameters include a
    /// rest parameter. The callback argument supply keeps the established
    /// flat-callback row convention: when fewer argument slots are supplied
    /// than top-level parameters, the final supplied argument opens into its
    /// items (matching <c>callee(S:i)</c>; exact lists stay opaque), exactly
    /// as <see cref="BindCountedCallbackParams"/> does for fixed-only flat
    /// callees. The resulting slots then bind through the shared
    /// prefix/rest/suffix binder, so the rest parameter COLLECTS its allocated
    /// slots as one exact immutable list. Lean:
    /// <c>bindCountedCallbackParameterPatternList</c>.
    /// </summary>
    private static EvalResult<CountedParameterPatternBindings> BindCountedCallbackParameterPatternList(
        IReadOnlyList<ParameterPattern> patterns,
        IReadOnlyList<CountedResult> args)
    {
        var slots = args;
        if (args.Count > 0 && args.Count < patterns.Count)
        {
            var expanded = new List<CountedResult>(patterns.Count);
            for (var index = 0; index < args.Count - 1; index++)
                expanded.Add(args[index]);
            expanded.AddRange(UnpackCountedArg(args[^1]));
            slots = expanded;
        }

        return BindCountedParameterPatternList(
            patterns,
            slots,
            static (required, actual) => new EvalError.ArityMismatch(required, actual));
    }

    private static EvalResult<CountedParameterPatternBindings> BindCountedParameterPattern(
        ParameterPattern pattern,
        CountedResult input)
    {
        switch (pattern)
        {
            case CaptureParameterPattern { Kind: ParameterKind.Normal } capture:
                return EvalResult<CountedParameterPatternBindings>.Ok(new CountedParameterPatternBindings(
                    [(capture.Name, input)]));

            case CaptureParameterPattern { Kind: ParameterKind.Variadic }:
                return new EvalError.BadArity();

            case SequenceValueParameterPattern group:
            {
                // A received sequence value or exact list value opens to its
                // immediate items (Lean: Result.structureItems?); the counted
                // callback path keeps its stricter singleton-only scalar
                // fallback (sequence-value-pattern callback deconstruction of
                // scalar elements stays deferred; flat top-level rest
                // callbacks bind via BindCountedCallbackParameterPatternList).
                var items = input.Value.StructureItems();
                if (items is null && group.Items.Count == 1)
                    items = [input.Value];

                if (items is null)
                    return new EvalError.BadArity();

                var nestedInputs = items
                    .Select(static item => new CountedResult(item, item.ValueCount()))
                    .ToList();
                return BindCountedParameterPatternList(
                    group.Items,
                    nestedInputs,
                    (required, actual) => new EvalError.ArityMismatch(required, actual));
            }

            default:
                return new EvalError.BadArity();
        }
    }

    private static EvalResult<CountedParameterPatternBindings> BindCountedParameterPatternList(
        IReadOnlyList<ParameterPattern> patterns,
        IReadOnlyList<CountedResult> inputs,
        Func<int, int, EvalError> arityMismatch)
    {
        var variadicIndex = -1;
        for (var index = 0; index < patterns.Count; index++)
        {
            if (patterns[index] is not CaptureParameterPattern { Kind: ParameterKind.Variadic })
                continue;

            if (variadicIndex >= 0)
                return new EvalError.BadArity();

            variadicIndex = index;
        }

        var bindings = new List<(string, CountedResult)>();

        EvalResult<bool> AddBindings(CountedParameterPatternBindings added)
        {
            foreach (var binding in added.CountedBindings)
            {
                var existing = LookupCountedParam(bindings, binding.Item1);
                if (existing is not null)
                {
                    if (!Result.ValueComparer.Equals(existing.Value.Value, binding.Item2.Value))
                        return new EvalError.BadArity();
                    continue;
                }

                bindings.Add(binding);
            }

            return EvalResult<bool>.Ok(true);
        }

        EvalResult<bool> BindOne(int patternIndex, int inputIndex)
        {
            var boundR = BindCountedParameterPattern(patterns[patternIndex], inputs[inputIndex]);
            if (boundR.IsError) return boundR.Error;

            return AddBindings(boundR.Value);
        }

        if (variadicIndex < 0)
        {
            if (patterns.Count != inputs.Count)
                return arityMismatch(patterns.Count, inputs.Count);

            for (var index = 0; index < patterns.Count; index++)
            {
                var boundR = BindOne(index, index);
                if (boundR.IsError) return boundR.Error;
            }

            return EvalResult<CountedParameterPatternBindings>.Ok(new CountedParameterPatternBindings(bindings));
        }

        var requiredCount = patterns.Count - 1;
        if (inputs.Count < requiredCount)
            return arityMismatch(requiredCount, inputs.Count);

        for (var index = 0; index < variadicIndex; index++)
        {
            var boundR = BindOne(index, index);
            if (boundR.IsError) return boundR.Error;
        }

        var suffixCount = patterns.Count - variadicIndex - 1;
        var suffixInputStart = inputs.Count - suffixCount;
        for (var suffixIndex = 0; suffixIndex < suffixCount; suffixIndex++)
        {
            var boundR = BindOne(variadicIndex + 1 + suffixIndex, suffixInputStart + suffixIndex);
            if (boundR.IsError) return boundR.Error;
        }

        var variadicCapture = (CaptureParameterPattern)patterns[variadicIndex];
        var capturedValues = inputs
            .Skip(variadicIndex)
            .Take(suffixInputStart - variadicIndex)
            .Select(static input => input.Value)
            .ToList();
        // Rest binding COLLECTS: the assigned supply becomes one exact
        // immutable list value, emitted count 1 (a list is one visible value).
        var capturedResult = CollectRest(capturedValues);
        var captured = new CountedResult(capturedResult, 1);
        var captureBindingsR = AddBindings(new CountedParameterPatternBindings(
            [(variadicCapture.Name, captured)]));
        if (captureBindingsR.IsError) return captureBindingsR.Error;

        return EvalResult<CountedParameterPatternBindings>.Ok(new CountedParameterPatternBindings(bindings));
    }

    /// <summary>
    /// Higher-order callbacks keep the collected item value shape for pattern
    /// matching, while the counted callback-param view still uses the same
    /// one-level projection rule as <c>S:i</c> for callback param operations
    /// like <c>x.count</c>.
    /// </summary>
    private static CountedResult CountedSequenceCallbackItem(CountedResult item)
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

                    var newCtx = WithCountedParameterEnvironments(ctx, countedEnvR.Value, simpleCallee.Params);
                    return EvalAlgOutputCounted(simpleCallee, newCtx, valEnv);
                }

                return EvalConditionalCallbackCallCounted(callee, args, ctx, valEnv, calleeName);

            default:
            {
                if (callee.Output.Count == 0)
                    return new EvalError.MissingOutput();

                if (UsesPatternBinding(callee))
                {
                    var countedPatternEnvR = BindCountedParameterPatternList(
                        callee.ParameterPatterns,
                        args,
                        (required, actual) => new EvalError.ArityMismatch(required, actual));
                    if (countedPatternEnvR.IsError) return countedPatternEnvR.Error;

                    var patternBindings = countedPatternEnvR.Value;
                    var patternCtx = WithCountedParameterEnvironments(
                        ctx,
                        patternBindings.CountedBindings,
                        patternBindings.CountedBindings.Select(static binding => binding.Item1));
                    return EvalAlgOutputCounted(callee, patternCtx, valEnv);
                }

                // A flat callee with a top-level rest parameter (`Rows.map(F)`
                // with `F(x, y..., z)` or a rest-only `Collect(items...)`)
                // binds through the shared prefix/rest/suffix binder so the
                // rest parameter COLLECTS an exact immutable list, after the
                // same final-argument row expansion the fixed-only flat path
                // uses below. Rest-only callees keep the whole iterated
                // element as one collected slot.
                if (ParameterPattern.HasVariadicCaptureAtCurrentLevel(callee.ParameterPatterns))
                {
                    var restPatternEnvR = BindCountedCallbackParameterPatternList(callee.ParameterPatterns, args);
                    if (restPatternEnvR.IsError) return restPatternEnvR.Error;

                    var restBindings = restPatternEnvR.Value;
                    var restCtx = WithCountedParameterEnvironments(
                        ctx,
                        restBindings.CountedBindings,
                        restBindings.CountedBindings.Select(static binding => binding.Item1));
                    return EvalAlgOutputCounted(callee, restCtx, valEnv);
                }

                // Fixed-only flat callback binding projects each callback item
                // into slots and binds those slots to the algorithm's flat
                // parameter names (the final item is unpacked across any
                // remaining names); it does not apply item-supply
                // singleton-boundary normalization. Scalar callback
                // deconstruction stays deferred so the counted callback path
                // keeps Lean/C# parity.
                var countedEnvR = BindCountedCallbackParams(callee.Params, args);
                if (countedEnvR.IsError) return countedEnvR.Error;

                var newCtx = WithCountedParameterEnvironments(ctx, countedEnvR.Value, callee.Params);
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
        CountedResult item,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv,
        string calleeName = "conditional")
        => EvalResolvedCallbackCall(callee, [CountedSequenceCallbackItem(item)], ctx, valEnv, calleeName);

    /// <summary>
    /// Counted variant of <see cref="EvalSequenceCallbackCall"/>.
    /// </summary>
    private static EvalResult<CountedResult> EvalSequenceCallbackCallCounted(
        Algorithm callee,
        CountedResult item,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv,
        string calleeName = "conditional")
        => EvalResolvedCallbackCallCounted(callee, [CountedSequenceCallbackItem(item)], ctx, valEnv, calleeName);

    /// <summary>
    /// Evaluate an algorithm's output expressions and count how many top-level
    /// values they emitted at the current algorithm boundary.
    /// A parenthesized sequence-value expression counts as one value, while multiple top-level
    /// output expressions count separately.
    /// Lean: <c>evalAlgOutputCounted</c>.
    /// </summary>
    private static EvalResult<CountedResult> EvalAlgOutputCountedCore(
        Algorithm alg,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        if (alg is Algorithm.Builtin(var builtin))
            return EvalBuiltinValueCounted(builtin);

        var dupProp = alg.FindDuplicatePropName();
        if (dupProp is not null)
            return new EvalError.DuplicateProperty(dupProp);

        if (ConditionalValueAccessError("conditional", alg) is { } conditionalError)
            return conditionalError;

        if (alg is Algorithm.User { Output: { Count: 0 } })
            return new EvalError.MissingOutput();

        var innerCtx = ctx.Push(alg);
        var results = new List<Result>();
        var emittedCount = 0;

        foreach (var expr in alg.Output)
        {
            var countedR = EvalCounted(expr, innerCtx, valEnv);
            if (countedR.IsError) return countedR.Error;

            if (expr is Expr.SequenceSpread)
            {
                AddCountedTopLevelValues(results, countedR.Value);
                emittedCount += countedR.Value.EmittedCount;
                continue;
            }

            // A non-spread output expression is always one visible output slot,
            // even when it evaluates to the empty sequence value `()`. Only an
            // explicit spread opens a sequence and can contribute zero items.
            results.Add(countedR.Value.Value);
            emittedCount += countedR.Value.EmittedCount == 0 ? 1 : countedR.Value.EmittedCount;
        }

        return EvalResult<CountedResult>.Ok(new CountedResult(CombineOutputSlots(results), emittedCount));
    }

    // Combine collected top-level output slots into one value. A single slot is
    // returned as-is so useful sequence structure is preserved; multiple slots
    // form one sequence value. Unlike <see cref="Result.FromItems"/>, this does
    // NOT singleton-collapse or recursively renormalize slot values — slots are
    // already evaluated values.
    private static Result CombineOutputSlots(IReadOnlyList<Result> slots)
        => slots.Count == 1 ? slots[0] : new Result.SequenceValue(slots);

    // Materialize a collection-producing builtin's kept/projected items as ONE
    // exact immutable list value. Unlike canonical arity capture (ordinary
    // construction via <see cref="Result.Normalize"/>,
    // <see cref="CombineOutputSlots"/>), the list boundary is exact:
    // zero items form `[]`, a single kept item forms `[item]` (the one-item
    // collection boundary is NEVER erased, so `take(((1, 2), (3, 4)), 1)`
    // yields `[(1, 2)]`), and item internals are never renormalized, dropped,
    // or flattened — nested sequence values and nested list values stay exact
    // elements. The emitted count is always 1: a list value is one visible
    // value (<see cref="Result.ValueCount"/>), including the empty list `[]`.
    // The items array is freshly materialized here, so ownership transfer via
    // <see cref="Result.ListValue.TakeOwnership"/> is safe.
    // Lean: makeCollectionListResult.
    private static CountedResult MakeCollectionListResult(IEnumerable<Result> items)
        => new(Result.ListValue.TakeOwnership(items.ToArray()), 1);

    // Re-count a counted result at a public property/call/builtin RESULT boundary.
    // A property/call boundary always returns ONE value: the body may internally
    // produce an item supply of count 0, 1, or many, but the caller observes the
    // same structural value with emitted count <see cref="Result.ValueCount"/>
    // (0 for the empty sequence value, otherwise 1). A multi-output body therefore
    // becomes one sequence value at the boundary; only an explicit caller-site
    // postfix `...` re-opens it (via ToItems, which reads the value, not this count).
    //
    // This re-counts without normalizing or rebuilding the value; ordinary value
    // construction has already canonicalized redundant unary empty structure.
    // It is applied only to public result boundaries, never to internal
    // body/root output accumulation (EvalAlgOutputCountedCore) or to multi-slot
    // while/repeat loop state, both of which must keep their multi-item counts.
    // (Rest bindings need no re-count: CollectRest stores one exact list with
    // emitted count 1.) Lexical zero-arg property access (EvalCounted
    // Expr.Resolve) and the `if` builtin already perform this same re-count
    // inline; this helper generalizes it.
    // Lean: reCountValueBoundary.
    private static CountedResult ReCountValueBoundary(CountedResult r)
        => new(r.Value, r.Value.ValueCount());

    // Re-count a successful counted result at a public boundary, propagating errors
    // unchanged. Convenience overload for the call/access dispatch sites.
    private static EvalResult<CountedResult> ReCountValueBoundary(EvalResult<CountedResult> r)
        => r.IsError ? r.Error : EvalResult<CountedResult>.Ok(ReCountValueBoundary(r.Value));

    private static EvalResult<CountedResult> EvalAlgOutputCounted(
        Algorithm alg,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
        => EvalAlgOutputCountedCore(alg, ctx, valEnv);

    private static EvalResult<CountedResult> EvalProgramOutputCounted(
        Algorithm alg,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
        => EvalAlgOutputCountedCore(alg, ctx, valEnv);

    // No builtin is valid as a bare zero-argument value; every builtin requires
    // a call. (The empty sequence value is written `()`, not a builtin.)
    private static EvalResult<CountedResult> EvalBuiltinValueCounted(BuiltinId builtin)
        => WrongBuiltinArity(builtin, 0);

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
                ValueEnvironmentCacheIdentity(valEnv),
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
        var newCtx = WithCountedParameterEnvironments(
            ctx.Push(callee),
            bindings,
            bindings.Select(static binding => binding.Item1));
        var newEnv = Concat(bindings.Select(static binding => (binding.Item1, binding.Item2.Value)).ToList(), valEnv);
        return EvalAlgOutputCounted(wiredBody, newCtx, newEnv);
    }

    private static bool ReducerAccumulatorSideHasTopLevelVariadic(Algorithm.User reducer)
    {
        try
        {
            var signature = CallableSignature.FromUserAlgorithm("reduce step", reducer);
            var plan = CallableBindingPlan.FromSignature(signature);
            return plan.TopLevelPatternList.Nodes
                .Skip(1)
                .Any(static node => node is VariadicCaptureBindingNode { IsTopLevel: true });
        }
        catch (InvalidOperationException)
        {
            return false;
        }
    }

    private static EvalResult<CountedResult> EvalReducerAccumulatorVariadicCallbackCallCounted(
        Algorithm.User callee,
        IReadOnlyList<CountedResult> args,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        if (callee.Output.Count == 0)
            return new EvalError.MissingOutput();

        var countedPatternEnvR = BindCountedParameterPatternList(
            callee.ParameterPatterns,
            args,
            (required, actual) => new EvalError.ArityMismatch(required, actual));
        if (countedPatternEnvR.IsError) return countedPatternEnvR.Error;

        var patternBindings = countedPatternEnvR.Value;
        var callbackCtx = WithCountedParameterEnvironments(
            ctx,
            patternBindings.CountedBindings,
            patternBindings.CountedBindings.Select(static binding => binding.Item1));
        return EvalAlgOutputCounted(callee, callbackCtx, valEnv);
    }

    /// <summary>
    /// Evaluate a <c>reduce</c> step on one collected iteration item. Reducers
    /// with a top-level variadic accumulator parameter bind accumulator state
    /// slots like loop state; other reducers keep ordinary structural
    /// accumulator binding.
    /// </summary>
    private static EvalResult<CountedResult> EvalSequenceReduceStepCounted(
        Algorithm callee,
        CountedResult element,
        Result accumulator,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv,
        string calleeName = "conditional")
    {
        var elementArg = CountedSequenceCallbackItem(element);
        if (callee is Algorithm.User userReducer && ReducerAccumulatorSideHasTopLevelVariadic(userReducer))
        {
            var accumulatorSlots = accumulator.ToItems();
            var args = new List<CountedResult>(1 + accumulatorSlots.Count) { elementArg };
            foreach (var slot in accumulatorSlots)
                args.Add(new CountedResult(slot, slot.ValueCount()));

            return EvalReducerAccumulatorVariadicCallbackCallCounted(userReducer, args, ctx, valEnv);
        }

        return EvalResolvedCallbackCallCounted(
            callee,
            [elementArg, new CountedResult(accumulator, accumulator.ValueCount())],
            ctx,
            valEnv,
            calleeName);
    }

    /// <summary>
    /// Recover the top-level values emitted at one algorithm boundary from a
    /// counted result.
    /// A sequence value emitted as one top-level result stays intact, while a
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

    private static List<Expr> SequenceConstructLeaves(Expr expr)
    {
        var leaves = new List<Expr>();
        var stack = new Stack<Expr>();
        stack.Push(expr);

        while (stack.Count != 0)
        {
            var current = stack.Pop();
            if (current is Expr.SequenceConstruct(var left, var right))
            {
                stack.Push(right);
                stack.Push(left);
                continue;
            }

            leaves.Add(current);
        }

        return leaves;
    }

    /// <summary>
    /// Evaluate the INTERNAL <see cref="Expr.SequenceConstruct"/> join node as
    /// one sequence value. Join semantics, not written-parentheses semantics:
    /// a non-spread leaf whose value is <c>()</c> contributes NO item (an
    /// empty join contribution), a spread leaf splices its operand's items,
    /// and the result is recursively normalized. Written parentheses parse to
    /// <see cref="Expr.Block"/> and always keep a non-spread <c>()</c> item
    /// visible — surface syntax must never route through this node
    /// (enforced by <c>SequenceConstructContainmentTests</c>).
    /// Lean: <c>evalSequenceConstructCounted</c>; plain evaluation is this
    /// function's value projection on both sides.
    /// </summary>
    private static EvalResult<CountedResult> EvalSequenceConstructCounted(
        Expr expr,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var leaves = SequenceConstructLeaves(expr);
        var items = new List<Result>(leaves.Count);

        foreach (var leaf in leaves)
        {
            if (leaf is Expr.SequenceSpread)
            {
                var suppliedItemsR = EvalSequenceSpreadOperandItems(leaf, ctx, valEnv);
                if (suppliedItemsR.IsError) return suppliedItemsR.Error;

                items.AddRange(suppliedItemsR.Value);
                continue;
            }

            var valueR = Eval(leaf, ctx, valEnv);
            if (valueR.IsError) return valueR.Error;

            if (valueR.Value.ValueCount() != 0)
                items.Add(valueR.Value);
        }

        var value = Result.FromItems(items);
        return EvalResult<CountedResult>.Ok(new CountedResult(
            value,
            value.ValueCount()));
    }

    private static EvalError SpreadMissingOutput(SourceSpan? span)
        => new EvalError.SpreadMissingOutput() { Span = span };

    private static bool IsMissingOutputError(EvalError error) => error switch
    {
        EvalError.MissingOutput => true,
        EvalError.WithContext(_, var inner) => IsMissingOutputError(inner),
        _ => false,
    };

    private static EvalResult<IReadOnlyList<Result>> EvalAlgorithmOutputSequenceSpreadItems(
        Algorithm alg,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv,
        SourceSpan? span)
    {
        if (alg is Algorithm.Builtin(var builtin))
        {
            var builtinR = EvalBuiltinValueCounted(builtin);
            return builtinR.IsError
                ? builtinR.Error
                : EvalResult<IReadOnlyList<Result>>.Ok(CountedTopLevelValues(builtinR.Value));
        }

        var dupProp = alg.FindDuplicatePropName();
        if (dupProp is not null)
            return new EvalError.DuplicateProperty(dupProp);

        if (ConditionalValueAccessError("conditional", alg) is { } conditionalError)
            return conditionalError;

        if (alg is Algorithm.User { Output.Count: 0 })
            return SpreadMissingOutput(span);

        var innerCtx = ctx.Push(alg);
        var items = new List<Result>();

        foreach (var expr in alg.Output)
        {
            var countedR = EvalCounted(expr, innerCtx, valEnv);
            if (countedR.IsError)
                return IsMissingOutputError(countedR.Error)
                    ? SpreadMissingOutput(expr.Span ?? span)
                    : countedR.Error;

            AddCountedTopLevelValues(items, countedR.Value);
        }

        return EvalResult<IReadOnlyList<Result>>.Ok(items);
    }

    private static EvalResult<IReadOnlyList<Result>> EvalSequenceSpreadOperandItems(
        Expr expr,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        if (expr is Expr.Block(var alg))
        {
            var wired = WireToCaller(ctx, alg);
            var blockSpan = expr.Span ?? FirstSpan(wired.Output);
            if (wired.Params.Count != 0)
                return MissingImplicitArguments<IReadOnlyList<Result>>(wired.Params, blockSpan);

            var blockR = EvalAlgOutput(wired, ctx, valEnv);
            if (blockR.IsError)
                return IsMissingOutputError(blockR.Error)
                    ? SpreadMissingOutput(blockSpan)
                    : blockR.Error;

            return EvalResult<IReadOnlyList<Result>>.Ok(blockR.Value.SpreadItems());
        }

        var outputR = Eval(expr, ctx, valEnv);
        if (outputR.IsError)
            return IsMissingOutputError(outputR.Error)
                ? SpreadMissingOutput(expr.Span)
                : outputR.Error;

        return EvalResult<IReadOnlyList<Result>>.Ok(outputR.Value.SpreadItems());
    }

    // Evaluate a unary `sequenceSpread` node by evaluating its single operand
    // once and spreading immediate top-level items. Directly-nested spreads
    // (`A......`) are unwrapped iteratively (stack-safe for deep nesting) and
    // then each written layer is applied COMPOSITIONALLY: every `...` opens
    // exactly one boundary of the value the previous layer would have
    // captured, so `A......` agrees with `(A...)...`. For sequence values the
    // extra layers are fixed points (value-equivalent to a single spread);
    // for exact LIST values each layer opens one more list boundary
    // (`[[7]]......` supplies `7`). Lean: evalSequenceSpreadCounted.
    private static EvalResult<CountedResult> EvalSequenceSpreadCounted(
        Expr expr,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var operand = expr;
        var layers = 0;
        while (operand is Expr.SequenceSpread(var supplied))
        {
            operand = supplied;
            layers++;
        }

        var operandR = EvalSequenceSpreadOperandItems(operand, ctx, valEnv);
        if (operandR.IsError) return operandR.Error;

        var items = operandR.Value;
        for (var layer = 1; layer < layers; layer++)
            items = Result.FromItems(items).SpreadItems();

        return EvalResult<CountedResult>.Ok(new CountedResult(
            Result.FromItems(items),
            items.Count));
    }

    /// <summary>
    /// Evaluate a surface list literal <c>[e1, ..., en]</c> as exactly ONE
    /// exact immutable list value. Element slots reuse the written-parentheses
    /// expression-list slot rules (<see cref="EvalExplicitSequenceValueExprSlots"/>):
    /// an explicit spread slot opens its operand's immediate items into the
    /// list being constructed (an empty spread contributes no elements), a
    /// non-spread slot is one element even when it evaluates to the empty
    /// sequence value <c>()</c>, and a nested zero-parameter block is one
    /// written grouping level. Unlike sequence construction the collected
    /// elements are stored EXACTLY: no singleton erasure and no empty
    /// canonicalization, so <c>[7]</c>, <c>[[7]]</c>, <c>[]</c>, and
    /// <c>[()]</c> are all distinct list values. A list literal always emits
    /// one value.
    /// Lean: <c>evalListLiteralCounted</c>; plain <c>Eval</c> is this
    /// function's value projection on both sides.
    /// </summary>
    private static EvalResult<CountedResult> EvalListLiteralCounted(
        IReadOnlyList<Expr> elements,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var items = new List<Result>();
        foreach (var element in elements)
        {
            var slotsR = EvalExplicitSequenceValueExprSlots(element, ctx, valEnv);
            if (slotsR.IsError) return slotsR.Error;
            items.AddRange(slotsR.Value);
        }

        return EvalResult<CountedResult>.Ok(new CountedResult(
            Result.ListValue.TakeOwnership(items.ToArray()), 1));
    }

    private readonly record struct BoundSequenceBuiltinArguments(
        PreparedSequenceBuiltinInput PreparedInput,
        IReadOnlyList<CountedResult> IterationItems,
        IReadOnlyList<PreparedSequenceBuiltinSuffixArg> SuffixArgs);

    private static IReadOnlyList<ResolvedArgumentAlgorithm> WithoutSequenceSpread(
        IReadOnlyList<Algorithm> args)
        => args.Select(static arg => new ResolvedArgumentAlgorithm(arg, SpreadsSequence: false)).ToList();

    private static EvalResult<IReadOnlyList<VariadicCallItem>> BuildCallableCallItems(
        IReadOnlyList<ResolvedArgumentAlgorithm> args,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var items = new List<VariadicCallItem>();
        foreach (var resolvedArg in args)
        {
            var arg = resolvedArg.Algorithm;

            // A callback/function argument (one that declares parameters) is applied
            // per element by the consuming sequence builtin, never used as a value
            // here. Its parameters are unbound at this collection point, so evaluating
            // its body standalone would resolve those parameter names against the
            // surrounding scope. When a sibling argument shares a parameter name and
            // was deferred as a self-referential thunk, that stray lookup re-enters the
            // same builtin call and recurses without ever settling on a value. Keep the
            // algorithm unevaluated so it can be applied with bound parameters later;
            // only value-shaped arguments (no parameters) are materialized eagerly.
            if (arg.Params.Count > 0 || arg.ParameterPatterns.Count > 0)
            {
                items.Add(new VariadicCallItem(Value: null, arg, ValueError: null));
                continue;
            }

            var outputR = EvalAlgOutputCounted(arg, ctx, valEnv);
            if (outputR.IsOk)
            {
                if (resolvedArg.SpreadsSequence)
                {
                    foreach (var value in CountedTopLevelValues(outputR.Value))
                        items.Add(new VariadicCallItem(value, arg, ValueError: null));
                }
                else
                {
                    items.Add(new VariadicCallItem(outputR.Value.Value, arg, ValueError: null));
                }

                continue;
            }

            items.Add(new VariadicCallItem(Value: null, arg, outputR.Error));
        }

        return EvalResult<IReadOnlyList<VariadicCallItem>>.Ok(items);
    }

    private static EvalResult<PreparedSequenceBuiltinSuffixArg> PrepareSequenceBuiltinSuffixArg(
        BuiltinId builtin,
        SequenceBuiltinSuffixArgDescriptor descriptor,
        VariadicCallItem item,
        EvalCtx ctx)
    {
        switch (descriptor.Kind)
        {
            case SequenceBuiltinSuffixArgKind.Algorithm:
                if (item.Algorithm is not null)
                {
                    return EvalResult<PreparedSequenceBuiltinSuffixArg>.Ok(
                        new PreparedSequenceBuiltinSuffixArg.AlgorithmArg(
                            NormalizeSequenceCallableSuffixAlgorithm(item.Algorithm, ctx)));
                }

                return item.ValueError ?? new EvalError.WithContext(
                    SequenceBuiltinSuffixArgErrorContext(builtin, descriptor),
                    new EvalError.BadArity());

            case SequenceBuiltinSuffixArgKind.Value:
                if (item.Value is not null)
                {
                    return EvalResult<PreparedSequenceBuiltinSuffixArg>.Ok(
                        new PreparedSequenceBuiltinSuffixArg.ValueArg(item.Value));
                }

                return item.ValueError ?? new EvalError.WithContext(
                    SequenceBuiltinSuffixArgErrorContext(builtin, descriptor),
                    new EvalError.BadArity());

            case SequenceBuiltinSuffixArgKind.WholeNumber:
            {
                if (item.Value is null)
                    return item.ValueError ?? new EvalError.WithContext(
                        SequenceBuiltinSuffixArgErrorContext(builtin, descriptor),
                        new EvalError.BadArity());

                var numeric = item.Value.SingleAtomicNumber();
                if (numeric is null || numeric.Value != Math.Truncate(numeric.Value))
                {
                    return new EvalError.WithContext(
                        SequenceBuiltinSuffixArgErrorContext(builtin, descriptor),
                        new EvalError.BadArity());
                }

                return EvalResult<PreparedSequenceBuiltinSuffixArg>.Ok(
                    new PreparedSequenceBuiltinSuffixArg.WholeNumberArg(numeric.Value));
            }

            default:
                return InternalSequenceBuiltinSuffixArgMetadataError<PreparedSequenceBuiltinSuffixArg>(
                    builtin,
                    "used an unknown suffix-argument kind");
        }
    }

    private static Algorithm NormalizeSequenceCallableSuffixAlgorithm(Algorithm algorithm, EvalCtx ctx)
    {
        if (algorithm is Algorithm.User { Params.Count: 0, Output.Count: 1 } user
            && user.Output[0] is Expr.Resolve(var name) resolve)
        {
            var resolvedR = ResolveNamedAlgorithm(name, resolve.Span, ctx);
            if (resolvedR.IsOk)
                return resolvedR.Value;
        }

        return algorithm;
    }

    private static EvalResult<IReadOnlyList<CountedResult>> EvalSequenceIterationItems(
        IReadOnlyList<Algorithm> collectionArgs,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
        => EvalSequenceIterationItems(WithoutSequenceSpread(collectionArgs), ctx, valEnv);

    private static EvalResult<IReadOnlyList<CountedResult>> EvalSequenceIterationItems(
        IReadOnlyList<ResolvedArgumentAlgorithm> collectionArgs,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var itemsR = BuildCallableCallItems(collectionArgs, ctx, valEnv);
        if (itemsR.IsError) return itemsR.Error;

        var items = new List<CountedResult>(itemsR.Value.Count);
        foreach (var item in itemsR.Value)
        {
            if (item.Value is null && item.ValueError is null)
                continue;

            if (item.Value is null)
                return item.ValueError ?? new EvalError.BadArity();

            items.Add(new CountedResult(item.Value, 1));
        }

        return EvalResult<IReadOnlyList<CountedResult>>.Ok(items);
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
        Result.SequenceValue(var items) when items.Count == 0 => "empty sequence value",
        Result.SequenceValue => "sequence value",
        Result.ListValue(var items) when items.Count == 0 => "empty list value",
        Result.ListValue => "list value",
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
    /// Evaluate <c>reduce(collection, reducer, initial)</c> while
    /// preserving the accumulator's emitted-value count for the empty-sequence
    /// case. The fixed <c>collection</c> argument supplies the items through
    /// the post-binding collection view; the reducer and initial accumulator
    /// are fixed control arguments.
    /// The current item is passed to the reducer exactly as collected;
    /// nested sequence values stay intact.
    /// Normal accumulator parameters keep ordinary structural semantics; a
    /// top-level variadic accumulator parameter receives accumulator state
    /// slots.
    /// Lean: <c>evalReduceCounted</c>.
    /// </summary>
    private static EvalResult<CountedResult> EvalReduceCounted(
        IReadOnlyList<CountedResult> items,
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
                "while evaluating reduce step (reduce passes each iterated collection item as collected; sequence parameters use values... top-level binding, nested sequence values stay intact, and top-level variadic accumulator parameters receive state slots)",
                EvalSequenceReduceStepCounted(stepAlg, item, accumulator.Value, ctx, valEnv, "reduce step"));
            if (stepR.IsError) return stepR.Error;

            var nextR = ExpectSingleAccumulator(stepR.Value);
            if (nextR.IsError) return nextR.Error;

            accumulator = new CountedResult(nextR.Value, 1);
        }

        return EvalResult<CountedResult>.Ok(accumulator);
    }

    /// <summary>
    /// Evaluate <c>filter(collection, predicate)</c>. The fixed
    /// <c>collection</c> argument supplies the items through the post-binding
    /// collection view, and <c>predicate</c> is a fixed control argument.
    /// Each iterated item is passed to the predicate exactly as collected;
    /// nested sequence values and nested list values stay intact.
    /// The kept items remain the original collection items and are
    /// materialized as one exact immutable list value.
    /// </summary>
    private static EvalResult<CountedResult> EvalFilterCounted(
        IReadOnlyList<CountedResult> items,
        Algorithm predicateAlg,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var kept = new List<Result>();
        for (var index = 0; index < items.Count; index++)
        {
            var item = items[index];
            var truthR = EvalFilterPredicateTruth(predicateAlg, item, index, ctx, valEnv);
            if (truthR.IsError)
                return truthR.Error;

            if (truthR.Value)
                kept.Add(item.Value);
        }

        return EvalResult<CountedResult>.Ok(MakeCollectionListResult(kept));
    }

    /// <summary>
    /// Evaluate a filter predicate with the same callback and truthiness rules
    /// used by generic <c>filter</c>; sequence optimizers call this to avoid
    /// duplicating callback semantics.
    /// </summary>
    internal static EvalResult<bool> EvalFilterPredicateTruth(
        Algorithm predicateAlg,
        CountedResult item,
        int index,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var predicateR = WithCtx(
            $"while evaluating filter predicate for item {index}: {FormatResultForDiagnostic(item.Value)} (filter passes each iterated collection item as collected; sequence parameters use values... top-level binding and nested sequence values stay intact)",
            EvalSequenceCallbackCall(predicateAlg, item, ctx, valEnv, "filter predicate"));
        if (predicateR.IsError)
            return predicateR.Error;

        var truth = predicateR.Value.SingleAtomicTruthValue();
        if (truth is null)
        {
            return new EvalError.WithContext(
                "filter predicate must return exactly one atomic numeric value",
                new EvalError.BadArity());
        }

        return EvalResult<bool>.Ok(truth.Value);
    }

    /// <summary>
    /// Evaluate <c>map(collection, mapper)</c> while preserving the number of
    /// top-level mapped elements. <c>mapper</c> is a fixed control argument.
    /// Each callback item is passed to the mapper exactly as collected from
    /// the post-binding collection view; nested sequence values and
    /// nested list values stay intact. Each captured callback result becomes
    /// one element of the exact immutable list result (mapped elements are
    /// never flattened into the outer list).
    /// Lean: <c>evalMapCounted</c>.
    /// </summary>
    private static EvalResult<CountedResult> EvalMapCounted(
        IReadOnlyList<CountedResult> items,
        Algorithm transformAlg,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var mapped = new List<Result>(items.Count);
        foreach (var item in items)
        {
            var transformR = WithCtx(
                "while evaluating map transform (map passes each iterated collection item as collected; sequence parameters use values... top-level binding and nested sequence values stay intact)",
                EvalSequenceCallbackCallCounted(transformAlg, item, ctx, valEnv, "map transform"));
            if (transformR.IsError) return transformR.Error;

            var mappedElementR = ExpectSingleMappedElement(transformR.Value);
            if (mappedElementR.IsError) return mappedElementR.Error;

            mapped.Add(mappedElementR.Value);
        }

        return EvalResult<CountedResult>.Ok(MakeCollectionListResult(mapped));
    }

    /// <summary>
    /// Collect top-level sequence items as single atomic numeric values.
    /// Used by numeric ordering and aggregation builtins that only accept
    /// clearly comparable numeric elements and reject strings or sequence values.
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

    private static string DescribeSequenceBuiltinSuffixArgRequirement(
        SequenceBuiltinSuffixArgKind kind)
        => kind switch
        {
            SequenceBuiltinSuffixArgKind.Algorithm => "an algorithm",
            SequenceBuiltinSuffixArgKind.Value => "exactly one value",
            SequenceBuiltinSuffixArgKind.WholeNumber => "exactly one whole-number value",
            _ => "a valid suffix argument",
        };

    private static string DescribeSequenceBuiltinSuffixArgKind(
        SequenceBuiltinSuffixArgKind kind)
        => kind switch
        {
            SequenceBuiltinSuffixArgKind.Algorithm => "algorithm",
            SequenceBuiltinSuffixArgKind.Value => "value",
            SequenceBuiltinSuffixArgKind.WholeNumber => "whole-number value",
            _ => "unknown",
        };

    private static string SequenceBuiltinSuffixArgErrorContext(
        BuiltinId builtin,
        SequenceBuiltinSuffixArgDescriptor descriptor)
        => $"{BuiltinDisplayName(builtin)} {descriptor.Name} must be {DescribeSequenceBuiltinSuffixArgRequirement(descriptor.Kind)}";

    private static EvalResult<T> InternalSequenceBuiltinSuffixArgMetadataError<T>(
        BuiltinId builtin,
        string detail)
        => new EvalError.WithContext(
            $"internal sequence metadata for {BuiltinDisplayName(builtin)} {detail}",
            new EvalError.BadArity());

    private static EvalResult<BoundSequenceBuiltinArguments> BindSequenceBuiltinArguments(
        BuiltinId builtin,
        SequenceBuiltinMetadata metadata,
        IReadOnlyList<ResolvedArgumentAlgorithm> args,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var descriptor = BuiltinRegistry.GetBuiltin(builtin);
        var signature = descriptor.PlainSignature;
        var itemsR = BuildCallableCallItems(args, ctx, valEnv);
        if (itemsR.IsError) return itemsR.Error;

        // A collection builtin is an ordinary fixed-arity callable: exactly one
        // collection argument followed by its fixed control arguments
        // (`count(collection)`, `take(collection, count)`,
        // `map(collection, mapper)`). An unspread sequence or list value is ONE
        // argument at this call boundary, exactly like at every other call
        // boundary; only explicit caller-site spread alters argument
        // boundaries, and the spread-opened items obey the same fixed arity
        // (`count([1, 2, 3]...)` supplies three arguments and is an arity
        // error). Nothing is opened before binding.
        var items = itemsR.Value;
        var expectedArgCount = 1 + metadata.SuffixArgs.Count;
        if (items.Count != expectedArgCount)
        {
            return new EvalError.ArityMismatch(expectedArgCount, items.Count)
            {
                Signature = signature,
            };
        }

        var collectionItem = items[0];
        if (collectionItem.Value is null)
            return collectionItem.ValueError ?? new EvalError.BadArity();

        // The one-level builtin collection view applies AFTER binding, to the
        // bound collection value only: a lone sequence or exact list value
        // opens to its immediate items, and any other value is a one-element
        // collection (`count(7)` is 1). Opening is never recursive — nested
        // sequence/list elements stay intact as single items.
        var collectionValues = BuiltinCollectionItems(collectionItem.Value);

        var collected = new CollectedSequenceBuiltinInput([collectionValues], collectionValues);
        var preparedInputR = PrepareSequenceBuiltinInput(builtin, metadata, collected);
        if (preparedInputR.IsError) return preparedInputR.Error;

        var suffixArgs = new List<PreparedSequenceBuiltinSuffixArg>(metadata.SuffixArgs.Count);
        for (var index = 0; index < metadata.SuffixArgs.Count; index++)
        {
            var preparedArgR = PrepareSequenceBuiltinSuffixArg(
                builtin,
                metadata.SuffixArgs[index],
                items[1 + index],
                ctx);
            if (preparedArgR.IsError) return preparedArgR.Error;

            suffixArgs.Add(preparedArgR.Value);
        }

        var iterationItems = collectionValues
            .Select(static value => new CountedResult(value, 1))
            .ToList();

        return EvalResult<BoundSequenceBuiltinArguments>.Ok(
            new BoundSequenceBuiltinArguments(preparedInputR.Value, iterationItems, suffixArgs));
    }

    private static EvalResult<T> ExpectPreparedSequenceBuiltinSuffixArgAt<T>(
        BuiltinId builtin,
        IReadOnlyList<SequenceBuiltinSuffixArgDescriptor> descriptors,
        IReadOnlyList<PreparedSequenceBuiltinSuffixArg> args,
        int index,
        SequenceBuiltinSuffixArgKind expectedKind,
        Func<SequenceBuiltinSuffixArgDescriptor, PreparedSequenceBuiltinSuffixArg, EvalResult<T>> projector)
    {
        if (descriptors.Count != args.Count)
        {
            return InternalSequenceBuiltinSuffixArgMetadataError<T>(
                builtin,
                "mismatched suffix arguments");
        }

        if ((uint)index >= (uint)descriptors.Count)
        {
            return InternalSequenceBuiltinSuffixArgMetadataError<T>(
                builtin,
                $"expected suffix argument {index + 1} to have metadata kind {DescribeSequenceBuiltinSuffixArgKind(expectedKind)}");
        }

        var descriptor = descriptors[index];
        if (descriptor.Kind != expectedKind)
        {
            return InternalSequenceBuiltinSuffixArgMetadataError<T>(
                builtin,
                $"expected suffix argument {index + 1} ({descriptor.Name}) to have metadata kind {DescribeSequenceBuiltinSuffixArgKind(expectedKind)}, but found {DescribeSequenceBuiltinSuffixArgKind(descriptor.Kind)}");
        }

        return projector(descriptor, args[index]);
    }

    private static EvalResult<Algorithm> ExpectPreparedAlgorithmSuffixArg(
        BuiltinId builtin,
        IReadOnlyList<SequenceBuiltinSuffixArgDescriptor> descriptors,
        IReadOnlyList<PreparedSequenceBuiltinSuffixArg> args,
        int index)
        => ExpectPreparedSequenceBuiltinSuffixArgAt(
            builtin,
            descriptors,
            args,
            index,
            SequenceBuiltinSuffixArgKind.Algorithm,
            (descriptor, arg) => arg is PreparedSequenceBuiltinSuffixArg.AlgorithmArg(var algorithm)
                ? EvalResult<Algorithm>.Ok(algorithm)
                : InternalSequenceBuiltinSuffixArgMetadataError<Algorithm>(
                    builtin,
                    $"prepared suffix argument {index + 1} ({descriptor.Name}) did not match metadata kind {DescribeSequenceBuiltinSuffixArgKind(SequenceBuiltinSuffixArgKind.Algorithm)}"));

    private static EvalResult<decimal> ExpectPreparedWholeNumberSuffixArg(
        BuiltinId builtin,
        IReadOnlyList<SequenceBuiltinSuffixArgDescriptor> descriptors,
        IReadOnlyList<PreparedSequenceBuiltinSuffixArg> args,
        int index)
        => ExpectPreparedSequenceBuiltinSuffixArgAt(
            builtin,
            descriptors,
            args,
            index,
            SequenceBuiltinSuffixArgKind.WholeNumber,
            (descriptor, arg) => arg is PreparedSequenceBuiltinSuffixArg.WholeNumberArg(var value)
                ? EvalResult<decimal>.Ok(value)
                : InternalSequenceBuiltinSuffixArgMetadataError<decimal>(
                    builtin,
                    $"prepared suffix argument {index + 1} ({descriptor.Name}) did not match metadata kind {DescribeSequenceBuiltinSuffixArgKind(SequenceBuiltinSuffixArgKind.WholeNumber)}"));

    private static EvalResult<Result> ExpectPreparedValueSuffixArg(
        BuiltinId builtin,
        IReadOnlyList<SequenceBuiltinSuffixArgDescriptor> descriptors,
        IReadOnlyList<PreparedSequenceBuiltinSuffixArg> args,
        int index)
        => ExpectPreparedSequenceBuiltinSuffixArgAt(
            builtin,
            descriptors,
            args,
            index,
            SequenceBuiltinSuffixArgKind.Value,
            (descriptor, arg) => arg is PreparedSequenceBuiltinSuffixArg.ValueArg(var value)
                ? EvalResult<Result>.Ok(value)
                : InternalSequenceBuiltinSuffixArgMetadataError<Result>(
                    builtin,
                    $"prepared suffix argument {index + 1} ({descriptor.Name}) did not match metadata kind {DescribeSequenceBuiltinSuffixArgKind(SequenceBuiltinSuffixArgKind.Value)}"));

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
    /// Evaluate <c>order(collection)</c> by eagerly sorting the top-level numeric
    /// collection items in ascending order and materializing them as one exact
    /// immutable list value.
    /// Duplicates are preserved, sequence values are not flattened, strings are
    /// rejected, and empty collections yield the empty list <c>[]</c>.
    /// </summary>
    private static EvalResult<CountedResult> EvalOrderCounted(
        IReadOnlyList<decimal> numbers)
    {
        var sorted = numbers.ToList();
        sorted.Sort();
        return EvalResult<CountedResult>.Ok(MakeCollectionListResult(
            sorted.Select(static value => (Result)new Result.Atom(value))));
    }

    /// <summary>
    /// Evaluate <c>orderDesc(collection)</c> by eagerly sorting the top-level
    /// numeric collection items in descending order and materializing them as
    /// one exact immutable list value.
    /// Duplicates are preserved, sequence values are not flattened, strings are
    /// rejected, and empty collections yield the empty list <c>[]</c>.
    /// </summary>
    private static EvalResult<CountedResult> EvalOrderDescCounted(
        IReadOnlyList<decimal> numbers)
    {
        var sorted = numbers.ToList();
        sorted.Sort(static (left, right) => right.CompareTo(left));
        return EvalResult<CountedResult>.Ok(MakeCollectionListResult(
            sorted.Select(static value => (Result)new Result.Atom(value))));
    }

    /// <summary>
    /// Evaluate <c>count(collection)</c> by counting the top-level sequence
    /// elements from left to right.
    /// Each atom, string, or sequence value counts as one top-level element;
    /// sequence values are not flattened or inspected recursively, and empty collections
    /// return <c>0</c>.
    /// Lean: <c>evalCountCounted</c>.
    /// </summary>
    private static EvalResult<CountedResult> EvalCountCounted(
        IReadOnlyList<Result> items)
        => EvalResult<CountedResult>.Ok(new CountedResult(new Result.Atom(items.Count), 1));

    /// <summary>
    /// Evaluate <c>contains(collection, item)</c> by checking whether any
    /// extracted top-level item equals the searched suffix item under ordinary
    /// KatLang value semantics.
    /// Search is top-level only: sequence values compare structurally as single
    /// items and are not searched recursively.
    /// </summary>
    private static EvalResult<CountedResult> EvalContainsCounted(
        IReadOnlyList<Result> items,
        Result searchedItem)
        => EvalResult<CountedResult>.Ok(new CountedResult(
            new Result.Atom(items.Any(item => Result.ValueComparer.Equals(item, searchedItem)) ? 1 : 0),
            1));

    /// <summary>
    /// Evaluate <c>distinct(collection)</c> by removing later duplicate top-level
    /// items while preserving the original order of first occurrence, then
    /// materializing the kept items as one exact immutable list value.
    /// Duplicate detection follows KatLang value
    /// semantics, so atoms compare by numeric value, strings by exact string
    /// value, and sequence/list values structurally by their elements.
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

        return EvalResult<CountedResult>.Ok(MakeCollectionListResult(distinctItems));
    }

    /// <summary>
    /// Evaluate <c>first(collection)</c> by returning the first top-level
    /// collection element unchanged.
    /// Atoms, strings, and sequence values each count as one top-level element;
    /// sequence values are preserved whole, and the collection must be non-empty.
    /// </summary>
    private static EvalResult<CountedResult> EvalFirstCounted(
        IReadOnlyList<Result> items)
    {
        if (items.Count == 0)
            return new EvalError.BadArity();

        return EvalResult<CountedResult>.Ok(new CountedResult(items[0], 1));
    }

    /// <summary>
    /// Evaluate <c>last(collection)</c> by returning the last top-level
    /// collection element unchanged.
    /// Atoms, strings, and sequence values each count as one top-level element;
    /// sequence values are preserved whole, and the collection must be non-empty.
    /// </summary>
    private static EvalResult<CountedResult> EvalLastCounted(
        IReadOnlyList<Result> items)
    {
        if (items.Count == 0)
            return new EvalError.BadArity();

        return EvalResult<CountedResult>.Ok(new CountedResult(items[^1], 1));
    }

    /// <summary>
    /// Evaluate <c>take(collection, count)</c> by returning the first
    /// <paramref name="count"/> extracted top-level items as one exact
    /// immutable list value. <paramref name="count"/> is a suffix parameter.
    /// Non-positive counts return the empty list <c>[]</c>, oversized counts
    /// return all items, nested sequence/list values stay intact as exact
    /// elements, and original order is preserved.
    /// </summary>
    private static EvalResult<CountedResult> EvalTakeCounted(
        IReadOnlyList<Result> items,
        decimal count)
    {
        IReadOnlyList<Result> taken = count <= 0
            ? []
            : items.Take((int)count).ToList();

        return EvalResult<CountedResult>.Ok(MakeCollectionListResult(taken));
    }

    /// <summary>
    /// Evaluate <c>skip(collection, count)</c> by returning the extracted
    /// top-level items after the first <paramref name="count"/> items as one
    /// exact immutable list value.
    /// <paramref name="count"/> is a suffix parameter. Non-positive counts keep
    /// all items, oversized counts return the empty list <c>[]</c>, nested
    /// sequence/list values stay intact as exact elements, and original order
    /// is preserved.
    /// </summary>
    private static EvalResult<CountedResult> EvalSkipCounted(
        IReadOnlyList<Result> items,
        decimal count)
    {
        IReadOnlyList<Result> remaining = count <= 0
            ? items.ToList()
            : items.Skip((int)count).ToList();

        return EvalResult<CountedResult>.Ok(MakeCollectionListResult(remaining));
    }

    /// <summary>
    /// Evaluate <c>min(collection)</c> by comparing top-level sequence elements
    /// from left to right and returning the smallest numeric element.
    /// The collection must be non-empty, and each top-level element must be
    /// exactly one atomic numeric value; sequence values are not flattened and strings
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
    /// Evaluate <c>max(collection)</c> by comparing top-level sequence elements
    /// from left to right and returning the largest numeric element.
    /// The collection must be non-empty, and each top-level element must be
    /// exactly one atomic numeric value; sequence values are not flattened and strings
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
    /// Evaluate <c>sum(collection)</c> by adding the top-level sequence elements
    /// from left to right.
    /// Each element must be exactly one atomic numeric value; sequence values are not
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
    /// Evaluate <c>sum(collection)</c> by adding the prepared numeric elements
    /// from left to right.
    /// Lean: <c>evalSumCounted</c>.
    /// </summary>
    private static EvalResult<CountedResult> EvalSumCounted(IReadOnlyList<decimal> numbers)
    {
        var totalR = SumNumbersChecked(numbers);
        if (totalR.IsError) return totalR.Error;

        return EvalResult<CountedResult>.Ok(new CountedResult(new Result.Atom(totalR.Value), 1));
    }

    /// <summary>
    /// Evaluate <c>avg(collection)</c> by averaging the top-level sequence
    /// elements from left to right.
    /// The collection must be non-empty, and each top-level element must be
    /// exactly one atomic numeric value; sequence values are not flattened and strings
    /// are rejected.
    /// The C# decimal runtime returns the true decimal arithmetic mean
    /// (total / count). Lean's Int-only core approximates this with truncation
    /// toward zero (Int.tdiv); that integer approximation is a Lean model
    /// limitation, not the C# runtime contract.
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

        var average = totalR.Value / numbers.Count;
        return EvalResult<CountedResult>.Ok(new CountedResult(new Result.Atom(average), 1));
    }

    private static EvalResult<CountedResult> ApplyBuiltinCountedSequence(
        BuiltinId builtin,
        SequenceBuiltinMetadata metadata,
        IReadOnlyList<ResolvedArgumentAlgorithm> args,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var boundR = BindSequenceBuiltinArguments(builtin, metadata, args, ctx, valEnv);
        if (boundR.IsError) return boundR.Error;

        var bound = boundR.Value;

        EvalResult<CountedResult> WithPreparedFlatItems(
            Func<IReadOnlyList<Result>, EvalResult<CountedResult>> handler)
            => handler(bound.PreparedInput.FlattenedItems);

        EvalResult<CountedResult> WithPreparedNumericItems(
            Func<IReadOnlyList<decimal>, EvalResult<CountedResult>> handler)
        {
            var numbersR = ExpectPreparedNumericItems(builtin, bound.PreparedInput);
            if (numbersR.IsError) return numbersR.Error;

            return handler(numbersR.Value);
        }

        EvalResult<CountedResult> WithPreparedSuffixArgs(
            Func<IReadOnlyList<PreparedSequenceBuiltinSuffixArg>, EvalResult<CountedResult>> handler)
            => handler(bound.SuffixArgs);

        return builtin switch
        {
            BuiltinId.@filter => WithPreparedSuffixArgs(
                    preparedSuffixArgs =>
                    {
                        var predicateR = ExpectPreparedAlgorithmSuffixArg(
                            builtin,
                            metadata.SuffixArgs,
                            preparedSuffixArgs,
                            0);
                        if (predicateR.IsError) return predicateR.Error;

                        return EvalFilterCounted(bound.IterationItems, predicateR.Value, ctx, valEnv);
                    }),
            BuiltinId.@map => WithPreparedSuffixArgs(
                    preparedSuffixArgs =>
                    {
                        var transformR = ExpectPreparedAlgorithmSuffixArg(
                            builtin,
                            metadata.SuffixArgs,
                            preparedSuffixArgs,
                            0);
                        if (transformR.IsError) return transformR.Error;

                        return EvalMapCounted(bound.IterationItems, transformR.Value, ctx, valEnv);
                    }),
            BuiltinId.@order => WithPreparedNumericItems(EvalOrderCounted),
            BuiltinId.@orderDesc => WithPreparedNumericItems(EvalOrderDescCounted),
            BuiltinId.@count => WithPreparedFlatItems(EvalCountCounted),
            BuiltinId.@contains => WithPreparedSuffixArgs(
                    preparedSuffixArgs =>
                    {
                        var searchedItemR = ExpectPreparedValueSuffixArg(
                            builtin,
                            metadata.SuffixArgs,
                            preparedSuffixArgs,
                            0);
                        if (searchedItemR.IsError) return searchedItemR.Error;

                        return WithPreparedFlatItems(items => EvalContainsCounted(items, searchedItemR.Value));
                    }),
            BuiltinId.@distinct => WithPreparedFlatItems(EvalDistinctCounted),
            BuiltinId.@first => WithPreparedFlatItems(EvalFirstCounted),
            BuiltinId.@last => WithPreparedFlatItems(EvalLastCounted),
            BuiltinId.@take => WithPreparedSuffixArgs(
                    preparedSuffixArgs =>
                    {
                        var countR = ExpectPreparedWholeNumberSuffixArg(
                            builtin,
                            metadata.SuffixArgs,
                            preparedSuffixArgs,
                            0);
                        if (countR.IsError) return countR.Error;

                        return WithPreparedFlatItems(items => EvalTakeCounted(items, countR.Value));
                    }),
            BuiltinId.@skip => WithPreparedSuffixArgs(
                    preparedSuffixArgs =>
                    {
                        var countR = ExpectPreparedWholeNumberSuffixArg(
                            builtin,
                            metadata.SuffixArgs,
                            preparedSuffixArgs,
                            0);
                        if (countR.IsError) return countR.Error;

                        return WithPreparedFlatItems(items => EvalSkipCounted(items, countR.Value));
                    }),
            BuiltinId.@min => WithPreparedNumericItems(EvalMinCounted),
            BuiltinId.@max => WithPreparedNumericItems(EvalMaxCounted),
            BuiltinId.@sum => WithPreparedNumericItems(EvalSumCounted),
            BuiltinId.@avg => WithPreparedNumericItems(EvalAvgCounted),
            BuiltinId.@reduce => WithPreparedSuffixArgs(
                    preparedSuffixArgs =>
                    {
                        var stepR = ExpectPreparedAlgorithmSuffixArg(
                            builtin,
                            metadata.SuffixArgs,
                            preparedSuffixArgs,
                            0);
                        if (stepR.IsError) return stepR.Error;

                        var initialR = ExpectPreparedAlgorithmSuffixArg(
                            builtin,
                            metadata.SuffixArgs,
                            preparedSuffixArgs,
                            1);
                        if (initialR.IsError) return initialR.Error;

                        return EvalReduceCounted(bound.IterationItems, stepR.Value, initialR.Value, ctx, valEnv);
                    }),
            _ => WrongBuiltinArity(builtin, args.Count),
        };
    }

    /// <summary>
    /// Builtin application with counted output shape.
    /// Used by <c>reduce</c> so step validation can distinguish sequence-value
    /// accumulator values from multiple top-level outputs.
    /// Lean: <c>applyBuiltinCounted</c>.
    /// </summary>
    private static EvalResult<CountedResult> ApplyBuiltinCounted(
        BuiltinId builtin,
        IReadOnlyList<Algorithm> args,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
        => ApplyBuiltinCountedResolved(builtin, WithoutSequenceSpread(args), ctx, valEnv);

    private static EvalResult<IReadOnlyList<Algorithm>> ExpandSequenceSpreadBuiltinArguments(
        IReadOnlyList<ResolvedArgumentAlgorithm> args,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var expanded = new List<Algorithm>(args.Count);
        foreach (var arg in args)
        {
            if (!arg.SpreadsSequence)
            {
                expanded.Add(arg.Algorithm);
                continue;
            }

            var outputR = EvalAlgOutputCounted(arg.Algorithm, ctx, valEnv);
            if (outputR.IsError) return outputR.Error;

            foreach (var value in CountedTopLevelValues(outputR.Value))
                expanded.Add(CountedArgAlgorithm(new CountedResult(value, 1)));
        }

        return EvalResult<IReadOnlyList<Algorithm>>.Ok(expanded);
    }

    private static EvalResult<CountedResult> ApplyBuiltinCountedResolved(
        BuiltinId builtin,
        IReadOnlyList<ResolvedArgumentAlgorithm> resolvedArgs,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        if (GetSequenceBuiltinMetadata(builtin) is { } metadata)
            return ApplyBuiltinCountedSequence(builtin, metadata, resolvedArgs, ctx, valEnv);

        var expandedArgsR = ExpandSequenceSpreadBuiltinArguments(resolvedArgs, ctx, valEnv);
        if (expandedArgsR.IsError) return expandedArgsR.Error;
        var args = expandedArgsR.Value;

        switch (builtin, args.Count)
        {
            case (BuiltinId.@if, 3):
            {
                var condR = EvalAlgOutput(args[0], ctx, valEnv);
                if (condR.IsError) return condR.Error;
                var truth = condR.Value.TruthValue();
                if (truth is null) return new EvalError.BadArity();

                // The selected branch is one argument expression, so `if` observes
                // it as a single value boundary — exactly like value-position
                // property access. A multi-output branch property such as
                // `X = 1, 2, 3` therefore yields the grouped sequence value
                // `(1, 2, 3)` with emitted count 1, not three separate outputs.
                // Explicit spread (`if(1, X, X)...`) is the way to open it.
                // Unlike `while`/`repeat`, which intentionally preserve multi-slot
                // loop state, `if` re-counts the chosen branch value here.
                var branchR = truth.Value
                    ? EvalAlgOutputCounted(args[1], ctx, valEnv)
                    : EvalAlgOutputCounted(args[2], ctx, valEnv);
                if (branchR.IsError) return branchR.Error;
                return EvalResult<CountedResult>.Ok(
                    new CountedResult(branchR.Value.Value, branchR.Value.Value.ValueCount()));
            }

            case (BuiltinId.@while, _) when args.Count >= 2:
            {
                var initialStateR = EvalInitialLoopStateSlots(args.Skip(1).ToList(), ctx, valEnv);
                if (initialStateR.IsError) return initialStateR.Error;
                return WhileLoopCounted(args[0], initialStateR.Value, ctx, valEnv);
            }

            case (BuiltinId.@repeat, _) when args.Count >= 3:
            {
                var countR = EvalAlgOutput(args[1], ctx, valEnv);
                if (countR.IsError) return countR.Error;
                var nR = ExpectWholeInt(countR.Value, "Repeat count");
                if (nR.IsError) return nR.Error;
                var n = (long)nR.Value;
                if (n < 0) return new EvalError.IllegalInEval("Repeat count must be >= 0");

                var initialStateR = EvalInitialLoopStateSlots(args.Skip(2).ToList(), ctx, valEnv);
                if (initialStateR.IsError) return initialStateR.Error;
                return RepeatLoopCounted(args[0], n, initialStateR.Value, ctx, valEnv);
            }

            case (BuiltinId.@atoms, 1):
            {
                var atomsR = EvalAlgOutput(args[0], ctx, valEnv);
                if (atomsR.IsError) return atomsR.Error;
                // `atoms` materializes a collection: one exact immutable list
                // of the recursively collected numeric atoms (sequence AND
                // list boundaries open; truth testing stays list-opaque).
                var atoms = atomsR.Value.LanguageAtoms();
                return EvalResult<CountedResult>.Ok(
                    MakeCollectionListResult(atoms.Select(static n => new Result.Atom(n))));
            }

            case (BuiltinId.@range, 2):
            {
                var rangeR = EvalBuiltinRangeArguments(args, ctx, valEnv);
                if (rangeR.IsError) return rangeR.Error;

                // A list value is always one visible value, including `[]`.
                var value = BuildInclusiveRange(rangeR.Value);
                return EvalResult<CountedResult>.Ok(new CountedResult(value, 1));
            }

            default:
                return WrongBuiltinArity(builtin, args.Count);
        }
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

    internal static string BuiltinDisplayName(BuiltinId builtin)
        => BuiltinRegistry.GetBuiltin(builtin).Name;

    /// <summary>Lean: builtinAcceptsArity. Every builtin is fixed-arity except the variadic-state loops <c>while</c>/<c>repeat</c>; collection builtins expect exactly one collection argument plus their fixed control arguments.</summary>
    private static bool BuiltinAcceptsArity(BuiltinId builtin, int argumentCount)
        => BuiltinRegistry.GetBuiltin(builtin).AcceptsArity(argumentCount);

    /// <summary>Lean: builtinArityDesc. Human-readable expected arity for error messages.</summary>
    private static string BuiltinArityDesc(BuiltinId builtin)
        => BuiltinRegistry.GetBuiltin(builtin).DescribeArity();

    private static EvalError WrongBuiltinArity(BuiltinId builtin, int actualCount)
    {
        var descriptor = BuiltinRegistry.GetBuiltin(builtin);
        var expected = builtin == BuiltinId.@if ? descriptor.FixedArity ?? 0 : 0;

        return new EvalError.ArityMismatch(expected, actualCount)
        {
            Signature = descriptor.PlainSignature,
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
    /// Does not rebind opened modules into the opener scope.
    /// Resolved lexical targets still keep their definition-site parent chain.
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
            case Expr.SequenceConstruct(var e1, var e2):
            {
                _ = e1;
                _ = e2;
                return new EvalError.BadOpenForm("sequence construction expressions cannot be opened") { Span = expr.Span };
            }

            case Expr.SequenceSpread(var operand):
            {
                _ = operand;
                return new EvalError.BadOpenForm("spread expressions cannot be opened") { Span = expr.Span };
            }

            case Expr.Block(var alg):
                return EvalResult<Algorithm>.Ok(WireOpenBlockToGlobalScope(alg, ctx));

            case Expr.Resolve(var name):
            {
                // open never requires the opened algorithm itself to be public.
                // It only requires the algorithm to be available in the current context.
                // open imports only public members (enforced later by LookupOpens).
                if (ctx.CallStack.Count > 0)
                {
                    var found = LookupLexicalDirect(ctx.CallStack[0], name);
                    if (found is not null)
                        return found is Algorithm.Builtin
                            ? new EvalError.IllegalInOpen($"builtin '{name}'") { Span = expr.Span }
                            : EvalResult<Algorithm>.Ok(found);
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

            // Property exists; check if it's public. Keep the property bound to
            // the resolved target so open A.B preserves definition-site scope.
            if (prop.IsPublic)
                return EvalResult<Algorithm>.Ok(ChildOf(targetResult.Value, prop.Value));

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
            case Expr.SequenceConstruct(var e1, var e2):
            {
                _ = e1;
                _ = e2;
                return new EvalError.NotAnAlgorithm("sequence construction expression") { Span = expr.Span };
            }

            case Expr.SequenceSpread(var operand):
            {
                _ = operand;
                return new EvalError.NotAnAlgorithm("spread expression") { Span = expr.Span };
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
                    Parent: null, Parameters: [], Opens: [],
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
            case Expr.EmptySequence:
                return new EvalError.NotAnAlgorithm("empty sequence value") { Span = expr.Span };
            case Expr.ListLiteral:
                return new EvalError.NotAnAlgorithm("list literal") { Span = expr.Span };
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
    /// Evaluate an algorithm's output expressions and collect into a single Result
    /// (the value projection of <see cref="EvalAlgOutputCountedCore"/>). Output slots
    /// are combined with the structure-preserving <see cref="CombineOutputSlots"/>, not a
    /// general normalize: each non-spread output is one visible slot even when it is the
    /// empty sequence value <c>()</c>, and only an explicit spread contributes its expanded
    /// items. Redundant empty-sequence nesting has already canonicalized to <c>()</c>.
    /// User-defined algorithms may exist structurally without output, but forcing
    /// them in value position raises <see cref="EvalError.MissingOutput"/>.
    /// Lean: evalAlgOutput → EvalM Result.
    /// </summary>
    private static EvalResult<Result> EvalAlgOutputCore(
        Algorithm alg,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var countedR = EvalAlgOutputCountedCore(alg, ctx, valEnv);
        return countedR.IsError
            ? countedR.Error
            : EvalResult<Result>.Ok(countedR.Value.Value);
    }

    private static EvalResult<Result> EvalAlgOutput(
        Algorithm alg,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
        => EvalAlgOutputCore(alg, ctx, valEnv);

    private static EvalResult<Result> EvalProgramOutput(
        Algorithm alg,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
        => EvalAlgOutputCore(alg, ctx, valEnv);

    private static Result LoopStateResult(IReadOnlyList<Result> stateSlots)
        => Result.FromItems(stateSlots);

    private static EvalResult<IReadOnlyList<Result>> EvalInitialLoopStateSlots(
        IReadOnlyList<Algorithm> initArgs,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        // Initial loop state preserves explicit argument boundaries: repeat(Step, 3, a, b)
        // starts with two slots, while repeat(Step, 3, Pair) starts with one slot even
        // when Pair evaluates to multiple values. Step outputs define later state slots;
        // capture a step result as a sequence value to keep one structured slot across iterations.
        var stateSlots = new List<Result>(initArgs.Count);
        foreach (var init in initArgs)
        {
            var slotR = EvalAlgOutput(init, ctx, valEnv);
            if (slotR.IsError) return slotR.Error;
            stateSlots.Add(slotR.Value);
        }

        return EvalResult<IReadOnlyList<Result>>.Ok(stateSlots);
    }

    private static EvalResult<IReadOnlyList<Result>> EvalAlgOutputSlots(
        Algorithm alg,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv,
        bool preserveSequenceSpreadExpressionBoundaries = false)
    {
        if (alg is Algorithm.Builtin(var builtin))
        {
            var countedR = EvalBuiltinValueCounted(builtin);
            return countedR.IsError
                ? countedR.Error
                : EvalResult<IReadOnlyList<Result>>.Ok(CountedTopLevelValues(countedR.Value));
        }

        if (alg.FindDuplicatePropName() is { } duplicateName)
            return new EvalError.DuplicateProperty(duplicateName);

        if (ConditionalValueAccessError("conditional", alg) is { } conditionalError)
            return conditionalError;

        if (alg is Algorithm.User { Output.Count: 0 })
            return new EvalError.MissingOutput();

        var slots = new List<Result>();
        var pushedCtx = ctx.Push(alg);
        foreach (var expr in alg.Output)
        {
            var countedR = EvalCounted(expr, pushedCtx, valEnv);
            if (countedR.IsError) return countedR.Error;

            if (preserveSequenceSpreadExpressionBoundaries && expr is Expr.SequenceSpread)
            {
                if (countedR.Value.EmittedCount != 0)
                    slots.Add(countedR.Value.Value);
                continue;
            }

            if (expr is Expr.SequenceSpread || countedR.Value.EmittedCount != 0)
                slots.AddRange(CountedTopLevelValues(countedR.Value));
            else
                slots.Add(countedR.Value.Value);
        }

        return EvalResult<IReadOnlyList<Result>>.Ok(slots);
    }

    private static EvalError LoopStateArityMismatch(
        Algorithm step,
        int actualStateValueCount,
        string loopName)
        => new EvalError.WithContext(
            new LoopStateBindingContext(loopName, step.Params.ToList(), actualStateValueCount),
            new EvalError.ArityMismatch(step.Params.Count, actualStateValueCount));

    private static EvalError VariadicLoopStateArityMismatch(
        Algorithm step,
        int expectedMinimumStateValueCount,
        int actualStateValueCount,
        string loopName)
        => new EvalError.WithContext(
            new VariadicLoopStateBindingContext(
                loopName,
                step.Parameters.Select(static parameter => parameter.DisplayName).ToList(),
                expectedMinimumStateValueCount,
                actualStateValueCount),
            new EvalError.ArityMismatch(expectedMinimumStateValueCount, actualStateValueCount));

    private static EvalResult<IReadOnlyList<(string Name, Result Value)>> BindEvaluatedSlotValueBindings(
        FlatVariadicBindingLayout layout,
        IReadOnlyList<(string ParameterName, BindingInputSlot Item)> normalBindings,
        VariadicCapture variadicCapture)
    {
        var valueBindings = new List<(string Name, Result Value)>(layout.Signature.Parameters.Count);
        var normalBindingIndex = 0;

        foreach (var parameter in layout.Signature.Parameters)
        {
            if (parameter.Kind == ParameterKind.Variadic)
            {
                valueBindings.Add((variadicCapture.Name, variadicCapture.Value));
                continue;
            }

            if (normalBindingIndex >= normalBindings.Count)
                return new EvalError.BadArity();

            var binding = normalBindings[normalBindingIndex++];
            if (binding.Item.Value is null)
                return new EvalError.BadArity();

            valueBindings.Add((binding.ParameterName, binding.Item.Value));
        }

        if (normalBindingIndex != normalBindings.Count)
            return new EvalError.BadArity();

        return EvalResult<IReadOnlyList<(string Name, Result Value)>>.Ok(valueBindings);
    }

    private static EvalResult<EvaluatedSlotBindings> BindEvaluatedSlotsToParameters(
        Algorithm algorithm,
        IReadOnlyList<Result> evaluatedSlots,
        string callableName,
        GenericLoopStepBindingSelection bindingSelection,
        Func<int, int, EvalError> fixedArityMismatch,
        Func<int, int, EvalError> variadicArityMismatch)
    {
        // Evaluated slots are already Result values. This helper only applies
        // parameter layout; it does not evaluate argument expressions, unpack a
        // final sequence-value argument, or apply dot-call receiver boundary rules.
        EvalResult<EvaluatedSlotBindings> BindPatternedSlots()
        {
            var inputs = evaluatedSlots
                .Select(static slot => new ParameterPatternInput(slot, Algorithm: null, ValueError: null, ExplicitSequenceValueItems: null))
                .ToList();
            var bindingsR = BindParameterPatternList(
                algorithm.ParameterPatterns,
                inputs,
                allowAlgorithmBindings: false,
                fixedArityMismatch);
            if (bindingsR.IsError) return bindingsR.Error;

            return EvalResult<EvaluatedSlotBindings>.Ok(new EvaluatedSlotBindings(
                bindingsR.Value.ValueBindings,
                bindingsR.Value.CountedBindings));
        }

        EvalResult<EvaluatedSlotBindings> BindFlatFixedSlots()
        {
            if (algorithm.Params.Count != evaluatedSlots.Count)
                return fixedArityMismatch(algorithm.Params.Count, evaluatedSlots.Count);

            var boundR = BindParams(algorithm.Params, evaluatedSlots);
            if (boundR.IsError) return boundR.Error;

            return EvalResult<EvaluatedSlotBindings>.Ok(new EvaluatedSlotBindings(boundR.Value, []));
        }

        EvalResult<EvaluatedSlotBindings> BindFlatVariadicSlots(FlatVariadicBindingLayout layout)
        {
            var inputSlots = evaluatedSlots
                .Select(BindingInputSlot.FromEvaluatedValue)
                .ToArray();

            var boundItemsR = BindItemsToFlatVariadicLayout(
                layout,
                inputSlots,
                variadicArityMismatch);
            if (boundItemsR.IsError) return boundItemsR.Error;

            var boundItems = boundItemsR.Value;
            var capturedValues = new List<Result>(boundItems.VariadicItems.Count);
            foreach (var item in boundItems.VariadicItems)
            {
                if (item.Value is null)
                    return new EvalError.BadArity();

                capturedValues.Add(item.Value);
            }

            var variadicName = boundItems.VariadicParameterName
                ?? layout.VariadicName;
            if (variadicName is null)
                return new EvalError.BadArity();

            var variadicCapture = CreateVariadicCapture(variadicName, capturedValues);

            var valueBindingsR = BindEvaluatedSlotValueBindings(
                layout,
                boundItems.NormalBindings,
                variadicCapture);
            if (valueBindingsR.IsError) return valueBindingsR.Error;

            return EvalResult<EvaluatedSlotBindings>.Ok(new EvaluatedSlotBindings(
                valueBindingsR.Value,
                [(variadicCapture.Name, variadicCapture.CountedValue)]));
        }

        EvalResult<EvaluatedSlotBindings> BindLegacyShape()
        {
            if (UsesPatternBinding(algorithm))
                return BindPatternedSlots();

            return TryGetLegacyFlatVariadicBindingLayout(algorithm, callableName, out var legacyLayout)
                ? BindFlatVariadicSlots(legacyLayout)
                : BindFlatFixedSlots();
        }

        EvalResult<EvaluatedSlotBindings> BindSelectedFlatVariadicShape()
        {
            return bindingSelection.Plan is not null
                && TryGetFlatVariadicBindingLayout(bindingSelection.Plan, out var layout)
                ? BindFlatVariadicSlots(layout)
                : BindLegacyShape();
        }

        return bindingSelection.Shape switch
        {
            GenericLoopStepBindingShape.Patterned => BindPatternedSlots(),
            GenericLoopStepBindingShape.FlatFixed => BindFlatFixedSlots(),
            GenericLoopStepBindingShape.FlatVariadic => BindSelectedFlatVariadicShape(),
            _ => BindLegacyShape(),
        };
    }

    private static EvalResult<EvaluatedSlotBindings> BindLoopStepState(
        Algorithm step,
        IReadOnlyList<Result> stateSlots,
        string loopName,
        GenericLoopStepBindingSelection bindingSelection)
    {
        // Loop state slots are produced by initial loop arguments or previous
        // step output. They are already evaluated and must not use ordinary
        // call-site behavior such as spread slot expansion.
        return BindEvaluatedSlotsToParameters(
            step,
            stateSlots,
            "loop step",
            bindingSelection,
            (_, actual) => LoopStateArityMismatch(step, actual, loopName),
            (required, actual) => VariadicLoopStateArityMismatch(step, required, actual, loopName));
    }

    internal static EvalResult<Result> ApplyBinaryOperator(
        BinaryOp op,
        Expr left,
        Expr right,
        Result leftValue,
        Result rightValue,
        SourceSpan? span)
    {
        // `==` and `!=` compare KatLang values structurally across all value kinds
        // (numbers, strings, and sequence values, recursively). Different value
        // kinds compare unequal rather than raising a type mismatch. This dedicated
        // path is deliberately separate from the numeric-scalar-only validation used
        // by arithmetic and ordering operators below.
        if (op == BinaryOp.Eq)
            return EvalResult<Result>.Ok(new Result.Atom(ValueEquals(leftValue, rightValue) ? 1 : 0));
        if (op == BinaryOp.Ne)
            return EvalResult<Result>.Ok(new Result.Atom(ValueEquals(leftValue, rightValue) ? 0 : 1));

        var leftEmpty = leftValue is Result.SequenceValue(var leftItems) && leftItems.Count == 0;
        var rightEmpty = rightValue is Result.SequenceValue(var rightItems) && rightItems.Count == 0;
        if (leftEmpty || rightEmpty)
        {
            // Empty results stay transparent for the non-comparison operators.
            if (leftEmpty && rightEmpty) return EvalResult<Result>.Ok(Result.SequenceValue.TakeOwnership([]));
            if (leftEmpty) return EvalResult<Result>.Ok(rightValue);
            return EvalResult<Result>.Ok(leftValue);
        }

        if (leftValue is Result.Str && rightValue is Result.Str)
            return new EvalError.TypeMismatch("Strings only support == and != operators") { Span = span };

        if (leftValue is Result.Str || rightValue is Result.Str)
            return new EvalError.TypeMismatch("Cannot apply operator to string and non-string operands") { Span = span };

        var binaryContext = $"while evaluating `{BinaryExprDiagnosticName(op, left, right)}`";
        var xR = RequireNumericScalarOperand(op, "left", leftValue);
        if (xR.IsError) return new EvalError.WithContext(binaryContext, xR.Error) { Span = span };
        var yR = RequireNumericScalarOperand(op, "right", rightValue);
        if (yR.IsError) return new EvalError.WithContext(binaryContext, yR.Error) { Span = span };
        decimal x = xR.Value, y = yR.Value;
        if ((op is BinaryOp.Div or BinaryOp.IDiv or BinaryOp.Mod) && y == 0)
            return new EvalError.DivByZero() { Span = span };

        if (op == BinaryOp.Pow)
            return EvalPow(span, x, y);

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
            return new EvalError.NumericOverflow() { Span = span };
        }

        return EvalResult<Result>.Ok(new Result.Atom(result));
    }

    /// <summary>Evaluate an expression and coerce to decimal.
    /// Lean: expectInt over eval (the model has no dedicated wrapper).</summary>
    private static EvalResult<decimal> EvalInt(
        Expr expr, EvalCtx ctx, IReadOnlyList<(string, Result)> valEnv)
    {
        var r = Eval(expr, ctx, valEnv);
        if (r.IsError) return r.Error;
        return ExpectInt(r.Value);
    }

    private static EvalResult<IReadOnlyList<Result>> RunStepSlots(
        Algorithm step,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv,
        IReadOnlyList<Result> stateSlots,
        string loopName)
    {
        var bindingSelection = SelectGenericLoopStepBinding(step);
        var boundR = BindLoopStepState(step, stateSlots, loopName, bindingSelection);
        if (boundR.IsError) return boundR.Error;

        var shadowedCountedParamEnv = ShadowCountedParamEnv(ctx.CountedParamEnv, step.Params);
        var stepCtx = ctx
            .WithCountedParamEnv(Concat(boundR.Value.CountedBindings, shadowedCountedParamEnv));
        return EvalAlgOutputSlots(
            step,
            stepCtx,
            Concat(boundR.Value.ValueBindings, valEnv),
            preserveSequenceSpreadExpressionBoundaries: ShouldPreserveLoopStepSequenceSpreadExpressionBoundaries(step, bindingSelection));
    }

    /// <summary>Run a step algorithm with the given state bound to its params. Lean: runStep.</summary>
    private static EvalResult<Result> RunStep(
        Algorithm step, EvalCtx ctx, IReadOnlyList<(string, Result)> valEnv, Result state, string loopName)
    {
        var outputSlotsR = RunStepSlots(step, ctx, valEnv, UnpackArgs(state), loopName);
        return outputSlotsR.IsError
            ? outputSlotsR.Error
            : EvalResult<Result>.Ok(LoopStateResult(outputSlotsR.Value));
    }

    private static EvalResult<(IReadOnlyList<Result> NextStateSlots, decimal Continue)> SplitContSlots(
        IReadOnlyList<Result> outputSlots)
    {
        if (outputSlots.Count == 0)
            return new EvalError.BadArity();

        if (outputSlots.Count == 1)
        {
            if (outputSlots[0] is Result.Atom(var number))
                return EvalResult<(IReadOnlyList<Result>, decimal)>.Ok((outputSlots, number));

            return new EvalError.BadArity();
        }

        var contR = ExpectInt(outputSlots[^1]);
        if (contR.IsError) return contR.Error;
        return EvalResult<(IReadOnlyList<Result>, decimal)>.Ok((outputSlots.Take(outputSlots.Count - 1).ToList(), contR.Value));
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
        => ApplyBuiltinResolved(builtin, WithoutSequenceSpread(args), ctx, valEnv);

    private static EvalResult<Result> ApplyBuiltinResolved(
        BuiltinId builtin,
        IReadOnlyList<ResolvedArgumentAlgorithm> resolvedArgs,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        if (GetSequenceBuiltinMetadata(builtin) is { } metadata)
        {
            var countedR = ApplyBuiltinCountedSequence(builtin, metadata, resolvedArgs, ctx, valEnv);
            if (countedR.IsError) return countedR.Error;
            return EvalResult<Result>.Ok(countedR.Value.Value);
        }

        var expandedArgsR = ExpandSequenceSpreadBuiltinArguments(resolvedArgs, ctx, valEnv);
        if (expandedArgsR.IsError) return expandedArgsR.Error;
        var args = expandedArgsR.Value;

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

            // while(step, init...)
            case (BuiltinId.@while, _) when args.Count >= 2:
            {
                var initialStateR = EvalInitialLoopStateSlots(args.Skip(1).ToList(), ctx, valEnv);
                if (initialStateR.IsError) return initialStateR.Error;
                return WhileLoop(args[0], initialStateR.Value, ctx, valEnv);
            }

            // repeat(step, count, init...)
            case (BuiltinId.@repeat, _) when args.Count >= 3:
            {
                var countR = EvalAlgOutput(args[1], ctx, valEnv);
                if (countR.IsError) return countR.Error;
                var nR = ExpectWholeInt(countR.Value, "Repeat count");
                if (nR.IsError) return nR.Error;
                var n = (long)nR.Value;
                if (n < 0) return new EvalError.IllegalInEval("Repeat count must be >= 0");
                var initialStateR = EvalInitialLoopStateSlots(args.Skip(2).ToList(), ctx, valEnv);
                if (initialStateR.IsError) return initialStateR.Error;
                return RepeatLoop(args[0], n, initialStateR.Value, ctx, valEnv);
            }

            // atoms(value) — recursively collect numeric atoms into one exact list
            case (BuiltinId.@atoms, 1):
            {
                var atomsR = EvalAlgOutput(args[0], ctx, valEnv);
                if (atomsR.IsError) return atomsR.Error;
                var atoms = atomsR.Value.LanguageAtoms();
                return EvalResult<Result>.Ok(
                    MakeCollectionListResult(atoms.Select(static n => new Result.Atom(n))).Value);
            }

            // range(start, stop) — inclusive integers materialized as one exact list.
            case (BuiltinId.@range, 2):
            {
                var rangeR = EvalBuiltinRangeArguments(args, ctx, valEnv);
                if (rangeR.IsError) return rangeR.Error;

                return EvalResult<Result>.Ok(BuildInclusiveRange(rangeR.Value));
            }

            default:
            {
                return WrongBuiltinArity(builtin, args.Count);
            }
        }
    }

    private static CountedResult CountedLoopStateResult(IReadOnlyList<Result> stateSlots)
        => new(LoopStateResult(stateSlots), stateSlots.Count);

    /// <summary>Lean: While loop → EvalM Result.</summary>
    private static EvalResult<Result> WhileLoop(
        Algorithm step,
        IReadOnlyList<Result> initialStateSlots,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var countedR = WhileLoopCounted(step, initialStateSlots, ctx, valEnv);
        return countedR.IsError
            ? countedR.Error
            : EvalResult<Result>.Ok(countedR.Value.Value);
    }

    private static EvalResult<CountedResult> WhileLoopCounted(
        Algorithm step,
        IReadOnlyList<Result> initialStateSlots,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        ctx.LoopDiagnostics?.RecordLoopExecution();

        if (!ctx.EnableLoopOptimization)
        {
            ctx.LoopDiagnostics?.RecordOptimizedLoopFallback("loop optimization disabled");
            return WhileLoopGenericCounted(step, initialStateSlots, ctx, valEnv);
        }

        if (!IsOptimizedLoopShapeEligible(step, out var fallbackReason))
        {
            ctx.LoopDiagnostics?.RecordOptimizedLoopFallback(fallbackReason!);
            return WhileLoopGenericCounted(step, initialStateSlots, ctx, valEnv);
        }

        if (initialStateSlots.Any(static slot => slot is not Result.Atom))
        {
            ctx.LoopDiagnostics?.RecordOptimizedLoopFallback("non-scalar loop state slot");
            return WhileLoopGenericCounted(step, initialStateSlots, ctx, valEnv);
        }

        if (step.Params.Count != initialStateSlots.Count)
            return LoopStateArityMismatch(step, initialStateSlots.Count, "while");

        return LoopOptimizer.TryEvaluateWhile(
            step,
            initialStateSlots,
            ctx,
            valEnv,
            fallbackState => WhileLoopGenericCounted(step, UnpackArgs(fallbackState), ctx, valEnv),
            out var optimizedResult)
            ? optimizedResult
            : WhileLoopGenericCounted(step, initialStateSlots, ctx, valEnv);
    }

    private static EvalResult<Result> WhileLoopGeneric(
        Algorithm step,
        IReadOnlyList<Result> initialStateSlots,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var countedR = WhileLoopGenericCounted(step, initialStateSlots, ctx, valEnv);
        return countedR.IsError
            ? countedR.Error
            : EvalResult<Result>.Ok(countedR.Value.Value);
    }

    private static EvalResult<CountedResult> WhileLoopGenericCounted(
        Algorithm step,
        IReadOnlyList<Result> initialStateSlots,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var stateSlots = initialStateSlots.ToList();
        while (true)
        {
            var outputSlotsR = RunStepSlots(step, ctx, valEnv, stateSlots, "while");
            if (outputSlotsR.IsError) return outputSlotsR.Error;
            var splitR = SplitContSlots(outputSlotsR.Value);
            if (splitR.IsError) return splitR.Error;
            var (nextStateSlots, cont) = splitR.Value;
            if (cont == 0) return EvalResult<CountedResult>.Ok(CountedLoopStateResult(stateSlots));
            stateSlots = nextStateSlots.ToList();
        }
    }

    /// <summary>Lean: Repeat loop → EvalM Result.</summary>
    private static EvalResult<Result> RepeatLoop(
        Algorithm step,
        long count,
        IReadOnlyList<Result> initialStateSlots,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var countedR = RepeatLoopCounted(step, count, initialStateSlots, ctx, valEnv);
        return countedR.IsError
            ? countedR.Error
            : EvalResult<Result>.Ok(countedR.Value.Value);
    }

    private static EvalResult<CountedResult> RepeatLoopCounted(
        Algorithm step,
        long count,
        IReadOnlyList<Result> initialStateSlots,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        ctx.LoopDiagnostics?.RecordLoopExecution();

        if (count == 0)
            return EvalResult<CountedResult>.Ok(CountedLoopStateResult(initialStateSlots));

        if (!ctx.EnableLoopOptimization)
        {
            ctx.LoopDiagnostics?.RecordOptimizedLoopFallback("loop optimization disabled");
            return RepeatLoopGenericCounted(step, count, initialStateSlots, ctx, valEnv);
        }

        if (!IsOptimizedLoopShapeEligible(step, out var fallbackReason))
        {
            ctx.LoopDiagnostics?.RecordOptimizedLoopFallback(fallbackReason!);
            return RepeatLoopGenericCounted(step, count, initialStateSlots, ctx, valEnv);
        }

        if (initialStateSlots.Any(static slot => slot is not Result.Atom))
        {
            ctx.LoopDiagnostics?.RecordOptimizedLoopFallback("non-scalar loop state slot");
            return RepeatLoopGenericCounted(step, count, initialStateSlots, ctx, valEnv);
        }

        if (step.Params.Count != initialStateSlots.Count)
            return LoopStateArityMismatch(step, initialStateSlots.Count, "repeat");

        return LoopOptimizer.TryEvaluateRepeat(
            step,
            count,
            initialStateSlots,
            ctx,
            valEnv,
            (remainingCount, fallbackState) => RepeatLoopGenericCounted(step, remainingCount, UnpackArgs(fallbackState), ctx, valEnv),
            out var optimizedResult)
            ? optimizedResult
            : RepeatLoopGenericCounted(step, count, initialStateSlots, ctx, valEnv);
    }

    private static EvalResult<Result> RepeatLoopGeneric(
        Algorithm step,
        long count,
        IReadOnlyList<Result> initialStateSlots,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var countedR = RepeatLoopGenericCounted(step, count, initialStateSlots, ctx, valEnv);
        return countedR.IsError
            ? countedR.Error
            : EvalResult<Result>.Ok(countedR.Value.Value);
    }

    private static EvalResult<CountedResult> RepeatLoopGenericCounted(
        Algorithm step,
        long count,
        IReadOnlyList<Result> initialStateSlots,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var stateSlots = initialStateSlots.ToList();
        for (var k = 0; k < count; k++)
        {
            var outputSlotsR = RunStepSlots(step, ctx, valEnv, stateSlots, "repeat");
            if (outputSlotsR.IsError) return outputSlotsR.Error;
            stateSlots = outputSlotsR.Value.ToList();
        }
        return EvalResult<CountedResult>.Ok(CountedLoopStateResult(stateSlots));
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
                    if (ConditionalValueAccessError(name, algBound) is { } conditionalError)
                        return conditionalError with { Span = expr.Span };
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
                if (operandR.Value is Result.SequenceValue(var uItems) && uItems.Count == 0)
                    return EvalResult<Result>.Ok(Result.SequenceValue.TakeOwnership([]));
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
                return ApplyBinaryOperator(op, left, right, lR.Value, rR.Value, expr.Span);
            }

            case Expr.SequenceConstruct:
            {
                var sequenceConstructR = EvalSequenceConstructCounted(expr, ctx, valEnv);
                return sequenceConstructR.IsError
                    ? sequenceConstructR.Error
                    : EvalResult<Result>.Ok(sequenceConstructR.Value.Value);
            }

            case Expr.EmptySequence(var depth):
                return EvalResult<Result>.Ok(BuildEmptySequenceValue(depth));

            case Expr.SequenceSpread:
            {
                var sequenceSpreadR = EvalSequenceSpreadCounted(expr, ctx, valEnv);
                return sequenceSpreadR.IsError
                    ? sequenceSpreadR.Error
                    : EvalResult<Result>.Ok(sequenceSpreadR.Value.Value);
            }

            case Expr.ListLiteral(var listItems):
            {
                var listLiteralR = EvalListLiteralCounted(listItems, ctx, valEnv);
                return listLiteralR.IsError
                    ? listLiteralR.Error
                    : EvalResult<Result>.Ok(listLiteralR.Value.Value);
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

                if (ConditionalValueAccessError(name, resolvedR.Value.ResolvedAlgorithm) is { } conditionalError)
                    return conditionalError with { Span = expr.Span };

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
    /// Calls, name resolution, and collection builtins are value boundaries: they
    /// emit <c>Result.ValueCount</c> of the result value (one value for a
    /// non-empty result), so a multi-output body/collection is observed as one
    /// sequence value and only caller-site <c>...</c> re-opens it.
    /// Block expressions count as one sequence value when non-empty. Spread
    /// emits the immediate spread items of its operand. All other value
    /// expressions emit either zero values (empty result) or one value.
    /// Lean: <c>evalCounted</c>.
    /// </summary>
    internal static EvalResult<CountedResult> EvalCounted(
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
                    if (ConditionalValueAccessError(name, algBound) is { } conditionalError)
                        return conditionalError with { Span = expr.Span };
                    if (algBound.Params.Count == 0)
                    {
                        var valueR = WithSpan(expr.Span, EvalAlgOutput(algBound, ctx, valEnv));
                        return valueR.IsError
                            ? valueR.Error
                            : EvalResult<CountedResult>.Ok(new CountedResult(valueR.Value, valueR.Value.ValueCount()));
                    }
                    return new EvalError.ArityMismatch(algBound.Params.Count, 0) { Span = expr.Span };
                }

                return new EvalError.UnknownName(name) { Span = expr.Span };
            }

            case Expr.SequenceSpread:
                return EvalSequenceSpreadCounted(expr, ctx, valEnv);

            case Expr.SequenceConstruct:
                return EvalSequenceConstructCounted(expr, ctx, valEnv);

            case Expr.ListLiteral(var listItems):
                return EvalListLiteralCounted(listItems, ctx, valEnv);

            case Expr.EmptySequence(var depth):
            {
                var emptyValue = BuildEmptySequenceValue(depth);
                return EvalResult<CountedResult>.Ok(new CountedResult(emptyValue, emptyValue.ValueCount()));
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

                if (ConditionalValueAccessError(name, resolvedR.Value.ResolvedAlgorithm) is { } conditionalError)
                    return conditionalError with { Span = expr.Span };

                if (resolvedR.Value.ResolvedAlgorithm.Params.Count != 0)
                {
                    return WithSpan<CountedResult>(
                        expr.Span,
                        new EvalError.WithContext(
                            CtxProperty(name),
                            new EvalError.ArityMismatch(resolvedR.Value.ResolvedAlgorithm.Params.Count, 0)));
                }

                var propertyR = WithPropertyContextOnMissingOutput(name, expr.Span,
                    EvalZeroArgPropertyAccessCounted(resolvedR.Value, ctx, valEnv));
                return propertyR.IsError
                    ? propertyR.Error
                    : EvalResult<CountedResult>.Ok(new CountedResult(
                        propertyR.Value.Value,
                        propertyR.Value.Value.ValueCount()));
            }

            case Expr.DotCall(var dotTarget, var dotName, var dotArgs):
                return WithSpan(expr.Span, WithCtx(CtxDotCall(dotTarget, dotName),
                    EvalDotCallCounted(dotTarget, dotName, dotArgs, ctx, valEnv)));

            case Expr.Call(var func, var argsAlg):
                return WithSpan(expr.Span,
                    EvalCallCountedExpr(func, argsAlg, ctx, valEnv));

            case Expr.Index(var target, var selector):
                // EvalIndexSelectionCounted owns the index-expression span.
                return EvalIndexSelectionCounted(target, selector, expr.Span, ctx, valEnv);

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
                case "Round":
                    if (args[1] != Math.Truncate(args[1]))
                        return new EvalError.IllegalInEval("digits must be an integer");
                    if (args[1] < 0 || args[1] > 28)
                        return new EvalError.IllegalInEval("digits must be between 0 and 28");
                    result = Math.Round(args[0], decimal.ToInt32(args[1]), MidpointRounding.AwayFromZero);
                    break;
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
                case "Atan2": result = NormalizeDoubleResult(Math.Atan2((double)args[0], (double)args[1])); break;
                case "Pow": result = NormalizeDoubleResult(Math.Pow((double)args[0], (double)args[1])); break;
                case "Log": result = NormalizeDoubleResult(Math.Log((double)args[0], (double)args[1])); break;
                case "Random":
                    if (args[0] >= args[1])
                        return new EvalError.IllegalInEval("Math.Random start must be less than end");
                    result = RandomInHalfOpenRange(args[0], args[1]);
                    break;
                case "RandomInt":
                    if (!IsWholeNumber(args[0]) || !IsWholeNumber(args[1]))
                        return new EvalError.IllegalInEval("Math.RandomInt bounds must be whole numbers");
                    if (args[0] >= args[1])
                        return new EvalError.IllegalInEval("Math.RandomInt start must be less than end");
                    result = Math.Floor(RandomInHalfOpenRange(args[0], args[1]));
                    break;
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

    private static bool IsWholeNumber(decimal value) => value == Math.Floor(value);

    private static decimal RandomInHalfOpenRange(decimal start, decimal end)
    {
        var result = start + ((decimal)Random.Shared.NextDouble() * (end - start));
        return result >= end ? start : result;
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
    /// Lean: resolveArgAlgExpr per argument (the list form is
    /// resolveArgAlgsWithSequenceSpread, which also tags spread
    /// arguments) — wraps only liftable errors (notAnAlgorithm,
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
                Parameters: [],
                Opens: [],
                Properties: [],
                Output: [expr]));

    private static bool ShouldWrapBuiltinArgExprAsValue(
        Expr expr,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
        => ShouldWrapArgExprAsValue(expr)
            || expr is Expr.Param(var name)
                && (LookupCountedParam(ctx.CountedParamEnv, name) is not null
                    || LookupVal(valEnv, name) is not null);

    private static EvalResult<IReadOnlyList<Algorithm>> ResolveArgAlgs(
        Algorithm argsAlg,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var resolvedR = ResolveArgAlgsWithSequenceSpread(argsAlg, ctx, valEnv);
        return resolvedR.IsError
            ? resolvedR.Error
            : EvalResult<IReadOnlyList<Algorithm>>.Ok(resolvedR.Value.Select(static arg => arg.Algorithm).ToList());
    }

    private static EvalResult<IReadOnlyList<ResolvedArgumentAlgorithm>> ResolveArgAlgsWithSequenceSpread(
        Algorithm argsAlg,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var result = new List<ResolvedArgumentAlgorithm>(argsAlg.Output.Count);
        foreach (var argExpr in argsAlg.Output)
        {
            var spreadsSequence = argExpr is Expr.SequenceSpread;
            if (ShouldWrapBuiltinArgExprAsValue(argExpr, ctx, valEnv))
            {
                result.Add(new ResolvedArgumentAlgorithm(WrapArgExprAsValue(argExpr, ctx), spreadsSequence));
                continue;
            }

            var r = ResolveAlg(argExpr, ctx);
            if (r.IsOk)
            {
                result.Add(new ResolvedArgumentAlgorithm(r.Value, spreadsSequence));
            }
            else if (IsLiftableError(r.Error))
            {
                // Wrap liftable non-resolvable expressions in a trivial algorithm.
                // evalAlgOutput will evaluate the expression lazily when needed.
                var wrapper = new Algorithm.User(
                    Parent: null, Parameters: [], Opens: [],
                    Properties: [], Output: [argExpr]);
                result.Add(new ResolvedArgumentAlgorithm(WireToCaller(ctx, wrapper), spreadsSequence));
            }
            else
            {
                // Propagate genuine lookup/semantic failures immediately.
                return r.Error;
            }
        }
        return EvalResult<IReadOnlyList<ResolvedArgumentAlgorithm>>.Ok(result);
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
    /// Lean: evalCallExpr → EvalM Result (Lean also attaches the call-context wrapper there).
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
    /// Lean: <c>evalCallCountedExpr</c> (Lean also attaches the call-context wrapper there).
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

        if (TryEvaluateSequencePipeline(
            SequencePipelineInvocation.PlainCall(func, argsAlg, calleeR.Value),
            ctx,
            valEnv,
            out var sequencePipelineR))
            return WithCtx(
                CtxCall(func),
                sequencePipelineR.IsError
                    ? sequencePipelineR.Error
                    : EvalResult<Result>.Ok(sequencePipelineR.Value.Value));

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

        if (TryEvaluateSequencePipeline(
            SequencePipelineInvocation.PlainCall(func, argsAlg, calleeR.Value),
            ctx,
            valEnv,
            out var sequencePipelineR))
            return WithCtx(CtxCall(func), sequencePipelineR);

        return WithCtx(CtxCall(func), EvalResolvedCallCounted(calleeR.Value, argsAlg, ctx, valEnv, OpenExprName(func)));
    }

    // ── Conditional algorithm call (Lean: evalConditionalCall) ──────────────

    /// <summary>
    /// Evaluates a conditional algorithm call.
    /// 1. Evaluate argument expressions eagerly.
    /// 2. Assemble full argument Result shape (preserving sequence-value shape for pattern matching).
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
        var shadowedNames = bindings.Select(static binding => binding.Item1).ToArray();
        var newCtx = ctx.Push(callee)
            .WithCountedParamEnv(ShadowCountedParamEnv(ctx.CountedParamEnv, shadowedNames));
        var newEnv = Concat(bindings, valEnv);
        return EvalAlgOutput(wiredBody, newCtx, newEnv);
    }

    /// <summary>
    /// Counted conditional call evaluation.
    /// The argument matching semantics are unchanged; the selected branch is a
    /// value boundary, so its public result re-counts the emitted arity with
    /// <see cref="ReCountValueBoundary"/> (<c>Result.ValueCount</c>) — a
    /// multi-output branch becomes one sequence value (count 1), matching
    /// <c>if</c> and plain calls.
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
        var shadowedNames = bindings.Select(static binding => binding.Item1).ToArray();
        var newCtx = ctx.Push(callee)
            .WithCountedParamEnv(ShadowCountedParamEnv(ctx.CountedParamEnv, shadowedNames));
        var newEnv = Concat(bindings, valEnv);
        return ReCountValueBoundary(EvalAlgOutputCounted(wiredBody, newCtx, newEnv));
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
    /// Flat fixed calls bind call-site structure: each comma argument is one
    /// argument expression, while a bare spread expression explicitly
    /// contributes its spread top-level items. Multi-output values from normal
    /// expressions, including <c>.atoms</c>, remain one argument expression.
    /// Earlier explicit argument positions remain distinct on the eager value
    /// side even if some later arguments bind only through AlgEnv.
    /// </summary>
    private static EvalResult<Result> EvalUserCall(
        Algorithm callee, Algorithm args,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv,
        IReadOnlyList<bool>? preserveArgBoundaries = null,
        string? calleeName = null)
    {
        var wiredArgs = WireToCaller(ctx, args);

        if (callee.Output.Count == 0)
            return new EvalError.MissingOutput();

        var signature = CallableSignature.FromAlgorithm(calleeName ?? "<anonymous>", callee);
        var bindingPlan = CallableBindingPlan.FromSignature(signature);

        if (bindingPlan.RequiresPatternedBinding)
        {
            var bindingsR = BindPatternedUserCall(callee, wiredArgs, ctx, valEnv, calleeName);
            if (bindingsR.IsError) return bindingsR.Error;

            var bindings = bindingsR.Value;
            var groupedCtx = WithUserCallBindingEnvironments(ctx, bindings, callee.Params);
            var groupedEnv = Concat(bindings.ValueBindings, valEnv);
            return EvalAlgOutput(callee, groupedCtx, groupedEnv);
        }

        if (IsDeconstructionUserCallShape(signature))
        {
            var bindingsR = BindDeconstructionUserCall(callee, wiredArgs, ctx, valEnv, calleeName, preserveArgBoundaries);
            if (bindingsR.IsError) return bindingsR.Error;

            var bindings = bindingsR.Value;
            var deconstructionCtx = WithUserCallBindingEnvironments(ctx, bindings, callee.Params);
            var deconstructionEnv = Concat(bindings.ValueBindings, valEnv);
            return EvalAlgOutput(callee, deconstructionCtx, deconstructionEnv);
        }

        if (!TryGetPlanDerivedFlatFixedParameterNames(bindingPlan, out var flatFixedParams))
            flatFixedParams = callee.Params;

        var flatBindingsR = BindFlatFixedUserCallArguments(signature, flatFixedParams, wiredArgs, ctx, valEnv);
        if (flatBindingsR.IsError) return flatBindingsR.Error;

        var flatBindings = flatBindingsR.Value;
        return EvalAlgOutput(callee, flatBindings.Context, flatBindings.ValueEnvironment);
    }

    /// <summary>
    /// Dispatches an already-resolved callee.
    /// </summary>
    private static EvalResult<Result> EvalResolvedCall(
        Algorithm callee,
        Algorithm argsAlg,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv,
        string calleeName,
        IReadOnlyList<bool>? preserveArgBoundaries = null)
    {
        if (callee is Algorithm.Builtin(var builtinId))
        {
            var argAlgsR = ResolveArgAlgsWithSequenceSpread(argsAlg, ctx, valEnv);
            if (argAlgsR.IsError) return argAlgsR.Error;
            return ApplyBuiltinResolved(builtinId, argAlgsR.Value, ctx, valEnv);
        }

        if (TryGetFlatBinderUserEquivalent(callee) is { } simpleCallee)
            return EvalUserCall(
                simpleCallee,
                argsAlg,
                ctx,
                valEnv,
                preserveArgBoundaries,
                calleeName);

        if (callee is Algorithm.Conditional)
            return EvalConditionalCall(callee, argsAlg, ctx, valEnv, calleeName);

        return EvalUserCall(
            callee,
            argsAlg,
            ctx,
            valEnv,
            preserveArgBoundaries,
            calleeName);
    }

    /// <summary>
    /// Counted user-defined call evaluation.
    /// A user/property call is a value boundary: argument-binding and body
    /// evaluation are unchanged, but the public result preserves the structural
    /// value while re-counting the emitted arity with
    /// <see cref="ReCountValueBoundary"/> (<c>Result.ValueCount</c>). A
    /// multi-output body therefore becomes one sequence value (count 1); only
    /// caller-site <c>...</c> re-opens it.
    /// Lean: <c>evalUserCallCounted</c>.
    /// </summary>
    private static EvalResult<CountedResult> EvalUserCallCounted(
        Algorithm callee, Algorithm args,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv,
        IReadOnlyList<bool>? preserveArgBoundaries = null,
        string? calleeName = null)
    {
        var wiredArgs = WireToCaller(ctx, args);

        if (callee.Output.Count == 0)
            return new EvalError.MissingOutput();

        var signature = CallableSignature.FromAlgorithm(calleeName ?? "<anonymous>", callee);
        var bindingPlan = CallableBindingPlan.FromSignature(signature);

        if (bindingPlan.RequiresPatternedBinding)
        {
            var bindingsR = BindPatternedUserCall(callee, wiredArgs, ctx, valEnv, calleeName);
            if (bindingsR.IsError) return bindingsR.Error;

            var bindings = bindingsR.Value;
            var groupedCtx = WithUserCallBindingEnvironments(ctx, bindings, callee.Params);
            var groupedEnv = Concat(bindings.ValueBindings, valEnv);
            return ReCountValueBoundary(EvalAlgOutputCounted(callee, groupedCtx, groupedEnv));
        }

        if (IsDeconstructionUserCallShape(signature))
        {
            var bindingsR = BindDeconstructionUserCall(callee, wiredArgs, ctx, valEnv, calleeName, preserveArgBoundaries);
            if (bindingsR.IsError) return bindingsR.Error;

            var bindings = bindingsR.Value;
            var deconstructionCtx = WithUserCallBindingEnvironments(ctx, bindings, callee.Params);
            var deconstructionEnv = Concat(bindings.ValueBindings, valEnv);
            return ReCountValueBoundary(EvalAlgOutputCounted(callee, deconstructionCtx, deconstructionEnv));
        }

        if (!TryGetPlanDerivedFlatFixedParameterNames(bindingPlan, out var flatFixedParams))
            flatFixedParams = callee.Params;

        var flatBindingsR = BindFlatFixedUserCallArguments(signature, flatFixedParams, wiredArgs, ctx, valEnv);
        if (flatBindingsR.IsError) return flatBindingsR.Error;

        var flatBindings = flatBindingsR.Value;
        return ReCountValueBoundary(EvalAlgOutputCounted(callee, flatBindings.Context, flatBindings.ValueEnvironment));
    }

    /// <summary>
    /// Counted dispatch for an already-resolved effective callee.
    /// </summary>
    private static EvalResult<CountedResult> EvalResolvedCallCounted(
        Algorithm callee,
        Algorithm argsAlg,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv,
        string calleeName,
        IReadOnlyList<bool>? preserveArgBoundaries = null)
    {
        if (callee is Algorithm.Builtin(var builtinId))
        {
            var argAlgsR = ResolveArgAlgsWithSequenceSpread(argsAlg, ctx, valEnv);
            if (argAlgsR.IsError) return argAlgsR.Error;
            return ApplyBuiltinCountedResolved(builtinId, argAlgsR.Value, ctx, valEnv);
        }

        if (TryGetFlatBinderUserEquivalent(callee) is { } simpleCallee)
            return EvalUserCallCounted(
                simpleCallee,
                argsAlg,
                ctx,
                valEnv,
                preserveArgBoundaries,
                calleeName);

        if (callee is Algorithm.Conditional)
            return EvalConditionalCallCounted(callee, argsAlg, ctx, valEnv, calleeName);

        return EvalUserCallCounted(
            callee,
            argsAlg,
            ctx,
            valEnv,
            preserveArgBoundaries,
            calleeName);
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
    /// 3. No property → lexical fallback (receiver injection via CallLexicalWithReceiver)
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

        if (TryEvaluateSequencePipeline(
            SequencePipelineInvocation.DotCall(target, name, argsOpt),
            ctx,
            valEnv,
            out var sequencePipelineR))
            return sequencePipelineR.IsError
                ? sequencePipelineR.Error
                : EvalResult<Result>.Ok(sequencePipelineR.Value.Value);

        // Lean: let targetAlg <- resolveAlg target ctx
        // Extension-property rule: if target is a value-producing expression (not an algorithm),
        // ResolveAlg returns NotAnAlgorithm — check value-based intrinsics first,
        // then fall back to lexical lookup so that
        //   e.P      → P(e)
        //   e.P(a,b) → P(e, a, b)
        // works for any receiver expression, including literals and parenthesized expressions.
        // The injected receiver remains one argument boundary.
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

        // Lexical fallback (receiver injection via CallLexicalWithReceiver)
        return CallLexicalWithReceiver(name, target, argsOpt, ctx, valEnv);
    }

    /// <summary>
    /// Resolves name lexically and calls with receiver prepended to args.
    /// The injected receiver remains one argument expression for flat fixed
    /// user calls; sequence builtin dot-call expansion is handled before this path.
    /// Delegates to EvalCall to get builtin dispatch for free.
    ///
    /// DotCall lexical fallback to "while" and "repeat" keeps explicit init
    /// arguments intact; the loop builtin turns each init argument into one
    /// initial state slot after structural property lookup has had priority.
    ///
    /// Lean: callLexicalWithReceiverCounted (the Lean plain path is the
    /// projection `evalDotCall`, so only the counted helper remains).
    /// </summary>
    private readonly record struct SequenceBuiltinDotCall(
        BuiltinId Builtin,
        IReadOnlyList<ResolvedArgumentAlgorithm> Args);

    /// <summary>
    /// Sequence builtins in dot-call form pass the receiver as one counted
    /// source to the shared sequence collector.
    /// A direct inline receiver block first exposes its inner algorithm output
    /// count, which strips exactly one receiver-scoping block layer for forms
    /// like <c>(1, 2, 3).take(2)</c> while still keeping
    /// <c>((1, 2, 3)).take(2)</c> and named sequence-valued helpers intact.
    /// The resulting counted receiver is reified as one ordinary leading
    /// source, and any extra dot-call arguments still follow the plain-call
    /// argument path.
    /// This keeps plain-call boundary preservation unchanged while making
    /// <c>receiver.builtin(...)</c> operate on the same top-level collection
    /// that <c>receiver:i</c> and higher-order callback projection observe.
    /// </summary>
    private static EvalResult<CountedResult> EvalSequenceBuiltinDotReceiverCounted(
        Expr receiver,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var valueR = Eval(receiver, ctx, valEnv);
        return valueR.IsError
            ? valueR.Error
            : EvalResult<CountedResult>.Ok(new CountedResult(valueR.Value, valueR.Value.ValueCount()));
    }

    private static EvalResult<IReadOnlyList<ResolvedArgumentAlgorithm>> SequenceBuiltinDotReceiverArgs(
        Expr receiver,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var receiverR = EvalSequenceBuiltinDotReceiverCounted(receiver, ctx, valEnv);
        if (receiverR.IsError) return receiverR.Error;

        return EvalResult<IReadOnlyList<ResolvedArgumentAlgorithm>>.Ok(
            [new ResolvedArgumentAlgorithm(CountedArgAlgorithm(receiverR.Value), SpreadsSequence: false)]);
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

        var argAlgs = new List<ResolvedArgumentAlgorithm>(receiverArgAlgsR.Value);

        if (extraArgs is not null)
        {
            var extraArgAlgsR = ResolveArgAlgsWithSequenceSpread(extraArgs, ctx, valEnv);
            if (extraArgAlgsR.IsError) return extraArgAlgsR.Error;
            if (builtin == BuiltinId.@reduce
                && extraArgAlgsR.Value is [{ Algorithm.Params.Count: > 0 } missingInitialReducer])
            {
                return ReduceInitialAccumulatorRequiresValueError(missingInitialReducer.Algorithm);
            }

            argAlgs.AddRange(extraArgAlgsR.Value);
        }

        return EvalResult<SequenceBuiltinDotCall?>.Ok(
            new SequenceBuiltinDotCall(builtin, argAlgs));
    }

    private static bool TryGetParenthesizedSequenceSpreadReceiver(Expr receiver, out Expr spreadReceiver)
    {
        if (receiver is Expr.Block({ Opens.Count: 0, Properties.Count: 0, Params.Count: 0, Output.Count: 1 } algorithm)
            && algorithm.Output[0] is Expr.SequenceSpread sequenceSpread)
        {
            spreadReceiver = sequenceSpread;
            return true;
        }

        spreadReceiver = receiver;
        return false;
    }

    private static bool HasLeadingFlatVariadicParameter(Algorithm callee, string name)
    {
        var effectiveCallee = TryGetFlatBinderUserEquivalent(callee) ?? callee;
        if (effectiveCallee is not Algorithm.User)
            return false;

        var signature = CallableSignature.FromAlgorithm(name, effectiveCallee);
        var plan = CallableBindingPlan.FromSignature(signature);
        return plan.TryGetFlatVariadicLayout(out var prefix, out _, out _)
            && prefix.Count == 0;
    }

    private static (Algorithm Args, IReadOnlyList<bool> PreserveArgBoundaries) BuildLexicalReceiverCallArgs(
        Algorithm callee,
        string name,
        Expr receiver,
        Algorithm? extraArgs)
    {
        var receiverExpr = receiver;
        var hasLeadingFlatVariadicParameter = HasLeadingFlatVariadicParameter(callee, name);
        var preserveReceiverBoundary = !hasLeadingFlatVariadicParameter;
        // The injected receiver is still one leading argument segment. When a
        // leading flat variadic parameter exists, that segment may carry its
        // emitted-count metadata into the capture after slot allocation.
        // Parenthesized receiver spread, as in (Arg...).F, can feed the
        // receiver's top-level items only to leading flat variadic receiver params.
        // Fixed receiver params keep the receiver as one argument boundary.
        if (TryGetParenthesizedSequenceSpreadReceiver(receiver, out var spreadReceiver)
            && hasLeadingFlatVariadicParameter)
        {
            receiverExpr = spreadReceiver;
        }

        var outputExprs = new List<Expr> { receiverExpr };
        var preserveArgBoundaries = new List<bool> { preserveReceiverBoundary };
        if (extraArgs is not null)
        {
            outputExprs.AddRange(extraArgs.Output);
            for (var i = 0; i < extraArgs.Output.Count; i++)
                preserveArgBoundaries.Add(false);
        }

        return (
            new Algorithm.User(
                Parent: null, Parameters: [], Opens: [],
                Properties: [], Output: outputExprs),
            preserveArgBoundaries);
    }

    private static bool TryEvaluateSequencePipeline(
        SequencePipelineInvocation invocation,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv,
        out EvalResult<CountedResult> result)
    {
        var services = new SequencePipelineEvaluationServices(
            GetDotCallLexicalBuiltinFallbackReason: (target, name, expectedBuiltin) =>
                GetDotCallLexicalBuiltinFallbackReason(target, name, expectedBuiltin, ctx),
            EvaluateDotReceiverIterationItems: receiver => EvaluateDotReceiverIterationItemsForSequenceOptimizer(receiver, ctx, valEnv),
            EvaluateSequenceIterationItems: collectionArgs => EvalSequenceIterationItems(collectionArgs, ctx, valEnv),
            ResolveArgumentAlgorithms: args => ResolveArgAlgs(args, ctx, valEnv),
            ResolveAlgorithm: expr => ResolveAlg(expr, ctx),
            EvaluateRangeCallArguments: (function, args, callSpan) => EvaluateRangeCallArgumentsForSequenceOptimizer(function, args, callSpan, ctx, valEnv));

        return SequencePipelineOptimizer.TryExecute(
            invocation,
            services,
            ctx,
            valEnv,
            ctx.SequenceDiagnostics,
            out result);
    }

    /// <summary>
    /// Semantic dot-receiver item collection shared with the sequence optimizer;
    /// this preserves the generic dot-call sequence builtin boundary rules.
    /// </summary>
    private static EvalResult<IReadOnlyList<CountedResult>> EvaluateDotReceiverIterationItemsForSequenceOptimizer(
        Expr receiver,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var receiverR = EvalSequenceBuiltinDotReceiverCounted(receiver, ctx, valEnv);
        if (receiverR.IsError)
            return receiverR.Error;

        // Mirror the generic builtin collection binding: the receiver value is
        // the bound collection, so exactly one outer sequence OR list boundary
        // is opened by the shared builtin collection-item view; any other value
        // supplies itself as one item.
        var items = BuiltinCollectionItems(receiverR.Value.Value);

        return EvalResult<IReadOnlyList<CountedResult>>.Ok(
            items
                .Select(static item => new CountedResult(item, item.ValueCount()))
                .ToList());
    }

    /// <summary>
    /// Evaluate already-recognized builtin <c>range(...)</c> arguments for the
    /// sequence optimizer while preserving the generic range call diagnostics.
    /// </summary>
    private static EvalResult<InclusiveRange> EvaluateRangeCallArgumentsForSequenceOptimizer(
        Expr function,
        Algorithm argsAlg,
        SourceSpan? callSpan,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
        => WithSpan(callSpan, WithCtx(CtxCall(function), EvalBuiltinRangeCallArguments(argsAlg, ctx, valEnv)));

    private static EvalResult<InclusiveRange> EvalBuiltinRangeCallArguments(
        Algorithm argsAlg,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var argAlgsR = ResolveArgAlgsWithSequenceSpread(argsAlg, ctx, valEnv);
        if (argAlgsR.IsError) return argAlgsR.Error;

        var expandedArgsR = ExpandSequenceSpreadBuiltinArguments(argAlgsR.Value, ctx, valEnv);
        if (expandedArgsR.IsError) return expandedArgsR.Error;

        return EvalBuiltinRangeArguments(expandedArgsR.Value, ctx, valEnv);
    }

    /// <summary>
    /// Check whether a dot call would fall through to a specific lexical
    /// builtin after structural shadowing rules are applied.
    /// </summary>
    private static string? GetDotCallLexicalBuiltinFallbackReason(
        Expr target,
        string name,
        BuiltinId expectedBuiltin,
        EvalCtx ctx)
    {
        var targetResult = ResolveAlg(target, ctx);
        if (targetResult.IsOk)
        {
            if (LookupPropBinding(targetResult.Value, name) is not null)
                return $"{name} is shadowed by a structural property";

            if (ConditionalBranchesDefineProperty(targetResult.Value, name))
                return $"{name} is shadowed by a conditional structural property";
        }
        else if (targetResult.Error is not EvalError.NotAnAlgorithm)
        {
            return $"{name} receiver resolution failed";
        }

        var calleeR = ResolveNamedAlgorithm(name, span: null, ctx);
        if (calleeR.IsError
            || calleeR.Value is not Algorithm.Builtin(var builtin)
            || builtin != expectedBuiltin)
        {
            return $"{name} does not resolve to builtin";
        }

        return null;
    }

    private static EvalResult<Result> CallLexicalWithReceiver(
        string name, Expr receiver, Algorithm? extraArgs,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var sequenceDotCallR = TryBuildSequenceBuiltinDotCall(name, receiver, extraArgs, ctx, valEnv);
        if (sequenceDotCallR.IsError) return sequenceDotCallR.Error;
        if (sequenceDotCallR.Value is { } sequenceDotCall)
            return ApplyBuiltinResolved(sequenceDotCall.Builtin, sequenceDotCall.Args, ctx, valEnv);

        var calleeR = ResolveNamedAlgorithm(name, span: null, ctx);
        if (calleeR.IsError) return calleeR.Error;
        var (combinedArgs, preserveArgBoundaries) = BuildLexicalReceiverCallArgs(calleeR.Value, name, receiver, extraArgs);
        return EvalResolvedCall(calleeR.Value, combinedArgs, ctx, valEnv, name, preserveArgBoundaries);
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

        if (TryEvaluateSequencePipeline(
            SequencePipelineInvocation.DotCall(target, name, argsOpt),
            ctx,
            valEnv,
            out var sequencePipelineR))
            return sequencePipelineR;

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
                    return ReCountValueBoundary(EvalZeroArgPropertyAccessCounted(targetAlg, prop, ZeroArgPropertyAccessKind.CountedStructural, wired, ctx, valEnv));
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
    /// Mirrors <see cref="CallLexicalWithReceiver"/>.
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
            return ApplyBuiltinCountedResolved(sequenceDotCall.Builtin, sequenceDotCall.Args, ctx, valEnv);

        var calleeR = ResolveNamedAlgorithm(name, span: null, ctx);
        if (calleeR.IsError) return calleeR.Error;
        var (combinedArgs, preserveArgBoundaries) = BuildLexicalReceiverCallArgs(calleeR.Value, name, receiver, extraArgs);
        return EvalResolvedCallCounted(calleeR.Value, combinedArgs, ctx, valEnv, name, preserveArgBoundaries);
    }

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
        => Run(expr, zeroArgPropertyResultCache, enableLoopOptimization: true);

    internal static EvalResult<Result> Run(
        Expr expr,
        IZeroArgPropertyResultCache zeroArgPropertyResultCache,
        bool enableLoopOptimization)
        => Run(expr, zeroArgPropertyResultCache, enableLoopOptimization, loopDiagnostics: null);

    internal static EvalResult<Result> Run(
        Expr expr,
        IZeroArgPropertyResultCache zeroArgPropertyResultCache,
        bool enableLoopOptimization,
        LoopOptimizationDiagnostics? loopDiagnostics)
        => Run(
            expr,
            zeroArgPropertyResultCache,
            enableLoopOptimization,
            loopDiagnostics,
            enableSequencePipelineOptimization: true,
            sequenceDiagnostics: null);

    internal static EvalResult<Result> Run(
        Expr expr,
        IZeroArgPropertyResultCache zeroArgPropertyResultCache,
        bool enableLoopOptimization,
        LoopOptimizationDiagnostics? loopDiagnostics,
        bool enableSequencePipelineOptimization,
        SequencePipelineDiagnostics? sequenceDiagnostics)
    {
        if (AlgorithmValidation.FindFirstExplicitParameterOutputViolation(expr) is { } violation)
            return new EvalError.ExplicitParametersRequireOutput() { Span = violation.Span };

        ArgumentNullException.ThrowIfNull(zeroArgPropertyResultCache);

        var ctx = new EvalCtx(
            [PreludeAlg],
            [],
            [],
            zeroArgPropertyResultCache,
            enableLoopOptimization,
            loopDiagnostics,
            enableSequencePipelineOptimization,
            sequenceDiagnostics);
        return expr is Expr.Block(var alg)
            ? EvalRootProgram(alg, expr.Span, ctx)
            : Eval(expr, ctx, []);
    }

    internal static EvalResult<CountedResult> RunCounted(Expr expr)
        => RunCounted(expr, new RunScopedZeroArgPropertyResultCache());

    internal static EvalResult<CountedResult> RunCounted(
        Expr expr,
        IZeroArgPropertyResultCache zeroArgPropertyResultCache)
    {
        if (AlgorithmValidation.FindFirstExplicitParameterOutputViolation(expr) is { } violation)
            return new EvalError.ExplicitParametersRequireOutput() { Span = violation.Span };

        ArgumentNullException.ThrowIfNull(zeroArgPropertyResultCache);

        var ctx = new EvalCtx(
            [PreludeAlg],
            [],
            [],
            zeroArgPropertyResultCache,
            EnableLoopOptimization: true,
            LoopDiagnostics: null,
            EnableSequencePipelineOptimization: true,
            SequenceDiagnostics: null);
        return expr is Expr.Block(var alg)
            ? EvalRootProgramCounted(alg, expr.Span, ctx)
            : EvalCounted(expr, ctx, []);
    }

    internal static EvalResult<CountedRootProgramResult> RunCountedWithTopLevelProperty(
        Expr expr,
        string topLevelPropertyName,
        IZeroArgPropertyResultCache zeroArgPropertyResultCache)
    {
        if (AlgorithmValidation.FindFirstExplicitParameterOutputViolation(expr) is { } violation)
            return new EvalError.ExplicitParametersRequireOutput() { Span = violation.Span };

        ArgumentNullException.ThrowIfNull(zeroArgPropertyResultCache);
        ArgumentException.ThrowIfNullOrWhiteSpace(topLevelPropertyName);

        var ctx = new EvalCtx(
            [PreludeAlg],
            [],
            [],
            zeroArgPropertyResultCache,
            EnableLoopOptimization: true,
            LoopDiagnostics: null,
            EnableSequencePipelineOptimization: true,
            SequenceDiagnostics: null);

        if (expr is Expr.Block(var alg))
            return EvalRootProgramCountedWithTopLevelProperty(alg, expr.Span, ctx, topLevelPropertyName);

        var outputR = EvalCounted(expr, ctx, []);
        return outputR.IsError
            ? outputR.Error
            : EvalResult<CountedRootProgramResult>.Ok(new CountedRootProgramResult(outputR.Value, TopLevelProperty: null));
    }

    private static EvalResult<Result> EvalRootProgram(Algorithm alg, SourceSpan? span, EvalCtx ctx)
    {
        var wired = WireToCaller(ctx, alg);
        if (wired.Params.Count == 0)
        {
            var result = EvalProgramOutput(wired, ctx, []);
            if (result.IsError
                && result.Error is EvalError.MissingOutput
                && wired is Algorithm.User { Output.Count: 0 })
            {
                return new EvalError.WithContext(new ProgramEvaluationContext(), result.Error)
                {
                    Span = result.Error.Span ?? span,
                };
            }

            return result;
        }

        var blockSpan = span ?? FirstSpan(wired.Output);
        return MissingImplicitArguments<Result>(wired.Params, blockSpan);
    }

    private static EvalResult<CountedResult> EvalRootProgramCounted(Algorithm alg, SourceSpan? span, EvalCtx ctx)
    {
        var wired = WireToCaller(ctx, alg);
        if (wired.Params.Count == 0)
        {
            var result = EvalProgramOutputCounted(wired, ctx, []);
            if (result.IsError
                && result.Error is EvalError.MissingOutput
                && wired is Algorithm.User { Output.Count: 0 })
            {
                return new EvalError.WithContext(new ProgramEvaluationContext(), result.Error)
                {
                    Span = result.Error.Span ?? span,
                };
            }

            return result;
        }

        var blockSpan = span ?? FirstSpan(wired.Output);
        return MissingImplicitArguments<CountedResult>(wired.Params, blockSpan);
    }

    private static EvalResult<CountedRootProgramResult> EvalRootProgramCountedWithTopLevelProperty(
        Algorithm alg,
        SourceSpan? span,
        EvalCtx ctx,
        string topLevelPropertyName)
    {
        var wired = WireToCaller(ctx, alg);
        if (wired.Params.Count != 0)
        {
            var blockSpan = span ?? FirstSpan(wired.Output);
            return MissingImplicitArguments<CountedRootProgramResult>(wired.Params, blockSpan);
        }

        var outputR = EvalProgramOutputCounted(wired, ctx, []);
        if (outputR.IsError)
        {
            if (outputR.Error is EvalError.MissingOutput
                && wired is Algorithm.User { Output.Count: 0 })
            {
                return new EvalError.WithContext(new ProgramEvaluationContext(), outputR.Error)
                {
                    Span = outputR.Error.Span ?? span,
                };
            }

            return outputR.Error;
        }

        var propertyR = EvalTopLevelZeroArgPropertyCounted(wired, topLevelPropertyName, ctx, []);
        return propertyR.IsError
            ? propertyR.Error
            : EvalResult<CountedRootProgramResult>.Ok(new CountedRootProgramResult(outputR.Value, propertyR.Value));
    }

    private static EvalResult<CountedResult?> EvalTopLevelZeroArgPropertyCounted(
        Algorithm alg,
        string name,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var binding = LookupPropBinding(alg, name);
        if (binding is null)
            return EvalResult<CountedResult?>.Ok(null);

        var resolvedAlgorithm = ChildOf(alg, binding.Value);
        var span = binding.DeclarationSpans.FirstOrDefault();
        if (resolvedAlgorithm.Params.Count != 0)
        {
            return WithSpan<CountedResult?>(
                span,
                new EvalError.WithContext(
                    CtxProperty(name),
                    new EvalError.ArityMismatch(resolvedAlgorithm.Params.Count, 0)));
        }

        var propertyR = WithPropertyContextOnMissingOutput(
            name,
            span,
            EvalZeroArgPropertyAccessCounted(
                new ResolvedLexicalProperty(alg, binding, resolvedAlgorithm),
                ctx,
                valEnv));

        return propertyR.IsError
            ? propertyR.Error
            : EvalResult<CountedResult?>.Ok(propertyR.Value);
    }

    /// <summary>
    /// Run evaluation and flatten to atoms at the host boundary: exact list
    /// boundaries are opened (<see cref="Result.ToHostAtoms"/>) so
    /// collection-builtin results surface their numeric contents.
    /// Lean: runFlat → EvalM (List Int).
    /// </summary>
    public static EvalResult<IReadOnlyList<decimal>> RunFlat(Expr expr)
    {
        var r = Run(expr);
        if (r.IsError) return r.Error;
        return EvalResult<IReadOnlyList<decimal>>.Ok(r.Value.ToHostAtoms());
    }

    // ── Utility ──────────────────────────────────────────────────────────────

    /// <summary>
    /// Integer exponents use exact decimal exponentiation by squaring.
    /// Negative integers are handled as a decimal reciprocal of the positive power.
    /// Non-integer exponents use approximate <see cref="Math.Pow(double, double)"/> via double,
    /// then normalize the result using the evaluator's standard floating-point cleanup.
    /// </summary>
    internal static EvalResult<Result> EvalPow(SourceSpan? span, decimal b, decimal exp)
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
