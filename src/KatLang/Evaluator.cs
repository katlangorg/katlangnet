using System.Collections;
using System.Runtime.CompilerServices;
using KatLang.Evaluation;
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
/// Builtins (If, While, Repeat, Atoms, Range, Filter, Map, Count, Contains, First, Last, Order, OrderDesc, Distinct, Take, Skip, Min, Max, Sum, Avg, Reduce) are injected via a prelude algorithm in the initial
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
    /// Budget is the run-scoped resource budget: it is a REFERENCE deliberately carried
    /// by this copied struct, so every derived context charges the same run's counters
    /// and no copy can reset them.
    /// Lean: structure EvalCtx where callStack : List Algorithm; algEnv : AlgEnv := [].
    /// </summary>
    internal readonly record struct EvalCtx(
        IReadOnlyList<Algorithm> CallStack,
        IReadOnlyList<(string Name, Algorithm Value)> AlgEnv,
        IReadOnlyList<(string Name, CountedResult Value)> CountedParamEnv,
        IZeroArgPropertyResultCache ZeroArgPropertyResultCache,
        IDeconstructionBindingCache DeconstructionBindingCache,
        bool EnableLoopOptimization,
        LoopOptimizationDiagnostics? LoopDiagnostics,
        bool EnableSequencePipelineOptimization,
        SequencePipelineDiagnostics? SequenceDiagnostics,
        EvaluationObservations? Observations,
        EvaluationBudget Budget)
    {
        /// <summary>
        /// A fresh empty context. This is a PROPERTY, not a shared static instance:
        /// every use must get its own budget, because a shared one would be global
        /// mutable evaluation state.
        /// </summary>
        public static EvalCtx Empty => new(
            [], [], [], UncachedZeroArgPropertyResultCache.Instance, UncachedDeconstructionBindingCache.Instance,
            true, null, true, null,
            null,
            EvaluationBudget.Create(null));

        /// <summary>Lean: EvalCtx.push — prepend an algorithm to the call stack.</summary>
        public EvalCtx Push(Algorithm alg)
            => new(
                Prepend(alg, CallStack),
                AlgEnv,
                CountedParamEnv,
                ZeroArgPropertyResultCache,
                DeconstructionBindingCache,
                EnableLoopOptimization,
                LoopDiagnostics,
                EnableSequencePipelineOptimization,
                SequenceDiagnostics,
                Observations,
                Budget);

        /// <summary>Lean: EvalCtx.head? — first algorithm in the call stack.</summary>
        public Algorithm? Head => CallStack.Count > 0 ? CallStack[0] : null;

        /// <summary>Lean: EvalCtx.withAlgEnv — replace the algorithm environment.</summary>
        public EvalCtx WithAlgEnv(IReadOnlyList<(string, Algorithm)> algEnv)
            => new(
                CallStack,
                algEnv,
                CountedParamEnv,
                ZeroArgPropertyResultCache,
                DeconstructionBindingCache,
                EnableLoopOptimization,
                LoopDiagnostics,
                EnableSequencePipelineOptimization,
                SequenceDiagnostics,
                Observations,
                Budget);

        /// <summary>Replace the counted callback-parameter environment.</summary>
        public EvalCtx WithCountedParamEnv(IReadOnlyList<(string, CountedResult)> countedParamEnv)
            => new(
                CallStack,
                AlgEnv,
                countedParamEnv,
                ZeroArgPropertyResultCache,
                DeconstructionBindingCache,
                EnableLoopOptimization,
                LoopDiagnostics,
                EnableSequencePipelineOptimization,
                SequenceDiagnostics,
                Observations,
                Budget);

        /// <summary>Replace the zero-argument property cache for a scoped evaluation subtree.</summary>
        public EvalCtx WithZeroArgPropertyResultCache(IZeroArgPropertyResultCache zeroArgPropertyResultCache)
            => new(
                CallStack,
                AlgEnv,
                CountedParamEnv,
                zeroArgPropertyResultCache,
                DeconstructionBindingCache,
                EnableLoopOptimization,
                LoopDiagnostics,
                EnableSequencePipelineOptimization,
                SequenceDiagnostics,
                Observations,
                Budget);
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
        Expr.AlgorithmExpr => "algorithmExpr",
        Expr.Capture => "capture",
        Expr.Call => "call",
        Expr.DotCall => "dotCall",
        Expr.Grace => "grace",
        Expr.NativeCall => "nativeCall",
        _ => "unknown",
    };

    /// <summary>
    /// Predicate defining which expression forms are allowed in open position.
    /// Only structural references to libraries are permitted. A Capture is NOT
    /// an open form: a capture is a value boundary, never algorithm/namespace
    /// identity, so `open (M)` fails open validation with BadOpenForm exactly
    /// like a spread-marked target (the parser also rejects it in source; the
    /// <see cref="ResolveAlgForOpen"/> capture arm covers dotted heads and
    /// prebuilt ASTs).
    /// Lean: Expr.isOpenForm.
    /// </summary>
    private static bool IsOpenForm(Expr e) => e is
        Expr.AlgorithmExpr or Expr.Resolve or Expr.DotCall(_, _, null);

    /// <summary>
    /// Extract a descriptive name from an open expression for error messages.
    /// Rendering is iterative and output-bounded (<see cref="ExprNameRenderer"/>):
    /// it never consumes CLR stack proportional to the expression's depth, so the
    /// arbitrarily deep internal join/spread chains the structural preflight
    /// deliberately accepts stay safe on every diagnostic path, and names beyond
    /// the bound are deterministically elided with the established <c>…</c> marker.
    /// Lean: openExprName (Lean models the unbounded spelling; the bound is
    /// C#-side host-safety presentation policy).
    /// </summary>
    internal static string OpenExprName(Expr e) => ExprNameRenderer.Render(e, ExprNameMode.Open);

    /// <summary>
    /// Renders a compound call-context expression on an actual diagnostic path and records that
    /// work for an observed run. Simple identifiers reuse their existing string.
    /// </summary>
    internal static string CallDiagnosticExprName(Expr expression, EvalCtx ctx)
        => CallDiagnosticName.FromExpression(expression).Render(ctx);

    /// <summary>
    /// Stack-only description of a callable's diagnostic name. Simple identifiers reuse their
    /// existing string; compound expressions retain the AST reference and are rendered only if an
    /// error actually needs the name. This avoids both a closure and diagnostic string allocation
    /// on successful resolved calls.
    /// </summary>
    private readonly struct CallDiagnosticName
    {
        private readonly string? _knownName;
        private readonly Expr? _expression;

        private CallDiagnosticName(string? knownName, Expr? expression)
        {
            _knownName = knownName;
            _expression = expression;
        }

        public static CallDiagnosticName FromExpression(Expr expression)
            => expression switch
            {
                Expr.Resolve(var name) when name.Length <= ExprNameRenderer.MaxRenderedNameLength
                    => new(name, null),
                Expr.Param(var name) when name.Length <= ExprNameRenderer.MaxRenderedNameLength
                    => new(name, null),
                _ => new(null, expression),
            };

        public static CallDiagnosticName FromKnown(string name) => new(name, null);

        /// <summary>
        /// A non-rendering placeholder used only to derive the callable's structural binding plan.
        /// Error-bearing signatures are rebuilt with <see cref="Render"/> on the error path.
        /// </summary>
        public string StructuralName => _knownName ?? "<anonymous>";

        public string Render(EvalCtx ctx)
        {
            if (_knownName is not null)
                return _knownName;

            ctx.Observations?.RecordCallDiagnosticNameRender();
            return OpenExprName(_expression!);
        }
    }

    /// <summary>
    /// Operand-shape spelling for binary operand-shape contexts (bare top-level
    /// binary chains, zero-shape blocks and internal sequence joins rendered as one
    /// written sequence value). Iterative and output-bounded like
    /// <see cref="OpenExprName"/>.
    /// </summary>
    private static string ExprDiagnosticName(Expr expr)
        => ExprNameRenderer.Render(expr, ExprNameMode.DiagnosticName);

    private static string BinaryExprDiagnosticName(BinaryOp op, Expr left, Expr right)
        => ExprNameRenderer.RenderBinaryDiagnosticName(op, left, right);

    private static string BinaryOperandContext(BinaryOp op, Expr left, Expr right)
        => $"while evaluating `{BinaryExprDiagnosticName(op, left, right)}`";

    // ── Error context helpers ──────────────────────────────────────────────

    private static ErrorContext CtxOpen(string key) => new OpenResolutionContext(key);
    private static ErrorContext CtxCall(CallDiagnosticName name, EvalCtx ctx) => new CallContext(name.Render(ctx));
    private static ErrorContext CtxProperty(string name) => new PropertyEvaluationContext(name);
    private static ErrorContext CtxDotCall(Expr obj, string name, EvalCtx ctx)
        => new DotCallContext(CallDiagnosticName.FromExpression(obj).Render(ctx), name);

    // ── Error context helper ────────────────────────────────────────────────

    /// <summary>
    /// Attach context to any error raised by the given result.
    /// Lean: withCtx.
    /// </summary>
    private static EvalResult<T> WithCtx<T>(ErrorContext context, EvalResult<T> result) =>
        result.IsError && !result.Error.IsResourceLimit
            ? new EvalError.WithContext(context, result.Error) { Span = result.Error.Span }
            : result;


    private static EvalResult<T> WithCtx<T>(string context, EvalResult<T> result)
        => WithCtx(new TextErrorContext(context), result);

    /// <summary>
    /// <see cref="WithCtx{T}(ErrorContext, EvalResult{T})"/> for call contexts, with
    /// the context CONSTRUCTED ONLY ON THE ERROR PATH: rendering the callee name is
    /// pure diagnostic work, so a successful call must not pay for it.
    /// </summary>
    private static EvalResult<T> WithCallCtx<T>(CallDiagnosticName function, EvalCtx ctx, EvalResult<T> result)
        => result.IsError && !result.Error.IsResourceLimit
            ? new EvalError.WithContext(CtxCall(function, ctx), result.Error) { Span = result.Error.Span }
            : result;

    /// <summary>
    /// <see cref="WithCtx{T}(ErrorContext, EvalResult{T})"/> for dot-call contexts,
    /// with the context constructed only on the error path (see
    /// <see cref="WithCallCtx{T}"/>).
    /// </summary>
    private static EvalResult<T> WithDotCallCtx<T>(Expr target, string name, EvalCtx ctx, EvalResult<T> result)
        => result.IsError && !result.Error.IsResourceLimit
            ? new EvalError.WithContext(CtxDotCall(target, name, ctx), result.Error) { Span = result.Error.Span }
            : result;

    /// <summary>
    /// The generic call-expression DIAGNOSTIC BOUNDARY, reusable by an optimizer that
    /// evaluates a planned call without going through <see cref="EvalCallExpr"/> /
    /// <see cref="EvalCallCountedExpr"/>. It is exactly the composition those two
    /// dispatch sites apply — <see cref="WithCallCtx{T}"/> inside
    /// <see cref="WithSpan{T}"/> — so a planned call reports the same context frame,
    /// the same callee spelling, the same resource-limit exemption, and the same
    /// span attribution as the expression it replaces.
    /// <paramref name="callExpr"/> and <paramref name="callee"/> must be the ORIGINAL
    /// planned expressions, so span/context attribution cannot drift from the generic
    /// evaluator's.
    /// </summary>
    internal static EvalResult<T> WithPlannedCallBoundary<T>(
        Expr callExpr,
        Expr callee,
        EvalCtx ctx,
        EvalResult<T> result)
        => WithSpan(callExpr.Span, WithCallCtx(CallDiagnosticName.FromExpression(callee), ctx, result));

    /// <summary>
    /// Attaches an expression's span to an error that does not already carry a more
    /// specific one. Internal rather than private so an optimizer that ELIDES an
    /// expression node can reproduce that node's span attribution point instead of
    /// letting the error float up to an enclosing expression (see
    /// <c>SequencePipelineOptimizer.WithContext</c> for the fused filter expression).
    /// </summary>
    internal static EvalResult<T> WithSpan<T>(SourceSpan? span, EvalResult<T> result) =>
        result.IsError ? AtSpanIfMissing(result.Error, span) : result;

    /// <summary>
    /// Attaches a source span to an error that does not already carry one. The single
    /// implementation behind <see cref="WithSpan{T}"/> and the resource-limit charge
    /// points, which hold a bare <see cref="EvalError"/> rather than a result.
    /// </summary>
    private static EvalError AtSpanIfMissing(EvalError error, SourceSpan? span)
        => error.Span is null && span is not null ? error with { Span = span } : error;

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
            var key = openExpr is Expr.AlgorithmExpr or Expr.Capture
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
            : new EvalError.TypeMismatch(NumericScalarOperandMessage(ExprNameRenderer.BinaryOpText(op), side, value));
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

    internal static string FormatResultForDiagnostic(Result value)
    {
        switch (value)
        {
            case Result.Atom(var number):
                return number.ToString(System.Globalization.CultureInfo.InvariantCulture);
            case Result.Str(var str):
                return $"'{str}'";
            case Result.SequenceValue:
            case Result.ListValue:
                break;
            default:
                return "value";
        }

        // Diagnostic values nest as deep and as wide as any runtime value
        // (see the depth note on Result), so the walk uses indexed
        // continuation frames: the builder is the required output; traversal
        // storage is one suspended frame per open structure level.
        var text = new System.Text.StringBuilder();
        var suspended = new Stack<(IReadOnlyList<Result> Items, int Next, char Close)>();
        var (items, close) = value switch
        {
            Result.SequenceValue(var rootItems) => (rootItems, ')'),
            Result.ListValue(var rootItems) => (rootItems, ']'),
            _ => throw new ArgumentException("Diagnostic structure walk requires a sequence or list value.", nameof(value)),
        };
        text.Append(close == ')' ? '(' : '[');
        var next = 0;

        while (true)
        {
            if (next >= items.Count)
            {
                text.Append(close);
                if (suspended.Count == 0) return text.ToString();
                (items, next, close) = suspended.Pop();
                continue;
            }

            if (next > 0) text.Append(", ");
            var child = items[next];
            next++;

            switch (child)
            {
                case Result.Atom(var number):
                    text.Append(number.ToString(System.Globalization.CultureInfo.InvariantCulture));
                    break;
                case Result.Str(var str):
                    text.Append('\'').Append(str).Append('\'');
                    break;
                case Result.SequenceValue(var childItems):
                    suspended.Push((items, next, close));
                    (items, next, close) = (childItems, 0, ')');
                    text.Append('(');
                    break;
                case Result.ListValue(var childItems):
                    suspended.Push((items, next, close));
                    (items, next, close) = (childItems, 0, ']');
                    text.Append('[');
                    break;
                default:
                    text.Append("value");
                    break;
            }
        }
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
    /// Evaluate and validate the arguments for <c>range(start, stop)</c>.
    /// This is the single range-boundary validation path used by both the
    /// builtin and sequence-pipeline direct range iteration.
    /// </summary>
    private static EvalResult<InclusiveRange> EvalBuiltinRangeArguments(
        IReadOnlyList<ResolvedArgumentAlgorithm> args,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        if (args.Count != 2)
            return WrongBuiltinArity(BuiltinId.@range, args.Count);

        var startR = EvalResolvedArgument(args[0], ctx, valEnv);
        if (startR.IsError) return startR.Error;
        var startIntR = ExpectWholeInt(startR.Value, "range start");
        if (startIntR.IsError) return startIntR.Error;

        var stopR = EvalResolvedArgument(args[1], ctx, valEnv);
        if (stopR.IsError) return stopR.Error;
        var stopIntR = ExpectWholeInt(stopR.Value, "range stop");
        if (stopIntR.IsError) return stopIntR.Error;

        return EvalResult<InclusiveRange>.Ok(new InclusiveRange(startIntR.Value, stopIntR.Value));
    }

    /// <summary>
    /// Enumerate the validated inclusive integer bounds for <c>range(start, stop)</c>.
    /// The inclusive-bound check runs BEFORE the step, never after: bounds are whole
    /// numbers, so the cursor lands exactly on <c>Stop</c>, and stepping only while
    /// strictly inside the bound keeps the enumeration total at the
    /// <see cref="decimal"/> extremes (<c>range(decimal.MaxValue, decimal.MaxValue)</c>
    /// must yield its one value, not overflow on a step past the bound).
    /// </summary>
    internal static IEnumerable<decimal> EnumerateInclusiveRangeValues(InclusiveRange range)
    {
        if (range.Start <= range.Stop)
        {
            var current = range.Start;
            yield return current;
            while (current < range.Stop)
            {
                current += 1m;
                yield return current;
            }
        }
        else
        {
            var current = range.Start;
            yield return current;
            while (current > range.Stop)
            {
                current -= 1m;
                yield return current;
            }
        }
    }

    /// <summary>
    /// Count the values that <see cref="EnumerateInclusiveRangeValues"/> would produce,
    /// saturating at <see cref="long.MaxValue"/>. The subtraction itself can exceed
    /// <see cref="decimal.MaxValue"/> for opposite-sign bounds, so that case is
    /// detected without performing it — any such span is far beyond the saturation
    /// ceiling anyway.
    /// </summary>
    internal static long CountInclusiveRangeValues(InclusiveRange range)
    {
        var lo = Math.Min(range.Start, range.Stop);
        var hi = Math.Max(range.Start, range.Stop);
        if (lo < 0m && hi > decimal.MaxValue + lo)
            return long.MaxValue;

        var span = hi - lo;
        return span >= long.MaxValue ? long.MaxValue : (long)span + 1;
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
    /// only an explicit caller-site <c>spread</c> opens it. Lean: unpackArgs.
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
        EvalError? ValueError,
        CountedResult? PreparedValue = null);

    private readonly record struct ResolvedArgumentAlgorithm(
        Algorithm? Algorithm,
        bool SpreadsSequence)
    {
        /// <summary>
        /// The already-computed value of this argument, when the caller evaluated it before
        /// assembling the call. Used for dotted receivers and builtin callback arguments,
        /// both of which have already been evaluated before builtin binding begins.
        ///
        /// <para><see cref="Algorithm"/> retains a source-backed algorithm channel when one
        /// exists. Callback data values and dotted sequence-builtin receivers leave that
        /// channel null so their structure is not eagerly rebuilt as an AST; an
        /// algorithm-only consumer can recreate the legacy channel lazily from this counted
        /// value. The value channel always uses this field directly and never re-evaluates
        /// a reconstructed literal.</para>
        /// </summary>
        public CountedResult? PreparedValue { get; init; }
    }

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
        FlatCollecting,
    }

    private readonly record struct GenericLoopStepBindingSelection(
        GenericLoopStepBindingShape Shape,
        CallableBindingPlan? Plan);

    private readonly record struct CallableArgumentBindings<T>(
        IReadOnlyList<(string ParameterName, T Item)> NormalBindings,
        string? CollectingParameterName,
        IReadOnlyList<T> CollectingItems);

    private readonly record struct FlatCollectingBindingLayout(
        CallableSignature Signature,
        string CollectingName);

    private readonly record struct CollectingCapture(
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

        if (plan.RequiresPatternedBinding || plan.HasTopLevelCollecting)
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

        if (plan.TryGetFlatCollectingLayout(out _, out _, out _))
            return new GenericLoopStepBindingSelection(GenericLoopStepBindingShape.FlatCollecting, plan);

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

    private static bool TryGetFlatCollectingBindingLayout(
        CallableBindingPlan plan,
        out FlatCollectingBindingLayout layout)
    {
        if (!plan.TryGetFlatCollectingLayout(out var prefix, out var collecting, out var suffix))
        {
            layout = default;
            return false;
        }

        layout = new FlatCollectingBindingLayout(
            plan.Signature,
            collecting.Name);
        return true;
    }

    private static bool TryGetLegacyFlatCollectingBindingLayout(
        Algorithm algorithm,
        string callableName,
        out FlatCollectingBindingLayout layout)
    {
        var parameters = algorithm.Parameters;
        for (var index = 0; index < parameters.Count; index++)
        {
            var parameter = parameters[index];
            if (parameter.Kind != ParameterKind.Collecting)
                continue;

            var signature = new CallableSignature(
                callableName,
                parameters
                    .Select(static parameter => new CallableParameter(parameter.Name, parameter.Kind))
                    .ToArray());
            layout = new FlatCollectingBindingLayout(
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
        Func<int, int, EvalError> arityMismatch)
    {
        if (signature.Validate() is { } validationError)
            return validationError;

        var collectingIndex = signature.CollectingParameterIndex;
        if (collectingIndex < 0)
        {
            if (items.Count != signature.Parameters.Count)
                return arityMismatch(signature.Parameters.Count, items.Count);

            return EvalResult<CallableArgumentBindings<T>>.Ok(new CallableArgumentBindings<T>(
                signature.Parameters.Zip(items, static (parameter, item) => (parameter.Name, item)).ToList(),
                CollectingParameterName: null,
                CollectingItems: []));
        }

        // The minimum is the FIXED (non-collecting) parameter count: like every
        // other collecting binding, the collecting parameter may collect ZERO items
        // (an empty collected segment is the exact list `[]`). This is the same rule the shared pattern
        // binder applies (BindParameterPatternList: required = patterns - 1).
        // (Collection builtins no longer bind here: they are ordinary
        // fixed-arity callables bound in BindSequenceBuiltinArguments.)
        var requiredNormalItemCount = signature.Parameters.Count - 1;
        if (items.Count < requiredNormalItemCount)
            return arityMismatch(requiredNormalItemCount, items.Count);

        var suffixCount = signature.Parameters.Count - collectingIndex - 1;
        var suffixStart = items.Count - suffixCount;
        var normalBindings = new List<(string ParameterName, T Item)>(requiredNormalItemCount);

        for (var index = 0; index < collectingIndex; index++)
            normalBindings.Add((signature.Parameters[index].Name, items[index]));

        for (var suffixIndex = 0; suffixIndex < suffixCount; suffixIndex++)
        {
            var parameterIndex = collectingIndex + 1 + suffixIndex;
            var itemIndex = suffixStart + suffixIndex;
            normalBindings.Add((signature.Parameters[parameterIndex].Name, items[itemIndex]));
        }

        var collectingItems = items
            .Skip(collectingIndex)
            .Take(suffixStart - collectingIndex)
            .ToList();

        return EvalResult<CallableArgumentBindings<T>>.Ok(new CallableArgumentBindings<T>(
            normalBindings,
            signature.Parameters[collectingIndex].Name,
            collectingItems));
    }

    private static EvalResult<CallableArgumentBindings<BindingInputSlot>> BindItemsToFlatCollectingLayout(
        FlatCollectingBindingLayout layout,
        IReadOnlyList<BindingInputSlot> items,
        Func<int, int, EvalError> arityMismatch)
        => BindCallableArguments(layout.Signature, items, arityMismatch);

    /// <summary>
    /// Collect the item segment assigned to a collecting binding as ONE exact immutable list value.
    ///
    /// KatLang distinguishes three item-supply operations by receiver purpose:
    /// <c>capture</c> — ordinary value/output capture, the canonicalizing
    /// boundary (<see cref="Result.FromItems"/>, singleton erasure applies);
    /// <c>collect</c> — THIS operation: a collecting binding (collecting parameter) materializes
    /// exactly the assigned items as one exact immutable list
    /// (<c>CollectSegment([]) == []</c>, <c>CollectSegment([v]) == [v]</c>, never
    /// erased); and <c>spread</c> — the postfix spread marker
    /// (<see cref="Result.SpreadItems"/>), which opens one sequence OR list
    /// boundary. The round trip <c>SpreadItems(CollectSegment(xs)) == xs</c>
    /// makes collecting-parameter forwarding ordinary list spread with no hidden
    /// raw-supply metadata. Snapshot construction: the public
    /// <see cref="Result.ListValue"/> constructor copies the supplied items,
    /// so no caller-retained buffer can mutate the collected value.
    /// Lean: <c>collectSegment</c>.
    /// </summary>
    private static EvalResult<Result.ListValue> CollectSegment(
        EvalCtx ctx,
        IReadOnlyList<Result> capturedValues,
        SourceSpan? span = null)
    {
        if (ReserveCollection(ctx, capturedValues.Count, span) is { } error)
            return error;

        return EvalResult<Result.ListValue>.Ok(
            Result.ListValue.TakeOwnership(capturedValues.ToArray()));
    }

    /// <summary>
    /// True when an argument's resolved algorithm meaning is genuinely
    /// FUNCTION-shaped — a builtin, a conditional clause family, or an
    /// algorithm declaring parameters/patterns — as opposed to a
    /// zero-parameter VALUE property that merely resolved through the dual
    /// algorithm channel. Used to decide whether a valueless argument
    /// bound by a collecting parameter gets the targeted "collects values, but ... is a function"
    /// diagnostic or surfaces its genuine value-evaluation error.
    /// Lean: <c>Algorithm.isFunctionShaped</c>.
    /// </summary>
    private static bool IsFunctionShapedAlgorithm(Algorithm algorithm)
        => algorithm switch
        {
            Algorithm.Builtin => true,
            Algorithm.Conditional => true,
            _ => algorithm.Params.Count > 0 || algorithm.ParameterPatterns.Count > 0,
        };

    private static EvalResult<CollectingCapture> CreateCollectingCapture(
        EvalCtx ctx,
        string name,
        IReadOnlyList<Result> capturedValues,
        SourceSpan? span = null)
    {
        var capturedResultR = CollectSegment(ctx, capturedValues, span);
        if (capturedResultR.IsError) return capturedResultR.Error;
        var capturedResult = capturedResultR.Value;
        // A list value is one visible value, so a collecting binding always carries
        // emitted count 1 (including the empty collected list `[]`).
        return EvalResult<CollectingCapture>.Ok(new CollectingCapture(
            name,
            capturedResult,
            new CountedResult(capturedResult, 1)));
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

        return EvalExplicitSequenceValueRowSlots(alg.Output, ctx.Push(alg), valEnv);
    }

    /// <summary>
    /// The shared written-slot loop over ordered bundle rows: each row
    /// contributes its explicit written slots. Algorithm-shaped groupings reach
    /// it after pushing their own scope; a <see cref="Expr.Capture"/> body
    /// reaches it directly (captures own no scope).
    /// </summary>
    private static EvalResult<IReadOnlyList<Result>> EvalExplicitSequenceValueRowSlots(
        IReadOnlyList<Expr> rows,
        EvalCtx rowCtx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var slots = new List<Result>();
        foreach (var expr in rows)
        {
            var exprSlotsR = EvalExplicitSequenceValueExprSlots(expr, rowCtx, valEnv);
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
        // A nested written grouping level materializes exactly one item,
        // combined with the same shallow singleton-erasing rule as ordinary
        // capture evaluation (CombineOutputSlots). A singleton group such as
        // `(A)` IS its single already-evaluated item and an all-spread-empty
        // group is `()` — never a literal-unwritable orphan such as `(5)`.
        // Both node kinds keep this written-slot view: a capture body directly,
        // and a zero-parameter scoped block through its algorithm.
        if (expr is Expr.Capture(var captureBody))
        {
            var nestedItemsR = EvalExplicitSequenceValueRowSlots(captureBody, ctx, valEnv);
            if (nestedItemsR.IsError) return nestedItemsR.Error;

            return EvalResult<IReadOnlyList<Result>>.Ok([CombineOutputSlots(nestedItemsR.Value)]);
        }

        if (expr is Expr.AlgorithmExpr(var algorithm))
        {
            var wired = WireToCaller(ctx, algorithm);
            if (wired.Params.Count == 0)
            {
                var nestedItemsR = EvalExplicitSequenceValueItems(wired, ctx, valEnv);
                if (nestedItemsR.IsError) return nestedItemsR.Error;

                return EvalResult<IReadOnlyList<Result>>.Ok([CombineOutputSlots(nestedItemsR.Value)]);
            }
        }

        var countedR = EvalCounted(expr, ctx, valEnv);
        if (countedR.IsError) return countedR.Error;

        // WRITTEN-SLOT REIFICATION: a non-spread expression occupying one
        // written slot contributes exactly ONE persistent value — the value its
        // counted supply denotes — regardless of how many items the expression
        // emitted (zero, one, or many; a counted-multi supply such as an index
        // projection is already represented by one structural value). Only an
        // explicit spread supplies the value's items into the surrounding item slots.
        return expr is Expr.SequenceSpread
            ? EvalResult<IReadOnlyList<Result>>.Ok(CountedTopLevelValues(countedR.Value))
            : EvalResult<IReadOnlyList<Result>>.Ok([countedR.Value.Value]);
    }

    private static EvalResult<IReadOnlyList<Result>> GetSequenceValuePatternItems(ParameterPatternInput input)
    {
        if (input.ExplicitSequenceValueItems is not null)
            return EvalResult<IReadOnlyList<Result>>.Ok(input.ExplicitSequenceValueItems);

        // A received sequence value or exact list value opens to its immediate
        // items (Lean: Result.structureItems?): the deconstruction receiver
        // opens ONE lone structure boundary of either kind, so
        // `x, y, z = [1, 2, 3]` binds like `x, y, z = [1, 2, 3]*`.
        if (input.Value?.StructureItems() is { } structureItems)
            return EvalResult<IReadOnlyList<Result>>.Ok(structureItems);

        return input.ValueError ?? new EvalError.BadArity();
    }

    /// <summary>
    /// Arity mismatch produced by binding one nested sequence-value parameter
    /// pattern group's OWN items. The structured payload keeps the innermost
    /// Lean-aligned <see cref="EvalError.ArityMismatch"/> unchanged; the added
    /// context only attributes the failure to the written group (e.g.
    /// <c>(b, c)</c>) instead of the enclosing call's argument count.
    /// Genuine top-level call-arity mismatches and argument evaluation errors
    /// passing through the binder are never wrapped.
    /// </summary>
    private static EvalError SequenceValuePatternArityMismatch(
        SequenceValueParameterPattern group,
        int required,
        int actual)
        => new EvalError.WithContext(
            new SequenceValueParameterBindingContext(
                group.DisplayName,
                group.Items.Any(static item => item is CaptureParameterPattern { Kind: ParameterKind.Collecting })),
            new EvalError.ArityMismatch(required, actual));

    private static EvalResult<UserCallBindings> BindParameterPattern(
        ParameterPattern pattern,
        ParameterPatternInput input,
        EvalCtx ctx,
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

            case CaptureParameterPattern { Kind: ParameterKind.Collecting }:
                return new EvalError.BadArity();

            case SequenceValueParameterPattern group:
                {
                    var itemsR = GetSequenceValuePatternItems(input);
                    // A non-grouped scalar value is a one-item supply for the
                    // prefix/collecting/suffix matcher (the same normalization the function
                    // deconstruction path applies via rule 4). This lets a scalar
                    // right-hand side bind a collecting pattern that captures zero items,
                    // e.g. `first, *tail = 1` (first = 1, tail = []), instead of being
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
                        ctx,
                        allowAlgorithmBindings: false,
                        (required, actual) => SequenceValuePatternArityMismatch(group, required, actual));
                }

            default:
                return new EvalError.BadArity();
        }
    }

    private static EvalResult<UserCallBindings> BindParameterPatternList(
        IReadOnlyList<ParameterPattern> patterns,
        IReadOnlyList<ParameterPatternInput> inputs,
        EvalCtx ctx,
        bool allowAlgorithmBindings,
        Func<int, int, EvalError> arityMismatch)
    {
        var collectingIndex = -1;
        for (var index = 0; index < patterns.Count; index++)
        {
            if (patterns[index] is not CaptureParameterPattern { Kind: ParameterKind.Collecting })
                continue;

            if (collectingIndex >= 0)
                return new EvalError.BadArity();

            collectingIndex = index;
        }

        var valueBindings = new List<(string, Result)>();
        var countedBindings = new List<(string, CountedResult)>();
        var algorithmBindings = new List<(string, Algorithm)>();
        // Running name -> value indexes over the accumulators. The prior implementation rebuilt a
        // name set and linear-scanned the accumulators on EVERY added binding, which is O(k) per
        // binding and O(patterns^2) across a whole pattern list — the residual quadratic in one
        // wide-deconstruction bind. These indexes keep the repeated-bind equality check (same name
        // must carry an equal value; unequal is an arity error) O(1) amortized without changing it.
        var valueBindingIndex = new Dictionary<string, Result>(StringComparer.Ordinal);
        var countedBindingIndex = new Dictionary<string, CountedResult>(StringComparer.Ordinal);

        EvalResult<bool> AddBindings(UserCallBindings bindings)
        {
            // The two name sets are only consulted by the algorithm-binding repeated-bind rule
            // below. Compute them (over the pre-add accumulator state) only when this binding set
            // actually carries algorithm bindings, so the common value/counted-only path — every
            // deconstruction capture — never pays for them.
            HashSet<string>? existingValueNames = null;
            HashSet<string>? incomingValueNames = null;
            if (bindings.AlgorithmBindings.Count > 0)
            {
                existingValueNames = valueBindingIndex.Keys.ToHashSet(StringComparer.Ordinal);
                incomingValueNames = bindings.ValueBindings
                    .Select(static binding => binding.Item1)
                    .ToHashSet(StringComparer.Ordinal);
            }

            foreach (var binding in bindings.ValueBindings)
            {
                if (valueBindingIndex.TryGetValue(binding.Item1, out var existing))
                {
                    if (!Result.ValueComparer.Equals(existing, binding.Item2))
                        return new EvalError.BadArity();
                    continue;
                }

                valueBindings.Add(binding);
                valueBindingIndex[binding.Item1] = binding.Item2;
            }

            foreach (var binding in bindings.CountedBindings)
            {
                if (countedBindingIndex.TryGetValue(binding.Item1, out var existing))
                {
                    if (!Result.ValueComparer.Equals(existing.Value, binding.Item2.Value))
                        return new EvalError.BadArity();
                    continue;
                }

                countedBindings.Add(binding);
                countedBindingIndex[binding.Item1] = binding.Item2;
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

                if (!existingValueNames!.Contains(binding.Item1) || !incomingValueNames!.Contains(binding.Item1))
                {
                    return new EvalError.TypeMismatch(
                        "Repeated bind equality is not supported for algorithm-only arguments");
                }
            }

            return EvalResult<bool>.Ok(true);
        }

        EvalResult<bool> BindOne(int patternIndex, int inputIndex)
        {
            var boundR = BindParameterPattern(patterns[patternIndex], inputs[inputIndex], ctx, allowAlgorithmBindings);
            if (boundR.IsError) return boundR.Error;

            return AddBindings(boundR.Value);
        }

        if (collectingIndex < 0)
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

        for (var index = 0; index < collectingIndex; index++)
        {
            var boundR = BindOne(index, index);
            if (boundR.IsError) return boundR.Error;
        }

        var suffixCount = patterns.Count - collectingIndex - 1;
        var suffixInputStart = inputs.Count - suffixCount;
        for (var suffixIndex = 0; suffixIndex < suffixCount; suffixIndex++)
        {
            var boundR = BindOne(collectingIndex + 1 + suffixIndex, suffixInputStart + suffixIndex);
            if (boundR.IsError) return boundR.Error;
        }

        var collectingCapture = (CaptureParameterPattern)patterns[collectingIndex];
        var capturedValues = new List<Result>(suffixInputStart - collectingIndex);
        for (var inputIndex = collectingIndex; inputIndex < suffixInputStart; inputIndex++)
        {
            var input = inputs[inputIndex];
            if (input.Value is null)
            {
                // A collecting binding collects VALUES. A FUNCTION-shaped argument
                // (a builtin, a clause family, or a parameterized algorithm)
                // has no value to collect — only fixed parameters keep the
                // dual algorithm channel — so name the actual conflict instead
                // of surfacing the argument's incidental value-evaluation
                // error. A zero-parameter VALUE property whose body failed is
                // NOT a function: its genuine evaluation error surfaces.
                if (input.Algorithm is { } algorithm && IsFunctionShapedAlgorithm(algorithm))
                {
                    return new EvalError.TypeMismatch(
                        $"Collecting parameter `*{collectingCapture.Name}` collects values, but a supplied argument is a function. " +
                        "Pass a value, or call the function so its result is collected.");
                }

                return input.ValueError ?? new EvalError.BadArity();
            }

            capturedValues.Add(input.Value);
        }

        var captureR = CreateCollectingCapture(ctx, collectingCapture.Name, capturedValues, collectingCapture.Span);
        if (captureR.IsError) return captureR.Error;
        var capture = captureR.Value;
        var captureBindingsR = AddBindings(new UserCallBindings(
            [(capture.Name, capture.Value)],
            [(capture.Name, capture.CountedValue)],
            []));
        if (captureBindingsR.IsError) return captureBindingsR.Error;

        return EvalResult<UserCallBindings>.Ok(new UserCallBindings(valueBindings, countedBindings, algorithmBindings));
    }

    private static EvalResult<UserCallBindings> BindPatternedUserCall(
        Algorithm callee,
        OutputBundle args,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv,
        CallDiagnosticName calleeName,
        IReadOnlyList<bool>? preserveArgBoundaries = null)
    {
        // Passive, run-scoped observation: this is the one path that binds a deconstruction helper's
        // shared N-capture pattern in both the old per-target and new shared-bind implementations, so
        // a run's observer counts N binds under the old design and exactly one under the shared bind.
        // Null for ordinary runs (no material effect); an observed run records through this context.
        if (callee is Algorithm.User { IsAssignmentDeconstructionHelper: true })
            ctx.Observations?.RecordDeconstructionFullBind();

        var inputsR = BuildCallArgumentInputs(
            args,
            ctx,
            valEnv,
            preserveArgBoundaries,
            includeExplicitSequenceValueItems: true);
        if (inputsR.IsError) return inputsR.Error;

        var bindingsR = BindParameterPatternList(
            callee.ParameterPatterns,
            inputsR.Value,
            ctx,
            allowAlgorithmBindings: true,
            (required, actual) => new EvalError.ArityMismatch(required, actual)
            {
                Signature = CallableSignature.FromAlgorithm(calleeName.Render(ctx), callee),
            });

        // Assignment deconstruction is parser-elaborated into an anonymous
        // inline helper; phrase its binding failures against the WRITTEN
        // assignment pattern instead of leaking the synthetic call shape
        // ("Algorithm `(inline library)` expects ..."). Wrap ONLY genuine
        // shape failures: when an input slot carried no value, the surfaced
        // ArityMismatch is (or reflects) that argument's own value-evaluation
        // error — re-wording it would misattribute unrelated numbers to the
        // written pattern (e.g. `x, y = sum` leaking sum's 0/0 arity error).
        // The helper binds through one synthetic inline sequence-value pattern,
        // so its shape failure may arrive wrapped in that pattern's
        // SequenceValueParameterBindingContext — the assignment-focused
        // DeconstructionBindingContext takes precedence and replaces it.
        if (bindingsR.IsError
            && callee is Algorithm.User { IsAssignmentDeconstructionHelper: true }
            && TryGetDeconstructionShapeMismatch(bindingsR.Error) is { } deconstructionMismatch
            && inputsR.Value.All(static input => input.Value is not null))
        {
            return new EvalError.WithContext(
                new DeconstructionBindingContext(
                    callee.Parameters.Select(static parameter => parameter.DisplayName).ToList(),
                    callee.Parameters.Any(static parameter => parameter.Kind == ParameterKind.Collecting)),
                deconstructionMismatch);
        }

        return bindingsR;
    }

    /// <summary>
    /// Recognize a deconstruction helper's genuine binding-shape failure: either
    /// a bare top-level <see cref="EvalError.ArityMismatch"/>, or one wrapped in
    /// the nested-group <see cref="SequenceValueParameterBindingContext"/> the
    /// helper's synthetic inline pattern produced (at most one such layer exists:
    /// only the innermost failing group attaches its context). Returns the inner
    /// mismatch to re-wrap in the assignment-focused context, or null when the
    /// error is not a shape mismatch (e.g. a passed-through argument error).
    /// </summary>
    private static EvalError.ArityMismatch? TryGetDeconstructionShapeMismatch(EvalError error)
        => error switch
        {
            EvalError.ArityMismatch direct => direct,
            EvalError.WithContext { ErrorContext: SequenceValueParameterBindingContext, Inner: EvalError.ArityMismatch nested } => nested,
            _ => null,
        };

    /// <summary>
    /// Shared lazy binding of one assignment-deconstruction group. All N target helpers of a
    /// deconstruction apply the SAME shared N-capture pattern to the SAME hoisted source value,
    /// so the whole bind is computed once per (group, binding context) and each target projects
    /// its own slot. The first demanded target pays the full bind (RHS evaluation, one pattern
    /// bind, one collected-list materialization); every later target of the same group projects in
    /// O(1). Deferred semantics are unchanged: nothing binds until a target is demanded, and a
    /// binding failure (wrong arity, phrased against the written pattern by
    /// <see cref="BindPatternedUserCall"/>) surfaces from the first demanded target with its span
    /// intact. Returns <c>null</c> only when the helper is not a shareable parser-elaborated group
    /// (no group token, or an out-of-range projection index on a hand-built AST), so the caller
    /// falls back to the ordinary per-call binding path.
    /// </summary>
    private static EvalResult<Result>? TryProjectSharedDeconstructionTarget(
        Algorithm.User helper,
        OutputBundle args,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv,
        CallDiagnosticName calleeName,
        IReadOnlyList<bool>? preserveArgBoundaries)
    {
        var group = helper.AssignmentDeconstructionGroup;
        if (group is null)
            return null;

        var execution = new DeconstructionBindingExecution(
            group,
            ValueEnvironmentCacheIdentity(valEnv),
            ctx.AlgEnv,
            ctx.CountedParamEnv);

        var sharedR = ctx.DeconstructionBindingCache.GetOrBind(
            execution,
            () =>
            {
                var bindingsR = BindPatternedUserCall(helper, args, ctx, valEnv, calleeName, preserveArgBoundaries);
                if (bindingsR.IsError)
                    return bindingsR.Error;

                // Materialize the shared bind as the bound values in TARGET order. Index the bind by
                // capture name and read the values out in the helper's parameter order (the written
                // target order): the front/collecting/back matcher may emit bindings in a different order
                // than the written targets (a movable collecting binding binds the fixed prefix and suffix before
                // the middle). The helper body is `Param(xi)`, which resolves xi from the counted
                // parameter environment first and the value environment second; deconstruction
                // captures populate the value bindings (the counted bindings stay empty), so seed the
                // index from the value bindings and let any counted binding win, matching that lookup
                // order exactly. The counted result then re-counts the value at the boundary and the
                // non-counted result is the value itself, so the value alone reproduces both without
                // the O(N) environment scan.
                var bindings = bindingsR.Value;
                var valueByName = new Dictionary<string, Result>(bindings.ValueBindings.Count, StringComparer.Ordinal);
                foreach (var (name, value) in bindings.ValueBindings)
                    valueByName[name] = value;
                foreach (var (name, counted) in bindings.CountedBindings)
                    valueByName[name] = counted.Value;

                var parameters = helper.Parameters;
                var projected = new Result[parameters.Count];
                for (var i = 0; i < parameters.Count; i++)
                {
                    if (!valueByName.TryGetValue(parameters[i].Name, out var value))
                        return new EvalError.UnknownName(parameters[i].Name);
                    projected[i] = value;
                }
                return EvalResult<IReadOnlyList<Result>>.Ok(projected);
            });

        if (sharedR.IsError)
            return sharedR.Error;

        var values = sharedR.Value;
        var index = helper.AssignmentDeconstructionTargetIndex;
        if ((uint)index >= (uint)values.Count)
            return null;

        return EvalResult<Result>.Ok(values[index]);
    }

    /// <summary>
    /// Shared call argument-slot assembly used by EVERY callable shape (flat
    /// fixed, flat/mixed variadic, patterned, and multi-clause conditional):
    /// each written argument slot is evaluated exactly once, left to right; every non-spread slot is
    /// reified as exactly ONE argument value (with its dual algorithm view
    /// where resolvable), and every explicit spread slot is expanded by
    /// exactly one value boundary into ordinary argument slots. The final
    /// argument supply is formed BEFORE any arity checking, clause selection,
    /// conditional dispatch, or pattern binding — the callee's internal
    /// representation never influences the meaning of caller-side spread.
    /// Dot-call receiver segments honor <paramref name="preserveArgBoundaries"/>
    /// (an injected receiver stays one boundary and is never expanded).
    /// Lean: <c>collectVariadicCallItems</c>.
    /// </summary>
    private static EvalResult<IReadOnlyList<ParameterPatternInput>> BuildCallArgumentInputs(
        OutputBundle args,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv,
        IReadOnlyList<bool>? preserveArgBoundaries = null,
        bool includeExplicitSequenceValueItems = false)
    {
        var maybeAlgsR = TryResolveArgAlgs(args, ctx);
        if (maybeAlgsR.IsError) return maybeAlgsR.Error;

        // Argument slots evaluate directly in the CALLER's context: the bundle
        // owns no scope, so there is no argument-level lexical frame to push.
        // (An argument frame would necessarily be empty and caller-wired, so
        // lookup behavior is identical to pushing one — none exists.)
        var maybeAlgs = maybeAlgsR.Value;
        var inputs = new List<ParameterPatternInput>();

        for (var index = 0; index < args.Count; index++)
        {
            var argExpr = args[index];
            var maybeAlg = index < maybeAlgs.Count ? maybeAlgs[index] : null;
            var preserveArgBoundary = PreserveCallArgBoundary(preserveArgBoundaries, index);
            var isDotReceiverSegment = IsInjectedDotCallReceiverSegment(preserveArgBoundaries, index);

            if (argExpr is Expr.SequenceSpread && !preserveArgBoundary)
            {
                var suppliedR = EvalCounted(argExpr, ctx, valEnv);
                if (suppliedR.IsError)
                    return suppliedR.Error;

                foreach (var value in CountedTopLevelValues(suppliedR.Value))
                    inputs.Add(new ParameterPatternInput(value, Algorithm: null, ValueError: null, ExplicitSequenceValueItems: null));

                continue;
            }

            var preparedR = PrepareCallArgumentEvaluation(
                argExpr,
                ctx,
                valEnv,
                isDotReceiverSegment,
                includeExplicitSequenceValueItems);
            if (preparedR.IsOk)
            {
                inputs.Add(new ParameterPatternInput(
                    preparedR.Value.Counted.Value,
                    maybeAlg,
                    ValueError: null,
                    preparedR.Value.ExplicitSequenceValueItems));
                continue;
            }

            if (maybeAlg is not null)
            {
                inputs.Add(new ParameterPatternInput(Value: null, maybeAlg, preparedR.Error, ExplicitSequenceValueItems: null));
                continue;
            }

            return preparedR.Error;
        }

        return EvalResult<IReadOnlyList<ParameterPatternInput>>.Ok(inputs);
    }

    /// <summary>
    /// Evaluates one non-expanded call argument. Patterned calls need an additional written-slot
    /// view for a capture or a zero-parameter AlgorithmExpr; that view is captured by the
    /// corresponding prepared-output evaluator during the SAME output pass that constructs the
    /// counted argument value. Multi-parameter algorithms stay on the ordinary dual-channel
    /// fallback and are never forced merely to request explicit pattern items.
    /// </summary>
    private static EvalResult<PreparedCallArgumentEvaluation> PrepareCallArgumentEvaluation(
        Expr argExpr,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv,
        bool isDotReceiverSegment,
        bool includeExplicitSequenceValueItems)
    {
        if (includeExplicitSequenceValueItems && argExpr is Expr.Capture(var captureBody))
        {
            // The caller context owns the value evaluation and its
            // explicit-slot view (argument bundles have no scope of their own).
            var captureSpan = argExpr.Span ?? FirstSpan(captureBody);
            var capturePreparedR = WithSpan(captureSpan, EvalCapturePreparedCore(captureBody, ctx, valEnv));
            if (capturePreparedR.IsError) return capturePreparedR.Error;

            var captureCounted = isDotReceiverSegment
                ? capturePreparedR.Value.Counted
                : ReCountValueBoundary(capturePreparedR.Value.Counted);
            return EvalResult<PreparedCallArgumentEvaluation>.Ok(new(
                captureCounted,
                capturePreparedR.Value.OutputSlots));
        }

        if (includeExplicitSequenceValueItems && argExpr is Expr.AlgorithmExpr(var algorithm))
        {
            var wired = WireToCaller(ctx, algorithm);
            if (wired.Params.Count == 0)
            {
                var blockSpan = argExpr.Span ?? FirstSpan(wired.Output);
                var preparedR = WithSpan(blockSpan, EvalAlgOutputPreparedCore(wired, ctx, valEnv));
                if (preparedR.IsError) return preparedR.Error;

                var counted = isDotReceiverSegment
                    ? preparedR.Value.Counted
                    : ReCountValueBoundary(preparedR.Value.Counted);
                return EvalResult<PreparedCallArgumentEvaluation>.Ok(new(
                    counted,
                    preparedR.Value.OutputSlots));
            }
        }

        var evaluatedR = isDotReceiverSegment
            ? EvalDotReceiverCallSegmentCounted(argExpr, ctx, valEnv)
            : EvalCounted(argExpr, ctx, valEnv);
        return evaluatedR.IsError
            ? evaluatedR.Error
            : EvalResult<PreparedCallArgumentEvaluation>.Ok(new(evaluatedR.Value, null));
    }

    private static bool IsInjectedDotCallReceiverSegment(
        IReadOnlyList<bool>? preserveArgBoundaries,
        int index)
        => preserveArgBoundaries is not null
        && index == 0;

    private static EvalResult<CountedResult> EvalDotReceiverCallSegmentCounted(
        Expr receiver,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        // A grouped receiver keeps its multi-item emitted count as the injected
        // leading argument segment (no value-boundary re-count), for both the
        // capture form and a zero-parameter scoped block.
        if (receiver is Expr.Capture(var captureBody))
            return WithSpan(receiver.Span ?? FirstSpan(captureBody), EvalCaptureCountedCore(captureBody, ctx, valEnv));

        if (receiver is Expr.AlgorithmExpr(var algorithm))
        {
            var wired = WireToCaller(ctx, algorithm);
            if (wired.Params.Count == 0)
                return WithSpan(receiver.Span ?? FirstSpan(wired.Output), EvalAlgOutputCounted(wired, ctx, valEnv));
        }

        return EvalCounted(receiver, ctx, valEnv);
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
    /// argument stream: any top-level collecting capture, including a lone
    /// collecting binding <c>*name</c> and mixed fixed/collecting shapes such
    /// as <c>x, *y, z</c>.
    /// Checked only after patterned (sequence-value / repeated-name) binding has
    /// been ruled out.
    /// Lean: <c>Algorithm.usesItemSupplyBinding</c>.
    /// </summary>
    private static bool IsDeconstructionUserCallShape(CallableSignature signature)
        => signature.HasCollectingParameter;

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
    /// Binds a call to an item-supply parameter list (any top-level collecting parameter).
    /// The call argument stream is already the receiver for parameter binding:
    /// a plain sequence-valued argument contributes one item, while explicit
    /// spread contributes the operand's items.
    /// Lean: <c>bindDeconstructionUserCall</c>.
    /// </summary>
    private static EvalResult<UserCallBindings> BindDeconstructionUserCall(
        Algorithm callee,
        OutputBundle args,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv,
        CallDiagnosticName calleeName,
        IReadOnlyList<bool>? preserveArgBoundaries = null)
    {
        var inputsR = BuildCallArgumentInputs(args, ctx, valEnv, preserveArgBoundaries);
        if (inputsR.IsError) return inputsR.Error;

        // A deconstruction parameter list always carries a collecting binding, so a
        // too-few-items failure reports the fixed-binding minimum ("at least N")
        // rather than the exact-count wording used by strict callables.
        return BindParameterPatternList(
            callee.ParameterPatterns,
            inputsR.Value,
            ctx,
            allowAlgorithmBindings: true,
            (required, actual) =>
            {
                var renderedName = calleeName.Render(ctx);
                return VariadicBindingArityMismatch(
                    renderedName,
                    required,
                    actual,
                    CallableSignature.FromAlgorithm(renderedName, callee));
            });
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
        Algorithm callee,
        CallDiagnosticName calleeName,
        IReadOnlyList<string> parameterNames,
        OutputBundle args,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var paramCount = parameterNames.Count;

        // Shared argument-slot assembly (spread expansion happens there, before
        // any arity checking). Dot-call fixed receivers that must stay one
        // boundary are wrapped before this path, so they do not arrive here as
        // Expr.SequenceSpread.
        var inputsR = BuildCallArgumentInputs(args, ctx, valEnv);
        if (inputsR.IsError) return inputsR.Error;

        var slots = inputsR.Value
            .Select(static input => new FlatFixedCallSlot(input.Value, input.Algorithm, input.ValueError))
            .ToList();

        if (slots.Count > paramCount)
            return new EvalError.ArityMismatch(paramCount, slots.Count)
            {
                Signature = CallableSignature.FromAlgorithm(calleeName.Render(ctx), callee),
            };

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
                return arityMismatch with
                {
                    Signature = CallableSignature.FromAlgorithm(calleeName.Render(ctx), callee),
                };

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
    /// <summary>
    /// Lean: <c>resultToExpr</c>. Reify a normalized result as an expression that
    /// evaluates back to the same shape.
    /// </summary>
    private static Expr EmptyResultExpr()
        => new Expr.EmptySequence(0);

    private static Expr ResultToExpr(Result result)
    {
        if (ResultToExprLeaf(result) is { } leaf)
            return leaf;

        // Reified values nest as deep as any runtime value (unbounded — see
        // the depth note on Result), so the rebuild is an iterative post-order
        // walk: each frame fills a fresh array of converted children, and a
        // completed frame hands its expression to the parent frame's open slot.
        var frames = new Stack<ResultToExprFrame>();
        frames.Push(new ResultToExprFrame(result));
        Expr? completed = null;

        while (true)
        {
            var frame = frames.Peek();
            if (completed is not null)
            {
                frame.Converted[frame.Next++] = completed;
                completed = null;
            }

            while (frame.Next < frame.Converted.Length)
            {
                if (ResultToExprLeaf(frame.Source[frame.Next]) is not { } childLeaf)
                    break;
                frame.Converted[frame.Next++] = childLeaf;
            }

            if (frame.Next < frame.Converted.Length)
            {
                frames.Push(new ResultToExprFrame(frame.Source[frame.Next]));
                continue;
            }

            frames.Pop();
            completed = frame.Complete();
            if (frames.Count == 0)
                return completed;
        }
    }

    /// <summary>
    /// Reifies the values <see cref="ResultToExpr"/> does not descend into;
    /// returns null for the two structure shapes that convert child by child.
    /// </summary>
    private static Expr? ResultToExprLeaf(Result result) => result switch
    {
        Result.Atom(var n) => new Expr.Num(n),
        Result.Str(var s) => new Expr.StringLiteral(s),
        // Repeated ordinary parentheses around the empty sequence are redundant
        // surface structure, so any empty-sequence chain reifies as `()`.
        Result.SequenceValue when IsEmptySequenceChain(result)
            => new Expr.EmptySequence(0),
        Result.SequenceValue => null,
        Result.ListValue => null,
        _ => EmptyResultExpr(),
    };

    /// <summary>One in-progress structure rebuild in the <see cref="ResultToExpr"/> walk.</summary>
    private sealed class ResultToExprFrame
    {
        public readonly IReadOnlyList<Result> Source;
        public readonly Expr[] Converted;
        public readonly bool IsSequence;
        public int Next;

        public ResultToExprFrame(Result structure)
        {
            switch (structure)
            {
                case Result.SequenceValue(var items):
                    Source = items;
                    IsSequence = true;
                    break;
                case Result.ListValue(var items):
                    Source = items;
                    IsSequence = false;
                    break;
                default:
                    throw new ArgumentException(
                        "Result reification frames require a sequence or list value.", nameof(structure));
            }

            Converted = new Expr[Source.Count];
        }

        public Expr Complete()
            => IsSequence
                // A reified sequence value is a capture of its already-evaluated
                // items — a value boundary, not an algorithm. Converted is this
                // frame's exclusively owned fresh array, so ownership transfers
                // without a snapshot copy.
                ? new Expr.Capture(OutputBundle.TakeOwnership(Converted))
                // Exact list values reify as list literals so they round-trip
                // losslessly (a reified `()` element stays one visible list
                // element).
                : new Expr.ListLiteral(OutputBundle.TakeOwnership(Converted));
    }

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

    /// <summary>
    /// Counted evaluation result: the normalized value paired with the number of
    /// top-level values emitted at the current algorithm boundary.
    /// Helpers whose names end in <c>Counted</c> preserve this pair instead of
    /// collapsing it to just <see cref="Result"/>.
    /// Lean: <c>CountedResult</c>.
    /// </summary>
    internal readonly record struct CountedResult(Result Value, int EmittedCount);

    /// <summary>
    /// One algorithm-output evaluation prepared for consumers that need both the ordinary
    /// counted value and the evaluated written output slots. <see cref="OutputSlots"/> holds
    /// the same <see cref="Result"/> instances used to construct <see cref="Counted"/>; it is
    /// not a second semantic sequence and never triggers a second evaluation. The backing
    /// storage is owned by the finished evaluation and must never be mutated (the combined
    /// value snapshots its items, so the slot list never aliases into a
    /// <see cref="Result"/>); the hot algorithm-output path deliberately allocates no
    /// per-evaluation read-only wrapper for it. Lean: <c>PreparedAlgorithmOutput</c>.
    /// </summary>
    private readonly record struct PreparedAlgorithmOutput(
        CountedResult Counted,
        IReadOnlyList<Result> OutputSlots);

    private readonly record struct PreparedCallArgumentEvaluation(
        CountedResult Counted,
        IReadOnlyList<Result>? ExplicitSequenceValueItems);

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
        /// <summary>
        /// An algorithm-kind suffix argument. <see cref="PreparedValue"/> carries the
        /// slot's already-computed counted value when call-item assembly evaluated it
        /// eagerly (a value-shaped zero-parameter argument): a value-consuming
        /// position (the reduce initial accumulator) must use THAT result instead of
        /// re-evaluating the algorithm channel — the written slot is evaluated
        /// exactly once. Genuine callbacks have no prepared value.
        /// </summary>
        public sealed record AlgorithmArg(KatLang.Algorithm AlgorithmValue) : PreparedSequenceBuiltinSuffixArg
        {
            public CountedResult? PreparedValue { get; init; }
        }

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
    /// that preserves the same value and emitted top-level count. This rebuild
    /// costs O(value size), so it is performed lazily — only when an
    /// algorithm-only consumer actually requests a prepared argument's
    /// algorithm channel — and each completed construction is recorded on the
    /// run's passive <see cref="EvaluationObservations"/>.
    /// </summary>
    private static Algorithm CountedArgAlgorithm(CountedResult arg, EvalCtx ctx)
    {
        OutputBundle output = arg.EmittedCount switch
        {
            0 => [EmptyResultExpr()],
            1 => [ResultToExpr(arg.Value)],
            // Freshly materialized here, so ownership transfers copy-free.
            _ => OutputBundle.TakeOwnership(arg.Value.ToItems().Select(ResultToExpr).ToArray()),
        };

        var algorithm = new Algorithm.User(
            Parent: null,
            Parameters: [],
            Opens: [],
            Properties: [],
            Output: output);

        // Record the completed wrapper, not merely a request that entered this helper.
        ctx.Observations?.RecordCountedArgumentReification();
        return algorithm;
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
    /// collecting parameter. The callback argument supply keeps the established
    /// flat-callback row convention: when fewer argument slots are supplied
    /// than top-level parameters, the final supplied argument opens into its
    /// items (matching <c>callee(S:i)</c>; exact lists stay opaque), exactly
    /// as <see cref="BindCountedCallbackParams"/> does for fixed-only flat
    /// callees. The resulting slots then bind through the shared
    /// prefix/collecting/suffix binder, so the collecting parameter COLLECTS its allocated
    /// slots as one exact immutable list. Lean:
    /// <c>bindCountedCallbackParameterPatternList</c>.
    /// </summary>
    private static EvalResult<CountedParameterPatternBindings> BindCountedCallbackParameterPatternList(
        IReadOnlyList<ParameterPattern> patterns,
        IReadOnlyList<CountedResult> args,
        EvalCtx ctx)
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
            ctx,
            static (required, actual) => new EvalError.ArityMismatch(required, actual));
    }

    private static EvalResult<CountedParameterPatternBindings> BindCountedParameterPattern(
        ParameterPattern pattern,
        CountedResult input,
        EvalCtx ctx)
    {
        switch (pattern)
        {
            case CaptureParameterPattern { Kind: ParameterKind.Normal } capture:
                return EvalResult<CountedParameterPatternBindings>.Ok(new CountedParameterPatternBindings(
                    [(capture.Name, input)]));

            case CaptureParameterPattern { Kind: ParameterKind.Collecting }:
                return new EvalError.BadArity();

            case SequenceValueParameterPattern group:
                {
                    // A received sequence value or exact list value opens to its
                    // immediate items (Lean: Result.structureItems?); the counted
                    // callback path keeps its stricter singleton-only scalar
                    // fallback (sequence-value-pattern callback deconstruction of
                    // scalar elements stays deferred; flat top-level collecting
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
                        ctx,
                        (required, actual) => SequenceValuePatternArityMismatch(group, required, actual));
                }

            default:
                return new EvalError.BadArity();
        }
    }

    private static EvalResult<CountedParameterPatternBindings> BindCountedParameterPatternList(
        IReadOnlyList<ParameterPattern> patterns,
        IReadOnlyList<CountedResult> inputs,
        EvalCtx ctx,
        Func<int, int, EvalError> arityMismatch)
    {
        var collectingIndex = -1;
        for (var index = 0; index < patterns.Count; index++)
        {
            if (patterns[index] is not CaptureParameterPattern { Kind: ParameterKind.Collecting })
                continue;

            if (collectingIndex >= 0)
                return new EvalError.BadArity();

            collectingIndex = index;
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
            var boundR = BindCountedParameterPattern(patterns[patternIndex], inputs[inputIndex], ctx);
            if (boundR.IsError) return boundR.Error;

            return AddBindings(boundR.Value);
        }

        if (collectingIndex < 0)
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

        for (var index = 0; index < collectingIndex; index++)
        {
            var boundR = BindOne(index, index);
            if (boundR.IsError) return boundR.Error;
        }

        var suffixCount = patterns.Count - collectingIndex - 1;
        var suffixInputStart = inputs.Count - suffixCount;
        for (var suffixIndex = 0; suffixIndex < suffixCount; suffixIndex++)
        {
            var boundR = BindOne(collectingIndex + 1 + suffixIndex, suffixInputStart + suffixIndex);
            if (boundR.IsError) return boundR.Error;
        }

        var collectingCapture = (CaptureParameterPattern)patterns[collectingIndex];
        var capturedValues = inputs
            .Skip(collectingIndex)
            .Take(suffixInputStart - collectingIndex)
            .Select(static input => input.Value)
            .ToList();
        // Collecting binding COLLECTS: the assigned supply becomes one exact
        // immutable list value, emitted count 1 (a list is one visible value).
        var capturedResultR = CollectSegment(ctx, capturedValues, collectingCapture.Span);
        if (capturedResultR.IsError) return capturedResultR.Error;
        var capturedResult = capturedResultR.Value;
        var captured = new CountedResult(capturedResult, 1);
        var captureBindingsR = AddBindings(new CountedParameterPatternBindings(
            [(collectingCapture.Name, captured)]));
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
        // Charged dynamic invocation boundary. This is the single callback dispatch
        // chokepoint: the plain wrapper, the sequence-callback wrappers, and the
        // conditional-callback path all route through here, so a callback invocation is
        // charged exactly once regardless of callee shape.
        if (ctx.Budget.TryEnterInvocation() is { } limitError)
            return limitError;

        try
        {
            return EvalResolvedCallbackCallCountedCore(callee, args, ctx, valEnv, calleeName);
        }
        finally
        {
            ctx.Budget.ExitInvocation();
        }
    }

    private static EvalResult<CountedResult> EvalResolvedCallbackCallCountedCore(
        Algorithm callee,
        IReadOnlyList<CountedResult> args,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv,
        string calleeName)
    {
        switch (callee)
        {
            case Algorithm.Builtin(var builtin):
                return ApplyBuiltinCountedResolved(
                    builtin,
                    args.Select(static arg => new ResolvedArgumentAlgorithm(
                        Algorithm: null,
                        SpreadsSequence: false)
                    {
                        PreparedValue = arg,
                    }).ToList(),
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
                            ctx,
                            (required, actual) => new EvalError.ArityMismatch(required, actual));
                        if (countedPatternEnvR.IsError) return countedPatternEnvR.Error;

                        var patternBindings = countedPatternEnvR.Value;
                        var patternCtx = WithCountedParameterEnvironments(
                            ctx,
                            patternBindings.CountedBindings,
                            patternBindings.CountedBindings.Select(static binding => binding.Item1));
                        return EvalAlgOutputCounted(callee, patternCtx, valEnv);
                    }

                    // A flat callee with a top-level collecting parameter (`Rows.map(F)`
                    // with `F(x, *y, z)` or a single-collecting `Collect(*items)`)
                    // binds through the shared prefix/collecting/suffix binder so the
                    // collecting parameter COLLECTS an exact immutable list, after the
                    // same final-argument row expansion the fixed-only flat path
                    // uses below. Single-collecting callees keep the whole iterated
                    // element as one collected slot.
                    if (ParameterPattern.HasCollectingCaptureAtCurrentLevel(callee.ParameterPatterns))
                    {
                        var collectingPatternEnvR = BindCountedCallbackParameterPatternList(callee.ParameterPatterns, args, ctx);
                        if (collectingPatternEnvR.IsError) return collectingPatternEnvR.Error;

                        var collectingBindings = collectingPatternEnvR.Value;
                        var collectingCtx = WithCountedParameterEnvironments(
                            ctx,
                            collectingBindings.CountedBindings,
                            collectingBindings.CountedBindings.Select(static binding => binding.Item1));
                        return EvalAlgOutputCounted(callee, collectingCtx, valEnv);
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
    private static EvalResult<PreparedAlgorithmOutput> EvalAlgOutputPreparedCore(
        Algorithm alg,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        if (alg is Algorithm.Builtin(var builtin))
        {
            var countedR = EvalBuiltinValueCounted(builtin);
            return countedR.IsError
                ? countedR.Error
                : EvalResult<PreparedAlgorithmOutput>.Ok(new(
                    countedR.Value,
                    CountedTopLevelValues(countedR.Value)));
        }

        var dupProp = alg.FindDuplicatePropName();
        if (dupProp is not null)
            return new EvalError.DuplicateProperty(dupProp);

        if (ConditionalValueAccessError("conditional", alg) is { } conditionalError)
            return conditionalError;

        if (alg is Algorithm.User { Output: { Count: 0 } })
            return new EvalError.MissingOutput();

        return EvalOutputRowsPreparedCore(alg.Output, ctx.Push(alg), ctx, valEnv);
    }

    /// <summary>
    /// The ONE shared output-row supply loop: evaluates ordered
    /// <see cref="OutputBundle"/> rows left to right (a spread row contributes
    /// its supplied items, a non-spread row contributes exactly one slot) and
    /// combines the collected slots into one canonical value
    /// (<see cref="CombineOutputSlots"/>). Algorithm output evaluation reaches
    /// it after pushing the algorithm's own scope; <see cref="Expr.Capture"/>
    /// evaluation reaches it directly with the surrounding context, because a
    /// capture owns no scope. Both receivers therefore share exactly the same
    /// supply semantics rather than duplicating them.
    /// </summary>
    private static EvalResult<PreparedAlgorithmOutput> EvalOutputRowsPreparedCore(
        IReadOnlyList<Expr> rows,
        EvalCtx rowCtx,
        EvalCtx reserveCtx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var results = new List<Result>();
        var emittedCount = 0;

        foreach (var expr in rows)
        {
            var countedR = EvalCounted(expr, rowCtx, valEnv);
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

        // Output-slot capture is a persistent collection: spread can expand it well beyond
        // any single input (`(A*, A*)` doubles), so the reservation happens
        // here, before the sequence value is built.
        if (ReserveSequenceCapture(reserveCtx, results.Count, FirstSpan(rows)) is { } capturedLimitError)
            return capturedLimitError;

        var counted = new CountedResult(CombineOutputSlots(results), emittedCount);
        return EvalResult<PreparedAlgorithmOutput>.Ok(new(counted, results));
    }

    /// <summary>
    /// Evaluates a <see cref="Expr.Capture"/> body's rows in the surrounding
    /// context (a capture owns no scope, so nothing is pushed) through the
    /// shared output-row supply loop. The multi-item emitted count is
    /// preserved here; value-position consumers re-count at the capture's
    /// value boundary (<see cref="Result.ValueCount"/>). An empty bundle
    /// captures the empty sequence value.
    /// Lean: <c>evalCapturePreparedCore</c>.
    /// </summary>
    private static EvalResult<PreparedAlgorithmOutput> EvalCapturePreparedCore(
        OutputBundle body,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
        => EvalOutputRowsPreparedCore(body, ctx, ctx, valEnv);

    private static EvalResult<CountedResult> EvalCaptureCountedCore(
        OutputBundle body,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var preparedR = EvalCapturePreparedCore(body, ctx, valEnv);
        return preparedR.IsError
            ? preparedR.Error
            : EvalResult<CountedResult>.Ok(preparedR.Value.Counted);
    }

    /// <summary>
    /// Evaluates a capture body to its single canonical captured value.
    /// </summary>
    private static EvalResult<Result> EvalCaptureValue(
        OutputBundle body,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var countedR = EvalCaptureCountedCore(body, ctx, valEnv);
        return countedR.IsError
            ? countedR.Error
            : EvalResult<Result>.Ok(countedR.Value.Value);
    }

    /// <summary>
    /// The algorithm-channel adapter for a capture: a fresh zero-parameter
    /// output-only thunk over the bundle, wired to the caller scope. CAPTURE IS
    /// NOT ALGORITHM IDENTITY — this never exposes the algorithm identity of
    /// any expression inside the bundle (a captured named algorithm stays
    /// suppressed, exactly like the pre-split transparent wrapper); it only
    /// lets algorithm-channel consumers evaluate the capture's value lazily.
    /// Lean: <c>captureValueThunk</c>.
    /// </summary>
    private static Algorithm CaptureValueThunk(OutputBundle body, EvalCtx ctx)
        => WireToCaller(
            ctx,
            new Algorithm.User(
                Parent: null,
                Parameters: [],
                Opens: [],
                Properties: [],
                Output: body));

    private static EvalResult<CountedResult> EvalAlgOutputCountedCore(
        Algorithm alg,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var preparedR = EvalAlgOutputPreparedCore(alg, ctx, valEnv);
        return preparedR.IsError
            ? preparedR.Error
            : EvalResult<CountedResult>.Ok(preparedR.Value.Counted);
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

    // ── Collection materialization budget ────────────────────────────────────

    /// <summary>
    /// RESERVES <paramref name="itemCount"/> item slots for a persistent collection that
    /// is about to be created. Every caller must reserve BEFORE allocating: a rejected
    /// request must never materialize the collection it is rejecting.
    /// </summary>
    private static EvalError? ReserveCollection(EvalCtx ctx, long itemCount, SourceSpan? span = null)
        => ctx.Budget.TryReserveCollection(itemCount) is { } error
            ? AtSpanIfMissing(error, span)
            : null;

    /// <summary>
    /// Charged form of <see cref="MakeCollectionListResult(IEnumerable{Result})"/>: the
    /// item count is already known, so the reservation happens before the exact list is
    /// built. Collection-producing builtins charge their TRUE output count here rather
    /// than an upper bound, so a cumulative budget is never over-charged.
    /// </summary>
    /// <summary>
    /// Sequence CAPTURE reserves only when a sequence value is actually created: ordinary
    /// construction erases singleton and empty structure (`(x)` is `x`, `()` stores no item
    /// slots), so fewer than two slots materialize no collection and cost nothing. Exact
    /// lists are different — `[x]` really does store one slot — and use
    /// <see cref="ReserveCollection"/> directly.
    /// </summary>
    private static EvalError? ReserveSequenceCapture(EvalCtx ctx, int slotCount, SourceSpan? span = null)
        => slotCount >= 2 ? ReserveCollection(ctx, slotCount, span) : null;

    /// <summary>
    /// Canonically captures an item supply after reserving only the slots that the
    /// resulting persistent sequence actually stores. Empty capture stores no item
    /// slots, singleton capture returns the existing child value, and two or more
    /// items create and charge one sequence value.
    /// </summary>
    private static EvalResult<Result> MakeCheckedSequenceCapture(
        EvalCtx ctx,
        IReadOnlyList<Result> items,
        SourceSpan? span = null)
        => ReserveSequenceCapture(ctx, items.Count, span) is { } error
            ? error
            : EvalResult<Result>.Ok(CombineOutputSlots(items));

    internal static EvalResult<CountedResult> MakeCheckedLoopStateResult(
        EvalCtx ctx,
        IReadOnlyList<Result> stateSlots,
        SourceSpan? span = null)
    {
        var valueR = MakeCheckedSequenceCapture(ctx, stateSlots, span);
        return valueR.IsError
            ? valueR.Error
            : EvalResult<CountedResult>.Ok(new CountedResult(valueR.Value, stateSlots.Count));
    }

    private static EvalResult<CountedResult> MakeCollectionListResult(
        EvalCtx ctx,
        IReadOnlyList<Result> items,
        SourceSpan? span = null)
        => ReserveCollection(ctx, items.Count, span) is { } error
            ? error
            : EvalResult<CountedResult>.Ok(MakeCollectionListResult(items));

    /// <summary>
    /// <c>atoms</c> result construction. Unlike every other collection builtin its output
    /// is not bounded by its input's item count, so the traversal itself is bounded and
    /// abandoned as soon as it passes the limit — no oversized intermediate is ever built,
    /// and no unbounded counting prepass is needed.
    /// </summary>
    private static EvalResult<CountedResult> MakeLanguageAtomsResult(
        EvalCtx ctx,
        Result value,
        SourceSpan? span = null)
    {
        var limit = ctx.Budget.MaxCollectionItems;
        if (!value.TryLanguageAtoms(limit, out var atoms))
            return AtSpanIfMissing(new EvalError.CollectionSizeLimitExceeded(limit, limit + 1L), span);

        return MakeCollectionListResult(ctx, atoms.Select(static n => (Result)new Result.Atom(n)).ToList(), span);
    }

    /// <summary>
    /// <c>range(start, stop)</c> result construction. The cardinality is computed from the
    /// bounds WITHOUT enumerating, so an oversized request is rejected before a single item
    /// is allocated — this is the path that made <c>range(1, 10000000)</c> a process risk.
    /// </summary>
    private static EvalResult<Result> BuildInclusiveRangeChecked(
        EvalCtx ctx,
        InclusiveRange range,
        SourceSpan? span = null)
        => ReserveCollection(ctx, CountInclusiveRangeValues(range), span) is { } error
            ? error
            : EvalResult<Result>.Ok(BuildInclusiveRange(range));

    // Re-count a counted result at a public property/call/builtin RESULT boundary.
    // A property/call boundary always returns ONE value: the body may internally
    // produce an item supply of count 0, 1, or many, but the caller observes the
    // same structural value with emitted count <see cref="Result.ValueCount"/>
    // (0 for the empty sequence value, otherwise 1). A multi-output body therefore
    // becomes one sequence value at the boundary; only an explicit caller-site
    // `spread` re-spreads it (via ToItems, which reads the value, not this count).
    //
    // This re-counts without normalizing or rebuilding the value; ordinary value
    // construction has already canonicalized redundant unary empty structure.
    // It is applied only to public result boundaries, never to internal
    // body/root output accumulation (EvalAlgOutputCountedCore) or to multi-slot
    // while/repeat loop state, both of which must keep their multi-item counts.
    // (Collecting bindings need no re-count: CollectSegment stores one exact list with
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
        // Charged dynamic invocation boundary, entered BEFORE the cache is consulted so
        // that recursive property access (`A = A`) is bounded by depth. A cache HIT
        // charges exactly this one access step and never re-charges the cached
        // computation; a MISS additionally charges everything its body evaluates.
        if (ctx.Budget.TryEnterInvocation() is { } limitError)
            return AtSpanIfMissing(limitError, binding.DeclarationSpans.FirstOrDefault());

        try
        {
            return GetOrEvaluateZeroArgPropertyResultCore(owner, binding, accessKind, resolvedAlgorithm, ctx, valEnv);
        }
        finally
        {
            ctx.Budget.ExitInvocation();
        }
    }

    private static EvalResult<ZeroArgPropertyResult> GetOrEvaluateZeroArgPropertyResultCore(
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
                ctx.CountedParamEnv,
                // The budget is created fresh per run (CreateRootCtx) and threaded by
                // reference through every derived ctx, so it is the run identity:
                // entries can never be served across runs even when a host shares
                // one cache instance between runs.
                ctx.Budget),
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

    private static bool ReducerAccumulatorSideHasTopLevelCollecting(Algorithm.User reducer)
    {
        try
        {
            var signature = CallableSignature.FromUserAlgorithm("reduce step", reducer);
            var plan = CallableBindingPlan.FromSignature(signature);
            return plan.TopLevelPatternList.Nodes
                .Skip(1)
                .Any(static node => node is CollectingCaptureBindingNode { IsTopLevel: true });
        }
        catch (InvalidOperationException)
        {
            return false;
        }
    }

    private static EvalResult<CountedResult> EvalReducerAccumulatorCollectingCallbackCallCounted(
        Algorithm.User callee,
        IReadOnlyList<CountedResult> args,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        // Charged dynamic invocation boundary. This reducer shape is dispatched INSTEAD
        // of EvalResolvedCallbackCallCounted, never in addition to it, so charging here
        // keeps one reduce step at exactly one charged invocation.
        if (ctx.Budget.TryEnterInvocation() is { } limitError)
            return limitError;

        try
        {
            return EvalReducerAccumulatorCollectingCallbackCallCountedCore(callee, args, ctx, valEnv);
        }
        finally
        {
            ctx.Budget.ExitInvocation();
        }
    }

    private static EvalResult<CountedResult> EvalReducerAccumulatorCollectingCallbackCallCountedCore(
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
            ctx,
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
    /// with a top-level collecting accumulator parameter bind accumulator state
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
        if (callee is Algorithm.User userReducer && ReducerAccumulatorSideHasTopLevelCollecting(userReducer))
        {
            var accumulatorSlots = accumulator.ToItems();
            var args = new List<CountedResult>(1 + accumulatorSlots.Count) { elementArg };
            foreach (var slot in accumulatorSlots)
                args.Add(new CountedResult(slot, slot.ValueCount()));

            return EvalReducerAccumulatorCollectingCallbackCallCounted(userReducer, args, ctx, valEnv);
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
    /// <see cref="Expr.Capture"/> and always keep a non-spread <c>()</c> item
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

        if (ReserveSequenceCapture(ctx, items.Count) is { } sequenceLimitError)
            return sequenceLimitError;

        var value = CombineOutputSlots(items);
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

    private static EvalResult<IReadOnlyList<Result>> EvalSequenceSpreadOperandItems(
        Expr expr,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        if (expr is Expr.Capture(var captureBody))
        {
            var captureSpan = expr.Span ?? FirstSpan(captureBody);
            var captureR = WithSpan(captureSpan, EvalCaptureValue(captureBody, ctx, valEnv));
            if (captureR.IsError)
                return IsMissingOutputError(captureR.Error)
                    ? SpreadMissingOutput(captureSpan)
                    : captureR.Error;

            return EvalResult<IReadOnlyList<Result>>.Ok(captureR.Value.SpreadItems());
        }

        if (expr is Expr.AlgorithmExpr(var alg))
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
    // (`A**`) are unwrapped iteratively (stack-safe for deep nesting) and
    // then each written layer is applied COMPOSITIONALLY: every spread layer
    // opens exactly one boundary of the value the previous layer would have
    // captured, so `A**` agrees with `(A*)*`. For sequence values the extra
    // layers are fixed points (value-equivalent to a single spread); a
    // singleton-list chain opens one list boundary per layer (`[[7]]**`
    // supplies `7`), while a multi-element list re-captures as a sequence
    // after the first layer and then stays fixed (`[[1, 2], [3, 4]]**`
    // supplies the two inner lists unchanged).
    // Lean: evalSequenceSpreadCounted.
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
        for (var layer = 0; layer < layers; layer++)
        {
            var capturedR = MakeCheckedSequenceCapture(ctx, items, expr.Span);
            if (capturedR.IsError) return capturedR.Error;

            if (layer == layers - 1)
                return EvalResult<CountedResult>.Ok(new CountedResult(capturedR.Value, items.Count));

            items = capturedR.Value.SpreadItems();
        }

        throw new InvalidOperationException("Sequence spread must contain at least one layer.");
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
            if (arg is not null && (arg.Params.Count > 0 || arg.ParameterPatterns.Count > 0))
            {
                items.Add(new VariadicCallItem(
                    Value: null,
                    arg,
                    ValueError: null,
                    resolvedArg.PreparedValue));
                continue;
            }

            // A prepared argument (a dotted receiver or builtin callback value) already
            // holds its counted value and must not be recomputed: re-evaluating the reified
            // value would repeat every allocation and charged unit the first evaluation paid.
            var outputR = resolvedArg.PreparedValue is { } prepared
                ? EvalResult<CountedResult>.Ok(prepared)
                : arg is { } algorithm
                    ? EvalArgumentAlgOutputCounted(algorithm, ctx, valEnv)
                    : EvalResult<CountedResult>.Err(new EvalError.BadArity());
            if (outputR.IsOk)
            {
                if (resolvedArg.SpreadsSequence)
                {
                    foreach (var value in CountedTopLevelValues(outputR.Value))
                    {
                        items.Add(new VariadicCallItem(
                            value,
                            arg,
                            ValueError: null,
                            new CountedResult(value, 1)));
                    }
                }
                else
                {
                    items.Add(new VariadicCallItem(
                        outputR.Value.Value,
                        arg,
                        ValueError: null,
                        outputR.Value));
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
                {
                    // A resource-limit failure from the slot's eager value evaluation is
                    // STICKY: the limit is a property of the run, and falling through to
                    // the algorithm channel would re-run the same body — each active
                    // level retrying once turns a failing self-referential argument
                    // (`A = xs.reduce(F, A)`) into work exponential in the depth limit.
                    // Non-limit value errors keep the legacy fall-through, which is what
                    // lets a genuine callback reference reach the algorithm channel.
                    if (item.ValueError is { IsResourceLimit: true } stickyLimit)
                        return stickyLimit;

                    var algorithm = item.Algorithm
                        ?? (item.PreparedValue is { } prepared
                            ? CountedArgAlgorithm(prepared, ctx)
                            : null);
                    if (algorithm is not null)
                    {
                        return EvalResult<PreparedSequenceBuiltinSuffixArg>.Ok(
                            new PreparedSequenceBuiltinSuffixArg.AlgorithmArg(
                                NormalizeSequenceCallableSuffixAlgorithm(algorithm, ctx))
                            {
                                PreparedValue = item.PreparedValue,
                            });
                    }

                    return item.ValueError ?? new EvalError.WithContext(
                        SequenceBuiltinSuffixArgErrorContext(builtin, descriptor),
                        new EvalError.BadArity());
                }

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
        Result.Atom(var n) => $"numeric value {n.ToString(System.Globalization.CultureInfo.InvariantCulture)}",
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
    /// top-level collecting accumulator parameter receives accumulator state
    /// slots.
    /// Lean: <c>evalReduceCounted</c>.
    /// </summary>
    private static EvalResult<CountedResult> EvalReduceCounted(
        IReadOnlyList<CountedResult> items,
        Algorithm stepAlg,
        Algorithm initialAlg,
        CountedResult? preparedInitial,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        // The initial accumulator is a written value slot: when call-item assembly
        // already evaluated it (a value-shaped argument), that result IS the slot's
        // value — evaluating the algorithm channel again would run the body twice.
        var initialR = preparedInitial is { } preparedValue
            ? EvalResult<CountedResult>.Ok(preparedValue)
            : EvalArgumentAlgOutputCounted(initialAlg, ctx, valEnv);
        if (initialR.IsError)
        {
            if (IsLikelyUnevaluatedParameterError(initialAlg, initialR.Error))
                return ReduceInitialAccumulatorRequiresValueError(initialAlg);

            return initialR.Error;
        }

        // The initial accumulator expression occupies ONE written accumulator
        // slot: its result is reified as one persistent value at the ordinary
        // value boundary (ReCountValueBoundary) BEFORE reduction begins, so an
        // initial expression that emitted multiple items cannot leak that
        // supply through the empty-collection return.
        var accumulator = ReCountValueBoundary(initialR.Value);
        foreach (var item in items)
        {
            var stepR = WithCtx(
                "while evaluating reduce step (reduce passes each iterated collection item as collected; a collecting parameter collects supplied values as one exact list, nested sequence and list values stay intact, and top-level collecting accumulator parameters receive state slots)",
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

        return MakeCollectionListResult(ctx, kept);
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
            $"while evaluating filter predicate for item {index}: {FormatResultForDiagnostic(item.Value)} (filter passes each iterated collection item as collected; a collecting parameter collects supplied values as one exact list and nested sequence and list values stay intact)",
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
                "while evaluating map transform (map passes each iterated collection item as collected; a collecting parameter collects supplied values as one exact list and nested sequence and list values stay intact)",
                EvalSequenceCallbackCallCounted(transformAlg, item, ctx, valEnv, "map transform"));
            if (transformR.IsError) return transformR.Error;

            var mappedElementR = ExpectSingleMappedElement(transformR.Value);
            if (mappedElementR.IsError) return mappedElementR.Error;

            mapped.Add(mappedElementR.Value);
        }

        return MakeCollectionListResult(ctx, mapped);
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
        // boundaries, and the spread items obey the same fixed arity
        // (`count([1, 2, 3]*)` supplies three arguments and is an arity
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
    {
        var argR = ExpectPreparedAlgorithmSuffixArgFull(builtin, descriptors, args, index);
        return argR.IsError
            ? argR.Error
            : EvalResult<Algorithm>.Ok(argR.Value.AlgorithmValue);
    }

    private static EvalResult<PreparedSequenceBuiltinSuffixArg.AlgorithmArg> ExpectPreparedAlgorithmSuffixArgFull(
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
            (descriptor, arg) => arg is PreparedSequenceBuiltinSuffixArg.AlgorithmArg algorithmArg
                ? EvalResult<PreparedSequenceBuiltinSuffixArg.AlgorithmArg>.Ok(algorithmArg)
                : InternalSequenceBuiltinSuffixArgMetadataError<PreparedSequenceBuiltinSuffixArg.AlgorithmArg>(
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
        EvalCtx ctx,
        IReadOnlyList<decimal> numbers)
    {
        var sorted = numbers.ToList();
        sorted.Sort();
        return MakeCollectionListResult(ctx, sorted.Select(static value => (Result)new Result.Atom(value)).ToList());
    }

    /// <summary>
    /// Evaluate <c>orderDesc(collection)</c> by eagerly sorting the top-level
    /// numeric collection items in descending order and materializing them as
    /// one exact immutable list value.
    /// Duplicates are preserved, sequence values are not flattened, strings are
    /// rejected, and empty collections yield the empty list <c>[]</c>.
    /// </summary>
    private static EvalResult<CountedResult> EvalOrderDescCounted(
        EvalCtx ctx,
        IReadOnlyList<decimal> numbers)
    {
        var sorted = numbers.ToList();
        sorted.Sort(static (left, right) => right.CompareTo(left));
        return MakeCollectionListResult(ctx, sorted.Select(static value => (Result)new Result.Atom(value)).ToList());
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
        EvalCtx ctx,
        IReadOnlyList<Result> items)
    {
        var distinctItems = new List<Result>(items.Count);
        var seen = new HashSet<Result>(Result.ValueComparer);
        foreach (var item in items)
        {
            if (seen.Add(item))
                distinctItems.Add(item);
        }

        return MakeCollectionListResult(ctx, distinctItems);
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
        EvalCtx ctx,
        IReadOnlyList<Result> items,
        decimal count)
    {
        // Saturate before narrowing: `count` is a validated whole decimal that may
        // exceed int.MaxValue, and an oversized count means "all items" by
        // specification, so it must never reach the host (int) conversion.
        IReadOnlyList<Result> taken = count <= 0
            ? []
            : items.Take(count >= items.Count ? items.Count : (int)count).ToList();

        return MakeCollectionListResult(ctx, taken);
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
        EvalCtx ctx,
        IReadOnlyList<Result> items,
        decimal count)
    {
        // Saturate before narrowing, mirroring EvalTakeCounted: an oversized count
        // means "skip everything" and must never reach the host (int) conversion.
        IReadOnlyList<Result> remaining = count <= 0
            ? items.ToList()
            : items.Skip(count >= items.Count ? items.Count : (int)count).ToList();

        return MakeCollectionListResult(ctx, remaining);
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
            BuiltinId.@order => WithPreparedNumericItems(numbers => EvalOrderCounted(ctx, numbers)),
            BuiltinId.@orderDesc => WithPreparedNumericItems(numbers => EvalOrderDescCounted(ctx, numbers)),
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
            BuiltinId.@distinct => WithPreparedFlatItems(items => EvalDistinctCounted(ctx, items)),
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

                        return WithPreparedFlatItems(items => EvalTakeCounted(ctx, items, countR.Value));
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

                        return WithPreparedFlatItems(items => EvalSkipCounted(ctx, items, countR.Value));
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

                        var initialR = ExpectPreparedAlgorithmSuffixArgFull(
                            builtin,
                            metadata.SuffixArgs,
                            preparedSuffixArgs,
                            1);
                        if (initialR.IsError) return initialR.Error;

                        return EvalReduceCounted(
                            bound.IterationItems,
                            stepR.Value,
                            initialR.Value.AlgorithmValue,
                            initialR.Value.PreparedValue,
                            ctx,
                            valEnv);
                    }),
            _ => WrongBuiltinArity(builtin, args.Count),
        };
    }

    /// <summary>
    /// Evaluate a builtin argument's algorithm body through the depth-charged
    /// chokepoint (<see cref="EvaluationBudget.TryEnterArgumentEvaluation"/>).
    /// Builtin argument evaluation re-enters an algorithm body exactly like a call
    /// does, so it must consume depth: without the charge, a zero-parameter
    /// property that reaches itself through a builtin argument (<c>A = count(A)</c>,
    /// <c>A = if(1, A, 0)</c>, <c>A = range(1, A)</c>, a loop's initial state or
    /// count) recurses outside every budget chokepoint and terminates the process
    /// with an uncatchable <see cref="StackOverflowException"/>. It charges no STEP,
    /// preserving the frozen step accounting (steps count dynamic invocations and
    /// loop iterations only) and the plain/dot work-parity pins.
    /// </summary>
    private static EvalResult<CountedResult> EvalArgumentAlgOutputCounted(
        Algorithm algorithm,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        if (ctx.Budget.TryEnterArgumentEvaluation() is { } limitError)
            return limitError;
        try
        {
            return EvalAlgOutputCounted(algorithm, ctx, valEnv);
        }
        finally
        {
            ctx.Budget.ExitInvocation();
        }
    }

    private static EvalResult<CountedResult> EvalResolvedArgumentCounted(
        ResolvedArgumentAlgorithm arg,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
        => arg.PreparedValue is { } prepared
            ? EvalResult<CountedResult>.Ok(prepared)
            : arg.Algorithm is { } algorithm
                ? EvalArgumentAlgOutputCounted(algorithm, ctx, valEnv)
                : new EvalError.BadArity();

    /// <summary>
    /// Returns the argument's algorithm channel. Already evaluated callback data and dotted
    /// sequence-builtin receivers normally never need one; if an algorithm-only builtin
    /// position does request it, build the legacy counted-value wrapper at that point rather
    /// than for every prepared argument.
    /// </summary>
    private static EvalResult<Algorithm> ResolveArgumentAlgorithm(ResolvedArgumentAlgorithm arg, EvalCtx ctx)
        => arg.Algorithm is { } algorithm
            ? EvalResult<Algorithm>.Ok(algorithm)
            : arg.PreparedValue is { } prepared
                ? EvalResult<Algorithm>.Ok(CountedArgAlgorithm(prepared, ctx))
                : new EvalError.BadArity();

    private static EvalResult<Result> EvalResolvedArgument(
        ResolvedArgumentAlgorithm arg,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var countedR = EvalResolvedArgumentCounted(arg, ctx, valEnv);
        return countedR.IsError
            ? countedR.Error
            : EvalResult<Result>.Ok(countedR.Value.Value);
    }

    private static EvalResult<IReadOnlyList<ResolvedArgumentAlgorithm>> ExpandSequenceSpreadBuiltinArguments(
        IReadOnlyList<ResolvedArgumentAlgorithm> args,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var expanded = new List<ResolvedArgumentAlgorithm>(args.Count);
        foreach (var arg in args)
        {
            if (!arg.SpreadsSequence)
            {
                expanded.Add(arg);
                continue;
            }

            var outputR = EvalResolvedArgumentCounted(arg, ctx, valEnv);
            if (outputR.IsError) return outputR.Error;

            foreach (var value in CountedTopLevelValues(outputR.Value))
            {
                var prepared = new CountedResult(value, 1);
                expanded.Add(new ResolvedArgumentAlgorithm(
                    Algorithm: null,
                    SpreadsSequence: false)
                {
                    PreparedValue = prepared,
                });
            }
        }

        return EvalResult<IReadOnlyList<ResolvedArgumentAlgorithm>>.Ok(expanded);
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
                    var condR = EvalResolvedArgument(args[0], ctx, valEnv);
                    if (condR.IsError) return condR.Error;
                    var truth = condR.Value.TruthValue();
                    if (truth is null) return new EvalError.BadArity();

                    // The selected branch is one argument expression, so `if` observes
                    // it as a single value boundary — exactly like value-position
                    // property access. A multi-output branch property such as
                    // `X = 1, 2, 3` therefore yields the grouped sequence value
                    // `(1, 2, 3)` with emitted count 1, not three separate outputs.
                    // Explicit spread (`if(1, X, X)*`) is the way to open it.
                    // Unlike `while`/`repeat`, which intentionally preserve multi-slot
                    // loop state, `if` re-counts the chosen branch value here.
                    var branchR = truth.Value
                        ? EvalResolvedArgumentCounted(args[1], ctx, valEnv)
                        : EvalResolvedArgumentCounted(args[2], ctx, valEnv);
                    if (branchR.IsError) return branchR.Error;
                    return EvalResult<CountedResult>.Ok(
                        new CountedResult(branchR.Value.Value, branchR.Value.Value.ValueCount()));
                }

            case (BuiltinId.@while, _) when args.Count >= 2:
                {
                    var stepR = ResolveArgumentAlgorithm(args[0], ctx);
                    if (stepR.IsError) return stepR.Error;
                    var initialStateR = EvalInitialLoopStateSlots(args.Skip(1).ToList(), ctx, valEnv);
                    if (initialStateR.IsError) return initialStateR.Error;
                    return WhileLoopCounted(stepR.Value, initialStateR.Value, ctx, valEnv);
                }

            case (BuiltinId.@repeat, _) when args.Count >= 3:
                {
                    var stepR = ResolveArgumentAlgorithm(args[0], ctx);
                    if (stepR.IsError) return stepR.Error;
                    var countR = EvalResolvedArgument(args[1], ctx, valEnv);
                    if (countR.IsError) return countR.Error;
                    var nR = ExpectWholeInt(countR.Value, "Repeat count");
                    if (nR.IsError) return nR.Error;
                    // Domain check BEFORE narrowing: the validated whole decimal may lie
                    // outside long's range in either direction, so the (long) conversion
                    // is only safe after rejecting negatives and saturating oversized
                    // counts (behaviorally identical: both exceed any finite budget).
                    if (nR.Value < 0) return new EvalError.IllegalInEval("Repeat count must be >= 0");
                    var n = nR.Value >= long.MaxValue ? long.MaxValue : (long)nR.Value;

                    var initialStateR = EvalInitialLoopStateSlots(args.Skip(2).ToList(), ctx, valEnv);
                    if (initialStateR.IsError) return initialStateR.Error;
                    return RepeatLoopCounted(stepR.Value, n, initialStateR.Value, ctx, valEnv);
                }

            case (BuiltinId.@atoms, 1):
                {
                    var atomsR = EvalResolvedArgument(args[0], ctx, valEnv);
                    if (atomsR.IsError) return atomsR.Error;
                    // `atoms` materializes a collection: one exact immutable list
                    // of the recursively collected numeric atoms (sequence AND
                    // list boundaries open; truth testing stays list-opaque).
                    return MakeLanguageAtomsResult(ctx, atomsR.Value);
                }

            case (BuiltinId.@range, 2):
                {
                    var rangeR = EvalBuiltinRangeArguments(args, ctx, valEnv);
                    if (rangeR.IsError) return rangeR.Error;

                    // A list value is always one visible value, including `[]`.
                    var rangeValueR = BuildInclusiveRangeChecked(ctx, rangeR.Value);
                    return rangeValueR.IsError
                        ? rangeValueR.Error
                        : EvalResult<CountedResult>.Ok(new CountedResult(rangeValueR.Value, 1));
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
    private static EvalResult<Result> ResultToString(EvalCtx ctx, Result r)
    {
        if (r is Result.Atom(var n))
            return MakeStringResult(ctx, n.ToString(System.Globalization.CultureInfo.InvariantCulture));
        return new EvalError.TypeMismatch("builtin property `string` expects a numeric receiver");
    }

    /// <summary>
    /// The single construction point for language string values created by source
    /// evaluation. Every producer routes through here so the length ceiling and the
    /// cumulative string budget cannot be forgotten at a scattered site, and so a
    /// future concatenating operation inherits both automatically.
    ///
    /// <para>The reservation happens BEFORE the value is created. In practice a source
    /// program cannot approach the ceiling — KatLang has no concatenation operator, so
    /// strings only come from source literals and roughly 30-unit numeric conversions —
    /// but a hand-built AST passed to the public evaluator API can, and that is the path
    /// this closes.</para>
    /// </summary>
    internal static EvalResult<Result> MakeStringResult(EvalCtx ctx, string text, SourceSpan? span = null)
        => ctx.Budget.TryReserveString(text.Length) is { } limitError
            ? AtSpanIfMissing(limitError, span)
            : EvalResult<Result>.Ok(new Result.Str(text));

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

            case Expr.AlgorithmExpr(var alg):
                return EvalResult<Algorithm>.Ok(WireOpenBlockToGlobalScope(alg, ctx));

            case Expr.Capture:
                // A capture is a value boundary, never algorithm/namespace
                // identity: `open` consumes algorithm identity, so a captured
                // target such as `open (M)` is not openable. The parser
                // rejects this form in source; this arm is the prebuilt-AST
                // defense, mirroring the spread arm above.
                return new EvalError.BadOpenForm("captured value groups cannot be opened") { Span = expr.Span };

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
                    // Lean: notAnAlgorithm "sequence construct expression" — the
                    // description is structured payload and must match exactly.
                    return new EvalError.NotAnAlgorithm("sequence construct expression") { Span = expr.Span };
                }

            case Expr.SequenceSpread(var operand):
                {
                    _ = operand;
                    return new EvalError.NotAnAlgorithm("spread expression") { Span = expr.Span };
                }

            case Expr.AlgorithmExpr(var alg):
                return EvalResult<Algorithm>.Ok(WireToCaller(ctx, alg));

            case Expr.Capture(var captureBody):
                // Capture is not algorithm identity: the algorithm channel sees
                // only a zero-parameter value thunk over the bundle, exactly as
                // the pre-split transparent wrapper behaved. `(F)(1)` therefore
                // stays an arity error and `Apply((Increment))` never receives
                // Increment's callable identity.
                return EvalResult<Algorithm>.Ok(CaptureValueThunk(captureBody, ctx));

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
                return new EvalError.NotAnAlgorithm($"num({n.ToString(System.Globalization.CultureInfo.InvariantCulture)})") { Span = expr.Span };
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
        var preparedR = EvalAlgOutputPreparedCore(alg, ctx, valEnv);
        return preparedR.IsError
            ? preparedR.Error
            : EvalResult<Result>.Ok(preparedR.Value.Counted.Value);
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

    private static EvalResult<IReadOnlyList<Result>> EvalInitialLoopStateSlots(
        IReadOnlyList<ResolvedArgumentAlgorithm> initArgs,
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
            var slotR = EvalResolvedArgument(init, ctx, valEnv);
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
        int expectedStateValueCount,
        int actualStateValueCount,
        string loopName)
        // Expected is the binder-computed top-level state-slot count, NOT the
        // flattened capture count: a patterned step `Step((x, y))` has ONE
        // state slot but two flattened captures. The context's parameter names
        // are the matching top-level display labels ("(x, y)" is one entry).
        => new EvalError.WithContext(
            new LoopStateBindingContext(
                loopName,
                step.ParameterPatterns.Select(static pattern => pattern.DisplayName).ToList(),
                actualStateValueCount),
            new EvalError.ArityMismatch(expectedStateValueCount, actualStateValueCount));

    private static EvalError VariadicLoopStateArityMismatch(
        Algorithm step,
        int expectedMinimumStateValueCount,
        int actualStateValueCount,
        string loopName)
        => new EvalError.WithContext(
            new VariadicLoopStateBindingContext(
                loopName,
                step.Parameters
                    .Where(static parameter => parameter.Kind != ParameterKind.Collecting)
                    .Select(static parameter => parameter.DisplayName)
                    .ToList(),
                expectedMinimumStateValueCount,
                actualStateValueCount),
            new EvalError.ArityMismatch(expectedMinimumStateValueCount, actualStateValueCount));

    private static EvalResult<IReadOnlyList<(string Name, Result Value)>> BindEvaluatedSlotValueBindings(
        FlatCollectingBindingLayout layout,
        IReadOnlyList<(string ParameterName, BindingInputSlot Item)> normalBindings,
        CollectingCapture collectingCapture)
    {
        var valueBindings = new List<(string Name, Result Value)>(layout.Signature.Parameters.Count);
        var normalBindingIndex = 0;

        foreach (var parameter in layout.Signature.Parameters)
        {
            if (parameter.Kind == ParameterKind.Collecting)
            {
                valueBindings.Add((collectingCapture.Name, collectingCapture.Value));
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
        EvalCtx ctx,
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
                ctx,
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

        EvalResult<EvaluatedSlotBindings> BindFlatCollectingSlots(FlatCollectingBindingLayout layout)
        {
            var inputSlots = evaluatedSlots
                .Select(BindingInputSlot.FromEvaluatedValue)
                .ToArray();

            var boundItemsR = BindItemsToFlatCollectingLayout(
                layout,
                inputSlots,
                variadicArityMismatch);
            if (boundItemsR.IsError) return boundItemsR.Error;

            var boundItems = boundItemsR.Value;
            var capturedValues = new List<Result>(boundItems.CollectingItems.Count);
            foreach (var item in boundItems.CollectingItems)
            {
                if (item.Value is null)
                    return new EvalError.BadArity();

                capturedValues.Add(item.Value);
            }

            var collectingName = boundItems.CollectingParameterName
                ?? layout.CollectingName;
            if (collectingName is null)
                return new EvalError.BadArity();

            var collectingCaptureR = CreateCollectingCapture(ctx, collectingName, capturedValues);
            if (collectingCaptureR.IsError) return collectingCaptureR.Error;
            var collectingCapture = collectingCaptureR.Value;

            var valueBindingsR = BindEvaluatedSlotValueBindings(
                layout,
                boundItems.NormalBindings,
                collectingCapture);
            if (valueBindingsR.IsError) return valueBindingsR.Error;

            return EvalResult<EvaluatedSlotBindings>.Ok(new EvaluatedSlotBindings(
                valueBindingsR.Value,
                [(collectingCapture.Name, collectingCapture.CountedValue)]));
        }

        EvalResult<EvaluatedSlotBindings> BindLegacyShape()
        {
            if (UsesPatternBinding(algorithm))
                return BindPatternedSlots();

            return TryGetLegacyFlatCollectingBindingLayout(algorithm, callableName, out var legacyLayout)
                ? BindFlatCollectingSlots(legacyLayout)
                : BindFlatFixedSlots();
        }

        EvalResult<EvaluatedSlotBindings> BindSelectedFlatCollectingShape()
        {
            return bindingSelection.Plan is not null
                && TryGetFlatCollectingBindingLayout(bindingSelection.Plan, out var layout)
                ? BindFlatCollectingSlots(layout)
                : BindLegacyShape();
        }

        return bindingSelection.Shape switch
        {
            GenericLoopStepBindingShape.Patterned => BindPatternedSlots(),
            GenericLoopStepBindingShape.FlatFixed => BindFlatFixedSlots(),
            GenericLoopStepBindingShape.FlatCollecting => BindSelectedFlatCollectingShape(),
            _ => BindLegacyShape(),
        };
    }

    private static EvalResult<EvaluatedSlotBindings> BindLoopStepState(
        Algorithm step,
        IReadOnlyList<Result> stateSlots,
        EvalCtx ctx,
        string loopName,
        GenericLoopStepBindingSelection bindingSelection)
    {
        // Loop state slots are produced by initial loop arguments or previous
        // step output. They are already evaluated and must not use ordinary
        // call-site behavior such as spread slot expansion.
        return BindEvaluatedSlotsToParameters(
            step,
            stateSlots,
            ctx,
            "loop step",
            bindingSelection,
            (required, actual) => LoopStateArityMismatch(step, required, actual, loopName),
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

        // The operand-shape context renders the WHOLE operand trees, which is
        // quadratic over an operator chain — build it only on the error paths that
        // actually attach it (the rendered text is identical either way).
        var xR = RequireNumericScalarOperand(op, "left", leftValue);
        if (xR.IsError)
            return new EvalError.WithContext(BinaryOperandContext(op, left, right), xR.Error) { Span = span };
        var yR = RequireNumericScalarOperand(op, "right", rightValue);
        if (yR.IsError)
            return new EvalError.WithContext(BinaryOperandContext(op, left, right), yR.Error) { Span = span };
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
        // One loop ITERATION is one charged work unit. Loops repeat work without growing
        // the host stack, so they charge work only — never depth. This is the single
        // per-iteration chokepoint shared by generic `while` and `repeat`; the optimized
        // loop paths never run under a step budget (see CreateRootCtx), so the charged
        // count is exactly the generic one.
        if (ctx.Budget.TryChargeStep() is { } limitError)
            return limitError;

        var bindingSelection = SelectGenericLoopStepBinding(step);
        var boundR = BindLoopStepState(step, stateSlots, ctx, loopName, bindingSelection);
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
            : MakeCheckedSequenceCapture(ctx, outputSlotsR.Value);
    }

    internal static EvalResult<(IReadOnlyList<Result> NextStateSlots, decimal Continue)> SplitContSlots(
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
                    var condR = EvalResolvedArgument(args[0], ctx, valEnv);
                    if (condR.IsError) return condR.Error;
                    var truth = condR.Value.TruthValue();
                    if (truth is null) return new EvalError.BadArity();
                    return truth.Value
                        ? EvalResolvedArgument(args[1], ctx, valEnv)
                        : EvalResolvedArgument(args[2], ctx, valEnv);
                }

            // while(step, init1, init2, ...)
            case (BuiltinId.@while, _) when args.Count >= 2:
                {
                    var stepR = ResolveArgumentAlgorithm(args[0], ctx);
                    if (stepR.IsError) return stepR.Error;
                    var initialStateR = EvalInitialLoopStateSlots(args.Skip(1).ToList(), ctx, valEnv);
                    if (initialStateR.IsError) return initialStateR.Error;
                    return WhileLoop(stepR.Value, initialStateR.Value, ctx, valEnv);
                }

            // repeat(step, count, init1, init2, ...)
            case (BuiltinId.@repeat, _) when args.Count >= 3:
                {
                    var stepR = ResolveArgumentAlgorithm(args[0], ctx);
                    if (stepR.IsError) return stepR.Error;
                    var countR = EvalResolvedArgument(args[1], ctx, valEnv);
                    if (countR.IsError) return countR.Error;
                    var nR = ExpectWholeInt(countR.Value, "Repeat count");
                    if (nR.IsError) return nR.Error;
                    // Domain check BEFORE narrowing, mirroring the counted twin above.
                    if (nR.Value < 0) return new EvalError.IllegalInEval("Repeat count must be >= 0");
                    var n = nR.Value >= long.MaxValue ? long.MaxValue : (long)nR.Value;
                    var initialStateR = EvalInitialLoopStateSlots(args.Skip(2).ToList(), ctx, valEnv);
                    if (initialStateR.IsError) return initialStateR.Error;
                    return RepeatLoop(stepR.Value, n, initialStateR.Value, ctx, valEnv);
                }

            // atoms(value) — recursively collect numeric atoms into one exact list
            case (BuiltinId.@atoms, 1):
                {
                    var atomsR = EvalResolvedArgument(args[0], ctx, valEnv);
                    if (atomsR.IsError) return atomsR.Error;
                    var atomsListR = MakeLanguageAtomsResult(ctx, atomsR.Value);
                    return atomsListR.IsError ? atomsListR.Error : EvalResult<Result>.Ok(atomsListR.Value.Value);
                }

            // range(start, stop) — inclusive integers materialized as one exact list.
            case (BuiltinId.@range, 2):
                {
                    var rangeR = EvalBuiltinRangeArguments(args, ctx, valEnv);
                    if (rangeR.IsError) return rangeR.Error;

                    return BuildInclusiveRangeChecked(ctx, rangeR.Value);
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
            return LoopStateArityMismatch(step, step.Params.Count, initialStateSlots.Count, "while");

        return LoopOptimizer.TryEvaluateWhile(
            step,
            initialStateSlots,
            ctx,
            valEnv,
            fallbackStateSlots => WhileLoopGenericCounted(step, fallbackStateSlots, ctx, valEnv),
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
            if (cont == 0) return MakeCheckedLoopStateResult(ctx, stateSlots);
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
            return MakeCheckedLoopStateResult(ctx, initialStateSlots);

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
            return LoopStateArityMismatch(step, step.Params.Count, initialStateSlots.Count, "repeat");

        return LoopOptimizer.TryEvaluateRepeat(
            step,
            count,
            initialStateSlots,
            ctx,
            valEnv,
            (remainingCount, fallbackStateSlots) => RepeatLoopGenericCounted(step, remainingCount, fallbackStateSlots, ctx, valEnv),
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
        return MakeCheckedLoopStateResult(ctx, stateSlots);
    }

    // ── Iterative expression-spine evaluation ───────────────────────────────

    /// <summary>
    /// The pure-expression composite node kinds whose evaluation is driven by the
    /// iterative spine machine (<see cref="EvalExpressionSpineCounted"/>) instead of
    /// CLR recursion: unary and binary operators, index selection, and list literals.
    /// These are the shapes whose recursive evaluation frames were measured to
    /// exhaust a 1 MiB stack within the structural depth ceiling (binary/unary spines
    /// at ~330-340 nodes, index spines at ~270-285, list spines at ~290-300 in Debug),
    /// so within-ceiling safety REQUIRES that their nesting consume no proportional
    /// call stack. Algorithm-carrying kinds (blocks, calls, dot-calls) stay on their
    /// recursive paths and are bounded by the structural ceiling instead; the internal
    /// sequence-join kinds already have their own iterative handling
    /// (<see cref="EvalSequenceConstructCounted"/>, <see cref="EvalSequenceSpreadCounted"/>).
    /// </summary>
    private static bool IsExpressionSpineNode(Expr expr)
        => expr is Expr.Unary or Expr.Binary or Expr.Index or Expr.ListLiteral;

    /// <summary>One in-progress spine node in <see cref="EvalExpressionSpineCounted"/>.</summary>
    private struct ExpressionSpineFrame(Expr node)
    {
        public readonly Expr Node = node;

        /// <summary>Unary/Binary/Index: completed child count. ListLiteral: next element index.</summary>
        public int Phase;

        /// <summary>Binary left value / Index target value, once evaluated.</summary>
        public Result? FirstValue;

        /// <summary>ListLiteral element accumulator (exact written slots, spread already expanded).</summary>
        public List<Result>? ListItems;
    }

    /// <summary>
    /// Evaluates one maximal pure-expression spine with an explicit frame stack,
    /// replicating the recursive per-kind evaluation EXACTLY — child order, error
    /// decoration, spans, budget reservations, and emitted counts — while consuming
    /// O(1) CLR stack per spine node. Children that are not spine kinds are delegated
    /// to the ordinary recursive paths (one bounded frame layer; the structural
    /// preflight bounds how many such layers a path can alternate through).
    ///
    /// <para>Per-kind semantics preserved here (previously the recursive
    /// <c>Eval</c> cases and the <c>EvalIndexSelectionCounted</c> /
    /// <c>EvalListLiteralCounted</c> helpers):</para>
    /// <list type="bullet">
    ///   <item><b>Unary</b>: empty sequence propagates; strings are a
    ///   <see cref="EvalError.TypeMismatch"/> at the unary expression's span; operand
    ///   errors propagate untouched. Lean: <c>eval</c> unary case.</item>
    ///   <item><b>Binary</b>: left then right, each error propagating untouched, then
    ///   <see cref="ApplyBinaryOperator"/>. Lean: <c>eval</c> binary case.</item>
    ///   <item><b>Index</b>: target then selector; every child or coercion error gains
    ///   the index expression's span when it has none; the selected item re-emits its
    ///   PROJECTED count (<c>S:0</c> re-emits, never re-counts). Lean:
    ///   <c>evalIndexSelectionCounted</c>.</item>
    ///   <item><b>ListLiteral</b>: element slots follow the written-parentheses
    ///   expression-list slot rules (<see cref="EvalExplicitSequenceValueExprSlots"/>);
    ///   elements are stored EXACTLY (no singleton erasure, no empty canonicalization),
    ///   the collection reservation happens before the persistent list is built, and a
    ///   list literal always emits one value. Lean: <c>evalListLiteralCounted</c>;
    ///   plain <c>Eval</c> is this function's value projection on both sides.</item>
    /// </list>
    /// </summary>
    private static EvalResult<CountedResult> EvalExpressionSpineCounted(
        Expr root,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var frames = new ExpressionSpineFrame[16];
        var frameCount = 0;
        frames[frameCount++] = new ExpressionSpineFrame(root);

        // The counted result most recently produced for the top frame's pending
        // child. Machine-kind children deliver here when their frame pops; delegated
        // children deliver here directly.
        CountedResult pendingChild = default;
        var hasPendingChild = false;

        while (true)
        {
            ref var frame = ref frames[frameCount - 1];
            EvalResult<CountedResult>? completed = null;
            Expr? requestedChild = null;

            switch (frame.Node)
            {
                case Expr.Unary(var unaryOp, var operand):
                {
                    if (!hasPendingChild)
                    {
                        requestedChild = operand;
                        break;
                    }

                    hasPendingChild = false;
                    var operandValue = pendingChild.Value;

                    // Empty result propagation through unary operators.
                    if (operandValue is Result.SequenceValue(var uItems) && uItems.Count == 0)
                    {
                        var empty = Result.SequenceValue.TakeOwnership([]);
                        completed = EvalResult<CountedResult>.Ok(new CountedResult(empty, empty.ValueCount()));
                        break;
                    }

                    if (operandValue is Result.Str)
                    {
                        completed = new EvalError.TypeMismatch("Unary operator is not supported for strings")
                        {
                            Span = frame.Node.Span,
                        };
                        break;
                    }

                    var vR = ExpectInt(operandValue);
                    if (vR.IsError)
                    {
                        completed = vR.Error;
                        break;
                    }

                    var unaryResult = unaryOp switch
                    {
                        UnaryOp.Minus => -vR.Value,
                        UnaryOp.Not => vR.Value == 0 ? 1m : 0m,
                        _ => 0m,
                    };
                    var unaryValue = new Result.Atom(unaryResult);
                    completed = EvalResult<CountedResult>.Ok(new CountedResult(unaryValue, unaryValue.ValueCount()));
                    break;
                }

                case Expr.Binary(var op, var left, var right):
                {
                    if (frame.Phase == 0)
                    {
                        if (!hasPendingChild)
                        {
                            requestedChild = left;
                            break;
                        }

                        hasPendingChild = false;
                        frame.FirstValue = pendingChild.Value;
                        frame.Phase = 1;
                        requestedChild = right;
                        break;
                    }

                    hasPendingChild = false;
                    var binaryR = ApplyBinaryOperator(
                        op, left, right, frame.FirstValue!, pendingChild.Value, frame.Node.Span);
                    completed = binaryR.IsError
                        ? binaryR.Error
                        : EvalResult<CountedResult>.Ok(new CountedResult(
                            binaryR.Value, binaryR.Value.ValueCount()));
                    break;
                }

                case Expr.Index(var target, var selector):
                {
                    if (frame.Phase == 0)
                    {
                        if (!hasPendingChild)
                        {
                            requestedChild = target;
                            break;
                        }

                        hasPendingChild = false;
                        frame.FirstValue = pendingChild.Value;
                        frame.Phase = 1;
                        requestedChild = selector;
                        break;
                    }

                    hasPendingChild = false;

                    // ExpectInt reports TypeMismatch/BadArity from a Result and so has no
                    // span of its own; the index expression is the nearest source location.
                    var nR = ExpectInt(pendingChild.Value);
                    if (nR.IsError)
                    {
                        completed = AtSpanIfMissing(nR.Error, frame.Node.Span);
                        break;
                    }

                    var n = nR.Value;
                    if (n < 0 || n != Math.Floor(n))
                    {
                        completed = new EvalError.BadIndex() { Span = frame.Node.Span };
                        break;
                    }

                    // Lean models the selector as an unbounded integer and reports
                    // badIndex for any position past the target's items; a selector
                    // beyond int range can never be in range, so it is the same
                    // out-of-range error rather than a host overflow.
                    if (n > int.MaxValue)
                    {
                        completed = new EvalError.BadIndex() { Span = frame.Node.Span };
                        break;
                    }

                    var selected = frame.FirstValue!.SelectProjected((int)n);
                    completed = selected is null
                        ? new EvalError.BadIndex() { Span = frame.Node.Span }
                        : EvalResult<CountedResult>.Ok(new CountedResult(
                            selected.Value.Value, selected.Value.EmittedCount));
                    break;
                }

                case Expr.ListLiteral(var elements):
                {
                    frame.ListItems ??= [];
                    if (hasPendingChild)
                    {
                        // WRITTEN-SLOT REIFICATION: a machine-kind element is never a
                        // spread, so its counted supply contributes exactly ONE value.
                        hasPendingChild = false;
                        frame.ListItems.Add(pendingChild.Value);
                        frame.Phase++;
                    }

                    while (frame.Phase < elements.Count)
                    {
                        var element = elements[frame.Phase];
                        if (IsExpressionSpineNode(element))
                            break;

                        var slotsR = EvalExplicitSequenceValueExprSlots(element, ctx, valEnv);
                        if (slotsR.IsError)
                        {
                            completed = slotsR.Error;
                            break;
                        }

                        frame.ListItems.AddRange(slotsR.Value);
                        frame.Phase++;
                    }

                    if (completed is not null)
                        break;

                    if (frame.Phase < elements.Count)
                    {
                        requestedChild = elements[frame.Phase];
                        break;
                    }

                    // Cardinality is known once the written slots (including spread
                    // expansion) are evaluated, so the reservation happens before the
                    // persistent list is built.
                    if (ReserveCollection(ctx, frame.ListItems.Count, frame.Node.Span) is { } limitError)
                    {
                        completed = limitError;
                        break;
                    }

                    completed = EvalResult<CountedResult>.Ok(new CountedResult(
                        Result.ListValue.TakeOwnership(frame.ListItems.ToArray()), 1));
                    break;
                }

                default:
                    throw new InvalidOperationException(
                        $"EvalExpressionSpineCounted received the non-spine node kind '{frame.Node.GetType()}'.");
            }

            if (requestedChild is not null)
            {
                if (IsExpressionSpineNode(requestedChild))
                {
                    if (frameCount == frames.Length)
                        Array.Resize(ref frames, frames.Length * 2);
                    frames[frameCount++] = new ExpressionSpineFrame(requestedChild);
                    continue;
                }

                // Delegated child: exactly the call the recursive code made — plain
                // Eval for unary/binary operands and index targets/selectors. (List
                // elements never reach here; non-machine elements go through
                // EvalExplicitSequenceValueExprSlots above, exactly as before.)
                var childR = Eval(requestedChild, ctx, valEnv);
                if (childR.IsError)
                {
                    completed = childR.Error;
                }
                else
                {
                    pendingChild = new CountedResult(childR.Value, childR.Value.ValueCount());
                    hasPendingChild = true;
                    continue;
                }
            }

            if (completed is not { } completedResult)
                continue;

            if (completedResult.IsError)
            {
                // Unwind exactly like the recursive returns: the frame whose child
                // failed applies its child-error decoration (only Index attaches its
                // span), then returns the error to ITS parent, which decorates in
                // turn. An error produced by a frame's own apply step starts at that
                // frame's parent.
                var error = completedResult.Error;
                var decorateTopFrame = requestedChild is not null;
                while (frameCount > 0)
                {
                    ref var unwound = ref frames[frameCount - 1];
                    if (decorateTopFrame && unwound.Node is Expr.Index)
                        error = AtSpanIfMissing(error, unwound.Node.Span);

                    decorateTopFrame = true;
                    frameCount--;
                }

                return error;
            }

            frameCount--;
            if (frameCount == 0)
                return completedResult;

            pendingChild = completedResult.Value;
            hasPendingChild = true;
        }
    }

    // ── Main eval ───────────────────────────────────────────────────────────

    /// <summary>Lean: eval → EvalM Result.</summary>
    private static EvalResult<Result> Eval(
        Expr expr,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        // Structural nesting charges no dynamic invocation depth; the pre-evaluation
        // structural preflight (AstStructuralPreflight) bounds every accepted tree to
        // EvaluationLimits.MaxSupportedAstDepth before evaluation begins, and the
        // pure-expression composite kinds (unary, binary, index, list literal, and the
        // internal sequence joins) evaluate ITERATIVELY, so recursion here grows only
        // at algorithm boundaries (blocks, calls, dot-calls) — the shapes the ceiling
        // is calibrated against. Deliberately NO TryEnsureSufficientExecutionStack
        // probe here: the CLR probe reserves roughly half of a 1 MiB stack, so a
        // per-node probe rejects deep parser-produced programs that complete fine
        // today (measured: a 288-level bracket nesting).
        switch (expr)
        {
            case Expr.Num(var n):
                return EvalResult<Result>.Ok(new Result.Atom(n));

            case Expr.StringLiteral(var s):
                return MakeStringResult(ctx, s, expr.Span);

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

            case Expr.Unary or Expr.Binary:
                {
                    // Unary and binary spines evaluate iteratively; the machine
                    // preserves the recursive semantics exactly (empty-result
                    // propagation, string rejection, ApplyBinaryOperator).
                    var spineR = EvalExpressionSpineCounted(expr, ctx, valEnv);
                    return spineR.IsError
                        ? spineR.Error
                        : EvalResult<Result>.Ok(spineR.Value.Value);
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

            case Expr.ListLiteral:
                {
                    var listLiteralR = EvalExpressionSpineCounted(expr, ctx, valEnv);
                    return listLiteralR.IsError
                        ? listLiteralR.Error
                        : EvalResult<Result>.Ok(listLiteralR.Value.Value);
                }

            case Expr.AlgorithmExpr(var alg):
                {
                    var wired = WireToCaller(ctx, alg);
                    if (wired.Params.Count == 0)
                        return WithSpan(expr.Span ?? FirstSpan(wired.Output), EvalAlgOutput(wired, ctx, valEnv));
                    var blockSpan = expr.Span ?? FirstSpan(wired.Output);
                    return MissingImplicitArguments<Result>(wired.Params, blockSpan);
                }

            case Expr.Capture(var captureBody):
                return WithSpan(expr.Span ?? FirstSpan(captureBody), EvalCaptureValue(captureBody, ctx, valEnv));

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
                // (the context — which renders the receiver's name — is built only on error).
                return WithSpan(expr.Span, WithDotCallCtx(dotTarget, dotName, ctx,
                    EvalDotCall(dotTarget, dotName, dotArgs, ctx, valEnv)));

            case Expr.Call(var func, var callArgs):
                return WithSpan(expr.Span,
                    EvalCallExpr(func, callArgs, ctx, valEnv));

            case Expr.Index:
                {
                    var selectionR = EvalExpressionSpineCounted(expr, ctx, valEnv);
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
    /// sequence value and only caller-site <c>spread</c> re-spreads it.
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

            case Expr.Unary or Expr.Binary or Expr.ListLiteral:
                return EvalExpressionSpineCounted(expr, ctx, valEnv);

            case Expr.EmptySequence(var depth):
                {
                    var emptyValue = BuildEmptySequenceValue(depth);
                    return EvalResult<CountedResult>.Ok(new CountedResult(emptyValue, emptyValue.ValueCount()));
                }

            case Expr.AlgorithmExpr(var alg):
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

            case Expr.Capture(var captureBody):
                {
                    // A capture in value position is a value boundary: the body's
                    // supply is captured to one canonical value and re-counted as
                    // that value's ValueCount.
                    var captureR = WithSpan(expr.Span ?? FirstSpan(captureBody), EvalCaptureValue(captureBody, ctx, valEnv));
                    if (captureR.IsError) return captureR.Error;
                    return EvalResult<CountedResult>.Ok(new CountedResult(captureR.Value, captureR.Value.ValueCount()));
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
                return WithSpan(expr.Span, WithDotCallCtx(dotTarget, dotName, ctx,
                    EvalDotCallCounted(dotTarget, dotName, dotArgs, ctx, valEnv)));

            case Expr.Call(var func, var callArgs):
                return WithSpan(expr.Span,
                    EvalCallCountedExpr(func, callArgs, ctx, valEnv));

            case Expr.Index:
                // The spine machine owns the index-expression span.
                return EvalExpressionSpineCounted(expr, ctx, valEnv);

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
    /// True when an argument expression supplies ONLY a value in argument
    /// position. A capture is a value boundary: it suppresses the algorithm
    /// identity of anything inside it, so higher-order probing never sees the
    /// enclosed content as callable. <see cref="Expr.AlgorithmExpr"/> is
    /// deliberately NOT value-only: an algorithm block explicitly exposes its
    /// contained Algorithm on the algorithm channel regardless of
    /// parameter/declaration/output count — <c>{42}</c> is as much an
    /// Algorithm as <c>{a + 1}</c> — while the value channel reifies the
    /// written slot independently.
    /// </summary>
    private static bool ShouldWrapArgExprAsValue(Expr expr) => expr is Expr.Capture;

    /// <summary>
    /// Builtin argument adapters reify each written slot as one value-producing
    /// adapter. A zero-declaration algorithm block slot keeps its one-slot
    /// value boundary here (written-slot reification: <c>repeat(step, n, {1, 2})</c>
    /// supplies ONE initial state slot), exactly as before the block's
    /// algorithm identity became visible to user-call higher-order binding.
    /// Blocks with parameters, properties, or opens still resolve as
    /// algorithms for algorithm-consuming builtin arguments (callbacks).
    /// </summary>
    private static bool IsZeroDeclarationBlockValueSlot(Expr expr) => expr is
        Expr.AlgorithmExpr(var algorithm)
            && algorithm.Params.Count == 0
            && algorithm.Opens.Count == 0
            && algorithm.Properties.Count == 0;

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
            || IsZeroDeclarationBlockValueSlot(expr)
            || expr is Expr.Param(var name)
                && (LookupCountedParam(ctx.CountedParamEnv, name) is not null
                    || LookupVal(valEnv, name) is not null);

    private static EvalResult<IReadOnlyList<Algorithm>> ResolveArgAlgs(
        OutputBundle args,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var resolvedR = ResolveArgAlgsWithSequenceSpread(args, ctx, valEnv);
        if (resolvedR.IsError) return resolvedR.Error;

        var algorithms = new List<Algorithm>(resolvedR.Value.Count);
        foreach (var arg in resolvedR.Value)
        {
            if (arg.Algorithm is null)
                return new EvalError.BadArity();
            algorithms.Add(arg.Algorithm);
        }

        return EvalResult<IReadOnlyList<Algorithm>>.Ok(algorithms);
    }

    private static EvalResult<IReadOnlyList<ResolvedArgumentAlgorithm>> ResolveArgAlgsWithSequenceSpread(
        OutputBundle args,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var result = new List<ResolvedArgumentAlgorithm>(args.Count);
        foreach (var argExpr in args)
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
    /// A capture slot never yields a candidate (a capture is a value boundary
    /// and suppresses enclosed identity); an algorithm block always yields its
    /// contained Algorithm, regardless of parameter/declaration/output count —
    /// <c>Call0({42})</c> binds the brace algorithm exactly like
    /// <c>Call0(Const)</c> binds a named zero-parameter property.
    /// Lean: tryResolveArgAlgs.
    /// </summary>
    private static EvalResult<IReadOnlyList<Algorithm?>> TryResolveArgAlgs(
        OutputBundle args, EvalCtx ctx)
    {
        var result = new List<Algorithm?>(args.Count);
        foreach (var argExpr in args)
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
        OutputBundle args,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var calleeR = ResolveAlg(func, ctx);
        if (calleeR.IsError) return calleeR.Error;
        return EvalResolvedCall(
            calleeR.Value,
            args,
            ctx,
            valEnv,
            CallDiagnosticName.FromExpression(func));
    }

    /// <summary>
    /// Counted call evaluation for <c>reduce</c> step validation.
    /// Lean: <c>evalCallCountedExpr</c> (Lean also attaches the call-context wrapper there).
    /// </summary>
    private static EvalResult<CountedResult> EvalCallCounted(
        Expr func,
        OutputBundle args,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var calleeR = ResolveAlg(func, ctx);
        if (calleeR.IsError) return calleeR.Error;
        return EvalResolvedCallCounted(
            calleeR.Value,
            args,
            ctx,
            valEnv,
            CallDiagnosticName.FromExpression(func));
    }

    /// <summary>
    /// Context-aware call evaluation for expression position.
    /// </summary>
    private static EvalResult<Result> EvalCallExpr(
        Expr func,
        OutputBundle args,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var diagnosticName = CallDiagnosticName.FromExpression(func);
        var calleeR = ResolveAlg(func, ctx);
        if (calleeR.IsError)
            return new EvalError.WithContext(CtxCall(diagnosticName, ctx), calleeR.Error) { Span = calleeR.Error.Span };

        if (TryEvaluateSequencePipeline(
            SequencePipelineInvocation.PlainCall(func, args, calleeR.Value),
            ctx,
            valEnv,
            out var sequencePipelineR))
            return WithCallCtx(
                diagnosticName,
                ctx,
                sequencePipelineR.IsError
                    ? sequencePipelineR.Error
                    : EvalResult<Result>.Ok(sequencePipelineR.Value.Value));

        return WithCallCtx(
            diagnosticName,
            ctx,
            EvalResolvedCall(calleeR.Value, args, ctx, valEnv, diagnosticName));
    }

    /// <summary>
    /// Counted expression-position call evaluation mirroring <see cref="EvalCallExpr"/>.
    /// </summary>
    private static EvalResult<CountedResult> EvalCallCountedExpr(
        Expr func,
        OutputBundle args,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var diagnosticName = CallDiagnosticName.FromExpression(func);
        var calleeR = ResolveAlg(func, ctx);
        if (calleeR.IsError)
            return new EvalError.WithContext(CtxCall(diagnosticName, ctx), calleeR.Error) { Span = calleeR.Error.Span };

        if (TryEvaluateSequencePipeline(
            SequencePipelineInvocation.PlainCall(func, args, calleeR.Value),
            ctx,
            valEnv,
            out var sequencePipelineR))
            return WithCallCtx(diagnosticName, ctx, sequencePipelineR);

        return WithCallCtx(
            diagnosticName,
            ctx,
            EvalResolvedCallCounted(calleeR.Value, args, ctx, valEnv, diagnosticName));
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
    /// <summary>
    /// Assemble the evaluated argument values for a conditional (multi-clause)
    /// call through the shared call argument pipeline
    /// (<see cref="BuildCallArgumentInputs"/>): non-spread slots reify as one
    /// value each and explicit spread expands by one value boundary, exactly
    /// as for every other callable shape. Clause matching needs plain values,
    /// so an algorithm-only argument surfaces its value-evaluation error.
    /// </summary>
    private static EvalResult<IReadOnlyList<Result>> EvalConditionalCallArguments(
        OutputBundle args,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv,
        IReadOnlyList<bool>? preserveArgBoundaries)
    {
        var inputsR = BuildCallArgumentInputs(args, ctx, valEnv, preserveArgBoundaries);
        if (inputsR.IsError) return inputsR.Error;

        var argResults = new List<Result>(inputsR.Value.Count);
        foreach (var input in inputsR.Value)
        {
            if (input.Value is null)
                return input.ValueError ?? new EvalError.BadArity();

            argResults.Add(input.Value);
        }

        return EvalResult<IReadOnlyList<Result>>.Ok(argResults);
    }

    private static EvalResult<Result> EvalConditionalCall(
        Algorithm callee, OutputBundle args,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv,
        CallDiagnosticName calleeName,
        IReadOnlyList<bool>? preserveArgBoundaries = null)
    {
        // Charged dynamic invocation boundary: clause selection plus the selected
        // branch body are ONE dynamic invocation, exactly like a flat user call.
        if (ctx.Budget.TryEnterInvocation() is { } limitError)
            return AtSpanIfMissing(limitError, FirstSpan(args));

        try
        {
            return EvalConditionalCallCore(callee, args, ctx, valEnv, calleeName, preserveArgBoundaries);
        }
        finally
        {
            ctx.Budget.ExitInvocation();
        }
    }

    private static EvalResult<Result> EvalConditionalCallCore(
        Algorithm callee, OutputBundle args,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv,
        CallDiagnosticName calleeName,
        IReadOnlyList<bool>? preserveArgBoundaries)
    {
        // Shared argument-slot assembly: explicit spread expands into ordinary
        // argument slots BEFORE clause matching, so a multi-clause callee sees
        // the same argument supply as every other callable shape.
        var argResultsR = EvalConditionalCallArguments(args, ctx, valEnv, preserveArgBoundaries);
        if (argResultsR.IsError) return argResultsR.Error;
        var argResults = argResultsR.Value;

        if (callee.HasDuplicateBranchPatterns())
            return new EvalError.DuplicateBranchPattern();

        var match = MatchCallBranches(callee.Branches, argResults);
        if (match is null)
            return new EvalError.NoMatchingBranch(calleeName.Render(ctx));

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
        Algorithm callee, OutputBundle args,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv,
        CallDiagnosticName calleeName,
        IReadOnlyList<bool>? preserveArgBoundaries = null)
    {
        // Charged dynamic invocation boundary (see EvalConditionalCall).
        if (ctx.Budget.TryEnterInvocation() is { } limitError)
            return AtSpanIfMissing(limitError, FirstSpan(args));

        try
        {
            return EvalConditionalCallCountedCore(callee, args, ctx, valEnv, calleeName, preserveArgBoundaries);
        }
        finally
        {
            ctx.Budget.ExitInvocation();
        }
    }

    private static EvalResult<CountedResult> EvalConditionalCallCountedCore(
        Algorithm callee, OutputBundle args,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv,
        CallDiagnosticName calleeName,
        IReadOnlyList<bool>? preserveArgBoundaries)
    {
        var argResultsR = EvalConditionalCallArguments(args, ctx, valEnv, preserveArgBoundaries);
        if (argResultsR.IsError) return argResultsR.Error;
        var argResults = argResultsR.Value;

        if (callee.HasDuplicateBranchPatterns())
            return new EvalError.DuplicateBranchPattern();

        var match = MatchCallBranches(callee.Branches, argResults);
        if (match is null)
            return new EvalError.NoMatchingBranch(calleeName.Render(ctx));

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
    /// If both fail, the eager-evaluation error is propagated. Every
    /// <see cref="Expr.AlgorithmExpr"/> contributes its contained algorithm to
    /// the AlgEnv side regardless of declaration/output count. A
    /// <see cref="Expr.Capture"/> contributes only its fresh zero-parameter
    /// value thunk, never the algorithm identity of an expression it contains.
    ///
    /// Flat fixed calls bind call-site structure: each comma argument is one
    /// argument expression, while a bare spread expression explicitly
    /// contributes its spread top-level items. Multi-output values from normal
    /// expressions, including <c>.atoms</c>, remain one argument expression.
    /// Earlier explicit argument positions remain distinct on the eager value
    /// side even if some later arguments bind only through AlgEnv.
    /// </summary>
    private static EvalResult<Result> EvalUserCall(
        Algorithm callee, OutputBundle args,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv,
        IReadOnlyList<bool>? preserveArgBoundaries,
        CallDiagnosticName calleeName)
    {
        // Charged dynamic invocation boundary (see EvaluationBudget).
        if (ctx.Budget.TryEnterInvocation() is { } limitError)
            return AtSpanIfMissing(limitError, FirstSpan(args));

        try
        {
            return EvalUserCallCore(callee, args, ctx, valEnv, preserveArgBoundaries, calleeName);
        }
        finally
        {
            ctx.Budget.ExitInvocation();
        }
    }

    private static EvalResult<Result> EvalUserCallCore(
        Algorithm callee, OutputBundle args,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv,
        IReadOnlyList<bool>? preserveArgBoundaries,
        CallDiagnosticName calleeName)
    {
        if (callee.Output.Count == 0)
            return new EvalError.MissingOutput();

        // Assignment-deconstruction target: project this target's slot from the group's shared
        // run-scoped bind (computed once for all N targets) instead of rebinding the whole
        // N-capture pattern per target. The non-counted value is the bound value itself.
        if (callee is Algorithm.User { IsAssignmentDeconstructionHelper: true } deconstructionHelper
            && TryProjectSharedDeconstructionTarget(deconstructionHelper, args, ctx, valEnv, calleeName, preserveArgBoundaries) is { } sharedTarget)
        {
            return sharedTarget;
        }

        var signature = CallableSignature.FromAlgorithm(calleeName.StructuralName, callee);
        var bindingPlan = CallableBindingPlan.FromSignature(signature);

        if (bindingPlan.RequiresPatternedBinding)
        {
            var bindingsR = BindPatternedUserCall(callee, args, ctx, valEnv, calleeName, preserveArgBoundaries);
            if (bindingsR.IsError) return bindingsR.Error;

            var bindings = bindingsR.Value;
            var groupedCtx = WithUserCallBindingEnvironments(ctx, bindings, callee.Params);
            var groupedEnv = Concat(bindings.ValueBindings, valEnv);
            return EvalAlgOutput(callee, groupedCtx, groupedEnv);
        }

        if (IsDeconstructionUserCallShape(signature))
        {
            var bindingsR = BindDeconstructionUserCall(callee, args, ctx, valEnv, calleeName, preserveArgBoundaries);
            if (bindingsR.IsError) return bindingsR.Error;

            var bindings = bindingsR.Value;
            var deconstructionCtx = WithUserCallBindingEnvironments(ctx, bindings, callee.Params);
            var deconstructionEnv = Concat(bindings.ValueBindings, valEnv);
            return EvalAlgOutput(callee, deconstructionCtx, deconstructionEnv);
        }

        if (!TryGetPlanDerivedFlatFixedParameterNames(bindingPlan, out var flatFixedParams))
            flatFixedParams = callee.Params;

        var flatBindingsR = BindFlatFixedUserCallArguments(
            callee,
            calleeName,
            flatFixedParams,
            args,
            ctx,
            valEnv);
        if (flatBindingsR.IsError) return flatBindingsR.Error;

        var flatBindings = flatBindingsR.Value;
        return EvalAlgOutput(callee, flatBindings.Context, flatBindings.ValueEnvironment);
    }

    /// <summary>
    /// Dispatches an already-resolved callee.
    /// </summary>
    private static EvalResult<Result> EvalResolvedCall(
        Algorithm callee,
        OutputBundle args,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv,
        CallDiagnosticName calleeName,
        IReadOnlyList<bool>? preserveArgBoundaries = null)
    {
        if (callee is Algorithm.Builtin(var builtinId))
        {
            var argAlgsR = ResolveArgAlgsWithSequenceSpread(args, ctx, valEnv);
            if (argAlgsR.IsError) return argAlgsR.Error;
            return ApplyBuiltinResolved(builtinId, argAlgsR.Value, ctx, valEnv);
        }

        if (TryGetFlatBinderUserEquivalent(callee) is { } simpleCallee)
            return EvalUserCall(
                simpleCallee,
                args,
                ctx,
                valEnv,
                preserveArgBoundaries,
                calleeName);

        if (callee is Algorithm.Conditional)
            return EvalConditionalCall(callee, args, ctx, valEnv, calleeName, preserveArgBoundaries);

        return EvalUserCall(
            callee,
            args,
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
    /// caller-site <c>spread</c> re-spreads it.
    /// Lean: <c>evalUserCallCounted</c>.
    /// </summary>
    private static EvalResult<CountedResult> EvalUserCallCounted(
        Algorithm callee, OutputBundle args,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv,
        IReadOnlyList<bool>? preserveArgBoundaries,
        CallDiagnosticName calleeName)
    {
        // Charged dynamic invocation boundary (see EvaluationBudget).
        if (ctx.Budget.TryEnterInvocation() is { } limitError)
            return AtSpanIfMissing(limitError, FirstSpan(args));

        try
        {
            return EvalUserCallCountedCore(callee, args, ctx, valEnv, preserveArgBoundaries, calleeName);
        }
        finally
        {
            ctx.Budget.ExitInvocation();
        }
    }

    private static EvalResult<CountedResult> EvalUserCallCountedCore(
        Algorithm callee, OutputBundle args,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv,
        IReadOnlyList<bool>? preserveArgBoundaries,
        CallDiagnosticName calleeName)
    {
        if (callee.Output.Count == 0)
            return new EvalError.MissingOutput();

        // Assignment-deconstruction target: project this target's slot from the group's shared
        // run-scoped bind. The projected value is re-counted at this value boundary exactly as the
        // helper body's `Param(xi)` result would be (`ReCountValueBoundary`): count = ValueCount().
        if (callee is Algorithm.User { IsAssignmentDeconstructionHelper: true } deconstructionHelper
            && TryProjectSharedDeconstructionTarget(deconstructionHelper, args, ctx, valEnv, calleeName, preserveArgBoundaries) is { } sharedTarget)
        {
            return sharedTarget.IsError
                ? sharedTarget.Error
                : EvalResult<CountedResult>.Ok(new CountedResult(sharedTarget.Value, sharedTarget.Value.ValueCount()));
        }

        var signature = CallableSignature.FromAlgorithm(calleeName.StructuralName, callee);
        var bindingPlan = CallableBindingPlan.FromSignature(signature);

        if (bindingPlan.RequiresPatternedBinding)
        {
            var bindingsR = BindPatternedUserCall(callee, args, ctx, valEnv, calleeName, preserveArgBoundaries);
            if (bindingsR.IsError) return bindingsR.Error;

            var bindings = bindingsR.Value;
            var groupedCtx = WithUserCallBindingEnvironments(ctx, bindings, callee.Params);
            var groupedEnv = Concat(bindings.ValueBindings, valEnv);
            return ReCountValueBoundary(EvalAlgOutputCounted(callee, groupedCtx, groupedEnv));
        }

        if (IsDeconstructionUserCallShape(signature))
        {
            var bindingsR = BindDeconstructionUserCall(callee, args, ctx, valEnv, calleeName, preserveArgBoundaries);
            if (bindingsR.IsError) return bindingsR.Error;

            var bindings = bindingsR.Value;
            var deconstructionCtx = WithUserCallBindingEnvironments(ctx, bindings, callee.Params);
            var deconstructionEnv = Concat(bindings.ValueBindings, valEnv);
            return ReCountValueBoundary(EvalAlgOutputCounted(callee, deconstructionCtx, deconstructionEnv));
        }

        if (!TryGetPlanDerivedFlatFixedParameterNames(bindingPlan, out var flatFixedParams))
            flatFixedParams = callee.Params;

        var flatBindingsR = BindFlatFixedUserCallArguments(
            callee,
            calleeName,
            flatFixedParams,
            args,
            ctx,
            valEnv);
        if (flatBindingsR.IsError) return flatBindingsR.Error;

        var flatBindings = flatBindingsR.Value;
        return ReCountValueBoundary(EvalAlgOutputCounted(callee, flatBindings.Context, flatBindings.ValueEnvironment));
    }

    /// <summary>
    /// Counted dispatch for an already-resolved effective callee.
    /// </summary>
    private static EvalResult<CountedResult> EvalResolvedCallCounted(
        Algorithm callee,
        OutputBundle args,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv,
        CallDiagnosticName calleeName,
        IReadOnlyList<bool>? preserveArgBoundaries = null)
    {
        if (callee is Algorithm.Builtin(var builtinId))
        {
            var argAlgsR = ResolveArgAlgsWithSequenceSpread(args, ctx, valEnv);
            if (argAlgsR.IsError) return argAlgsR.Error;
            return ApplyBuiltinCountedResolved(builtinId, argAlgsR.Value, ctx, valEnv);
        }

        if (TryGetFlatBinderUserEquivalent(callee) is { } simpleCallee)
            return EvalUserCallCounted(
                simpleCallee,
                args,
                ctx,
                valEnv,
                preserveArgBoundaries,
                calleeName);

        if (callee is Algorithm.Conditional)
            return EvalConditionalCallCounted(callee, args, ctx, valEnv, calleeName, preserveArgBoundaries);

        return EvalUserCallCounted(
            callee,
            args,
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
        Expr target, string name, OutputBundle? argsOpt,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
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
                    return ResultToString(ctx, val.Value);
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
            return ResultToString(ctx, val.Value);
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

            return EvalResolvedCall(
                wired,
                argsOpt,
                ctx,
                valEnv,
                CallDiagnosticName.FromKnown(name));
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
    /// Sequence builtins in dot-call form evaluate the receiver to ONE value,
    /// re-counted to <c>Result.ValueCount</c>, and pass it as the ordinary
    /// fixed <c>collection</c> argument (the post-binding collection view
    /// opens it, exactly as for the plain call form).
    /// A direct inline receiver block first exposes its inner algorithm output
    /// count, which strips exactly one receiver-scoping block layer for forms
    /// like <c>(1, 2, 3).take(2)</c> while still keeping
    /// <c>((1, 2, 3)).take(2)</c> and named sequence-valued helpers intact.
    /// Any extra dot-call arguments still follow the plain-call argument path.
    /// This keeps plain-call boundary preservation unchanged while making
    /// <c>receiver.builtin(...)</c> operate on the same top-level collection
    /// that <c>receiver:i</c> and higher-order callback projection observe.
    /// </summary>
    private static EvalResult<CountedResult> EvalSequenceBuiltinDotReceiverCounted(
        Expr receiver,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        // The receiver is this builtin call's collection ARGUMENT, so it consumes
        // one depth-only argument-evaluation level exactly like the plain-call
        // spelling's argument funnel (EvalArgumentAlgOutputCounted). This keeps the
        // plain/dot work observations identical — including PeakDepth — and bounds
        // a self-referential receiver (`A = A.count`) by the same deterministic
        // depth limit instead of the machine-dependent stack backstop.
        if (ctx.Budget.TryEnterArgumentEvaluation() is { } limitError)
            return limitError;
        try
        {
            var valueR = Eval(receiver, ctx, valEnv);
            return valueR.IsError
                ? valueR.Error
                : EvalResult<CountedResult>.Ok(new CountedResult(valueR.Value, valueR.Value.ValueCount()));
        }
        finally
        {
            ctx.Budget.ExitInvocation();
        }
    }

    private static EvalResult<IReadOnlyList<ResolvedArgumentAlgorithm>> SequenceBuiltinDotReceiverArgs(
        Expr receiver,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var receiverR = EvalSequenceBuiltinDotReceiverCounted(receiver, ctx, valEnv);
        if (receiverR.IsError) return receiverR.Error;

        // The receiver has just been evaluated — exactly once — to dispatch on it. Carry
        // that counted result forward as the argument's PREPARED value only: the value
        // channel reads it directly and must never reconstruct or re-evaluate it. No
        // algorithm channel is built here — reifying the result as an expression tree
        // (CountedArgAlgorithm → ResultToExpr) costs O(receiver size), and the ordinary
        // value path (`A.count`, `A.take(2)`, `A.map(F)`) never consumes it because
        // PreparedValue short-circuits evaluation. If an algorithm-only consumer does
        // request the channel, ResolveArgumentAlgorithm / PrepareSequenceBuiltinSuffixArg
        // synthesize the legacy counted-value wrapper lazily at that point.
        return EvalResult<IReadOnlyList<ResolvedArgumentAlgorithm>>.Ok(
            [new ResolvedArgumentAlgorithm(Algorithm: null, SpreadsSequence: false)
            {
                PreparedValue = receiverR.Value,
            }]);
    }

    private static EvalResult<SequenceBuiltinDotCall?> TryBuildSequenceBuiltinDotCall(
        string name,
        Expr receiver,
        OutputBundle? extraArgs,
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
                && extraArgAlgsR.Value is [{ Algorithm: { Params.Count: > 0 } reducerAlgorithm }])
            {
                return ReduceInitialAccumulatorRequiresValueError(reducerAlgorithm);
            }

            argAlgs.AddRange(extraArgAlgsR.Value);
        }

        return EvalResult<SequenceBuiltinDotCall?>.Ok(
            new SequenceBuiltinDotCall(builtin, argAlgs));
    }

    private static bool TryGetParenthesizedSequenceSpreadReceiver(Expr receiver, out Expr spreadReceiver)
    {
        if (receiver is Expr.Capture([Expr.SequenceSpread captureSpread]))
        {
            spreadReceiver = captureSpread;
            return true;
        }

        if (receiver is Expr.AlgorithmExpr({ Opens.Count: 0, Properties.Count: 0, Params.Count: 0, Output.Count: 1 } algorithm)
            && algorithm.Output[0] is Expr.SequenceSpread sequenceSpread)
        {
            spreadReceiver = sequenceSpread;
            return true;
        }

        spreadReceiver = receiver;
        return false;
    }

    private static bool HasLeadingFlatCollectingParameter(Algorithm callee, string name)
    {
        var effectiveCallee = TryGetFlatBinderUserEquivalent(callee) ?? callee;
        if (effectiveCallee is not Algorithm.User)
            return false;

        var signature = CallableSignature.FromAlgorithm(name, effectiveCallee);
        var plan = CallableBindingPlan.FromSignature(signature);
        return plan.TryGetFlatCollectingLayout(out var prefix, out _, out _)
            && prefix.Count == 0;
    }

    private static (OutputBundle Args, IReadOnlyList<bool> PreserveArgBoundaries) BuildLexicalReceiverCallArgs(
        Algorithm callee,
        string name,
        Expr receiver,
        OutputBundle? extraArgs)
    {
        var receiverExpr = receiver;
        var hasLeadingFlatCollectingParameter = HasLeadingFlatCollectingParameter(callee, name);
        var preserveReceiverBoundary = !hasLeadingFlatCollectingParameter;
        // The injected receiver is still one leading argument segment. When a
        // leading flat collecting parameter exists, that segment may carry its
        // emitted-count metadata into the capture after slot allocation.
        // Parenthesized receiver spread, as in (Arg*).F, can feed the
        // receiver's top-level items only to leading flat collecting receiver params.
        // Fixed receiver params keep the receiver as one argument boundary.
        if (TryGetParenthesizedSequenceSpreadReceiver(receiver, out var spreadReceiver)
            && hasLeadingFlatCollectingParameter)
        {
            receiverExpr = spreadReceiver;
        }

        var outputExprs = new Expr[1 + (extraArgs?.Count ?? 0)];
        outputExprs[0] = receiverExpr;
        var preserveArgBoundaries = new List<bool> { preserveReceiverBoundary };
        if (extraArgs is not null)
        {
            for (var i = 0; i < extraArgs.Count; i++)
            {
                outputExprs[i + 1] = extraArgs[i];
                preserveArgBoundaries.Add(false);
            }
        }

        // outputExprs is this call's exclusively owned fresh array, so
        // ownership transfers without a snapshot copy.
        return (OutputBundle.TakeOwnership(outputExprs), preserveArgBoundaries);
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
        OutputBundle args,
        SourceSpan? callSpan,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var rangeR = WithSpan(
            callSpan,
            WithCallCtx(
                CallDiagnosticName.FromExpression(function),
                ctx,
                EvalBuiltinRangeCallArguments(args, ctx, valEnv)));
        if (rangeR.IsError)
            return rangeR;

        // Optimizer/generic boundary parity: a fused pipeline evaluates the range's
        // bounds and then iterates them WITHOUT materializing the list, so it must still
        // reject exactly the sizes the generic `range` builtin rejects. The check
        // consumes no cumulative budget precisely because nothing is materialized here —
        // and if the pipeline is not fused after all, the generic path reserves for real,
        // so the same range is never charged twice.
        return ctx.Budget.CheckCollectionSize(CountInclusiveRangeValues(rangeR.Value)) is { } limitError
            ? AtSpanIfMissing(limitError, callSpan)
            : rangeR;
    }

    private static EvalResult<InclusiveRange> EvalBuiltinRangeCallArguments(
        OutputBundle args,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var argAlgsR = ResolveArgAlgsWithSequenceSpread(args, ctx, valEnv);
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
        string name, Expr receiver, OutputBundle? extraArgs,
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
        return EvalResolvedCall(
            calleeR.Value,
            combinedArgs,
            ctx,
            valEnv,
            CallDiagnosticName.FromKnown(name),
            preserveArgBoundaries);
    }

    /// <summary>
    /// Counted dotCall evaluation for <c>reduce</c> step validation.
    /// Lean: <c>evalDotCallCounted</c>.
    /// </summary>
    private static EvalResult<CountedResult> EvalDotCallCounted(
        Expr target, string name, OutputBundle? argsOpt,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
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
                    var outR = ResultToString(ctx, val.Value);
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
            var outR = ResultToString(ctx, val.Value);
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

            return EvalResolvedCallCounted(
                wired,
                argsOpt,
                ctx,
                valEnv,
                CallDiagnosticName.FromKnown(name));
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
        string name, Expr receiver, OutputBundle? extraArgs,
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
        return EvalResolvedCallCounted(
            calleeR.Value,
            combinedArgs,
            ctx,
            valEnv,
            CallDiagnosticName.FromKnown(name),
            preserveArgBoundaries);
    }

    // ── Entry points ────────────────────────────────────────────────────────

    /// <summary>
    /// Run evaluation on an expression with prelude in scope.
    /// Lean: runResult → EvalM Result.
    /// <para><b>Host-AST contract:</b> the expression may be a preconstructed
    /// (host-built) AST. Every entry point first runs a non-recursive structural safety
    /// preflight: a tree whose weighted structural depth exceeds
    /// <see cref="EvaluationLimits.MaxAstDepth"/> (bounded by
    /// <see cref="EvaluationLimits.MaxSupportedAstDepth"/>) is rejected with
    /// <see cref="EvalError.AstDepthLimitExceeded"/>, and a cyclic node graph with
    /// <see cref="EvalError.AstCycleDetected"/>, before any recursive validation,
    /// optimization, or evaluation can overflow the CLR stack. Programs accepted by
    /// the elaborating public parser stay within the hard ceiling; a raw syntax tree
    /// from <c>Parser.ParseSyntax</c> may validly fall between that API's larger raw
    /// gate and this evaluation gate and is rejected here.</para>
    /// <para><b>Pre-evaluation validation:</b> after the structural preflight, the
    /// validation pass Lean's <c>runResultM</c> runs before evaluation is applied to
    /// the whole tree: an algorithm with explicit parameters but no output is rejected
    /// with <see cref="EvalError.ExplicitParametersRequireOutput"/>, and a conditional
    /// whose branches disagree on top-level pattern arity or top-level output arity is
    /// rejected with <see cref="EvalError.BranchArityMismatch"/> /
    /// <see cref="EvalError.BranchOutputArityMismatch"/> before any branch matching or
    /// evaluation — even when the malformed conditional is never referenced. Parsed
    /// surface programs never contain such conditionals (clause elaboration rejects
    /// them with source-positioned diagnostics); this gate aligns hand-built ASTs with
    /// Lean's <c>runResult</c>.</para>
    /// <para><b>Supported execution environment:</b> the structural safety envelope
    /// is calibrated for threads with at least 1 MiB of stack (the CLR/Windows
    /// default). Embedders running evaluation on smaller custom stacks are outside
    /// the documented envelope and should lower
    /// <see cref="EvaluationLimits.MaxAstDepth"/> accordingly.</para>
    /// </summary>
    public static EvalResult<Result> Run(Expr expr)
        => Run(expr, limits: null);

    /// <summary>
    /// Run evaluation under explicit resource limits.
    /// <para>The no-limits overloads are NOT unbounded: they use
    /// <see cref="EvaluationLimits.Default"/>, so the hard depth, collection, and string
    /// ceilings are enforced on every public evaluator entry point, exactly as through
    /// <see cref="KatLangEngine"/>. Step and cumulative materialization budgets are opt-in;
    /// display is a host-rendering policy applied by <see cref="RunResult"/>.</para>
    /// </summary>
    public static EvalResult<Result> Run(Expr expr, EvaluationLimits? limits)
        => Run(expr, new RunScopedZeroArgPropertyResultCache(), limits);

    internal static EvalResult<Result> Run(
        Expr expr,
        IZeroArgPropertyResultCache zeroArgPropertyResultCache,
        EvaluationLimits? limits = null)
        => Run(expr, zeroArgPropertyResultCache, enableLoopOptimization: true, limits);

    /// <summary>
    /// Builds the root evaluation context for one run, including its fresh
    /// <see cref="EvaluationBudget"/>.
    ///
    /// <para>A configured step budget must mean the same thing no matter which internal
    /// execution strategy runs. The optimized loop and sequence-pipeline paths collapse
    /// many generic evaluator operations into specialized routines, so their internal
    /// operation counts do not match the generic paths. A budgeted run therefore always
    /// takes the generic paths and charges exactly the generic units; an unbudgeted run
    /// keeps every optimization. This is optimizer independence by construction rather
    /// than by parallel accounting.</para>
    /// </summary>
    private static EvalCtx CreateRootCtx(
        IZeroArgPropertyResultCache zeroArgPropertyResultCache,
        bool enableLoopOptimization,
        LoopOptimizationDiagnostics? loopDiagnostics,
        bool enableSequencePipelineOptimization,
        SequencePipelineDiagnostics? sequenceDiagnostics,
        EvaluationLimits? limits,
        EvaluationObservations? observations = null)
        => CreateRootCtx(
            zeroArgPropertyResultCache,
            enableLoopOptimization,
            loopDiagnostics,
            enableSequencePipelineOptimization,
            sequenceDiagnostics,
            EvaluationBudget.Create(limits),
            observations);

    private static EvalCtx CreateRootCtx(
        IZeroArgPropertyResultCache zeroArgPropertyResultCache,
        bool enableLoopOptimization,
        LoopOptimizationDiagnostics? loopDiagnostics,
        bool enableSequencePipelineOptimization,
        SequencePipelineDiagnostics? sequenceDiagnostics,
        EvaluationBudget budget,
        EvaluationObservations? observations = null)
    {
        var loopOptimize = !budget.HasStepLimit;
        var sequenceOptimize = loopOptimize && !budget.HasConfiguredStringLimit;
        return new EvalCtx(
            [PreludeAlg],
            [],
            [],
            zeroArgPropertyResultCache,
            new RunScopedDeconstructionBindingCache(),
            enableLoopOptimization && loopOptimize,
            loopDiagnostics,
            enableSequencePipelineOptimization && sequenceOptimize,
            sequenceDiagnostics,
            observations,
            budget);
    }

    internal static EvalResult<Result> Run(
        Expr expr,
        IZeroArgPropertyResultCache zeroArgPropertyResultCache,
        bool enableLoopOptimization,
        EvaluationLimits? limits = null)
        => Run(expr, zeroArgPropertyResultCache, enableLoopOptimization, loopDiagnostics: null, limits);

    internal static EvalResult<Result> Run(
        Expr expr,
        IZeroArgPropertyResultCache zeroArgPropertyResultCache,
        bool enableLoopOptimization,
        LoopOptimizationDiagnostics? loopDiagnostics,
        EvaluationLimits? limits = null)
        => Run(
            expr,
            zeroArgPropertyResultCache,
            enableLoopOptimization,
            loopDiagnostics,
            enableSequencePipelineOptimization: true,
            sequenceDiagnostics: null,
            limits);

    /// <summary>
    /// Non-recursive structural safety preflight shared by every evaluator entry point
    /// that accepts a preconstructed AST. It MUST run before
    /// <see cref="AlgorithmValidation.FindFirstPreEvaluationViolation(Expr)"/>
    /// and before any other recursive pass (validation walk, optimizer planning,
    /// evaluation): those consume the tree on the CLR stack, so a host-built tree
    /// deeper than the structural limit would otherwise terminate the process with an
    /// unhandleable <see cref="StackOverflowException"/>. Returns <c>null</c> for safe
    /// trees; runs before any budget exists and charges nothing to evaluation budgets.
    /// </summary>
    private static EvalError? StructuralPreflight(Expr expr, EvaluationLimits? limits)
    {
        var effectiveLimit = (limits ?? EvaluationLimits.Default).EffectiveMaxAstDepth;
        return AstStructuralPreflight.Check(
                expr, effectiveLimit, AstConsumerProfile.EvaluatorIterativeJoinSpines) is { } rejection
            ? AstStructuralPreflight.ToEvalError(rejection, effectiveLimit)
            : null;
    }

    /// <summary>
    /// Shared pre-evaluation validation gate for every prebuilt-AST entry point.
    /// Lean: the validation pass <c>runResultM</c> runs before any evaluation
    /// (<c>validateExplicitParamOutputInvariantExpr</c>). The violation kinds map
    /// 1:1 onto Lean's validation errors, so a malformed hand-built tree — for
    /// example a conditional with mismatched branch arities — is rejected here,
    /// before branch matching, optimizer planning, or any evaluation, exactly
    /// where Lean rejects it. Runs after <see cref="StructuralPreflight"/> because
    /// the validation walk itself is recursive.
    /// </summary>
    private static EvalError? PreEvaluationValidationError(Expr expr)
        => AlgorithmValidation.FindFirstPreEvaluationViolation(expr) switch
        {
            null => null,
            PreEvaluationAstViolation.ExplicitParametersWithoutOutput v =>
                new EvalError.ExplicitParametersRequireOutput() { Span = v.Span },
            PreEvaluationAstViolation.ConditionalBranchArityMismatch v =>
                new EvalError.BranchArityMismatch(v.AlgorithmName, v.Expected, v.Actual),
            PreEvaluationAstViolation.ConditionalBranchOutputArityMismatch v =>
                new EvalError.BranchOutputArityMismatch(v.AlgorithmName, v.Expected, v.Actual),
            var unknown => throw new InvalidOperationException(
                $"Unhandled pre-evaluation violation kind: {unknown.GetType().Name}"),
        };

    internal static EvalResult<Result> Run(
        Expr expr,
        IZeroArgPropertyResultCache zeroArgPropertyResultCache,
        bool enableLoopOptimization,
        LoopOptimizationDiagnostics? loopDiagnostics,
        bool enableSequencePipelineOptimization,
        SequencePipelineDiagnostics? sequenceDiagnostics,
        EvaluationLimits? limits = null,
        EvaluationObservations? observations = null)
    {
        if (StructuralPreflight(expr, limits) is { } structuralError)
            return structuralError;

        if (PreEvaluationValidationError(expr) is { } validationError)
            return validationError;

        ArgumentNullException.ThrowIfNull(zeroArgPropertyResultCache);

        var ctx = CreateRootCtx(
            zeroArgPropertyResultCache,
            enableLoopOptimization,
            loopDiagnostics,
            enableSequencePipelineOptimization,
            sequenceDiagnostics,
            limits,
            observations);
        return expr is Expr.AlgorithmExpr(var alg)
            ? EvalRootProgram(alg, expr.Span, ctx)
            : Eval(expr, ctx, []);
    }

    /// <summary>
    /// Non-counted harness entry point with the same passive, run-scoped observations as
    /// <see cref="RunCountedObserved"/>. It exists only to prove implementation-path properties;
    /// ordinary evaluation creates no observation object.
    /// </summary>
    internal static EvalResult<Result> RunObserved(
        Expr expr,
        EvaluationObservations observations,
        bool enableOptimizations = true,
        EvaluationLimits? limits = null)
        => Run(
            expr,
            new RunScopedZeroArgPropertyResultCache(),
            enableLoopOptimization: enableOptimizations,
            loopDiagnostics: null,
            enableSequencePipelineOptimization: enableOptimizations,
            sequenceDiagnostics: null,
            limits,
            observations);

    internal static EvalResult<CountedResult> RunCounted(Expr expr)
        => RunCounted(expr, new RunScopedZeroArgPropertyResultCache());

    /// <summary>
    /// Harness entry point: evaluates exactly like <see cref="RunCounted(Expr, IZeroArgPropertyResultCache, EvaluationLimits?)"/>
    /// and additionally hands back the run's <see cref="EvaluationBudget"/> so a test can
    /// read the OPERATIONAL counters this run actually charged (steps, materialized item
    /// slots and string units, peak dynamic depth).
    ///
    /// <para>The budget is created here and belongs to this run alone — no static state,
    /// nothing shared between runs — and it is the same object the evaluator charged, so
    /// observing it neither re-evaluates anything nor changes optimizer eligibility. These
    /// counters are C# implementation observations: they may be compared between C#
    /// executions, never against Lean.</para>
    ///
    /// <para>The optional <paramref name="loopDiagnostics"/> and
    /// <paramref name="sequenceDiagnostics"/> collectors are the SAME channel the internal
    /// <see cref="Run(Expr, IZeroArgPropertyResultCache, bool, LoopOptimizationDiagnostics?, bool, SequencePipelineDiagnostics?, EvaluationLimits?)"/>
    /// overload already exposes, so an observed run can additionally record which execution
    /// path the optimizers actually took (planned, fused, fallen back, or generic). They are
    /// write-only counters the evaluator increments through a null-conditional call: supplying
    /// one cannot change optimizer eligibility, evaluation order, or any result.</para>
    /// </summary>
    internal static (EvalResult<CountedResult> Result, EvaluationBudget Budget) RunCountedObserved(
        Expr expr,
        EvaluationLimits? limits = null,
        bool enableOptimizations = true,
        IZeroArgPropertyResultCache? zeroArgPropertyResultCache = null,
        LoopOptimizationDiagnostics? loopDiagnostics = null,
        SequencePipelineDiagnostics? sequenceDiagnostics = null,
        EvaluationObservations? observations = null)
    {
        var budget = EvaluationBudget.Create(limits);
        if (StructuralPreflight(expr, limits) is { } structuralError)
            return (structuralError, budget);

        if (PreEvaluationValidationError(expr) is { } validationError)
            return (validationError, budget);

        var ctx = CreateRootCtx(
            zeroArgPropertyResultCache ?? new RunScopedZeroArgPropertyResultCache(),
            enableLoopOptimization: enableOptimizations,
            loopDiagnostics: loopDiagnostics,
            enableSequencePipelineOptimization: enableOptimizations,
            sequenceDiagnostics: sequenceDiagnostics,
            budget,
            observations);

        var result = expr is Expr.AlgorithmExpr(var alg)
            ? EvalRootProgramCounted(alg, expr.Span, ctx)
            : EvalCounted(expr, ctx, []);
        return (result, budget);
    }

    internal static EvalResult<CountedResult> RunCounted(
        Expr expr,
        IZeroArgPropertyResultCache zeroArgPropertyResultCache,
        EvaluationLimits? limits = null)
    {
        if (StructuralPreflight(expr, limits) is { } structuralError)
            return structuralError;

        if (PreEvaluationValidationError(expr) is { } validationError)
            return validationError;

        ArgumentNullException.ThrowIfNull(zeroArgPropertyResultCache);

        var ctx = CreateRootCtx(
            zeroArgPropertyResultCache,
            enableLoopOptimization: true,
            loopDiagnostics: null,
            enableSequencePipelineOptimization: true,
            sequenceDiagnostics: null,
            limits);
        return expr is Expr.AlgorithmExpr(var alg)
            ? EvalRootProgramCounted(alg, expr.Span, ctx)
            : EvalCounted(expr, ctx, []);
    }

    internal static EvalResult<CountedRootProgramResult> RunCountedWithTopLevelProperty(
        Expr expr,
        string topLevelPropertyName,
        IZeroArgPropertyResultCache zeroArgPropertyResultCache,
        EvaluationLimits? limits = null)
    {
        if (StructuralPreflight(expr, limits) is { } structuralError)
            return structuralError;

        if (PreEvaluationValidationError(expr) is { } validationError)
            return validationError;

        ArgumentNullException.ThrowIfNull(zeroArgPropertyResultCache);
        ArgumentException.ThrowIfNullOrWhiteSpace(topLevelPropertyName);

        var ctx = CreateRootCtx(
            zeroArgPropertyResultCache,
            enableLoopOptimization: true,
            loopDiagnostics: null,
            enableSequencePipelineOptimization: true,
            sequenceDiagnostics: null,
            limits);

        if (expr is Expr.AlgorithmExpr(var alg))
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
        => RunFlat(expr, limits: null);

    /// <summary>Host-boundary flattening run under explicit resource limits.</summary>
    public static EvalResult<IReadOnlyList<decimal>> RunFlat(Expr expr, EvaluationLimits? limits)
    {
        var r = Run(expr, limits);
        if (r.IsError) return r.Error;

        // Same rule as the engine: the host projection is bounded, so a successful
        // evaluation cannot be followed by an unbounded flattening allocation.
        var limit = (limits ?? EvaluationLimits.Default).EffectiveMaxCollectionItems;
        return r.Value.TryToHostAtoms(limit, out var atoms)
            ? EvalResult<IReadOnlyList<decimal>>.Ok(atoms)
            : new EvalError.CollectionSizeLimitExceeded(limit, limit + 1L);
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
