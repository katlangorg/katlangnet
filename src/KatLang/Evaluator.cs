using System.Collections;
using System.Numerics;
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
public static partial class Evaluator
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
    /// A binding may additionally retain a resource-limit failure from its eager value
    /// channel; that failure is observed only if the parameter is demanded as a value.
    /// Budget is the run-scoped resource budget: it is a REFERENCE deliberately carried
    /// by this copied struct, so every derived context charges the same run's counters
    /// and no copy can reset them.
    /// Lean: structure EvalCtx where callStack : List Algorithm; algEnv : AlgEnv := [].
    /// </summary>
    internal readonly record struct EvalCtx(
        IReadOnlyList<Algorithm> CallStack,
        IReadOnlyList<(string Name, Algorithm Value, EvalError? ValueError)> AlgEnv,
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
        public EvalCtx WithAlgEnv(IReadOnlyList<(string Name, Algorithm Value, EvalError? ValueError)> algEnv)
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

    /// <summary>
    /// Lexical-scope identity of the caller that resolves an assignment-deconstruction group's
    /// hoisted <c>$deconstruct$</c> source, used to key the shared-bind cache. Returns a
    /// never-matching token when the call stack is empty: no evaluator run reaches that state
    /// (the root context always carries the prelude), so the defensive path gives up reuse
    /// rather than risking an alias.
    /// </summary>
    private static object DeconstructionOwnerIdentity(EvalCtx ctx)
        => ctx.Head is { } caller
            ? StructuralOwnerIdentity.FromOwner(caller)
            : new object();

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

    /// <summary>
    /// Native-wrapper argument lookup, shared by Math-member natives and host
    /// operations. A wrapper body's argument names are the wrapper's own bound
    /// parameters, which live in the counted callback-parameter environment when
    /// the wrapper was invoked through the flat-callback/loop-step funnel and in
    /// the value environment on direct calls. Counted-first with value fallback is
    /// the <see cref="Expr.Param"/> dual-view order (minus the algorithm-binding
    /// tier — native arguments are always value bindings), so a native callback
    /// reads its actual bound argument and can never capture a same-named ambient
    /// caller value instead. Direct calls are unaffected: flat fixed binding
    /// shadows the callee's parameter names out of the caller's counted
    /// environment before the body evaluates.
    /// </summary>
    private static Result? LookupNativeArgument(
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv,
        string name)
    {
        var counted = LookupCountedParam(ctx.CountedParamEnv, name);
        if (counted is not null)
            return counted.Value.Value;
        return LookupVal(valEnv, name);
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

    private static (Algorithm Algorithm, EvalError? ValueError)? LookupAlgBinding(
        IReadOnlyList<(string Name, Algorithm Value, EvalError? ValueError)> env,
        string name)
    {
        foreach (var (n, algorithm, valueError) in env)
            if (n == name) return (algorithm, valueError);
        return null;
    }

    /// <summary>Algorithm environment: maps parameter names to algorithms. Lean: AlgEnv.lookup.</summary>
    private static Algorithm? LookupAlg(
        IReadOnlyList<(string Name, Algorithm Value, EvalError? ValueError)> env,
        string name)
        => LookupAlgBinding(env, name) is { } binding ? binding.Algorithm : null;

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

    /// <summary>Lean: Algorithm.lookupPropDefPublic? (public only).</summary>
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
    /// The ONE dedup identity of a written <c>open</c> target, owned here beside
    /// <see cref="OpenExprName"/> and shared by runtime open resolution
    /// (<see cref="ResolveAllOpens"/>) and elaborated-scope lookup
    /// (<c>ElaboratedPropertyScope.GetResolvedOpenProviders</c>), so both views
    /// deduplicate targets by the same relation. An INLINE target
    /// (<see cref="Expr.AlgorithmExpr"/> or <see cref="Expr.Capture"/>) is keyed by
    /// its written position, so two structurally identical inline blocks are never
    /// merged. Every other target — a named resolve, a dotted path, and on the
    /// tolerant host/recovery paths any other expression — is keyed by its rendered
    /// open spelling, so repeating one spelling is ONE provider (first occurrence
    /// wins; consumers compare keys ordinally). The generic arm is deliberate and
    /// must stay total: <see cref="ResolveAllOpens"/> spells an illegal target's
    /// <c>BadOpenForm</c> diagnostic with this key, and the key is also the open's
    /// diagnostic context and ambiguity-provider spelling. A new inline-like open
    /// form must be added to the positional arm here — nowhere else.
    /// Lean: <c>resolveAllOpens</c>.
    /// </summary>
    internal static string OpenTargetDedupKey(Expr openExpr, int index)
        => openExpr is Expr.AlgorithmExpr or Expr.Capture
            ? $"(inline#{index})"
            : OpenExprName(openExpr);

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
    /// <see cref="WithCtx{T}(ErrorContext, EvalResult{T})"/> for one iterated filter item,
    /// with the context CONSTRUCTED ONLY ON THE ERROR PATH (see <see cref="WithCallCtx{T}"/>).
    ///
    /// <para>This runs once per iterated item, and rendering the item is path-proportional on
    /// a shared value graph, so eagerly interpolating the message charged every PASSING
    /// predicate for a diagnostic nothing would ever read.</para>
    /// </summary>
    private static EvalResult<T> WithFilterItemCtx<T>(Result item, int index, EvalCtx ctx, EvalResult<T> result)
        => result.IsError && !result.Error.IsResourceLimit
            ? new EvalError.WithContext(FilterPredicateItemContext(item, index, ctx.Observations), result.Error) { Span = result.Error.Span }
            : result;

    private static ErrorContext FilterPredicateItemContext(
        Result item,
        int index,
        EvaluationObservations? observations)
    {
        observations?.RecordFilterItemDiagnosticContext();
        return new TextErrorContext(
            $"while evaluating filter predicate for item {index}: {FormatResultForDiagnostic(item)} (filter passes each iterated collection item as collected; a collecting parameter collects supplied values as one exact list and nested sequence and list values stay intact)");
    }

    /// <summary>
    /// <see cref="WithCtx{T}(ErrorContext, EvalResult{T})"/> for dot-call contexts,
    /// with the context constructed only on the error path (see
    /// <see cref="WithCallCtx{T}"/>).
    /// </summary>
    private static EvalResult<T> WithDotCallCtx<T>(Expr.DotCall dotCall, EvalCtx ctx, EvalResult<T> result)
        => result.IsError && !result.Error.IsResourceLimit
            ? new EvalError.WithContext(
                CtxDotCall(dotCall.Target, dotCall.Name, ctx),
                result.Error)
            { Span = result.Error.Span }
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

    private static EvalResult<T> MissingImplicitArguments<T>(Algorithm wired, SourceSpan? span)
    {
        var paramNames = wired.Params;
        var inner = new EvalError.UnresolvedImplicitParams(paramNames)
        {
            Span = span,
            InferredImplicitParameters = ImplicitParameterProvenance.CollectFrom(wired.Parameters),
        };
        return new EvalError.WithContext(new ImplicitParameterContext(paramNames, 0), inner) { Span = span };
    }

    /// <summary>
    /// The arity mismatch for a zero-argument value demand of a parametered
    /// callable, carrying the callee's inferred-implicit-parameter provenance
    /// as diagnostic-only notes so the eventual message can point back at the
    /// unresolved identifiers the parameters came from (see
    /// <see cref="ImplicitParameterProvenance"/>). Identical to the plain
    /// mismatch for callees with no inferred parameters.
    /// </summary>
    private static EvalError.ArityMismatch ZeroArgumentDemandArityMismatch(Algorithm callee)
        => new(callee.Params.Count, 0)
        {
            InferredImplicitParameters = ImplicitParameterProvenance.CollectFrom(callee.Parameters),
        };

    /// <summary>
    /// Adds diagnostic-only inferred-parameter provenance to the terminal
    /// arity mismatch of an already-selected callee. Callback/pattern binders
    /// may wrap that mismatch in a precise binding context, so preserve the
    /// context chain and enrich only the existing terminal error kind.
    /// </summary>
    private static EvalError AttachImplicitParameterProvenance(EvalError error, Algorithm callee)
    {
        var notes = ImplicitParameterProvenance.CollectFrom(callee.Parameters);
        if (notes is null)
            return error;

        return error switch
        {
            EvalError.ArityMismatch arity => arity with
            {
                InferredImplicitParameters = notes,
            },
            EvalError.WithContext context => new EvalError.WithContext(
                context.ErrorContext,
                AttachImplicitParameterProvenance(context.Inner, callee))
            {
                Span = context.Span,
            },
            _ => error,
        };
    }

    /// <summary>Returns the <see cref="SourceSpan"/> of the first output expression that has one.</summary>
    private static SourceSpan? FirstSpan(IReadOnlyList<Expr> output)
    {
        foreach (var e in output)
            if (e.Span is { } s) return s;
        return null;
    }

    internal static SourceSpan? PreferExpressionSpan(
        SourceSpan? expressionSpan,
        IReadOnlyList<Expr> output)
        => expressionSpan ?? FirstSpan(output);

    // ── Lexical lookup (direct — no opens, used for open resolution) ────────

    /// <summary>
    /// Lean: lookupInParentsDirect (Option). Iterative over the parent chain: scope
    /// chains grow with structural nesting, and resolving a name from the deepest
    /// evaluation frame must not add another O(chain) recursive burst on top of the
    /// already-deep host stack.
    /// </summary>
    private static Algorithm? LookupInParentsDirect(ScopeCtx sc, string name)
    {
        for (ScopeCtx? current = sc; current is not null; current = current.Parent)
        {
            foreach (var prop in current.Properties)
            {
                if (prop.Name == name)
                    return WithParent(prop.Value, current);
            }
        }

        return null;
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
    /// Deduplicates targets by the shared <see cref="OpenTargetDedupKey"/> (named
    /// targets by their open spelling, first occurrence wins; inline blocks by
    /// position, never deduplicated) to avoid repeated resolution and spurious
    /// ambiguity from duplicate opens.
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
            var key = OpenTargetDedupKey(openExpr, i);
            if (seen.Add(key))
                deduped.Add((key, openExpr));
        }

        // Validate all open expressions first (fail-fast with clear errors)
        foreach (var (key, openExpr) in deduped)
        {
            if (!openExpr.IsCoreOpenForm())
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

    // Iterative over the parent chain for the same reason as LookupInParentsDirect:
    // no O(chain) recursion on top of the deepest evaluation stack.
    private static ResolvedLexicalProperty? LookupInParentsDirectBinding(ScopeCtx sc, string name)
    {
        for (ScopeCtx? current = sc; current is not null; current = current.Parent)
        {
            foreach (var prop in current.Properties)
            {
                if (prop.Name == name)
                {
                    return new ResolvedLexicalProperty(
                        TryGetScopeOwnerAlgorithm(current),
                        prop,
                        WithParent(prop.Value, current));
                }
            }
        }

        return null;
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
    /// Algorithm-position lexical lookup (call callees, dot-call targets).
    /// This is the algorithm PROJECTION of <see cref="LookupLexical"/>: the
    /// canonical binding-carrying chain owns ownership-first ordering, open
    /// dedup, public-only filtering, ambiguity, and precedence, and this
    /// projection only discards the owner/binding metadata that
    /// algorithm-position consumers never read — mirroring Lean, where
    /// <c>lookupLexical</c> projects <c>lookupLexicalProperty</c>.
    /// Lean: lookupLexical.
    /// </summary>
    private static EvalResult<Algorithm> LookupLexicalResolvedAlgorithm(
        Algorithm alg, string name, EvalCtx ctx)
    {
        var result = LookupLexical(alg, name, ctx);
        return result.IsError
            ? result.Error
            : EvalResult<Algorithm>.Ok(result.Value.ResolvedAlgorithm);
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

    /// <summary>Coerce a Result to a number, or raise TypeMismatch for strings, BadArity otherwise. Lean: expectInt.</summary>
    internal static EvalResult<Decimal128> ExpectInt(Result r)
    {
        if (r is Result.Str)
            return new EvalError.TypeMismatch("Expected a number, got a string");
        var v = r.AsNum();
        return v is not null
            ? EvalResult<Decimal128>.Ok(v.Value)
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

    private static EvalResult<Decimal128> RequireNumericScalarOperand(BinaryOp op, string side, Result value)
    {
        var number = value.AsNum();
        return number is not null
            ? EvalResult<Decimal128>.Ok(number.Value)
            : new EvalError.TypeMismatch(NumericScalarOperandMessage(ExprNameRenderer.BinaryOpText(op), side, value));
    }

    private static string NumericScalarOperandMessage(string operatorName, string side, Result value)
        => $"operator `{operatorName}` expects numeric scalar operands, but the {side} operand was {DescribeNumericScalarOperand(value)}";

    private static string DescribeNumericScalarOperand(Result value) => value switch
    {
        Result.SequenceValue(var items) => $"a sequence value with {items.Count} {Pluralize(items.Count, "sequence element")}: {FormatResultForDiagnostic(value)}",
        Result.Str => $"a string: {FormatResultForDiagnostic(value)}",
        Result.Atom(var number) => $"numeric value {number.ToString(System.Globalization.CultureInfo.InvariantCulture)}",
        Result.ListValue(var items) => $"a list value with {items.Count} {Pluralize(items.Count, "element")}: {FormatResultForDiagnostic(value)}",
        _ => $"a value: {FormatResultForDiagnostic(value)}",
    };

    private static string Pluralize(int count, string singular)
        => count == 1 ? singular : singular + "s";

    /// <summary>
    /// Renders one value as the bounded fragment a diagnostic quotes it by.
    ///
    /// <para>A value is a DAG, so this rendering is PATH-proportional by semantics — every
    /// occurrence is spelled out, and repeated occurrences stay repeated occurrences — which
    /// on a shared graph an ordinary in-budget loop builds is exponential in the graph's
    /// size. <see cref="Rendering.DiagnosticValueRenderer"/> therefore bounds the fragment
    /// DURING construction and abandons the walk once no further visible text can be
    /// emitted; values that fit the bound render exactly as before. Callers embed the result
    /// in a message, so the enclosing text is not itself bounded by this cap.</para>
    /// </summary>
    internal static string FormatResultForDiagnostic(Result value)
        => Rendering.DiagnosticValueRenderer.Render(value);

    /// <summary>
    /// Require an exact integer-valued number for integer-only builtins.
    /// Lean's core uses <c>Int</c> directly, while the C# runtime allows fractional
    /// numbers and must reject them explicitly. <see cref="Decimal128.IsInteger"/> is
    /// false for NaN and the infinities, so non-finite values are rejected here too.
    /// </summary>
    private static EvalResult<Decimal128> ExpectWholeInt(Result r, string description)
    {
        var valueR = ExpectInt(r);
        if (valueR.IsError) return valueR.Error;
        if (!Decimal128.IsInteger(valueR.Value))
            return new EvalError.IllegalInEval($"{description} must be an integer");
        return valueR;
    }

    /// <summary>
    /// Evaluate and validate the arguments for <c>range(start, stop)</c>.
    /// This is the single range-boundary validation path used by both the
    /// builtin and sequence-pipeline direct range iteration; the async twin
    /// shares <see cref="ValidateRangeBound"/> so the safety policy cannot
    /// drift between execution paths.
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
        var startIntR = ValidateRangeBound(startR.Value, "range start");
        if (startIntR.IsError) return startIntR.Error;

        var stopR = EvalResolvedArgument(args[1], ctx, valEnv);
        if (stopR.IsError) return stopR.Error;
        var stopIntR = ValidateRangeBound(stopR.Value, "range stop");
        if (stopIntR.IsError) return stopIntR.Error;

        return EvalResult<InclusiveRange>.Ok(new InclusiveRange(startIntR.Value, stopIntR.Value));
    }

    /// <summary>
    /// The ONE range-bound safety policy, shared by every execution path that
    /// builds an <see cref="InclusiveRange"/> (synchronous evaluation, the async
    /// twin, and — through the synchronous entry — sequence-pipeline direct range
    /// iteration): a bound must be an exact integer whose magnitude does not
    /// exceed <see cref="MaxExactRangeBound"/>, because beyond 1e34 a unit step
    /// is absorbed (<c>x + 1 == x</c>) and enumeration could never advance while
    /// the computed cardinality still looked small enough to pass collection
    /// limits. Pure over the already-evaluated bound value, so no path can
    /// re-implement (and drift from) the policy.
    /// </summary>
    private static EvalResult<Decimal128> ValidateRangeBound(Result value, string description)
    {
        var wholeR = ExpectWholeInt(value, description);
        if (wholeR.IsError) return wholeR.Error;
        if (Decimal128.Abs(wholeR.Value) > MaxExactRangeBound)
            return new EvalError.IllegalInEval($"{description} must not exceed 1e34 in magnitude");
        return wholeR;
    }

    /// <summary>
    /// Largest magnitude a <c>range</c> or <c>Math.RandomInt</c> bound may have:
    /// every integer in <c>[-1e34, 1e34]</c> is exactly representable in
    /// <see cref="Decimal128"/> and stepping by one is exact throughout, so bounded
    /// enumeration stays total and faithful and uniform integer sampling is
    /// well-defined. Beyond 1e34 consecutive integers are no longer representable —
    /// adding one would be absorbed and a cursor could never advance. Exactly
    /// ±1e34 is safe as an endpoint because enumeration never steps outward past
    /// the endpoint it just yielded.
    /// </summary>
    private static readonly Decimal128 MaxExactRangeBound = Decimal128.ScaleB(Decimal128.One, 34);

    /// <summary>
    /// Enumerate the validated inclusive integer bounds for <c>range(start, stop)</c>.
    /// The inclusive-bound check runs BEFORE the step, never after: bounds are whole
    /// numbers within <see cref="MaxExactRangeBound"/>, so every step is exact, the
    /// cursor lands exactly on <c>Stop</c>, and the enumeration is total. A step that
    /// fails to advance (unit-step absorption above 1e34) means a caller bypassed
    /// <see cref="ValidateRangeBound"/>; that is an internal invariant violation and
    /// fails loud rather than looping forever — the same discipline as the budget
    /// underflow guards.
    /// </summary>
    internal static IEnumerable<Decimal128> EnumerateInclusiveRangeValues(InclusiveRange range)
    {
        if (range.Start <= range.Stop)
        {
            var current = range.Start;
            yield return current;
            while (current < range.Stop)
            {
                var next = current + Decimal128.One;
                if (next == current)
                    throw UnvalidatedRangeBoundInvariantViolation(current);
                current = next;
                yield return current;
            }
        }
        else
        {
            var current = range.Start;
            yield return current;
            while (current > range.Stop)
            {
                var next = current - Decimal128.One;
                if (next == current)
                    throw UnvalidatedRangeBoundInvariantViolation(current);
                current = next;
                yield return current;
            }
        }
    }

    private static InvalidOperationException UnvalidatedRangeBoundInvariantViolation(Decimal128 cursor)
        => new(
            $"range enumeration cannot advance from {cursor.ToString(System.Globalization.CultureInfo.InvariantCulture)}: "
            + "a unit step was absorbed, so the bounds bypassed ValidateRangeBound. "
            + "Every InclusiveRange producer must validate bounds through that shared policy.");

    /// <summary>
    /// Count the values that <see cref="EnumerateInclusiveRangeValues"/> would produce,
    /// saturating at <see cref="long.MaxValue"/>. Bounds are validated to at most 1e34
    /// in magnitude, so the span (at most 2e34) is always exactly representable.
    /// </summary>
    internal static long CountInclusiveRangeValues(InclusiveRange range)
    {
        var lo = Decimal128.Min(range.Start, range.Stop);
        var hi = Decimal128.Max(range.Start, range.Stop);
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

    // ── Built-in prelude ────────────────────────────────────────────────────

    private static readonly Algorithm.User MathAlgorithm = BuiltinRegistry.CreateMathAlgorithm(MathAlgorithmFlavor.Runtime);

    /// <summary>
    /// Prelude algorithm providing builtin operations in scope by default.
    /// Lean: preludeAlg. Builtins are injected into the initial call stack.
    /// All builtins, Math, and the lower-camel-case Math member aliases
    /// (`pi`, `sin`, ... — synthetic properties sharing the canonical member
    /// algorithm instances) are public for use in opened contexts.
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

            case Expr.DotCall openDotCall when openDotCall.IsCoreOpenForm():
                return WithSpan(expr.Span, ResolveOpenPropAccess(openDotCall.Target, openDotCall.Name, ctx));

            default:
                // Not an open form — reject with informative error. The
                // front end separately rejects Grace-marked targets such as
                // `open A~.B`; no Grace metadata reaches runtime.
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
        if (targetResult.Value.DefinesConditionalBranchProperty(propName))
            return new EvalError.LocalOnlyProperty(OpenExprName(target), propName, PropertyExposure.LocalOnlyConditionalAlgorithm);

        return new EvalError.UnknownProperty(OpenExprName(target), propName);
    }

    // ── Algorithm resolution (full — with opens) ─────────────────────────────

    /// <summary>
    /// Resolves the canonical qualified spelling of a runtime Math FUNCTION
    /// (<c>Math.Abs</c>, <c>Math.Pow</c>, ...) to the same native wrapper algorithm
    /// shared by its lowercase alias and an opened canonical name. General
    /// argumentless dot calls keep their ordinary zero-parameter thunk identity;
    /// this exception is gated both by authoritative Math metadata and by the
    /// resolved member's actual <see cref="Expr.NativeCall"/> body, so a user-defined
    /// property named <c>Math</c> is not reinterpreted as the prelude module.
    /// </summary>
    private static Algorithm? TryResolveQualifiedMathNativeReference(
        Expr.DotCall dotCall,
        EvalCtx ctx)
    {
        // The shape gate is the ONE canonical-Math-member classification
        // (AstHelpers); it is binding-neutral here because binding is established
        // below by resolving the receiver itself and verifying the resolved
        // member's actual native body, not by a static shadow predicate.
        if (!dotCall.TryGetRegistryProvenCanonicalMathFacts(isPreludeNameShadowed: null, out _))
            return null;

        var targetR = ResolveAlg(dotCall.Target, ctx);
        if (targetR.IsError)
            return null;

        var memberName = dotCall.Name;
        var binding = LookupPropBinding(targetR.Value, memberName);
        if (binding is null || !IsExported(binding))
            return null;

        var candidate = ChildOf(targetR.Value, binding.Value);
        if (candidate.Output.Count != 1
            || candidate.Output[0] is not Expr.NativeCall(var nativeName, var argNames)
            || !string.Equals(nativeName, memberName, StringComparison.Ordinal)
            || !candidate.Params.SequenceEqual(argNames, StringComparer.Ordinal))
        {
            return null;
        }

        return candidate;
    }

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

            case Expr.DotCall { Args: var dotArgs } dotCall:
                {
                    // Math functions have one canonical callable identity across
                    // `Math.X`, opened `X`, and the predefined alias. In algorithm
                    // position, return the verified native wrapper itself so the
                    // callback/loop binder can bind its declared parameters. The
                    // generic DotCall thunk below remains authoritative for every
                    // other dotted expression (and for explicit argument lists).
                    if (dotArgs is null
                        && TryResolveQualifiedMathNativeReference(dotCall, ctx) is { } mathNative)
                    {
                        return EvalResult<Algorithm>.Ok(mathNative);
                    }

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

    // ── Entry points ────────────────────────────────────────────────────────

    /// <summary>
    /// Run evaluation on an expression with prelude in scope.
    /// Lean: runResult → EvalM Result.
    /// <para><b>No front-end elaboration:</b> this lower-level host-AST boundary
    /// evaluates <paramref name="expr"/> exactly as supplied. It does not parse source,
    /// load modules, detect parameters, resolve implicit arguments, or finalize property
    /// exposure metadata. Hosts that need authoritative source elaboration use
    /// <see cref="Parser.Parse(string)"/> / <see cref="Parser.ParseAsync"/> or
    /// <see cref="KatLangEngine"/>; a host that constructs an AST owns the correctness
    /// of its elaboration metadata.</para>
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

    /// <summary>
    /// Run evaluation under explicit resource limits and cooperative host cancellation.
    /// <para>The token is observed once at entry — an already-cancelled token prevents
    /// evaluation from starting — and then cooperatively at the evaluator's budget
    /// chokepoints (dynamic invocations, loop iterations — optimized and generic —
    /// argument evaluation, expression-work checkpoints, and collection/string
    /// reservations), whether or not any opt-in budgets are configured. Cancellation
    /// is observed again before the run completes, including after bounded host
    /// projection in <see cref="RunFlat(Expr, EvaluationLimits?, CancellationToken)"/>.
    /// Requested cancellation escapes as <see cref="OperationCanceledException"/> carrying this
    /// token; it is never converted into an <see cref="EvalError"/> and never retained
    /// on a binding, so a cancelled run does not continue. An uncancelled token changes
    /// no result, no diagnostic, and no limit verdict.</para>
    /// </summary>
    /// <exception cref="OperationCanceledException">
    /// <paramref name="cancellationToken"/> was cancelled before or during evaluation.
    /// </exception>
    public static EvalResult<Result> Run(Expr expr, EvaluationLimits? limits, CancellationToken cancellationToken)
        => Run(
            expr,
            new RunScopedZeroArgPropertyResultCache(),
            enableLoopOptimization: true,
            loopDiagnostics: null,
            enableSequencePipelineOptimization: true,
            sequenceDiagnostics: null,
            limits,
            observations: null,
            hostOperations: null,
            cancellationToken);

    /// <summary>
    /// Run evaluation with SYNCHRONOUS host operations ambiently in scope, under the
    /// ordinary limits and cancellation contracts of
    /// <see cref="Run(Expr, EvaluationLimits?, CancellationToken)"/>.
    ///
    /// <para>Each operation resolves like a prelude member (see
    /// <see cref="HostOperations"/>), so a preparsed program that references host
    /// operation names — typically obtained from
    /// <see cref="Parser.Parse(string, RunOptions?)"/> with the same operations
    /// configured on <see cref="RunOptions.HostOperations"/> — evaluates them at the
    /// referencing sites. Host-operation delegates run inline on the calling thread;
    /// exceptions they throw propagate to the caller unchanged (see
    /// <see cref="HostOperation"/> for the full contract).</para>
    ///
    /// <para>This synchronous entry point accepts synchronous operations only: a set
    /// containing an asynchronous operation is rejected with
    /// <see cref="InvalidOperationException"/> before anything is evaluated — use
    /// <see cref="RunAsync(Expr, HostOperations, EvaluationLimits?, CancellationToken)"/>
    /// for asynchronous operations. All parameters are explicit on this overload so
    /// existing <c>Run</c> call sites (including literal-null arguments) keep binding
    /// exactly as before.</para>
    /// </summary>
    /// <exception cref="InvalidOperationException">
    /// <paramref name="hostOperations"/> contains an asynchronous operation.
    /// </exception>
    /// <exception cref="OperationCanceledException">
    /// <paramref name="cancellationToken"/> was cancelled before or during evaluation.
    /// </exception>
    public static EvalResult<Result> Run(
        Expr expr,
        HostOperations hostOperations,
        EvaluationLimits? limits,
        CancellationToken cancellationToken)
    {
        ArgumentNullException.ThrowIfNull(hostOperations);
        return Run(
            expr,
            new RunScopedZeroArgPropertyResultCache(),
            enableLoopOptimization: true,
            loopDiagnostics: null,
            enableSequencePipelineOptimization: true,
            sequenceDiagnostics: null,
            limits,
            observations: null,
            hostOperations,
            cancellationToken);
    }

    internal static EvalResult<Result> Run(
        Expr expr,
        IZeroArgPropertyResultCache zeroArgPropertyResultCache,
        EvaluationLimits? limits = null)
        => Run(expr, zeroArgPropertyResultCache, enableLoopOptimization: true, limits);

    /// <summary>
    /// Builds the root evaluation context for one run, including its fresh
    /// <see cref="EvaluationBudget"/>.
    ///
    /// <para>Configured operational budgets must mean the same thing no matter which
    /// internal execution strategy runs. A step budget disables both optimized loops
    /// and sequence pipelines because their operation counts differ from the generic
    /// paths. Configured string or cumulative-item budgets disable sequence fusion,
    /// whose allocation profile differs, while optimized loops remain eligible because
    /// both loop strategies charge those budgets identically. With none of those opt-in
    /// budgets, every requested optimization remains eligible. This is strategy
    /// independence by construction rather than by parallel accounting.</para>
    ///
    /// <para><b>This construction covers OPT-IN budgets only.</b> It works because an
    /// unconfigured step / cumulative-item / cumulative-string budget has no verdict at
    /// all, so pinning one strategy from the moment it is configured settles the
    /// question. An ALWAYS-ACTIVE budget — dynamic depth, the per-collection ceiling,
    /// the per-string ceiling — has a verdict on every run and therefore cannot be
    /// protected this way: whichever strategy runs, its accounting is observable. Those
    /// budgets must instead be EQUALIZED between the strategies
    /// (<see cref="EvaluationBudget.CheckCollectionSize"/> on the fused range path;
    /// the argument-evaluation levels charged by
    /// <c>SequencePipelineOptimizer.TryExecuteRecognized</c> and
    /// <see cref="EvaluateRangeCallArgumentsForSequenceOptimizer"/>). Adding a strategy
    /// switch here is never a way to make an always-active budget safe — and because
    /// this method's switches are driven by which UNRELATED budgets the caller
    /// configured, any inequality between the strategies becomes cross-talk. Pinned by
    /// <c>BudgetCrossTalkMatrixTests</c>.</para>
    /// </summary>
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
        // A configured cumulative materialization budget also forces the generic
        // SEQUENCE paths: fused pipelines charge only the per-collection boundary,
        // never the cumulative counter, so leaving them enabled made the verdict a
        // function of whether an unrelated MaxSteps happened to disable them.
        // Optimized LOOPS charge the cumulative counter identically to the generic
        // paths (pinned by GenericAndOptimizedLoops_ChargeOnlyTheirFinalPersistentState),
        // so they stay eligible.
        var sequenceOptimize = loopOptimize
            && !budget.HasConfiguredStringLimit
            && !budget.HasConfiguredMaterializationLimit;
        // A run configured with host operations resolves names against that
        // configuration's extended prelude (the ordinary prelude plus one ambient
        // wrapper member per operation); the budget carries the configuration, so the
        // prelude choice and the dispatch registry can never disagree within a run.
        return new EvalCtx(
            [budget.HostOperations?.RuntimePreludeAlgorithm ?? PreludeAlg],
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
    /// trees; runs before any evaluation-budget counter can move and charges nothing.
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
    /// Routing enforcement for the synchronous entry family: an asynchronous host
    /// operation can complete only by suspending the evaluation spine, which the
    /// synchronous pipeline is structurally unable to do — blocking a thread to
    /// simulate completion is exactly what the async surface exists to avoid. The
    /// configuration is rejected here, before any preflight or evaluation, as a host
    /// configuration error (never a KatLang diagnostic), mirroring the async twin
    /// family's own fail-loud ownership guards.
    /// </summary>
    private static void ThrowIfAsynchronousHostOperationsOnSynchronousEntry(HostOperations? hostOperations)
    {
        if (hostOperations?.ContainsAsynchronousOperations == true)
        {
            throw new InvalidOperationException(
                "The configured host operations contain an asynchronous operation, which a synchronous " +
                "evaluation entry point cannot suspend for. Use RunAsync (or an async KatLangEngine entry point), " +
                "or configure only synchronous host operations.");
        }
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

    /// <summary>
    /// Outcome of the shared run-entry preparation: either a pre-evaluation rejection
    /// (<see cref="Error"/> non-null) or a ready root context (<see cref="Ctx"/>).
    /// <see cref="Budget"/> is the run's fresh budget in BOTH cases, so the observed
    /// harness entry points can hand back the budget a rejected run would have used.
    /// </summary>
    private readonly struct PreparedRun
    {
        private readonly EvalCtx _ctx;

        private PreparedRun(EvalError? error, EvaluationBudget budget, EvalCtx ctx)
        {
            Error = error;
            Budget = budget;
            _ctx = ctx;
        }

        /// <summary>The structural-preflight or pre-evaluation validation rejection, if any.</summary>
        internal EvalError? Error { get; }

        /// <summary>The run's fresh <see cref="EvaluationBudget"/>; valid on both outcomes.</summary>
        internal EvaluationBudget Budget { get; }

        /// <summary>The ready root context. Fail-loud when the preparation was rejected.</summary>
        internal EvalCtx Ctx
            => Error is null
                ? _ctx
                : throw new InvalidOperationException(
                    "A rejected run preparation has no evaluation context; check Error first.");

        internal static PreparedRun Rejected(EvalError error, EvaluationBudget budget)
            => new(error, budget, default);

        internal static PreparedRun Ready(EvalCtx ctx)
            => new(null, ctx.Budget, ctx);
    }

    /// <summary>
    /// Run-entry preparation for the SYNCHRONOUS entry family: the host token is
    /// observed first (cancellation preempts every pre-evaluation verdict, including a
    /// misconfiguration rejection), then an asynchronous host-operation configuration is
    /// rejected before any tree work, then the shared admitted-run sequence runs. The
    /// async twin family prepares through <c>PrepareAsyncTwinRun</c>, whose guard order
    /// differs — that ordering difference is each wrapper's contract, so a new entry
    /// point must choose a wrapper, never call <see cref="PrepareAdmittedRun"/> directly.
    /// </summary>
    private static PreparedRun PrepareSynchronousRun(
        Expr expr,
        IZeroArgPropertyResultCache zeroArgPropertyResultCache,
        bool enableLoopOptimization,
        LoopOptimizationDiagnostics? loopDiagnostics,
        bool enableSequencePipelineOptimization,
        SequencePipelineDiagnostics? sequenceDiagnostics,
        EvaluationLimits? limits,
        EvaluationObservations? observations,
        HostOperations? hostOperations,
        CancellationToken cancellationToken)
    {
        // Host cancellation preempts every pre-evaluation verdict: an already-cancelled
        // token stops the run before the structural preflight spends O(tree) work.
        cancellationToken.ThrowIfCancellationRequested();
        ThrowIfAsynchronousHostOperationsOnSynchronousEntry(hostOperations);

        return PrepareAdmittedRun(
            expr,
            zeroArgPropertyResultCache,
            enableLoopOptimization,
            loopDiagnostics,
            enableSequencePipelineOptimization,
            sequenceDiagnostics,
            limits,
            observations,
            hostOperations,
            cancellationToken);
    }

    /// <summary>
    /// The ONE ordered non-evaluating preparation sequence shared by every evaluator
    /// run entry point, synchronous and async twin alike (none of it awaits):
    /// fresh run budget, structural safety preflight, Lean-aligned pre-evaluation
    /// validation, cache argument validation, root context construction. A preflight or
    /// validation rejection observes the host token (a cancellation requested during
    /// the rejected pass still escapes as <see cref="OperationCanceledException"/>,
    /// never as the returned error) and hands the rejection back with the budget.
    /// Callers reach this only through <see cref="PrepareSynchronousRun"/> or
    /// <c>PrepareAsyncTwinRun</c>, which own the per-family entry guards and their
    /// ordering relative to the first token observation.
    /// </summary>
    private static PreparedRun PrepareAdmittedRun(
        Expr expr,
        IZeroArgPropertyResultCache zeroArgPropertyResultCache,
        bool enableLoopOptimization,
        LoopOptimizationDiagnostics? loopDiagnostics,
        bool enableSequencePipelineOptimization,
        SequencePipelineDiagnostics? sequenceDiagnostics,
        EvaluationLimits? limits,
        EvaluationObservations? observations,
        HostOperations? hostOperations,
        CancellationToken cancellationToken)
    {
        // Creating the budget is pure field initialization — the structural preflight
        // still runs before any budget COUNTER can move and charges nothing.
        var budget = EvaluationBudget.Create(limits, hostOperations, cancellationToken);

        if (StructuralPreflight(expr, limits) is { } structuralError)
        {
            budget.ObserveCancellation();
            return PreparedRun.Rejected(structuralError, budget);
        }

        if (PreEvaluationValidationError(expr) is { } validationError)
        {
            budget.ObserveCancellation();
            return PreparedRun.Rejected(validationError, budget);
        }

        ArgumentNullException.ThrowIfNull(zeroArgPropertyResultCache);

        return PreparedRun.Ready(CreateRootCtx(
            zeroArgPropertyResultCache,
            enableLoopOptimization,
            loopDiagnostics,
            enableSequencePipelineOptimization,
            sequenceDiagnostics,
            budget,
            observations));
    }

    internal static EvalResult<Result> Run(
        Expr expr,
        IZeroArgPropertyResultCache zeroArgPropertyResultCache,
        bool enableLoopOptimization,
        LoopOptimizationDiagnostics? loopDiagnostics,
        bool enableSequencePipelineOptimization,
        SequencePipelineDiagnostics? sequenceDiagnostics,
        EvaluationLimits? limits = null,
        EvaluationObservations? observations = null,
        HostOperations? hostOperations = null,
        CancellationToken cancellationToken = default)
    {
        var preparation = PrepareSynchronousRun(
            expr,
            zeroArgPropertyResultCache,
            enableLoopOptimization,
            loopDiagnostics,
            enableSequencePipelineOptimization,
            sequenceDiagnostics,
            limits,
            observations,
            hostOperations,
            cancellationToken);
        if (preparation.Error is { } preparationError)
            return preparationError;

        var ctx = preparation.Ctx;
        var result = expr is Expr.AlgorithmExpr(var alg)
            ? EvalRootProgram(alg, expr.Span, ctx)
            : Eval(expr, ctx, []);

        // A cancellation requested during the final operation must not be missed merely
        // because that operation has no later charging checkpoint (for example, the last
        // one-slot property result needs no collection reservation). This is observation
        // only: every admitted depth level has already unwound, and no counter changes.
        ctx.Budget.ObserveCancellation();
        return result;
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
    /// Harness entry point: evaluates exactly like <see cref="RunCounted(Expr, IZeroArgPropertyResultCache, EvaluationLimits?, HostOperations?, CancellationToken)"/>
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
    /// <see cref="Run(Expr, IZeroArgPropertyResultCache, bool, LoopOptimizationDiagnostics?, bool, SequencePipelineDiagnostics?, EvaluationLimits?, EvaluationObservations?, HostOperations?, CancellationToken)"/>
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
        EvaluationObservations? observations = null,
        HostOperations? hostOperations = null,
        CancellationToken cancellationToken = default)
    {
        var preparation = PrepareSynchronousRun(
            expr,
            zeroArgPropertyResultCache ?? new RunScopedZeroArgPropertyResultCache(),
            enableLoopOptimization: enableOptimizations,
            loopDiagnostics,
            enableSequencePipelineOptimization: enableOptimizations,
            sequenceDiagnostics,
            limits,
            observations,
            hostOperations,
            cancellationToken);
        if (preparation.Error is { } preparationError)
            return (preparationError, preparation.Budget);

        var ctx = preparation.Ctx;
        var result = expr is Expr.AlgorithmExpr(var alg)
            ? EvalRootProgramCounted(alg, expr.Span, ctx)
            : EvalCounted(expr, ctx, []);

        ctx.Budget.ObserveCancellation();
        return (result, ctx.Budget);
    }

    internal static EvalResult<CountedResult> RunCounted(
        Expr expr,
        IZeroArgPropertyResultCache zeroArgPropertyResultCache,
        EvaluationLimits? limits = null,
        HostOperations? hostOperations = null,
        CancellationToken cancellationToken = default)
    {
        var preparation = PrepareSynchronousRun(
            expr,
            zeroArgPropertyResultCache,
            enableLoopOptimization: true,
            loopDiagnostics: null,
            enableSequencePipelineOptimization: true,
            sequenceDiagnostics: null,
            limits,
            observations: null,
            hostOperations,
            cancellationToken);
        if (preparation.Error is { } preparationError)
            return preparationError;

        var ctx = preparation.Ctx;
        var result = expr is Expr.AlgorithmExpr(var alg)
            ? EvalRootProgramCounted(alg, expr.Span, ctx)
            : EvalCounted(expr, ctx, []);

        ctx.Budget.ObserveCancellation();
        return result;
    }

    internal static EvalResult<CountedRootProgramResult> RunCountedWithTopLevelProperty(
        Expr expr,
        string topLevelPropertyName,
        IZeroArgPropertyResultCache zeroArgPropertyResultCache,
        EvaluationLimits? limits = null,
        HostOperations? hostOperations = null,
        CancellationToken cancellationToken = default)
    {
        var preparation = PrepareSynchronousRun(
            expr,
            zeroArgPropertyResultCache,
            enableLoopOptimization: true,
            loopDiagnostics: null,
            enableSequencePipelineOptimization: true,
            sequenceDiagnostics: null,
            limits,
            observations: null,
            hostOperations,
            cancellationToken);
        if (preparation.Error is { } preparationError)
            return preparationError;

        ArgumentException.ThrowIfNullOrWhiteSpace(topLevelPropertyName);

        var ctx = preparation.Ctx;
        EvalResult<CountedRootProgramResult> result;
        if (expr is Expr.AlgorithmExpr(var alg))
        {
            result = EvalRootProgramCountedWithTopLevelProperty(alg, expr.Span, ctx, topLevelPropertyName);
        }
        else
        {
            var outputR = EvalCounted(expr, ctx, []);
            result = outputR.IsError
                ? outputR.Error
                : EvalResult<CountedRootProgramResult>.Ok(
                    new CountedRootProgramResult(outputR.Value, TopLevelProperty: null));
        }

        ctx.Budget.ObserveCancellation();
        return result;
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
        return MissingImplicitArguments<Result>(wired, blockSpan);
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
        return MissingImplicitArguments<CountedResult>(wired, blockSpan);
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
            return MissingImplicitArguments<CountedRootProgramResult>(wired, blockSpan);
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
                    ZeroArgumentDemandArityMismatch(resolvedAlgorithm)));
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
    public static EvalResult<IReadOnlyList<Decimal128>> RunFlat(Expr expr)
        => RunFlat(expr, limits: null);

    /// <summary>Host-boundary flattening run under explicit resource limits.</summary>
    public static EvalResult<IReadOnlyList<Decimal128>> RunFlat(Expr expr, EvaluationLimits? limits)
        => RunFlat(expr, limits, cancellationToken: default);

    /// <summary>
    /// Host-boundary flattening run under explicit resource limits and cooperative host
    /// cancellation. Same cancellation contract as
    /// <see cref="Run(Expr, EvaluationLimits?, CancellationToken)"/>.
    /// </summary>
    /// <exception cref="OperationCanceledException">
    /// <paramref name="cancellationToken"/> was cancelled before or during evaluation.
    /// </exception>
    public static EvalResult<IReadOnlyList<Decimal128>> RunFlat(
        Expr expr, EvaluationLimits? limits, CancellationToken cancellationToken)
        => ProjectFlatHostAtoms(Run(expr, limits, cancellationToken), limits, cancellationToken);

    /// <summary>
    /// The flat entry family's host-boundary projection, shared by <see cref="RunFlat(Expr, EvaluationLimits?, CancellationToken)"/>
    /// and <see cref="RunFlatAsync(Expr, EvaluationLimits?, CancellationToken)"/> (it
    /// awaits nothing). Same rule as the engine: the host projection is bounded, so a
    /// successful evaluation cannot be followed by an unbounded flattening allocation.
    /// The trailing observation exists because host flattening belongs to the flat run
    /// operation and may walk a bounded but wide value graph after core evaluation has
    /// completed.
    /// </summary>
    private static EvalResult<IReadOnlyList<Decimal128>> ProjectFlatHostAtoms(
        EvalResult<Result> evaluation, EvaluationLimits? limits, CancellationToken cancellationToken)
    {
        if (evaluation.IsError) return evaluation.Error;

        var limit = (limits ?? EvaluationLimits.Default).EffectiveMaxCollectionItems;
        var result = evaluation.Value.TryToHostAtoms(limit, out var atoms)
            ? EvalResult<IReadOnlyList<Decimal128>>.Ok(atoms)
            : new EvalError.CollectionSizeLimitExceeded(limit, limit + 1L);

        cancellationToken.ThrowIfCancellationRequested();
        return result;
    }


    // ── Utility ──────────────────────────────────────────────────────────────

    /// <summary>
    /// Shared exponentiation for the <c>^</c> operator and <c>Math.Pow</c>.
    /// The EXACT-BY-SQUARING guarantee covers integer exponents whose magnitude
    /// fits the host <see cref="long"/>: those use Decimal128 exponentiation by
    /// squaring — exact whenever the true power fits 34 significant digits, and
    /// carrying an integral quantum so <c>2^10</c> stays <c>1024</c>, not
    /// <c>1024.000…</c>. Negative integer exponents are the reciprocal of the
    /// positive power. Everything else — fractional, non-finite, and beyond-long
    /// integral exponents — uses <see cref="Decimal128.Pow"/> and is a 34-digit
    /// approximation for ordinary finite bases; the IEEE-specified special bases
    /// (0, ±1, NaN, the infinities, signed zero) still resolve exactly by sign
    /// and parity there, which <c>Decimal128NumericsTests</c> pins through both
    /// public spellings. Zero raised to any negative integer exponent stays the
    /// specified KatLang error rather than the IEEE infinity.
    /// </summary>
    internal static EvalResult<Result> EvalPow(SourceSpan? span, Decimal128 b, Decimal128 exp)
    {
        if (b == 0 && exp < 0 && Decimal128.IsInteger(exp))
            return new EvalError.IllegalInEval("zero cannot be raised to a negative integer exponent") { Span = span };

        return EvalResult<Result>.Ok(new Result.Atom(Decimal128Pow(b, exp)));
    }

    private static Decimal128 Decimal128Pow(Decimal128 b, Decimal128 exp)
    {
        // IsInteger is false for NaN and the infinities, so non-finite exponents
        // take Decimal128.Pow's IEEE behavior. Integral exponents beyond long also
        // delegate: IEEE pow fully specifies the special bases (0, ±1, NaN, the
        // infinities resolve exactly by sign and parity — pinned by tests), and for
        // any other finite base the true power needs more than 34 digits, so no
        // squaring loop could deliver exactness either; bases very close to 1 give
        // genuine finite approximations that Decimal128.Pow computes directly.
        if (!Decimal128.IsInteger(exp) || Decimal128.Abs(exp) > long.MaxValue)
            return CanonicalizeMathResult(Decimal128.Pow(b, exp));

        // |exp| <= long.MaxValue, so the narrowing is exact and negation cannot
        // overflow. For a negative exponent, prefer the by-squaring positive
        // power followed by one correctly-rounded division. Its intermediate can
        // overflow even when the reciprocal is still a representable subnormal
        // (for example 10^-6146), though, because Decimal128's subnormal range
        // extends farther below zero than its finite range extends above it. In
        // that one case delegate the original signed exponent to Decimal128.Pow
        // instead of collapsing the valid reciprocal to zero.
        var exponent = (long)exp;
        if (exponent < 0)
        {
            var positivePower = PowNonNegative(b, (ulong)(-exponent));
            return Decimal128.IsInfinity(positivePower)
                ? CanonicalizeMathResult(Decimal128.Pow(b, exp))
                : Decimal128.One / positivePower;
        }

        return PowNonNegative(b, (ulong)exponent);
    }

    private static Decimal128 PowNonNegative(Decimal128 b, ulong exponent)
    {
        Decimal128 result = Decimal128.One;
        var baseVal = b;
        var remainingExponent = exponent;

        while (remainingExponent > 0)
        {
            if ((remainingExponent & 1UL) == 1UL)
                result *= baseVal;

            remainingExponent >>= 1;
            if (remainingExponent > 0)
                baseVal *= baseVal;
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
