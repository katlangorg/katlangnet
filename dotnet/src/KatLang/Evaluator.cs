using System.Collections;
using System.Numerics;
using KatLang.Evaluation;
using KatLang.Evaluation.Caching;
using KatLang.Optimizations.Loops;
using KatLang.Optimizations.Sequences;

namespace KatLang;

/// <summary>
/// The LOW-LEVEL evaluator: evaluates a host-built <see cref="Expr"/> exactly as supplied —
/// without parsing, module loading, front-end elaboration, or the engine's reading of the
/// root's <c>MinDecimalPlaces</c> / <c>MaxDecimalPlaces</c> display settings — and returns the structured value or error as an
/// <see cref="EvalResult{T}"/>. It is not a source runner: source text goes through
/// <see cref="KatLangEngine"/> (or <see cref="Parser"/> to elaborate without evaluating), and
/// an elaborated <see cref="ParseResult.Root"/> may be evaluated here only when it has no
/// errors. The evaluator matches the Lean specification.
/// Host-built nodes must satisfy their declared payload types and semantic invariants;
/// they are not deeply immutable DTOs. Structural preflight rejects cycles and excessive
/// depth, but is not a general validator for null children or every malformed payload.
/// Do not mutate an AST or its caller-owned collections while a consumer is using it.
///
/// <para>Implementation notes.</para>
/// Uses <see cref="EvalResult{T}"/> for structured errors instead of nullable returns;
/// Lean's <c>EvalM</c> also carries the per-run cache and binding-context state.
/// Ownership-first lookup: local → parent chain structural → opens fallback across chain.
/// Member selection: an open provides only PUBLIC members, and structural dot access selects DECLARED members
/// (private included). Selection never depends on exposure: the selected member's accessibility is checked afterwards.
///
/// Builtins are ordinary prelude bindings. Every call forms the same demandable supply:
/// an ordinary expression becomes a suspended <c>NeedCell</c>, a parameter reference
/// transports its existing cell, and an arbitrary explicit spread forces supply formation.
/// Parameters expose independent channels: VALUE demands one sticky counted completion;
/// CALLABLE projects a resolved algorithm identity without evaluating VALUE. Ready data
/// has no invented callable. Bodies, patterns, builtin controls and callbacks determine
/// first-demand order. Property-result caching remains a separate memoization domain.
/// </summary>
/// <remarks>
/// All Run* entry points evaluate supplied ASTs as-is after structural and core
/// validity preflight; they do not perform front-end elaboration. Hosts may build
/// ASTs through the public records, but must supply correct name ownership and
/// <see cref="Property.Exposure"/> metadata and keep executable metadata unchanged
/// during evaluation. Exported properties must not capture caller bindings, and the
/// evaluator ENFORCES this (since November 2026; formerly it trusted the flag). An
/// exported zero-argument property is evaluated DETACHED from the calls that are
/// active when its evaluation starts: it inherits no parameter binding, and the
/// activations that exist at that moment stay identities but supply no input. A
/// captured parameter is used through the activation of the scope that lexically
/// owns it, never from a caller's environment. On the paths the evaluator checks, a
/// falsely exported capture is therefore REFUSED —
/// <see cref="KatLangErrorCode.UnknownName"/> at every executed operation on the
/// parameter (its value read, a call through it, its transport as an argument),
/// <see cref="KatLangErrorCode.LocalOnlyProperty"/> at a navigation or at a
/// local-only read — instead of exposing an inaccessible member's value or reusing
/// another call's value for the rest of the run. The binding cell a runtime-target
/// alias retains is checked as well (row R-1 of
/// <c>docs/design/formal-correspondence-ledger.md</c>, qualified, November 2026): it
/// records the input reads of its computation — a captured parameter operation, a
/// local-only property read, an admitted access of a local-only member by a dot
/// access, a static alias path step or an <c>open</c> that provides the name (not the
/// path step of an <c>open</c> target: that row's open-target qualification) — and an
/// exported evaluation that reuses a cell known to have read an input of an
/// activation detached in it is refused before the cell's channel runs, with the
/// alias's own <see cref="KatLangErrorCode.LocalOnlyProperty"/>, whichever read
/// established the cell first; a read the computation makes while such an
/// evaluation is being served — in the row, or later in a lazy position or a
/// captured call's argument that the evaluation demands — is refused at the read,
/// with the read's own refusal. A read an attached reader demands afterwards uses
/// its own inputs.
/// These are the paths the enforcement covers; no statement says that every wrong
/// flag is a refusal. Supplying correct exposure metadata remains the host's
/// obligation. The flag governs accessibility
/// and detachment. Each call owns its inner bindings. An accessible binding with
/// no owning call uses the run-scoped entry. A host-built <see cref="ScopeCtx"/>
/// (kept as the parent of an opened inline block) is the declaring
/// owner of its properties for caching, identified by the scope OBJECT — two
/// independently constructed scopes never share cached values, even when they are
/// structurally equal — and it is never activated, so a name it lists among its
/// <see cref="ScopeCtx.Parameters"/> has no binding to read. Use
/// <see cref="Parser.Parse(string)"/> or <see cref="KatLangEngine"/> for
/// source programs and the complete front-end invariants.
/// </remarks>
public static partial class Evaluator
{
    /// <summary>
    /// A selected lexical binding: its declaring owner (an evaluator-owned declaration, or the
    /// ownerless host-built level that declares it — CACHE-OWNER-D3), the binding, and the binding's
    /// value wired in context. <see cref="CrossesCarrier"/> marks a VALUE read that reached this binding
    /// through a structural carrier (Q-36 with M4★, <see cref="AliasTerminal.CrossesCarrier"/>).
    /// </summary>
    private readonly record struct ResolvedLexicalProperty(
        PropertyDeclaringOwner Owner,
        Property Binding,
        Algorithm ResolvedAlgorithm,
        bool CrossesCarrier = false)
    {
        /// <summary>
        /// THE OPEN ROUTE'S ADMISSION (ledger R-1, November 2026; Lean <c>ResolvedProperty.openRefusal</c>):
        /// the display name of the <c>open</c> that PROVIDED this binding, whose access law admitted the
        /// selected member at the reading site (<see cref="SelectOpenHit"/>; its refusal names this
        /// provider), or null for a structural selection, which no access law judges. The lookup that sets
        /// it notes nothing; the consumer of the selected member makes the admission's input read
        /// (<see cref="AdmitOpenAccess"/>).
        /// </summary>
        internal string? OpenProvider { get; init; }
    }

    // ── EvalCtx (Lean: EvalCtx) ─────────────────────────────────────────────

    /// <summary>
    /// Evaluation context threaded through resolution and evaluation.
    /// Wraps the algorithm chain (current algorithm + enclosing callers) used for
    /// both lexical resolution and runtime dispatch.
    /// HeadScope is the ACTIVATED declaring scope of the head when the head was entered
    /// with parameters (<see cref="EnterAlgorithmBody"/>): the level whose
    /// <see cref="ScopeCtx.Activation"/> captured-parameter reads and the accessibility law
    /// consult, and the parent every scope wired under the head receives. It is null for a
    /// head pushed without an activation, whose site scope is then its plain declaring scope
    /// (<c>SiteScope</c>); every push resets it, because it describes the head alone.
    /// NeedEnv carries the invocation's shared parameter cells: a parameter's VALUE outcome
    /// and its CALLABLE identity (higher-order dispatch projects the callable from the cell).
    /// Services is the run's ONE <see cref="RunServices"/> (caches, optimizer selection,
    /// diagnostics, observations), and Budget the run-scoped resource budget: both are
    /// REFERENCES deliberately carried by this copied struct, so every derived context
    /// shares the same run's services, charges the same run's counters, and no copy can
    /// reset them.
    /// Lean: structure EvalCtx where callStack : List Algorithm; needEnv; bindingContext;
    /// headScope : Option ScopeCtx := none.
    /// </summary>
    internal readonly record struct EvalCtx(
        IReadOnlyList<Algorithm> CallStack,
        ScopeCtx? HeadScope,
        RunServices Services,
        EvaluationBudget Budget)
    {
        internal NeedEnv NeedEnv { get; init; } = [];
        internal EvalCtx WithNeedEnv(NeedEnv env) => this with { NeedEnv = env };

        /// <summary>
        /// THE ACTIVATION WATERMARK of this context (EXPORTED-DETACHED, November 2026), or zero when no
        /// exported evaluation entered it: a <see cref="ParameterActivation"/> whose
        /// <see cref="ParameterActivation.Serial"/> is below it and that is one of the context's
        /// <see cref="DetachedOwners"/> — an activation of a level enclosing a binding whose detached
        /// evaluation the context is inside — is DETACHED here (<see cref="IsDetached"/>): still an
        /// identity, never a source of inputs. It rides on the call-stack node
        /// (<see cref="AnnotatedReadOnlyList{T}"/>), so this struct keeps its size and every derived
        /// context — a pushed head, a bound callee, a suspended cell's caller — carries it: a closure or
        /// plan created inside an exported evaluation stays detached wherever it is demanded later.
        /// Lean: <c>EvalCtx.detachedBefore</c>.
        /// </summary>
        internal long DetachedBefore
            => CallStack is AnnotatedReadOnlyList<Algorithm> annotated ? annotated.DetachedBefore : 0;

        /// <summary>
        /// THE DETACHED OWNERS of this context (RETURNED CALLABLES ACROSS DETACHED READS, November 2026), or
        /// null: the declaring chains of the bindings whose detached evaluation the context is inside, whose
        /// activations are the evaluations' ENCLOSING CALLS. Only those are detached below the watermark; an
        /// activation recorded before the evaluation started by a computation it did not run inside — the
        /// level of a callable a retained cell or another exported evaluation returned — stays usable. Carried
        /// by the call-stack node beside the input record. Lean: <c>EvalCtx.detachedOwners</c>.
        /// </summary>
        internal DetachedOwnerSet? DetachedOwners
            => CallStack is AnnotatedReadOnlyList<Algorithm> annotated ? annotated.Owners : null;

        internal DetachedOwnerSet? ServingOwners => DetachedOwnerSet.Union(null, DetachedOwners, DetachedBefore);

        /// <summary>
        /// THE INPUT RECORD of this context (ledger R-1, November 2026), or null: the record of the
        /// retained runtime-alias binding cell whose computation this context belongs to. Set where a
        /// cell's row is supplied (<see cref="AliasBindingCell"/>, <see cref="MarkInputRecord"/>) and
        /// carried by the call-stack node exactly as the watermark is, so every context derived from the
        /// row's — a pushed head, a bound callee, a suspended cell's caller — records its input reads
        /// on that cell. Lean: <c>EvalCtx.inputRecord</c>.
        /// </summary>
        internal AliasCellInputs? InputRecord
            => CallStack is AnnotatedReadOnlyList<Algorithm> annotated ? annotated.InputRecord : null;

        /// <summary>This context with its input record replaced by <paramref name="record"/> (its watermark kept).</summary>
        internal EvalCtx MarkInputRecord(AliasCellInputs? record)
            => this with { CallStack = AnnotatedReadOnlyList<Algorithm>.MarkInputRecord(CallStack, record) };

        /// <summary>
        /// THE DETACHED CONTEXT of an exported evaluation that starts under <paramref name="watermark"/>
        /// (<see cref="EvaluationBudget.ActivationWatermark"/>), of a binding declared under
        /// <paramref name="declaringChain"/> (its wired parent): the same call stack, head scope, services
        /// and budget, NO inherited need cell, the watermark raised to at least <paramref name="watermark"/>
        /// (a nested detachment never lowers it) and the chain's activations added to the detached owners
        /// (<see cref="DetachedOwners"/>). The caller supplies the empty value environment beside it
        /// (<see cref="DetachedEvaluation"/>). Lean: <c>EvalCtx.detach</c> over <c>chainActivations</c>.
        /// </summary>
        internal EvalCtx Detach(long watermark, ScopeCtx? declaringChain)
            => this with { CallStack = AnnotatedReadOnlyList<Algorithm>.Mark(CallStack, watermark, declaringChain), NeedEnv = [] };

        /// <summary>
        /// THIS CONTEXT AT AN ACTIVATION'S OWN WATERMARK (ledger R-1, November 2026; Lean
        /// <c>EvalCtx.reattach</c>): the same call stack, need tier, head scope, input record and budget
        /// under the watermark that was in force when the activation with serial
        /// <paramref name="activationSerial"/> was recorded — the first watermark, from this context's own
        /// outwards, that does not detach it (the call-stack nodes below keep the watermarks the context was
        /// under before each exported evaluation it is inside raised it). A context that does not detach the
        /// activation is unchanged. It is the context a local-only runtime alias's row is supplied in
        /// (<see cref="AliasCellContext"/>): the row belongs to its declaring level, whichever reader reaches
        /// it first.
        /// </summary>
        internal EvalCtx Reattach(long activationSerial)
            => CallStack is AnnotatedReadOnlyList<Algorithm> annotated && annotated.DetachedBefore > activationSerial
                ? this with { CallStack = AnnotatedReadOnlyList<Algorithm>.Reattach(annotated, activationSerial) }
                : this;
        /// <summary>
        /// A fresh empty context. This is a PROPERTY, not a shared static instance:
        /// every use must get its own budget — and with it its own UNSEEDED random
        /// stream — because a shared one would be global mutable evaluation state.
        /// Its services are the stateless <see cref="RunServices.Unconfigured"/>.
        /// </summary>
        public static EvalCtx Empty => new([], null, RunServices.Unconfigured, EvaluationBudget.Create(null));

        /// <summary>
        /// Lean: EvalCtx.push — prepend an algorithm to the call stack. The pushed head has no
        /// activated head scope (<c>headScope := none</c>); <see cref="EnterAlgorithmBody"/>
        /// supplies one through <see cref="Push(Algorithm, ScopeCtx?)"/>.
        /// </summary>
        public EvalCtx Push(Algorithm alg)
            => Push(alg, headScope: null);

        /// <summary>Prepend an algorithm to the call stack with its activated head scope.</summary>
        public EvalCtx Push(Algorithm alg, ScopeCtx? headScope)
            => this with { CallStack = Prepend(alg, CallStack), HeadScope = headScope };

        /// <summary>Lean: EvalCtx.head? — first algorithm in the call stack.</summary>
        public Algorithm? Head => CallStack.Count > 0 ? CallStack[0] : null;

        internal IZeroArgPropertyResultCache ZeroArgPropertyResultCache => Services.ZeroArgPropertyResultCache;
        internal IZeroArgPropertyResultCache PropertyAccessCache
        {
            get
            {
                var cache = Services.ZeroArgPropertyResultCache;
                // A synchronous run lends its own store to its heap steps. Even cells supplied before
                // the fold use this accessor, so the ordinary twin cache guards apply at every read.
                return FoldTrampoline.IsPumpingRun(Budget) ? cache.TwinView ?? cache : cache;
            }
        }
        internal IDeconstructionBindingCache DeconstructionBindingCache => Services.DeconstructionBindingCache;
        internal bool EnableLoopOptimization => Services.EnableLoopOptimization;
        internal LoopOptimizationDiagnostics? LoopDiagnostics => Services.LoopDiagnostics;
        internal bool EnableSequencePipelineOptimization => Services.EnableSequencePipelineOptimization;
        internal SequencePipelineDiagnostics? SequenceDiagnostics => Services.SequenceDiagnostics;
        internal EvaluationObservations? Observations => Services.Observations;
    }

    /// <summary>
    /// The run-invariant services of an evaluation context (PERF-STATE-1, implementation-only): what
    /// the run's entry point chose once — its zero-argument property cache, its deconstruction
    /// shared-bind cache, the optimizer selection and the optimizers' diagnostics, and the passive
    /// observations. ONE instance is created with a run's root context and every context derived from
    /// it carries the same reference; no derivation replaces it and nothing mutates it, so a context
    /// holds these in one slot instead of copying seven fields into every context and suspension.
    /// The caches and sinks it references are the run's own mutable objects, exactly as before: their
    /// identities, not this holder's, remain the cache and run identities. Activation state (call
    /// stack, head scope, parameter cells) and the run budget stay fields of <see cref="EvalCtx"/>.
    /// </summary>
    internal sealed record RunServices(
        IZeroArgPropertyResultCache ZeroArgPropertyResultCache,
        IDeconstructionBindingCache DeconstructionBindingCache,
        bool EnableLoopOptimization,
        LoopOptimizationDiagnostics? LoopDiagnostics,
        bool EnableSequencePipelineOptimization,
        SequencePipelineDiagnostics? SequenceDiagnostics,
        EvaluationObservations? Observations)
    {
        /// <summary>
        /// The services of a context built outside a run entry (<see cref="EvalCtx.Empty"/>): no caching
        /// (both caches are the stateless pass-through singletons), both optimizers enabled, no diagnostics
        /// and no observations. It holds no mutable state, so one shared instance is safe.
        /// </summary>
        internal static RunServices Unconfigured { get; } = new(
            UncachedZeroArgPropertyResultCache.Instance, UncachedDeconstructionBindingCache.Instance,
            EnableLoopOptimization: true, LoopDiagnostics: null,
            EnableSequencePipelineOptimization: true, SequenceDiagnostics: null,
            Observations: null);
    }

    // ── Environment types ────────────────────────────────────────────────────

    internal static object ValueEnvironmentCacheIdentity(ValEnv valEnv)
        => valEnv is IValueEnvironmentCacheIdentityProvider provider
            ? provider.CacheIdentity
            : valEnv;

    /// <summary>
    /// The binding-context identity of <paramref name="ctx"/> (Lean: <c>EvalCtx.bindingContext</c>):
    /// what a LOCAL-ONLY zero-argument property entry is keyed by — recorded at owner entry
    /// (<see cref="ParameterActivation.Capture"/>), or taken at the access when no activation owns the
    /// binding — and so, through its hoisted source's cache key, what separates a deconstruction
    /// group's shared binds of distinct activations. The need tier a binding
    /// boundary minted (<see cref="BoundNeedEnv"/>, or the <see cref="LayeredBoundNeedEnv"/> of a narrow
    /// boundary over a wide tier) IS that identity, EVEN WHEN IT IS EMPTY: a call that
    /// binds no cell and inherits none is still a new activation (CACHE-OWNER-D2, October 2026; Lean
    /// <c>EvalCtx.bindParameters</c> allocates a fresh context at every boundary). Only a context below
    /// no boundary — the root, a host entry, a planned loop's shadowed step context — falls back to its
    /// value environment's identity, which a planned loop advances per iteration. A layered tier is
    /// recognized before its <c>Count</c> is read, which would build its flat list.
    /// </summary>
    internal static object BindingContextIdentity(in EvalCtx ctx, ValEnv valEnv)
        => ctx.NeedEnv is LayeredBoundNeedEnv || ctx.NeedEnv.Count != 0 || ctx.NeedEnv is BoundNeedEnv
            ? ctx.NeedEnv
            : ValueEnvironmentCacheIdentity(valEnv);

    /// <summary>Value environment: maps parameter names to results. Lean: ValEnv.lookup (Option).</summary>
    private static Result? LookupVal(ValEnv env, string name)
    {
        // Indexed like LookupNeed: no boxed enumerator per lookup (PERF-ORD-1).
        for (var i = 0; i < env.Count; i++)
        {
            var (n, v) = env[i];
            if (n == name) return v;
        }
        return null;
    }

    /// <summary>
    /// Native-wrapper argument read, shared by Math-member natives and host
    /// operations. A wrapper body's argument names are the wrapper's own bound
    /// parameters, so this is EXACTLY the <see cref="Expr.Param"/> value read —
    /// <see cref="EvalParamCounted"/> projected to its value — and not a
    /// separate lookup rule: the parameter's supplied cell first (Model C; its
    /// demand is the argument's one value evaluation), then the value
    /// environment.
    /// The wrapper body carries no source span, so the error is positioned by
    /// the enclosing call/dot-call context like every other native failure.
    /// </summary>
    private static EvalResult<Result> LookupNativeArgument(
        EvalCtx ctx,
        ValEnv valEnv,
        string name)
        => ProjectCountedValue(EvalParamCounted(name, span: null, ctx, valEnv));

    /// <summary>
    /// The inherited need-cell tier of a callee's context with the callee's parameter
    /// names shadowed out of it (`NeedEnv`; the value tier is shadowed beside this helper
    /// by <see cref="ShadowValEnv"/>).
    /// <para>A bound parameter owns its name on every channel: its supplied cell carries
    /// both its VALUE and its CALLABLE channel, so neither a value-position read nor a
    /// call-position read of it can reach a same-named caller binding. Names the callee
    /// does not bind stay visible, which is what lets a nested call still reach an
    /// ancestor-owned parameter. Every user-call, conditional-call, callback, and
    /// loop-step binding site — generic and planned, synchronous and async twin —
    /// derives its callee tier from this ONE filter (<see cref="UnshadowedBindings"/>) with its own cells
    /// prepended (<see cref="MintNeedBindingContext"/>); the callee's binding-context identity (the key
    /// component of a LOCAL-ONLY property's zero-arg cache entry) is minted with that tier — by the
    /// <see cref="Concat"/> that prepends them, or as the <see cref="LayeredBoundNeedEnv"/> of a narrow
    /// boundary over a wide tier, which applies the same filter without copying. The loop planner's
    /// shadowed step context is this helper's own result: a filtered tier of at least
    /// <see cref="MinimumIndexedParameterCount"/> bindings is held as a <see cref="ShadowedNeedEnv"/> (the same
    /// bindings, recognizably made by the evaluator), so each planned round's boundary can layer over it.</para>
    /// Lean: <c>EvalCtx.bindParameters</c> (which also performs the prepend).
    /// </summary>
    internal static EvalCtx ShadowInheritedParameterEnvironments(EvalCtx ctx, IReadOnlyList<string> parameterNames)
    {
        var shadowed = UnshadowedBindings(ctx.NeedEnv, parameterNames);
        return ctx.WithNeedEnv(shadowed.Count >= MinimumIndexedParameterCount ? new ShadowedNeedEnv(shadowed) : shadowed);
    }

    // The kept bindings in order, as the former `Where(…).ToArray()` produced them — a fresh array,
    // or the shared empty array when none is kept — without its closure, delegate and iterator
    // (three heap objects per binding site; 2026-11 allocation attribution). A layered tier filters
    // its parts without building its flat list (LayeredBoundNeedEnv.Unshadowed).
    private static NeedEnv UnshadowedBindings(NeedEnv inherited, IReadOnlyList<string> parameterNames)
    {
        if (inherited is LayeredBoundNeedEnv layered)
            return layered.Unshadowed(parameterNames);
        if (parameterNames.Count >= MinimumIndexedParameterCount && inherited.Count > LinearShadowNameScanLimit)
            return UnshadowedWideBindings(inherited, parameterNames);
        var kept = 0;
        for (var i = 0; i < inherited.Count; i++)
            if (!ContainsOrdinal(parameterNames, inherited[i].Name)) kept++;
        if (kept == 0)
            return Array.Empty<(string Name, NeedCell Cell)>();
        var bindings = new (string Name, NeedCell Cell)[kept];
        var next = 0;
        for (var i = 0; i < inherited.Count && next < kept; i++)
            if (!ContainsOrdinal(parameterNames, inherited[i].Name))
                bindings[next++] = inherited[i];
        return bindings;
    }

    // UnshadowedBindings when the callee's names are wide and so is the inherited tier — a wide head called from
    // a wide activation, its own recursion included: membership goes through ONE ordinal set of the names
    // (null included, as in ShadowValEnv) instead of a scan of them per inherited binding, which cost
    // inherited × names comparisons per call. The kept bindings and their order are the scan's.
    [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.NoInlining)]
    private static NeedEnv UnshadowedWideBindings(NeedEnv inherited, IReadOnlyList<string> parameterNames)
    {
        var shadowed = new HashSet<string>(parameterNames, StringComparer.Ordinal);
        var kept = 0;
        for (var i = 0; i < inherited.Count; i++)
            if (!shadowed.Contains(inherited[i].Name)) kept++;
        if (kept == 0)
            return Array.Empty<(string Name, NeedCell Cell)>();
        var bindings = new (string Name, NeedCell Cell)[kept];
        var next = 0;
        for (var i = 0; i < inherited.Count && next < kept; i++)
            if (!shadowed.Contains(inherited[i].Name))
                bindings[next++] = inherited[i];
        return bindings;
    }

    /// <summary>
    /// Removes the named bindings from an INHERITED value environment — the
    /// value-tier counterpart of <see cref="ShadowInheritedParameterEnvironments"/>.
    /// <para>A callee's value environment is its own bindings prepended to the
    /// CALLER's, which is what lets a nested property body still read an
    /// ancestor-owned parameter. A parameter the call bound through its
    /// supplied cell (every Model-C binding) contributes no value binding, so
    /// without this filter a same-named binding inherited from the caller would
    /// stay in the callee's value tier: a read that reaches that tier would
    /// observe an unrelated caller value instead of the argument bound at THIS
    /// invocation, and which caller parameter names happen to collide with a
    /// callee's parameter names would become observable. Shadowing the callee's
    /// whole parameter list is the same rule the need-cell tier applies
    /// (<see cref="ShadowInheritedParameterEnvironments"/>); names that
    /// DO carry a value binding are shadowed by the prepended bindings anyway,
    /// so filtering the tail changes nothing for them.</para>
    /// Returns the SAME instance when nothing is removed: a shadowed tier is a view of
    /// the caller's binding context, and the callee's own context identity is minted by
    /// the <see cref="Concat"/> that prepends its bindings.
    /// Lean: <c>ValEnv.shadow</c>.
    /// </summary>
    internal static ValEnv ShadowValEnv(
        ValEnv env,
        IReadOnlyList<string> shadowedNames)
    {
        if (env.Count == 0 || shadowedNames.Count == 0)
            return env;

        // Callee parameter lists are short in every ordinary program, so the
        // linear membership scan avoids allocating a set on the hot call path;
        // a wide deconstruction signature crosses over to the set.
        HashSet<string>? shadowedSet = shadowedNames.Count > LinearShadowNameScanLimit
            ? new HashSet<string>(shadowedNames, StringComparer.Ordinal)
            : null;

        List<(string Name, Result Value)>? filtered = null;
        for (var index = 0; index < env.Count; index++)
        {
            var binding = env[index];
            var isShadowed = shadowedSet is not null
                ? shadowedSet.Contains(binding.Name)
                : ContainsOrdinal(shadowedNames, binding.Name);

            if (isShadowed)
            {
                if (filtered is null)
                {
                    filtered = new List<(string Name, Result Value)>(env.Count - 1);
                    for (var copied = 0; copied < index; copied++)
                        filtered.Add(env[copied]);
                }

                continue;
            }

            filtered?.Add(binding);
        }

        return filtered ?? env;
    }

    /// <summary>
    /// Parameter-list length at which <see cref="ShadowValEnv"/> switches from a
    /// linear membership scan to a hash set.
    /// </summary>
    internal const int LinearShadowNameScanLimit = 8;

    /// <summary>
    /// The smallest WIDE parameter frame (implementation-only, 2026-11-22, finding
    /// <c>evaluator-runtime-quadratic-parameter-width</c>): an activation captured over at least this many names
    /// keeps its owned-name index (<see cref="ParameterActivation.Capture"/>, <see cref="ScopeBindsParameter"/>),
    /// the tier a call minted with at least this many cells of its own looks the callee's names up through that
    /// index (<see cref="WideBoundNeedEnv"/>, <see cref="LookupNeed"/>), and a callee with at least this many names
    /// called from a tier of more than <see cref="LinearShadowNameScanLimit"/> bindings shadows it through a set
    /// (<see cref="UnshadowedBindings"/>).
    /// Before, every parameter read of a frame of N names scanned the head's names and the bindings (O(N) per
    /// read, O(N²) per body that reads them all), as did every forwarded parameter and every inherited binding a
    /// call shadowed. Every narrower frame keeps the scans, which are cheaper than an index at that size: the same
    /// threshold as <see cref="PropertyBindingIndexCache.MinimumIndexedPropertyCount"/>.
    /// </summary>
    internal const int MinimumIndexedParameterCount = 32;

    internal static bool ContainsOrdinal(IReadOnlyList<string> names, string name)
    {
        for (var index = 0; index < names.Count; index++)
            if (string.Equals(names[index], name, StringComparison.Ordinal))
                return true;
        return false;
    }

    // ── Algorithm helpers ────────────────────────────────────────────────────

    /// <summary>
    /// Lean: Algorithm.withParent. No-op for Builtin variant. The wired copy is a VIEW of the
    /// same written declaration: the record copy carries <see cref="Algorithm.Declaration"/>.
    /// An alias is wired like any declaration: its parent is the scope its target is resolved in.
    /// <para>A loaded module (Q-31 H-P, decided 2026-10-06) is a hygienic source unit rooted at the
    /// prelude: wherever it is reached — a property holding it, an <c>open</c>, a dot path, an
    /// argument — it is wired under the chain's root level, never under the scope that reached it,
    /// so its names never see the load site's and every reach is the ONE declaration in the ONE
    /// declaring scope (Q-32 I-U: one member binding per module declaration).</para>
    /// </summary>
    private static Algorithm WithParent(Algorithm alg, ScopeCtx? parent) => alg switch
    {
        Algorithm.Builtin => alg,
        Algorithm.User { IsModuleElaborated: true } module => module with { Parent = ChainRoot(parent) },
        Algorithm.User user => user with { Parent = parent },
        Algorithm.Conditional family => family with { Parent = parent },
        Algorithm.Alias alias => WireAlias(alias, parent),
    };

    /// <summary>Each wired alias with opens carries the plain scope for that wiring's steps.</summary>
    internal static Algorithm.Alias WireAlias(Algorithm.Alias alias, ScopeCtx? parent)
    {
        var wired = alias with { Parent = alias.IsModuleElaborated ? ChainRoot(parent) : parent };
        wired.WiredOpenScope = wired.Opens.Count == 0 ? null : AsScopeCtx(wired);
        return wired;
    }

    /// <summary>
    /// The root level of a scope chain — the prelude level every evaluation chain is rooted at
    /// (Lean <c>ScopeCtx.chainRoot</c>). A loaded module is wired there (see <see cref="WithParent"/>).
    /// </summary>
    private static ScopeCtx? ChainRoot(ScopeCtx? scope)
    {
        if (scope is null)
            return null;
        while (scope.Parent is { } outer)
            scope = outer;
        return scope;
    }

    /// <summary>
    /// The plain (non-activated) declaring scope of an algorithm, owned by it.
    /// Lean: <c>Algorithm.asScopeCtx</c>.
    /// </summary>
    private static ScopeCtx AsScopeCtx(Algorithm alg)
        => new(alg.Parent, alg.Opens, alg.Properties,
            ParameterPattern.CaptureNamesSkippingBarrenNodes(alg.ParameterPatterns)) { Owner = alg };

    /// <summary>
    /// Wires a selected branch body under its clause family for one call, publishing the
    /// matched pattern binders as the family scope's <see cref="ScopeCtx.Parameters"/> and
    /// the binders' bindings as its <see cref="ScopeCtx.Activation"/>: the body itself
    /// declares no parameters (binders bind by pattern matching), so this is the level at
    /// which the accessibility walk finds the owner of a binder-capturing member.
    /// Lean: <c>wireSelectedBranchBody</c>.
    /// </summary>
    private static Algorithm ChildOfConditionalCall(Algorithm callee, Algorithm body, IReadOnlyList<string> binderNames,
        EvalCtx ctx, ValEnv values)
    {
        var scope = new ScopeCtx(callee.Parent, callee.Opens, callee.Properties, binderNames)
        {
            Owner = callee,
            // A selected clause is an actual call of its family: the family scope's activation owns
            // the invocation (Lean: `wireSelectedBranchBody` records it under the invocation mark).
            Activation = ParameterActivation.Capture(binderNames, ctx, values, invoked: true),
        };
        return WithParent(body, scope);
    }

    /// <summary>Best-effort algorithm path for internal diagnostics.</summary>
    internal static string? TryGetAlgorithmPath(Algorithm algorithm)
    {
        if (algorithm.Parent is not { } scope)
            return null;

        var name = TryGetAlgorithmNameInScope(algorithm, scope);
        if (name is null)
            return null;

        var owner = scope.Owner;
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
            Parent: sc, ParameterPatterns: [], Opens: sc.Opens,
            Properties: [], Output: []);

    /// <summary>Lean: Algorithm.lookupProp (any visibility).</summary>
    private static Algorithm? LookupProp(Algorithm alg, string name, EvaluationBudget budget)
        => LookupPropBinding(alg, name, budget)?.Value;

    private static Property? LookupPropBinding(Algorithm alg, string name, EvaluationBudget budget)
        => budget.PropertyBindings.Lookup(alg.Properties, name);

    private static bool IsExported(Property property)
        => property.Exposure == PropertyExposure.Exported;

    /// <summary>
    /// The member-accessibility law after structural/open selection. Exported members need no
    /// ancestor activation. Captured members retain owner-relative requirements so transitive
    /// captures survive shadowing; diagnostic names alone use the host nearest-owner convention.
    /// Each required declaration and activation, including captured parents of static providers,
    /// must occur on the site's lexical chain. A live unrelated dynamic binding never qualifies.
    /// The owners are read on the container's chain in context (<see cref="ScopeInContext"/>), the
    /// chain the member is then wired under, where a static owner level is anchored to its
    /// activation on the site chain, and each must be ACTIVATED there: a static owner anchoring
    /// cannot reach (one above an activated level of the container's chain) refuses the access. So
    /// an accepted member reads its owner's bindings.
    /// A DETACHED owner activation refuses the access too (EXPORTED-DETACHED, November 2026,
    /// <see cref="IsDetached"/>): inside an exported evaluation the enclosing calls it detaches
    /// supply no inputs, so a local-only member one of them owns is inaccessible
    /// — the same <see cref="EvalError.LocalOnlyProperty"/>. <see cref="LexicalChainContains"/> needs
    /// no watermark of its own: the level it accepts carries the owner's own activation
    /// (<see cref="CompatibleActivations"/>), which this test has already found usable.
    /// Direct lexical hits already select on that chain. An admitted access is noted as an input read
    /// of the retained cell whose computation makes it (<see cref="AliasCellInputs.AdmitMemberAccess"/>) unless
    /// <paramref name="noteAdmission"/> is false: the <c>open</c> route's state-free judgments pass false
    /// — an <c>open</c>-provided name is noted where its selection is consumed (<see cref="AdmitOpenAccess"/>),
    /// an <c>open</c> target's path step is not noted (ledger R-1, open-target qualification).
    /// Lean: memberAccessible? (with <c>noteMemberAccess</c> at the noting callers).
    /// </summary>
    internal static bool IsAccessibleFrom(Property member, Algorithm container, EvalCtx ctx, bool noteAdmission = true)
    {
        if (IsExported(member))
            return true;
        if (member.Exposure != PropertyExposure.LocalOnlyCapturedAncestorParameters || ctx.Head is null)
            return false;

        var declaringScope = ScopeInContext(container, ctx);
        // Record all owners only after every access check succeeds (Lean: memberAccessActivations).
        var record = noteAdmission ? ctx.InputRecord : null;
        List<long>? used = null;
        if (member.CaptureRequirements is { } requirements)
        {
            foreach (var requirement in requirements)
            {
                var owner = declaringScope;
                for (var depth = 0; depth < requirement.OwnerDepth && owner is not null; depth++)
                    owner = owner.Parent;
                if (requirement.OwnerDepth < 0 || owner is null
                    || !ScopeBindsParameter(owner, requirement.Name)
                    || owner.Activation is not { } activation
                    || IsDetached(activation, ctx)
                    || !LexicalChainContains(ctx, owner))
                    return false;
                if (record is not null)
                    (used ??= []).Add(activation.Serial);
            }
            return record is null || record.AdmitMemberAccess(used);
        }
        foreach (var name in member.RequiredAncestorParameters)
        {
            if (RequiredParameterOwner(declaringScope, name) is not { } owner
                || owner.Activation is not { } activation
                || IsDetached(activation, ctx)
                || !LexicalChainContains(ctx, owner))
                return false;
            if (record is not null)
                (used ??= []).Add(activation.Serial);
        }

        return record is null || record.AdmitMemberAccess(used);
    }

    /// <summary>
    /// The scope owning parameter <paramref name="name"/> as seen from <paramref name="scope"/>:
    /// the nearest level, that scope itself first, whose parameters bind the name
    /// (<see cref="ScopeBindsParameter"/>: indexed on a wide activated level, scanned otherwise).
    /// Lean: <c>requiredParameterOwner?</c>.
    /// </summary>
    private static ScopeCtx? RequiredParameterOwner(ScopeCtx scope, string name)
    {
        for (var level = scope; level is not null; level = level.Parent)
        {
            if (ScopeBindsParameter(level, name))
                return level;
        }

        return null;
    }

    /// <summary>
    /// Whether the exact required owner activation is in the site's lexical chain: a level of
    /// the site scope's chain that is the same declaring scope, is itself activated, and
    /// agrees with every activation the owner names — its own and every captured ancestor's
    /// (<see cref="CompatibleActivations"/> starts at the owner itself). Static owners may
    /// match an active declaration only when their already captured ancestor activations
    /// agree. Runtime identity is separate from exported-property structural cache identity.
    /// Lean: <c>lexicalChainContains</c>.
    /// </summary>
    private static bool LexicalChainContains(EvalCtx ctx, ScopeCtx owner)
    {
        for (var level = SiteScope(ctx); level is not null; level = level.Parent)
        {
            if (IsSameDeclaringScope(level, owner)
                && level.Activation is not null
                && CompatibleActivations(owner, level))
                return true;
        }

        return false;
    }

    private static bool IsSameDeclaringScope(ScopeCtx? left, ScopeCtx? right)
    {
        while (left is not null && right is not null)
        {
            if (!IsSameDeclaringLevel(left, right))
                return false;

            left = left.Parent;
            right = right.Parent;
        }

        return left is null && right is null;
    }

    /// <summary>One level of <see cref="IsSameDeclaringScope"/>: the declaration and the binder view, parents aside.</summary>
    private static bool IsSameDeclaringLevel(ScopeCtx left, ScopeCtx right)
        => SameDeclarationBody(left, right)
            && IsSameScopeComponent(left.Opens, right.Opens)
            && IsSameScopeComponent(left.Properties, right.Properties)
            && SameParameterNames(left.Parameters, right.Parameters);

    /// <summary>
    /// Evaluator-created scopes carry the identity of their algorithm declaration across wiring
    /// (<see cref="ScopeCtx.Declaration"/>). Distinct declarations remain distinct even with
    /// shared output/property nodes or identical clause binders. An opaque host scope, or one
    /// owned by a builtin, carries no declaration and can establish identity only by being the
    /// same scope.
    /// </summary>
    private static bool SameDeclarationBody(ScopeCtx left, ScopeCtx right)
    {
        if (ReferenceEquals(left, right))
            return true;

        return left.Declaration is { } leftDeclaration
            && ReferenceEquals(leftDeclaration, right.Declaration);
    }

    private static bool IsSameScopeComponent<T>(IReadOnlyList<T> left, IReadOnlyList<T> right)
        => ReferenceEquals(left, right) || (left.Count == 0 && right.Count == 0);

    /// <summary>
    /// Parameter names are compared by content because projection and conditional matching
    /// create fresh lists. This checks the binder view of a declaration, not declaration identity.
    /// </summary>
    private static bool SameParameterNames(IReadOnlyList<string> left, IReadOnlyList<string> right)
    {
        if (ReferenceEquals(left, right)) return true;
        if (left.Count != right.Count) return false;
        for (var i = 0; i < left.Count; i++)
        {
            if (!string.Equals(left[i], right[i], StringComparison.Ordinal)) return false;
        }

        return true;
    }

    /// <summary>
    /// Whether an algorithm is ineligible as an open provider: an explicitly or implicitly
    /// parameterized algorithm or a clause family (even with a zero-arity branch). Such an algorithm
    /// is not an <c>open</c> provider under MOD-04 — <c>open</c> imports a namespace and never creates an
    /// activation. Every ALIAS that reaches the provider rule is a namespace (OD-C, M4★): a static
    /// transparent reference was normalized to its target's stratified structure first
    /// (<see cref="OpenStructure"/>), and a structural carrier or a runtime reference is its own
    /// namespace — <c>open</c> imports declarations, never a callable (Lean:
    /// <c>Algorithm.requiresArguments</c>). Despite the name, the parameter test is MOD-04's
    /// nonempty EFFECTIVE parameter list, not a minimum supplied arity: a collector-only
    /// <c>Only(*xs)</c> accepts an empty supply yet is refused here (X-27; Q-58 asks whether
    /// that strictness is intended).
    /// </summary>
    internal static bool RequiresArguments(Algorithm algorithm)
        => algorithm is Algorithm.Conditional
            || (algorithm is not Algorithm.Alias && algorithm.HasAnyParameter);

    private static EvalError OpenTargetRequiresArguments(string targetDescription, Algorithm provider)
        => new EvalError.IllegalInOpen(FormatOpenTargetRequiresArguments(targetDescription, provider));

    internal static string FormatOpenTargetRequiresArguments(string targetDescription, Algorithm provider, bool sourceBacked = false)
    {
        if (provider is Algorithm.Conditional)
            return $"'{targetDescription}' cannot be opened because it is a clause family, not a namespace.";

        // The front end reports this once per written target, so the provider's parameter list
        // is echoed bounded, reading only the names it shows (see ExprNameRenderer.BoundedJoin).
        var names = ExprNameRenderer.BoundedJoin(NamedParameters(provider, sourceBacked), ", ");
        // The rule that failed is MOD-04's EMPTY EFFECTIVE PARAMETER LIST (written, inferred and
        // lifted parameters all count), not a need for supplied arguments: a collector-only
        // `Only(*xs)` binds an empty supply and reads as a value, yet is still no provider (X-27).
        var parameterList = names.Length == 0 ? "" : $" (found: {names})";
        return $"'{targetDescription}' cannot be opened because open providers must have an empty effective parameter list{parameterList}.";
    }

    /// <summary>
    /// The parameter names a diagnostic may quote, lazily in declaration order: every parameter
    /// except the parser's spanless recovery binder for a malformed pattern item
    /// (`F(a, *) = …`), which is not source-backed and must never be named to the user. Only the
    /// front-end validator identifies recovery binders this way: a host-built algorithm keeps
    /// every name, regardless of which parameters the host supplied spans for. At most
    /// <see cref="ExprNameRenderer.MaxRenderedNameLength"/> declarations are examined — more
    /// names than a bounded list can show — so quoting a huge list costs a constant whatever
    /// the filter skips.
    /// </summary>
    private static IEnumerable<string> NamedParameters(Algorithm provider, bool sourceBacked)
    {
        if (provider is not Algorithm.User user)
            return [];

        var parameters = ParameterPattern.EnumerateCaptures(user.ParameterPatterns)
            .Take(ExprNameRenderer.MaxRenderedNameLength);

        // Only a WRITTEN (explicit) list can contain the recovery binder: an inferred
        // signature's captures are promoted names, every one of them nameable. The binder is
        // the list's one spanless declaration, under a unique name no source can write.
        return sourceBacked && user.HasExplicitParameterList
            ? parameters.Where(static parameter => parameter.Span is not null).Select(static parameter => parameter.Name)
            : parameters.Select(static parameter => parameter.Name);
    }

    /// <summary>
    /// The front-end wording for a prelude builtin named as an open target: the evaluator's
    /// open resolution refuses builtins by kind (<c>IllegalInOpen("builtin 'count'")</c>, Lean
    /// <c>resolveAlgForOpen</c>); the validator states the same rule in KatLang terms.
    /// </summary>
    internal static string FormatOpenTargetIsBuiltin(string targetDescription)
        => $"'{targetDescription}' cannot be opened because it is a builtin callable; open imports only an algorithm that needs no call.";

    /// <summary>
    /// Lean: Algorithm.lookupPropDefPublic? (public only — exposure is checked after selection): the
    /// provider's first public member of the name, through the run's index of a LARGE member list and an
    /// ordered scan of a small one (<see cref="PropertyBindingIndexCache.LookupPublic"/>), so one large opened
    /// module read R times costs R index probes rather than R scans of its members.
    /// </summary>
    private static Property? LookupPublicPropBinding(Algorithm alg, string name, PropertyBindingIndexCache bindings)
        => bindings.LookupPublic(alg.Properties, name);

    /// <summary>
    /// Human-readable constructor kind for diagnostics.
    /// Lean: Expr.kind.
    /// </summary>
    internal static string ExprKind(Expr e) => e switch
    {
        Expr.Param => "param",
        Expr.Num => "num",
        Expr.StringLiteral => "stringLiteral",
        Expr.BoolLiteral => "boolLiteral",
        Expr.Unary => "unary",
        Expr.Binary => "binary",
        Expr.Comparison => "comparison",
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
    /// The written-target key of an <c>open</c> target: a PRE-RESOLUTION OPTIMIZATION, never a
    /// provider identity (Q-19 D-I, decided 2026-10-06). Two targets with the same key resolve
    /// to the same provider by construction — one complete name spelling at one open level
    /// resolves one target — so a consumer may skip re-resolving a repeated key; whether two
    /// targets with DIFFERENT keys are one provider is decided after resolution by the semantic
    /// provider identity (<see cref="ResolveAllOpens"/>: <see cref="SameRepeatedCallableIdentity"/>;
    /// the front end: the <see cref="OpenProviderIdentity"/> that <see cref="ElaboratedScopeLookup.ResolveOpenProvider"/>
    /// resolves with each target). An INLINE target
    /// (<see cref="Expr.AlgorithmExpr"/> or <see cref="Expr.Capture"/>) is keyed by its written
    /// position, including when it heads a dotted path, so the skip never merges two written
    /// blocks. A name-headed path uses its COMPLETE spelling (ordinal comparison): diagnostic
    /// rendering is bounded and must never decide even this skip, because distinct long names can
    /// have the same abbreviated display. Invalid host/recovery forms retain their bounded
    /// diagnostic key; validation rejects them before lookup. A new inline-like form belongs in
    /// the positional arm here — nowhere else.
    /// </summary>
    internal static string OpenTargetDedupKey(Expr openExpr, int index)
    {
        var head = openExpr.OpenTargetHead(out var steps);
        if (head is Expr.AlgorithmExpr or Expr.Capture)
            return $"(inline#{index})";
        if (head is Expr.Resolve(var headName))
            return steps.Count == 0 ? headName : headName + "." + string.Join(".", steps);
        return OpenExprName(openExpr);
    }

    /// <summary>
    /// Renders a compound call-context expression on an actual diagnostic path and records that
    /// work for an observed run. Simple identifiers reuse their existing string.
    /// </summary>
    internal static string CallDiagnosticExprName(Expr expression, EvalCtx ctx)
        => CallDiagnosticName.FromExpression(expression).Render(ctx);

    /// <summary>
    /// <see cref="CallDiagnosticExprName"/> for the RECEIVER of a dot edge — the one
    /// description every <see cref="DotCallContext"/> carries (see
    /// <see cref="CallDiagnosticName.RenderAsDotReceiver"/>).
    /// </summary>
    internal static string DotReceiverDiagnosticExprName(Expr receiver, EvalCtx ctx)
        => CallDiagnosticName.FromExpression(receiver).RenderAsDotReceiver(ctx);

    /// <summary>
    /// Stack-only description of a callable's diagnostic name. Simple identifiers reuse their
    /// existing string; compound expressions retain the AST reference and are rendered only if an
    /// error actually needs the name. This avoids both a closure and diagnostic string allocation
    /// on successful resolved calls.
    /// </summary>
    internal readonly struct CallDiagnosticName
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
        /// True when this callee is a synthetic implementation frame rather than a
        /// user-semantic one — the parser's assignment-deconstruction target helper, the one
        /// callee it writes as an <see cref="Expr.AlgorithmExpr"/>. The generic call-context
        /// enrichment (<see cref="WithCallCtx{T}"/>, <see cref="CalleeResolutionFailure"/>)
        /// then attaches NOTHING and the error passes through with its own kind, payload, and
        /// span; the surrounding user-written frames are untouched. See
        /// <see cref="Algorithm.IsSyntheticDeconstructionFrame"/>.
        ///
        /// <para>Derived from the retained callee node rather than stored, for the same
        /// reason the name itself is: both callers consult it only AFTER an error, so the
        /// struct stays two references wide on the call-recursion spine (frame-size
        /// discipline) and a successful call pays nothing.</para>
        /// </summary>
        public bool IsDiagnosticallyTransparent
            => _expression is Expr.AlgorithmExpr(var algorithm)
                && Algorithm.IsSyntheticDeconstructionFrame(algorithm);

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

        /// <summary>
        /// This name as the RECEIVER of a dot edge (<see cref="ExprNameRenderer.RenderDotReceiver"/>):
        /// a prefix-form receiver keeps its parentheses, so a message that composes the
        /// description with the member reads back as the edge — <c>(-2).f</c>, never
        /// <c>-2.f</c>. Identifiers and every other receiver render as <see cref="Render"/> does.
        /// </summary>
        public string RenderAsDotReceiver(EvalCtx ctx)
        {
            if (_knownName is not null)
                return _knownName;

            ctx.Observations?.RecordCallDiagnosticNameRender();
            return ExprNameRenderer.RenderDotReceiver(_expression!);
        }
    }

    private static string BinaryExprDiagnosticName(BinaryOp op, Expr left, Expr right)
        => ExprNameRenderer.RenderBinaryDiagnosticName(op, left, right);

    private static string BinaryOperandContext(BinaryOp op, Expr left, Expr right)
        => $"while evaluating `{BinaryExprDiagnosticName(op, left, right)}`";

    /// <summary>
    /// The operand-shape context of ONE adjacent comparison of a chain — the two
    /// operands the link actually compares, never the whole chain and never a nested
    /// binary spelling: the failing link of <c>1 &lt; 2 &lt; true</c> is reported as
    /// <c>while evaluating `2 &lt; true`</c>. Lean: <c>comparisonLinkDiagnosticName</c>.
    /// </summary>
    private static string ComparisonLinkContext(ComparisonOp op, Expr left, Expr right)
        => $"while evaluating `{ExprNameRenderer.RenderComparisonLinkDiagnosticName(op, left, right)}`";

    // ── Error context helpers ──────────────────────────────────────────────

    private static ErrorContext CtxOpen(string key) => new OpenResolutionContext(key);
    private static ErrorContext CtxCall(CallDiagnosticName name, EvalCtx ctx) => new CallContext(name.Render(ctx));
    private static ErrorContext CtxProperty(string name) => new PropertyEvaluationContext(name);
    private static ErrorContext CtxDotCall(Expr obj, string name, EvalCtx ctx)
        => new DotCallContext(DotReceiverDiagnosticExprName(obj, ctx), name);

    // ── Error context helper ────────────────────────────────────────────────

    /// <summary>
    /// Attach context to any error raised by the given result.
    /// Lean: withCtx.
    /// </summary>
    private static EvalResult<T> WithCtx<T>(ErrorContext context, EvalResult<T> result) =>
        result.IsError && !result.Error.IsTerminalForRun
            ? new EvalError.WithContext(context, result.Error) { Span = result.Error.Span }
            : result;


    private static EvalResult<T> WithCtx<T>(string context, EvalResult<T> result)
        => WithCtx(new TextErrorContext(context), result);

    /// <summary>
    /// <see cref="WithCtx{T}(ErrorContext, EvalResult{T})"/> for call contexts, with
    /// the context CONSTRUCTED ONLY ON THE ERROR PATH: rendering the callee name is
    /// pure diagnostic work, so a successful call must not pay for it.
    ///
    /// <para>A DIAGNOSTICALLY TRANSPARENT callee attaches no frame at all
    /// (<see cref="CallDiagnosticName.IsDiagnosticallyTransparent"/>): the error passes
    /// through unchanged — same kind, same payload, same span — so the enclosing
    /// user-written frames keep their own order and nothing names an evaluator-generated
    /// helper.</para>
    /// </summary>
    private static EvalResult<T> WithCallCtx<T>(CallDiagnosticName function, EvalCtx ctx, EvalResult<T> result)
    {
        // A `map` / `filter` stage this call built reports its later steps under this call's
        // frame (lazy collections, issue #204; LazyList.StageSite).
        if (FreshStage(result) is { Site: null } stage)
            stage.NoteSiteFrame(function, null, ctx);
        return result.IsError && !result.Error.IsTerminalForRun && !function.IsDiagnosticallyTransparent
            ? new EvalError.WithContext(CtxCall(function, ctx), result.Error) { Span = result.Error.Span }
            : result;
    }

    /// <summary>
    /// <see cref="WithCtx{T}(ErrorContext, EvalResult{T})"/> for one iterated filter item,
    /// with the context CONSTRUCTED ONLY ON THE ERROR PATH (see <see cref="WithCallCtx{T}"/>).
    ///
    /// <para>This runs once per iterated item, and rendering the item is path-proportional on
    /// a shared value graph, so eagerly interpolating the message charged every PASSING
    /// predicate for a diagnostic nothing would ever read.</para>
    /// </summary>
    private static EvalResult<T> WithFilterItemCtx<T>(Result item, int index, EvalCtx ctx, EvalResult<T> result)
        => result.IsError && !result.Error.IsTerminalForRun
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
    {
        // A `map` / `filter` stage this dot call built reports its later steps under this
        // frame (lazy collections, issue #204; LazyList.StageSite).
        if (FreshStage(result) is { Site: null } stage)
            stage.NoteSiteFrame(null, dotCall, ctx);
        return result.IsError && !result.Error.IsTerminalForRun
            ? new EvalError.WithContext(
                CtxDotCall(dotCall.Target, dotCall.Name, ctx),
                result.Error)
            { Span = result.Error.Span }
            : result;
    }

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
    /// <see cref="WithSpan{T}"/> positioned by an expression, reading its span only when there IS
    /// an error to position. The recursive evaluation frame that awaits <paramref name="result"/>
    /// then holds a node reference instead of a span copy: a span is a 20-byte value as
    /// <c>SourceSpan?</c>, and one eager copy per dispatch arm measurably fattened every
    /// frame on the call-recursion spine (frame-size discipline, see the parser's leaf-frame
    /// helpers).
    /// </summary>
    internal static EvalResult<T> WithSpanOf<T>(Expr expr, EvalResult<T> result)
    {
        // The written call that built a `map` / `filter` stage positions the stage's later
        // spanless failures (lazy collections, issue #204; LazyList.StageSite).
        if (FreshStage(result) is { Site: { } site })
            site.NoteSpan(expr.Span);
        return result.IsError ? AtSpanIfMissing(result.Error, expr.Span) : result;
    }

    /// <summary>
    /// <see cref="WithSpanOf{T}"/> for a capture: the expression's own span, else the first
    /// positioned row of <paramref name="body"/> (<see cref="PreferExpressionSpan"/>), chosen on
    /// error only.
    /// </summary>
    private static EvalResult<T> WithPreferredSpanOf<T>(Expr expr, IReadOnlyList<Expr> body, EvalResult<T> result) =>
        result.IsError ? AtSpanIfMissing(result.Error, PreferExpressionSpan(expr.Span, body)) : result;

    /// <summary>
    /// Attaches a source span to an error that does not already carry one. The single
    /// implementation behind <see cref="WithSpan{T}"/> and the resource-limit charge
    /// points, which hold a bare <see cref="EvalError"/> rather than a result.
    /// </summary>
    private static EvalError AtSpanIfMissing(EvalError error, SourceSpan? span)
        => error.Span is null && span is not null ? error with { Span = span } : error;

    /// <summary>
    /// Blame the READ PROPERTY for an output-less value demand ("Property 'P' has no
    /// defined output"), positioning the report at the reference.
    ///
    /// <para><paramref name="resolvedAlgorithm"/> is the algorithm the name resolved to, and
    /// decides whether there is a user-semantic property to blame at all: the parser's hoisted
    /// <c>$deconstruct$N</c> deconstruction source is a DIAGNOSTICALLY TRANSPARENT frame
    /// (<see cref="Algorithm.IsSyntheticDeconstructionFrame"/>), so the failure stays the
    /// written right-hand side's own output-less error, at the right-hand side's own span,
    /// instead of naming a property nobody wrote. Pass <c>null</c> where the demanded
    /// algorithm is not at hand; the frame is then attached as before.</para>
    ///
    /// <para>Only the property's OWN missing output is blamed on it (<see cref="IsOwnForBlame"/>):
    /// <c>H2 = { } + 1</c> has an output, and its missing output is the <c>{ }</c> operand's
    /// (nested, Q-36), so the read passes it on with the reference's span attached only if it has
    /// none, and the report stays the operand's generic one at the operand's span.
    /// Lean: <c>withMissingOutputCtx</c>.</para>
    /// </summary>
    private static EvalResult<T> WithPropertyContextOnMissingOutput<T>(
        string name,
        SourceSpan? span,
        Algorithm? resolvedAlgorithm,
        EvalResult<T> result)
    {
        if (result.IsError
            && result.Error is EvalError.MissingOutput missing
            && IsOwnForBlame(missing)
            && !Algorithm.IsSyntheticDeconstructionFrame(resolvedAlgorithm))
        {
            return WithSpan<T>(span, new EvalError.WithContext(CtxProperty(name), result.Error));
        }

        return WithSpan(span, result);
    }

    /// <summary>
    /// THE ONE WRITTEN-ARGUMENT BLAME (F5). A written argument that was required to
    /// supply a value and produced no output is that ARGUMENT's failure: the error is
    /// attributed to the written expression and positioned at it, so no enclosing call
    /// or dot-call frame can claim it and render "Cannot call '<c>callee</c>' because it
    /// has no defined output" for a callee that is perfectly well formed
    /// (<c>count({ })</c>, <c>Coll({ })</c>, <c>if(c, { }, 2)</c>, <c>F(1 + { })</c>).
    ///
    /// <para>This is the unnamed half of the blame rule a NAMED argument already gets
    /// from its own evaluation (<see cref="WithPropertyContextOnMissingOutput{T}"/>,
    /// <c>WithParameterContextOnMissingOutput</c>); it applies to every other written
    /// shape. The structured kind and payload are unchanged — the innermost error stays
    /// <see cref="EvalError.MissingOutput"/> — and the span is attached only when the
    /// error has none, so a failing SUB-expression keeps its own precise location while
    /// the description names the argument the reader has to change.</para>
    ///
    /// <para>Distinctions this rule must not erase: an OMITTED argument is an arity
    /// failure before any of this (<c>F()</c>), a legitimate empty value is a value
    /// (<c>F([])</c>, <c>F(())</c>), and an explicit spread supplying zero items is a
    /// legal supply, not a missing output (<c>Coll(Empty*)</c>) — a spread operand
    /// without output is its own <see cref="EvalError.SpreadMissingOutput"/>.</para>
    /// </summary>
    private static EvalError BlameWrittenArgumentForMissingOutput(Expr source, EvalError error)
        => error is EvalError.MissingOutput
            ? AtSpanIfMissing(
                new EvalError.WithContext(new ArgumentEvaluationContext(OpenExprName(source)), error) { Span = error.Span },
                source.Span)
            : error;

    /// <summary>
    /// <see cref="BlameWrittenArgumentForMissingOutput"/> for a written call-argument
    /// SLOT, whose supplied computation is evaluated as an ordinary expression on its first
    /// VALUE demand (<c>SupplyCell</c>, Model C; until Model C at assembly, by the deleted
    /// <c>BuildCallArgumentInputs</c>). A NAME occurrence therefore already made its
    /// own blame decision during that evaluation — including the deliberate diagnostic
    /// TRANSPARENCY of the parser's hoisted deconstruction source, whose bare
    /// <see cref="EvalError.MissingOutput"/> must keep bubbling to the written
    /// assignment target (<see cref="Algorithm.IsSyntheticDeconstructionFrame"/>) — so
    /// only a shape that cannot self-blame is attributed here.
    /// </summary>
    private static EvalError BlameWrittenArgumentSlot(Expr source, EvalError error)
        => source is Expr.Resolve or Expr.Param
            ? error
            : BlameWrittenArgumentForMissingOutput(source, error);

    private static EvalResult<T> MissingImplicitArguments<T>(Algorithm wired, SourceSpan? span)
        => MissingImplicitArgumentsError(wired, span);

    /// <summary>
    /// The value-position rejection of a written brace block whose implicit
    /// parameters nobody can supply: the <see cref="Expr.AlgorithmExpr"/> arm of
    /// the zero-argument value-demand law
    /// (<see cref="ZeroArgumentValueDemandRejection"/>).
    /// </summary>
    private static EvalError MissingImplicitArgumentsError(Algorithm wired, SourceSpan? span)
    {
        // The per-occurrence names and notes, read output-sensitively: a shared capture-free group of a
        // host-built signature is expanded once, not once per path (exactly Params / Parameters otherwise).
        // The error and its context publish this list, so it is a read-only view of the fresh array (never the array).
        IReadOnlyList<string> paramNames = SafeReadOnlyCollection.Over(ParameterPattern.CaptureNamesSkippingBarrenNodes(wired.ParameterPatterns));
        var notes = ImplicitParameterProvenance.CollectFromPatterns(wired.ParameterPatterns);
        // The ordinary missing-arguments span is the demanded block (the root's
        // first output row). When the ONE unresolved parameter is the misspelled
        // member of a dot edge on a statically known receiver, the member token
        // is the precise location the report is about, so the error is positioned
        // there instead. A member token inside imported module content has no span
        // (an import view carries no source locations), so such a report keeps the
        // local demand span. Diagnostic position only: the structured error, its
        // context, and every multi-parameter or bare-name report are unchanged.
        var errorSpan = paramNames.Count == 1 && notes is [{ DotMemberOrigin: not null, Span: { } memberSpan }]
            ? memberSpan
            : span;
        var inner = new EvalError.UnresolvedImplicitParams(paramNames)
        {
            Span = errorSpan,
            InferredImplicitParameters = notes,
        };
        return new EvalError.WithContext(new ImplicitParameterContext(paramNames, 0), inner) { Span = errorSpan };
    }

    /// <summary>
    /// ONE zero-supply acceptability rule: whether an ORDINARY call that supplies ZERO
    /// argument slots can bind this callable. It is derived from the very binder and
    /// dispatch semantics such a call uses, never from parameter-list emptiness:
    /// <list type="bullet">
    ///   <item>a user algorithm accepts iff its top-level pattern list's
    ///   <see cref="ParameterPattern.MinimumSuppliedSlots"/> is zero — so
    ///   <c>Only(*xs)</c> accepts (<c>Only()</c> binds <c>xs = []</c>) while
    ///   <c>Head(x, *rest)</c>, <c>Tail(*rest, z)</c>, <c>P((x, *rest))</c>,
    ///   <c>P([x])</c> and <c>Pair(x, y)</c> do not. A COLLECTING parameter contributes
    ///   ZERO required slots; a nested pattern still consumes one, and binds ONE
    ///   supplied value of its own kind, never none;</item>
    ///   <item>a clause family accepts iff some branch's top-level pattern has arity
    ///   zero — exactly the branch <see cref="BindNeedFamilySupply"/> selects for an empty
    ///   argument list. A flat multi-binder core equivalent always has at least two
    ///   parameters, so it never accepts;</item>
    ///   <item>a BUILTIN never accepts (<c>sum()</c> is an arity error). Its rejection
    ///   stays owned by <see cref="EvalBuiltinValueCounted"/>, which is the very report
    ///   <c>sum()</c> produces, so <see cref="ZeroArgumentValueDemandRejection"/>
    ///   deliberately does not intercept builtins.</item>
    /// </list>
    /// The user-algorithm arm is the shared signature rule
    /// <see cref="ParameterPattern.AcceptsZeroSuppliedSlots"/>, which the front end's
    /// implicit lifting reads too (Q-03): a bare value reference to a callable this accepts
    /// is never rewritten into a fresh forwarding call, so every such reference reaches this
    /// law and the property cache.
    /// Lean: <c>Algorithm.acceptsZeroSuppliedArguments</c>.
    /// </summary>
    internal static bool AcceptsZeroSuppliedArguments(Algorithm algorithm)
        => algorithm switch
        {
            Algorithm.Builtin => false,
            Algorithm.Conditional conditional =>
                conditional.Branches.Any(static branch => branch.Pattern.TopLevelArity() == 0),
            Algorithm.User user => ParameterPattern.AcceptsZeroSuppliedSlots(user.ParameterPatterns),
            // An alias is decided by its TARGET: every binding lookup normalizes an alias before a
            // demand consults this law, and an alias that reaches a demand unnormalized (a written
            // block, a host tree) is normalized by the demand funnel, whose target demand then
            // applies the target's own rejection — so the alias itself never blocks the demand.
            Algorithm.Alias => true,
        };

    /// <summary>
    /// The ACCEPTANCE half of the ONE zero-argument value-demand law: <c>true</c> exactly
    /// when <see cref="ZeroArgumentValueDemandRejection"/> lets the demand proceed. That
    /// method returns <c>null</c> for precisely these two cases and a report for every
    /// other, so the halves cannot disagree, and stating it directly keeps the sites that
    /// only need the DECISION from building (and discarding) a report. It differs from
    /// <see cref="AcceptsZeroSuppliedArguments"/> only for a BUILTIN, which the law
    /// deliberately passes through to its own arity rejection. Used by the zero-argument
    /// structural member read (<see cref="EvalStructuralMemberRead"/> and its twin) and by
    /// the collection builtins' value slots. Lean: <c>acceptsZeroArgumentValueDemand</c>.
    /// </summary>
    internal static bool AcceptsZeroArgumentValueDemand(Algorithm algorithm)
        => algorithm is Algorithm.Builtin || AcceptsZeroSuppliedArguments(algorithm);

    /// <summary>
    /// The arity mismatch for a zero-argument value demand of a callable that cannot
    /// accept an empty supply. <c>Expected</c> is the callable's true MINIMUM supplied
    /// count (<see cref="ParameterPattern.MinimumSuppliedSlots"/>) — the same count its
    /// ordinary zero-argument call reports — never the flattened declared capture count,
    /// which claimed two for <c>Head(x, *rest)</c> and <c>P((x, y))</c> alike. The
    /// callee's inferred-implicit-parameter provenance rides along as diagnostic-only
    /// notes so the eventual message can point back at the unresolved identifiers the
    /// parameters came from (see <see cref="ImplicitParameterProvenance"/>).
    /// </summary>
    private static EvalError.ArityMismatch ZeroArgumentDemandArityMismatch(Algorithm callee)
        => new(ParameterPattern.MinimumSuppliedSlots(callee.ParameterPatterns), 0)
        {
            InferredImplicitParameters = ImplicitParameterProvenance.CollectFromPatterns(callee.ParameterPatterns),
        };

    /// <summary>
    /// The written shape through which an algorithm is demanded as a zero-argument
    /// VALUE; it selects the report of <see cref="ZeroArgumentValueDemandRejection"/>.
    /// Lean: the <c>source?</c> match of <c>zeroArgumentDemandError?</c>.
    /// </summary>
    private enum ZeroArgumentDemandShape
    {
        /// <summary>A lexical property reference <c>X</c> (<see cref="Expr.Resolve"/>).</summary>
        Property,

        /// <summary>An algorithm-channel parameter <c>x</c> (<see cref="Expr.Param"/>).</summary>
        Parameter,

        /// <summary>
        /// A structurally navigated member <c>A.M</c> (a <see cref="Expr.DotCall"/>
        /// receiver resolved through <see cref="ResolveDotReceiver"/>).
        /// </summary>
        StructuralMember,

        /// <summary>
        /// A written brace block (<see cref="Expr.AlgorithmExpr"/>) that is NOT a callable alias:
        /// an inline alias <c>{ F }</c> is reported as its written target reference
        /// (<see cref="ZeroArgumentValueDemandError"/>), never with this shape.
        /// </summary>
        Block,

        /// <summary>An anonymous or value-reified algorithm (no written source).</summary>
        Anonymous,
    }

    /// <summary>
    /// The ONE zero-argument value-demand law (its rejection half). It is consulted
    /// BEFORE an algorithm's body is entered wherever a resolved algorithm is
    /// demanded for its VALUE with zero explicit arguments: the value-position
    /// <c>Resolve</c>/<c>AlgorithmExpr</c> arms (both dispatch twins),
    /// every lazy builtin VALUE slot (<see cref="EvalResolvedArgumentCounted"/>: the
    /// <c>if</c> condition and branches, <c>while</c>/<c>repeat</c> initial state,
    /// the <c>repeat</c> count, <c>atoms</c>, <c>range</c>), and the ordinary-dot
    /// <c>string</c> intrinsic's receiver (<see cref="EvalDotStringReceiverAlgOutput"/>).
    /// The value-position <c>Param</c> read does NOT consult it: a parameter's value outcome
    /// was established when its argument slot was evaluated (through this law, at the
    /// written argument), and the read reuses that outcome (AT-MOST-ONCE ARGUMENT VALUE
    /// EVALUATION, <see cref="EvalParamCounted"/>).
    ///
    /// <para>ELIGIBILITY IS ARITY, NOT PARAMETER-LIST EMPTINESS (September 2026): a
    /// callable may satisfy a zero-argument value demand exactly when an ordinary call
    /// supplying zero arguments can bind it (<see cref="AcceptsZeroSuppliedArguments"/> —
    /// the binder's own <see cref="ParameterPattern.MinimumSuppliedSlots"/> rule and the
    /// family's zero-arity branch rule). So <c>Only(*xs) = xs</c> is demandable (a
    /// collecting parameter requires no supplied slot: <c>Only</c> and <c>Only()</c> both
    /// accept zero) while <c>Head(x, *rest)</c> still requires one supplied value and is
    /// rejected. The REPORT names that true minimum.</para>
    ///
    /// A conditional that cannot accept zero arguments cannot be accessed as a value
    /// (<see cref="ConditionalValueAccessError"/>); a property reports the
    /// property-context arity mismatch, a parameter or a navigated member the bare one,
    /// and a written block <see cref="EvalError.UnresolvedImplicitParams"/> — its OWN
    /// inferred parameters; an inline callable alias has none and is reported as its
    /// written target reference (<see cref="ZeroArgumentValueDemandError"/>). <c>null</c>
    /// means the demand may proceed to the algorithm's zero-argument value
    /// (<see cref="EvalZeroArgumentDemandOutputCounted"/>, which binds the accepted EMPTY
    /// supply first). The decision is the effective signature's alone — a body that would
    /// happen to succeed without its parameter is rejected all the same — and a builtin
    /// CALLBACK slot (<c>map</c>/<c>filter</c>/<c>reduce</c> steps, loop steps) supplies
    /// arguments and never consults this law. Lean: <c>zeroArgumentDemandError?</c>.
    /// </summary>
    private static EvalError? ZeroArgumentValueDemandRejection(
        ZeroArgumentDemandShape shape,
        string? name,
        SourceSpan? span,
        Algorithm algorithm)
    {
        // A builtin is deliberately NOT decided here: its zero-argument rejection is
        // owned by EvalBuiltinValueCounted (the very error `sum()` reports), and
        // intercepting it would replace that report with a parameter-list one.
        if (algorithm is Algorithm.Builtin)
            return null;

        if (AcceptsZeroSuppliedArguments(algorithm))
            return null;

        if (ConditionalValueAccessError(name ?? "conditional", algorithm) is { } conditionalError)
            return conditionalError with { Span = span };

        if (shape == ZeroArgumentDemandShape.Block)
            return MissingImplicitArgumentsError(algorithm, span);

        var arity = ZeroArgumentDemandArityMismatch(algorithm);
        return shape == ZeroArgumentDemandShape.Property
            ? AtSpanIfMissing(new EvalError.WithContext(CtxProperty(name!), arity), span)
            : arity with { Span = span };
    }

    /// <summary>
    /// <see cref="ZeroArgumentValueDemandRejection"/> keyed by the written expression
    /// the demanded algorithm was resolved from: a lexical reference, an
    /// algorithm-channel parameter, a dot receiver, a written block, or nothing
    /// (a value-reified argument, which carries no parameters). Every other written
    /// shape resolves to a zero-parameter thunk and is never rejected.
    ///
    /// <para>An inline CALLABLE ALIAS (<c>{ F }</c>, FWD-02) is binding indirection: it has
    /// no signature and no report of its own, so its rejected demand is exactly the one its
    /// written target reference <c>F</c> reports — the target's own contract (a user
    /// algorithm's arity, a family's <c>NoMatchingBranch</c>, a builtin's own arity error),
    /// never the written block's <see cref="EvalError.UnresolvedImplicitParams"/>, which would
    /// present the target's parameters as implicit parameters of the program (FA-OQ-1, owner
    /// decision Option B, 2026-10-10). The report is located at that reference, or at the
    /// written block when the reference carries no location (the attach-if-missing law).
    /// Every demand site judging a written block — value position, a spread operand, a builtin
    /// value slot, the <c>.string</c> receiver — reaches the alias through this one mapping.</para>
    /// Lean: <c>zeroArgumentDemandError?</c>.
    /// </summary>
    private static EvalError? ZeroArgumentValueDemandError(Expr? source, Algorithm algorithm)
        => source switch
        {
            Expr.AlgorithmExpr { Algorithm: Algorithm.Alias alias } =>
                ZeroArgumentValueDemandError(alias.Target, algorithm) is { } rejection
                    ? AtSpanIfMissing(rejection, source.Span)
                    : null,
            Expr.Resolve(var name) =>
                ZeroArgumentValueDemandRejection(ZeroArgumentDemandShape.Property, name, source.Span, algorithm),
            Expr.Param(var name) =>
                ZeroArgumentValueDemandRejection(ZeroArgumentDemandShape.Parameter, name, source.Span, algorithm),
            Expr.DotCall dotCall =>
                ZeroArgumentValueDemandRejection(ZeroArgumentDemandShape.StructuralMember, dotCall.Name, source.Span, algorithm),
            Expr.AlgorithmExpr =>
                ZeroArgumentValueDemandRejection(
                    ZeroArgumentDemandShape.Block,
                    name: null,
                    PreferExpressionSpan(source.Span, algorithm.Output),
                    algorithm),
            _ =>
                ZeroArgumentValueDemandRejection(ZeroArgumentDemandShape.Anonymous, name: null, source?.Span, algorithm),
        };

    /// <summary>
    /// Adds diagnostic-only inferred-parameter provenance to the terminal
    /// arity mismatch of an already-selected callee. Callback/pattern binders
    /// may wrap that mismatch in a precise binding context, so preserve the
    /// context chain and enrich only the existing terminal error kind.
    /// </summary>
    private static EvalError AttachImplicitParameterProvenance(EvalError error, Algorithm callee)
    {
        var notes = ImplicitParameterProvenance.CollectFromPatterns(callee.ParameterPatterns);
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
        // Indexed, in written order: a body's output is an OutputBundle, whose iterator-method
        // enumerator would cost one heap object per user call (2026-11 allocation attribution).
        for (var i = 0; i < output.Count; i++)
            if (output[i].Span is { } s) return s;
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
    private static Algorithm? LookupInParentsDirect(ScopeCtx sc, string name, EvaluationBudget budget)
    {
        for (ScopeCtx? current = sc; current is not null; current = current.Parent)
        {
            if (budget.PropertyBindings.Lookup(current.Properties, name) is { } prop)
                return WithParent(prop.Value, current);
        }

        return null;
    }

    /// <summary>
    /// Direct lexical lookup: local properties + parent chain only (no opens).
    /// Lean: lookupLexicalDirect (Option).
    /// </summary>
    private static Algorithm? LookupLexicalDirect(Algorithm alg, string name, EvaluationBudget budget)
    {
        var local = LookupProp(alg, name, budget);
        if (local is not null)
            return ChildOf(alg, local);

        return alg.Parent is { } sc ? LookupInParentsDirect(sc, name, budget) : null;
    }

    // ── Open resolution ─────────────────────────────────────────────────────

    /// <summary>
    /// Resolves an open expression to a library algorithm and applies the PROVIDER rule: the
    /// resolved provider — the whole target, never an intermediate of a dotted path — must
    /// need no call. A parameterized algorithm (explicit or inferred parameters) or a clause
    /// family has no members outside an activation, and <c>open</c> never creates one (there
    /// is no <c>open Lib(5)</c>), so it is refused with <see cref="EvalError.IllegalInOpen"/>;
    /// a parameterized HEAD is navigated by identity like any structural receiver
    /// (<c>open Lib.Sub</c> with <c>Lib(p)</c> opens a self-contained <c>Sub</c>), and a
    /// member of it that captures <c>p</c> is refused at the access by the accessibility law.
    /// Lean: resolveOpen → EvalM Algorithm.
    /// </summary>
    private static EvalResult<Algorithm> ResolveOpen(Expr openExpr, EvalCtx ctx, ref OpenStructureChase? chase)
    {
        var resolved = ResolveAlgForOpen(openExpr, ctx, ref chase);
        if (resolved.IsError)
            return resolved;

        // OD-C (M4★): a transparent reference opens its TARGET's namespace, under the target's own
        // provider identity (so `open A, Lib` with `A = Lib` is ONE provider).
        var provider = OpenStructure(resolved.Value, ctx, ref chase);
        if (provider.IsError)
            return AtSpanIfMissing(provider.Error, openExpr.Span);
        if (provider.Value is Algorithm.Builtin)
            return new EvalError.IllegalInOpen($"builtin '{OpenExprName(openExpr)}'") { Span = openExpr.Span };
        return RequiresArguments(provider.Value)
            ? OpenTargetRequiresArguments(OpenExprName(openExpr), provider.Value) with { Span = openExpr.Span }
            : provider;
    }

    /// <summary>
    /// THE STRATIFIED STRUCTURE OF AN OPEN TARGET (OD-C, M4★; Lean <c>openStructure</c>): a TRANSPARENT
    /// REFERENCE opens its target's namespace, resolved WITHOUT any <c>open</c> — the reference's static
    /// target is looked up DIRECTLY in the reference's own declarations and its declaring chain
    /// (<see cref="LookupLexicalDirect"/>, never an open, never the evaluation of anything), and its member
    /// steps navigate DECLARED members, each receiver read through this same structure — so resolving an
    /// open target never depends on an open: a target only an open provides is unresolved
    /// (<see cref="EvalError.UnknownName"/>). A structural CARRIER is its own namespace (its own public
    /// declarations; its output is never evaluated), and so is a RUNTIME reference — a parameter row, a
    /// parameter-rooted path, an <c>.Algorithm</c> link on a structural miss: its own namespace, so nothing
    /// is opened dynamically. Every non-alias is itself. Lean's tail recursion is a loop here; only a member
    /// step's receiver recurses, under the host-stack backstop.
    /// <para>Each alias on the current path, including an enclosing receiver walk, is identified by
    /// its host view and callable identity (<see cref="OpenStructureKey"/>). Revisiting it reports
    /// <see cref="AliasCycleMessage"/>. A receiver leaves the active path when it returns.</para>
    /// <para>Direct name lookups depend only on the reference and its declaring chain. Their ends live
    /// on the nearest declaring activation or the run. Member paths also read the opening site's
    /// activation and access watermark. Their successful ends live only for this resolution of one open
    /// list. Reference hops and publication of name-run ends observe the run's cancellation.</para>
    /// </summary>
    private static EvalResult<Algorithm> OpenStructure(Algorithm algorithm, EvalCtx ctx, ref OpenStructureChase? chase)
    {
        var mark = chase?.Mark ?? 0;
        var result = OpenStructureOnChain(algorithm, ctx, ref chase);
        // The first failure aborts the whole open list and drops its chase.
        if (result.IsError || chase is null)
            return result;
        return chase.Finish(mark, result.Value, ctx.Budget) is { } terminal ? terminal : result;
    }

    /// <summary>
    /// <see cref="OpenStructure"/> on the current chain <paramref name="chase"/> — null
    /// until the walk takes its first step, and the enclosing walk's chain for a member step's receiver.
    /// </summary>
    private static EvalResult<Algorithm> OpenStructureOnChain(Algorithm algorithm, EvalCtx ctx, ref OpenStructureChase? chase)
    {
        if (!System.Runtime.CompilerServices.RuntimeHelpers.TryEnsureSufficientExecutionStack())
            return new EvalError.EvaluationStackExhausted();

        for (var current = algorithm; ;)
        {
            if (current is not Algorithm.Alias { IsReference: true } reference)
                return EvalResult<Algorithm>.Ok(current);
            if (!StaticAliasTargets.IsStaticPath(reference.Target))
                return EvalResult<Algorithm>.Ok(current);

            if (reference.Target is Expr.Resolve)
            {
                var run = FollowOpenNameRun(reference, ctx, ref chase);
                if (run.IsError)
                    return run.Error;
                current = run.Value;
                continue;
            }

            if (ctx.Budget.CheckContinuation() is { } terminal)
                return terminal;
            chase ??= new OpenStructureChase();
            if (chase.MemberEnd(reference) is { } end)
            {
                ctx.Observations?.RecordOpenStructureRememberedEnd();
                return EvalResult<Algorithm>.Ok(end);
            }
            if (!chase.Visit(reference))
                return new EvalError.IllegalInEval(AliasCycleMessage);
            ctx.Observations?.RecordOpenStructureStep();

            var edges = new List<Expr.DotCall>();
            Expr head = reference.Target;
            while (head is Expr.DotCall { Args: null } edge)
            {
                edges.Add(edge);
                head = edge.Target;
            }
            edges.Reverse();

            Algorithm value;
            switch (head)
            {
                case Expr.Resolve(var name):
                    if (LookupLexicalDirect(reference, name, ctx.Budget) is not { } found)
                        return new EvalError.UnknownName(name) { Span = head.Span };
                    value = found;
                    break;
                case Expr.AlgorithmExpr(var block):
                    value = ChildOfInContext(reference, block, ctx);
                    break;
                default:
                    return new EvalError.IllegalInEval(AliasTargetNotStaticPathMessage(reference.Target)) { Span = reference.Target.Span };
            }

            foreach (var edge in edges)
            {
                var receiverR = OpenStructure(value, ctx, ref chase);
                if (receiverR.IsError)
                    return receiverR.Error;
                var receiver = receiverR.Value;
                var member = LookupPropBinding(receiver, edge.Name, ctx.Budget);
                if (member is null)
                {
                    // `X.Algorithm` on a structural miss is the intrinsic: a runtime link, its own namespace.
                    if (edge.Name == "Algorithm")
                        return EvalResult<Algorithm>.Ok(current);
                    return receiver.DefinesConditionalBranchProperty(edge.Name)
                        ? new EvalError.LocalOnlyProperty(OpenExprName(edge.Target), edge.Name, PropertyExposure.LocalOnlyConditionalAlgorithm) { Span = edge.Span }
                        : new EvalError.IllegalInEval(AliasTargetNotStaticPathMessage(reference.Target)) { Span = reference.Target.Span };
                }

                if (!IsAccessibleFrom(member, receiver, ctx, noteAdmission: false))
                    return LocalOnlyPropertyError(OpenExprName(edge.Target), member) with { Span = edge.Span };
                value = ChildOfInContext(receiver, member.Value, ctx);
            }

            current = value;
        }
    }

    /// <summary>
    /// A NAME RUN of <see cref="OpenStructure"/> from <paramref name="start"/>: while the walk stands on a
    /// transparent reference whose target is a bare name, the next algorithm is that name's direct lookup in the
    /// reference's own scope chain (<see cref="LookupLexicalDirect"/>). The run ends at the first algorithm that
    /// is not such a reference — a non-alias, a carrier, a runtime reference, or a reference whose target is a
    /// member path or a block, which the walk navigates itself — and every reference it passed remembers that end
    /// (<see cref="ReadOpenNameRunEnd"/>), so a later run reaching any of them jumps there. A run reaching a
    /// reference already on the current chain is the alias cycle; a failed run remembers nothing. Never inlined,
    /// so the walk's own recursive frame keeps its size.
    /// </summary>
    [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.NoInlining)]
    private static EvalResult<Algorithm> FollowOpenNameRun(Algorithm.Alias start, EvalCtx ctx, ref OpenStructureChase? chase)
    {
        List<(Dictionary<OpenStructureKey, Algorithm> Memo, OpenStructureKey Key)>? pending = null;
        Algorithm current = start;
        while (current is Algorithm.Alias { IsReference: true, Target: Expr.Resolve(var name) } reference)
        {
            if (ctx.Budget.CheckContinuation() is { } terminal)
                return terminal;
            if (ReadOpenNameRunEnd(reference, ctx.Budget, ref pending) is { } end)
            {
                ctx.Observations?.RecordOpenStructureRememberedEnd();
                current = end;
                break;
            }

            if (!(chase ??= new OpenStructureChase()).Visit(reference))
                return new EvalError.IllegalInEval(AliasCycleMessage);
            ctx.Observations?.RecordOpenStructureStep();
            if (LookupLexicalDirect(reference, name, ctx.Budget) is not { } found)
                return new EvalError.UnknownName(name) { Span = reference.Target.Span };
            current = found;
        }

        if (pending is not null)
        {
            foreach (var (memo, key) in pending)
            {
                if (ctx.Budget.CheckContinuation() is { } terminal)
                    return terminal;
                lock (memo)
                    memo.TryAdd(key, current);
            }
        }

        return EvalResult<Algorithm>.Ok(current);
    }

    /// <summary>
    /// The remembered end of the name run that starts at <paramref name="reference"/> (<see cref="FollowOpenNameRun"/>),
    /// or null after queueing its <see cref="OpenStructureKey"/> for the run's end;
    /// the entry lives on the nearest activation of that chain, or on the run when the chain has none
    /// (<see cref="AliasMemoOwner"/>), like the alias chase's static ends. A reference with declarations of its own
    /// (only a host-built one) is never remembered: its own declarations are part of its lookup. First wins under the
    /// memo's own lock: every run from one key computes the same end.
    /// </summary>
    private static Algorithm? ReadOpenNameRunEnd(
        Algorithm.Alias reference,
        Evaluation.EvaluationBudget run,
        ref List<(Dictionary<OpenStructureKey, Algorithm> Memo, OpenStructureKey Key)>? pending)
    {
        if (reference.Properties.Count != 0)
            return null;

        var memo = AliasMemoOwner(reference) is { } activation ? activation.OpenStructureEnds : run.OpenStructureEnds;
        var key = new OpenStructureKey(reference);
        lock (memo)
        {
            if (memo.TryGetValue(key, out var end))
                return end;
        }

        (pending ??= []).Add((memo, key));
        return null;
    }

    // The resolved algorithm carries its declaring scope. Two owners can share every property in a
    // host-built tree and still give the same member distinct provider identities. A host can also
    // make two views of one alias declaration with different targets or local declarations.
    internal readonly struct OpenStructureKey(Algorithm.Alias reference) : IEquatable<OpenStructureKey>
    {
        private readonly Algorithm.Alias _reference = reference;
        internal bool IsMemberPath => _reference.Target is Expr.DotCall;

        public bool Equals(OpenStructureKey other)
            => ReferenceEquals(_reference.Target, other._reference.Target)
                && ReferenceEquals(_reference.Properties, other._reference.Properties)
                && ReferenceEquals(_reference.Opens, other._reference.Opens)
                && ReferenceEquals(_reference.Declaration, other._reference.Declaration)
                && (ReferenceEquals(_reference.Parent, other._reference.Parent)
                    || SameRepeatedCallableIdentity(_reference, other._reference));

        public override bool Equals(object? obj) => obj is OpenStructureKey other && Equals(other);
        public override int GetHashCode() => HashCode.Combine(_reference.Declaration, _reference.Parent?.Declaration,
            System.Runtime.CompilerServices.RuntimeHelpers.GetHashCode(_reference.Target));
    }

    // All targets of one open list are resolved from one reader. A completed member path can be
    // reused here, including by a sibling receiver. The active path ends at each receiver return.
    private sealed class OpenStructureChase
    {
        private readonly HashSet<OpenStructureKey> _onChain = [];
        private readonly List<OpenStructureKey> _taken = [];
        private Dictionary<OpenStructureKey, Algorithm>? _memberEnds;

        /// <summary>The number of steps on the chain, where a receiver walk starts.</summary>
        internal int Mark => _taken.Count;

        /// <summary>Records a step on <paramref name="reference"/>; false when it is already on the chain (a cycle).</summary>
        internal bool Visit(Algorithm.Alias reference)
        {
            var visit = new OpenStructureKey(reference);
            if (!_onChain.Add(visit))
                return false;
            _taken.Add(visit);
            return true;
        }

        internal Algorithm? MemberEnd(Algorithm.Alias reference)
            => _memberEnds?.GetValueOrDefault(new OpenStructureKey(reference));

        internal EvalError? Finish(int mark, Algorithm end, EvaluationBudget budget)
        {
            for (var index = _taken.Count - 1; index >= mark; index--)
            {
                if (budget.CheckContinuation() is { } terminal)
                    return terminal;
                var step = _taken[index];
                _onChain.Remove(step);
                if (step.IsMemberPath)
                    (_memberEnds ??= []).TryAdd(step, end);
            }
            _taken.RemoveRange(mark, _taken.Count - mark);
            return null;
        }
    }

    /// <summary>
    /// A resolved open: its bounded diagnostic name, original expression, and resolved algorithm.
    /// Deduplication has already used the complete key. Lean's ResolvedOpen uses its
    /// unbounded spelling for both purposes; C# display limits are presentation policy.
    /// </summary>
    internal readonly record struct ResolvedOpen(string DisplayName, Expr Expr, Algorithm Lib);

    /// <summary>
    /// THE RESOLVED OPEN PROVIDERS OF ONE LEVEL STATE (implementation-only optimization, November 2026):
    /// <see cref="ResolveAllOpens"/>'s providers of a consulted level — written order, first
    /// representatives, display names — together with the level state they were resolved for, so the
    /// reads of that state resolve its targets ONCE instead of once per read.
    /// <para><b>What the providers depend on.</b> Resolving a level's opens reads the level's own opens,
    /// properties and parent chain and the activations ON that chain (target names are looked up directly
    /// on it, a dotted target navigates declared members, and every access check and in-context wiring
    /// compares the chain's declarations and activations by identity), plus the run's prelude level
    /// (the call stack's bottom, where an unparented inline block is wired). It evaluates nothing, reads no
    /// parameter value, projects no runtime alias and opens nothing (<see cref="OpenStructure"/>), charges
    /// no budget. Reference walks can observe cancellation. Each successfully resolved provider is a pure
    /// function of inputs fixed for a level object: a scope
    /// is immutable, its parent chain and activations are fixed at construction, host-owned lists may not
    /// change during a run (<see cref="Evaluation.PropertyBindingIndexCache"/>), and the prelude is the
    /// run's. So the providers are a PURE FUNCTION of the level object and the run, and the head's own level
    /// (resolved from the head with its head scope) and the same scope consulted as an ENCLOSING level
    /// (<see cref="ForOpens"/>: an empty level over it) resolve the same providers — the enclosing form only
    /// adds a bottom site level of a fresh declaration, which no lookup, access check or anchoring ever
    /// matches. Only a host-stack refusal depends on where a read runs, and a FAILED resolution is never
    /// memoized: a later read resolves again and reports the same first error in the same open frame at the
    /// same span.</para>
    /// <para><b>Where it lives.</b> On the level's runtime state, which a read already holds as the head
    /// scope or a level of the head's parent chain, and with that state's lifetime: an activated level's
    /// <see cref="ParameterActivation.OpenLevel"/>, or a static evaluator-owned level's own scope
    /// (<see cref="ScopeCtx.StaticOpenLevel"/>) — the static head level of a body entry
    /// (<see cref="EnterAlgorithmBody"/>), the head level of an alias step (<see cref="AliasStepContext"/>:
    /// one per evaluator wiring), the scope of a loop plan under construction, or a static wiring of a declaring scope. A
    /// host-constructed level (shared across runs and threads) has no such state and is resolved on every
    /// read, as before. A loop planner recognizes each written <c>if</c> in the step's scope. A prewired
    /// host parent can supply it through the step's opens, so these reads share the planning scope.
    /// Fully planned rounds read slots directly. A round that reads rows generically enters the step with
    /// its own activation. A clause family pushed for its binding is never the head of a read (the selected
    /// body is entered above it, under the family's activated scope). No table of providers outlives
    /// the state. A directly supplied alias without a wiring uses its memo owner's single spare head
    /// scope. <see cref="Level"/> and <see cref="Run"/> are checked on every reuse, so a <c>with</c>
    /// copy of a scope or a scope reached from another run resolves afresh.</para>
    /// <para><b>Selection.</b> A memoized wide level (more than <see cref="OpenProviderLinearIndexLimit"/>
    /// providers) that is read a SECOND time takes the RUN's index of its providers' PUBLIC members by name
    /// (<see cref="MemberIndex"/>), in provider order, each provider contributing its first public member of a
    /// name (<see cref="LookupPublicPropBinding"/>), so later reads find their hits without scanning every
    /// provider; a narrow, unmemoized or once-read level asks its providers in order, each through the run's
    /// index of a large member list (<see cref="Evaluation.PropertyBindingIndexCache.LookupPublic"/>, from
    /// <see cref="Evaluation.PropertyBindingIndexCache.MinimumIndexedPublicPropertyCount"/> members) or a scan
    /// of a small one. Either way a read sees exactly the ordered hits the scan sees. The member index is a
    /// function of the providers' member LISTS alone, never of the providers' wirings, so the run builds it
    /// once per distinct sequence of member lists and every later level state with the same lists — the next
    /// call of the same body, the next entry, round or member call — shares it
    /// (<see cref="OpenLevelMemberIndexCache"/>); it holds no provider, activation or value, so it gives no
    /// state a longer lifetime.</para>
    /// </summary>
    internal sealed class ResolvedOpenLevel
    {
        private readonly IReadOnlyList<ResolvedOpen> _providers;

        // The run's property indexes (Run.PropertyBindings), taken once here, so a read's provider walk loads a
        // field instead of inlining the run's lazily created table.
        private readonly PropertyBindingIndexCache _bindings;

        // A memoized wide level's member index, the run's (OpenLevelMemberIndexCache), taken by its second read
        // and published whole; the read count that decides it may race, which at worst takes the same index twice.
        private MemberIndex? _index;
        private int _reads;

        // The highest watermark these providers are known to stand under (AnswersWatermark).
        private long _resolvedUnder;

        internal ResolvedOpenLevel(ScopeCtx? level, Evaluation.EvaluationBudget run, IReadOnlyList<ResolvedOpen> providers,
            long resolvedUnder = 0)
        {
            Level = level;
            Run = run;
            _providers = providers;
            _bindings = run.PropertyBindings;
            _resolvedUnder = resolvedUnder;
        }

        /// <summary>
        /// Whether these providers answer a reader whose activation watermark is <paramref name="reader"/>
        /// (EXPORTED-DETACHED, November 2026; <see cref="EvalCtx.DetachedBefore"/>). Resolving a level's
        /// opens passes access checks that read the activations of the level's chain, and a watermark
        /// only ever REMOVES usable activations (<see cref="IsDetached"/>: at most those below it). The
        /// known bound starts at the watermark the resolution ran under, lowered below every activation of
        /// the chain that was still usable there although below it — the level of a returned callable
        /// (<see cref="OpenLevelResolutionBound"/>) — so every chain activation below the bound was
        /// unusable to the resolution. A successful resolution therefore answers every reader at or below
        /// the bound — the same checks pass with no fewer usable activations, and the providers are the
        /// same — and a reader ABOVE it exactly when no activation of the chain lies between the two
        /// watermarks; the known bound then rises, so the walk is paid once. Otherwise the reader resolves
        /// again in its own context (and a refused dotted target is its ordinary failure, memoized
        /// nowhere). A reader outside every exported evaluation (watermark zero) is always answered.
        /// </summary>
        internal bool AnswersWatermark(long reader)
        {
            var resolvedUnder = Volatile.Read(ref _resolvedUnder);
            if (reader <= resolvedUnder)
                return true;

            for (var scope = Level; scope is not null; scope = scope.Parent)
            {
                if (scope.Activation is { } activation && activation.Serial >= resolvedUnder && activation.Serial < reader)
                    return false;
            }

            // Racing readers each verified their own bound; whichever write lands is a verified one.
            Volatile.Write(ref _resolvedUnder, reader);
            return true;
        }

        /// <summary>The level state these providers were resolved for, or null for an unmemoized level.</summary>
        internal ScopeCtx? Level { get; }

        /// <summary>The run they were resolved in (its budget, one per run).</summary>
        internal Evaluation.EvaluationBudget Run { get; }

        /// <summary>The provider at <paramref name="position"/>, in written order.</summary>
        internal ResolvedOpen this[int position] => _providers[position];

        /// <summary>The providers publicly offering <paramref name="name"/>, in written order, for one read.</summary>
        internal OfferCursor Offers(string name, EvaluationObservations? observations)
        {
            var index = Volatile.Read(ref _index);
            if (index is null && Level is not null && _providers.Count > OpenProviderLinearIndexLimit && ++_reads > 1)
                index = TakeMemberIndex(observations);

            return new OfferCursor(this, name, index);
        }

        // The run's member index of these providers' member lists, built by the first level state of the run that
        // needs it (OpenLevelMemberIndexCache). Out of line: a level state pays for it once, on its second read.
        [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.NoInlining)]
        private MemberIndex TakeMemberIndex(EvaluationObservations? observations)
        {
            var index = Run.OpenLevelMemberIndexes.IndexOf(_providers, observations);
            Volatile.Write(ref _index, index);
            return index;
        }

        /// <summary>
        /// One read's walk over the offers of a name: the member index's chain when the level has one (taken
        /// once, at the read's start), else a scan of the providers in order.
        /// </summary>
        internal struct OfferCursor(ResolvedOpenLevel level, string name, MemberIndex? index)
        {
            private int _next = index is null ? 0 : index.FirstOffer(name);

            /// <summary>The position of the next provider publicly offering the name, with its member, or -1.</summary>
            internal int Next(out Property? binding)
            {
                if (index is not null)
                    return index.Offer(ref _next, out binding);

                var providers = level._providers;
                for (var position = _next; position < providers.Count; position++)
                {
                    if (LookupPublicPropBinding(providers[position].Lib, name, level._bindings) is { } found)
                    {
                        _next = position + 1;
                        binding = found;
                        return position;
                    }
                }

                _next = providers.Count;
                binding = null;
                return -1;
            }
        }

        /// <summary>
        /// The public members of a wide level's providers by name: the name's first offer, each offer chained
        /// to the next provider's offer of the same name (-1 ends a chain), in provider order. Built from the
        /// providers' member LISTS alone — the list of each position, which the index keeps as its key
        /// (<see cref="OpenLevelMemberIndexCache"/>) — so it serves every level state whose providers have the
        /// same lists in the same order: a position names the reading level's own provider, and a selected
        /// member is the list's own <see cref="Property"/>. A host-built list can hold PUBLIC members with a
        /// null name, which the ordered scan compares like any other name; they form their own chain. Immutable
        /// once built.
        /// </summary>
        internal sealed class MemberIndex
        {
            private readonly IReadOnlyList<Property>[] _lists;
            private readonly Dictionary<string, int> _firstOffer = new(StringComparer.Ordinal);
            // Private members and repeated names in one provider do not need offer storage.
            private readonly List<(int Provider, Property Binding, int Next)> _offers = [];
            private readonly int _firstUnnamedOffer;

            internal MemberIndex(IReadOnlyList<ResolvedOpen> providers)
            {
                _lists = new IReadOnlyList<Property>[providers.Count];
                // Built backwards, so each offer is prepended to its name's chain: providers last to first, and
                // each provider's members last to first, a later member of a name giving way to an earlier one.
                var firstUnnamed = -1;
                long members = 0;
                for (var position = _lists.Length - 1; position >= 0; position--)
                {
                    var list = providers[position].Lib.Properties;
                    _lists[position] = list;
                    var count = list.Count;
                    members += count;
                    for (var index = count - 1; index >= 0; index--)
                    {
                        var member = list[index];
                        if (!member.IsPublic)
                            continue;
                        bool known;
                        ref var first = ref firstUnnamed;
                        if (member.Name is { } memberName)
                            first = ref System.Runtime.InteropServices.CollectionsMarshal.GetValueRefOrAddDefault(
                                _firstOffer, memberName, out known);
                        else
                            known = first >= 0;
                        if (known && _offers[first].Provider == position)
                        {
                            _offers[first] = (position, member, _offers[first].Next);
                            continue;
                        }

                        _offers.Add((position, member, known ? first : -1));
                        first = _offers.Count - 1;
                    }
                }

                _firstUnnamedOffer = firstUnnamed;
                MemberCount = members;
            }

            /// <summary>The members of the providers' lists, public or not, that building this index visited.</summary>
            internal long MemberCount { get; }

            /// <summary>The member list of each provider, in provider order: the lists this index was built from.</summary>
            internal IReadOnlyList<Property>[] Lists => _lists;

            /// <summary>Whether this index was built from exactly the member lists of <paramref name="providers"/>, in order.</summary>
            internal bool IndexesListsOf(IReadOnlyList<ResolvedOpen> providers)
            {
                if (providers.Count != _lists.Length)
                    return false;
                for (var position = 0; position < _lists.Length; position++)
                {
                    if (!ReferenceEquals(providers[position].Lib.Properties, _lists[position]))
                        return false;
                }

                return true;
            }

            /// <summary>The first offer of <paramref name="name"/> (a null name: of an unnamed host-built member), or -1.</summary>
            internal int FirstOffer(string name)
                => name is null ? _firstUnnamedOffer : _firstOffer.TryGetValue(name, out var first) ? first : -1;

            /// <summary>The provider position of the offer at <paramref name="cursor"/>, advancing it, or -1 at a chain's end.</summary>
            internal int Offer(ref int cursor, out Property? binding)
            {
                if (cursor < 0)
                {
                    binding = null;
                    return -1;
                }

                var offer = _offers[cursor];
                cursor = offer.Next;
                binding = offer.Binding;
                return offer.Provider;
            }
        }
    }

    /// <summary>
    /// THE RUN'S MEMBER INDEXES OF WIDE OPEN LEVELS (implementation-only optimization, November 2026): one
    /// <see cref="ResolvedOpenLevel.MemberIndex"/> per distinct SEQUENCE of provider member lists, built by
    /// the first wide level state of the run that is read twice and taken by every later one whose providers
    /// have the same lists in the same order. A level's providers are resolved once per level STATE — per
    /// call, entry, round, alias wiring or member call (<see cref="ResolvedOpenLevel"/>) — and the index used
    /// to be built per state as well, so <c>C</c> calls through one level of providers with <c>M</c> members
    /// in all visited <c>C·M</c> members; now the run visits <c>M</c> once and each later state compares its
    /// <c>K</c> member lists with the last index served, or hashes them.
    /// <para><b>Why sharing is exact.</b> The index reads nothing but the lists — each member's name and
    /// visibility, in list order — and host-owned lists may not change during a run
    /// (<see cref="Evaluation.PropertyBindingIndexCache"/>), so two states whose providers have the same lists
    /// index the same offers. It stores provider POSITIONS and the lists' own members: the reading state
    /// supplies the provider at a position (its wiring, display name and identity) and the access check and
    /// wiring stay per read, in the reading context, so providers, order, precedence, ambiguity and errors are
    /// the scan's. Different lists, or the same lists in another order, are another key.</para>
    /// <para><b>Lifetime.</b> Run-scoped (<see cref="Evaluation.EvaluationBudget.OpenLevelMemberIndexes"/>), like
    /// the run's index of one large member list (<see cref="Evaluation.PropertyBindingIndexCache.LookupPublic"/>):
    /// a new run builds new indexes, so host edits between runs stay visible. An entry keeps only member lists
    /// and their members — the declarations' own, never a provider, scope, activation or value — so no frame
    /// outlives its state through it, and there is one entry per distinct sequence of lists the run's wide
    /// levels resolve to, not one per call. Unmemoized levels (a host-constructed level, a head pushed without
    /// a head scope) never reach it.</para>
    /// <para>Sequential lookups need no lock, but the cache follows the run's other shared preparation table
    /// (<see cref="NeedFamilyPreparationCache"/>): the last index served is read without the lock, the table
    /// under it, and an index is built outside it, the first published one winning.</para>
    /// </summary>
    internal sealed class OpenLevelMemberIndexCache
    {
        // The last index served: repeated calls through one level take it without hashing or locking.
        // Indexes are immutable, so a racing reader sees a complete one.
        private ResolvedOpenLevel.MemberIndex? _last;
        private readonly Dictionary<IReadOnlyList<Property>[], ResolvedOpenLevel.MemberIndex> _indexes;
        private readonly Dictionary<IReadOnlyList<Property>[], ResolvedOpenLevel.MemberIndex>.AlternateLookup<IReadOnlyList<ResolvedOpen>> _byProviders;

        internal OpenLevelMemberIndexCache()
        {
            _indexes = new(MemberListsComparer.Instance);
            _byProviders = _indexes.GetAlternateLookup<IReadOnlyList<ResolvedOpen>>();
        }

        /// <summary>
        /// The run's member index of the member lists of <paramref name="providers"/>, built now if no level
        /// state of the run has needed it yet; <paramref name="observations"/> records a build or a share.
        /// </summary>
        internal ResolvedOpenLevel.MemberIndex IndexOf(IReadOnlyList<ResolvedOpen> providers, EvaluationObservations? observations)
        {
            if (Volatile.Read(ref _last) is { } last && last.IndexesListsOf(providers))
            {
                observations?.RecordOpenLevelMemberIndex(built: false, members: 0);
                return last;
            }

            ResolvedOpenLevel.MemberIndex? found;
            lock (_indexes)
                _byProviders.TryGetValue(providers, out found);
            var built = false;
            if (found is null)
            {
                // Built outside the lock: a pure function of the lists; a racing equal index is discarded.
                var index = new ResolvedOpenLevel.MemberIndex(providers);
                lock (_indexes)
                {
                    if (!_byProviders.TryGetValue(providers, out found))
                    {
                        _indexes.Add(index.Lists, index);
                        found = index;
                        built = true;
                    }
                }
            }

            observations?.RecordOpenLevelMemberIndex(built, built ? found.MemberCount : 0);
            Volatile.Write(ref _last, found);
            return found;
        }

        /// <summary>The number of member indexes this run has built; a test observation.</summary>
        internal int Count
        {
            get
            {
                lock (_indexes)
                    return _indexes.Count;
            }
        }

        // Keys are the member lists of a level's providers, in order, compared by reference; a level's providers
        // look their key up without copying it out.
        private sealed class MemberListsComparer
            : IEqualityComparer<IReadOnlyList<Property>[]>, IAlternateEqualityComparer<IReadOnlyList<ResolvedOpen>, IReadOnlyList<Property>[]>
        {
            internal static readonly MemberListsComparer Instance = new();

            public bool Equals(IReadOnlyList<Property>[]? left, IReadOnlyList<Property>[]? right)
            {
                if (ReferenceEquals(left, right))
                    return true;
                if (left is null || right is null || left.Length != right.Length)
                    return false;
                for (var position = 0; position < left.Length; position++)
                {
                    if (!ReferenceEquals(left[position], right[position]))
                        return false;
                }

                return true;
            }

            public int GetHashCode(IReadOnlyList<Property>[] lists)
            {
                var hash = new HashCode();
                foreach (var list in lists)
                    hash.Add(System.Runtime.CompilerServices.RuntimeHelpers.GetHashCode(list));
                return hash.ToHashCode();
            }

            public bool Equals(IReadOnlyList<ResolvedOpen> providers, IReadOnlyList<Property>[] lists)
            {
                if (providers.Count != lists.Length)
                    return false;
                for (var position = 0; position < lists.Length; position++)
                {
                    if (!ReferenceEquals(providers[position].Lib.Properties, lists[position]))
                        return false;
                }

                return true;
            }

            public int GetHashCode(IReadOnlyList<ResolvedOpen> providers)
            {
                var hash = new HashCode();
                for (var position = 0; position < providers.Count; position++)
                    hash.Add(System.Runtime.CompilerServices.RuntimeHelpers.GetHashCode(providers[position].Lib.Properties));
                return hash.ToHashCode();
            }

            public IReadOnlyList<Property>[] Create(IReadOnlyList<ResolvedOpen> providers)
            {
                var lists = new IReadOnlyList<Property>[providers.Count];
                for (var position = 0; position < lists.Length; position++)
                    lists[position] = providers[position].Lib.Properties;
                return lists;
            }
        }
    }

    /// <summary>
    /// Resolve all opens of an algorithm upfront: the level's PROVIDERS, each counted once.
    /// Q-19 D-I (decided 2026-10-06): written targets that resolve to the same semantic
    /// provider count once, whatever their spelling or position — the provider identity is the
    /// language's one callable identity (NEED-04's relation, <see cref="SameRepeatedCallableIdentity"/>:
    /// the declaration, its declaring scope, and compatible activations), so <c>open M, M</c>,
    /// <c>open M, (M)</c>, <c>open Sub, Lib.Sub</c> (one declaration) and two loads of one module
    /// are one provider, while two written blocks, two declarations, or two canonical module URLs
    /// stay two, however equal their members or values. The first occurrence supplies the
    /// provider's diagnostic name; which providers the level has never depends on order.
    /// A repeated written-target key (<see cref="OpenTargetDedupKey"/>) is skipped before
    /// resolution as a pure optimization (it resolves the same target). Validates all open
    /// expressions first for fail-fast diagnostics, then resolves every remaining target in
    /// written order — the first failure, with its open frame and span, is the level's error —
    /// and only then counts the providers (<see cref="DeduplicateResolvedProviders"/>), as Lean
    /// resolves the whole list before its fold.
    /// Lean: resolveAllOpens → EvalM (List ResolvedOpen).
    /// </summary>
    private static EvalResult<IReadOnlyList<ResolvedOpen>> ResolveAllOpens(
        Algorithm alg, EvalCtx ctx)
    {
        if (alg.Opens.Count == 0)
            return EvalResult<IReadOnlyList<ResolvedOpen>>.Ok([]);

        // Skip a repeated written-target key (it resolves the same target); inline blocks use
        // positional keys, so this never merges two written blocks.
        var seen = new HashSet<string>();
        var deduped = new List<(string DisplayName, Expr Expr)>();
        for (var i = 0; i < alg.Opens.Count; i++)
        {
            var openExpr = alg.Opens[i];
            var key = OpenTargetDedupKey(openExpr, i);
            if (seen.Add(key))
                deduped.Add((openExpr is Expr.AlgorithmExpr or Expr.Capture ? key : OpenExprName(openExpr), openExpr));
        }

        // Validate all open expressions first (fail-fast with clear errors)
        foreach (var (displayName, openExpr) in deduped)
        {
            if (!openExpr.IsCoreOpenForm())
                return new EvalError.BadOpenForm($"{ExprKind(openExpr)}: {displayName}");
        }

        // Then resolve every target in written order with its bounded diagnostic name; the
        // first failure is the level's error.
        var result = new List<ResolvedOpen>(deduped.Count);
        OpenStructureChase? chase = null;
        foreach (var (displayName, openExpr) in deduped)
        {
            var libResult = WithCtx(
                CtxOpen(displayName),
                ResolveOpen(openExpr, ctx, ref chase));
            if (libResult.IsError) return libResult.Error;
            result.Add(new ResolvedOpen(displayName, openExpr, libResult.Value));
        }

        // Count each semantic provider once: a target resolving to the callable identity of an
        // earlier one is that provider.
        DeduplicateResolvedProviders(result, ctx.Observations);
        return EvalResult<IReadOnlyList<ResolvedOpen>>.Ok(result);
    }

    /// <summary>
    /// The widest open level whose providers <see cref="DeduplicateResolvedProviders"/> scans
    /// linearly by declaration key: allocation-free and at most 28 reference comparisons. A wider
    /// level indexes its declarations in a hash table.
    /// </summary>
    internal const int OpenProviderLinearIndexLimit = 8;

    /// <summary>Provider deduplication work of one level, for <see cref="EvaluationObservations"/>.</summary>
    private struct OpenProviderIndexWork
    {
        internal int KeyComparisons;
        internal int IdentityComparisons;
        internal int CrossDeclarationIdentityComparisons;
    }

    /// <summary>
    /// Q-19 D-I's provider count over one level's resolved targets, IN PLACE: keeps the first target
    /// of each semantic provider in written order and drops every later target whose provider is the
    /// callable identity of an accepted one (<see cref="SameRepeatedCallableIdentity"/>, the accepted
    /// provider first). The kept list is the level's providers, each named by its first target.
    /// <para><b>The declaration index</b> (implementation-only optimization, November 2026). A
    /// successful <see cref="ResolveOpen"/> never yields a builtin; every other algorithm carries a
    /// <see cref="Algorithm.Declaration"/> fixed at construction and shared by its <c>with</c> copies;
    /// and the identity of two non-builtins holds only for one object or for one declaration
    /// reference. A target is therefore compared only with the accepted targets of its OWN
    /// declaration, in acceptance order: an accepted target of another declaration could never have
    /// matched, so skipping it hides nothing, and the kept list — members, first representatives,
    /// display names and order — is the one the former scan over every accepted provider kept. The
    /// declaring scope and activations still decide inside a declaration, so one block under two
    /// host levels stays two providers.</para>
    /// <para>Work per level of <c>K</c> targets: <c>K</c> index probes and no identity comparison
    /// across declarations (formerly <c>K(K−1)/2</c> for <c>K</c> distinct declarations), plus the
    /// comparisons inside each declaration's reaches — at most <c>B(B−1)/2</c> for <c>B</c> reaches
    /// of one declaration, each a declaring-chain walk. Resolving the targets costs what it did; a level
    /// state is resolved, and so deduplicated, once (<see cref="ResolvedOpenLevel"/>), not once per read.
    /// Reported to <paramref name="observations"/>.</para>
    /// </summary>
    private static void DeduplicateResolvedProviders(List<ResolvedOpen> resolved, EvaluationObservations? observations)
    {
        var work = new OpenProviderIndexWork();
        var entries = resolved.Count;
        if (entries > 1)
        {
            var accepted = entries <= OpenProviderLinearIndexLimit
                ? DeduplicateByDeclarationScan(resolved, ref work)
                : DeduplicateByDeclarationTable(resolved, ref work);
            resolved.RemoveRange(accepted, entries - accepted);
        }

        observations?.RecordOpenProviderIndexing(entries, work.KeyComparisons, work.IdentityComparisons, work.CrossDeclarationIdentityComparisons);
    }

    /// <summary>
    /// <see cref="DeduplicateResolvedProviders"/> for a narrow level: each target scans the accepted
    /// targets' declaration keys in order and compares identity with those of its own declaration.
    /// Returns the number of accepted targets, moved to the front in order.
    /// </summary>
    private static int DeduplicateByDeclarationScan(List<ResolvedOpen> resolved, ref OpenProviderIndexWork work)
    {
        var accepted = 0;
        for (var i = 0; i < resolved.Count; i++)
        {
            var candidate = resolved[i];
            var declaration = ProviderDeclaration(candidate.Lib);
            var duplicate = false;
            for (var j = 0; j < accepted && !duplicate; j++)
            {
                work.KeyComparisons++;
                var earlier = resolved[j].Lib;
                if (ReferenceEquals(earlier.Declaration, declaration))
                    duplicate = SameResolvedProvider(earlier, candidate.Lib, ref work);
            }

            if (!duplicate)
                resolved[accepted++] = candidate;
        }

        return accepted;
    }

    /// <summary>
    /// <see cref="DeduplicateResolvedProviders"/> for a wide level: a hash table maps each declaration
    /// to its first accepted target, and the later accepted targets of the same declaration are
    /// chained after it in acceptance order (<c>next</c>: position + 1, 0 ends the chain; allocated
    /// only once some declaration keeps a second provider). Returns the number of accepted targets,
    /// moved to the front in order.
    /// </summary>
    private static int DeduplicateByDeclarationTable(List<ResolvedOpen> resolved, ref OpenProviderIndexWork work)
    {
        var firstOfDeclaration = new Dictionary<DeclarationIdentity, int>(resolved.Count);
        int[]? next = null;
        var accepted = 0;
        for (var i = 0; i < resolved.Count; i++)
        {
            var candidate = resolved[i];
            ref var first = ref System.Runtime.InteropServices.CollectionsMarshal.GetValueRefOrAddDefault(
                firstOfDeclaration, ProviderDeclaration(candidate.Lib), out var known);
            if (!known)
            {
                first = accepted;
                resolved[accepted++] = candidate;
                continue;
            }

            var position = first;
            var duplicate = false;
            while (true)
            {
                if (SameResolvedProvider(resolved[position].Lib, candidate.Lib, ref work))
                {
                    duplicate = true;
                    break;
                }

                var successor = next is null ? 0 : next[position];
                if (successor == 0)
                    break;
                position = successor - 1;
            }

            if (duplicate)
                continue;
            next ??= new int[resolved.Count];
            next[position] = accepted + 1;
            resolved[accepted++] = candidate;
        }

        return accepted;
    }

    /// <summary>The index key of a resolved provider: its declaration (a builtin never resolves as one).</summary>
    private static DeclarationIdentity ProviderDeclaration(Algorithm provider)
        => provider.Declaration
            ?? throw new System.Diagnostics.UnreachableException("Q-19: a resolved open provider is never a builtin, so it carries its declaration.");

    /// <summary>Whether <paramref name="provider"/> is the semantic provider of the accepted <paramref name="earlier"/> (Q-19 D-I).</summary>
    private static bool SameResolvedProvider(Algorithm earlier, Algorithm provider, ref OpenProviderIndexWork work)
    {
        work.IdentityComparisons++;
        if (!ReferenceEquals(earlier.Declaration, provider.Declaration))
            work.CrossDeclarationIdentityComparisons++;
        return SameRepeatedCallableIdentity(earlier, provider);
    }

    /// <summary>
    /// Searches opened namespaces for a name using public-only property lookup.
    /// Returns Ok(null) if no open provides the name publicly.
    /// Returns Ok(alg) if exactly one open provides it publicly and the site may use it.
    /// Returns Err(AmbiguousOpen) if multiple opens provide it publicly.
    /// Returns Err(LocalOnlyProperty) if the one provided member is local-only and the
    /// site lies outside an owner of what it captures.
    /// SELECTION IS BY VISIBILITY ONLY: a public member is provided by its open whatever its
    /// exposure (it takes part in precedence and ambiguity like any provided name), and
    /// accessibility is checked on the selected member afterwards (<see cref="IsAccessibleFrom"/>),
    /// so which declaration a name selects never depends on exposure and the front end can
    /// reproduce the selection before exposure is classified.
    /// The level's providers are resolved once per level state and reused by every later read of it
    /// (<see cref="ResolvedOpenLevel"/>); the hits, the access check and the wiring of the selected
    /// member stay per read, in the reading context.
    /// Lean: lookupOpenProperties → EvalM (Option ResolvedProperty).
    /// </summary>
    private static EvalResult<ResolvedLexicalProperty?> LookupOpens(
        Algorithm alg, string name, EvalCtx ctx)
    {
        if (alg.Opens.Count == 0) return EvalResult<ResolvedLexicalProperty?>.Ok(null);

        var level = HeadOpenLevel(alg, ctx);
        return level.IsError ? level.Error : SelectOpenHit(level.Value, name, ctx);
    }

    /// <summary>
    /// The resolved providers of the HEAD's own level (<paramref name="alg"/>, the context's head: every
    /// lexical lookup starts there). Its level state is the head scope when the head was entered with one
    /// that describes it (<see cref="EnterAlgorithmBody"/>: an activated scope or the static head level);
    /// a head pushed without one is resolved on every read.
    /// </summary>
    private static EvalResult<ResolvedOpenLevel> HeadOpenLevel(Algorithm alg, EvalCtx ctx)
    {
        var level = ctx.HeadScope is { } headScope && ReferenceEquals(headScope.Owner, alg) && ReferenceEquals(ctx.Head, alg)
            ? headScope
            : null;
        System.Diagnostics.Debug.Assert(level is null
            || (ReferenceEquals(level.Opens, alg.Opens) && ReferenceEquals(level.Properties, alg.Properties) && ReferenceEquals(level.Parent, alg.Parent)),
            "A head scope describes its owner: the same opens, properties and parent chain.");
        if (level is not null && MemoizedOpenLevel(level, ctx) is { } memoized)
            return EvalResult<ResolvedOpenLevel>.Ok(memoized);

        return ResolveOpenLevel(alg, level, ctx);
    }

    /// <summary>
    /// The resolved providers of the ENCLOSING level <paramref name="scope"/> of the head's parent chain,
    /// consulted through an empty level over it (<see cref="ForOpens"/>). An evaluator-owned level is its
    /// own level state (memoized on its activation or on itself); an ownerless host level, which may be
    /// shared across runs and threads, is resolved on every read.
    /// </summary>
    private static EvalResult<ResolvedOpenLevel> EnclosingOpenLevel(ScopeCtx scope, EvalCtx ctx)
    {
        var level = scope.Owner is not null ? scope : null;
        if (level is not null && MemoizedOpenLevel(level, ctx) is { } memoized)
            return EvalResult<ResolvedOpenLevel>.Ok(memoized);

        return ResolveOpenLevel(ForOpens(scope), level, ctx);
    }

    /// <summary>The memoized providers of <paramref name="level"/> for this run, or null (<see cref="ResolvedOpenLevel"/>).</summary>
    private static ResolvedOpenLevel? MemoizedOpenLevel(ScopeCtx level, EvalCtx ctx)
    {
        var memo = level.Activation is { } activation ? activation.OpenLevel : level.StaticOpenLevel;
        if (memo is null || !ReferenceEquals(memo.Level, level) || !ReferenceEquals(memo.Run, ctx.Budget)
            || !memo.AnswersWatermark(ctx.DetachedBefore))
            return null;

        ctx.Observations?.RecordOpenLevelConsultation(reused: true);
        return memo;
    }

    /// <summary>
    /// Resolves the opens of <paramref name="opener"/> — the head, or the empty level over an enclosing
    /// scope — and memoizes the providers on <paramref name="level"/> when it has a level state. A failure
    /// is returned as it is and memoized nowhere. Kept out of line: only a level's first read pays for it.
    /// </summary>
    [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.NoInlining)]
    private static EvalResult<ResolvedOpenLevel> ResolveOpenLevel(Algorithm opener, ScopeCtx? level, EvalCtx ctx)
    {
        ctx.Observations?.RecordOpenLevelConsultation(reused: false);

        // The opens are resolved from the consulted level as its own site: the head keeps
        // its activated scope (a dotted target's captured member is judged from inside the
        // head's activation), a parent-chain wrapper is its plain scope.
        // Lean: `{ ctx.push a with headScope := some (scopeInContext a ctx) }`.
        var innerCtx = ctx.Push(opener, ScopeInContext(opener, ctx));
        var resolvedResult = ResolveAllOpens(opener, innerCtx);
        if (resolvedResult.IsError) return resolvedResult.Error;

        var resolved = new ResolvedOpenLevel(level, ctx.Budget, resolvedResult.Value, OpenLevelResolutionBound(level, ctx));
        if (level is not null)
        {
            if (level.Activation is { } activation)
                activation.PublishOpenLevel(resolved);
            else
                level.PublishStaticOpenLevel(resolved);
        }

        return EvalResult<ResolvedOpenLevel>.Ok(resolved);
    }

    /// <summary>
    /// The watermark a level's providers resolved in <paramref name="ctx"/> are known to stand under
    /// (<see cref="ResolvedOpenLevel.AnswersWatermark"/>): the context's watermark, lowered to the serial of the
    /// least activation of <paramref name="level"/>'s chain that lies below it and is NOT detached there — the
    /// level of a callable another computation returned (RETURNED CALLABLES ACROSS DETACHED READS, November
    /// 2026; <see cref="IsDetached"/>). Every activation of the chain below the bound was then unusable to the
    /// resolution, so a reader at or below it finds no fewer usable activations, as the memo assumes. In a
    /// context whose detached chain activations are all detached owners it is the watermark itself.
    /// </summary>
    private static long OpenLevelResolutionBound(ScopeCtx? level, in EvalCtx ctx)
    {
        var bound = ctx.DetachedBefore;
        if (bound == 0)
            return 0;
        for (var scope = level; scope is not null; scope = scope.Parent)
        {
            if (scope.Activation is { } activation && activation.Serial < bound && !IsDetached(activation, ctx))
                bound = activation.Serial;
        }
        return bound;
    }

    /// <summary>
    /// <see cref="LookupOpens"/>'s selection over a level's resolved providers: public-only, in provider
    /// order. No provider offering <paramref name="name"/> is no hit; exactly one is the hit, checked for
    /// access from the READING site (the original context's head, not the consulted level) and wired in
    /// that context, carrying its provider as the admission its consumer notes
    /// (<see cref="ResolvedLexicalProperty.OpenProvider"/>, <see cref="AdmitOpenAccess"/>; the selection
    /// itself notes nothing); two or more are the ambiguity naming every offering provider in order.
    /// </summary>
    private static EvalResult<ResolvedLexicalProperty?> SelectOpenHit(ResolvedOpenLevel level, string name, EvalCtx ctx)
    {
        var offers = level.Offers(name, ctx.Observations);
        var first = offers.Next(out var binding);
        if (first < 0)
            return EvalResult<ResolvedLexicalProperty?>.Ok(null);

        var second = offers.Next(out _);
        if (second < 0)
        {
            var hit = level[first];
            if (!IsAccessibleFrom(binding!, hit.Lib, ctx, noteAdmission: false))
                return LocalOnlyPropertyError(hit.DisplayName, binding!);

            return EvalResult<ResolvedLexicalProperty?>.Ok(
                new ResolvedLexicalProperty(
                    hit.Lib,
                    binding!,
                    ChildOfInContext(hit.Lib, binding!.Value, ctx)) { OpenProvider = hit.DisplayName });
        }

        var providers = new List<string> { level[first].DisplayName, level[second].DisplayName };
        for (var next = offers.Next(out _); next >= 0; next = offers.Next(out _))
            providers.Add(level[next].DisplayName);
        // Published by the error: a read-only view, so no holder can change the provider list through a cast.
        return new EvalError.AmbiguousOpen(name, SafeReadOnlyCollection.OverList(providers));
    }

    /// <summary>The ONE constructor of the captured-member refusal, carrying the required names for the report.</summary>
    private static EvalError.LocalOnlyProperty LocalOnlyPropertyError(string objectDesc, Property member)
        => new(objectDesc, member.Name, member.Exposure) { RequiredParameters = member.RequiredAncestorParameters };

    // Iterative over the parent chain for the same reason as LookupInParentsDirect:
    // no O(chain) recursion on top of the deepest evaluation stack.
    private static ResolvedLexicalProperty? LookupInParentsDirectBinding(ScopeCtx sc, string name, EvaluationBudget budget)
    {
        for (ScopeCtx? current = sc; current is not null; current = current.Parent)
        {
            if (budget.PropertyBindings.Lookup(current.Properties, name) is { } prop)
            {
                // A host-built level has no evaluator owner: the level object itself is the
                // declaring owner (CACHE-OWNER-D3), the very object the value is wired under.
                return new ResolvedLexicalProperty(
                    PropertyDeclaringOwner.OfLevel(current),
                    prop,
                    WithParent(prop.Value, current));
            }
        }

        return null;
    }

    // ── Lexical resolution (ownership-first) ────────────────────────────────

    /// <summary>
    /// Open-based lookup in parent chain (helper for LookupOpensInChain).
    /// Checks opens at each level of the parent chain as fallback.
    /// Lean: lookupOpensInParentChain → EvalM (Option Algorithm).
    /// <para>Lean's tail recursion over the parent chain is a loop here, for the same reason as
    /// <see cref="LookupInParentsDirectBinding"/>: no O(chain) recursion on top of the deepest
    /// evaluation stack, so this walk needs no host-stack probe of its own (Q-09a). Each level's
    /// open resolution returns before the next level is consulted, and that resolution probes
    /// per open-target link (<see cref="ResolveOpenPropAccess"/>) and per structure read
    /// (<see cref="OpenStructure"/>). A level without opens is skipped before its empty level is
    /// built (it could provide nothing), and a level with opens is read through its memoized providers
    /// (<see cref="EnclosingOpenLevel"/>).</para>
    /// </summary>
    private static EvalResult<ResolvedLexicalProperty?> LookupOpensInParentChain(
        ScopeCtx sc, string name, EvalCtx ctx)
    {
        for (ScopeCtx? current = sc; current is not null; current = current.Parent)
        {
            if (current.Opens.Count == 0)
                continue;

            var level = EnclosingOpenLevel(current, ctx);
            if (level.IsError) return level.Error;
            var openResult = SelectOpenHit(level.Value, name, ctx);
            if (openResult.IsError) return openResult.Error;
            if (openResult.Value is not null)
                return EvalResult<ResolvedLexicalProperty?>.Ok(openResult.Value);
        }

        return EvalResult<ResolvedLexicalProperty?>.Ok(null);
    }

    /// <summary>
    /// Open-based lookup across the algorithm chain (current first, then parents).
    /// Checks opens at each level of the parent chain as fallback.
    /// Lean: lookupOpensInChain → EvalM (Option Algorithm).
    /// Never inlined: every lexical read enters <see cref="LookupLexicalRaw"/>, and most are decided by
    /// the structural walk alone, so the open fallback's temporaries stay out of that frame.
    /// </summary>
    [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.NoInlining)]
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
        // A loop plan can inspect a row that a false while flag will skip. Inside a retained
        // computation only recognize a direct builtin whose lookup needs no input record.
        // An alias or an activation-dependent open hit is resolved if execution reaches it.
        if (ctx.InputRecord is not null && ctx.Head is { } owner)
        {
            var selected = LookupLexicalRaw(owner, name, ctx);
            return selected.IsOk && selected.Value.ResolvedAlgorithm is Algorithm.Builtin(var direct)
                && direct == builtinId && (selected.Value.OpenProvider is null || IsExported(selected.Value.Binding));
        }

        // Optimizer recognition: non-initiating (META-S3-0b/S3-2) — a name whose identity needs a
        // runtime projection (a runtime-target alias) is declined, never projected to learn it.
        if (PeekResolve(ctx, (name, ctx), static state => ResolveNamedAlgorithm(state.name, span: null, state.ctx)) is not { } result)
            return false;
        return !result.IsError
            && result.Value is Algorithm.Builtin(var resolvedBuiltinId)
            && resolvedBuiltinId == builtinId;
    }

    /// <summary>
    /// Full lexical lookup with ownership-first model (<see cref="LookupLexicalRaw"/>), with the
    /// selected binding made CALLABLE: a binding that is a callable alias keeps its own property as
    /// the binding (its zero-argument cache key) while its resolved algorithm is the alias's
    /// normalized target (<see cref="NormalizeAliasBinding"/>). Never inlined, so its result never
    /// occupies a slot in the calibrated recursive frames that call it.
    /// Lean: <c>lookupLexicalProperty</c> followed by alias normalization.
    /// </summary>
    [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.NoInlining)]
    private static EvalResult<ResolvedLexicalProperty> LookupLexical(
        Algorithm alg, string name, EvalCtx ctx)
    {
        var resolved = LookupLexicalNoted(alg, name, ctx);
        return resolved.IsOk && resolved.Value.ResolvedAlgorithm is Algorithm.Alias
            ? NormalizeAliasBinding(resolved.Value, ctx)
            : resolved;
    }

    /// <summary>
    /// THE LEXICAL SELECTION AN EVALUATION CONSUMES (ledger R-1, the <c>open</c> route, November 2026;
    /// Lean <c>lookupLexicalPropertyNoted</c>): the ownership-first lexical lookup
    /// (<see cref="LookupLexicalRaw"/>), unchanged — the same selection, provider order and state-free
    /// judgment — followed by the input read of the access an <c>open</c> admitted
    /// (<see cref="AdmitOpenAccess"/>). Every evaluation that USES the selected binding selects through
    /// it: the callable and VALUE lookups (<see cref="LookupLexical"/>, <see cref="LookupLexicalForValue"/>),
    /// a supplied name's projection (<see cref="ProjectSuspendedCallable"/>), a receiver head
    /// (<see cref="ResolveReceiverHead"/>), the <c>.string</c> receiver
    /// (<see cref="EvalDotStringLexicalPropertyReceiver"/>), an alias's static step and its route decision
    /// (<see cref="AliasChaseMachine"/>). A re-read that consumes nothing keeps the raw lookup: the
    /// publication identity of a callee the callee law already selected (<see cref="WrittenCalleeBinding"/>)
    /// and the supply-time classification of a written reference (<see cref="ReferenceReachesRuntimeAlias"/>,
    /// <see cref="DotPathReachesRuntimeAlias"/>), whose projection then selects through this lookup.
    /// </summary>
    private static EvalResult<ResolvedLexicalProperty> LookupLexicalNoted(
        Algorithm alg, string name, EvalCtx ctx)
    {
        var resolved = LookupLexicalRaw(alg, name, ctx);
        return resolved.IsOk && resolved.Value.OpenProvider is not null
            ? AdmitOpenAccess(resolved.Value, ctx)
            : resolved;
    }

    /// <summary>
    /// THE OPEN ROUTE'S INPUT READ (ledger R-1, November 2026; Lean <c>noteOpenAccess</c>): a binding an
    /// <c>open</c> provided (<see cref="ResolvedLexicalProperty.OpenProvider"/>) passed that route's access law
    /// at the reading site, so the access used the owner activations the law requires — whether or not the
    /// member's body ever reads the owner's parameter — and inside a retained runtime-alias cell's
    /// computation it is an input read through each of them (<see cref="AliasCellInputs.AdmitMemberAccess"/>, reached
    /// through the same law in the same context, which admits again), refused, with the open route's own
    /// <see cref="EvalError.LocalOnlyProperty"/> naming the provider, when an owner it uses is detached by a reader admitted to
    /// the cell while a detached evaluation that detaches the owner is served. Outside every retained cell's
    /// computation it notes nothing and returns the selection.
    /// </summary>
    [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.NoInlining)]
    private static EvalResult<ResolvedLexicalProperty> AdmitOpenAccess(ResolvedLexicalProperty resolved, EvalCtx ctx)
    {
        if (ctx.CallStack is not AnnotatedReadOnlyList<Algorithm> { InputRecord: not null })
            return EvalResult<ResolvedLexicalProperty>.Ok(resolved);
        return IsAccessibleFrom(resolved.Binding, resolved.Owner.Algorithm!, ctx)
            ? EvalResult<ResolvedLexicalProperty>.Ok(resolved)
            : LocalOnlyPropertyError(resolved.OpenProvider!, resolved.Binding);
    }

    /// <summary>
    /// The lexical lookup of a VALUE read (a property read <c>A</c>, a <c>.string</c> receiver; OD-E, M4★):
    /// the selected binding's VALUE terminal — the binding itself when it is no alias, else the TERMINAL
    /// binding of its static chain (whose key, owner and activation the read uses: an alias owns no entry)
    /// or the first runtime-target alias as the resolved algorithm, whose bare read is its binding cell's
    /// VALUE (<see cref="ReadValueBindingCounted"/>); a VALUE read never initiates a CALLABLE projection.
    /// Lean: <c>lookupLexicalValueProperty</c>.
    /// </summary>
    [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.NoInlining)]
    private static EvalResult<ResolvedLexicalProperty> LookupLexicalForValue(
        Algorithm alg, string name, EvalCtx ctx)
        => NormalizeValueBinding(LookupLexicalNoted(alg, name, ctx), ctx);

    /// <summary>
    /// The alias normalization of a VALUE read (<see cref="LookupLexicalForValue"/>): an alias binding
    /// reads its VALUE terminal (<see cref="NormalizeAliasValueBinding"/>); every other binding is returned
    /// as is. Shared with the deconstruction source lookup (<see cref="SharedDeconstructionBind"/>), so
    /// both select the same entry.
    /// </summary>
    private static EvalResult<ResolvedLexicalProperty> NormalizeValueBinding(EvalResult<ResolvedLexicalProperty> resolved, EvalCtx ctx)
        => resolved.IsOk && resolved.Value.ResolvedAlgorithm is Algorithm.Alias
            ? NormalizeAliasValueBinding(resolved.Value, ctx)
            : resolved;

    /// <summary>
    /// Full lexical lookup with ownership-first model:
    /// 1. Local properties (owned by this algorithm — any visibility)
    /// 2. Parent chain structural properties (owned by ancestors — any visibility, no opens)
    /// 3. Opens as fallback across the entire chain (public only)
    /// Structural ownership always takes precedence over opens. The selected binding is returned
    /// RAW — an alias as the alias — for the consumers that normalize it themselves: a written
    /// receiver's head, which is then read through its STRUCTURE (<c>ReceiverStructure</c>: a
    /// transparent reference navigates its target's declarations, M4★), the supplied-cell projection,
    /// and alias resolution itself. It notes nothing: an evaluation that consumes the selection reads it
    /// through <see cref="LookupLexicalNoted"/> (ledger R-1).
    /// Lean: lookupLexicalPropertyRaw.
    /// </summary>
    private static EvalResult<ResolvedLexicalProperty> LookupLexicalRaw(
        Algorithm alg, string name, EvalCtx ctx)
    {
        // 1.-2. The structural owner walk (local properties, then the parent chain).
        if (LookupLexicalStructural(alg, name, ctx) is { } structural)
            return EvalResult<ResolvedLexicalProperty>.Ok(structural);

        // 3. Opens fallback across the entire chain (public only)
        var opensResult = LookupOpensInChain(alg, name, ctx);
        if (opensResult.IsError) return opensResult.Error;
        if (opensResult.Value is { } openBinding)
            return EvalResult<ResolvedLexicalProperty>.Ok(openBinding);

        return new EvalError.UnknownName(name);
    }

    /// <summary>
    /// The STRUCTURAL half of <see cref="LookupLexicalRaw"/>, before any open is consulted:
    /// 1. local properties (owned by this algorithm — any visibility), then 2. the parent chain's
    /// structural properties (owned by ancestors — any visibility). <c>null</c> when neither declares
    /// the name, i.e. when only the opens fallback could select it. Evaluates nothing and charges
    /// nothing.
    /// </summary>
    private static ResolvedLexicalProperty? LookupLexicalStructural(Algorithm alg, string name, EvalCtx ctx)
    {
        var local = LookupPropBinding(alg, name, ctx.Budget);
        if (local is not null)
            return new ResolvedLexicalProperty(alg, local, ChildOfInContext(alg, local.Value, ctx));

        return alg.Parent is { } sc ? LookupInParentsDirectBinding(sc, name, ctx.Budget) : null;
    }

    // ── Wire parent ─────────────────────────────────────────────────────────

    /// <summary>Lean: wireToCaller.</summary>
    private static Algorithm WireToCaller(EvalCtx ctx, Algorithm alg)
    {
        if (ctx.CallStack.Count > 0)
            return ChildOfInContext(ctx.CallStack[0], alg, ctx);
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

    /// <summary>
    /// Coerce a Result to a number. Every present value that is not a number — a string, a
    /// Boolean, a sequence (<c>()</c> included) or a list — is the value-KIND failure
    /// <c>TypeMismatch</c> (Q-27): a selector, a <c>range</c> bound, a <c>repeat</c> count and a
    /// Math argument of the wrong kind are never an arity error. Lean: expectInt.
    /// </summary>
    internal static EvalResult<Decimal128> ExpectInt(Result r)
    {
        if (r is Result.Str)
            return new EvalError.TypeMismatch("Expected a number, got a string");
        if (r is Result.Bool)
            return new EvalError.TypeMismatch("Expected a number, got a Boolean value");
        var v = r.AsNum();
        return v is not null
            ? EvalResult<Decimal128>.Ok(v.Value)
            : new EvalError.TypeMismatch($"Expected a number, got {DescribeOperand(r)}");
    }

    /// <summary>
    /// Structural KatLang value equality used by <c>==</c> and <c>!=</c>.
    /// Numbers compare by value, strings by exact value, and sequence values by
    /// length plus recursive pairwise equality. Different value kinds compare
    /// unequal rather than raising a type mismatch. This mirrors Lean's
    /// <c>resultValueEq</c> (the derived structural <c>BEq</c> on <c>Result</c>)
    /// and decides exactly the <see cref="Result.ValueComparer"/> verdict, the same value
    /// equality the builtins <c>contains</c> and <c>distinct</c> use. Like theirs, its
    /// structural and long-string work is charged to the run's budget and observes host
    /// cancellation (SEC-02-FU, <see cref="Result.EvaluatorValueEquals"/>): a refused charge is
    /// the run's terminal error, never inequality.
    /// </summary>
    private static EvalResult<bool> ValueEquals(Result left, Result right, EvalCtx ctx)
        => Result.EvaluatorValueEquals(left, right, ctx.Budget, ctx.Observations?.StructuralTraversal);

    private static EvalResult<Decimal128> RequireNumericScalarOperand(BinaryOp op, string side, Result value)
        => RequireNumericScalarOperand(ExprNameRenderer.BinaryOpText(op), side, value);

    /// <summary>The ordering comparisons share the arithmetic operators' numeric-scalar operand rule and message.</summary>
    private static EvalResult<Decimal128> RequireNumericScalarOperand(ComparisonOp op, string side, Result value)
        => RequireNumericScalarOperand(ExprNameRenderer.ComparisonOpText(op), side, value);

    private static EvalResult<Decimal128> RequireNumericScalarOperand(string operatorName, string side, Result value)
    {
        var number = value.AsNum();
        return number is not null
            ? EvalResult<Decimal128>.Ok(number.Value)
            : new EvalError.TypeMismatch(NumericScalarOperandMessage(operatorName, side, value));
    }

    private static string NumericScalarOperandMessage(string operatorName, string side, Result value)
        => $"operator `{operatorName}` expects numeric scalar operands, but the {side} operand was {DescribeOperand(value)}";

    /// <summary>
    /// The logical operators <c>and</c> / <c>or</c> / <c>xor</c> require a Boolean value on
    /// every side they EVALUATE: there is no numeric truthiness, so a number, string, sequence
    /// value, or list operand is a value-kind error naming the operand. (A right operand that
    /// <c>and</c> / <c>or</c> skip is never evaluated and so never checked:
    /// <see cref="DecideLogicalAfterLeftOperand"/>.) Lean: <c>requireBooleanOperand</c>.
    /// </summary>
    private static EvalResult<bool> RequireBooleanOperand(BinaryOp op, string side, Result value)
    {
        var flag = value.AsBool();
        return flag is not null
            ? EvalResult<bool>.Ok(flag.Value)
            : new EvalError.TypeMismatch(BooleanOperandMessage(ExprNameRenderer.BinaryOpText(op), side, value));
    }

    private static string BooleanOperandMessage(string operatorName, string side, Result value)
        => $"operator `{operatorName}` expects Boolean operands, but the {side} operand was {DescribeOperand(value)}";

    /// <summary>
    /// The ONE message for every position that REQUIRES a Boolean value — an <c>if</c>
    /// condition, a <c>filter</c> predicate result, a <c>while</c> continuation flag: it names
    /// the role and the value kind actually supplied, so a number in a predicate position is
    /// reported as the value-kind mismatch it is, never as an arity or numeric error.
    /// Lean: <c>booleanRequiredMessage</c>.
    /// </summary>
    internal static string BooleanRequiredMessage(string role, Result value)
        => $"{role} must be a Boolean value (true or false), but was {DescribeOperand(value)}";

    /// <summary>The role text of the <c>while</c> continuation flag in <see cref="BooleanRequiredMessage"/>.</summary>
    internal const string WhileContinuationFlagRole = "while continuation flag (the step's last output)";

    /// <summary>
    /// The context of a <c>while</c> step that emitted no slot at all: its output has no
    /// continuation flag, an emitted-slot cardinality failure (<c>ArityMismatch</c>, Q-27).
    /// Lean: <c>splitContSlots</c>.
    /// </summary>
    internal const string WhileStepWithoutFlagContext = "a while step must output at least its continuation flag";

    /// <summary>
    /// How a diagnostic names one value that failed an operand, condition, or predicate
    /// requirement: the value KIND first, then the value itself. Lean: <c>operandDescription</c>.
    /// </summary>
    internal static string DescribeOperand(Result value) => value switch
    {
        Result.SequenceValue(var items) => $"a sequence value with {items.Count} {Pluralize(items.Count, "sequence element")}: {FormatResultForDiagnostic(value)}",
        Result.Str => $"a string: {FormatResultForDiagnostic(value)}",
        Result.Bool(var flag) => $"a Boolean value: {Rendering.ValueTextRenderer.FormatBool(flag)}",
        Result.Atom(var number) => $"numeric value {Rendering.ValueTextRenderer.FormatNumberInvariant(number)}",
        // A list evaluated on demand (issue #204) is described without reading any position: its
        // cardinality when that is known, never its unread elements.
        Result.ListValue { Lazy: { IsPending: true } } => "a list value whose elements are not yet evaluated",
        Result.ListValue { Lazy: { } positions } => $"a list value with {positions.Discovered} {Pluralize(positions.Discovered, "element")}: {FormatResultForDiagnostic(value)}",
        Result.ListValue(var items) => $"a list value with {items.Count} {Pluralize(items.Count, "element")}: {FormatResultForDiagnostic(value)}",
        Result.CallReference { IsArgumentView: true } => "an argument view",
        Result.CallReference => "a call reference",
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
        ValEnv valEnv)
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
    /// The ONE range-bound policy, shared by every execution path that builds an
    /// <see cref="InclusiveRange"/> (synchronous evaluation, the async twin, and —
    /// through the synchronous entry — sequence-pipeline direct range iteration).
    /// Safety half: a bound must be an exact integer whose magnitude does not
    /// exceed <see cref="MaxExactRangeBound"/>, because beyond 1e34 a unit step
    /// is absorbed (<c>x + 1 == x</c>) and enumeration could never advance while
    /// the computed cardinality still looked small enough to pass collection
    /// limits. Representation half: an accepted bound is returned in its canonical
    /// integer representation (<see cref="CanonicalizeIntegralRangeBound"/>), so
    /// the quantum a whole-number bound was written with never reaches the
    /// generated list. Pure over the already-evaluated bound value, so no path can
    /// re-implement (and drift from) either half.
    /// </summary>
    private static EvalResult<Decimal128> ValidateRangeBound(Result value, string description)
    {
        var wholeR = ExpectWholeInt(value, description);
        if (wholeR.IsError) return wholeR.Error;
        if (Decimal128.Abs(wholeR.Value) > MaxExactRangeBound)
            return new EvalError.IllegalInEval($"{description} must not exceed 1e34 in magnitude");
        return EvalResult<Decimal128>.Ok(CanonicalizeIntegralRangeBound(wholeR.Value));
    }

    /// <summary>
    /// Canonical representation of an already-validated integral <c>range</c> bound:
    /// unsigned zero, or the exponent-0 cohort member. Quantize is exact for these
    /// integers of at most 34 digits. The only accepted 35-digit integers, ±1e34,
    /// require exponent 1 (coefficient 10^33). Unit steps preserve this representation,
    /// including transitions to and from those endpoints, so enumeration needs no
    /// per-item normalization. This is range-specific: ordinary arithmetic and other
    /// whole-integer argument validators retain their existing quantum behavior.
    /// </summary>
    internal static Decimal128 CanonicalizeIntegralRangeBound(Decimal128 whole)
    {
        if (whole == Decimal128.Zero)
            return Decimal128.Zero;

        var canonical = Decimal128.Quantize(whole, Decimal128.One);
        if (Decimal128.IsNaN(canonical))
            canonical = Decimal128.Quantize(whole, RangeCeilingQuantum);

        // Value preservation is what makes this a representation-only step. An
        // inexact quantize (or a NaN after both attempts) means the bound bypassed
        // the whole-integer and magnitude checks above — an internal invariant
        // violation that fails loud, never a silently changed range.
        if (canonical != whole)
        {
            throw new InvalidOperationException(
                $"range bound {Rendering.ValueTextRenderer.FormatNumberInvariant(whole)} has no exact canonical "
                + "integer representation, so it bypassed ValidateRangeBound's whole-integer and magnitude checks.");
        }

        return canonical;
    }

    /// <summary>
    /// Quantum of the canonical representation of the ±1e34 range endpoints
    /// (coefficient 10^33, exponent 1): 1e34 itself has 35 digits, one more than
    /// a Decimal128 coefficient holds, so it has no exponent-0 cohort member.
    /// </summary>
    private static readonly Decimal128 RangeCeilingQuantum = Decimal128.ScaleB(Decimal128.One, 1);

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
    /// cursor lands exactly on <c>Stop</c>, and the enumeration is total. Bounds arrive
    /// canonical (<see cref="CanonicalizeIntegralRangeBound"/>) and a unit step from
    /// an exponent-0 value keeps exponent 0, so every enumerated value is canonical
    /// without per-item normalization; only a ±1e34 endpoint is reached at exponent 1,
    /// the representation Decimal128 precision forces there. A step that
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
            $"range enumeration cannot advance from {Rendering.ValueTextRenderer.FormatNumberInvariant(cursor)}: "
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
    /// list value. Counts upward when <c>start &lt;= stop</c>
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

    private static EvalError WrongBuiltinArity(BuiltinId builtin, int actualCount)
    {
        var descriptor = BuiltinRegistry.GetBuiltin(builtin);
        // The payload is the builtin's real arity contract, its fixed arity (formerly a placeholder
        // 0 for all but `if`). Lean: `builtinMinimumArity`, read by `builtinArityError`. The message
        // renders it from the one registry signature, whose patterns are that contract.
        return new EvalError.ArityMismatch(descriptor.FixedArity, actualCount)
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
            return MakeStringResult(ctx, Rendering.ValueTextRenderer.FormatNumberInvariant(n));
        return new EvalError.TypeMismatch("builtin property `string` expects a numeric receiver");
    }

    /// <summary>
    /// The single construction point for language string values created by source
    /// evaluation from one finished text: string literals, the <c>.string</c> intrinsic, and
    /// the planned loop's string constant. Every producer charges the length ceiling and the
    /// cumulative string budget through the one reservation
    /// (<see cref="Evaluation.EvaluationBudget.TryReserveString"/>) BEFORE the value is
    /// created.
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
    private static EvalResult<Algorithm> ResolveAlgForOpen(Expr expr, EvalCtx ctx, ref OpenStructureChase? chase)
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
                // target such as `open (M, M)` is not openable. The parser
                // rejects this form in source; this arm is the prebuilt-AST
                // defense, mirroring the spread arm above.
                return new EvalError.BadOpenForm("captured value groups cannot be opened") { Span = expr.Span };

            case Expr.Resolve(var name):
                {
                    // open never requires the opened algorithm itself to be public.
                    // It only requires the algorithm to be available in the current context.
                    // open imports only public members (enforced later by LookupOpens).
                    // The target is wired on the head's scope IN CONTEXT — its activated head scope —
                    // as every lexical lookup wires a property of the head (Lean: `resolveOpen`'s
                    // `.resolve` arm, `lookupInParentsDirect (scopeInContext a ctx) n`).
                    if (ctx.Head is { } head)
                    {
                        var found = LookupInParentsDirect(ScopeInContext(head, ctx), name, ctx.Budget);
                        if (found is not null)
                        {
                            if (found is Algorithm.Builtin)
                                return new EvalError.IllegalInOpen($"builtin '{name}'") { Span = expr.Span };
                            return EvalResult<Algorithm>.Ok(found);
                        }
                    }
                    return new EvalError.UnknownName(name) { Span = expr.Span };
                }

            case Expr.DotCall openDotCall when openDotCall.IsCoreOpenForm():
                return WithSpan(expr.Span, ResolveOpenPropAccess(openDotCall.Target, openDotCall.Name, ctx, ref chase));

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
    /// <para>Host-stack backstop, one per open-target link (Q-09a): this method and
    /// <see cref="ResolveAlgForOpen"/> recurse once per <c>.name</c> link of an open target, and
    /// a lexical lookup that consults the opens can start this navigation deep on the
    /// evaluator's stack, so the structural gate alone cannot bound it. The probe runs BEFORE
    /// the receiver recursion (the <see cref="OpenStructure"/> probe runs only after it returns),
    /// on this half of the pair only, so a link costs one probe, as on the dot navigation
    /// (<see cref="ResolveDotReceiver"/>).</para>
    /// </summary>
    private static EvalResult<Algorithm> ResolveOpenPropAccess(
        Expr target, string propName, EvalCtx ctx, ref OpenStructureChase? chase)
    {
        if (!System.Runtime.CompilerServices.RuntimeHelpers.TryEnsureSufficientExecutionStack())
            return new EvalError.EvaluationStackExhausted();

        var targetResult = ResolveAlgForOpen(target, ctx, ref chase);
        if (targetResult.IsError) return targetResult.Error;

        // A transparent reference receiver is navigated as its target (OD-C), resolved without opens.
        targetResult = OpenStructure(targetResult.Value, ctx, ref chase);
        if (targetResult.IsError) return AtSpanIfMissing(targetResult.Error, target.Span);

        // First check if property exists at all so ownership still wins over opens.
        var prop = LookupPropBinding(targetResult.Value, propName, ctx.Budget);
        if (prop is not null)
        {
            if (prop.Value is Algorithm.Builtin)
                return new EvalError.IllegalInOpen(
                    $"builtin not allowed in open: {OpenExprName(target)}.{propName}");

            // An open path selects public members. Visibility is decided before the
            // selected member's contextual capture requirements.
            if (!prop.IsPublic)
                return new EvalError.NotPublicProperty(OpenExprName(target), propName);

            if (!IsAccessibleFrom(prop, targetResult.Value, ctx, noteAdmission: false))
                return LocalOnlyPropertyError(OpenExprName(target), prop);

            // Keep the selected property bound to its definition-site scope.
            return EvalResult<Algorithm>.Ok(ChildOfInContext(targetResult.Value, prop.Value, ctx));
        }
        if (targetResult.Value.DefinesConditionalBranchProperty(propName))
            return new EvalError.LocalOnlyProperty(OpenExprName(target), propName, PropertyExposure.LocalOnlyConditionalAlgorithm);

        return new EvalError.UnknownProperty(OpenExprName(target), propName);
    }

    // ── Algorithm resolution (full — with opens) ─────────────────────────────

    /// <summary>Lean: resolveAlg → EvalM Algorithm.</summary>
    private static EvalResult<Algorithm> ResolveAlg(Expr expr, EvalCtx ctx)
    {
        return expr switch
        {
            // An inline block that is a callable alias (`{ F }`) is its target in callable position.
            Expr.AlgorithmExpr(var alg) => alg is Algorithm.Alias
                ? ResolveInlineAliasTarget(alg, ctx)
                : EvalResult<Algorithm>.Ok(WireToCaller(ctx, alg)),

            // Capture is not algorithm identity: the algorithm channel sees
            // only a zero-parameter value thunk over the bundle, exactly as
            // the pre-split transparent wrapper behaved. `Apply((Inc, Dec))`
            // therefore never receives either callable identity, while the
            // redundant group `Apply((Increment))` IS `Apply(Increment)` — the
            // parser erases it before this node exists (parentheses group
            // syntax; they do not introduce a semantic boundary).
            Expr.Capture(var captureBody) => EvalResult<Algorithm>.Ok(CaptureValueThunk(captureBody, ctx)),

            Expr.Resolve(var name) => ResolveNamedAlgorithm(name, expr.Span, ctx),

            Expr.DotCall dotCall => ResolveDotCallAlgorithm(dotCall, ctx),

            // Algorithm resolution for parameters (Lean: resolveAlg Param(x)):
            // The parameter's supplied cell projects its CALLABLE identity (never a VALUE
            // demand); an algorithm-tier binding (internally constructed contexts only) is
            // returned as is. Otherwise NotAnAlgorithm (parameters are not structurally algorithms).
            // The environment reaching here was shadowed by every enclosing
            // binding's parameter names (UnshadowedBindings, MintNeedBindingContext), so a
            // parameter bound only on the value channel finds NO entry and fails as
            // not-callable instead of reaching a same-named caller callable.
            Expr.Param(var x) => ResolveNeedParameterAlgorithm(x, expr.Span, ctx),

            // Value forms are not algorithms. Lean: notAnAlgorithm <description> — each
            // description is structured payload and must match exactly.
            Expr.SequenceConstruct => new EvalError.NotAnAlgorithm("sequence construct expression") { Span = expr.Span },
            Expr.SequenceSpread => new EvalError.NotAnAlgorithm("spread expression") { Span = expr.Span },
            Expr.Num(var n) => new EvalError.NotAnAlgorithm($"num({Rendering.ValueTextRenderer.FormatNumberInvariant(n)})") { Span = expr.Span },
            Expr.EmptySequence => new EvalError.NotAnAlgorithm("empty sequence value") { Span = expr.Span },
            Expr.ListLiteral => new EvalError.NotAnAlgorithm("list literal") { Span = expr.Span },
            Expr.Unary => new EvalError.NotAnAlgorithm("unary expression") { Span = expr.Span },
            Expr.Binary => new EvalError.NotAnAlgorithm("binary expression") { Span = expr.Span },
            Expr.Comparison => new EvalError.NotAnAlgorithm("comparison expression") { Span = expr.Span },
            Expr.Index => new EvalError.NotAnAlgorithm("index expression") { Span = expr.Span },
            Expr.Call => new EvalError.NotAnAlgorithm("call expression") { Span = expr.Span },
            Expr.NativeCall => new EvalError.NotAnAlgorithm("native call") { Span = expr.Span },
            Expr.Grace => new EvalError.NotAnAlgorithm("grace expression") { Span = expr.Span },
            Expr.StringLiteral => new EvalError.NotAnAlgorithm("string literal") { Span = expr.Span },
            Expr.BoolLiteral => new EvalError.NotAnAlgorithm("Boolean literal") { Span = expr.Span },
        };
    }

    /// <summary>
    /// The internal CARRIER of a dot RESULT used as a RECEIVER (Lean: resolveAlg
    /// (.dotMember o n fallback args)): a memberless zero-parameter algorithm whose one output
    /// row is the dot expression itself, so its evaluation — <c>evalDotCall</c> — owns every
    /// dot semantic (structural lookup, the <c>.string</c> intrinsic, the extension call). Its
    /// only consumer is RECEIVER resolution (<see cref="ResolveDotReceiver"/>, Lean
    /// <c>resolveDotReceiver</c>): an edge whose receiver lacks the member, or an
    /// argument-bearing edge, is a VALUE there (DOT-02), carried by this wrapper into the next
    /// edge's member lookup (it declares none) and the <c>.string</c> intrinsic's value demand.
    /// It is never a program-visible callable: every algorithm-capable position — a supplied
    /// argument, a callback, a loop step and the callee alike — reads a dot expression's
    /// identity through <see cref="ProjectDotPathCallable"/> (DOT-09), which gives a computed
    /// value no callable identity at all.
    /// <para>No host-stack probe: this builds one wrapper and never recurses per dot link (nor does
    /// <see cref="ResolveAlg"/>, which dispatches one node); the per-link recursions are the receiver
    /// navigation (<see cref="ResolveDotReceiver"/>) and the open navigation
    /// (<see cref="ResolveOpenPropAccess"/>), and each probes once per link (Q-09a).</para>
    /// </summary>
    private static EvalResult<Algorithm> ResolveDotCallAlgorithm(Expr.DotCall dotCall, EvalCtx ctx)
    {
        var wrapper = new Algorithm.User(
            Parent: null, ParameterPatterns: [], Opens: [],
            Properties: [], Output: [dotCall]);
        return EvalResult<Algorithm>.Ok(WireToCaller(ctx, wrapper));
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
    /// of its elaboration metadata. Exposure metadata is ENFORCED, not trusted
    /// (EXPORTED-DETACHED): a property left <see cref="PropertyExposure.Exported"/> that
    /// reads an input of an enclosing call is refused where it reads it
    /// (<c>UnknownName</c>, <c>LocalOnlyProperty</c>), never given a value shared across
    /// calls.</para>
    /// <para><b>Host-AST contract:</b> the expression may be a preconstructed
    /// (host-built) AST. Every entry point first runs a non-recursive structural safety
    /// preflight: a tree whose weighted structural depth exceeds
    /// <see cref="EvaluationLimits.MaxAstDepth"/> (bounded by
    /// <see cref="EvaluationLimits.MaxSupportedAstDepth"/>) is rejected with
    /// <see cref="EvalError.AstDepthLimitExceeded"/>, and a cyclic node graph with
    /// <see cref="EvalError.AstCycleDetected"/>, before any recursive validation,
    /// optimization, or evaluation can overflow the CLR stack. Programs accepted by
    /// the public <see cref="Parser"/> always stay within the hard ceiling.</para>
    /// <para><b>Pre-evaluation validation:</b> after the structural preflight, the
    /// validation pass Lean's <c>runResultM</c> runs before evaluation is applied to
    /// the whole tree, every host-built parent <see cref="ScopeCtx"/> included (its
    /// <c>open</c> targets and properties): an algorithm with explicit parameters but
    /// no output is rejected with <see cref="EvalError.ExplicitParametersRequireOutput"/>,
    /// and a conditional whose branches disagree on top-level pattern arity or top-level
    /// output arity is rejected with <see cref="EvalError.BranchArityMismatch"/> /
    /// <see cref="EvalError.BranchOutputArityMismatch"/> before any branch matching or
    /// evaluation — even when the malformed conditional is never referenced. Parsed
    /// surface programs never contain such conditionals (clause elaboration rejects
    /// them with source-positioned diagnostics); this gate aligns hand-built ASTs with
    /// Lean's <c>runResult</c>.</para>
    /// <para><b>Deferred module regions:</b> a tree carrying a deferred module region — a
    /// clause branch whose modules load only when evaluation selects it, which
    /// <see cref="Parser.ParseAsync"/> produces when <see cref="RunOptions.DownloadCode"/> is
    /// configured — can be evaluated only asynchronously, because materializing a selected
    /// branch can await the module downloader. Every synchronous <c>Run</c> and
    /// <c>RunFlat</c> overload rejects such a tree with
    /// <see cref="InvalidOperationException"/> before evaluating it; use
    /// <see cref="RunAsync(Expr, EvaluationLimits?, CancellationToken)"/> or another
    /// asynchronous entry point.</para>
    /// <para><b>Supported execution environment:</b> the structural safety envelope
    /// is calibrated for threads with at least 1 MiB of stack (the CLR/Windows
    /// default). Embedders running evaluation on smaller custom stacks are outside
    /// the documented envelope and should lower
    /// <see cref="EvaluationLimits.MaxAstDepth"/> accordingly.</para>
    /// <para><b>Failures:</b> every failure of the program itself is returned as the
    /// structured <see cref="EvalResult{T}.Error"/> (render it with
    /// <see cref="KatLangError.FromEvalError"/>); only host misuse, host cancellation, and
    /// exceptions thrown by host code escape as CLR exceptions. The evaluator keeps no
    /// state between calls, so concurrent runs — also over one shared, immutable AST — are
    /// independent.</para>
    /// </summary>
    /// <exception cref="ArgumentNullException"><paramref name="expr"/> is null.</exception>
    /// <exception cref="InvalidOperationException">
    /// <paramref name="expr"/> carries a deferred module region, which only an asynchronous
    /// entry point can evaluate.
    /// </exception>
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
    /// <exception cref="ArgumentNullException"><paramref name="expr"/> is null.</exception>
    /// <exception cref="InvalidOperationException">
    /// <paramref name="expr"/> carries a deferred module region (see <see cref="Run(Expr)"/>).
    /// </exception>
    public static EvalResult<Result> Run(Expr expr, EvaluationLimits? limits)
    {
        ArgumentNullException.ThrowIfNull(expr);
        return Run(expr, new RunScopedZeroArgPropertyResultCache(collectStatistics: false), limits);
    }

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
    /// <exception cref="InvalidOperationException">
    /// <paramref name="expr"/> carries a deferred module region (see <see cref="Run(Expr)"/>).
    /// </exception>
    public static EvalResult<Result> Run(Expr expr, EvaluationLimits? limits, CancellationToken cancellationToken)
        => Run(expr, limits, randomSeed: null, cancellationToken);

    /// <summary>
    /// Run evaluation under explicit resource limits, an optional random seed, and
    /// cooperative host cancellation — the direct-evaluator counterpart of
    /// <see cref="RunOptions.RandomSeed"/>, with the same contract: <c>null</c> keeps the
    /// unseeded, nondeterministic stream; any <see cref="long"/> selects one reproducible
    /// stream for this run alone (each call starts it from the beginning), shared in
    /// evaluation order by every <c>Math.Random</c> / <c>random</c> and
    /// <c>Math.RandomInt</c> / <c>randomInt</c> call of the run. Limits and cancellation
    /// behave exactly as in <see cref="Run(Expr, EvaluationLimits?, CancellationToken)"/>.
    /// KatLang randomness is not cryptographically secure.
    /// </summary>
    /// <exception cref="OperationCanceledException">
    /// <paramref name="cancellationToken"/> was cancelled before or during evaluation.
    /// </exception>
    /// <exception cref="ArgumentNullException"><paramref name="expr"/> is null.</exception>
    /// <exception cref="InvalidOperationException">
    /// <paramref name="expr"/> carries a deferred module region (see <see cref="Run(Expr)"/>).
    /// </exception>
    public static EvalResult<Result> Run(
        Expr expr,
        EvaluationLimits? limits,
        long? randomSeed,
        CancellationToken cancellationToken)
    {
        ArgumentNullException.ThrowIfNull(expr);
        return Run(
            expr,
            new RunScopedZeroArgPropertyResultCache(collectStatistics: false),
            enableLoopOptimization: true,
            loopDiagnostics: null,
            enableSequencePipelineOptimization: true,
            sequenceDiagnostics: null,
            limits,
            observations: null,
            hostOperations: null,
            randomSeed,
            cancellationToken: cancellationToken);
    }

    /// <summary>
    /// Run evaluation with SYNCHRONOUS host operations ambiently in scope, under the
    /// ordinary limits and cancellation contracts of
    /// <see cref="Run(Expr, EvaluationLimits?, CancellationToken)"/> and the seed contract of
    /// <see cref="Run(Expr, EvaluationLimits?, long?, CancellationToken)"/> (pass <c>null</c>
    /// for an unseeded run).
    ///
    /// <para>Each operation resolves like a prelude member (see
    /// <see cref="HostOperations"/>), so a preparsed program that references host
    /// operation names — typically obtained from
    /// <see cref="Parser.Parse(string, RunOptions?)"/> with the same operations
    /// configured on <see cref="RunOptions.HostOperations"/> — evaluates them at the
    /// referencing sites. Host-operation delegates run inline on the calling thread;
    /// exceptions they throw propagate to the caller unchanged (see
    /// <see cref="HostOperation"/> for the full contract). Host operations are outside the
    /// seeded stream — what they return remains the host's responsibility — while every
    /// KatLang random call of the run draws from the one seeded stream in evaluation
    /// order.</para>
    ///
    /// <para>This synchronous entry point accepts synchronous operations only: a set
    /// containing an asynchronous operation is rejected with
    /// <see cref="InvalidOperationException"/> before anything is evaluated — use
    /// <see cref="RunAsync(Expr, HostOperations, EvaluationLimits?, long?, CancellationToken)"/>
    /// for asynchronous operations. A tree carrying a deferred module region is rejected the
    /// same way (see <see cref="Run(Expr)"/>).</para>
    ///
    /// <para>Every arity of the <c>Run</c> family has exactly one overload, so positional
    /// arguments — <c>null</c> literals included — always select exactly one of them:
    /// <c>Run(expr, null, null, token)</c> is the four-argument limits-and-seed overload.</para>
    /// </summary>
    /// <exception cref="ArgumentNullException">
    /// <paramref name="expr"/> is null, or <paramref name="hostOperations"/> is null — a run
    /// without host operations uses an overload that does not take them.
    /// </exception>
    /// <exception cref="InvalidOperationException">
    /// <paramref name="hostOperations"/> contains an asynchronous operation, or
    /// <paramref name="expr"/> carries a deferred module region (see <see cref="Run(Expr)"/>).
    /// </exception>
    /// <exception cref="OperationCanceledException">
    /// <paramref name="cancellationToken"/> was cancelled before or during evaluation.
    /// </exception>
    public static EvalResult<Result> Run(
        Expr expr,
        HostOperations hostOperations,
        EvaluationLimits? limits,
        long? randomSeed,
        CancellationToken cancellationToken)
    {
        ArgumentNullException.ThrowIfNull(expr);
        ArgumentNullException.ThrowIfNull(hostOperations);
        return Run(
            expr,
            new RunScopedZeroArgPropertyResultCache(collectStatistics: false),
            enableLoopOptimization: true,
            loopDiagnostics: null,
            enableSequencePipelineOptimization: true,
            sequenceDiagnostics: null,
            limits,
            observations: null,
            hostOperations,
            randomSeed,
            cancellationToken: cancellationToken);
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
    /// <para><b>LIMITS OBSERVE A RUN; THEY NEVER CHOOSE HOW IT RUNS (Q-09b).</b> The
    /// execution strategies a run uses are decided by the caller's request and the run's
    /// route — never by <see cref="EvaluationLimits"/>: the optimization flags are passed
    /// through exactly as requested, and the budget exposes only effective thresholds. That
    /// is sound because every strategy charges every budget at the same logical points: a
    /// planned loop charges one step per iteration and the generic evaluator's
    /// expression-work checkpoints for every planned expression
    /// (<c>LoopOptimizer.EvalLoopExprPlan</c>), and the fused <c>filter</c>→<c>count</c>
    /// pipeline charges the dispatch checkpoints of the stage expressions it elides and
    /// reserves the items the generic composition materializes
    /// (<c>SequencePipelineOptimizer</c>). Depth, strings and the per-collection ceiling were
    /// already charged identically. So a limit that is reached gives the same verdict at the
    /// same point on every strategy, and a limit that is not reached changes nothing — not
    /// the value, the effects, the counters, or which strategy runs (and with it, on the same
    /// host, whether the host-stack backstop stops the run).</para>
    ///
    /// <para>Never reintroduce a limit-to-strategy switch here to make a budget's accounting
    /// convenient: an inequality between strategies is an accounting defect of the strategy,
    /// to be fixed there. Pinned by <c>LimitConfigurationTransparencyTests</c>,
    /// <c>StrategyNeutralBudgetParityTests</c> and <c>BudgetCrossTalkMatrixTests</c>.</para>
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
        // A run configured with host operations resolves names against that
        // configuration's extended prelude (the ordinary prelude plus one ambient
        // wrapper member per operation); the budget carries the configuration, so the
        // prelude choice and the dispatch registry can never disagree within a run.
        var deconstructionBindingCache = new RunScopedDeconstructionBindingCache();
        observations?.RecordDeconstructionBindingCache(deconstructionBindingCache);
        return new EvalCtx(
            [budget.HostOperations?.RuntimePreludeAlgorithm ?? PreludeAlg],
            null,
            new RunServices(
                zeroArgPropertyResultCache,
                deconstructionBindingCache,
                enableLoopOptimization,
                loopDiagnostics,
                enableSequencePipelineOptimization,
                sequenceDiagnostics,
                observations),
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
    /// trees; runs before any evaluation-budget counter can move and charges nothing. The same walk
    /// decides the run's program facts (<paramref name="facts"/>): its J7 plan-retention fact
    /// (<see cref="AstStructuralPreflight.MayCaptureCalls"/>), its runtime-alias reach
    /// (<see cref="AstStructuralPreflight.MayReachRuntimeAlias"/>) and whether the graph is alias-free
    /// (<see cref="AstStructuralPreflight.AdmittedProgramFacts.IsAliasFree"/>). An accepted walk hands its
    /// table over to <paramref name="tables"/> for the validation walk. The walk observes the run's
    /// <paramref name="cancellationToken"/> before its first edge and in blocks of
    /// <see cref="AstStructuralPreflight.CancellationCheckpointEdges"/> edges, so a run over a large program is
    /// cancellable inside its preflight; its verdict and facts are unchanged.
    /// </summary>
    private static EvalError? StructuralPreflight(
        Expr expr,
        EvaluationLimits? limits,
        int nodeCountHint,
        PreEvaluationTables tables,
        FrontEndTraversalObservations? observations,
        out AstStructuralPreflight.AdmittedProgramFacts facts,
        CancellationToken cancellationToken)
    {
        var effectiveLimit = (limits ?? EvaluationLimits.Default).EffectiveMaxAstDepth;
        return AstStructuralPreflight.CheckAdmittedProgram(
                expr, effectiveLimit, AstConsumerProfile.EvaluatorIterativeJoinSpines, out facts, nodeCountHint, tables, observations,
                cancellationToken)
                is { } rejection
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
    /// Routing enforcement for the synchronous entry family, B2c half: a root carrying
    /// deferred module regions (conditional branches whose module dependencies load on
    /// demand) can select a branch only by awaiting the module downloader, which the
    /// synchronous pipeline is structurally unable to do. Rejected here, before any tree
    /// work, as a host configuration error — the same rule and the same shape as the
    /// asynchronous host-operation rejection above. An async entry's synchronous fast path
    /// hands in the fact it already decided for this call (<paramref name="treeRequiresAsyncEvaluation"/>,
    /// whose answer is always <c>false</c> there), so the tree is walked once per run; every other caller
    /// passes <c>null</c> and the tree is walked here. Either way <paramref name="nodeCountHint"/> is how
    /// many distinct nodes the deciding walk visited — the fact's count, or this walk's — a capacity hint
    /// for the admission tables built over the same graph next, never a decision. A walk made here that
    /// admits the run hands its visited set over to <paramref name="tables"/> for the validation walk.
    /// <para>A walk made here observes the run's <paramref name="cancellationToken"/> before its first edge and after
    /// every <see cref="AstStructuralPreflight.CancellationCheckpointEdges"/> edges
    /// (<see cref="FrontEndCancellationCheckpoint.EvaluatorRoute"/>, recorded in <paramref name="observations"/>). The
    /// synchronous family observes the token before every pre-evaluation verdict, this misconfiguration rejection
    /// included, so a cancellation requested before the walk reaches a placeholder escapes as that cancellation, as it
    /// would at the entry; the asynchronous host-operation rejection runs before this walk and is unaffected.</para>
    /// </summary>
    private static void ThrowIfDeferredModuleRegionsOnSynchronousEntry(
        Expr expr,
        TreeRouteFact? treeRequiresAsyncEvaluation,
        PreEvaluationTables tables,
        FrontEndTraversalObservations? observations,
        out int nodeCountHint,
        CancellationToken cancellationToken)
    {
        bool requiresAsyncEvaluation;
        if (treeRequiresAsyncEvaluation is { } decided)
        {
            requiresAsyncEvaluation = decided.RequiresAsyncEvaluation;
            nodeCountHint = decided.NodeCountHint;
        }
        else
        {
            requiresAsyncEvaluation = DeferredModuleRegion.RequiresAsyncEvaluationCounting(
                expr, out nodeCountHint, tables, observations, cancellationToken);
        }

        if (requiresAsyncEvaluation)
        {
            throw new InvalidOperationException(
                "The program contains conditional branches whose module dependencies load on demand " +
                "(deferred module regions), which a synchronous evaluation entry point cannot await. " +
                "Use RunAsync (or an async KatLangEngine entry point).");
        }
    }

    /// <summary>
    /// Shared pre-evaluation validation gate for every prebuilt-AST entry point.
    /// Lean: the validation pass <c>runResultM</c> runs before any evaluation
    /// (<c>validateExplicitParamOutputInvariantExpr</c>). Representable violations map
    /// onto Lean's validation errors; C# also rejects collecting clause binders,
    /// whose kind Lean's clause AST cannot express. A malformed hand-built tree — for
    /// example a conditional with mismatched branch arities — is rejected here,
    /// before branch matching, optimizer planning, or any evaluation, exactly
    /// where Lean rejects it. Runs after <see cref="StructuralPreflight"/> because
    /// the validation walk itself is recursive. The walk probes the host stack's
    /// reserve per level (<see cref="FrontEndStack"/>), so an entry on a stack too
    /// small to walk the tree is the structured
    /// <see cref="EvalError.EvaluationStackExhausted"/>, never an overflow.
    /// <para>That refusal is ROOT-LEVEL and carries no span. The gate walks the whole program
    /// before evaluation enters any written expression, and the node its walk had reached when the
    /// reserve ran out marks where the host stack ran short, not a written cause. Attaching that
    /// node's span would invent a position (Q-09a: where a stack refusal fires is never promised).
    /// The refusal does no evaluation work at all, which
    /// <c>EvaluatorOpenChainStackProcessTests.OneNameOpenChain_ProbeChild</c> pins (it is the only
    /// spanless refusal there, about 140 KiB and less on Windows x64).</para>
    /// <para>The walk sizes its tables from the preflight's node count, reuses the storage the run's earlier
    /// passes handed over (<paramref name="tables"/>, cleared), and builds no alias-reach table when the
    /// preflight proved the graph alias-free (<see cref="AstStructuralPreflight.AdmittedProgramFacts.IsAliasFree"/>):
    /// none of it changes a visit, a check, their order or a verdict.</para>
    /// </summary>
    private static EvalError? PreEvaluationValidationError(
        Expr expr,
        int nodeCountHint,
        bool graphIsAliasFree,
        PreEvaluationTables tables,
        FrontEndTraversalObservations? observations,
        CancellationToken cancellationToken)
    {
        PreEvaluationAstViolation? violation;
        try
        {
            violation = AlgorithmValidation.FindFirstPreEvaluationViolation(
                expr, observations, nodeCountHint, tables, graphIsAliasFree, cancellationToken);
        }
        catch (FrontEndStackExhaustedException)
        {
            return new EvalError.EvaluationStackExhausted();
        }

        return violation switch
        {
            null => null,
            PreEvaluationAstViolation.ExplicitParametersWithoutOutput v =>
                new EvalError.ExplicitParametersRequireOutput() { Span = v.Span },
            PreEvaluationAstViolation.ConditionalBranchArityMismatch v =>
                new EvalError.BranchArityMismatch(v.AlgorithmName, v.Expected, v.Actual),
            PreEvaluationAstViolation.SingletonSequencePattern v =>
                new EvalError.IllegalInEval(Parser.SingletonSequencePatternDiagnostic) { Span = v.Span },
            PreEvaluationAstViolation.MultipleCollectingCaptures =>
                new EvalError.IllegalInEval(Parser.MultipleCollectingBindingsPerLevelDiagnostic),
            PreEvaluationAstViolation.RepeatedNameIncludesCollecting =>
                new EvalError.IllegalInEval(Parser.RepeatedNameIncludesCollectingDiagnostic),
            PreEvaluationAstViolation.CollectingClauseBinder =>
                new EvalError.IllegalInEval(Parser.CollectingClauseBinderDiagnostic),
            PreEvaluationAstViolation.InvalidMetaParameter or PreEvaluationAstViolation.MetaClauseBinder =>
                new EvalError.IllegalInEval(Parser.InvalidMetaParameterDiagnostic),
            PreEvaluationAstViolation.ConditionalBranchOutputArityMismatch v =>
                new EvalError.BranchOutputArityMismatch(v.AlgorithmName, v.Expected, v.Actual),
            PreEvaluationAstViolation.AliasTargetNotStaticPath v =>
                new EvalError.IllegalInEval(AliasTargetNotStaticPathMessage(v.Target)) { Span = v.Target.Span },
            PreEvaluationAstViolation.AliasCycle v =>
                new EvalError.IllegalInEval(AliasCycleMessage) { Span = v.Target.Span },
        };
    }

    /// <summary>
    /// Outcome of the shared run-entry preparation: either a pre-evaluation rejection
    /// (<see cref="Error"/> non-null) or a ready root context (<see cref="Ctx"/>).
    /// <see cref="Budget"/> is the run's fresh budget in BOTH cases, so the observed
    /// harness entry points can hand back the budget a rejected run would have used.
    /// </summary>
    private readonly struct PreparedRun : IDisposable
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

        // Run-entry owners dispose on EVERY exit, including an exception. No allocation or
        // counter charge is added, and nested evaluator calls share the still-live budget.
        public void Dispose() => Budget.EndRun();

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
    /// misconfiguration rejection), then an asynchronous host-operation configuration and
    /// then a tree carrying deferred module regions (B2c) are rejected before any other tree
    /// work, then the shared admitted-run sequence runs. The
    /// async twin family prepares through <c>PrepareAsyncTwinRun</c>, whose guard order
    /// differs — that ordering difference is each wrapper's contract, so a new entry
    /// point must choose a wrapper, never call <see cref="PrepareAdmittedRun"/> directly.
    /// <paramref name="treeRequiresAsyncEvaluation"/> is the deferred-region fact an async
    /// entry already decided for THIS call in its synchronous prefix (<c>null</c>: not decided,
    /// the guard walks the tree); it is never stored. The run's <see cref="PreEvaluationTables"/>
    /// are created here and dropped when the preparation returns.
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
        long? randomSeed,
        TreeRouteFact? treeRequiresAsyncEvaluation,
        CancellationToken cancellationToken)
    {
        // Host cancellation preempts every pre-evaluation verdict: an already-cancelled
        // token stops the run before the structural preflight spends O(tree) work.
        cancellationToken.ThrowIfCancellationRequested();
        ThrowIfAsynchronousHostOperationsOnSynchronousEntry(hostOperations);
        // The hand-over between this run's pre-evaluation passes (storage only, never contents).
        var tables = new PreEvaluationTables();
        ThrowIfDeferredModuleRegionsOnSynchronousEntry(
            expr, treeRequiresAsyncEvaluation, tables, observations?.PreEvaluationTraversal, out var nodeCountHint, cancellationToken);

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
            randomSeed,
            asynchronousRun: false,
            nodeCountHint,
            tables,
            cancellationToken);
    }

    /// <summary>
    /// The ONE ordered non-evaluating preparation sequence shared by every evaluator
    /// run entry point, synchronous and async twin alike (none of it awaits):
    /// fresh run budget (which owns the run's fresh random stream, seeded from
    /// <paramref name="randomSeed"/> or from entropy), structural safety preflight,
    /// Lean-aligned pre-evaluation validation, cache argument validation, root context
    /// construction. A preflight or validation rejection observes the host token (a
    /// cancellation requested during the rejected pass still escapes as
    /// <see cref="OperationCanceledException"/>, never as the returned error) and hands
    /// the rejection back with the budget. Callers reach this only through
    /// <see cref="PrepareSynchronousRun"/> or <c>PrepareAsyncTwinRun</c>, which own the
    /// per-family entry guards and their ordering relative to the first token
    /// observation, and create the run's <paramref name="tables"/>.
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
        long? randomSeed,
        bool asynchronousRun,
        int nodeCountHint,
        PreEvaluationTables tables,
        CancellationToken cancellationToken)
    {
        // Creating the budget is field initialization plus the run's random-stream
        // construction (unseeded entropy is acquired here, once) — the structural
        // preflight still runs before any budget COUNTER can move and charges nothing.
        var budget = EvaluationBudget.Create(limits, hostOperations, randomSeed, cancellationToken);
        // META-S3-0b: the async twin family's run (its unpublished runtime projections are
        // resolved through the async resolution adapter, never synchronously).
        if (asynchronousRun) budget.MarkAsynchronousRun();

        // The two admission passes build reference-identity tables over the whole graph. Each is
        // sized from the node count an earlier walk of this run already produced (the entry guard's
        // or the async entry's tree fact's for the preflight, the preflight's for the validation
        // walk), and the validation walk reuses the storage of the tables the earlier passes handed
        // over (`tables`, cleared on take). Counts and storage are capacity only: every pass still
        // makes its own complete walk and its own decisions, in this order. The preflight also proves
        // whether the graph is alias-free, which spares the validation walk an alias-reach table that
        // could only answer `false`.
        var admissionObservations = observations?.PreEvaluationTraversal;
        if (StructuralPreflight(expr, limits, nodeCountHint, tables, admissionObservations, out var programFacts, cancellationToken)
            is { } structuralError)
        {
            budget.ObserveCancellation();
            return PreparedRun.Rejected(structuralError, budget);
        }

        if (PreEvaluationValidationError(expr, programFacts.NodeCount, programFacts.IsAliasFree, tables, admissionObservations,
                cancellationToken)
            is { } validationError)
        {
            budget.ObserveCancellation();
            return PreparedRun.Rejected(validationError, budget);
        }

        ArgumentNullException.ThrowIfNull(zeroArgPropertyResultCache);

        // J7: the run's one, immutable plan-retention decision, read by the structural preflight's
        // walk over the admitted program, taken before any supplied cell exists. A per-site run's transport-name
        // analysis observes the run's token in bounded blocks (Evaluator.TransportAnalysisWork).
        budget.DecideInvocationPlanRetention(programFacts.MayCaptureCalls, programFacts.IsLoopOnly, expr, programFacts.TreeNodeCount,
            observations?.TransportAnalysisTraversal);
        // META-S3-2: a run that may reach a runtime-target alias is pre-marked before any resolver runs.
        budget.DecideRuntimeAliasReach(programFacts.MayReachRuntimeAlias, programFacts.HasDeferredModuleRegion);
        // B2c: a deferred body is admitted by the run that consumes it, at its position in this root.
        // Its walks observe the run's token in bounded blocks (DeferredBodyAdmission, Cancellation).
        if (programFacts.HasDeferredModuleRegion)
            budget.RecordDeferredBodyAdmission(
                expr, (limits ?? EvaluationLimits.Default).EffectiveMaxAstDepth, observations?.DeferredAdmissionTraversal);

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
        long? randomSeed = null,
        TreeRouteFact? treeRequiresAsyncEvaluation = null,
        CancellationToken cancellationToken = default)
    {
        using var preparation = PrepareSynchronousRun(
            expr,
            zeroArgPropertyResultCache,
            enableLoopOptimization,
            loopDiagnostics,
            enableSequencePipelineOptimization,
            sequenceDiagnostics,
            limits,
            observations,
            hostOperations,
            randomSeed,
            treeRequiresAsyncEvaluation,
            cancellationToken);
        if (preparation.Error is { } preparationError)
            return preparationError;

        var ctx = preparation.Ctx;
        var result = expr is Expr.AlgorithmExpr(var alg)
            ? ProjectCountedValue(EvalRootProgramCounted(alg, expr.Span, ctx))
            : Eval(expr, ctx, []);

        // The run result boundary (CallReference S1): a call reference never leaves its run.
        result = ExportRunValue(result, expr, ctx);

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
        EvaluationLimits? limits = null,
        long? randomSeed = null)
        => Run(
            expr,
            new RunScopedZeroArgPropertyResultCache(collectStatistics: false),
            enableLoopOptimization: enableOptimizations,
            loopDiagnostics: null,
            enableSequencePipelineOptimization: enableOptimizations,
            sequenceDiagnostics: null,
            limits,
            observations,
            randomSeed: randomSeed);

    internal static EvalResult<CountedResult> RunCounted(Expr expr)
        => RunCounted(expr, new RunScopedZeroArgPropertyResultCache(collectStatistics: false));

    /// <summary>
    /// Harness entry point: evaluates exactly like <see cref="RunCounted(Expr, IZeroArgPropertyResultCache, EvaluationLimits?, HostOperations?, long?, TreeRouteFact?, CancellationToken)"/>
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
    /// <see cref="Run(Expr, IZeroArgPropertyResultCache, bool, LoopOptimizationDiagnostics?, bool, SequencePipelineDiagnostics?, EvaluationLimits?, EvaluationObservations?, HostOperations?, long?, TreeRouteFact?, CancellationToken)"/>
    /// overload already exposes, so an observed run can additionally record which execution
    /// path the optimizers actually took (planned, fused, fallen back, or generic). They are
    /// write-only counters the evaluator increments through a null-conditional call: supplying
    /// one cannot change optimizer eligibility, evaluation order, or any result.</para>
    ///
    /// <para><paramref name="rootOutputRows"/> attaches a caller-made root output-row recorder
    /// (<see cref="RootOutputRowRecorder"/>, made over the root's own output rows) for this run's
    /// evaluation, exactly as the engine's funnel attaches its own, so a test can compare a recorded
    /// run with an unrecorded one counter for counter. It is as passive as the collectors.</para>
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
        long? randomSeed = null,
        TreeRouteFact? treeRequiresAsyncEvaluation = null,
        RootOutputRowRecorder? rootOutputRows = null,
        CancellationToken cancellationToken = default)
    {
        using var preparation = PrepareSynchronousRun(
            expr,
            zeroArgPropertyResultCache ?? new RunScopedZeroArgPropertyResultCache(collectStatistics: false),
            enableLoopOptimization: enableOptimizations,
            loopDiagnostics,
            enableSequencePipelineOptimization: enableOptimizations,
            sequenceDiagnostics,
            limits,
            observations,
            hostOperations,
            randomSeed,
            treeRequiresAsyncEvaluation,
            cancellationToken);
        if (preparation.Error is { } preparationError)
            return (preparationError, preparation.Budget);

        var ctx = preparation.Ctx;
        EvalResult<CountedResult> result;
        ctx.Budget.RootOutputRows = rootOutputRows;
        try
        {
            result = ExportRunValue(expr is Expr.AlgorithmExpr(var alg)
                ? EvalRootProgramCounted(alg, expr.Span, ctx)
                : EvalCounted(expr, ctx, []), expr, ctx);
        }
        finally
        {
            ctx.Budget.RootOutputRows = null;
        }

        ctx.Budget.ObserveCancellation();
        return (result, ctx.Budget);
    }

    internal static EvalResult<CountedResult> RunCounted(
        Expr expr,
        IZeroArgPropertyResultCache zeroArgPropertyResultCache,
        EvaluationLimits? limits = null,
        HostOperations? hostOperations = null,
        long? randomSeed = null,
        TreeRouteFact? treeRequiresAsyncEvaluation = null,
        CancellationToken cancellationToken = default)
    {
        using var preparation = PrepareSynchronousRun(
            expr,
            zeroArgPropertyResultCache,
            enableLoopOptimization: true,
            loopDiagnostics: null,
            enableSequencePipelineOptimization: true,
            sequenceDiagnostics: null,
            limits,
            observations: null,
            hostOperations,
            randomSeed,
            treeRequiresAsyncEvaluation,
            cancellationToken);
        if (preparation.Error is { } preparationError)
            return preparationError;

        var ctx = preparation.Ctx;
        var result = ExportRunValue(expr is Expr.AlgorithmExpr(var alg)
            ? EvalRootProgramCounted(alg, expr.Span, ctx)
            : EvalCounted(expr, ctx, []), expr, ctx);

        ctx.Budget.ObserveCancellation();
        return result;
    }

    /// <summary>
    /// The counted run plus the root's named top-level properties — the funnel
    /// <see cref="KatLangEngine.Run"/> evaluates through. After the output SUCCEEDS, each name in
    /// <paramref name="topLevelPropertyNames"/> is read in the given order by the ordinary cached
    /// zero-argument VALUE read of the same run (same budget, property cache, random stream, host
    /// operations and cancellation token); a name the root does not declare reads as <c>null</c>
    /// without touching the cache. The FIRST failing read fails the run with its own error and no
    /// later name is attempted; a failed output reads none.
    /// </summary>
    internal static EvalResult<CountedRootProgramResult> RunCountedWithTopLevelProperties(
        Expr expr,
        IReadOnlyList<string> topLevelPropertyNames,
        IZeroArgPropertyResultCache zeroArgPropertyResultCache,
        EvaluationLimits? limits = null,
        HostOperations? hostOperations = null,
        long? randomSeed = null,
        TreeRouteFact? treeRequiresAsyncEvaluation = null,
        CancellationToken cancellationToken = default)
    {
        using var preparation = PrepareSynchronousRun(
            expr,
            zeroArgPropertyResultCache,
            enableLoopOptimization: true,
            loopDiagnostics: null,
            enableSequencePipelineOptimization: true,
            sequenceDiagnostics: null,
            limits,
            observations: null,
            hostOperations,
            randomSeed,
            treeRequiresAsyncEvaluation,
            cancellationToken);
        if (preparation.Error is { } preparationError)
            return preparationError;

        RequireTopLevelPropertyNames(topLevelPropertyNames);

        var ctx = preparation.Ctx;
        EvalResult<CountedRootProgramResult> result;
        if (expr is Expr.AlgorithmExpr(var alg))
        {
            result = EvalRootProgramCountedWithTopLevelProperties(alg, expr.Span, ctx, topLevelPropertyNames);
        }
        else
        {
            var outputR = MaterializeRunOutput(EvalCounted(expr, ctx, []), ctx);
            result = outputR.IsError
                ? outputR.Error
                : EvalResult<CountedRootProgramResult>.Ok(
                    new CountedRootProgramResult(outputR.Value, new CountedResult?[topLevelPropertyNames.Count]));
        }

        result = ExportRunValue(result, expr, topLevelPropertyNames, ctx);
        ctx.Budget.ObserveCancellation();
        return result;
    }

    /// <summary>
    /// The argument contract of the top-level property names shared by
    /// <see cref="RunCountedWithTopLevelProperties"/> and its async twin: a non-null list of
    /// non-blank names.
    /// </summary>
    private static void RequireTopLevelPropertyNames(IReadOnlyList<string> topLevelPropertyNames)
    {
        ArgumentNullException.ThrowIfNull(topLevelPropertyNames);
        for (var i = 0; i < topLevelPropertyNames.Count; i++)
            ArgumentException.ThrowIfNullOrWhiteSpace(topLevelPropertyNames[i], nameof(topLevelPropertyNames));
    }

    /// <summary>
    /// The root program of a run, wired to its caller and then evaluated by the ONE root body
    /// <see cref="EvalWiredRootProgramCounted"/>. The plain run reads it through
    /// <see cref="ProjectCountedValue"/>, so the root has no independent plain body.
    /// </summary>
    private static EvalResult<CountedResult> EvalRootProgramCounted(Algorithm alg, SourceSpan? span, EvalCtx ctx)
        => EvalWiredRootProgramCounted(WireToCaller(ctx, alg), span, ctx);

    /// <summary>
    /// Evaluate a WIRED root program algorithm when a result is requested: the ONE body of the
    /// root-program contract, which every root route (plain, counted, and with top-level
    /// properties) reaches. The root is demanded for its value with NOTHING supplied, so it goes
    /// through the ONE zero-argument demand funnel (<see cref="EvalZeroArgumentDemandOutputCounted"/>):
    /// a root declaring no parameter pattern is its output exactly as before, and a root whose
    /// parameter list accepts an EMPTY supply (a collecting-only host-built root) binds that
    /// supply first. A root whose parameter list still REQUIRES a supplied argument has
    /// unresolved implicit parameters, reported at <paramref name="span"/>, else at its first
    /// output row. A <see cref="EvalError.MissingOutput"/> of a user root with no output row
    /// gains the C#-only <see cref="ProgramEvaluationContext"/> frame, at the error's own span,
    /// else at <paramref name="span"/>. Lean: <c>evalProgramOutput</c> (the acceptance check is
    /// <c>runResultM</c>'s).
    /// </summary>
    private static EvalResult<CountedResult> EvalWiredRootProgramCounted(Algorithm wired, SourceSpan? span, EvalCtx ctx)
    {
        if (AcceptsZeroSuppliedArguments(wired))
        {
            var result = EvalZeroArgumentDemandOutputCounted(wired, ctx, []);
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

    private static EvalResult<CountedRootProgramResult> EvalRootProgramCountedWithTopLevelProperties(
        Algorithm alg,
        SourceSpan? span,
        EvalCtx ctx,
        IReadOnlyList<string> topLevelPropertyNames)
    {
        // ONE wired instance feeds the output and every property read (the property cache's owner identity).
        var wired = WireToCaller(ctx, alg);
        // The root claims the recorder on row-loop entry. Clear an unclaimed offer on every exit.
        var rootOutputRows = new RootOutputRowRecorder(wired.Output);
        EvalResult<CountedResult> outputR;
        ctx.Budget.RootOutputRows = rootOutputRows;
        try
        {
            outputR = EvalWiredRootProgramCounted(wired, span, ctx);
        }
        finally
        {
            ctx.Budget.RootOutputRows = null;
        }
        if (outputR.IsError)
            return outputR.Error;

        // Read only now that the root output succeeded: counts never accompany a failure.
        var rootRowSlotCounts = rootOutputRows.TakeSlotCounts();

        // THE RUN RESULT IS MATERIALIZED (issue #204): the assembled output first — before any
        // named property is read, so the run's value is what every other entry point returns —
        // and then each named property's value as it is read.
        outputR = MaterializeRunOutput(outputR, ctx);
        if (outputR.IsError)
            return outputR.Error;

        // In the given order; the first failing read is the run's failure and no later name is read.
        var properties = new CountedResult?[topLevelPropertyNames.Count];
        for (var i = 0; i < properties.Length; i++)
        {
            var propertyR = EvalTopLevelZeroArgPropertyCounted(wired, topLevelPropertyNames[i], ctx, []);
            if (propertyR.IsError)
                return propertyR.Error;

            if (propertyR.Value is { } read)
            {
                var wholeR = MaterializeRunOutput(EvalResult<CountedResult>.Ok(read), ctx);
                if (wholeR.IsError)
                    return wholeR.Error;
                properties[i] = wholeR.Value;
            }
        }

        return EvalResult<CountedRootProgramResult>.Ok(
            new CountedRootProgramResult(outputR.Value, properties) { RootRowSlotCounts = rootRowSlotCounts });
    }

    private static EvalResult<CountedResult?> EvalTopLevelZeroArgPropertyCounted(
        Algorithm alg,
        string name,
        EvalCtx ctx,
        ValEnv valEnv)
    {
        var binding = LookupPropBinding(alg, name, ctx.Budget);
        if (binding is null)
            return EvalResult<CountedResult?>.Ok(null);

        // An alias binding reads its VALUE terminal (OD-E, M4★): the terminal binding's own entry, or a
        // runtime-target alias's binding cell — never an entry of its own.
        var resolvedR = NormalizeTopLevelBinding(alg, binding, ChildOf(alg, binding.Value), ctx);
        if (resolvedR.IsError)
            return resolvedR.Error;
        var resolvedAlgorithm = resolvedR.Value.ResolvedAlgorithm;
        var span = binding.FirstDeclarationSpan;
        // A named top-level property read is an ordinary zero-argument value demand, so
        // the ONE law decides and shapes its report: a callable that cannot accept zero
        // supplied arguments is the property-context mismatch naming its true minimum
        // supply, and a clause family keeps its ordinary dispatch failure.
        if (resolvedAlgorithm is not Algorithm.Alias
            && ZeroArgumentValueDemandRejection(ZeroArgumentDemandShape.Property, name, span, resolvedAlgorithm) is { } rejection)
            return rejection;

        // A reference's missing output is its TERMINAL binding's (M4★), which the report names.
        var propertyR = WithPropertyContextOnMissingOutput(
            resolvedR.Value.Binding.Name,
            span,
            resolvedAlgorithm,
            // An ordinary binding keeps its direct frame chain (FRAME-SIZE DISCIPLINE; an alias read is out of line).
            resolvedR.Value is { ResolvedAlgorithm: not Algorithm.Alias, CrossesCarrier: false }
                ? EvalZeroArgPropertyAccessCounted(resolvedR.Value, ctx, valEnv)
                : ReadValueBindingCounted(resolvedR.Value, ctx, valEnv));

        return propertyR.IsError
            ? propertyR.Error
            : EvalResult<CountedResult?>.Ok(propertyR.Value);
    }

    /// <summary>
    /// Run evaluation and flatten to atoms at the host boundary: the numeric atoms reachable
    /// through sequence AND exact list boundaries, depth-first and left to right, so
    /// collection-builtin results surface their numeric contents. Booleans and strings are
    /// omitted; use <see cref="Run(Expr)"/> for the complete value. The projection is bounded
    /// like the engine's <see cref="RunResult.Success.Atoms"/>: more atoms than the effective
    /// <see cref="EvaluationLimits.MaxCollectionItems"/> is
    /// <see cref="EvalError.CollectionSizeLimitExceeded"/>, never an unbounded allocation.
    /// Lean: runFlat → EvalM (List Int).
    /// </summary>
    /// <exception cref="ArgumentNullException"><paramref name="expr"/> is null.</exception>
    /// <exception cref="InvalidOperationException">
    /// <paramref name="expr"/> carries a deferred module region (see <see cref="Run(Expr)"/>).
    /// </exception>
    public static EvalResult<IReadOnlyList<Decimal128>> RunFlat(Expr expr)
        => RunFlat(expr, limits: null);

    /// <summary>Host-boundary flattening run under explicit resource limits.</summary>
    /// <exception cref="InvalidOperationException">
    /// <paramref name="expr"/> carries a deferred module region (see <see cref="Run(Expr)"/>).
    /// </exception>
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
    /// <exception cref="InvalidOperationException">
    /// <paramref name="expr"/> carries a deferred module region (see <see cref="Run(Expr)"/>).
    /// </exception>
    public static EvalResult<IReadOnlyList<Decimal128>> RunFlat(
        Expr expr, EvaluationLimits? limits, CancellationToken cancellationToken)
        => RunFlat(expr, limits, randomSeed: null, cancellationToken);

    /// <summary>
    /// Host-boundary flattening run under explicit resource limits, an optional random
    /// seed, and cooperative host cancellation. Same seed contract as
    /// <see cref="Run(Expr, EvaluationLimits?, long?, CancellationToken)"/>; same
    /// projection and cancellation contract as
    /// <see cref="RunFlat(Expr, EvaluationLimits?, CancellationToken)"/>.
    /// </summary>
    /// <exception cref="OperationCanceledException">
    /// <paramref name="cancellationToken"/> was cancelled before or during evaluation.
    /// </exception>
    /// <exception cref="InvalidOperationException">
    /// <paramref name="expr"/> carries a deferred module region (see <see cref="Run(Expr)"/>).
    /// </exception>
    public static EvalResult<IReadOnlyList<Decimal128>> RunFlat(
        Expr expr, EvaluationLimits? limits, long? randomSeed, CancellationToken cancellationToken)
        => ProjectFlatHostAtoms(Run(expr, limits, randomSeed, cancellationToken), limits, cancellationToken);

    /// <summary>
    /// Evaluates a host-built AST with synchronous host operations and returns its bounded,
    /// lossy numeric projection. Uses the same invocation and limit rules as
    /// <see cref="Run(Expr, HostOperations, EvaluationLimits?, long?, CancellationToken)"/>;
    /// strings and Booleans are omitted and both list and sequence boundaries are opened.
    /// </summary>
    /// <exception cref="ArgumentNullException"><paramref name="expr"/> or <paramref name="hostOperations"/> is null.</exception>
    /// <exception cref="InvalidOperationException">
    /// The operations, or a deferred module region in <paramref name="expr"/>, require
    /// asynchronous evaluation (see <see cref="Run(Expr)"/>).
    /// </exception>
    /// <exception cref="OperationCanceledException">Evaluation or projection was cancelled.</exception>
    public static EvalResult<IReadOnlyList<Decimal128>> RunFlat(
        Expr expr, HostOperations hostOperations, EvaluationLimits? limits, long? randomSeed, CancellationToken cancellationToken)
        => ProjectFlatHostAtoms(Run(expr, hostOperations, limits, randomSeed, cancellationToken), limits, cancellationToken);

    /// <summary>
    /// The flat entry family's host-boundary projection, shared by <see cref="RunFlat(Expr, EvaluationLimits?, CancellationToken)"/>
    /// and <see cref="RunFlatAsync(Expr, EvaluationLimits?, CancellationToken)"/> (it
    /// awaits nothing). Same rule as the engine: the host projection is bounded, so a
    /// successful evaluation cannot be followed by an unbounded flattening allocation.
    /// Host flattening belongs to the flat run operation and may walk a bounded but wide
    /// value graph after core evaluation has completed, so the projection observes the
    /// token DURING the walk (every 256 slot reads or replayed atoms) and once more after
    /// it. The refusal stays the bare <see cref="EvalError.CollectionSizeLimitExceeded"/>
    /// hosts of this entry family may type-match.
    /// </summary>
    private static EvalResult<IReadOnlyList<Decimal128>> ProjectFlatHostAtoms(
        EvalResult<Result> evaluation, EvaluationLimits? limits, CancellationToken cancellationToken)
    {
        if (evaluation.IsError) return evaluation.Error;

        var limit = (limits ?? EvaluationLimits.Default).EffectiveMaxCollectionItems;
        var result = evaluation.Value.TryToHostAtoms(limit, out var atoms, cancellationToken)
            ? EvalResult<IReadOnlyList<Decimal128>>.Ok(atoms)
            : new EvalError.CollectionSizeLimitExceeded(limit, limit + 1L);

        cancellationToken.ThrowIfCancellationRequested();
        return result;
    }


    // ── Utility ──────────────────────────────────────────────────────────────

    /// <summary>
    /// Shared exponentiation for <c>^</c>, <c>Math.Pow</c>, and <c>pow</c>.
    /// Finite nonzero bases with integral |exponent| &lt;= long.MaxValue use
    /// <see cref="Decimal128Numerics.TryIntegerPower(Decimal128, long, out Decimal128)"/> except for the existing
    /// negative-exponent overflow delegation described below. Successful certified
    /// results round the exact input power once to Decimal128, ties to even;
    /// negative exponents certify the reciprocal before target rounding.
    /// Exact positive powers retain the preferred quantum (2^10 is 1024).
    /// Reciprocals retain the previous division's quantum whenever its numerical
    /// result agrees with the certified result (including the exact 5^-50).
    /// <para>Refinement starts at 34 + digits(|n|) + 8 and doubles up to 4096
    /// working digits, including the final capped attempt. The helper's midpoint
    /// argument establishes eventual certification, not success within this cap.
    /// Exhaustion returns IllegalInEval with the expression span, never an
    /// uncertified approximation. The optional internal precision arguments are
    /// a test seam for this otherwise difficult-to-reach error path.</para>
    /// <para>The delegation domain is unchanged from before B4: fractional,
    /// non-finite, and beyond-long exponents, plus negative integral exponents
    /// whose legacy positive-power chain overflows (10^-6146 remains a nonzero
    /// subnormal), take <see cref="DelegatedPower"/> — Decimal128.Pow, or the
    /// near-one fixed-point power for a finite exponent over a base whose MAGNITUDE
    /// is in the near-one band. These results are quantum-canonicalized and are
    /// not covered by the certification guarantee. Special bases retain IEEE
    /// sign/parity and x^0 is 1.</para>
    /// <para>ZERO BASE, NEGATIVE EXPONENT: a zero-valued base (signed zeros included)
    /// raised to ANY exponent below zero is the KatLang error decided here, before
    /// any delegation — whether the exponent is integral is irrelevant, so
    /// <c>0 ^ -1</c>, <c>0 ^ -0.5</c>, and <c>Math.Pow(0, -2.5)</c> reject alike
    /// (a negative power of zero is reciprocal-like, and KatLang treats a zero
    /// divisor as an error rather than adopting IEEE's <c>Infinity</c>). The
    /// comparison is IEEE, so a NaN exponent is not "below zero" and keeps its
    /// propagating NaN result, while <c>-Infinity</c> is and rejects. The Lean
    /// model states the same rule at its integer instance (<c>negativeIntPow</c>);
    /// fractional exponents are Decimal128-only.</para>
    /// </summary>
    internal static EvalResult<Result> EvalPow(
        SourceSpan? span, Decimal128 b, Decimal128 exp,
        int? initialWorkingDigits = null, int maxWorkingDigits = Decimal128Numerics.MaxWorkingDigits)
    {
        if (b == 0 && exp < 0)
            return new EvalError.IllegalInEval("zero cannot be raised to a negative exponent") { Span = span };

        if (TryDecimal128Pow(b, exp, initialWorkingDigits, maxWorkingDigits, out var result))
            return EvalResult<Result>.Ok(new Result.Atom(result));

        // The certification loop reached its working-precision cap without an
        // unambiguous rounding decision. Fail loudly: returning the nearest
        // uncertified digit would silently break the correct-rounding contract.
        return new EvalError.IllegalInEval(
            $"the correctly rounded value of {FormatNumber(b)} ^ {FormatNumber(exp)} could not be certified "
            + $"within the {maxWorkingDigits}-digit working-precision limit")
        { Span = span };
    }

    private static string FormatNumber(Decimal128 value)
        => Rendering.ValueTextRenderer.FormatNumberInvariant(value);

    private static bool TryDecimal128Pow(
        Decimal128 b, Decimal128 exp, int? initialWorkingDigits, int maxWorkingDigits, out Decimal128 result)
    {
        // IsInteger is false for NaN and the infinities, so non-finite exponents
        // take Decimal128.Pow's IEEE behavior. Integral exponents beyond long also
        // delegate: IEEE pow fully specifies the special bases (0, ±1, NaN, the
        // infinities resolve exactly by sign and parity — pinned by tests), and for
        // any other finite base the true power needs more than 34 digits, so no
        // squaring loop could deliver exactness either; bases of magnitude very
        // close to 1 give genuine finite approximations, which the near-one power
        // computes (DelegatedPower).
        if (!Decimal128.IsInteger(exp) || Decimal128.Abs(exp) > long.MaxValue)
        {
            result = CanonicalizeMathResult(DelegatedPower(b, exp));
            return true;
        }

        // |exp| <= long.MaxValue, so the narrowing is exact and negation cannot
        // overflow.
        var exponent = (long)exp;
        if (exponent == 0 || !Decimal128.IsFinite(b) || b == 0)
        {
            // x ^ 0 is 1 for every base, and the special bases (NaN, the infinities,
            // signed zero) only ever produce sign-and-parity outcomes: every product
            // of the chain is exact, so the plain Decimal128 chain is the exact
            // answer here. (Zero with a negative exponent is rejected by EvalPow.)
            result = exponent < 0
                ? Decimal128.One / PowNonNegative(b, (ulong)(-exponent))
                : PowNonNegative(b, (ulong)exponent);
            return true;
        }

        Decimal128? previousReciprocal = null;
        if (exponent < 0)
        {
            var positivePower = PowNonNegative(b, (ulong)(-exponent));
            if (Decimal128.IsInfinity(positivePower))
            {
                // Preserve the pre-B4 delegation domain: a positive intermediate
                // can overflow while its reciprocal is a representable subnormal.
                result = CanonicalizeMathResult(DelegatedPower(b, exp));
                return true;
            }

            previousReciprocal = Decimal128.One / positivePower;
        }

        if (!Decimal128Numerics.TryIntegerPower(
                b, exponent,
                initialWorkingDigits ?? Decimal128Numerics.Precision
                    + Decimal128Numerics.DigitCount((BigInteger)System.Math.Abs(exponent))
                    + Decimal128Numerics.InitialGuardDigits,
                maxWorkingDigits, out result))
            return false;

        // The old chain supplies ONLY a compatible quantum, after certification.
        // In particular 5^-50 is exact even though 5^50 is not representable.
        // Never use that rounded positive power as the input to certification.
        if (previousReciprocal is { } previous && previous == result)
            result = previous;
        return true;
    }

    /// <summary>
    /// The DELEGATED power — every shape the certified integer path does not take (a
    /// fractional, non-finite, or beyond-<see cref="long"/> exponent, and a negative
    /// integral exponent whose positive power overflows): the platform
    /// <see cref="Decimal128.Pow"/>, except for a finite exponent over a base whose
    /// MAGNITUDE lies in the near-one band. The platform power inherits the logarithm's
    /// cancellation near 1 there (see <see cref="Decimal128Numerics.IsInNearOnePowerBand"/>),
    /// so the band takes <see cref="Decimal128Numerics.NearOnePower"/> instead — for a
    /// NEGATIVE base too (numeric audit #6, September 2026): the band once admitted only
    /// positive bases, so <c>(-0.9999999999999999999999999999999999) ^ 1e34</c> kept four
    /// correct digits while its positive twin kept all 34. A negative base reaches the band
    /// only with an integral exponent (a fractional power of a negative base stays the
    /// platform's NaN) and takes its magnitude's power with the exponent's parity sign —
    /// the sign rule the certified integer path applies — so <c>(-b) ^ n</c> is exactly
    /// <c>(-1) ^ n · b ^ n</c> on both sides of every routing boundary.
    /// </summary>
    private static Decimal128 DelegatedPower(Decimal128 b, Decimal128 exp)
    {
        if (Decimal128.IsFinite(exp) && Decimal128Numerics.IsInNearOnePowerBand(Decimal128.Abs(b)))
        {
            if (!Decimal128.IsNegative(b))
                return Decimal128Numerics.NearOnePower(b, exp);
            if (Decimal128.IsInteger(exp))
            {
                var magnitude = Decimal128Numerics.NearOnePower(-b, exp);
                return Decimal128.IsOddInteger(exp) ? -magnitude : magnitude;
            }
        }

        return Decimal128.Pow(b, exp);
    }

    /// <summary>
    /// Decimal128 exponentiation by squaring, used for special bases, the existing
    /// reciprocal overflow delegation, and compatible reciprocal quantum selection.
    /// It is not an accuracy oracle for ordinary finite bases: each Decimal128
    /// multiplication would otherwise round, and those roundings compound to a
    /// relative error of about |n| half-ulps — see <see cref="Decimal128Numerics"/>
    /// for the certified path that ordinary finite bases take.
    /// </summary>
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

    // A call-stack node of an ANNOTATED context (detached, or inside a retained cell's computation) is an
    // annotated node carrying the same annotations, so every context derived by a push inherits them;
    // every other push builds the node it always built.
    private static IReadOnlyList<T> Prepend<T>(T item, IReadOnlyList<T> list)
        => list is AnnotatedReadOnlyList<T> annotated
            ? new AnnotatedPrependedReadOnlyList<T>(item, list, annotated.DetachedBefore, annotated.Annotations)
            : new PrependedReadOnlyList<T>(item, list);

    /// <summary>Detached lexical activation serials. These immutable sets carry no references to calls or
    /// need cells, including when a retained cell records the owners of a reader that has returned.</summary>
    internal sealed class DetachedOwnerSet(long serial, DetachedOwnerSet? next = null)
    {
        internal long Serial { get; } = serial;
        internal DetachedOwnerSet? Next { get; } = next;
        private readonly long _maximum = Math.Max(serial, next?._maximum ?? 0);

        internal bool Contains(long value)
        {
            for (var node = this; node is not null && value <= node._maximum; node = node.Next)
                if (node.Serial == value) return true;
            return false;
        }

        internal static DetachedOwnerSet? With(ScopeCtx? chain, DetachedOwnerSet? owners)
        {
            if (DeclaringActivation(chain) is null) return owners;
            for (var scope = chain; scope is not null; scope = scope.Parent)
                if (scope.Activation is { } activation && owners?.Contains(activation.Serial) != true)
                    owners = new(activation.Serial, owners);
            return owners;
        }

        internal static DetachedOwnerSet? Union(DetachedOwnerSet? owners, DetachedOwnerSet? additions, long below = long.MaxValue)
        {
            if (owners is null && additions is not null && additions._maximum < below) return additions;
            for (var node = additions; node is not null && !ReferenceEquals(node, owners); node = node.Next)
                if (node.Serial < below && owners?.Contains(node.Serial) != true)
                    owners = new(node.Serial, owners);
            return owners;
        }
    }

    // The input record and the detached owners of an annotated node that has both (a detached evaluation
    // inside a retained cell's computation whose binding encloses an activated level). Either alone is
    // stored as itself, so a node keeps the size it had before the owners existed.
    private sealed class AnnotationPair(AliasCellInputs inputRecord, DetachedOwnerSet owners)
    {
        internal AliasCellInputs InputRecord { get; } = inputRecord;

        internal DetachedOwnerSet Owners { get; } = owners;
    }

    /// <summary>
    /// A call stack that carries an ACTIVATION WATERMARK (EXPORTED-DETACHED, November 2026;
    /// <see cref="EvalCtx.DetachedBefore"/>) — the stack of a context inside an exported evaluation —
    /// and/or an INPUT RECORD (ledger R-1, November 2026; <see cref="EvalCtx.InputRecord"/>) — the stack
    /// of a context inside a retained runtime-alias cell's computation. Both live on the call-stack node
    /// instead of <see cref="EvalCtx"/>, which is copied by value through calibrated frames, so no
    /// evaluator frame grows; and only annotated contexts build these nodes, so a context outside every
    /// exported evaluation and every retained cell's computation allocates exactly the
    /// <see cref="PrependedReadOnlyList{T}"/> it always did. Two shapes: the marker an annotation starts
    /// with (<see cref="AnnotationMarkerReadOnlyList{T}"/>, element-free) and a head pushed above an
    /// annotated stack (<see cref="AnnotatedPrependedReadOnlyList{T}"/>). A detached stack also carries its
    /// DETACHED OWNERS (<see cref="EvalCtx.DetachedOwners"/>), in the slot of the input record
    /// (<see cref="Annotations"/>).
    /// </summary>
    private abstract class AnnotatedReadOnlyList<T>(long detachedBefore, object? annotations) : IReadOnlyList<T>
    {
        /// <summary>
        /// Activations with a serial below this are detached in the context when they are detached owners
        /// (zero: none is).
        /// </summary>
        internal readonly long DetachedBefore = detachedBefore;

        /// <summary>
        /// The input record and the detached owners in one slot: null, an <see cref="AliasCellInputs"/>, a
        /// <see cref="DetachedOwnerSet"/>, or an <see cref="AnnotationPair"/> of both. A push passes it on as it is.
        /// </summary>
        internal readonly object? Annotations = annotations;

        /// <summary>The record of the retained cell whose computation the context belongs to, if any.</summary>
        internal AliasCellInputs? InputRecord
            => Annotations switch
            {
                AliasCellInputs record => record,
                AnnotationPair pair => pair.InputRecord,
                _ => null,
            };

        /// <summary>The detached owners of the context, if any (<see cref="EvalCtx.DetachedOwners"/>).</summary>
        internal DetachedOwnerSet? Owners
            => Annotations switch
            {
                DetachedOwnerSet owners => owners,
                AnnotationPair pair => pair.Owners,
                _ => null,
            };

        private static object? Pack(AliasCellInputs? inputRecord, DetachedOwnerSet? owners)
            => inputRecord is null ? owners : owners is null ? inputRecord : new AnnotationPair(inputRecord, owners);

        public abstract int Count { get; }

        public abstract T this[int index] { get; }

        public abstract IEnumerator<T> GetEnumerator();

        IEnumerator IEnumerable.GetEnumerator()
            => GetEnumerator();

        /// <summary>The stack this node annotates or extends: the next node outwards.</summary>
        internal abstract IReadOnlyList<T> Below { get; }

        private static long WatermarkOf(IReadOnlyList<T> stack)
            => stack is AnnotatedReadOnlyList<T> annotated ? annotated.DetachedBefore : 0;

        /// <summary>
        /// <paramref name="stack"/> under at least <paramref name="watermark"/>, with the activations of
        /// <paramref name="declaringChain"/> added to its detached owners: the same elements, the same input
        /// record, and a watermark that a nested detachment never lowers. A marker that carries no watermark of
        /// its own (it only marked an input record, or only added owners) is never wrapped in a marker, so a
        /// re-marked stack reads its elements in one hop; a marker that does carry one stays in the chain,
        /// because the watermark it holds is the one in force outside this detachment
        /// (<see cref="Reattach"/>).
        /// </summary>
        internal static AnnotatedReadOnlyList<T> Mark(IReadOnlyList<T> stack, long watermark, ScopeCtx? declaringChain)
        {
            if (stack is not AnnotatedReadOnlyList<T> annotated)
                return new AnnotationMarkerReadOnlyList<T>(stack, watermark, DetachedOwnerSet.With(declaringChain, null));

            watermark = Math.Max(watermark, annotated.DetachedBefore);
            var owners = annotated.Owners;
            var extended = DetachedOwnerSet.With(declaringChain, owners);
            return new AnnotationMarkerReadOnlyList<T>(
                annotated is AnnotationMarkerReadOnlyList<T> marker && marker.DetachedBefore == WatermarkOf(marker.Inner)
                    ? marker.Inner
                    : stack,
                watermark,
                ReferenceEquals(extended, owners) ? annotated.Annotations : Pack(annotated.InputRecord, extended));
        }

        /// <summary>
        /// <paramref name="stack"/> under the watermark that was in force when the activation with serial
        /// <paramref name="activationSerial"/> was recorded (Lean <c>EvalCtx.attachedLevel</c>): the first
        /// watermark, from this node outwards, that does not detach it — zero when every one does. The same
        /// elements, input record and detached owners (Lean: <c>reattach</c> leaves <c>detachedOwners</c>; an owner
        /// at or above the lowered watermark is no longer detached).
        /// </summary>
        internal static AnnotatedReadOnlyList<T> Reattach(AnnotatedReadOnlyList<T> stack, long activationSerial)
        {
            long level = 0;
            for (IReadOnlyList<T> node = stack; node is AnnotatedReadOnlyList<T> annotated; node = annotated.Below)
            {
                if (annotated.DetachedBefore <= activationSerial)
                {
                    level = annotated.DetachedBefore;
                    break;
                }
            }
            return new AnnotationMarkerReadOnlyList<T>(stack, level, stack.Annotations);
        }

        /// <summary><paramref name="stack"/> with its input record replaced by <paramref name="record"/>: the same
        /// elements, watermark and detached owners.</summary>
        internal static AnnotatedReadOnlyList<T> MarkInputRecord(IReadOnlyList<T> stack, AliasCellInputs? record)
        {
            if (stack is not AnnotatedReadOnlyList<T> annotated)
                return new AnnotationMarkerReadOnlyList<T>(stack, 0, record);

            return new AnnotationMarkerReadOnlyList<T>(
                annotated is AnnotationMarkerReadOnlyList<T> marker ? marker.Inner : stack,
                annotated.DetachedBefore,
                Pack(record, annotated.Owners));
        }
    }

    // The marker an annotation starts with: the reader's stack, unchanged, under the annotations.
    private sealed class AnnotationMarkerReadOnlyList<T>(IReadOnlyList<T> inner, long detachedBefore, object? annotations)
        : AnnotatedReadOnlyList<T>(detachedBefore, annotations)
    {
        internal IReadOnlyList<T> Inner => inner;

        internal override IReadOnlyList<T> Below => inner;

        public override int Count => inner.Count;

        public override T this[int index] => inner[index];

        public override IEnumerator<T> GetEnumerator() => inner.GetEnumerator();
    }

    // PrependedReadOnlyList over an annotated stack: the same list, carrying its tail's annotations.
    private sealed class AnnotatedPrependedReadOnlyList<T> : AnnotatedReadOnlyList<T>
    {
        private readonly T _head;
        private readonly IReadOnlyList<T> _tail;

        public AnnotatedPrependedReadOnlyList(T head, IReadOnlyList<T> tail, long detachedBefore, object? annotations)
            : base(detachedBefore, annotations)
        {
            _head = head;
            _tail = tail;
            Count = tail.Count + 1;
        }

        public override int Count { get; }

        internal override IReadOnlyList<T> Below => _tail;

        public override T this[int index]
            => index switch
            {
                0 => _head,
                > 0 when index <= _tail.Count => _tail[index - 1],
                _ => throw new ArgumentOutOfRangeException(nameof(index)),
            };

        public override IEnumerator<T> GetEnumerator()
        {
            yield return _head;
            foreach (var item in _tail)
                yield return item;
        }
    }

    /// <summary>
    /// The value environment of a DETACHED evaluation: no binding at all, under the READER's
    /// binding-context identity (<see cref="BindingContextIdentity"/>). The empty need tier beside it
    /// is no binding boundary, so the detached context's identity is this environment's — the one the
    /// reader had. Detachment therefore removes the reader's INPUTS and nothing else: a key computed
    /// below the boundary before any call binds (a local-only property on a chain with no activated
    /// level, the identity a parameterless or collecting-only owner inherits when its declaring chain
    /// has none — CACHE-OWNER-D1) is the key the reader's own context computes. Lean:
    /// <c>EvalCtx.detach</c> keeps <c>bindingContext</c>.
    /// </summary>
    private sealed class DetachedValueEnvironment(object cacheIdentity)
        : ValEnv, IValueEnvironmentCacheIdentityProvider
    {
        public object CacheIdentity => cacheIdentity;

        public int Count => 0;

        public (string Name, Result Value) this[int index] => throw new ArgumentOutOfRangeException(nameof(index));

        public IEnumerator<(string Name, Result Value)> GetEnumerator()
            => Enumerable.Empty<(string Name, Result Value)>().GetEnumerator();

        IEnumerator IEnumerable.GetEnumerator()
            => GetEnumerator();
    }

    /// <summary>
    /// EXPORTED MEANS DETACHED (EXPORTED-DETACHED, November 2026): the context and the value
    /// environment every evaluation that can create or own an <see cref="PropertyExposure.Exported"/>
    /// zero-argument key runs in — the read's miss and re-entrant calculation
    /// (<see cref="GetOrEvaluateZeroArgPropertyResultCore"/>), the qualifying zero-supply invocation
    /// (CACHE-PUB-1), their async twins, and the row of an exported runtime alias's binding cell.
    /// The reader's context under the run's current watermark, over the binding's declaring chain
    /// <paramref name="declaringChain"/> (its wired parent; <see cref="EvalCtx.Detach"/>,
    /// <see cref="EvaluationBudget.ActivationWatermark"/>), and an empty value environment that keeps
    /// the reader's binding identity (<see cref="DetachedValueEnvironment"/>). Every activation that
    /// exists now stays an IDENTITY — cache keys, alias memos, anchoring and CACHE-OWNER-D1
    /// inheritance are unchanged — and one of the chain's — an ENCLOSING CALL of the binding —, on the
    /// checked paths, supplies no INPUT: every executed operation on a captured parameter through one is
    /// refused (<see cref="CapturedParameterActivation"/>, <see cref="UnboundParameter"/>), a local-only
    /// member one of them owns is inaccessible (<see cref="IsAccessibleFrom"/>) and a local-only property
    /// keyed on one is refused (<see cref="DetachedLocalOnlyRead"/>). So on those paths a wrong
    /// <c>Exported</c> flag is a refusal instead of a value shared across calls, and so is the reuse of a
    /// retained runtime-alias binding cell whose computation read an input of a detached activation
    /// (<see cref="RetainedCellAdmission"/>, ledger R-1). An activation that encloses no binding being
    /// evaluated detached — the level of a callable a retained cell or another exported evaluation
    /// returned — keeps supplying that callable's inputs (<see cref="EvalCtx.DetachedOwners"/>). One
    /// helper, never inlined: its locals stay out of the property and call seams' calibrated frames.
    /// Lean: <c>EvalCtx.detach</c> in <c>EvalBody.evalZeroArgPropertyAccessCounted</c>.
    /// </summary>
    [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.NoInlining)]
    internal static EvalCtx DetachedEvaluation(EvalCtx ctx, ValEnv readerValues, ScopeCtx? declaringChain, out ValEnv values)
    {
        if (!ctx.Budget.DetachesExportedEvaluations)
        {
            values = readerValues;
            return ctx;
        }

        values = new DetachedValueEnvironment(BindingContextIdentity(ctx, readerValues));
        return ctx.Detach(ctx.Budget.ActivationWatermark, declaringChain);
    }

    /// <summary>
    /// Whether <paramref name="activation"/> is DETACHED in <paramref name="ctx"/>: recorded before the
    /// exported evaluation the context is inside started (<see cref="EvalCtx.DetachedBefore"/>) AND an
    /// activation of a level enclosing a binding whose detached evaluation the context is inside
    /// (<see cref="EvalCtx.DetachedOwners"/>). False in every context no exported evaluation entered, and
    /// for the level of a callable another computation returned. THE one predicate of the watermark (the
    /// captured-parameter lookup inlines the same test). Lean: <c>EvalCtx.isDetached</c>.
    /// </summary>
    [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.AggressiveInlining)]
    internal static bool IsDetached(ParameterActivation activation, in EvalCtx ctx)
    {
        var watermark = ctx.DetachedBefore;
        return watermark != 0 && activation.Serial < watermark && IsDetachedOwner(activation, ctx);
    }

    // The owner half of IsDetached, out of line: only an activation already below the watermark comes here.
    [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.NoInlining)]
    private static bool IsDetachedOwner(ParameterActivation activation, in EvalCtx ctx)
        => ctx.DetachedOwners is { } owners && owners.Contains(activation.Serial);

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

    /// <summary>
    /// Prepends a binding's own entries to an inherited environment tier, producing the
    /// tier of a NEW binding context: an ordinary user call, a conditional-family call,
    /// a callback invocation, or a generic loop iteration, in both sync and async paths.
    /// Planned loops instead give their reusable value environment an explicit fresh
    /// iteration identity through <see cref="ValueEnvironmentCacheIdentity"/>.
    ///
    /// <para><b>Load-bearing invariant: the result is ALWAYS a fresh list, never
    /// <paramref name="a"/> or <paramref name="b"/> itself — even when the other operand
    /// is empty.</b> The reference identity of an environment tier is the binding-context
    /// identity of the zero-argument property cache (<see cref="ZeroArgPropertyCacheKey"/>:
    /// a LOCAL-ONLY entry is keyed by <see cref="BindingContextIdentity"/> — the minted
    /// need-cell list, empty or not, or <see cref="ValueEnvironmentCacheIdentity"/> below
    /// every boundary) and of the deconstruction binding
    /// cache (<see cref="DeconstructionBindingExecution"/>). Two activations that bind
    /// NOTHING new — <c>Inner()</c> called twice from one caller, a zero-parameter
    /// callback, an iteration of a step with no state — must still be two binding
    /// contexts, so that a local-only property (one reading a captured ancestor
    /// parameter, possibly together with a host value or the random stream) is evaluated
    /// once per activation
    /// and never served another activation's entry. The apparently obvious
    /// short-circuit <c>if (a.Count == 0) return b;</c> would silently collapse those
    /// activations into one context. Contrast <see cref="ShadowValEnv"/>, which MAY
    /// return its input unchanged: a shadowed inherited tier is a VIEW of the caller's
    /// context, not a new one, and the new context's identity is minted here when the
    /// callee's own bindings are prepended. Pinned by
    /// <c>EnvironmentIdentityInvariantTests</c>.</para>
    /// </summary>
    internal static IReadOnlyList<T> Concat<T>(IReadOnlyList<T> a, IReadOnlyList<T> b)
    {
        var result = new List<T>(a.Count + b.Count);
        result.AddRange(a);
        result.AddRange(b);
        return result;
    }

    /// <summary>
    /// The need tier's <see cref="Concat{T}"/>: the same fresh list, typed as a
    /// <see cref="BoundNeedEnv"/> so that the binding context it mints stays recognizable when
    /// it binds no cell and inherits none (<see cref="BindingContextIdentity"/>). No extra
    /// allocation: the boundary already allocated this list. A tier whose own part <paramref name="a"/> holds
    /// at least <see cref="MinimumIndexedParameterCount"/> bindings is a <see cref="WideBoundNeedEnv"/>, the same
    /// list, which the activation entered over it lends its owned-name index.
    /// </summary>
    internal static NeedEnv Concat(NeedEnv a, NeedEnv b)
        => a.Count >= MinimumIndexedParameterCount ? new WideBoundNeedEnv(a, b) : new BoundNeedEnv(a, b);

    /// <summary>
    /// The need tier of a binding context that a binding boundary minted
    /// (<see cref="Concat(NeedEnv, NeedEnv)"/>; Lean <c>needBindingContext</c> /
    /// <c>EvalCtx.bindParameters</c>): an ordinary call, a conditional-family call, a callback
    /// invocation, a loop iteration, a zero-argument demand that binds a pattern, a runtime alias's
    /// bare cell. Its reference is the binding-context identity even when it is EMPTY — a call that
    /// binds nothing is still a new activation (CACHE-OWNER-D2). Every other tier (the root's, a
    /// shadowed view, an activation's captured cells) is no boundary when empty. A NARROW boundary
    /// over a wide tier the evaluator made mints the same list as parts instead
    /// (<see cref="LayeredBoundNeedEnv"/>, <see cref="MintNeedBindingContext"/>), which is a boundary too, and
    /// a tier minted here can be the shared base of such layers: nothing changes it after it is minted.
    /// </summary>
    internal class BoundNeedEnv : List<(string Name, NeedCell Cell)>
    {
        internal BoundNeedEnv(NeedEnv own, NeedEnv inherited)
            : base(own.Count + inherited.Count)
        {
            AddRange(own);
            AddRange(inherited);
        }
    }

    /// <summary>
    /// A minted need tier whose callee binds at least <see cref="MinimumIndexedParameterCount"/> cells of its own
    /// (<see cref="Concat(NeedEnv, NeedEnv)"/>): the same <see cref="BoundNeedEnv"/> — the same bindings in the same
    /// order, the same binding-context identity — whose lookups of the callee's own names (<see cref="LookupNeed"/>:
    /// every read of the head's own parameters, every parameter it forwards) do not scan it (implementation-only,
    /// 2026-11-22). The activation captured from it LENDS it the owned-name index its capture built
    /// (<see cref="Lend"/>, <see cref="OwnedNeedBindings.Filter"/>), which holds the first binding of each name it owns
    /// in this very list. Any other name — a free host-built parameter, read through no lexical owner — is scanned as
    /// before. The list is never changed after it is minted, so the lent index is exact for its whole life; it is
    /// published once (compare-and-set), so concurrent readers need no lock.
    /// </summary>
    internal sealed class WideBoundNeedEnv : BoundNeedEnv
    {
        private OwnedNeedBindings? _owned;
        private int _scanned;

        internal WideBoundNeedEnv(NeedEnv own, NeedEnv inherited)
            : base(own, inherited)
        {
        }

        /// <summary>
        /// Lends this tier the owned-name index of an activation captured FROM it (<see cref="OwnedNeedBindings.Filter"/>):
        /// the first binding of each name the activation owns, found by that scan of this very list. A lookup of such
        /// a name is then answered from it, so a wide frame builds one name index, not one per tier. The first lender
        /// is kept; any lender is exact for the names it owns.
        /// </summary>
        internal void Lend(OwnedNeedBindings owned)
            => Interlocked.CompareExchange(ref _owned, owned, null);

        /// <summary>The cell of the first binding named <paramref name="name"/>, or null: the ordered scan's answer.</summary>
        internal NeedCell? Find(string name)
        {
            if (Volatile.Read(ref _owned) is { } owned && owned.Owned.SlotOf(name) is var slot and >= 0)
                return owned.CellAt(slot);

            var count = Count;
            for (var i = 0; i < count; i++)
            {
                var binding = this[i];
                if (binding.Name == name)
                {
                    _scanned += i + 1;
                    return binding.Cell;
                }
            }

            _scanned += count;
            return null;
        }

        /// <summary>Whether an activation has lent this tier its owned-name index; a test observation.</summary>
        internal bool IsLent => Volatile.Read(ref _owned) is not null;

        /// <summary>The bindings this tier's lookups have compared by scanning it so far (advisory under races); a test observation.</summary>
        internal int ScannedBindings => _scanned;
    }
}
