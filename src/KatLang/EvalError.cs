namespace KatLang;

/// <summary>
/// Structured evaluation error.
/// Corresponds to <c>Error</c> in the Lean specification.
/// <code>
/// inductive Error where
///   | unknownName      : Ident → Error
///   | unknownProperty  : String → Ident → Error
///   | notPublicProperty : String → Ident → Error
///   | localOnlyProperty : String → Ident → PropertyExposure → Error
///   | notAnAlgorithm   : String → Error
///   | illegalInOpen     : String → Error
///   | badOpenForm       : String → Error
///   | illegalInEval     : String → Error
///   | ambiguousOpen     : Ident → List String → Error
///   | arityMismatch     : Nat → Nat → Error
///   | badArity          : Error
///   | typeMismatch      : String → Error
///   | badIndex          : Error
///   | divByZero         : Error
///   | noMatchingBranch  : Ident → Error
///   | branchArityMismatch : Ident → Nat → Nat → Error
///   | branchOutputArityMismatch : Ident → Nat → Nat → Error
///   | duplicateProperty : Ident → Error
///   | duplicateBranchPattern : Error
///   | explicitParamsRequireOutput : Error
///   | missingOutput      : Error
///   | unresolvedImplicitParams : List Ident → Error
///   | withContext        : String → Error → Error
/// </code>
/// C# carries structured <see cref="ErrorContext"/> values in <see cref="WithContext"/>
/// while preserving Lean's user-visible context wording where needed.
/// </summary>
public abstract record EvalError
{
    /// <summary>Source location of the expression that caused this error.</summary>
    public SourceSpan? Span { get; init; }

    private EvalError() { }

    /// <summary>
    /// True for every host resource-limit outcome: runtime or weighted structural
    /// depth, steps, stack headroom, collection size and cumulative items, string size
    /// and cumulative string units, and display. A structural reference cycle is
    /// malformed host input, not a resource limit. Host cancellation is not an error
    /// value at all — a cancelled run throws <see cref="OperationCanceledException"/>
    /// and never produces an <see cref="EvalError"/> — so it is outside this
    /// classification. The check resolves through <see cref="WithContext"/> wrappers,
    /// and this is the one authoritative resource-limit classifier
    /// (<see cref="KatLangError.IsResourceLimit"/> delegates here); it never inspects
    /// message text.
    /// These stop accumulating call/property context on the way out: the limit is a
    /// property of the RUN, not of any one call on the chain,
    /// so the innermost span is preserved and a depth failure does not report one identical
    /// context frame per active invocation.
    /// </summary>
    public bool IsResourceLimit => this switch
    {
        EvaluationDepthExceeded
            or AstDepthLimitExceeded
            or EvaluationStepLimitExceeded
            or EvaluationStackExhausted
            or CollectionSizeLimitExceeded
            or MaterializationLimitExceeded
            or StringSizeLimitExceeded
            or StringMaterializationLimitExceeded
            or DisplayLengthLimitExceeded => true,
        WithContext(_, var inner) => inner.IsResourceLimit,
        _ => false,
    };

    /// <summary>
    /// Stable machine-readable classification of this error's semantic family —
    /// the one authoritative mapping from the concrete <see cref="EvalError"/>
    /// variants to the public <see cref="KatLangErrorCode"/> facade. Contextual
    /// <see cref="WithContext"/> wrappers resolve to their innermost error's
    /// family, so common classification never requires unwrapping. The three
    /// arity-shape variants (<see cref="ArityMismatch"/>,
    /// <see cref="VariadicArityMismatch"/>, <see cref="BadArity"/>) deliberately
    /// share <see cref="KatLangErrorCode.ArityMismatch"/> — one host-facing
    /// family, distinguishable through the structured error itself. Every other
    /// variant maps one-to-one. The mapping is fail-loud: an unmapped future
    /// variant throws instead of silently inheriting
    /// <see cref="KatLangErrorCode.Unspecified"/>.
    /// </summary>
    public KatLangErrorCode Code
    {
        get
        {
            var terminal = this;
            while (terminal is WithContext withContext)
                terminal = withContext.Inner;

            return terminal switch
            {
                UnknownName => KatLangErrorCode.UnknownName,
                UnknownProperty => KatLangErrorCode.UnknownProperty,
                NotPublicProperty => KatLangErrorCode.NotPublicProperty,
                LocalOnlyProperty => KatLangErrorCode.LocalOnlyProperty,
                NotAnAlgorithm => KatLangErrorCode.NotAnAlgorithm,
                IllegalInOpen => KatLangErrorCode.IllegalInOpen,
                BadOpenForm => KatLangErrorCode.BadOpenForm,
                IllegalInEval => KatLangErrorCode.IllegalInEval,
                AmbiguousOpen => KatLangErrorCode.AmbiguousOpen,
                ArityMismatch => KatLangErrorCode.ArityMismatch,
                VariadicArityMismatch => KatLangErrorCode.ArityMismatch,
                BadArity => KatLangErrorCode.ArityMismatch,
                TypeMismatch => KatLangErrorCode.TypeMismatch,
                BadIndex => KatLangErrorCode.BadIndex,
                DivByZero => KatLangErrorCode.DivisionByZero,
                NoMatchingBranch => KatLangErrorCode.NoMatchingBranch,
                BranchArityMismatch => KatLangErrorCode.BranchArityMismatch,
                BranchOutputArityMismatch => KatLangErrorCode.BranchOutputArityMismatch,
                DuplicateProperty => KatLangErrorCode.DuplicateProperty,
                DuplicateBranchPattern => KatLangErrorCode.DuplicateBranchPattern,
                ExplicitParametersRequireOutput => KatLangErrorCode.ExplicitParametersRequireOutput,
                MissingOutput => KatLangErrorCode.MissingOutput,
                SpreadMissingOutput => KatLangErrorCode.SpreadMissingOutput,
                UnresolvedImplicitParams => KatLangErrorCode.UnresolvedImplicitParams,
                EvaluationDepthExceeded => KatLangErrorCode.EvaluationDepthExceeded,
                EvaluationStepLimitExceeded => KatLangErrorCode.EvaluationStepLimitExceeded,
                CollectionSizeLimitExceeded => KatLangErrorCode.CollectionSizeLimitExceeded,
                MaterializationLimitExceeded => KatLangErrorCode.MaterializationLimitExceeded,
                StringSizeLimitExceeded => KatLangErrorCode.StringSizeLimitExceeded,
                StringMaterializationLimitExceeded => KatLangErrorCode.StringMaterializationLimitExceeded,
                DisplayLengthLimitExceeded => KatLangErrorCode.DisplayLengthLimitExceeded,
                EvaluationStackExhausted => KatLangErrorCode.EvaluationStackExhausted,
                AstDepthLimitExceeded => KatLangErrorCode.AstDepthLimitExceeded,
                AstCycleDetected => KatLangErrorCode.AstCycleDetected,
                _ => throw new InvalidOperationException(
                    $"Unhandled EvalError variant in {nameof(EvalError)}.{nameof(Code)}: {terminal.GetType().Name}. "
                    + "Map the new variant to a KatLangErrorCode family explicitly."),
            };
        }
    }

    /// <summary>Name could not be resolved in any scope.</summary>
    public sealed record UnknownName(string Name) : EvalError;

    /// <summary>Property not found on the target algorithm.</summary>
    public sealed record UnknownProperty(string ObjectDesc, string PropertyName) : EvalError;

    /// <summary>Property exists but is not public (e.g. private property accessed via open path).</summary>
    public sealed record NotPublicProperty(string ObjectDesc, string PropertyName) : EvalError;

    /// <summary>Property exists but is local-only and cannot be accessed structurally through its owner.</summary>
    public sealed record LocalOnlyProperty(string ObjectDesc, string PropertyName, PropertyExposure Exposure) : EvalError;

    /// <summary>Expression does not resolve to an algorithm.</summary>
    public sealed record NotAnAlgorithm(string Description) : EvalError;

    /// <summary>Semantic restriction in an open expression (e.g. builtin not allowed).</summary>
    public sealed record IllegalInOpen(string Reason) : EvalError;

    /// <summary>Syntactic form not allowed in open position.</summary>
    public sealed record BadOpenForm(string Reason) : EvalError;

    /// <summary>Expression form not evaluable to a value (e.g. name literal, spread in algorithm position).</summary>
    public sealed record IllegalInEval(string Reason) : EvalError;

    /// <summary>Multiple opens provide the same name publicly.</summary>
    public sealed record AmbiguousOpen(string Name, IReadOnlyList<string> Providers) : EvalError;

    /// <summary>Parameter count does not match argument count (with counts).</summary>
    public sealed record ArityMismatch(int Expected, int Actual) : EvalError
    {
        private ArityMismatch(ArityMismatch original)
            : base(original)
        {
            Expected = original.Expected;
            Actual = original.Actual;
            Signature = original.Signature;
            DiagnosticRecordMetadata<IReadOnlyList<ImplicitParameterProvenance>>.Copy(original, this);
        }

        public CallableSignature? Signature { get; init; }

        /// <summary>
        /// Diagnostic-only provenance of the callee's implicit parameters that
        /// were inferred from unresolved identifiers (name, original source
        /// occurrence, optional near-miss suggestion); <c>null</c> when the
        /// callee has none. Like <see cref="Signature"/>, this is C#-side
        /// diagnostic metadata with no Lean counterpart — the structured error
        /// kind and its Lean-modeled payload are unchanged.
        /// </summary>
        internal IReadOnlyList<ImplicitParameterProvenance>? InferredImplicitParameters
        {
            get => DiagnosticRecordMetadata<IReadOnlyList<ImplicitParameterProvenance>>.Get(this);
            init => DiagnosticRecordMetadata<IReadOnlyList<ImplicitParameterProvenance>>.Set(this, value);
        }
    }

    /// <summary>A variadic callable did not receive enough items for its fixed parameters.</summary>
    public sealed record VariadicArityMismatch(string CalleeName, int ExpectedMinimum, int Actual) : EvalError
    {
        public CallableSignature? Signature { get; init; }
    }

    /// <summary>Shape / unpacking failure.</summary>
    public sealed record BadArity() : EvalError;

    /// <summary>Type error (e.g. string where number expected).</summary>
    public sealed record TypeMismatch(string Message) : EvalError;

    /// <summary>Index is out of range or invalid.</summary>
    public sealed record BadIndex() : EvalError;

    /// <summary>Division or modulo by zero.</summary>
    public sealed record DivByZero() : EvalError;

    /// <summary>Conditional algorithm: no branch pattern matched the call arguments.</summary>
    public sealed record NoMatchingBranch(string AlgorithmName) : EvalError;

    /// <summary>Conditional algorithm: branch top-level arity mismatch.</summary>
    public sealed record BranchArityMismatch(string AlgorithmName, int Expected, int Actual) : EvalError;

    /// <summary>Conditional algorithm: branch top-level output arity mismatch.</summary>
    public sealed record BranchOutputArityMismatch(string AlgorithmName, int Expected, int Actual) : EvalError;

    /// <summary>Algorithm defines the same property name more than once.</summary>
    public sealed record DuplicateProperty(string Name) : EvalError;

    /// <summary>Conditional algorithm has match-equivalent branch patterns.</summary>
    public sealed record DuplicateBranchPattern() : EvalError;

    /// <summary>Explicit algorithm parameters require an algorithm output.</summary>
    public sealed record ExplicitParametersRequireOutput() : EvalError;

    /// <summary>Forced user-defined algorithm value does not define an output.</summary>
    public sealed record MissingOutput() : EvalError;

    /// <summary>Spread operand did not produce output.</summary>
    public sealed record SpreadMissingOutput() : EvalError;

    /// <summary>Top-level program has unresolved implicit parameters (no arguments supplied).</summary>
    public sealed record UnresolvedImplicitParams(IReadOnlyList<string> ParamNames) : EvalError
    {
        private UnresolvedImplicitParams(UnresolvedImplicitParams original)
            : base(original)
        {
            ParamNames = original.ParamNames;
            DiagnosticRecordMetadata<IReadOnlyList<ImplicitParameterProvenance>>.Copy(original, this);
        }

        /// <summary>
        /// Diagnostic-only provenance for the subset of <see cref="ParamNames"/>
        /// that carry inferred-origin metadata (source occurrence and optional
        /// near-miss suggestion); <c>null</c> when none do (e.g. host-built
        /// parameter lists). No Lean counterpart — the structured error kind
        /// and its Lean-modeled payload are unchanged.
        /// </summary>
        internal IReadOnlyList<ImplicitParameterProvenance>? InferredImplicitParameters
        {
            get => DiagnosticRecordMetadata<IReadOnlyList<ImplicitParameterProvenance>>.Get(this);
            init => DiagnosticRecordMetadata<IReadOnlyList<ImplicitParameterProvenance>>.Set(this, value);
        }
    }

    /// <summary>
    /// Evaluation reached the deterministic limit on simultaneously active dynamic
    /// algorithm invocations (<see cref="EvaluationLimits.MaxDepth"/>, bounded by
    /// <see cref="EvaluationLimits.MaxSupportedDepth"/>). Host-runtime resource policy,
    /// not a property of the KatLang program: an in-budget program is unaffected.
    /// </summary>
    public sealed record EvaluationDepthExceeded(int Limit) : EvalError;

    /// <summary>
    /// Evaluation reached the deterministic step budget
    /// (<see cref="EvaluationLimits.MaxSteps"/>). One step is charged per dynamic
    /// algorithm invocation and per loop iteration.
    /// </summary>
    public sealed record EvaluationStepLimitExceeded(long Limit) : EvalError;

    /// <summary>
    /// A single collection would have exceeded the item-slot limit for one materialized
    /// sequence or exact list (<see cref="EvaluationLimits.MaxCollectionItems"/>, bounded
    /// by <see cref="EvaluationLimits.MaxSupportedCollectionItems"/>). Reported BEFORE the
    /// collection is allocated. Payload is machine-independent: item counts, never bytes.
    /// </summary>
    public sealed record CollectionSizeLimitExceeded(int Limit, long Requested) : EvalError;

    /// <summary>
    /// The run's cumulative materialized item-slot budget
    /// (<see cref="EvaluationLimits.MaxMaterializedItems"/>) was exhausted. Counts slots
    /// CREATED across the run; it is not a live-memory measure.
    /// </summary>
    public sealed record MaterializationLimitExceeded(long Limit) : EvalError;

    /// <summary>
    /// One language string value would have exceeded the per-string length limit
    /// (<see cref="EvaluationLimits.MaxStringLength"/>, bounded by
    /// <see cref="EvaluationLimits.MaxSupportedStringLength"/>). Reported BEFORE the string
    /// is created. Lengths are UTF-16 code units, never bytes: CLR string representation
    /// and per-object overhead vary.
    /// </summary>
    public sealed record StringSizeLimitExceeded(int Limit, long Requested) : EvalError;

    /// <summary>
    /// The run's cumulative language-string budget
    /// (<see cref="EvaluationLimits.MaxMaterializedStringChars"/>) was exhausted. Counts
    /// UTF-16 code units CREATED across the run; it is not a live-memory measure.
    /// </summary>
    public sealed record StringMaterializationLimitExceeded(long Limit) : EvalError;

    /// <summary>
    /// Rendering a value or error to display text would have exceeded the rendered-output
    /// limit (<see cref="EvaluationLimits.MaxDisplayLength"/>, bounded by
    /// <see cref="EvaluationLimits.MaxSupportedDisplayLength"/>). This is a property of the
    /// RENDERING, not of the value: the structured result is unaffected and remains
    /// available through <see cref="KatLangEngine.Run(string, RunOptions)"/>.
    /// </summary>
    public sealed record DisplayLengthLimitExceeded(int Limit) : EvalError;

    /// <summary>
    /// Evaluation stopped because host stack headroom ran out before the deterministic
    /// depth limit was reached. This is the machine-dependent backstop that keeps
    /// stack-expensive evaluation shapes from terminating the process; it carries no
    /// machine-specific payload precisely because the boundary is not a semantic fact.
    /// </summary>
    public sealed record EvaluationStackExhausted() : EvalError;

    /// <summary>
    /// The pre-evaluation structural safety preflight rejected the program tree because
    /// its WEIGHTED STRUCTURAL DEPTH exceeds <paramref name="Limit"/>
    /// (<see cref="EvaluationLimits.MaxAstDepth"/>, bounded by
    /// <see cref="EvaluationLimits.MaxSupportedAstDepth"/>). The metric is a
    /// consumer-faithful structural depth budget over the longest
    /// parent-to-descendant path, NOT a literal node count: most nodes cost one unit,
    /// but on the evaluator gates a dot-call link costs THREE units (its resolution
    /// machinery consumes several stack frames per link) and the internal
    /// sequence-join kinds cost ZERO (every consumer walks their spines iteratively),
    /// so a ~100-link dot-call chain reaches a limit of 300 units. Reported BEFORE any
    /// recursive validation, optimization, or evaluation touches the tree, because a
    /// tree this deep can otherwise terminate the process with an unhandleable
    /// <see cref="StackOverflowException"/>. Successfully elaborated public parse
    /// results stay within the hard ceiling; this error remains reachable through
    /// host-constructed ASTs, raw syntax trees between the parser's larger raw gate
    /// and this evaluation gate, and configured lower limits. Distinct from
    /// <see cref="EvaluationDepthExceeded"/>, which bounds
    /// RUNTIME algorithm recursion of an accepted program.
    /// </summary>
    public sealed record AstDepthLimitExceeded(int Limit) : EvalError;

    /// <summary>
    /// The pre-evaluation structural safety preflight found a reference cycle in the
    /// program tree: some node reaches itself again through its own children. A cyclic
    /// graph is not a valid KatLang program (recursive walkers would never terminate),
    /// and is only constructible by mutating the caller-owned collections behind a
    /// host-built AST after construction — the parser cannot produce one. Shared
    /// ACYCLIC subtrees are legal and are not reported as cycles.
    /// </summary>
    public sealed record AstCycleDetected() : EvalError;

    /// <summary>Contextual wrapper attaching structured context to an inner error.</summary>
    public sealed record WithContext : EvalError
    {
        public ErrorContext ErrorContext { get; }

        public EvalError Inner { get; }

        public string Context => ErrorContext.ToLegacyString();

        public WithContext(ErrorContext errorContext, EvalError inner)
        {
            ErrorContext = errorContext;
            Inner = inner;
        }

        public WithContext(string context, EvalError inner)
            : this(new TextErrorContext(context), inner)
        {
        }

        public void Deconstruct(out ErrorContext errorContext, out EvalError inner)
        {
            errorContext = ErrorContext;
            inner = Inner;
        }
    }
}
