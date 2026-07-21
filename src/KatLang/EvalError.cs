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
///   | specialOutputAccess : Error
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
    /// True for the host resource-limit outcomes (depth, steps, stack headroom, collection
    /// size, cumulative materialization). These stop accumulating call/property context on
    /// the way out: the limit is a property of the RUN, not of any one call on the chain,
    /// so the innermost span is preserved and a depth failure does not report one identical
    /// context frame per active invocation.
    /// </summary>
    internal bool IsResourceLimit => this switch
    {
        EvaluationDepthExceeded
            or EvaluationStepLimitExceeded
            or EvaluationStackExhausted
            or CollectionSizeLimitExceeded
            or MaterializationLimitExceeded => true,
        WithContext(_, var inner) => inner.IsResourceLimit,
        _ => false,
    };

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
        public CallableSignature? Signature { get; init; }
    }

    /// <summary>Variadic binding did not receive enough items for its fixed parameters.</summary>
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

    /// <summary>External property-style access to the reserved special Output member is invalid.</summary>
    public sealed record SpecialOutputAccess() : EvalError;

    /// <summary>Explicit algorithm parameters require an algorithm output.</summary>
    public sealed record ExplicitParametersRequireOutput() : EvalError;

    /// <summary>Forced user-defined algorithm value does not define an output.</summary>
    public sealed record MissingOutput() : EvalError;

    /// <summary>Spread operand did not produce output.</summary>
    public sealed record SpreadMissingOutput() : EvalError;

    /// <summary>Arithmetic result exceeds the representable decimal range.</summary>
    public sealed record NumericOverflow() : EvalError;

    /// <summary>Top-level program has unresolved implicit parameters (no arguments supplied).</summary>
    public sealed record UnresolvedImplicitParams(IReadOnlyList<string> ParamNames) : EvalError;

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
