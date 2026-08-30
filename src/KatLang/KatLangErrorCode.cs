namespace KatLang;

/// <summary>
/// Stable machine-readable classification of a <see cref="KatLangError"/> — the
/// unified public error facade covering both front-end (parse/elaboration)
/// failures and evaluation failures. This is the supported host classification
/// API: <see cref="KatLangError.Message"/> stays human-readable presentation and
/// is never the classification channel.
///
/// <para><b>Two origins, one vocabulary.</b> An error projected from a front-end
/// <see cref="Diagnostic"/> carries the same-named code as the diagnostic's
/// <see cref="DiagnosticCode"/> (and <see cref="KatLangError.Source"/> is
/// <c>null</c>); an error projected from an <see cref="EvalError"/> carries the
/// code of its underlying error family, resolved through any
/// <see cref="EvalError.WithContext"/> wrappers (and <see cref="KatLangError.Source"/>
/// preserves the original structured error). Families that exist in both phases
/// (for example <see cref="BadOpenForm"/>, <see cref="ArityMismatch"/>, and
/// <see cref="DuplicateProperty"/>)
/// share one member.</para>
///
/// <para><b>Granularity.</b> One code covers one host-facing semantic family.
/// A few internal error variants that are one family deliberately share a code
/// — <see cref="EvalError.ArityMismatch"/>, <see cref="EvalError.VariadicArityMismatch"/>,
/// and <see cref="EvalError.BadArity"/> all classify as <see cref="ArityMismatch"/> —
/// while remaining distinguishable through <see cref="KatLangError.Source"/>.</para>
///
/// <para><b>Resource limits.</b> Each evaluation resource-limit family keeps its
/// own code so hosts can report which limit was hit; the family-level check is
/// <see cref="KatLangError.IsResourceLimit"/> / <see cref="EvalError.IsResourceLimit"/>,
/// not a code comparison. Cancellation has no code: a cancelled run throws
/// <see cref="OperationCanceledException"/> and is never represented as an error
/// value.</para>
///
/// <para><b>Stability.</b> Names and numeric values are stable public contract:
/// existing members are never renumbered, renamed, or removed; new families are
/// appended with new values. Hosts may persist the numeric values.</para>
/// </summary>
public enum KatLangErrorCode
{
    /// <summary>
    /// No structured identity. Reached only by compatibility paths — a
    /// <see cref="KatLangError"/> projected from an externally constructed
    /// <see cref="Diagnostic"/> whose code was left unset. Errors produced by
    /// KatLang itself never use it.
    /// </summary>
    Unspecified = 0,

    // ── Evaluation: names, properties, and structure ────────────────────────

    /// <summary>A name could not be resolved in any scope (<see cref="EvalError.UnknownName"/>).</summary>
    UnknownName = 1,

    /// <summary>A property was not found on the target algorithm (<see cref="EvalError.UnknownProperty"/>).</summary>
    UnknownProperty = 2,

    /// <summary>A property exists but is not public (<see cref="EvalError.NotPublicProperty"/>).</summary>
    NotPublicProperty = 3,

    /// <summary>A property exists but is local-only and cannot be accessed structurally (<see cref="EvalError.LocalOnlyProperty"/>).</summary>
    LocalOnlyProperty = 4,

    /// <summary>An expression does not resolve to an algorithm (<see cref="EvalError.NotAnAlgorithm"/>).</summary>
    NotAnAlgorithm = 5,

    /// <summary>A semantic restriction in an open expression was violated (<see cref="EvalError.IllegalInOpen"/>).</summary>
    IllegalInOpen = 6,

    /// <summary>
    /// A syntactic form is not allowed in open position
    /// (<see cref="EvalError.BadOpenForm"/> / <see cref="DiagnosticCode.BadOpenForm"/>).
    /// </summary>
    BadOpenForm = 7,

    /// <summary>An expression form is not evaluable to a value (<see cref="EvalError.IllegalInEval"/>).</summary>
    IllegalInEval = 8,

    /// <summary>Multiple opens provide the same name publicly (<see cref="EvalError.AmbiguousOpen"/>).</summary>
    AmbiguousOpen = 9,

    // ── Arity, types, and operations ────────────────────────────────────────

    /// <summary>
    /// The supplied items do not fit the callable or binding shape: parameter
    /// count vs argument count, a variadic callable's fixed-parameter minimum,
    /// or a shape/unpacking failure (<see cref="EvalError.ArityMismatch"/>,
    /// <see cref="EvalError.VariadicArityMismatch"/>, <see cref="EvalError.BadArity"/>,
    /// and the parse-time <see cref="DiagnosticCode.ArityMismatch"/> gate).
    /// </summary>
    ArityMismatch = 10,

    /// <summary>A type error, for example a string where a number is expected (<see cref="EvalError.TypeMismatch"/>).</summary>
    TypeMismatch = 11,

    /// <summary>An index is out of range or invalid (<see cref="EvalError.BadIndex"/>).</summary>
    BadIndex = 12,

    /// <summary>Division or modulo by a zero-valued divisor (<see cref="EvalError.DivByZero"/>).</summary>
    DivisionByZero = 13,

    /// <summary>No branch pattern of a conditional algorithm matched the call arguments (<see cref="EvalError.NoMatchingBranch"/>).</summary>
    NoMatchingBranch = 14,

    /// <summary>Conditional algorithm branches disagree on top-level pattern arity (<see cref="EvalError.BranchArityMismatch"/>).</summary>
    BranchArityMismatch = 15,

    /// <summary>Conditional algorithm branches disagree on top-level output arity (<see cref="EvalError.BranchOutputArityMismatch"/>).</summary>
    BranchOutputArityMismatch = 16,

    /// <summary>The same property name is defined more than once (<see cref="EvalError.DuplicateProperty"/>).</summary>
    DuplicateProperty = 17,

    /// <summary>A conditional algorithm has match-equivalent branch patterns (<see cref="EvalError.DuplicateBranchPattern"/>).</summary>
    DuplicateBranchPattern = 18,

    /// <summary>An algorithm declares explicit parameters but defines no output (<see cref="EvalError.ExplicitParametersRequireOutput"/>).</summary>
    ExplicitParametersRequireOutput = 19,

    /// <summary>A forced user-defined algorithm value does not define an output (<see cref="EvalError.MissingOutput"/>).</summary>
    MissingOutput = 20,

    /// <summary>A spread operand did not produce output (<see cref="EvalError.SpreadMissingOutput"/>).</summary>
    SpreadMissingOutput = 21,

    /// <summary>The top-level program has unresolved implicit parameters (<see cref="EvalError.UnresolvedImplicitParams"/>).</summary>
    UnresolvedImplicitParams = 22,

    // ── Evaluation resource limits (see KatLangError.IsResourceLimit) ───────

    /// <summary>The runtime invocation-depth limit was exceeded (<see cref="EvalError.EvaluationDepthExceeded"/>).</summary>
    EvaluationDepthExceeded = 23,

    /// <summary>The evaluation step budget was exhausted (<see cref="EvalError.EvaluationStepLimitExceeded"/>).</summary>
    EvaluationStepLimitExceeded = 24,

    /// <summary>One collection would exceed the per-collection item limit (<see cref="EvalError.CollectionSizeLimitExceeded"/>).</summary>
    CollectionSizeLimitExceeded = 25,

    /// <summary>The run's cumulative materialized item budget was exhausted (<see cref="EvalError.MaterializationLimitExceeded"/>).</summary>
    MaterializationLimitExceeded = 26,

    /// <summary>One string value would exceed the per-string length limit (<see cref="EvalError.StringSizeLimitExceeded"/>).</summary>
    StringSizeLimitExceeded = 27,

    /// <summary>The run's cumulative string materialization budget was exhausted (<see cref="EvalError.StringMaterializationLimitExceeded"/>).</summary>
    StringMaterializationLimitExceeded = 28,

    /// <summary>Rendering to display text would exceed the rendered-output limit (<see cref="EvalError.DisplayLengthLimitExceeded"/>).</summary>
    DisplayLengthLimitExceeded = 29,

    /// <summary>Evaluation stopped to protect the host stack (<see cref="EvalError.EvaluationStackExhausted"/>).</summary>
    EvaluationStackExhausted = 30,

    // ── Program structure (both phases) ─────────────────────────────────────

    /// <summary>
    /// The program tree's weighted structural depth exceeds the safe processing
    /// limit (<see cref="EvalError.AstDepthLimitExceeded"/> /
    /// <see cref="DiagnosticCode.AstDepthLimitExceeded"/>). An evaluation-phase
    /// occurrence classifies as a resource limit; the front-end phase does not.
    /// </summary>
    AstDepthLimitExceeded = 31,

    /// <summary>
    /// The program tree contains a reference cycle and is not a valid KatLang
    /// program structure (<see cref="EvalError.AstCycleDetected"/> /
    /// <see cref="DiagnosticCode.AstCycleDetected"/>). Malformed host input,
    /// never a resource limit.
    /// </summary>
    AstCycleDetected = 32,

    // ── Front end: lexical (see DiagnosticCode) ─────────────────────────────

    /// <summary>Front-end <see cref="DiagnosticCode.UnexpectedCharacter"/>.</summary>
    UnexpectedCharacter = 33,

    /// <summary>Front-end <see cref="DiagnosticCode.UnterminatedStringLiteral"/>.</summary>
    UnterminatedStringLiteral = 34,

    /// <summary>Front-end <see cref="DiagnosticCode.NumberLiteralTooLarge"/>.</summary>
    NumberLiteralTooLarge = 35,

    // ── Front end: syntax and declarations (see DiagnosticCode) ─────────────

    /// <summary>Front-end <see cref="DiagnosticCode.UnexpectedToken"/>.</summary>
    UnexpectedToken = 36,

    /// <summary>Front-end <see cref="DiagnosticCode.UnsupportedSemicolon"/>.</summary>
    UnsupportedSemicolon = 37,

    /// <summary>Front-end <see cref="DiagnosticCode.NestingTooDeep"/>.</summary>
    NestingTooDeep = 38,

    /// <summary>Front-end <see cref="DiagnosticCode.ExpressionChainTooDeep"/>.</summary>
    ExpressionChainTooDeep = 39,

    /// <summary>Front-end <see cref="DiagnosticCode.DeclarationInParentheses"/>.</summary>
    DeclarationInParentheses = 40,

    /// <summary>Front-end <see cref="DiagnosticCode.InvalidOpenDeclaration"/>.</summary>
    InvalidOpenDeclaration = 41,

    /// <summary>Front-end <see cref="DiagnosticCode.InvalidOpenTargetList"/>.</summary>
    InvalidOpenTargetList = 42,

    /// <summary>Front-end <see cref="DiagnosticCode.ClauseVisibilityMismatch"/>.</summary>
    ClauseVisibilityMismatch = 43,

    /// <summary>Front-end <see cref="DiagnosticCode.InvalidGraceMarker"/>.</summary>
    InvalidGraceMarker = 44,

    /// <summary>Front-end <see cref="DiagnosticCode.InvalidCollectMarker"/>.</summary>
    InvalidCollectMarker = 45,

    /// <summary>Front-end <see cref="DiagnosticCode.InvalidCollectingBinding"/>.</summary>
    InvalidCollectingBinding = 46,

    /// <summary>Front-end <see cref="DiagnosticCode.MisplacedSpread"/>.</summary>
    MisplacedSpread = 47,

    /// <summary>Front-end <see cref="DiagnosticCode.UndeclaredIdentifier"/>.</summary>
    UndeclaredIdentifier = 48,

    // ── Front end: source-processing limits (see DiagnosticCode) ────────────

    /// <summary>Front-end <see cref="DiagnosticCode.SourceLengthExceeded"/>.</summary>
    SourceLengthExceeded = 49,

    /// <summary>Front-end <see cref="DiagnosticCode.AggregateSourceLengthExceeded"/>.</summary>
    AggregateSourceLengthExceeded = 50,

    /// <summary>Front-end <see cref="DiagnosticCode.ModuleImportDepthExceeded"/>.</summary>
    ModuleImportDepthExceeded = 51,

    /// <summary>Front-end <see cref="DiagnosticCode.ModuleCountExceeded"/>.</summary>
    ModuleCountExceeded = 52,

    /// <summary>Front-end <see cref="DiagnosticCode.ModuleNestingTooDeep"/>.</summary>
    ModuleNestingTooDeep = 53,

    /// <summary>Front-end <see cref="DiagnosticCode.ModuleElaborationStackExhausted"/>.</summary>
    ModuleElaborationStackExhausted = 54,

    // ── Front end: module loading (see DiagnosticCode) ──────────────────────

    /// <summary>Front-end <see cref="DiagnosticCode.InvalidLoadDirective"/>.</summary>
    InvalidLoadDirective = 55,

    /// <summary>Front-end <see cref="DiagnosticCode.InvalidLoadUrl"/>.</summary>
    InvalidLoadUrl = 56,

    /// <summary>Front-end <see cref="DiagnosticCode.LoadCycle"/>.</summary>
    LoadCycle = 57,

    /// <summary>Front-end <see cref="DiagnosticCode.LoadFetchFailed"/>.</summary>
    LoadFetchFailed = 58,

    /// <summary>Front-end <see cref="DiagnosticCode.InvalidLoadedSource"/>.</summary>
    InvalidLoadedSource = 59,

    /// <summary>Front-end <see cref="DiagnosticCode.LoadElaborationUnavailable"/>.</summary>
    LoadElaborationUnavailable = 60,

    /// <summary>Front-end <see cref="DiagnosticCode.InternalError"/>.</summary>
    InternalError = 61,
}
