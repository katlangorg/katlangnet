namespace KatLang;

/// <summary>
/// Structured evaluation error.
/// Corresponds to <c>Error</c> in the Lean specification.
/// <code>
/// inductive Error where
///   | unknownName      : Ident → Error
///   | unknownProperty  : String → Ident → Error
///   | notPublicProperty : String → Ident → Error
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
///   | missingOutput      : Error
///   | unresolvedImplicitParams : List Ident → Error
///   | withContext        : String → Error → Error
/// </code>
/// </summary>
public abstract record EvalError
{
    /// <summary>Source location of the expression that caused this error.</summary>
    public SourceSpan? Span { get; init; }

    private EvalError() { }

    /// <summary>Name could not be resolved in any scope.</summary>
    public sealed record UnknownName(string Name) : EvalError;

    /// <summary>Property not found on the target algorithm.</summary>
    public sealed record UnknownProperty(string ObjectDesc, string PropertyName) : EvalError;

    /// <summary>Property exists but is not public (e.g. private property accessed via open path).</summary>
    public sealed record NotPublicProperty(string ObjectDesc, string PropertyName) : EvalError;

    /// <summary>Expression does not resolve to an algorithm.</summary>
    public sealed record NotAnAlgorithm(string Description) : EvalError;

    /// <summary>Semantic restriction in an open expression (e.g. builtin not allowed).</summary>
    public sealed record IllegalInOpen(string Reason) : EvalError;

    /// <summary>Syntactic form not allowed in open position.</summary>
    public sealed record BadOpenForm(string Reason) : EvalError;

    /// <summary>Expression form not evaluable to a value (e.g. name literal, combine).</summary>
    public sealed record IllegalInEval(string Reason) : EvalError;

    /// <summary>Multiple opens provide the same name publicly.</summary>
    public sealed record AmbiguousOpen(string Name, IReadOnlyList<string> Providers) : EvalError;

    /// <summary>Parameter count does not match argument count (with counts).</summary>
    public sealed record ArityMismatch(int Expected, int Actual) : EvalError;

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

    /// <summary>Forced user-defined algorithm value does not define an output.</summary>
    public sealed record MissingOutput() : EvalError;

    /// <summary>Arithmetic result exceeds the representable decimal range.</summary>
    public sealed record NumericOverflow() : EvalError;

    /// <summary>Top-level program has unresolved implicit parameters (no arguments supplied).</summary>
    public sealed record UnresolvedImplicitParams(IReadOnlyList<string> ParamNames) : EvalError;

    /// <summary>Contextual wrapper attaching a description to an inner error.</summary>
    public sealed record WithContext(string Context, EvalError Inner) : EvalError;
}
