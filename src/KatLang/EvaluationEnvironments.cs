// The three evaluator parameter-binding environment tiers, named as in Lean.
//
// Each alias is the C# spelling of a Lean `abbrev`: a transparent name for the
// same association-list representation (an ordered `IReadOnlyList` of bindings,
// first match wins, a callee's own bindings prepended to the caller's), not a
// new type. The evaluator's lookup, shadowing, concatenation, loop-environment
// implementations, and cache-identity checks all keep operating on the plain
// list.
//
// Lean: abbrev ValEnv := Assoc Ident Result
global using ValEnv =
    System.Collections.Generic.IReadOnlyList<(string Name, KatLang.Result Value)>;

// Lean: abbrev AlgEnv := Assoc Ident AlgBinding
//
// ValueError is Lean's AlgBinding.valueFailure?: the failure (ordinary or
// resource-limit) that the parameter's written argument slot established as
// its VALUE outcome when its one value evaluation failed, null when the
// parameter has a value. A value read reports it and never evaluates the
// algorithm again (AT-MOST-ONCE ARGUMENT VALUE EVALUATION,
// Evaluator.SlotAlgorithmBinding).
global using AlgEnv =
    System.Collections.Generic.IReadOnlyList<(string Name, KatLang.Algorithm Value, KatLang.EvalError? ValueError)>;

// Lean: abbrev CountedParamEnv := Assoc Ident (Prod Result Nat)
global using CountedParamEnv =
    System.Collections.Generic.IReadOnlyList<(string Name, KatLang.Evaluator.CountedResult Value)>;
