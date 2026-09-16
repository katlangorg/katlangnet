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

// Lean: abbrev AlgEnv := Assoc Ident Algorithm
//
// C# additionally retains ValueError: the resource-limit failure of an
// argument's eager value channel, observed only if the parameter is later
// demanded as a value. Lean has no execution-budget model, so it has no
// corresponding element.
global using AlgEnv =
    System.Collections.Generic.IReadOnlyList<(string Name, KatLang.Algorithm Value, KatLang.EvalError? ValueError)>;

// Lean: abbrev CountedParamEnv := Assoc Ident (Prod Result Nat)
global using CountedParamEnv =
    System.Collections.Generic.IReadOnlyList<(string Name, KatLang.Evaluator.CountedResult Value)>;
