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
// ValueError is Lean's AlgBinding.valueFailure?: an ORDINARY failure recorded on the
// algorithm tier as a parameter's VALUE outcome, null when the parameter has a value
// or nothing was recorded. Under Model C (NEED-01/02) no binding path writes it: a
// parameter's VALUE outcome is its NeedCell's completed outcome (NeedEnv), established
// by the cell's first demand and reused by every later demand (AT-MOST-ONCE ARGUMENT
// VALUE EVALUATION). The pre-Model-C eager writer, Evaluator.SlotAlgorithmBinding, was
// deleted; the field and its readers (ParameterValueFailure, ParameterSlotFailure) remain
// for the legacy Ready tier, as Lean keeps valueFailure? (whose eager writer survives only
// in lean/HistoricalReadyBinding.lean). A resource limit is never recorded here: a
// demanded computation that reaches one ends the run (RESOURCE LIMITS ARE TERMINAL).
global using AlgEnv =
    System.Collections.Generic.IReadOnlyList<(string Name, KatLang.Algorithm Value, KatLang.EvalError? ValueError)>;

// Lean: abbrev CountedParamEnv := Assoc Ident (Prod Result Nat)
global using CountedParamEnv =
    System.Collections.Generic.IReadOnlyList<(string Name, KatLang.Evaluator.CountedResult Value)>;

// A parameter retains one complete demandable supply, including its independent channels.
global using NeedEnv =
    System.Collections.Generic.IReadOnlyList<(string Name, KatLang.Evaluation.NeedCell Cell)>;
