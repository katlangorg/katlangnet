// The two evaluator parameter-binding environment tiers, named as in Lean.
//
// Each alias is the C# spelling of a Lean `abbrev`: a transparent name for the
// same association-list representation (an ordered `IReadOnlyList` of bindings,
// first match wins, a callee's own bindings prepended to the caller's), not a
// new type. The evaluator's lookup, shadowing, concatenation, loop-environment
// implementations, and cache-identity checks all keep operating on the plain
// list.
//
// A parameter's VALUE and its CALLABLE identity both live on its supplied cell
// (NeedEnv): since Model C there is no separate algorithm-channel tier and no counted
// callback-parameter tier (both retired on 2026-10-13 with their Lean counterparts,
// after audits showed that no production binding site still wrote either).
//
// Lean: abbrev ValEnv := Assoc Ident Result
global using ValEnv =
    System.Collections.Generic.IReadOnlyList<(string Name, KatLang.Result Value)>;

// A parameter retains one complete demandable supply, including its independent channels.
// Lean: abbrev NeedEnv := Assoc Ident Nat
global using NeedEnv =
    System.Collections.Generic.IReadOnlyList<(string Name, KatLang.Evaluation.NeedCell Cell)>;
