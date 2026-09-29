import KatLang
import CoreTests.Common

namespace KatLangTests
open KatLang (alg algWithParameterPatterns algPrivate runResultM Algorithm Error Result EvalState
  ParameterPattern ParameterPatternInput ParameterPatternBindings)
open KatLang (resolve param num)

--------------------------------------------------------------------------------
-- Repeated names are constraints, not merges (Q-05, September 2026)
--------------------------------------------------------------------------------
-- THE RULE: a repeated parameter name is a compatibility constraint over
-- INDEPENDENTLY supplied arguments. Every occurrence must supply its OWN value
-- (a top-level capture whose name the level repeats needs its slot's value,
-- `bindParameterPattern` / `ParameterPattern.repeatsAtLevel`); the values must be
-- equal; a failed required value propagates as the slot's own recorded outcome;
-- a callable-only argument cannot satisfy the constraint (its value demand is its
-- own arity rejection); several callable channels must share one identity; and
-- channels from different occurrences are never spliced together. Repeated-name
-- matching may RESTRICT a binding; it never manufactures one no individual
-- argument supplied.
--
-- Before Q-05 the verdict ignored valueless contributions unless TWO of them met:
-- `PC(x, x) = [x, x(5)]` with `PC(Inc, 1)` bound x to the value 1 AND the
-- algorithm Inc (a chimera, `[1, 6]`), `P(Bad, 7)` repaired Bad's failure with
-- 7, and `P(Bad, Bad)` masked the division by zero with a type mismatch.
--
-- Evaluation-count evidence without host operations (as in
-- `ArgumentValueOutcome.lean`): `Bad = Id(1) / 0`, `Missing = [Id(1)]:5`,
-- `A = Id(5)` and `B = Id(5) + 0` each open exactly ONE binding context per
-- evaluation of their bodies, and every user call whose parameters BIND opens
-- one more (`EvalCtx.bindParameters`). A call whose binding fails opens none.

/-- `Id(y) = y`: one binding context per call. -/
def rnIdAlg : Algorithm := alg ["y"] [] [] [param "y"]

/-- `Bad = Id(1) / 0`: one context, then `divByZero`. -/
def rnBadAlg : Algorithm := alg [] [] [] [.binary .div (.call (resolve "Id") [num 1]) (num 0)]

/-- `Missing = [Id(1)]:5`: one context, then `badIndex` — a second failure KIND. -/
def rnMissingAlg : Algorithm :=
  alg [] [] [] [.index (.listLiteral [.call (resolve "Id") [num 1]]) (num 5)]

/-- `A = Id(5)` and `B = Id(5) + 0`: equal values, two distinct callables. -/
def rnAAlg : Algorithm := alg [] [] [] [.call (resolve "Id") [num 5]]

def rnBAlg : Algorithm := alg [] [] [] [.binary .add (.call (resolve "Id") [num 5]) (num 0)]

/-- `Inc(z) = z + 1`: callable-only — its value demand is its own arity rejection. -/
def rnIncAlg : Algorithm := alg ["z"] [] [] [.binary .add (param "z") (num 1)]

def rnCap (name : String) : ParameterPattern := .capture { name := name }

def rnColl (name : String) : ParameterPattern := .capture { name := name, kind := .collecting }

/-- `P(x, x) = x`. -/
def rnPAlg : Algorithm := algWithParameterPatterns [rnCap "x", rnCap "x"] [] [] [param "x"]

/-- `PC(x, x) = [x, x(5)]`: reads BOTH channels of `x` — the old chimera's witness. -/
def rnPCAlg : Algorithm :=
  algWithParameterPatterns [rnCap "x", rnCap "x"] [] [] [.listLiteral [param "x", .call (param "x") [num 5]]]

/-- `PF(f, f) = [f, f()]`: the value channel and an explicit invocation. -/
def rnPFAlg : Algorithm :=
  algWithParameterPatterns [rnCap "f", rnCap "f"] [] [] [.listLiteral [param "f", .call (param "f") []]]

/-- `T(x, x, x) = x`. -/
def rnTAlg : Algorithm := algWithParameterPatterns [rnCap "x", rnCap "x", rnCap "x"] [] [] [param "x"]

/-- `N(x, (x, y)) = y`: `x` repeats across a nested group. -/
def rnNAlg : Algorithm :=
  algWithParameterPatterns [rnCap "x", .sequenceValue [rnCap "x", rnCap "y"]] [] [] [param "y"]

/-- `C(x, *r, x) = x`: `x` repeats across the collector. -/
def rnCAlg : Algorithm := algWithParameterPatterns [rnCap "x", rnColl "r", rnCap "x"] [] [] [param "x"]

/-- Retained failures still follow D1's prefix, suffix, collector demand order. -/
def rnSuffixAlg : Algorithm :=
  algWithParameterPatterns [rnColl "r", rnCap "x", rnCap "x"] [] [] [param "x"]

def rnPrefixAlg : Algorithm :=
  algWithParameterPatterns [rnCap "x", rnCap "x", rnColl "r", rnCap "f", rnCap "f"] [] [] [num 0]

/-- `Q2(x, x, y, y) = 0`: two repeated names. -/
def rnQ2Alg : Algorithm :=
  algWithParameterPatterns [rnCap "x", rnCap "x", rnCap "y", rnCap "y"] [] [] [num 0]

/-- `Fwd(a, b) = P(a, b)`: forwards both parameters into the repeated name. -/
def rnFwdAlg : Algorithm := alg ["a", "b"] [] [] [.call (resolve "P") [param "a", param "b"]]

/-- `Same(x) = P(x, x)`: the WRITTEN form that supplies one value to both occurrences. -/
def rnSameAlg : Algorithm := alg ["x"] [] [] [.call (resolve "P") [param "x", param "x"]]

/-- `NW(p, q) = N(p, q)`: an explicit wrapper of the nested repetition. -/
def rnNWAlg : Algorithm := alg ["p", "q"] [] [] [.call (resolve "N") [param "p", param "q"]]

/-- `Some = P`, as the front end elaborates it: forwarding is by binding name, so the ONE
    caller binding `x` is supplied to both occurrences, `Some(x) = P(x, x)` — the very tree of
    the written `Same`. -/
def rnSomeAlg : Algorithm := alg ["x"] [] [] [.call (resolve "P") [param "x", param "x"]]

/-- `SomeN = N`, elaborated: `SomeN(x, (y)) = N(x, (x, y))` — one binding per name, the group
    keeping its shape for the name that is new there. -/
def rnSomeNAlg : Algorithm :=
  algWithParameterPatterns [rnCap "x", .sequenceValue [rnCap "y"]] [] []
    [.call (resolve "N") [param "x", .capture [param "x", param "y"]]]

/-- `SomeC = C`, elaborated: `SomeC(x, *r) = C(x, r*, x)` — the repeated `x` supplied from one
    binding, the collector re-spread because its SOURCE binding collects (FWD-02). -/
def rnSomeCAlg : Algorithm :=
  algWithParameterPatterns [rnCap "x", rnColl "r"] [] []
    [.call (resolve "C") [param "x", .sequenceSpread (param "r"), param "x"]]

/-- `G((x, x)) = x` and the elaborated `SomeG((x)) = G((x, x))`. Deduplicating
    names preserves the caller's sequence-value pattern, including its value opening. -/
def rnGAlg : Algorithm :=
  algWithParameterPatterns [.sequenceValue [rnCap "x", rnCap "x"]] [] [] [param "x"]

def rnSomeGAlg : Algorithm :=
  algWithParameterPatterns [.sequenceValue [rnCap "x"]] [] []
    [.call (resolve "G") [.capture [param "x", param "x"]]]

/-- `E(x, x) = true` / `E(x, y) = false`: a clause family. -/
def rnEAlg : Algorithm :=
  Algorithm.elaborateClauseGroup [
    { pattern := KatLang.Pattern.sequenceValue [KatLang.Pattern.bind "x", KatLang.Pattern.bind "x"]
      body := alg [] [] [] [.boolLiteral true] },
    { pattern := KatLang.Pattern.sequenceValue [KatLang.Pattern.bind "x", KatLang.Pattern.bind "y"]
      body := alg [] [] [] [.boolLiteral false] } ]

def rnRoot (out : List KatLang.Expr) : KatLang.Expr :=
  .algorithmExpr (algPrivate [] []
    [ ("Id", rnIdAlg), ("Bad", rnBadAlg), ("Missing", rnMissingAlg), ("A", rnAAlg), ("B", rnBAlg)
    , ("Inc", rnIncAlg), ("P", rnPAlg), ("PC", rnPCAlg), ("PF", rnPFAlg), ("T", rnTAlg)
    , ("N", rnNAlg), ("C", rnCAlg), ("Q2", rnQ2Alg), ("Fwd", rnFwdAlg), ("E", rnEAlg)
    , ("Same", rnSameAlg), ("NW", rnNWAlg), ("Suffix", rnSuffixAlg), ("Prefix", rnPrefixAlg)
    , ("Some", rnSomeAlg), ("SomeN", rnSomeNAlg), ("SomeC", rnSomeCAlg)
    , ("G", rnGAlg), ("SomeG", rnSomeGAlg) ]
    out)

/-- The outcome of a run AND the binding contexts it opened, kept for a FAILED run too. -/
def rnRun (out : List KatLang.Expr) : Except Error Result × Nat :=
  let (result, state) := (runResultM (rnRoot out)).runState EvalState.empty
  (result, state.nextBindingContext - 1)

def rnContexts (out : List KatLang.Expr) : Nat := (rnRun out).snd

def rnFailsWith (check : Error -> Bool) (out : List KatLang.Expr) : Bool :=
  match (rnRun out).fst with
  | .error err => check err
  | .ok _ => false

def rnSucceedsWith (out : List KatLang.Expr) (expected : Result) : Bool :=
  match (rnRun out).fst with
  | .ok value => value == expected
  | .error _ => false

def rnCall (callee : String) (args : List KatLang.Expr) : KatLang.Expr := .call (resolve callee) args

/-- `Inc`'s own value-demand failure: its arity rejection (1 required, 0 supplied). -/
def rnIncFailure : Error -> Bool := innermostIsArityMismatch 1 0

def rnIdentityFailure : Error -> Bool :=
  innermostIsTypeMismatch "Repeated bind equality requires the same callable identity"

-- The references: each property body opens exactly one context.
#guard rnContexts [resolve "Bad"] == 1
#guard rnFailsWith innermostIsDivByZero [resolve "Bad"]
#guard rnFailsWith innermostIsBadIndex [resolve "Missing"]
#guard rnSucceedsWith [resolve "A"] (.atom 5)
#guard rnSucceedsWith [resolve "B"] (.atom 5)

-- 1. Ordinary equal values match; unequal values do not (the ordinary `badArity`).
#guard rnSucceedsWith [rnCall "P" [num 7, num 7]] (.atom 7)
#guard rnFailsWith innermostIsBadArity [rnCall "P" [num 7, num 8]]

-- 2. A callable-only argument is not a value, and no value beside it borrows its
--    algorithm: both orders are Inc's own failure (formerly the chimera `[1, 6]`).
#guard rnFailsWith rnIncFailure [rnCall "PC" [resolve "Inc", num 1]]
#guard rnFailsWith rnIncFailure [rnCall "PC" [num 1, resolve "Inc"]]
#guard rnFailsWith rnIncFailure [rnCall "PC" [resolve "Inc", resolve "Inc"]]
#guard rnFailsWith rnIncFailure [rnCall "PF" [num 5, resolve "Inc"]]

-- 3. A failed argument's failure propagates; the other occurrence's value never
--    stands in for it (formerly `ok 7`). Bad's body ran exactly ONCE (its one Id
--    context) and P never bound (no context of its own) — matching adds no evaluation.
#guard rnFailsWith innermostIsDivByZero [rnCall "P" [resolve "Bad", num 7]]
#guard rnFailsWith innermostIsDivByZero [rnCall "P" [num 7, resolve "Bad"]]
#guard rnContexts [rnCall "P" [resolve "Bad", num 7]] == 1
#guard rnContexts [rnCall "P" [num 7, resolve "Bad"]] == 1

-- 4. Two failed arguments: the FIRST failure in evaluation order is reported, never an
--    unrelated repeated-name error (formerly the algorithm-only type mismatch). Both
--    arguments were evaluated once each, left to right, before anything bound.
#guard rnFailsWith innermostIsDivByZero [rnCall "P" [resolve "Bad", resolve "Missing"]]
#guard rnFailsWith innermostIsBadIndex [rnCall "P" [resolve "Missing", resolve "Bad"]]
#guard rnFailsWith innermostIsDivByZero [rnCall "P" [resolve "Bad", resolve "Bad"]]
#guard rnContexts [rnCall "P" [resolve "Bad", resolve "Missing"]] == 2

-- 5. Arguments that each carry BOTH channels: equal values and one callable identity
--    bind (and invoke that callable); equal values with two identities reject. One
--    algorithm channel beside an equal plain value accompanies its OWN argument's value,
--    in both orders.
#guard rnSucceedsWith [rnCall "PF" [resolve "A", resolve "A"]] (.listValue [.atom 5, .atom 5])
#guard rnFailsWith rnIdentityFailure [rnCall "PF" [resolve "A", resolve "B"]]
#guard rnFailsWith rnIdentityFailure [rnCall "PF" [resolve "B", resolve "A"]]
#guard rnSucceedsWith [rnCall "PF" [resolve "A", num 5]] (.listValue [.atom 5, .atom 5])
#guard rnSucceedsWith [rnCall "PF" [num 5, resolve "A"]] (.listValue [.atom 5, .atom 5])

-- 6. Across a nested group: the nested occurrence's value never completes a top-level
--    callable-only or failed occurrence (formerly Inc's chimera bound `y = 8`).
#guard rnSucceedsWith [rnCall "N" [num 7, .capture [num 7, num 8]]] (.atom 8)
#guard rnFailsWith innermostIsBadArity [rnCall "N" [num 6, .capture [num 7, num 8]]]
#guard rnFailsWith innermostIsDivByZero [rnCall "N" [resolve "Bad", .capture [num 7, num 8]]]
#guard rnFailsWith rnIncFailure [rnCall "N" [resolve "Inc", .capture [num 7, num 8]]]

-- 7. Across a collector.
#guard rnSucceedsWith [rnCall "C" [num 7, num 9, num 7]] (.atom 7)
#guard rnFailsWith innermostIsBadArity [rnCall "C" [num 7, num 9, num 8]]
#guard rnFailsWith innermostIsDivByZero [rnCall "C" [resolve "Bad", num 9, num 7]]
#guard rnFailsWith rnIncFailure [rnCall "C" [num 7, num 9, resolve "Inc"]]

-- "First failure" means the established binding order, not a new global scan
-- for retained failures. A suffix binds before the collector's middle is demanded;
-- a prefix-local verdict settles before the suffix binds (PAT-10).
#guard rnFailsWith innermostIsBadIndex [rnCall "Suffix" [resolve "Bad", resolve "Missing", num 7]]
#guard rnFailsWith innermostIsDivByZero [rnCall "Suffix" [resolve "Missing", resolve "Bad", num 7]]
#guard rnContexts [rnCall "Suffix" [resolve "Bad", resolve "Missing", num 7]] == 2
#guard rnFailsWith innermostIsBadArity [rnCall "Prefix" [num 1, num 2, resolve "Bad", num 7]]
#guard rnContexts [rnCall "Prefix" [num 1, num 2, resolve "Bad", num 7]] == 1

-- 8. Clause families: every argument's value is required before any clause is tried,
--    so a failed or callable-only argument is its own failure, never a fall-through;
--    equal values select the repeated clause. Family binders carry values only (PAT-07),
--    so two distinct callables with equal values match the repeated clause (PV-43).
#guard rnSucceedsWith [rnCall "E" [num 7, num 7]] (.bool true)
#guard rnSucceedsWith [rnCall "E" [num 7, num 8]] (.bool false)
#guard rnFailsWith innermostIsDivByZero [rnCall "E" [resolve "Bad", num 7]]
#guard rnFailsWith innermostIsDivByZero [rnCall "E" [num 7, resolve "Bad"]]
#guard rnFailsWith rnIncFailure [rnCall "E" [resolve "Inc", num 1]]
#guard rnSucceedsWith [rnCall "E" [resolve "A", resolve "B"]] (.bool true)

-- 9. Lists and sequences: the ONE structural, kind-sensitive value equality.
#guard rnSucceedsWith [rnCall "P" [.listLiteral [num 1], .listLiteral [num 1]]] (.listValue [.atom 1])
#guard rnFailsWith innermostIsBadArity [rnCall "P" [.listLiteral [num 1], num 1]]
#guard rnSucceedsWith [rnCall "P" [.capture [num 1, num 2], .capture [num 1, num 2]]]
  (.sequenceValue [.atom 1, .atom 2])
#guard rnFailsWith innermostIsBadArity [rnCall "P" [.listLiteral [num 1, num 2], .capture [num 1, num 2]]]
#guard rnSucceedsWith [rnCall "E" [.listLiteral [num 1], num 1]] (.bool false)

-- 10. Forwarding carries each parameter's established outcome into the repeated name:
--     it never reconstructs a combined binding. Bad ran once, Fwd bound (one context),
--     and P never bound.
#guard rnFailsWith rnIncFailure [rnCall "Fwd" [resolve "Inc", num 1]]
#guard rnFailsWith rnIncFailure [rnCall "Fwd" [num 1, resolve "Inc"]]
#guard rnFailsWith innermostIsDivByZero [rnCall "Fwd" [resolve "Bad", num 7]]
#guard rnContexts [rnCall "Fwd" [resolve "Bad", num 7]] == 2
#guard rnSucceedsWith [rnCall "Fwd" [num 7, num 7]] (.atom 7)

-- 11. Dot-call is the ordinary call with the receiver as the leading argument.
#guard rnFailsWith rnIncFailure [.dotCall (resolve "Inc") "PC" (some [num 1])]
#guard rnFailsWith rnIncFailure [.dotCall (num 1) "PC" (some [resolve "Inc"])]
#guard rnFailsWith innermostIsDivByZero [.dotCall (num 7) "P" (some [resolve "Bad"])]

-- 12. Three occurrences: every one needs its own value, wherever the callable stands.
#guard rnFailsWith rnIncFailure [rnCall "T" [resolve "A", num 5, resolve "Inc"]]
#guard rnFailsWith rnIncFailure [rnCall "T" [resolve "Inc", resolve "A", num 5]]
#guard rnSucceedsWith [rnCall "T" [num 5, resolve "A", resolve "A"]] (.atom 5)

-- 13. A valueless occurrence is a BINDING failure: it precedes the level's repeated-name
--     verdicts, wherever the unequal name stands (D1's binding-before-verdict order).
#guard rnFailsWith innermostIsDivByZero [rnCall "Q2" [resolve "Bad", num 7, num 1, num 2]]
#guard rnFailsWith innermostIsDivByZero [rnCall "Q2" [num 1, num 2, resolve "Bad", num 7]]
#guard rnFailsWith rnIncFailure [rnCall "Q2" [num 1, num 2, resolve "Inc", resolve "Inc"]]
#guard rnFailsWith innermostIsBadArity [rnCall "Q2" [num 1, num 2, num 3, num 3]]

-- 14. The binder itself: the kept binding of a successful repeated name is the one its
--     valued argument supplied (value and algorithm, NO recorded failure), in both orders;
--     a valueless contribution fails with its own outcome in either position.
def rnBind (inputs : List ParameterPatternInput) : Except Error ParameterPatternBindings :=
  KatLang.runEvalM (KatLang.bindParameterPatternList [rnCap "x", rnCap "x"] inputs true)

def rnKeptBindingIs (inputs : List ParameterPatternInput) (value : Result) : Bool :=
  match rnBind inputs with
  | .ok bindings =>
      KatLang.lookupAssoc "x" bindings.argEnv == some value
        && (match bindings.algEnv.lookupBinding "x" with
            | some binding => binding.valueFailure?.isNone
            | none => false)
  | .error _ => false

#guard rnKeptBindingIs [{ value? := some (.atom 5), algorithm? := some rnAAlg }, { value? := some (.atom 5) }] (.atom 5)
#guard rnKeptBindingIs [{ value? := some (.atom 5) }, { value? := some (.atom 5), algorithm? := some rnAAlg }] (.atom 5)
#guard match rnBind [{ algorithm? := some rnIncAlg, error? := some .divByZero }, { value? := some (.atom 1) }] with
  | .error .divByZero => true
  | _ => false
#guard match rnBind [{ value? := some (.atom 1) }, { algorithm? := some rnIncAlg, error? := some .divByZero }] with
  | .error .divByZero => true
  | _ => false

--------------------------------------------------------------------------------
-- Implicit forwarding is by binding name (decided 2026-09-29; reverses Q-72)
--------------------------------------------------------------------------------
-- Implicit forwarding supplies the caller's ONE binding of a name to EVERY
-- occurrence of that name in the callee's parameter patterns, exactly as it
-- shares one binding across callees (`H = F + G` is `H(x) = F(x) + G(x)`). Lean
-- models no signature construction; it evaluates the ELABORATED forwarding trees
-- (`rnSomeAlg`, `rnSomeNAlg`, `rnSomeCAlg`), and the Lean programs of the
-- `implicit-forwarding-is-by-binding-name` spec cases are derived from the C#
-- elaboration. Each occurrence is an ordinary argument slot reading the one
-- binding, so the occurrences agree by construction on a value, and a
-- callable-only or failed argument is its own failure: nothing is merged. (The
-- Q-72 decision had refused such references with a front-end error; that
-- refusal is removed.)

-- 15. The forwarded alias is the written same-binding call, observation for
--     observation: the value, the failures, and the binding contexts (Some binds —
--     one context — then P binds — one more; a failed argument never lets P bind).
#guard rnSucceedsWith [rnCall "Some" [num 7]] (.atom 7)
#guard rnContexts [rnCall "Some" [num 7]] == 2
#guard rnContexts [rnCall "Some" [num 7]] == rnContexts [rnCall "Same" [num 7]]
#guard rnFailsWith innermostIsDivByZero [rnCall "Some" [resolve "Bad"]]
#guard rnContexts [rnCall "Some" [resolve "Bad"]] == rnContexts [rnCall "Same" [resolve "Bad"]]
#guard rnFailsWith rnIncFailure [rnCall "Some" [resolve "Inc"]]
#guard rnSucceedsWith [rnCall "Some" [.listLiteral [num 1]]] (.listValue [.atom 1])
-- One binding name is one caller parameter: two arguments are an arity error ...
#guard rnFailsWith (innermostIsArityMismatch 1 2) [rnCall "Some" [num 7, num 7]]
-- ... while the direct call still supplies independent arguments (Q-05).
#guard rnFailsWith innermostIsBadArity [rnCall "P" [num 7, num 8]]

-- 16. A nested repetition and a collector forward by name too: one binding for `x`,
--     the group keeping its shape for `y`, the collector re-spread by its kind.
#guard rnSucceedsWith [rnCall "SomeN" [num 7, num 8]] (.atom 8)
#guard rnFailsWith innermostIsDivByZero [rnCall "SomeN" [resolve "Bad", num 8]]
#guard rnFailsWith rnIncFailure [rnCall "SomeN" [resolve "Inc", num 8]]
#guard rnSucceedsWith [rnCall "SomeC" [num 7, num 9]] (.atom 7)
#guard rnFailsWith innermostIsDivByZero [rnCall "SomeC" [resolve "Bad", num 9]]

-- 17. Who supplies the occurrences decides what is checked. A wrapper with its OWN
--     two parameters keeps P's arguments independent (`Fwd(a, b) = P(a, b)`, section
--     10): equal values match, unequal values are P's own `badArity`. Writing one
--     binding into both occurrences (`Same(x) = P(x, x)`) is what forwarding does. A
--     nested repetition's wrapper (`NW(p, q) = N(p, q)`) keeps N's constraint.
#guard rnSucceedsWith [rnCall "Fwd" [num 7, num 7]] (.atom 7)
#guard rnFailsWith innermostIsBadArity [rnCall "Fwd" [num 7, num 8]]
#guard rnSucceedsWith [rnCall "Same" [num 7]] (.atom 7)
#guard rnFailsWith innermostIsDivByZero [rnCall "Same" [resolve "Bad"]]
#guard rnFailsWith rnIncFailure [rnCall "Same" [resolve "Inc"]]
#guard rnSucceedsWith [rnCall "NW" [num 7, .capture [num 7, num 8]]] (.atom 8)
#guard rnFailsWith innermostIsBadArity [rnCall "NW" [num 6, .capture [num 7, num 8]]]

-- 18. The surviving one-name group is a real pattern boundary. These guards
--     evaluate the tree; C# tests separately pin that inference produces it.
#guard rnSucceedsWith [rnCall "SomeG" [num 7]] (.atom 7)
#guard rnSucceedsWith [rnCall "SomeG" [.listLiteral [num 7]]] (.atom 7)
#guard rnSucceedsWith [rnCall "SomeG" [.listLiteral [.capture [num 7, num 8]]]]
  (.sequenceValue [.atom 7, .atom 8])
#guard rnFailsWith (innermostIsArityMismatch 1 2) [rnCall "SomeG" [.capture [num 7, num 8]]]
#guard rnFailsWith (innermostIsArityMismatch 1 0) [rnCall "SomeG" [.listLiteral []]]

end KatLangTests
