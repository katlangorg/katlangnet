import KatLang
import CoreTests.Common

namespace KatLangTests
open KatLang (alg algWithParameterPatterns algPrivate runResultM Algorithm Error Result EvalState
  ParameterPattern)
open KatLang (resolve param num)

--------------------------------------------------------------------------------
-- Repeated names are constraints, not merges (Q-05, September 2026)
--------------------------------------------------------------------------------
-- THE RULE: a repeated parameter name is a compatibility constraint over
-- INDEPENDENTLY supplied arguments (NEED-04, group-aware since ALIAS-UNIFY-1,
-- October 2026). At every occurrence the binder projects that cell's CALLABLE
-- first (`bindNeedName`): every two callable identities must be the same identity
-- (a conflict is rejected before any VALUE demand); a value-only argument demands
-- its own value, the first one being the group's DATA ANCHOR, against which every
-- other occurrence's OWN value — references included — is then checked. A group
-- of references alone matches by identity and demands no VALUE. A failed required
-- value propagates as the slot's own completed outcome; channels from different
-- occurrences are never spliced together. Repeated-name matching may RESTRICT a
-- binding; it never manufactures one no individual argument supplied.
--
-- Before Q-05 the verdict ignored valueless contributions unless TWO of them met:
-- `PC(x, x) = [x, x(5)]` with `PC(Inc, 1)` bound x to the value 1 AND the
-- algorithm Inc (a chimera, `[1, 6]`), `P(Bad, 7)` repaired Bad's failure with
-- 7, and `P(Bad, Bad)` masked the division by zero with a type mismatch.
--
-- Evaluation-count evidence without host operations (as in
-- `ArgumentValueOutcome.lean`): `Bad = Id(1) / 0`, `Missing = [Id(1)][5]`,
-- `A = Id(5)` and `B = Id(5) + 0` each open exactly ONE binding context per
-- evaluation of their bodies, and every user call whose parameters BIND opens
-- one more (`EvalCtx.bindParameters`). A call whose binding fails opens none.

/-- `Id(y) = y`: one binding context per call. -/
def rnIdAlg : Algorithm := alg ["y"] [] [] [param "y"]

/-- `Bad = Id(1) / 0`: one context, then `divByZero`. -/
def rnBadAlg : Algorithm := alg [] [] [] [.binary .div (.call (resolve "Id") [num 1]) (num 0)]

/-- `Missing = [Id(1)][5]`: one context, then `badIndex` — a second failure KIND. -/
def rnMissingAlg : Algorithm :=
  alg [] [] [] [.index (.listLiteral [.call (resolve "Id") [num 1]]) [num 5]]

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

/-- Failures follow the NEED-04 inspection order (PAT-10): the collector demands nothing, and
    the repeated suffix name demands its cells as they are visited. -/
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

/-- `NW(p, q) = N(p, q)`: an explicit call of the nested repetition. -/
def rnNWAlg : Algorithm := alg ["p", "q"] [] [] [.call (resolve "N") [param "p", param "q"]]

/-- The CALLABLE ALIAS of a callee, as the front end elaborates `Alias = Callee` (FWD-02,
    binding indirection, `Algorithm.alias`): a binding of its own whose callable IS the callee —
    no wrapper and no copied signature. `Some = P` therefore takes `P(x, x)`'s two independent
    arguments, because a call through it is `P`'s own call. -/
def rnAlias (callee : String) : Algorithm := .alias none [] [] (resolve callee)

/-- `Some = P`, `SomeN = N`, `SomeC = C`: callable aliases of the repeated-name callees. -/
def rnSomeAlg : Algorithm := rnAlias "P"

def rnSomeNAlg : Algorithm := rnAlias "N"

def rnSomeCAlg : Algorithm := rnAlias "C"

/-- `Lifted = [P][0]`, as the front end elaborates it: a FORMULA forwards by binding name, so
    the ONE caller binding `x` is supplied to both occurrences, `Lifted(x) = [P(x, x)][0]` —
    the call of the written `Same`. -/
def rnLifted (call : KatLang.Expr) : List KatLang.Expr := [.index (.listLiteral [call]) [num 0]]

def rnLiftedAlg : Algorithm := alg ["x"] [] [] (rnLifted (.call (resolve "P") [param "x", param "x"]))

/-- `LiftedN = [N][0]`, elaborated: `LiftedN(x, y) = [N(x, (x, y))][0]` — one binding per name;
    the group keeps its kind for the names that are new there, and a SEQUENCE group left with
    one non-collecting item is that item (there is no one-item sequence), so `y` is a plain
    parameter. The callee's sequence group is rebuilt as a sequence (FWD-02). -/
def rnLiftedNAlg : Algorithm :=
  algWithParameterPatterns [rnCap "x", rnCap "y"] [] []
    (rnLifted (.call (resolve "N") [param "x", .capture [param "x", param "y"]]))

/-- `LiftedC = [C][0]`, elaborated: `LiftedC(x, *r) = [C(x, r*, x)][0]` — the repeated `x`
    supplied from one binding, the collector re-spread because its SOURCE binding collects. -/
def rnLiftedCAlg : Algorithm :=
  algWithParameterPatterns [rnCap "x", rnColl "r"] [] []
    (rnLifted (.call (resolve "C") [param "x", .sequenceSpread (param "r"), param "x"]))

/-- `G((x, x)) = x`, its callable alias `SomeG = G` (which IS G, with its one sequence parameter
    `(x, x)`), and the formula `LiftedG = [G][0]`, elaborated `LiftedG(x) = [G((x, x))][0]`:
    deduplicating names leaves the caller's sequence group ONE non-collecting item, and a
    one-item sequence group does not exist (the singleton rule), so the lifted parameter is the
    name itself and the callee's group is rebuilt as the sequence `(x, x)` from the one binding. -/
def rnGAlg : Algorithm :=
  algWithParameterPatterns [.sequenceValue [rnCap "x", rnCap "x"]] [] [] [param "x"]

def rnSomeGAlg : Algorithm := rnAlias "G"

def rnLiftedGAlg : Algorithm :=
  alg ["x"] [] [] (rnLifted (.call (resolve "G") [.capture [param "x", param "x"]]))

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
    , ("Lifted", rnLiftedAlg), ("LiftedN", rnLiftedNAlg), ("LiftedC", rnLiftedCAlg)
    , ("G", rnGAlg), ("SomeG", rnSomeGAlg), ("LiftedG", rnLiftedGAlg) ]
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

-- 4. Two REFERENCES: their identities are compared before any VALUE (NEED-04, group-aware):
--    two different properties are the identity mismatch and neither body runs (no context);
--    one property twice matches by identity, and P's body then demands its value — Bad's
--    own failure, raised by the body, not by the binder.
#guard rnFailsWith rnIdentityFailure [rnCall "P" [resolve "Bad", resolve "Missing"]]
#guard rnFailsWith rnIdentityFailure [rnCall "P" [resolve "Missing", resolve "Bad"]]
#guard rnContexts [rnCall "P" [resolve "Bad", resolve "Missing"]] == 0
#guard rnFailsWith innermostIsDivByZero [rnCall "P" [resolve "Bad", resolve "Bad"]]

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

-- "First failure" means the ordinary inspection order (NEED-04, PAT-10), not a global
-- scan: the collector binds its slice without demanding it, the suffix's repeated `x`
-- demands its cells as they are visited, and a prefix's repeated-name conflict ends
-- the binding before the suffix is visited.
#guard rnFailsWith innermostIsBadIndex [rnCall "Suffix" [resolve "Bad", resolve "Missing", num 7]]
#guard rnFailsWith innermostIsDivByZero [rnCall "Suffix" [resolve "Missing", resolve "Bad", num 7]]
#guard rnContexts [rnCall "Suffix" [resolve "Bad", resolve "Missing", num 7]] == 1
#guard rnFailsWith innermostIsBadArity [rnCall "Prefix" [num 1, num 2, resolve "Bad", num 7]]
#guard rnContexts [rnCall "Prefix" [num 1, num 2, resolve "Bad", num 7]] == 0

-- 8. Clause families: a clause inspects only what its patterns need, and a repeated name
--    demands each occurrence when it is visited (NEED-04), so a failed or callable-only
--    argument a clause inspects is its own failure — it ends dispatch, never a
--    fall-through; equal values select the repeated clause. Family binders keep both
--    channels (PAT-07 as restated 2026-10-09), so two distinct callables with equal values
--    are incompatible identities: a non-match, and the next clause answers (`E(A, B)` is
--    `false`; before Model C, family binders carried values only and such callables matched
--    the repeated clause, PV-43).
#guard rnSucceedsWith [rnCall "E" [num 7, num 7]] (.bool true)
#guard rnSucceedsWith [rnCall "E" [num 7, num 8]] (.bool false)
#guard rnFailsWith innermostIsDivByZero [rnCall "E" [resolve "Bad", num 7]]
#guard rnFailsWith innermostIsDivByZero [rnCall "E" [num 7, resolve "Bad"]]
#guard rnFailsWith rnIncFailure [rnCall "E" [resolve "Inc", num 1]]
#guard rnSucceedsWith [rnCall "E" [resolve "A", resolve "B"]] (.bool false)

-- 9. Lists and sequences: the ONE structural, kind-sensitive value equality.
#guard rnSucceedsWith [rnCall "P" [.listLiteral [num 1], .listLiteral [num 1]]] (.listValue [.atom 1])
#guard rnFailsWith innermostIsBadArity [rnCall "P" [.listLiteral [num 1], num 1]]
#guard rnSucceedsWith [rnCall "P" [.capture [num 1, num 2], .capture [num 1, num 2]]]
  (.sequenceValue [.atom 1, .atom 2])
#guard rnFailsWith innermostIsBadArity [rnCall "P" [.listLiteral [num 1, num 2], .capture [num 1, num 2]]]
#guard rnSucceedsWith [rnCall "E" [.listLiteral [num 1], num 1]] (.bool false)

-- 10. Forwarding transports each parameter's supplied cell into the repeated name
--     (NEED-08): it never reconstructs a combined binding. Bad ran once (when P's binder
--     demanded it), Fwd bound (one context), and P never bound.
#guard rnFailsWith rnIncFailure [rnCall "Fwd" [resolve "Inc", num 1]]
#guard rnFailsWith rnIncFailure [rnCall "Fwd" [num 1, resolve "Inc"]]
#guard rnFailsWith innermostIsDivByZero [rnCall "Fwd" [resolve "Bad", num 7]]
#guard rnContexts [rnCall "Fwd" [resolve "Bad", num 7]] == 2
#guard rnSucceedsWith [rnCall "Fwd" [num 7, num 7]] (.atom 7)

-- 11. Dot-call is the ordinary call with the receiver as the leading argument.
#guard rnFailsWith rnIncFailure [.dotCall (resolve "Inc") "PC" (some [num 1])]
#guard rnFailsWith rnIncFailure [.dotCall (num 1) "PC" (some [resolve "Inc"])]
#guard rnFailsWith innermostIsDivByZero [.dotCall (num 7) "P" (some [resolve "Bad"])]

-- 12. Three occurrences: two different callables conflict by identity wherever they stand,
--     before Inc's value is ever demanded; equal identities agreeing with the value bind.
#guard rnFailsWith rnIdentityFailure [rnCall "T" [resolve "A", num 5, resolve "Inc"]]
#guard rnFailsWith rnIdentityFailure [rnCall "T" [resolve "Inc", resolve "A", num 5]]
#guard rnSucceedsWith [rnCall "T" [num 5, resolve "A", resolve "A"]] (.atom 5)

-- 13. Inspection order decides between a valueless occurrence and an unequal repeated
--     name (NEED-04, PAT-10): the first failure or conflict met in written order is
--     reported — `Q2(Bad, 7, 1, 2)` is Bad's own failure, while `Q2(1, 2, Bad, 7)` is the
--     unequal `x` (`badArity`) before `y` is visited. (Formerly D1's binding-before-verdict
--     order reported a valueless occurrence first wherever the unequal name stood.)
#guard rnFailsWith innermostIsDivByZero [rnCall "Q2" [resolve "Bad", num 7, num 1, num 2]]
#guard rnFailsWith innermostIsBadArity [rnCall "Q2" [num 1, num 2, resolve "Bad", num 7]]
#guard rnFailsWith innermostIsBadArity [rnCall "Q2" [num 1, num 2, resolve "Inc", resolve "Inc"]]
#guard rnFailsWith innermostIsBadArity [rnCall "Q2" [num 1, num 2, num 3, num 3]]

-- 14. The binder itself (the production `bindNeedPatterns` over `P(x, x)`'s two argument cells,
--     formed exactly as a call forms them): the kept binding of a successful repeated name is the
--     RICHEST contribution — an argument with a value AND a callable (`A`) beats a value-only one,
--     in either position (NEED-04, Q-28) — and a valueless contribution (a failing value, or a
--     callable-only `Inc` whose value demand is its own arity rejection) fails the binding with
--     ITS OWN outcome in either position; the other occurrence's value never stands in (Q-05).
def rnBindCtx : KatLang.EvalCtx :=
  { KatLang.EvalCtx.empty with callStack :=
      [algPrivate [] [] [("Id", rnIdAlg), ("A", rnAAlg), ("Bad", rnBadAlg), ("Inc", rnIncAlg)] []] }

/-- Bind `P(x, x)` over the given argument expressions through the production binder, returning
    the outcome and the argument cells. -/
def rnNeedBind (arguments : List KatLang.Expr) :
    KatLang.EvalM (Except Error (Option KatLang.NeedEnv) × List Nat) := do
  let addresses <- arguments.mapM (fun argument => KatLang.supplyNeed argument rnBindCtx [])
  let outcome <- KatLang.evalAttempt (KatLang.bindNeedPatterns
    ⟨KatLang.demandNeed, KatLang.projectNeedCallable⟩ [.bind "x", .bind "x"] addresses)
  pure (outcome, addresses)

/-- The repeated name binds the cell of argument `keptIndex`, whose value is `5` and which
    projects a callable. -/
def rnNeedKeeps (arguments : List KatLang.Expr) (keptIndex : Nat) : Bool :=
  match KatLang.runEvalM (do
      let (outcome, addresses) <- rnNeedBind arguments
      match outcome with
      | .ok (some [("x", address)]) =>
          let value <- KatLang.demandNeed address
          let callable <- KatLang.projectNeedCallable address
          pure (addresses[keptIndex]? == some address && value == (.atom 5, 1) && callable.isSome)
      | _ => pure false) with
  | .ok kept => kept
  | .error _ => false

def rnNeedFails (arguments : List KatLang.Expr) (check : Error -> Bool) : Bool :=
  match KatLang.runEvalM (do let (outcome, _) <- rnNeedBind arguments; pure outcome) with
  | .ok (.error err) => check err
  | _ => false

#guard rnNeedKeeps [resolve "A", num 5] 0
#guard rnNeedKeeps [num 5, resolve "A"] 1
#guard rnNeedFails [resolve "Bad", num 1] innermostIsDivByZero
#guard rnNeedFails [num 1, resolve "Bad"] innermostIsDivByZero
#guard rnNeedFails [resolve "Inc", num 1] rnIncFailure
#guard rnNeedFails [num 1, resolve "Inc"] rnIncFailure

--------------------------------------------------------------------------------
-- Formula lifting is by binding name; an alias IS its callee
-- (decided 2026-09-29; the by-name rule reverses Q-72; binding indirection 2026-10-01)
--------------------------------------------------------------------------------
-- A FORMULA that uses a callee supplies the caller's ONE binding of a name to
-- EVERY occurrence of that name in the callee's parameter patterns, exactly as
-- it shares one binding across callees (`H = F + G` is `H(x) = F(x) + G(x)`).
-- A body whose ONE row is the bare callee is not a formula: it is a CALLABLE
-- ALIAS (`Some = P` is P's callable itself, so a call through it takes P's two
-- independent arguments) — the earlier alias-signature deduplication
-- (`Some(x) = P(x, x)`) and the later exact-alias wrapper (`Some(x, x) =
-- P(x, x)`) are both superseded. Lean models no signature construction; it
-- evaluates the ELABORATED trees (the aliases as `Algorithm.alias`, the formulas
-- `rnLiftedAlg`, `rnLiftedNAlg`, `rnLiftedCAlg`, `rnLiftedGAlg`), and the Lean
-- programs of the corresponding spec cases are derived from the C# elaboration.
-- Each forwarded occurrence is an ordinary argument slot reading the one
-- binding, so the occurrences agree by construction on a value, and a
-- callable-only or failed argument is its own failure: nothing is merged.

-- 15. The callable alias IS its callee: it takes P's two independent arguments, with
--     P's constraint and P's failures, and adds NO binding context — an alias is no
--     invocation — re-evaluating nothing.
#guard rnSucceedsWith [rnCall "Some" [num 7, num 7]] (.atom 7)
#guard rnFailsWith innermostIsBadArity [rnCall "Some" [num 7, num 8]]
#guard rnFailsWith (innermostIsArityMismatch 2 1) [rnCall "Some" [num 7]]
#guard rnFailsWith innermostIsDivByZero [rnCall "Some" [resolve "Bad", num 7]]
#guard rnFailsWith rnIncFailure [rnCall "Some" [resolve "Inc", num 1]]
#guard rnContexts [rnCall "Some" [num 7, num 7]] == rnContexts [rnCall "P" [num 7, num 7]]
-- A failed argument lets neither the alias nor P bind: no context beyond Bad's own.
#guard rnContexts [rnCall "Some" [resolve "Bad", num 7]] == rnContexts [rnCall "P" [resolve "Bad", num 7]]
-- The formula is the written same-binding call, observation for observation: the
-- value, the failures, and the binding contexts (Lifted binds — one context — then P
-- binds — one more; a failed argument never lets P bind).
#guard rnSucceedsWith [rnCall "Lifted" [num 7]] (.atom 7)
#guard rnContexts [rnCall "Lifted" [num 7]] == 2
#guard rnContexts [rnCall "Lifted" [num 7]] == rnContexts [rnCall "Same" [num 7]]
#guard rnFailsWith innermostIsDivByZero [rnCall "Lifted" [resolve "Bad"]]
#guard rnContexts [rnCall "Lifted" [resolve "Bad"]] == rnContexts [rnCall "Same" [resolve "Bad"]]
#guard rnFailsWith rnIncFailure [rnCall "Lifted" [resolve "Inc"]]
#guard rnSucceedsWith [rnCall "Lifted" [.listLiteral [num 1]]] (.listValue [.atom 1])
-- One binding name is one formula parameter: two arguments are an arity error ...
#guard rnFailsWith (innermostIsArityMismatch 1 2) [rnCall "Lifted" [num 7, num 7]]
-- ... while the direct call still supplies independent arguments (Q-05).
#guard rnFailsWith innermostIsBadArity [rnCall "P" [num 7, num 8]]

-- 16. A nested repetition and a collector: the aliases are the callees, with their own
--     shapes and constraints; the formulas forward by name — one binding for `x`, the group
--     keeping its shape for `y`, the collector re-spread by its kind.
#guard rnSucceedsWith [rnCall "SomeN" [num 7, .capture [num 7, num 8]]] (.atom 8)
#guard rnFailsWith innermostIsBadArity [rnCall "SomeN" [num 6, .capture [num 7, num 8]]]
#guard rnSucceedsWith [rnCall "SomeC" [num 7, num 9, num 7]] (.atom 7)
#guard rnFailsWith innermostIsBadArity [rnCall "SomeC" [num 7, num 9, num 8]]
#guard rnSucceedsWith [rnCall "LiftedN" [num 7, num 8]] (.atom 8)
#guard rnFailsWith innermostIsDivByZero [rnCall "LiftedN" [resolve "Bad", num 8]]
#guard rnFailsWith rnIncFailure [rnCall "LiftedN" [resolve "Inc", num 8]]
#guard rnSucceedsWith [rnCall "LiftedC" [num 7, num 9]] (.atom 7)
#guard rnFailsWith innermostIsDivByZero [rnCall "LiftedC" [resolve "Bad", num 9]]

-- 17. Who supplies the occurrences decides what is checked. An explicit call with its
--     OWN two parameters keeps P's arguments independent (`Fwd(a, b) = P(a, b)`, section
--     10): equal values match, unequal values are P's own `badArity`. Writing one
--     binding into both occurrences (`Same(x) = P(x, x)`) is what a formula does — and
--     what bare forwarding `Q(x) = P` does, since it reuses Q's one binding `x` by name
--     (`bareForwardingArguments`, `CoreTests/AliasForwarding.lean`). A nested repetition's
--     explicit call (`NW(p, q) = N(p, q)`) keeps N's constraint.
#guard rnSucceedsWith [rnCall "Fwd" [num 7, num 7]] (.atom 7)
#guard rnFailsWith innermostIsBadArity [rnCall "Fwd" [num 7, num 8]]
#guard rnSucceedsWith [rnCall "Same" [num 7]] (.atom 7)
#guard rnFailsWith innermostIsDivByZero [rnCall "Same" [resolve "Bad"]]
#guard rnFailsWith rnIncFailure [rnCall "Same" [resolve "Inc"]]
#guard rnSucceedsWith [rnCall "NW" [num 7, .capture [num 7, num 8]]] (.atom 8)
#guard rnFailsWith innermostIsBadArity [rnCall "NW" [num 6, .capture [num 7, num 8]]]

-- 18. The one-name group lifts as its one name in a FORMULA (September 2026,
--     structural patterns): `LiftedG(x) = [G((x, x))][0]` binds its argument WHOLE,
--     whatever its kind, exactly like the written `Same`-style explicit call, and G's
--     pattern then checks the two occurrences it was given. (The former lifted `(x)`
--     opened lists and took scalars; a one-item sequence pattern no longer exists.)
--     The callable alias `SomeG = G` is G, with its one SEQUENCE parameter. These
--     guards evaluate the trees; C# tests separately pin that elaboration produces them.
#guard rnSucceedsWith [rnCall "LiftedG" [num 7]] (.atom 7)
#guard rnSucceedsWith [rnCall "LiftedG" [.listLiteral [num 7]]] (.listValue [.atom 7])
#guard rnSucceedsWith [rnCall "LiftedG" [.listLiteral [.capture [num 7, num 8]]]]
  (.listValue [.sequenceValue [.atom 7, .atom 8]])
#guard rnSucceedsWith [rnCall "LiftedG" [.capture [num 7, num 8]]] (.sequenceValue [.atom 7, .atom 8])
#guard rnSucceedsWith [rnCall "LiftedG" [.listLiteral []]] (.listValue [])
#guard rnFailsWith innermostIsDivByZero [rnCall "LiftedG" [resolve "Bad"]]
#guard rnFailsWith (innermostIsArityMismatch 1 2) [rnCall "LiftedG" [num 7, num 7]]
#guard rnSucceedsWith [rnCall "SomeG" [.capture [num 7, num 7]]] (.atom 7)
#guard rnFailsWith innermostIsBadArity [rnCall "SomeG" [.capture [num 7, num 8]]]
#guard rnFailsWith innermostIsAnyTypeMismatch [rnCall "SomeG" [num 7]]

end KatLangTests
