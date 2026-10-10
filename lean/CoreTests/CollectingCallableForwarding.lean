import KatLang
import CoreTests.Common

--------------------------------------------------------------------------------
-- A COLLECTING PARAMETER PRESERVES THE SUPPLIED DEMANDABLE CELLS (VAR-03)
--------------------------------------------------------------------------------
-- VAR-03 as reconciled on 2026-10-09: the owner adopted the Model-C NEED-07/08
-- collector and forwarding laws, superseding the older "a collecting binding
-- collects values, never callables" text. Three DIFFERENT operations:
--
-- * COLLECTING. A collecting parameter `*xs` binds an exact slice of the supplied
--   cells (`bindNeedPatterns` → a `.collector` suspension). Binding demands none
--   of them.
-- * RE-SPREADING A KNOWN SLICE. `xs*` transfers those very cells
--   (`formNeedSupply`'s `.collector` arm), with whatever VALUE/CALLABLE channels
--   they already have and without forcing them: a callable that flows through a
--   collector and is re-spread is callable again. No identity is invented — a
--   value, a capture or a computed result stays value-only (NEED-06).
-- * READING THE COLLECTOR AS A VALUE. Ordinary `xs` materializes ONE exact eager
--   list (`demandNeed` of the collector), demanding every element by its own VALUE
--   contract; a callable element reports its own zero-argument demand failure,
--   never a collector-specific type mismatch. The unspread collector is one
--   collection-valued computation with no CALLABLE identity.
--
-- An ARBITRARY spread `E*` (a list literal, a call result, a fixed parameter
-- holding a list) is still evaluated during supply formation (NEED-07), and
-- re-spread items are never reopened. These guards evaluate the production model
-- on the elaborated ASTs of the source witnesses; the heap guards at the end
-- inspect the supply heap directly. C#: `CollectingCallableForwardingLawTests`
-- (six routes); spec case `collected-callable-survives-explicit-respread`.

namespace KatLangTests.CollectingCallableForwarding
open KatLang

private def bad : Expr := .binary .div (.num 1) (.num 0)

private def collecting (name : Ident) (body : List Expr) : Algorithm :=
  algWithParameters [{ name := name, kind := .collecting }] [] [] body

-- Inc(x) = x + 1
private def ccfInc : Algorithm := alg ["x"] [] [] [.binary .add (.param "x") (.num 1)]
-- Apply(f) = f(9)
private def ccfApply : Algorithm := alg ["f"] [] [] [.call (.param "f") [.num 9]]
-- Fwd(*fs) = Apply(fs*)
private def ccfFwd : Algorithm := collecting "fs" [.call (.resolve "Apply") [.sequenceSpread (.param "fs")]]

private def run (props : List (Prod Ident Algorithm)) (out : List Expr) : Except Error Result :=
  runResult (.algorithmExpr (algPrivate [] [] props out))

private def yields (props : List (Prod Ident Algorithm)) (out : List Expr) (expected : Result) : Bool :=
  match run props out with
  | .ok value => value == expected
  | _ => false

private def fails (props : List (Prod Ident Algorithm)) (out : List Expr) (classify : Error -> Bool) : Bool :=
  match run props out with
  | .error err => classify err
  | _ => false

private def innermost : Error -> Error
  | .withContext _ inner => innermost inner
  | err => err

/-- Both programs fail with the SAME innermost error (contexts aside). -/
private def sameInnermostFailure (left right : Except Error Result) : Bool :=
  match left, right with
  | .error a, .error b => reprStr (innermost a) == reprStr (innermost b)
  | _, _ => false

private def notCallable : Error -> Bool := innermostIsNotAnAlgorithm "param(f)"

-- 1. The canonical witnesses ------------------------------------------------------

-- V1: Fwd(Inc) is 10 — the known slice re-spread carries Inc's CALLABLE channel.
#guard yields [("Inc", ccfInc), ("Apply", ccfApply), ("Fwd", ccfFwd)] [.call (.resolve "Fwd") [.resolve "Inc"]] (.atom 10)

-- V2: ApplyFirst(*fs) = map([1, 2], fs*) / ApplyFirst(Inc) — the builtin callback slot
-- receives the transported callable.
#guard yields [("Inc", ccfInc),
    ("ApplyFirst", collecting "fs" [.call (.resolve "map") [.listLiteral [.num 1, .num 2], .sequenceSpread (.param "fs")]])]
  [.call (.resolve "ApplyFirst") [.resolve "Inc"]] (.listValue [.atom 2, .atom 3])

-- V3/V4: Ignore(*xs) = 1 demands nothing — neither Inc's zero-argument VALUE nor a failure.
#guard yields [("Inc", ccfInc), ("Ignore", collecting "xs" [.num 1])] [.call (.resolve "Ignore") [.resolve "Inc"]] (.atom 1)
#guard yields [("Bad", alg [] [] [] [bad]), ("Ignore", collecting "xs" [.num 1])] [.call (.resolve "Ignore") [.resolve "Bad"]] (.atom 1)

-- V5: Collect(*xs) = xs / Collect(Inc) — materializing the collector demands Inc's
-- VALUE: Inc's own arity rejection (1 expected, 0 supplied), not a collector error.
#guard fails [("Inc", ccfInc), ("Collect", collecting "xs" [.param "xs"])] [.call (.resolve "Collect") [.resolve "Inc"]]
  (innermostIsArityMismatch 1 0)

-- 2. A known slice versus the collector's VALUE versus arbitrary spreads -------------

private def withFwdBody (body : Expr) : List (Prod Ident Algorithm) :=
  [("Inc", ccfInc), ("Apply", ccfApply), ("Hold", alg ["v"] [] [] [.param "v"]), ("Fwd", collecting "fs" [body])]

-- V6a: Apply(fs) passes the collector itself — one collection-valued computation with no
-- CALLABLE identity; invoking it is NotAnAlgorithm by projection (no VALUE demand).
#guard fails (withFwdBody (.call (.resolve "Apply") [.param "fs"])) [.call (.resolve "Fwd") [.resolve "Inc"]] notCallable
-- V6b: a selection is a computed value: no identity.
#guard fails (withFwdBody (.call (.resolve "Apply") [.index (.param "fs") (.num 0)])) [.call (.resolve "Fwd") [.resolve "Inc"]] notCallable
-- V6f: a capture of the spread is one sequence-valued computation: no identity.
#guard fails (withFwdBody (.call (.resolve "Apply") [.capture [.sequenceSpread (.param "fs")]])) [.call (.resolve "Fwd") [.resolve "Inc"]] notCallable
-- V6c: an ordinary materialized list, then `*`: building `[fs*]` demands Inc's VALUE.
#guard fails (withFwdBody (.call (.resolve "Apply") [.sequenceSpread (.listLiteral [.sequenceSpread (.param "fs")])]))
  [.call (.resolve "Fwd") [.resolve "Inc"]] (innermostIsArityMismatch 1 0)
-- V6d: an arbitrary computed spread operand is evaluated during supply formation.
#guard fails (withFwdBody (.call (.resolve "Apply") [.sequenceSpread (.call (.resolve "Hold") [.param "fs"])]))
  [.call (.resolve "Fwd") [.resolve "Inc"]] (innermostIsArityMismatch 1 0)
-- V6e2: a FIXED parameter holding a list is not a collector slice:
-- Fix(xs) = Apply(xs*) / Wrap(f) = Fix([f]) / Wrap(Inc).
#guard fails [("Inc", ccfInc), ("Apply", ccfApply),
    ("Fix", alg ["xs"] [] [] [.call (.resolve "Apply") [.sequenceSpread (.param "xs")]]),
    ("Wrap", alg ["f"] [] [] [.call (.resolve "Fix") [.listLiteral [.param "f"]]])]
  [.call (.resolve "Wrap") [.resolve "Inc"]] (innermostIsArityMismatch 1 0)
-- V6g/V6h: slices and materialized lists of VALUES re-spread as ordinary items.
#guard yields [("Add", alg ["a", "b"] [] [] [.binary .add (.param "a") (.param "b")]),
    ("Fwd", collecting "xs" [.call (.resolve "Add") [.sequenceSpread (.param "xs")]])]
  [.call (.resolve "Fwd") [.num 1, .num 2]] (.atom 3)
#guard yields [("Add", alg ["a", "b"] [] [] [.binary .add (.param "a") (.param "b")]),
    ("Fix", alg ["xs"] [] [] [.call (.resolve "Add") [.sequenceSpread (.param "xs")]])]
  [.call (.resolve "Fix") [.listLiteral [.num 1, .num 2]]] (.atom 3)
-- V6i: no recursive spreading — re-spread items are never reopened.
#guard yields [("Use", collecting "ys" [.param "ys"]), ("Fwd", collecting "xs" [.call (.resolve "Use") [.sequenceSpread (.param "xs")]])]
  [.call (.resolve "Fwd") [.capture [.num 1, .num 2], .listLiteral [.num 3]]]
  (.listValue [.sequenceValue [.atom 1, .atom 2], .listValue [.atom 3]])

-- 3. Laziness through transport, and the operation that demands -------------------

private def useAndForward (forwardTo : Ident) : List (Prod Ident Algorithm) :=
  [("Use", collecting "ys" [.param "ys"]), ("Ignore", collecting "ys" [.num 1]),
   ("Fwd", collecting "xs" [.call (.resolve forwardTo) [.sequenceSpread (.param "xs")]])]

-- V7e: a transported failure that nothing demands stays suspended.
#guard yields (useAndForward "Ignore") [.call (.resolve "Fwd") [bad]] (.atom 1)
-- V7f: the materialization that demands the original cell reports its failure.
#guard fails (useAndForward "Use") [.call (.resolve "Fwd") [bad]] innermostIsDivByZero
-- V7aa: a collector and a fixed parameter treat an unused failed argument alike.
#guard yields [("Bad", alg [] [] [] [bad]), ("Fix", alg ["x"] [] [] [.num 1]), ("Ignore", collecting "xs" [.num 1])]
  [.call (.resolve "Fix") [.resolve "Bad"], .call (.resolve "Ignore") [.resolve "Bad"]]
  (.sequenceValue [.atom 1, .atom 1])
-- V7ab/V7ac: an output-less written block is demanded only when the collector is read.
private def noOutputBlock : Expr := .algorithmExpr (alg [] [] [privateProp "X" (alg [] [] [] [.num 1])] [])
#guard yields [("Coll", collecting "xs" [.num 1])] [.call (.resolve "Coll") [noOutputBlock]] (.atom 1)
#guard fails [("Coll", collecting "xs" [.param "xs"])] [.call (.resolve "Coll") [noOutputBlock]] innermostIsMissingOutput

-- 4. Every forwarding route and callable kind keeps the CALLABLE channel ------------

-- V7h: three wrappers.
#guard yields [("Inc", ccfInc), ("Apply", ccfApply), ("Fwd", ccfFwd),
    ("Fwd2", collecting "gs" [.call (.resolve "Fwd") [.sequenceSpread (.param "gs")]]),
    ("Fwd3", collecting "hs" [.call (.resolve "Fwd2") [.sequenceSpread (.param "hs")]])]
  [.call (.resolve "Fwd3") [.resolve "Inc"]] (.atom 10)
-- V7i: a callable alias is its target's callable.
#guard yields [("A", .alias none [] [] (.resolve "Inc")), ("Inc", ccfInc), ("Apply", ccfApply), ("Fwd", ccfFwd)]
  [.call (.resolve "Fwd") [.resolve "A"]] (.atom 10)
-- V7j: a clause family.
#guard yields [("Apply", ccfApply),
    ("Fam", .conditional none [] [⟨.litInt 0, alg [] [] [] [.num 100]⟩, ⟨.bind "n", alg [] [] [] [.binary .add (.param "n") (.num 1)]⟩]),
    ("Fwd", ccfFwd)]
  [.call (.resolve "Fwd") [.resolve "Fam"]] (.atom 10)
-- V7l: a recursive clause family (Fact(9)).
#guard yields [("Apply", ccfApply),
    ("Fact", .conditional none [] [⟨.litInt 0, alg [] [] [] [.num 1]⟩,
      ⟨.bind "n", alg [] [] [] [.binary .mul (.param "n") (.call (.resolve "Fact") [.binary .sub (.param "n") (.num 1)])]⟩]),
    ("Fwd", ccfFwd)]
  [.call (.resolve "Fwd") [.resolve "Fact"]] (.atom 362880)
-- V7m: a builtin (count of one scalar).
#guard yields [("Apply", ccfApply), ("Fwd", ccfFwd)] [.call (.resolve "Fwd") [.resolve "count"]] (.atom 1)
-- V7n: an anonymous brace block `{ x * 2 }`.
#guard yields [("Apply", ccfApply), ("Fwd", ccfFwd)]
  [.call (.resolve "Fwd") [.algorithmExpr (alg ["x"] [] [] [.binary .mul (.param "x") (.num 2)])]] (.atom 18)
-- V7v: a mixed prefix/collector/suffix list.
#guard yields [("Inc", ccfInc), ("Apply", ccfApply),
    ("Mid", algWithParameters [{ name := "a" }, { name := "fs", kind := .collecting }, { name := "z" }] [] []
      [.call (.resolve "Apply") [.sequenceSpread (.param "fs")]])]
  [.call (.resolve "Mid") [.num 1, .resolve "Inc", .num 2]] (.atom 10)
-- V7x: bare forwarding `Relay(*fs) = Use` (elaborated `Use(fs*)`) transfers the slice.
#guard yields [("Inc", ccfInc), ("Apply", ccfApply),
    ("Use", collecting "fs" [.call (.resolve "Apply") [.sequenceSpread (.param "fs")]]),
    ("Relay", collecting "fs" [.call (.resolve "Use") [.sequenceSpread (.param "fs")]])]
  [.call (.resolve "Relay") [.resolve "Inc"]] (.atom 10)
-- V7z: a FIXED source into a collecting destination (`Relay(fs) = Use`, elaborated `Use(fs)`).
#guard yields [("Inc", ccfInc), ("Apply", ccfApply),
    ("Use", collecting "fs" [.call (.resolve "Apply") [.sequenceSpread (.param "fs")]]),
    ("Relay", alg ["fs"] [] [] [.call (.resolve "Use") [.param "fs"]])]
  [.call (.resolve "Relay") [.resolve "Inc"]] (.atom 10)
-- V7af: a two-cell slice re-spread into two FIXED callable parameters: Inc(Inc(1)).
#guard yields [("Inc", ccfInc),
    ("Apply2", alg ["f", "g"] [] [] [.call (.param "f") [.call (.param "g") [.num 1]]]),
    ("Both", collecting "fs" [.call (.resolve "Apply2") [.sequenceSpread (.param "fs")]])]
  [.call (.resolve "Both") [.resolve "Inc", .resolve "Inc"]] (.atom 3)

-- 5. No capability is invented; cardinality precedes any demand --------------------

-- V7q: a scalar never becomes callable by passing through a collector.
#guard fails [("Apply", ccfApply), ("Fwd", ccfFwd)] [.call (.resolve "Fwd") [.num 5]] notCallable
-- V7s2: a capture stays value-only: Pair(f) = Fwd((f, f)) / Pair(Inc).
#guard fails [("Inc", ccfInc), ("Apply", ccfApply), ("Fwd", ccfFwd),
    ("Pair", alg ["f"] [] [] [.call (.resolve "Fwd") [.capture [.param "f", .param "f"]]])]
  [.call (.resolve "Pair") [.resolve "Inc"]] notCallable
-- V7t/V7u: two cells or none for Apply's one parameter.
#guard fails [("Inc", ccfInc), ("Apply", ccfApply), ("Fwd", ccfFwd)] [.call (.resolve "Fwd") [.resolve "Inc", .resolve "Inc"]]
  (innermostIsArityMismatch 1 2)
#guard fails [("Inc", ccfInc), ("Apply", ccfApply), ("Fwd", ccfFwd)] [.call (.resolve "Fwd") []] (innermostIsArityMismatch 1 0)
-- V7w2: a structural pattern demands its argument's VALUE; its nested collector holds
-- ready values only: Nest((*fs)) = Apply(fs*) / Pair(f) = Nest((f, f)) / Pair(Inc).
#guard fails [("Inc", ccfInc), ("Apply", ccfApply),
    ("Nest", algWithParameterPatterns [.sequenceValue [.capture { name := "fs", kind := .collecting }]] [] []
      [.call (.resolve "Apply") [.sequenceSpread (.param "fs")]]),
    ("Pair", alg ["f"] [] [] [.call (.resolve "Nest") [.capture [.param "f", .param "f"]]])]
  [.call (.resolve "Pair") [.resolve "Inc"]] (innermostIsArityMismatch 1 0)

-- 6. Materializing a collector reports the ORIGINAL callable's own error -------------
--    (oracle: the same callable value-demanded through a FIXED parameter, `Id(x) = x`)

private def viaCollector (defs : List (Prod Ident Algorithm)) (arg : Expr) : Except Error Result :=
  run (defs ++ [("Coll", collecting "xs" [.param "xs"])]) [.call (.resolve "Coll") [arg]]
private def viaFixed (defs : List (Prod Ident Algorithm)) (arg : Expr) : Except Error Result :=
  run (defs ++ [("Id", alg ["x"] [] [] [.param "x"])]) [.call (.resolve "Id") [arg]]
private def famZeroOne : Algorithm :=
  .conditional none [] [⟨.litInt 0, alg [] [] [] [.num 0]⟩, ⟨.bind "n", alg [] [] [] [.param "n"]⟩]

#guard sameInnermostFailure (viaCollector [("Inc", ccfInc)] (.resolve "Inc")) (viaFixed [("Inc", ccfInc)] (.resolve "Inc"))
#guard sameInnermostFailure (viaCollector [] (.resolve "sum")) (viaFixed [] (.resolve "sum"))
#guard sameInnermostFailure (viaCollector [("Fam", famZeroOne)] (.resolve "Fam")) (viaFixed [("Fam", famZeroOne)] (.resolve "Fam"))
#guard match viaCollector [("Fam", famZeroOne)] (.resolve "Fam") with
  | .error err => innermostIsNoMatchingBranch "Fam" err
  | _ => false

-- 7. Supply formation still evaluates an arbitrary spread (NEED-07) ----------------

-- V7ah: Ignore((1 / 0)*) fails although Ignore never reads its collector.
#guard fails [("Ignore", collecting "xs" [.num 1])] [.call (.resolve "Ignore") [.sequenceSpread bad]] innermostIsDivByZero

-- 8. The supply heap: transport and CALLABLE invocation never force VALUE -----------

private def isSuspended (address : Nat) : EvalM Bool := do
  match (<- get).needs[address]? with
  | some { state := .suspended, .. } => pure true
  | _ => pure false

-- Inc's supplied cell crosses two collectors (two re-spreads) and one invocation through
-- its CALLABLE channel; the invocation yields 10, the opened supply is that very cell,
-- and the cell and both collectors are still suspended: nothing demanded Inc's VALUE.
def transportedCallableStaysSuspended : EvalM Bool := do
  let root := algPrivate [] [] [("Inc", ccfInc), ("Apply", ccfApply)] []
  let ctx := EvalCtx.empty.push root
  let supplied <- supplyNeed (.resolve "Inc") ctx []
  let outer <- allocateNeed (.collector [supplied])
  let forwarded <- formNeedSupply [.sequenceSpread (.param "fs")] { ctx with needEnv := [("fs", outer)] } []
  let inner <- allocateNeed (.collector forwarded)
  let opened <- formNeedSupply [.sequenceSpread (.param "gs")] { ctx with needEnv := [("gs", inner)] } []
  let result <- evalNeedUserSupply ccfApply opened ctx []
  pure (forwarded == [supplied] && opened == [supplied] && result.fst == .atom 10 &&
    (<- isSuspended supplied) && (<- isSuspended outer) && (<- isSuspended inner))
#guard (runEvalM transportedCallableStaysSuspended).toOption == some true

-- Materializing a SECOND collector over the same transported cells observes the first
-- completion: the original cell is evaluated once, and its outcome is shared.
def oneOriginalCellThroughTwoCollectors : EvalM Bool := do
  let supplied <- supplyNeed (.call (.algorithmExpr (alg [] [] [] [.num 7])) []) EvalCtx.empty []
  let first <- allocateNeed (.collector [supplied])
  let second <- allocateNeed (.collector [supplied])
  let one <- demandNeed first
  let afterFirst := (<- get).nextBindingContext
  let two <- demandNeed second
  pure (one == two && one == (.listValue [.atom 7], 1) && (<- get).nextBindingContext == afterFirst &&
    !(<- isSuspended supplied))
#guard (runEvalM oneOriginalCellThroughTwoCollectors).toOption == some true

-- The unspread collector projects NO callable identity, and projecting does not force it.
def collectorHasNoCallableIdentity : EvalM Bool := do
  let root := algPrivate [] [] [("Inc", ccfInc)] []
  let supplied <- supplyNeed (.resolve "Inc") (EvalCtx.empty.push root) []
  let collector <- allocateNeed (.collector [supplied])
  let identity <- projectNeedCallable collector
  let element <- projectNeedCallable supplied
  pure (identity.isNone && element.isSome && (<- isSuspended collector) && (<- isSuspended supplied))
#guard (runEvalM collectorHasNoCallableIdentity).toOption == some true

-- A fixed binder transports the collector CELL, so its known slice survives.
private def fixedCarrier : Algorithm := alg ["v"] [] [] [.call (.resolve "Apply") [.sequenceSpread (.param "v")]]
#guard yields [("Inc", ccfInc), ("Apply", ccfApply), ("Pass", fixedCarrier),
    ("Outer", collecting "fs" [.call (.resolve "Pass") [.param "fs"]])]
  [.call (.resolve "Outer") [.resolve "Inc"]] (.atom 10)
#guard yields [("Ignore", collecting "ys" [.num 7]),
    ("Pass", alg ["v"] [] [] [.call (.resolve "Ignore") [.sequenceSpread (.param "v")]]),
    ("Outer", collecting "xs" [.call (.resolve "Pass") [.param "xs"]])]
  [.call (.resolve "Outer") [bad]] (.atom 7)
-- Materializing a collector does not remove its known slice or its elements' identity.
#guard yields [("Z", alg [] [] [] [.num 7]), ("Call", alg ["f"] [] [] [.call (.param "f") []]),
    ("Outer", collecting "xs" [.param "xs", .call (.resolve "Call") [.sequenceSpread (.param "xs")]])]
  [.call (.resolve "Outer") [.resolve "Z"]] (.sequenceValue [.listValue [.atom 7], .atom 7])
-- Selection receives the whole eager list: a failure in its tail aborts before selection.
#guard fails [("Outer", collecting "xs" [.index (.param "xs") (.num 0)])]
  [.call (.resolve "Outer") [.num 1, bad]] innermostIsDivByZero

end KatLangTests.CollectingCallableForwarding
