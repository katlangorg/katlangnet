import KatLangArityLaws.NeedControl

open KatLang NeedSupply NeedDemand

namespace KatLang.NeedControlGuards.Witnesses
theorem invalid_parameter_transport :
    (supplyNeed (.param "x") { callStack := [], needEnv := [("x", 99)] } []).runState
      EvalState.empty = (.ok 99, EvalState.empty) := rfl

def cycleCtx : EvalCtx := { callStack := [], needEnv := [("x", 0)] }
def cycleState : EvalState := { needs := #[{ suspension := .expression (.param "x") cycleCtx [] }] }
#guard match (demandNeed 0).runState cycleState with
  | (.error .demandCycle, s) =>
    match s.needs[0]? with
    | some (NeedCell.mk _ (.completed (.error .demandCycle)) _ _ _ _ _ _ _) => true
    | _ => false
  | _ => false

def sliceState : EvalState := { needs := #[
  { suspension := .expression (.param "missing") EvalCtx.empty [] },
  { suspension := .collector [0, 0] }] }
def sliceCtx : EvalCtx := { callStack := [], needEnv := [("xs", 1)] }

#guard match (formNeedSupplySourced [.sequenceSpread (.param "xs")] sliceCtx []).runState sliceState with
  | (.ok [(0, some (.param "missing")), (0, some (.param "missing"))], s) =>
    s.needs.size == 2 &&
    match s.needs[0]?, s.needs[1]? with
    | some (NeedCell.mk _ .suspended _ _ _ _ _ _ _), some (NeedCell.mk _ .suspended _ _ _ _ _ _ _) => true
    | _, _ => false
  | _ => false

#guard match (demandNeed 1).runState sliceState with
  | (.error (.unknownName "missing"), s) =>
    match s.needs[1]? with
    | some (NeedCell.mk _ (.completed (.error (.unknownName "missing"))) _ _ _ _ _ _ _) => true
    | _ => false
  | _ => false

#guard match (do
    let a ← readyNeed (.atom 7, 1)
    projectNeedCallable a).runState EvalState.empty with
  | (.ok none, _) => true
  | _ => false

end KatLang.NeedControlGuards.Witnesses

namespace KatLang.NeedControlGuards
open KatLang.NeedControl.Collector
/- Adversarial executable guards below exercise actual helpers or current opaque production. -/
def refuse (_ : Expr) (_ : EvalCtx) (_ : ValEnv) : EvalM SpreadSupply := throw Error.divByZero
def ctx (name : Ident) (a : Nat) : EvalCtx := {callStack := [], needEnv := [(name, a)]}

-- A list-valued Ready parameter is not a collector suspension.
#guard match (spreadCollectorSlice? (.param "xs") (ctx "xs" 0)).runState
    {needs := #[{suspension := .ready (.listValue [.atom 7], 1)}]} with
  | (.ok none, s) => s.needs.size == 1
  | _ => false

-- A dangling collector candidate fails; ordinary supply transport still accepts it.
#guard match (spreadCollectorSlice? (.param "xs") (ctx "xs" 99)).runState EvalState.empty with
  | (.error .badArity, _) => true
  | _ => false

-- Arbitrary counts do not describe the number of countedTopLevelValues items.
#guard (countedTopLevelValues (.sequenceValue [.atom 3, .atom 4], 99)).length == 2

-- Whole spread callback, mixed source metadata, Ready counts, ordering, and aliased slice.
def mixedState : EvalState := {needs := #[
  {suspension := .expression (.num 40) EvalCtx.empty []},
  {suspension := .collector [0, 0]}]}
def observeWritten (e : Expr) (_ : EvalCtx) (_ : ValEnv) : EvalM SpreadSupply := do
  match e with
  | .sequenceSpread (.num 5) =>
    modify fun s => {s with nextRuntimeDeclaration := s.nextRuntimeDeclaration + 1}
    pure (.items (countedTopLevelValues
      (.sequenceValue [.sequenceValue [], .listValue [], .sequenceValue [.atom 1, .atom 2]], 99)))
  | _ => throw Error.divByZero
#guard match (form observeWritten (ctx "xs" 1) []
    [.num 9, .sequenceSpread (.param "xs"), .sequenceSpread (.num 5)]).runState mixedState with
  | (.ok [(2, some (.num 9)), (0, some (.num 40)), (0, some (.num 40)),
      (3, none), (4, none), (5, none)], s) =>
    s.needs.size == 6 && s.nextRuntimeDeclaration == 1 &&
    match s.needs[3]?, s.needs[4]?, s.needs[5]? with
    | some (NeedCell.mk (.ready (.sequenceValue [], 0)) .suspended .unprojected _ _ _ _ _ _),
      some (NeedCell.mk (.ready (.listValue [], 1)) .suspended .unprojected _ _ _ _ _ _),
      some (NeedCell.mk (.ready (.sequenceValue [.atom 1, .atom 2], 1)) .suspended .unprojected _ _ _ _ _ _) => true
    | _, _, _ => false
  | _ => false

-- Ordinary metadata uses current written param even when original source is different.
#guard match (form refuse (ctx "x" 0) [] [.param "x"]).runState mixedState with
  | (.ok [(0, some (.param "x"))], s) => s.needs.size == 2
  | _ => false

-- A failing spread keeps earlier ordinary allocation and the callback's own allocation.
def failingSpread (_ : Expr) (_ : EvalCtx) (_ : ValEnv) : EvalM SpreadSupply := do
  let _ ← readyNeed (.atom 7, 1)
  modify fun s => {s with nextRuntimeDeclaration := 23}
  throw Error.divByZero
#guard match (form failingSpread EvalCtx.empty []
    [.num 1, .sequenceSpread (.num 2), .num 3]).runState EvalState.empty with
  | (.error .divByZero, s) => s.needs.size == 2 && s.nextRuntimeDeclaration == 23 &&
    match s.needs[0]?, s.needs[1]? with
    | some (NeedCell.mk (.expression (.num 1) _ _) .suspended _ _ _ _ _ _ _),
      some (NeedCell.mk (.ready (.atom 7, 1)) .suspended _ _ _ _ _ _ _) => true
    | _, _ => false
  | _ => false

-- Actual B2 materialization: effects 1,2 retained; third element never demanded.
#guard match (materialize KatLang.NeedControl.Collector.stateful [1, 2, 3]).runState EvalState.empty with
  | (.error .badArity, s) => s.nextBindingContext == 112
  | _ => false

-- Completion must preserve callable memo changes made by the callback even on failure.
def failWithMemo (_ : Expr) (_ : EvalCtx) (_ : ValEnv) : EvalM CountedResult := do
  modify fun s => {s with
    needs := s.needs.modify 0 (fun c => {c with callable := .projected (.ok none)})
    nextRuntimeDeclaration := s.nextRuntimeDeclaration + 17}
  throw Error.divByZero
def oneExpr : EvalState := {needs := #[{suspension := .expression (.num 1) EvalCtx.empty []}]}
#guard match (NeedDemand.step failWithMemo productionPlanRoute (fun _ => throw Error.badArity) 0).runState oneExpr with
  | (.error .divByZero, s) => s.nextRuntimeDeclaration == 17 &&
    match s.needs[0]? with
    | some (NeedCell.mk (.expression (.num 1) _ _) (.completed (.error .divByZero)) (.projected (.ok none)) _ _ _ _ _ _) => true
    | _ => false
  | _ => false

-- A completed failure is reused without restarting its expression or callback.
#guard match (do
    let _ ← evalAttempt (NeedDemand.step failWithMemo productionPlanRoute (fun _ => throw Error.badArity) 0)
    NeedDemand.step failWithMemo productionPlanRoute (fun _ => throw Error.badArity) 0).runState oneExpr with
  | (.error .divByZero, s) => s.nextRuntimeDeclaration == 17
  | _ => false

-- Public production entry point observes a cached failure even if VALUE would succeed.
#guard match (demandNeed 0).runState {needs := #[
    {suspension := .expression (.num 1) EvalCtx.empty [],
      state := .completed (.error .divByZero)}]} with
  | (.error .divByZero, _) => true
  | _ => false

-- A shrinking callback makes publication a no-op: original validity alone is insufficient.
def shrinkExpression (_ : Expr) (_ : EvalCtx) (_ : ValEnv) : EvalM CountedResult := do
  modify fun s => {s with needs := #[]}
  throw Error.badArity
#guard match (NeedDemand.step shrinkExpression productionPlanRoute (fun _ => throw Error.badArity) 0).runState oneExpr with
  | (.error .badArity, s) => s.needs.size == 0
  | _ => false

-- Shrink between actual production allocations reuses address zero.
#guard match (do
    let a ← allocateNeed (.ready (.atom 1, 1))
    modify fun s => {s with needs := #[]}
    let b ← allocateNeed (.ready (.atom 2, 1))
    pure (a, b) : EvalM (Nat × Nat)).runState EvalState.empty with
  | (.ok (0, 0), _) => true
  | _ => false

-- Same heap size does not preserve original suspension identity.
#guard match (NeedDemand.step (fun _ _ _ => do
    modify fun s => {s with needs := #[{suspension := .ready (.atom 99, 1)}]}
    pure (.atom 1, 1)) productionPlanRoute (fun _ => throw Error.badArity) 0).runState oneExpr with
  | (.ok (.atom 1, 1), s) =>
    match s.needs[0]? with
    | some (NeedCell.mk (.ready (.atom 99, 1)) (.completed (.ok (.atom 1, 1))) _ _ _ _ _ _ _) => true
    | _ => false
  | _ => false

-- An unchecked reference beyond a collector's prefix is not made valid by allocation.
#guard match (allocateNeed (.collector [99])).runState EvalState.empty with
  | (.ok 0, s) => s.needs.size == 1 && s.needs[99]?.isNone
  | _ => false

-- Production nested/empty list materialization retains aliases and one-value result count.
#guard match (demandNeed 2).runState {needs := #[
    {suspension := .ready (.sequenceValue [], 0)},
    {suspension := .ready (.listValue [], 1)},
    {suspension := .collector [0, 1, 0]}]} with
  | (.ok (.listValue [.sequenceValue [], .listValue [], .sequenceValue []], 1), _) => true
  | _ => false

end KatLang.NeedControlGuards

/-! ## Projection (META-S3-0a): the production `projectNeedCallable` runs `NeedProjection.step`.
The partial driver is opaque to the kernel, so these executable guards witness its wiring
to the total shell whose laws are `KatLang.NeedControl.Projection`. -/
namespace KatLang.NeedControlGuards.Projection

-- An active projection: re-entry is `demandCycle` and leaves the marker in place.
def activeState : EvalState :=
  { needs := #[{ suspension := .expression (.num 5) EvalCtx.empty [], callable := .projecting }] }
#guard match (projectNeedCallable 0).runState activeState with
  | (.error .demandCycle, s) => (s.needs[0]? matches some (NeedCell.mk _ .suspended .projecting _ _ _ _ _ _))
  | _ => false

-- A completed failure is sticky: returned unchanged, nothing recomputed.
def failedState : EvalState :=
  { needs := #[{ suspension := .expression (.num 5) EvalCtx.empty [], callable := .projected (.error .divByZero) }] }
#guard match (projectNeedCallable 0).runState failedState with
  | (.error .divByZero, s) => (s.needs[0]? matches some (NeedCell.mk _ .suspended (.projected (.error .divByZero)) _ _ _ _ _ _))
  | _ => false

-- A computed value has no identity: SUCCESSFUL absence, published, VALUE still suspended.
def numberState : EvalState := { needs := #[{ suspension := .expression (.num 5) EvalCtx.empty [] }] }
#guard match (projectNeedCallable 0).runState numberState with
  | (.ok none, s) => (s.needs[0]? matches some (NeedCell.mk _ .suspended (.projected (.ok none)) _ _ _ _ _ _))
  | _ => false

-- A resolution failure that is not an absence report (`isLiftableArgResolutionError`) is the
-- projection's ordinary FAILURE: published, and returned again by a later projection.
def unknownState : EvalState :=
  { needs := #[{ suspension := .expression (.resolve "missing") EvalCtx.empty [] }] }
#guard match (do
    let first ← evalAttempt (projectNeedCallable 0)
    let second ← evalAttempt (projectNeedCallable 0)
    pure (first, second)).runState unknownState with
  | (.ok (.error (.unknownName "missing"), .error (.unknownName "missing")), s) =>
    (s.needs[0]? matches some (NeedCell.mk _ .suspended (.projected (.error (.unknownName "missing"))) _ _ _ _ _ _))
  | _ => false

-- A computation re-entering its own cell gets `demandCycle`, which the outer projection
-- publishes as the cell's sticky outcome (`self_reentry_publishes_cycle`).
#guard match (NeedProjection.step (fun _ => projectNeedCallable 0) 0).runState numberState with
  | (.error .demandCycle, s) =>
    (s.needs[0]? matches some (NeedCell.mk _ .suspended (.projected (.error .demandCycle)) _ _ _ _ _ _))
  | _ => false

-- VALUE demand leaves a published CALLABLE outcome alone, and projection leaves VALUE alone.
#guard match (do
    let _ ← projectNeedCallable 0
    demandNeed 0).runState { needs := #[{ suspension := .ready (.atom 3, 1) }] } with
  | (.ok (.atom 3, 1), s) =>
    (s.needs[0]? matches some (NeedCell.mk _ (.completed (.ok (.atom 3, 1))) (.projected (.ok none)) _ _ _ _ _ _))
  | _ => false

end KatLang.NeedControlGuards.Projection
