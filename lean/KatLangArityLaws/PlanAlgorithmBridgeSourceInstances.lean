import KatLangArityLaws.PlanAlgorithmBridgeParameterInstances
import KatLangArityLaws.AddressInvariantProduction

/-!
# The `.Algorithm` bridge APPLIED to genuine source programs (E-18 step 1, M2 — closing instances)

`PlanAlgorithmBridgeInstances` (`Five`, `Missing`, `Reference`) and
`PlanAlgorithmBridgeParameterInstances` (`Parameter`) apply the final bridge theorems on states the
KERNEL can evaluate. The kernel cannot evaluate a run that performs a lexical lookup from a nested
body, binds a parameter pattern or dispatches a clause family: fourteen helpers of `KatLang.lean`
are well-founded definitions whose accessibility proof Lean wraps in `opaqueId`
(`activeDeclaration?`, `NeedPattern.ofParameter`, `NeedPattern.ofClause`,
`propertyOwnerBindingContext`, …). That is a limit of DEFINITIONAL evaluation, not of proof. This
module proves the remaining mandatory instances PROPOSITIONALLY:

* every run equation below is proved by Lean's `cbv` tactic — a proof-producing call-by-value
  evaluator that rewrites with the DEFINING EQUATIONS of the production definitions (the unfolding
  theorems of the well-founded helpers included) and builds an ordinary `Eq` proof term, checked by
  the kernel, from the three standard axioms only. No definition of `KatLang.lean` is replaced,
  twinned or re-implemented; no `native_decide`; the statements mention production definitions only
  (`evalCounted`, `invocationReceiverValue`, `algorithmOfValue`, `ordinaryCall productionPlanRoute`,
  `demandNeed`, …), run by `evalUnbounded` — the production fuel search itself;
* the declaration identities are the ones `runResultM` assigns (`identifyPropertyExpr`): without
  them the evaluator compares declaring scopes through `reprStr`, whose pretty-printer is an opaque
  `partial` definition of Lean core, so those runs are not provable at all (and are not the runs of
  a source program);
* the conclusion of every `bridge` theorem is the final bridge theorem's — `Bridged`, i.e. the
  outcome equation and `HeapInsertion.Inserted` with `Frame` — obtained by APPLYING
  `algorithm_bridge_dot_at` / `algorithm_bridge_grouped_at` (resp. the `_param_at` forms) with every
  premise proved, never by comparing the two final states.

## Source-program reachability

Each instance namespace fixes ONE SOURCE PROGRAM: the shared declarations below and the single
root row `Capture(P)`, where `P` is the written `.Algorithm` invocation and
`Capture(meta op) = op`. Its root context `ctx` is built exactly as `runResultM` builds it
(`identifyPropertyExpr`, `wireToCaller` over the prelude; `enterAlgorithmBody` pushes the root). The
chain from the source evaluation to the comparison state is:

1. `captured` — production's evaluation of the row from `EvalState.empty` returns the reference to
   cell 0 and leaves the state `fin`;
2. `plan_cell` — cell 0 of `fin` is the plan: `P` supplied in the program's own context,
   suspended, no route, no callee (capture is inert);
3. `flight` — from `fin` with the cell marked `evaluating` (the VALUE shell's first write), the
   plan's own first route decision (`NeedPlan.routeOf` over the production classifier) selects the
   `.Algorithm` intrinsic, records it and exits at `x`: THE COMPARISON STATE;
4. `demand_passes` — the production VALUE demand of the plan cell from `fin` (`demandNeed 0`, what
   every VALUE consumer of the reference performs) IS the completion shell over the plan's
   `.algorithm` execution from `x` (`demand_passes_flight`, a symbolic law over
   `NeedDemand.step` and `NeedPlan.execute`).

So `x` is not a hand-built heap: it is the state at which the genuine demand of the genuinely
supplied plan executes its recorded route. The bridge then compares, from `x`, the plan's ordinary
call on that route with production's ordinary evaluation of the same written source.

## The instances

Both written forms each (`N` the dot form `t.Algorithm(args)`, `NG` the grouped form
`(t.Algorithm)(args)`). `Control` is in this module; the others are in the companion modules
`PlanAlgorithmBridgeSourceReceivers` (`CapturedCall`, `Alias`), `PlanAlgorithmBridgeSourceOutcomes`
(`Failure`, `AddressBearing`), `PlanAlgorithmBridgeSourceEffects` (`Effectful`) and
`PlanAlgorithmBridgeSourceAncestor` (`Ancestor`), which import this one. In each namespace ONE
theorem `facts` holds every evaluated fact — one proof-producing evaluation, so the runs are
shared between the facts — and the named theorems are its projections; the theorems that are not
evaluations (`flight`, `demand_passes`, `inv_x`, `not_self`, `bridge`, …) are ordinary proofs over
them.

| namespace | source `P` | what it exhibits |
| --- | --- | --- |
| `Control` | `R.Algorithm(0)` | THE MANDATORY NON-SELF-OBSERVING POSITIVE CONTROL: the receiver read returns the reference `R = Capture(F(0))` holds; value 0 |
| `Failure` | `R.Algorithm(1)` | a structured failure of the tail (`noMatchingBranch "F"`), equal on both sides |
| `CapturedCall` | `Capture(F(0)).Algorithm(0)` | a genuine captured-reference receiver: the read itself captures, past the insertion |
| `Alias` | `RA.Algorithm(0)`, `RA = R` | an alias receiver |
| `Effectful` | `Both(tick(), R).Algorithm(0)` | an effectful receiver, demanded twice, evaluated once: `tick()` counted once on each side |
| `AddressBearing` | `Capture(Mk(1)).Algorithm(2)` | an address-bearing result: production's reference shifted by the two inserted cells |
| `Ancestor` | `r.Algorithm(0)` inside `Inner` of `PO(r)` | a CAPTURED-ANCESTOR PARAMETER receiver: one inserted cell, the parameter's own cell the receiver cell |

`Control.not_self` (and its siblings) prove that the hostile value of the old universal premise —
the plan cell's own reference — is not the receiver's result: it has no tail entry. The
self-observation witnesses stay negative controls (`PlanAlgorithmBridgeInstances.Reference`,
`PlanAlgorithmBridgeGuards.tailContractSelfReferenceDiffers`, the M0 witness).

## A boundary of provability

The property cache's keys and the alias-cell keys are built with `reprStr`, whose pretty-printer
is an opaque `partial` definition of Lean core. A run that compares two such keys built from
DIFFERENT scopes has an outcome no kernel proof can decide. The instance programs make no such
comparison (at most one cached property is read per run; `Ancestor` binds its parameter to a
written call, not to a property of another owner). The bridge theorems have no such restriction.
-/

open KatLang KatLang.CallPlan KatLang.EvaluatorCore KatLang.PlanRouteBridge KatLang.HeapInsertion
open KatLang.PlanAlgorithmBridge KatLang.PlanAlgorithmBridgeInstances
open KatLang.AddressInvariant (Inv empty_inv CallPre production_sound_all)
open KatLang.HeapAddressValidity (ValidCtx)

namespace KatLang.PlanAlgorithmBridgeInstances.Source

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option cbv.maxSteps 20000000

/-! ## The source program -/

def metaParam (name : Ident) : CallableParameter := { name := name, kind := .metaRef }
def callN (f : Ident) (args : List Expr) : Expr := .call (.resolve f) args
def capture (e : Expr) : Expr := callN "Capture" [e]
def tickE : Expr := .call (.resolve "tick") []
def R : Expr := .resolve "R"
def fb : Expr := .resolve "Algorithm"
def add (a b : Expr) : Expr := .binary .add a b

/-- `Capture(meta op) = op`; `F(0) = 0`; `R = Capture(F(0))`; `RA = R` (a transparent reference);
    `Inc(x) = x + 1`; `Mk(t) = Capture(Inc(t))`; `Both(a, b) = if(a + a > 0, b, b)`;
    `PO(r) = { Inner = Capture(r.Algorithm(0)) ⏎ Inner }` and `POG` with the grouped form
    `(r.Algorithm)(0)`: the plan is written in the nested body `Inner`, whose parameter `r` is its
    ANCESTOR's. -/
def decls : List (Ident × Algorithm) :=
  [("Capture", algWithParameters [metaParam "op"] [] [] [.param "op"]),
   ("F", .conditional none [] [⟨.litInt 0, alg [] [] [] [.num 0]⟩]),
   ("R", alg [] [] [] [capture (callN "F" [.num 0])]),
   ("RA", .alias none [] [] (.resolve "R")),
   ("Inc", alg ["x"] [] [] [add (.param "x") (.num 1)]),
   ("Mk", alg ["t"] [] [] [capture (callN "Inc" [.param "t"])]),
   ("Both", alg ["a", "b"] [] []
      [.call (.resolve "if") [.compare .gt (add (.param "a") (.param "a")) (.num 0), .param "b", .param "b"]]),
   ("PO", alg ["r"] []
      [{ name := "Inner", isPublic := false, exposure := .localCapturedAncestorParams ["r"],
         alg := alg [] [] [] [capture (.dotMember (.param "r") "Algorithm" fb (some [.num 0]))] }]
      [.resolve "Inner"]),
   ("POG", alg ["r"] []
      [{ name := "Inner", isPublic := false, exposure := .localCapturedAncestorParams ["r"],
         alg := alg [] [] [] [capture (.call (.dotMember (.param "r") "Algorithm" fb none) [.num 0])] }]
      [.resolve "Inner"])]

/-- The source program with the given root rows. -/
def program (rows : List Expr) : Expr := .algorithmExpr (algPrivate [] [] decls rows)

/-- The program's root algorithm with the declaration identities `runResultM` assigns. -/
def rootOf (rows : List Expr) : Algorithm :=
  match (identifyPropertyExpr (program rows)).run' 0 with
  | .algorithmExpr a => a
  | _ => alg [] [] [] []

def base : EvalCtx := { callStack := [preludeAlg] }

/-- The context a program's root rows are evaluated in: the identified root, wired to the prelude
    and pushed — `runResultM`'s `wireToCaller` and the root's `enterAlgorithmBody`. -/
def ctxOf (rows : List Expr) : EvalCtx := base.push (wireToCaller base (rootOf rows))

/-! ## General lemmas -/

theorem validCtx_nil (h : Array NeedCell) (ctx : EvalCtx) (hne : ctx.needEnv = []) : ValidCtx h ctx := by
  intro p m
  rw [hne] at m
  cases m

theorem validCtx_of_all {h : Array NeedCell} {ctx : EvalCtx}
    (hall : ctx.needEnv.all (fun p => decide (p.2 < h.size)) = true) : ValidCtx h ctx := by
  intro p m
  exact of_decide_eq_true (List.all_eq_true.mp hall p m)

/-- The address invariant holds after production's evaluation of a row from the empty state. -/
theorem inv_row (row : Expr) (ctx : EvalCtx) (hv : ValidCtx EvalState.empty.needs ctx) :
    Inv ((evalCounted row ctx []).runState EvalState.empty).2 :=
  (production_sound_all (.evalCounted row ctx []) EvalState.empty empty_inv ⟨hv, fun _ m => nomatch m⟩).1

theorem inv_evaluating {s : EvalState} (vs : Inv s) (a : Nat) : Inv (withState a .evaluating s) :=
  KatLang.AddressInvariant.inv_modify vs a _ (fun c hc =>
    ⟨rfl, ⟨(vs.cells a c hc).susp, trivial, (vs.cells a c hc).plan, (vs.cells a c hc).callee,
      (vs.cells a c hc).receiver⟩⟩)

theorem inv_routed {s : EvalState} (vs : Inv s) (a : Nat) : Inv (withRoute a .algorithm s) :=
  KatLang.AddressInvariant.inv_modify vs a _ (fun c hc =>
    ⟨rfl, ⟨(vs.cells a c hc).susp, (vs.cells a c hc).state, (vs.cells a c hc).plan, (vs.cells a c hc).callee,
      (vs.cells a c hc).receiver⟩⟩)

/-- The address invariant at a flight: after the VALUE shell's mark, the route decision's
    production probe `c`, and the route record. -/
theorem inv_flight_of_probe {s : EvalState} (vs : Inv s) (a : Nat) (c : EvalCall) {r : c.Ret} {t : EvalState}
    (hrun : (evalUnbounded c).runState (withState a .evaluating s) = (.ok r, t))
    (hpre : CallPre c (withState a .evaluating s).needs) : Inv (withRoute a .algorithm t) := by
  have h := (production_sound_all c (withState a .evaluating s) (inv_evaluating vs a) hpre).1
  rw [hrun] at h
  exact inv_routed h a

/-- The innermost payload of a failure. -/
def innermost : Error → Error
  | .withContext _ inner => innermost inner
  | e => e

def innermost? {α : Type} (o : Except Error α) : Option Error :=
  match o with
  | .error e => some (innermost e)
  | .ok _ => none

/-- **THE VALUE DEMAND OF A SUSPENDED PLAN PASSES THROUGH ITS FLIGHT.** For a suspended cell `a`
    whose written source is a supported invocation of shape `shape`: when the plan's first route
    decision, run from the state where the VALUE shell marked the cell `evaluating`, exits at `x`
    with a callable route `r`, the production VALUE demand of the cell is the completion shell over
    the plan's execution along `r` FROM `x` — its outcome returned and memoized in the cell. -/
theorem demand_passes_flight (a : Nat) (s x : EvalState) (cell : NeedCell) (e : Expr) (c : EvalCtx) (v : ValEnv)
    (shape : NeedPlan.CallShape) (r : PlanRoute)
    (hc : s.needs[a]? = some cell) (hs : cell.state = .suspended) (hsus : cell.suspension = .expression e c v)
    (hshape : NeedPlan.callShape? e c v = some shape)
    (hflight : (withCtx shape.ctxMsg (NeedPlan.routeOf productionPlanRoute.classify a shape)).runState
      (withState a .evaluating s) = (.ok r, x))
    (hr : r ≠ .intrinsic)
    (hcomplete : ((NeedPlan.executeAlong productionPlanRoute a shape r).runState x).1.isIncomplete = false) :
    (demandNeed a).runState s =
      (let res := (NeedPlan.executeAlong productionPlanRoute a shape r).runState x
       (res.1, withState a (.completed res.1) res.2)) := by
  rw [production_demand]
  have hexec : (NeedPlan.execute productionPlanRoute a shape).runState (withState a .evaluating s) =
      (NeedPlan.executeAlong productionPlanRoute a shape r).runState x := by
    simp only [NeedPlan.execute, bind_run, hflight]
    all_goals (cases r <;> first | rfl | exact absurd rfl hr)
  have hcallable : ((withCtx shape.ctxMsg (NeedPlan.routeOf productionPlanRoute.classify a shape)).runState
      (withState a .evaluating s)).1 ≠ .ok .intrinsic := by
    rw [hflight]
    intro h
    exact hr (Except.ok.inj h)
  have hv := suspended_call_is_plan (evalSuppliedAt a) productionPlanRoute demandNeedRecursive a e c v shape hshape
    (withState a .evaluating s) hcallable
  rw [← hsus, hexec] at hv
  generalize hres : (NeedPlan.executeAlong productionPlanRoute a shape r).runState x = res at hcomplete hv ⊢
  rcases res with ⟨o, t⟩
  exact KatLang.NeedControl.Memo.suspended_retains_state _ _ _ a s t cell o hc hs hv hcomplete

/-! ## `Control`: the dot form -/

namespace Control
/-- `R.Algorithm(0)` — THE MANDATORY POSITIVE CONTROL (`R = Capture(F(0))`, `F(0) = 0`): the receiver read returns the reference `R` captured, the tail is a fresh `F(0)`: the value 0. -/
def recv : Expr := R
def args : OutputBundle := [.num 0]
def edge : Expr := .dotMember recv "Algorithm" fb none
/-- The plan's written source. -/
def src : Expr := .dotMember recv "Algorithm" fb (some args)
/-- THE SOURCE PROGRAM's one row: `Capture(…)`. -/
def row : Expr := capture src
/-- The root context of the source program, as `runResultM` wires it. -/
def ctx : EvalCtx := ctxOf [row]
def shape : NeedPlan.CallShape := dotShape recv fb args ctx []

/-- The state the GENUINE evaluation of the row leaves, from the empty state. -/
def fin : EvalState := ((evalCounted row ctx []).runState EvalState.empty).2

/-- The state the VALUE shell runs the plan from: the cell marked `evaluating`. -/
def entry : EvalState := withState 0 .evaluating fin
def entryCell : NeedCell := { suspension := .expression src ctx [], state := .evaluating }
def ca : NeedCell := { suspension := .expression src ctx [], state := .evaluating, route := some .algorithm }
/-- The receiver's identity as production's probe answers it. -/
def alg? : Option Algorithm :=
  match ((resolveDotReceiver? recv ctx).runState entry).1 with
  | .ok a => a
  | .error _ => none
def probed : EvalState := ((resolveDotReceiver? recv ctx).runState entry).2
/-- THE COMPARISON STATE: the plan's flight. -/
def x : EvalState := withRoute 0 .algorithm probed
def recvOut : Except Error Result := ((invocationReceiverValue recv ctx []).runState x).1
/-- Production's state after the receiver read: the tail entry. -/
def x₄ : EvalState := ((invocationReceiverValue recv ctx []).runState x).2
/-- The receiver's VALUE (computed by the evaluator). -/
def recvVal : Result := match recvOut with | .ok v => v | .error _ => .atom 0
/-- The cell the receiver's reference names (computed by the evaluator). -/
def refAddr : Nat := match recvVal with | .callRef a => a | _ => 0
abbrev ιe : Insertion := planInsertion x.needs.size 0 edge ctx [] .evaluating
def tailOut : Except Error CountedResult := ((algorithmOfValue recvVal (some args) ctx []).runState x₄).1
def x₅ : EvalState := ((algorithmOfValue recvVal (some args) ctx []).runState x₄).2
abbrev ιd : Insertion :=
  planInsertion x.needs.size 0 edge ctx [] (.completed (receiverMemo ⟨x.needs.size, 2⟩ (.ok recvVal)))
/-- EVERY evaluated fact of this instance, in ONE proof-producing evaluation (`cbv`); the theorems
    below are its projections. -/
theorem facts :
    ((evalCounted row ctx []).runState EvalState.empty = (.ok (.callRef 0, 1), fin)) ∧
    ((evalProgramOutput (wireToCaller base (rootOf [row])) base []).runState EvalState.empty = (.ok (.callRef 0), fin)) ∧
    (fin.needs[0]? = some { suspension := .expression src ctx [] }) ∧
    (entry.needs[0]? = some entryCell) ∧
    ((resolveDotReceiver? recv ctx).runState entry = (.ok alg?, probed)) ∧
    (selectDotEdge ctx recv "Algorithm" alg? = .ok (.miss .algorithm)) ∧
    (x.needs[0]? = some ca) ∧
    ((probed.needs[0]?).bind NeedCell.route = none) ∧
    ((resolveDotReceiver? recv ctx).runState x = (.ok alg?, x)) ∧
    (((NeedPlan.executeAlong productionPlanRoute 0 shape .algorithm).runState x).1.isIncomplete = false) ∧
    (ctx.needEnv = []) ∧
    (recvOut = .ok recvVal) ∧
    (recvVal = .callRef refAddr) ∧
    ((invocationReceiverValue recv ctx []).runState (embed ιe x) = (shiftExcept (shiftResult ⟨x.needs.size, 2⟩) recvOut, embed ιe x₄)) ∧
    (Unrecorded 0 x₄) ∧
    (planCalleesB x₄ = true) ∧
    ((algorithmOfValue (shiftResult ⟨x.needs.size, 2⟩ recvVal) (some args) ctx []).runState (embed ιd x₄) = (shiftExcept (shiftCounted ⟨x.needs.size, 2⟩) tailOut, embed ιd x₅)) ∧
    (Unrecorded 0 x₅) ∧
    (decide (refAddr ≠ 0) = true) ∧
    (completeB ((evalCounted src ctx []).runState x).1 = true) ∧
    (((ordinaryCall productionPlanRoute 0 shape .algorithm).runState x).2.needs.size = ((reCountValueBoundary <$> evalCounted src ctx []).runState x).2.needs.size + 2) ∧
    (((ordinaryCall productionPlanRoute 0 shape .algorithm).runState x).1 = .ok (.atom 0, 1) ∧ ((evalCounted src ctx []).runState x).1 = .ok (.atom 0, 1)) := by
  cbv
  all_goals (repeat' (first | rfl | constructor))


/-- **REACHED (1).** Production's evaluation of the source row from the empty state captures the
    written invocation: it returns the reference to cell 0. -/
theorem captured : (evalCounted row ctx []).runState EvalState.empty = (.ok (.callRef 0, 1), fin) :=
  facts.1

/-- The same evaluation as `runResultM` enters it: the program root's zero-argument demand over the
    prelude context, from the empty state — the reference, and the same state `fin`. (`runResultM`
    then refuses to export a reference: a reference never leaves its run.) -/
theorem program_run :
    (evalProgramOutput (wireToCaller base (rootOf [row])) base []).runState EvalState.empty =
      (.ok (.callRef 0), fin) :=
  facts.2.1

/-- **REACHED (2).** Cell 0 of that state is THE PLAN: the written source, supplied in the program's
    root context, suspended, with no route and no callee recorded. -/
theorem plan_cell : fin.needs[0]? = some { suspension := .expression src ctx [] } :=
  facts.2.2.1

theorem entry_cell : entry.needs[0]? = some entryCell :=
  facts.2.2.2.1

theorem probe_entry : (resolveDotReceiver? recv ctx).runState entry = (.ok alg?, probed) :=
  facts.2.2.2.2.1

/-- Production's own route selection: the `.Algorithm` intrinsic (a structural miss). -/
theorem miss : selectDotEdge ctx recv "Algorithm" alg? = .ok (.miss .algorithm) :=
  facts.2.2.2.2.2.1

theorem x_cell : x.needs[0]? = some ca :=
  facts.2.2.2.2.2.2.1

theorem route_free : (probed.needs[0]?).bind NeedCell.route = none :=
  facts.2.2.2.2.2.2.2.1

/-- **REACHED (3).** `x` is the flight of the plan cell: from the state where the VALUE shell marked
    it `evaluating`, the plan's FIRST route decision selects the `.Algorithm` intrinsic and records it. -/
theorem flight :
    (withCtx shape.ctxMsg (NeedPlan.routeOf productionPlanRoute.classify 0 shape)).runState entry =
      (.ok .algorithm, x) :=
  flight_dot 0 recv fb args ctx [] entry probed entryCell alg? entry_cell rfl probe_entry miss route_free
theorem probe_x : (resolveDotReceiver? recv ctx).runState x = (.ok alg?, x) :=
  facts.2.2.2.2.2.2.2.2.1

theorem demand_done :
    ((NeedPlan.executeAlong productionPlanRoute 0 shape .algorithm).runState x).1.isIncomplete = false :=
  facts.2.2.2.2.2.2.2.2.2.1

/-- **REACHED (4).** The production VALUE demand of the plan cell from the genuine state `fin` IS the
    completion shell over the plan's `.algorithm` execution from the flight `x`. -/
theorem demand_passes :
    (demandNeed 0).runState fin =
      (let res := (NeedPlan.executeAlong productionPlanRoute 0 shape .algorithm).runState x
       (res.1, withState 0 (.completed res.1) res.2)) :=
  demand_passes_flight 0 fin x _ src ctx [] shape .algorithm plan_cell rfl rfl rfl flight nofun demand_done

theorem ctx_needEnv : ctx.needEnv = [] :=
  facts.2.2.2.2.2.2.2.2.2.2.1

theorem ctx_valid (h : Array NeedCell) : ValidCtx h ctx := validCtx_nil h ctx ctx_needEnv
theorem inv_fin : Inv fin := inv_row row ctx (ctx_valid _)
theorem inv_x : Inv x := inv_flight_of_probe inv_fin 0 (.resolveDotReceiver? recv ctx) probe_entry (ctx_valid _)

theorem recv_not_param : ∀ p, recv ≠ .param p := by intro p h; cases h

/-! ### Production's receiver read, and the plan side's -/

theorem recv_ok : recvOut = .ok recvVal :=
  facts.2.2.2.2.2.2.2.2.2.2.2.1

/-- **The actual receiver read returns a call reference.** -/
theorem recv_reference : recvVal = .callRef refAddr :=
  facts.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem read_x : (invocationReceiverValue recv ctx []).runState x = (recvOut, x₄) := rfl
/-- THE PLAN SIDE's receiver read, from the plan-side state with the receiver cell `evaluating`:
    production's outcome shifted, production's exit state under the insertion. -/
theorem read_plan : (invocationReceiverValue recv ctx []).runState (embed ιe x) =
    (shiftExcept (shiftResult ⟨x.needs.size, 2⟩) recvOut, embed ιe x₄) :=
  facts.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem read_unrecorded : Unrecorded 0 x₄ :=
  facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem read_callees : planCalleesB x₄ = true :=
  facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-! ### The admissible tail entry, production's tail and the plan side's -/

theorem tail_x : (algorithmOfValue recvVal (some args) ctx []).runState x₄ = (tailOut, x₅) := rfl
theorem tail_plan :
    (algorithmOfValue (shiftResult ⟨x.needs.size, 2⟩ recvVal) (some args) ctx []).runState (embed ιd x₄) =
      (shiftExcept (shiftCounted ⟨x.needs.size, 2⟩) tailOut, embed ιd x₅) :=
  facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem tail_unrecorded : Unrecorded 0 x₅ :=
  facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- The plan cell's own reference is NOT the receiver's result: the hostile value has no tail entry. -/
theorem ref_ne : refAddr ≠ 0 :=
  of_decide_eq_true facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem not_self : recvVal ≠ .callRef 0 := by
  rw [recv_reference]
  intro h
  exact ref_ne (Result.callRef.inj h)

theorem production_done : completeB ((evalCounted src ctx []).runState x).1 = true :=
  facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem production_completes : ProductionCompletes (evalCounted src ctx []) x := complete_of_B production_done

/-- **`algorithm_bridge_dot_at` APPLIED** at the plan's flight, every premise proved above. -/
theorem bridge :
    Bridged (finalInsertion x 0 shape recv)
      ((ordinaryCall productionPlanRoute 0 shape .algorithm).runState x)
      ((reCountValueBoundary <$> evalCounted src ctx []).runState x) :=
  algorithm_bridge_dot_at 0 recv fb args ctx [] x x alg? ca recv_not_param x_cell rfl rfl rfl probe_x miss
    inv_x recvOut x₄ read_x read_plan read_unrecorded
    (fun v hv => by
      have hv' : v = recvVal := by
        have h := recv_ok.symm.trans hv
        exact (Except.ok.inj h).symm
      subst hv'
      exact ⟨planCallees_of_B read_callees, tailOut, x₅, tail_x, tail_plan, tail_unrecorded⟩)
    production_completes

/-- The complete relation: the plan's final state is production's with the link and the completed
    receiver cell inserted, and production's final state keeps `Frame`. -/
theorem inserted :
    Inserted (finalInsertion x 0 shape recv)
      ((ordinaryCall productionPlanRoute 0 shape .algorithm).runState x).2
      ((reCountValueBoundary <$> evalCounted src ctx []).runState x).2 := bridge.2

/-- The plan side allocated exactly the two inserted cells more than production. -/
theorem two_cells :
    ((ordinaryCall productionPlanRoute 0 shape .algorithm).runState x).2.needs.size =
      ((reCountValueBoundary <$> evalCounted src ctx []).runState x).2.needs.size + 2 :=
  facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- Both sides return the value 0. -/
theorem value :
    ((ordinaryCall productionPlanRoute 0 shape .algorithm).runState x).1 = .ok (.atom 0, 1) ∧
    ((evalCounted src ctx []).runState x).1 = .ok (.atom 0, 1) :=
  facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

end Control

/-! ## `ControlG`: the grouped form `(…​.Algorithm)(…)` -/

namespace ControlG
/-- `R.Algorithm(0)` — THE MANDATORY POSITIVE CONTROL (`R = Capture(F(0))`, `F(0) = 0`): the receiver read returns the reference `R` captured, the tail is a fresh `F(0)`: the value 0. -/
def recv : Expr := R
def args : OutputBundle := [.num 0]
def edge : Expr := .dotMember recv "Algorithm" fb none
/-- The plan's written source. -/
def src : Expr := .call edge args
/-- THE SOURCE PROGRAM's one row: `Capture(…)`. -/
def row : Expr := capture src
/-- The root context of the source program, as `runResultM` wires it. -/
def ctx : EvalCtx := ctxOf [row]
def shape : NeedPlan.CallShape := groupedShape recv fb args ctx []

/-- The state the GENUINE evaluation of the row leaves, from the empty state. -/
def fin : EvalState := ((evalCounted row ctx []).runState EvalState.empty).2

/-- The state the VALUE shell runs the plan from: the cell marked `evaluating`. -/
def entry : EvalState := withState 0 .evaluating fin
def entryCell : NeedCell := { suspension := .expression src ctx [], state := .evaluating }
def ca : NeedCell := { suspension := .expression src ctx [], state := .evaluating, route := some .algorithm }
def probed : EvalState := ((algorithmIntrinsicRoute recv ctx).runState entry).2
/-- THE COMPARISON STATE: the plan's flight. -/
def x : EvalState := withRoute 0 .algorithm probed
def recvOut : Except Error Result := ((invocationReceiverValue recv ctx []).runState x).1
/-- Production's state after the receiver read: the tail entry. -/
def x₄ : EvalState := ((invocationReceiverValue recv ctx []).runState x).2
/-- The receiver's VALUE (computed by the evaluator). -/
def recvVal : Result := match recvOut with | .ok v => v | .error _ => .atom 0
/-- The cell the receiver's reference names (computed by the evaluator). -/
def refAddr : Nat := match recvVal with | .callRef a => a | _ => 0
abbrev ιe : Insertion := planInsertion x.needs.size 0 edge ctx [] .evaluating
def tailOut : Except Error CountedResult := ((algorithmOfValue recvVal (some args) ctx []).runState x₄).1
def x₅ : EvalState := ((algorithmOfValue recvVal (some args) ctx []).runState x₄).2
abbrev ιd : Insertion :=
  planInsertion x.needs.size 0 edge ctx [] (.completed (receiverMemo ⟨x.needs.size, 2⟩ (.ok recvVal)))
/-- EVERY evaluated fact of this instance, in ONE proof-producing evaluation (`cbv`); the theorems
    below are its projections. -/
theorem facts :
    ((evalCounted row ctx []).runState EvalState.empty = (.ok (.callRef 0, 1), fin)) ∧
    ((evalProgramOutput (wireToCaller base (rootOf [row])) base []).runState EvalState.empty = (.ok (.callRef 0), fin)) ∧
    (fin.needs[0]? = some { suspension := .expression src ctx [] }) ∧
    (entry.needs[0]? = some entryCell) ∧
    ((algorithmIntrinsicRoute recv ctx).runState entry = (.ok true, probed)) ∧
    (x.needs[0]? = some ca) ∧
    ((probed.needs[0]?).bind NeedCell.route = none) ∧
    ((withCtx (CtxMsg.call edge) (algorithmIntrinsicRoute recv ctx)).runState x = (.ok true, x)) ∧
    (((NeedPlan.executeAlong productionPlanRoute 0 shape .algorithm).runState x).1.isIncomplete = false) ∧
    (ctx.needEnv = []) ∧
    (recvOut = .ok recvVal) ∧
    (recvVal = .callRef refAddr) ∧
    ((invocationReceiverValue recv ctx []).runState (embed ιe x) = (shiftExcept (shiftResult ⟨x.needs.size, 2⟩) recvOut, embed ιe x₄)) ∧
    (Unrecorded 0 x₄) ∧
    (planCalleesB x₄ = true) ∧
    ((algorithmOfValue (shiftResult ⟨x.needs.size, 2⟩ recvVal) (some args) ctx []).runState (embed ιd x₄) = (shiftExcept (shiftCounted ⟨x.needs.size, 2⟩) tailOut, embed ιd x₅)) ∧
    (Unrecorded 0 x₅) ∧
    (decide (refAddr ≠ 0) = true) ∧
    (completeB ((evalCallCountedExpr edge args ctx []).runState x).1 = true) ∧
    (((ordinaryCall productionPlanRoute 0 shape .algorithm).runState x).2.needs.size = ((reCountValueBoundary <$> evalCallCountedExpr edge args ctx []).runState x).2.needs.size + 2) ∧
    (((ordinaryCall productionPlanRoute 0 shape .algorithm).runState x).1 = .ok (.atom 0, 1) ∧ ((evalCallCountedExpr edge args ctx []).runState x).1 = .ok (.atom 0, 1)) := by
  cbv
  all_goals (repeat' (first | rfl | constructor))


/-- **REACHED (1).** Production's evaluation of the source row from the empty state captures the
    written invocation: it returns the reference to cell 0. -/
theorem captured : (evalCounted row ctx []).runState EvalState.empty = (.ok (.callRef 0, 1), fin) :=
  facts.1

/-- The same evaluation as `runResultM` enters it: the program root's zero-argument demand over the
    prelude context, from the empty state — the reference, and the same state `fin`. (`runResultM`
    then refuses to export a reference: a reference never leaves its run.) -/
theorem program_run :
    (evalProgramOutput (wireToCaller base (rootOf [row])) base []).runState EvalState.empty =
      (.ok (.callRef 0), fin) :=
  facts.2.1

/-- **REACHED (2).** Cell 0 of that state is THE PLAN: the written source, supplied in the program's
    root context, suspended, with no route and no callee recorded. -/
theorem plan_cell : fin.needs[0]? = some { suspension := .expression src ctx [] } :=
  facts.2.2.1

theorem entry_cell : entry.needs[0]? = some entryCell :=
  facts.2.2.2.1

/-- Production's own route decision for the edge: the `.Algorithm` intrinsic. -/
theorem decided_entry : (algorithmIntrinsicRoute recv ctx).runState entry = (.ok true, probed) :=
  facts.2.2.2.2.1

theorem x_cell : x.needs[0]? = some ca :=
  facts.2.2.2.2.2.1

theorem route_free : (probed.needs[0]?).bind NeedCell.route = none :=
  facts.2.2.2.2.2.2.1

/-- **REACHED (3).** `x` is the flight of the grouped plan cell: its first route decision is the
    edge's `.Algorithm` route fact. -/
theorem flight :
    (withCtx shape.ctxMsg (NeedPlan.routeOf productionPlanRoute.classify 0 shape)).runState entry =
      (.ok .algorithm, x) :=
  flight_grouped 0 recv fb args ctx [] entry probed entryCell entry_cell rfl decided_entry route_free
/-- Production's route decision is SETTLED at the flight: it answers `true` and changes nothing. -/
theorem settled : (withCtx (CtxMsg.call edge) (algorithmIntrinsicRoute recv ctx)).runState x = (.ok true, x) :=
  facts.2.2.2.2.2.2.2.1

theorem demand_done :
    ((NeedPlan.executeAlong productionPlanRoute 0 shape .algorithm).runState x).1.isIncomplete = false :=
  facts.2.2.2.2.2.2.2.2.1

/-- **REACHED (4).** The production VALUE demand of the plan cell from the genuine state `fin` IS the
    completion shell over the plan's `.algorithm` execution from the flight `x`. -/
theorem demand_passes :
    (demandNeed 0).runState fin =
      (let res := (NeedPlan.executeAlong productionPlanRoute 0 shape .algorithm).runState x
       (res.1, withState 0 (.completed res.1) res.2)) :=
  demand_passes_flight 0 fin x _ src ctx [] shape .algorithm plan_cell rfl rfl rfl flight nofun demand_done

theorem ctx_needEnv : ctx.needEnv = [] :=
  facts.2.2.2.2.2.2.2.2.2.1

theorem ctx_valid (h : Array NeedCell) : ValidCtx h ctx := validCtx_nil h ctx ctx_needEnv
theorem inv_fin : Inv fin := inv_row row ctx (ctx_valid _)
theorem inv_x : Inv x := inv_flight_of_probe inv_fin 0 (.algorithmIntrinsicRoute recv ctx) decided_entry (ctx_valid _)

theorem recv_not_param : ∀ p, recv ≠ .param p := by intro p h; cases h

/-! ### Production's receiver read, and the plan side's -/

theorem recv_ok : recvOut = .ok recvVal :=
  facts.2.2.2.2.2.2.2.2.2.2.1

/-- **The actual receiver read returns a call reference.** -/
theorem recv_reference : recvVal = .callRef refAddr :=
  facts.2.2.2.2.2.2.2.2.2.2.2.1

theorem read_x : (invocationReceiverValue recv ctx []).runState x = (recvOut, x₄) := rfl
/-- THE PLAN SIDE's receiver read, from the plan-side state with the receiver cell `evaluating`:
    production's outcome shifted, production's exit state under the insertion. -/
theorem read_plan : (invocationReceiverValue recv ctx []).runState (embed ιe x) =
    (shiftExcept (shiftResult ⟨x.needs.size, 2⟩) recvOut, embed ιe x₄) :=
  facts.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem read_unrecorded : Unrecorded 0 x₄ :=
  facts.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem read_callees : planCalleesB x₄ = true :=
  facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-! ### The admissible tail entry, production's tail and the plan side's -/

theorem tail_x : (algorithmOfValue recvVal (some args) ctx []).runState x₄ = (tailOut, x₅) := rfl
theorem tail_plan :
    (algorithmOfValue (shiftResult ⟨x.needs.size, 2⟩ recvVal) (some args) ctx []).runState (embed ιd x₄) =
      (shiftExcept (shiftCounted ⟨x.needs.size, 2⟩) tailOut, embed ιd x₅) :=
  facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem tail_unrecorded : Unrecorded 0 x₅ :=
  facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- The plan cell's own reference is NOT the receiver's result: the hostile value has no tail entry. -/
theorem ref_ne : refAddr ≠ 0 :=
  of_decide_eq_true facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem not_self : recvVal ≠ .callRef 0 := by
  rw [recv_reference]
  intro h
  exact ref_ne (Result.callRef.inj h)

theorem production_done : completeB ((evalCallCountedExpr edge args ctx []).runState x).1 = true :=
  facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem production_completes : ProductionCompletes (evalCallCountedExpr edge args ctx []) x := complete_of_B production_done

/-- **`algorithm_bridge_grouped_at` APPLIED** at the plan's flight, every premise proved above. -/
theorem bridge :
    Bridged (finalInsertion x 0 shape recv)
      ((ordinaryCall productionPlanRoute 0 shape .algorithm).runState x)
      ((reCountValueBoundary <$> evalCallCountedExpr edge args ctx []).runState x) :=
  algorithm_bridge_grouped_at 0 recv fb args ctx [] x ca recv_not_param settled x_cell rfl rfl rfl
    inv_x recvOut x₄ read_x read_plan read_unrecorded
    (fun v hv => by
      have hv' : v = recvVal := by
        have h := recv_ok.symm.trans hv
        exact (Except.ok.inj h).symm
      subst hv'
      exact ⟨planCallees_of_B read_callees, tailOut, x₅, tail_x, tail_plan, tail_unrecorded⟩)
    production_completes

/-- The complete relation: the plan's final state is production's with the link and the completed
    receiver cell inserted, and production's final state keeps `Frame`. -/
theorem inserted :
    Inserted (finalInsertion x 0 shape recv)
      ((ordinaryCall productionPlanRoute 0 shape .algorithm).runState x).2
      ((reCountValueBoundary <$> evalCallCountedExpr edge args ctx []).runState x).2 := bridge.2

/-- The plan side allocated exactly the two inserted cells more than production. -/
theorem two_cells :
    ((ordinaryCall productionPlanRoute 0 shape .algorithm).runState x).2.needs.size =
      ((reCountValueBoundary <$> evalCallCountedExpr edge args ctx []).runState x).2.needs.size + 2 :=
  facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- Both sides return the value 0. -/
theorem value :
    ((ordinaryCall productionPlanRoute 0 shape .algorithm).runState x).1 = .ok (.atom 0, 1) ∧
    ((evalCallCountedExpr edge args ctx []).runState x).1 = .ok (.atom 0, 1) :=
  facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

end ControlG

end KatLang.PlanAlgorithmBridgeInstances.Source
