import Lean
import KatLangArityLaws.PlanAlgorithmBridge

open KatLang KatLang.CallPlan KatLang.EvaluatorCore KatLang.PlanRouteBridge KatLang.HeapInsertion
open KatLang.PlanAlgorithmBridge
open KatLang.AddressInvariant (Inv inv_push empty_inv)
open KatLang.FiniteLoop (nested_run ctx_run)

/-!
# The `.Algorithm` bridge APPLIED: kernel-checked instances on concrete reached states (E-18, M2 § 4)

`PlanAlgorithmBridge`'s final theorems are implications. This module APPLIES them: for concrete
states it proves EVERY premise — the flight facts, the address invariant, production's route
selection, both runs of the receiver read and of the tail, the preservation of the plan cell's
unrecorded callee, `PlanCallees`, production's completion — and concludes `Bridged` (the outcome
equation and `HeapInsertion.Inserted`, `Frame` included) by the theorem, not by comparing two
computed states. Standard axioms only; no `native_decide`.

## How a concrete run becomes a kernel fact

A production operation is `evalUnbounded c`: the total core `evalFuel n c` under an unbounded fuel
search, which the kernel cannot run. `prod_of_fuel` turns a COMPLETED core run at an explicit fuel
into the production run (`EvaluatorCore.production_completes_iff`), and the core run at an explicit
fuel is a closed term the kernel evaluates: `kernel_rfl` closes `lhs = rhs` with `Eq.refl lhs`, left
to the kernel's definitional check (as `decide +kernel` does for a decidable proposition).

## What the kernel can evaluate — the boundary of this module

The KERNEL's closed-term reduction stops at well-founded helpers whose accessibility proofs are
behind `opaqueId`, or at opaque printers (`scratch/kernel_probe*.lean` in the earlier evidence).
That is a limit of definitional evaluation, not of proof: the alias receivers, the full
`Capture(meta op)` positive control `R.Algorithm(0)`, effectful memo sharing, an address-bearing
whole-bridge result and a captured-ancestor parameter receiver are proved PROPOSITIONALLY — by
proof-producing evaluation over the same production definitions — in
`PlanAlgorithmBridgeSourceInstances` and its companion modules. This module supplies the
kernel-evaluated instances:

* `Five` — `5.Algorithm(0)` and `(5.Algorithm)(0)`: the receiver read SUCCEEDS with a value that is
  no call reference; the tail is the intrinsic's structured kind rejection. Both written forms,
  each from its plan's flight, itself derived from the supplied state (`flight_*`).
* `Missing` — `Empty.Algorithm(0)` and `(Empty.Algorithm)(0)`: the receiver read FAILS (a nested
  missing output); no tail entry exists, so the tail premises hold vacuously — by proof.
* `Reference` — the TAIL obligations over a call reference to the supplied invocation `Seven()`:
  a success, value 7, with a later callee allocation shifted past TWO inserted cells. This is
  neither a receiver-read proof nor a whole-bridge application.

`PlanAlgorithmBridgeParameterInstances` adds successful WHOLE-bridge applications for both
parameter forms, with a captured Ready adapter in an own-parameter context and ONE inserted cell.
That path is kernel-evaluable; the general parameter (captured-ancestor) and alias scenarios are
in `PlanAlgorithmBridgeSourceAncestor` and `PlanAlgorithmBridgeSourceReceivers`.

The `Five` and `Missing` flight states are built from `EvalState.empty` by supply primitives and
the plan's own route classification (proved, `flight_*`). `Reference` is a separate tail-only
harness with a supplied plan and explicit flight marks; it binds no parameter.
-/

namespace KatLang.PlanAlgorithmBridgeInstances

open Lean Elab Tactic Meta in
/-- Closes `lhs = rhs` with `Eq.refl lhs`, checked by the KERNEL's definitional equality alone (the
    elaborator does not unfold anything). No axiom is used; a false equation is rejected when the
    enclosing declaration is added. -/
elab "kernel_rfl" : tactic => do
  let goal ← getMainGoal
  let t ← instantiateMVars (← goal.getType)
  let some (α, lhs, _) := t.eq? | throwError "kernel_rfl: the goal is not an equality"
  let u ← getLevel α
  goal.assign (mkApp2 (mkConst ``Eq.refl [u]) α lhs)

/-! ## From a completed core run to the production run -/

/-- **A completed core run IS the production run.** -/
theorem prod_of_fuel (m : Nat) (c : EvalCall) (s : EvalState) (r : Except Error c.Ret × EvalState)
    (h : (evalFuel m c).runState s = r) (hc : r.1 ≠ .error .fuelExhausted) :
    (evalUnbounded c).runState s = r :=
  ((production_completes_iff c s r).2 ⟨m, h, (evalFuel_completes_iff m c s).2 (by rw [h]; exact hc)⟩).1

def completeB {α : Type} (o : Except Error α) : Bool :=
  match o with
  | .error .fuelExhausted => false
  | _ => true

theorem complete_of_B {α : Type} {o : Except Error α} (h : completeB o = true) : o ≠ .error .fuelExhausted := by
  intro he
  subst he
  cases h

theorem ok_complete {α : Type} (v : α) : (Except.ok v : Except Error α) ≠ .error .fuelExhausted := nofun

def errorB (e : Error) : Bool :=
  match e with
  | .fuelExhausted => false
  | _ => true

theorem error_complete {α : Type} {e : Error} (h : errorB e = true) :
    (Except.error e : Except Error α) ≠ .error .fuelExhausted := by
  intro he
  injection he with he
  subst he
  cases h

/-! ## The receiver read from its two production steps -/

/-- A subordinate read's outcome: a failure nested (`withNestedMissingOutput`). -/
def nestOutcome (o : Except Error Result) : Except Error Result :=
  match o with
  | .ok v => .ok v
  | .error e => .error e.nestMissingOutput

/-- The invocation receiver read of a VALUE receiver (the probe answers `none`): the receiver's
    ordinary value, a failure nested. -/
theorem irv_value (receiver : Expr) (ctx : EvalCtx) (env : ValEnv) (x x' t : EvalState)
    (o : Except Error Result)
    (hprobe : (resolveDotReceiver? receiver ctx).runState x = (.ok none, x'))
    (heval : (eval receiver ctx env).runState x' = (o, t)) :
    (invocationReceiverValue receiver ctx env).runState x = (nestOutcome o, t) := by
  rw [invocationReceiverValue_eq, bind_run, hprobe]
  show (withNestedMissingOutput (eval receiver ctx env)).runState x' = _
  rw [nested_run, heval]
  cases o <;> rfl

/-- The invocation receiver read of an ALGORITHM receiver (the probe answers `some g`): the
    call-reference intrinsics' receiver read over `g`. -/
theorem irv_reference (receiver : Expr) (ctx : EvalCtx) (env : ValEnv) (x x' t : EvalState) (g : Algorithm)
    (o : Except Error Result)
    (hprobe : (resolveDotReceiver? receiver ctx).runState x = (.ok (some g), x'))
    (href : (referenceReceiverValue receiver g ctx env).runState x' = (o, t)) :
    (invocationReceiverValue receiver ctx env).runState x = (o, t) := by
  rw [invocationReceiverValue_eq, bind_run, hprobe]
  exact href

/-! ## Deciding the two heap facts -/

def planCalleesB (s : EvalState) : Bool :=
  s.needs.toList.all fun cell => cell.callee.isNone || (NeedPlan.ofSuspension? cell.suspension).isSome

theorem planCallees_of_B {s : EvalState} (h : planCalleesB s = true) : PlanCallees s := by
  intro b cell hb hc
  have hmem : cell ∈ s.needs.toList := by
    rw [← Array.getElem?_toList] at hb
    exact List.mem_of_getElem? hb
  have hall := List.all_eq_true.mp h cell hmem
  rw [Bool.or_eq_true] at hall
  rcases hall with h1 | h2
  · cases hcc : cell.callee with
    | none => rw [hcc] at hc; cases hc
    | some c => rw [hcc] at h1; cases h1
  · exact h2

/-- The plan's flight mark and route record keep the address invariant. -/
theorem inv_flight {s : EvalState} (vs : Inv s) (a : Nat) :
    Inv (withRoute a .algorithm (withState a .evaluating s)) := by
  have h1 : Inv (withState a .evaluating s) :=
    KatLang.AddressInvariant.inv_modify vs a _ (fun c hc =>
      ⟨rfl, ⟨(vs.cells a c hc).susp, trivial, (vs.cells a c hc).plan, (vs.cells a c hc).callee,
        (vs.cells a c hc).receiver⟩⟩)
  exact KatLang.AddressInvariant.inv_modify h1 a _ (fun c hc =>
    ⟨rfl, ⟨(h1.cells a c hc).susp, (h1.cells a c hc).state, (h1.cells a c hc).plan, (h1.cells a c hc).callee,
      (h1.cells a c hc).receiver⟩⟩)

/-! ## The plan's flight, from its own classification -/

/-- **The flight of a dot-form plan.** From the state where the VALUE shell marked the plan cell
    `evaluating`, the plan's FIRST route decision runs the receiver probe, selects the `.Algorithm`
    intrinsic and records the route: the flight state is the probe's exit with the route recorded. -/
theorem flight_dot (a : Nat) (target fallback : Expr) (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv)
    (e e' : EvalState) (cell : NeedCell) (alg? : Option Algorithm)
    (hcell : e.needs[a]? = some cell) (hr : cell.route = none)
    (hprobe : (resolveDotReceiver? target ctx).runState e = (.ok alg?, e'))
    (hmiss : selectDotEdge ctx target "Algorithm" alg? = .ok (.miss .algorithm))
    (hstill : (e'.needs[a]?).bind NeedCell.route = none) :
    (withCtx (dotShape target fallback args ctx env).ctxMsg
        (NeedPlan.routeOf productionPlanRoute.classify a (dotShape target fallback args ctx env))).runState e =
      (.ok .algorithm, withRoute a .algorithm e') := by
  rw [ctx_run, routeOf_fresh _ a _ e cell hcell hr]
  have hc := classify_dot target "Algorithm" fallback args ctx env e e' alg? _ hprobe hmiss
  have hc' : (productionPlanRoute.classify (dotShape target fallback args ctx env)).runState e =
      (.ok .algorithm, e') := hc
  rw [hc']
  simp only [recordRoute, hstill]
  rfl

/-- **The flight of a grouped-form plan**: its first route decision is the edge's `.Algorithm`
    route fact, answering `true`. -/
theorem flight_grouped (a : Nat) (receiver fallback : Expr) (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv)
    (e e' : EvalState) (cell : NeedCell)
    (hcell : e.needs[a]? = some cell) (hr : cell.route = none)
    (hdecided : (algorithmIntrinsicRoute receiver ctx).runState e = (.ok true, e'))
    (hstill : (e'.needs[a]?).bind NeedCell.route = none) :
    (withCtx (groupedShape receiver fallback args ctx env).ctxMsg
        (NeedPlan.routeOf productionPlanRoute.classify a (groupedShape receiver fallback args ctx env))).runState e =
      (.ok .algorithm, withRoute a .algorithm e') := by
  rw [ctx_run, routeOf_fresh _ a _ e cell hcell hr]
  have hc := KatLang.InvocationRouteLaws.classify_call_link resolveDotReceiver? algorithmIntrinsicRoute receiver fallback
    args ctx env e
  rw [hdecided] at hc
  have hc' : (productionPlanRoute.classify (groupedShape receiver fallback args ctx env)).runState e =
      (.ok .algorithm, e') := hc
  rw [hc']
  simp only [recordRoute, hstill]
  rfl

/-! ## The instance context -/

def decls : List (Ident × Algorithm) :=
  [("Seven", alg [] [] [] [.num 7]),
   ("Empty", alg [] [] [] [])]

def root : Algorithm := algPrivate [] [] decls []
def base : EvalCtx := { callStack := [preludeAlg] }
/-- The root context, wired as `runResultM` wires a program root over the prelude. -/
def ctx : EvalCtx := base.push (wireToCaller base root)

def fb : Expr := .resolve "Algorithm"

theorem ctx_valid (h : Array NeedCell) : KatLang.HeapAddressValidity.ValidCtx h ctx := by
  have hne : ctx.needEnv = [] := by kernel_rfl
  intro p m
  rw [hne] at m
  cases m

set_option maxRecDepth 100000

/-! ## `5.Algorithm(0)` and `(5.Algorithm)(0)`: a successful receiver read, the tail's kind rejection -/

namespace Five

def five : Expr := .num 5
def args : OutputBundle := [.num 0]
def edge : Expr := .dotMember five "Algorithm" fb none

/-! ### The dot form -/

def src : Expr := .dotMember five "Algorithm" fb (some args)

/-- The written invocation supplied as a fresh cell from the empty state (`supplyNeed`). -/
def supplied : EvalState := ((supplyNeed src ctx []).runState EvalState.empty).2
/-- The state the VALUE shell runs the plan from: the cell marked `evaluating`. -/
def entry : EvalState := withState 0 .evaluating supplied
/-- THE COMPARISON STATE: the plan's flight — the route `.algorithm` recorded, the callee not. -/
def x : EvalState := withRoute 0 .algorithm entry

def entryCell : NeedCell := { suspension := .expression src ctx [], state := .evaluating }
def ca : NeedCell := { suspension := .expression src ctx [], state := .evaluating, route := some .algorithm }

theorem supplied_address : ((supplyNeed src ctx []).runState EvalState.empty).1 = .ok 0 := by kernel_rfl
theorem entry_cell : entry.needs[0]? = some entryCell := by kernel_rfl
theorem x_cell : x.needs[0]? = some ca := by kernel_rfl

theorem miss : selectDotEdge ctx five "Algorithm" none = .ok (.miss .algorithm) := by kernel_rfl

theorem probe_entry : (resolveDotReceiver? five ctx).runState entry = (.ok none, entry) :=
  prod_of_fuel 20 (.resolveDotReceiver? five ctx) entry _ (by kernel_rfl) (ok_complete _)

/-- **REACHED.** `x` is the flight of the plan cell supplied from the empty state: its first route
    decision selects the `.Algorithm` intrinsic. -/
theorem flight :
    (withCtx (dotShape five fb args ctx []).ctxMsg
        (NeedPlan.routeOf productionPlanRoute.classify 0 (dotShape five fb args ctx []))).runState entry =
      (.ok .algorithm, x) :=
  flight_dot 0 five fb args ctx [] entry entry entryCell none entry_cell rfl probe_entry miss (by kernel_rfl)

theorem supplied_eq : supplied =
    { EvalState.empty with needs := EvalState.empty.needs.push { suspension := .expression src ctx [] } } := by
  kernel_rfl

theorem inv_x : Inv x := by
  have h := inv_push empty_inv (.expression src ctx []) ⟨ctx_valid _, fun _ m => by cases m⟩
  rw [← supplied_eq] at h
  exact inv_flight h 0

/-- Production's receiver probe at the flight. -/
theorem probe_x : (resolveDotReceiver? five ctx).runState x = (.ok none, x) :=
  prod_of_fuel 20 (.resolveDotReceiver? five ctx) x _ (by kernel_rfl) (ok_complete _)

/-- The receiver's VALUE (computed by the kernel: the number 5). -/
def value : Result :=
  match ((evalFuel 20 (.eval five ctx [])).runState x).1 with
  | .ok v => v
  | .error _ => .atom 0

theorem eval_x : (eval five ctx []).runState x = (.ok value, x) :=
  prod_of_fuel 20 (.eval five ctx []) x _ (by kernel_rfl) (ok_complete _)

/-- PRODUCTION's receiver read from the flight. -/
theorem read_x : (invocationReceiverValue five ctx []).runState x = (.ok value, x) :=
  irv_value five ctx [] x x x (.ok value) probe_x eval_x

theorem value_unshifted : shiftResult ⟨x.needs.size, 2⟩ value = value := by kernel_rfl

/-- The plan side's insertion with the receiver cell `evaluating`. -/
abbrev ιe : Insertion := planInsertion x.needs.size 0 edge ctx [] .evaluating
/-- The plan side's insertion with the receiver cell completed with the read VALUE. -/
abbrev ιd : Insertion := planInsertion x.needs.size 0 edge ctx [] (.completed (receiverMemo ⟨x.needs.size, 2⟩ (.ok value)))

theorem probe_plan : (resolveDotReceiver? five ctx).runState (embed ιe x) = (.ok none, embed ιe x) :=
  prod_of_fuel 20 (.resolveDotReceiver? five ctx) (embed ιe x) _ (by kernel_rfl) (ok_complete _)

theorem eval_plan : (eval five ctx []).runState (embed ιe x) = (.ok value, embed ιe x) :=
  prod_of_fuel 20 (.eval five ctx []) (embed ιe x) _ (by kernel_rfl) (ok_complete _)

/-- THE PLAN SIDE's receiver read, from the plan-side state: production's, under the insertion. -/
theorem read_plan : (invocationReceiverValue five ctx []).runState (embed ιe x) =
    (shiftExcept (shiftResult ⟨x.needs.size, 2⟩) (.ok value), embed ιe x) := by
  rw [irv_value five ctx [] _ _ _ (.ok value) probe_plan eval_plan]
  show (Except.ok value, embed ιe x) = (Except.ok (shiftResult ⟨x.needs.size, 2⟩ value), embed ιe x)
  rw [value_unshifted]

/-- The intrinsic's failure over the value 5 (computed by the kernel: the kind rejection). -/
def tailError : Error :=
  match ((evalFuel 20 (.algorithmOfValue value (some args) ctx [])).runState x).1 with
  | .error e => e
  | .ok _ => .fuelExhausted

theorem tailError_complete : errorB tailError = true := by decide +kernel

/-- PRODUCTION's tail from the tail entry. -/
theorem tail_x : (algorithmOfValue value (some args) ctx []).runState x = (.error tailError, x) :=
  prod_of_fuel 20 (.algorithmOfValue value (some args) ctx []) x _ (by kernel_rfl) (error_complete tailError_complete)

/-- THE PLAN SIDE's tail, from the plan-side state with the receiver cell completed. -/
theorem tail_plan : (algorithmOfValue (shiftResult ⟨x.needs.size, 2⟩ value) (some args) ctx []).runState (embed ιd x) =
    (.error tailError, embed ιd x) :=
  prod_of_fuel 20 (.algorithmOfValue (shiftResult ⟨x.needs.size, 2⟩ value) (some args) ctx []) (embed ιd x) _
    (by kernel_rfl) (error_complete tailError_complete)

theorem production_completeB : completeB ((evalFuel 30 (.evalCounted src ctx [])).runState x).1 = true := by
  decide +kernel

theorem production_completes : ProductionCompletes (evalCounted src ctx []) x := by
  have h := prod_of_fuel 30 (.evalCounted src ctx []) x _ rfl (complete_of_B production_completeB)
  unfold ProductionCompletes
  rw [show (evalCounted src ctx []).runState x = _ from h]
  exact complete_of_B production_completeB

/-- **`algorithm_bridge_dot` APPLIED to `5.Algorithm(0)` at its plan's flight.** Every premise is
    proved above; the conclusion — the plan's outcome is production's (shifted), and the two final
    states are in `HeapInsertion.Inserted` — is the theorem's. -/
theorem bridge_dot :
    Bridged (finalInsertion x 0 (dotShape five fb args ctx []) five)
      ((ordinaryCall productionPlanRoute 0 (dotShape five fb args ctx []) .algorithm).runState x)
      ((reCountValueBoundary <$> evalCounted src ctx []).runState x) :=
  algorithm_bridge_dot_at 0 five fb args ctx [] x x none ca (by intro p h; cases h) x_cell rfl rfl rfl probe_x miss
    inv_x (.ok value) x read_x read_plan (by decide +kernel)
    (fun v hv => by
      cases hv
      exact ⟨planCallees_of_B (by decide +kernel), .error tailError, x, tail_x, tail_plan, by decide +kernel⟩)
    production_completes

/-- The relation itself: the plan's final state is production's with the link and the completed
    receiver cell inserted, and production's final state keeps `Frame`. -/
theorem inserted_dot :
    Inserted (finalInsertion x 0 (dotShape five fb args ctx []) five)
      ((ordinaryCall productionPlanRoute 0 (dotShape five fb args ctx []) .algorithm).runState x).2
      ((reCountValueBoundary <$> evalCounted src ctx []).runState x).2 :=
  bridge_dot.2

/-! ### The grouped form -/

def srcG : Expr := .call edge args

def suppliedG : EvalState := ((supplyNeed srcG ctx []).runState EvalState.empty).2
def entryG : EvalState := withState 0 .evaluating suppliedG
def xG : EvalState := withRoute 0 .algorithm entryG

def entryCellG : NeedCell := { suspension := .expression srcG ctx [], state := .evaluating }
def caG : NeedCell := { suspension := .expression srcG ctx [], state := .evaluating, route := some .algorithm }

theorem entryG_cell : entryG.needs[0]? = some entryCellG := by kernel_rfl
theorem xG_cell : xG.needs[0]? = some caG := by kernel_rfl

theorem decided_entry : (algorithmIntrinsicRoute five ctx).runState entryG = (.ok true, entryG) :=
  prod_of_fuel 20 (.algorithmIntrinsicRoute five ctx) entryG _ (by kernel_rfl) (ok_complete _)

/-- **REACHED.** `xG` is the flight of the grouped plan cell supplied from the empty state. -/
theorem flightG :
    (withCtx (groupedShape five fb args ctx []).ctxMsg
        (NeedPlan.routeOf productionPlanRoute.classify 0 (groupedShape five fb args ctx []))).runState entryG =
      (.ok .algorithm, xG) :=
  flight_grouped 0 five fb args ctx [] entryG entryG entryCellG entryG_cell rfl decided_entry (by kernel_rfl)

theorem suppliedG_eq : suppliedG =
    { EvalState.empty with needs := EvalState.empty.needs.push { suspension := .expression srcG ctx [] } } := by
  kernel_rfl

theorem inv_xG : Inv xG := by
  have h := inv_push empty_inv (.expression srcG ctx []) ⟨ctx_valid _, fun _ m => by cases m⟩
  rw [← suppliedG_eq] at h
  exact inv_flight h 0

/-- Production's route decision is SETTLED at the flight: it answers `true` and changes nothing. -/
theorem settled : (withCtx (CtxMsg.call edge) (algorithmIntrinsicRoute five ctx)).runState xG = (.ok true, xG) := by
  rw [ctx_run, show (algorithmIntrinsicRoute five ctx).runState xG = (.ok true, xG) from
    prod_of_fuel 20 (.algorithmIntrinsicRoute five ctx) xG _ (by kernel_rfl) (ok_complete _)]
  rfl

theorem probe_xG : (resolveDotReceiver? five ctx).runState xG = (.ok none, xG) :=
  prod_of_fuel 20 (.resolveDotReceiver? five ctx) xG _ (by kernel_rfl) (ok_complete _)

theorem eval_xG : (eval five ctx []).runState xG = (.ok value, xG) :=
  prod_of_fuel 20 (.eval five ctx []) xG _ (by kernel_rfl) (ok_complete _)

theorem read_xG : (invocationReceiverValue five ctx []).runState xG = (.ok value, xG) :=
  irv_value five ctx [] xG xG xG (.ok value) probe_xG eval_xG

theorem value_unshiftedG : shiftResult ⟨xG.needs.size, 2⟩ value = value := by kernel_rfl

abbrev ιeG : Insertion := planInsertion xG.needs.size 0 edge ctx [] .evaluating
abbrev ιdG : Insertion :=
  planInsertion xG.needs.size 0 edge ctx [] (.completed (receiverMemo ⟨xG.needs.size, 2⟩ (.ok value)))

theorem probe_planG : (resolveDotReceiver? five ctx).runState (embed ιeG xG) = (.ok none, embed ιeG xG) :=
  prod_of_fuel 20 (.resolveDotReceiver? five ctx) (embed ιeG xG) _ (by kernel_rfl) (ok_complete _)

theorem eval_planG : (eval five ctx []).runState (embed ιeG xG) = (.ok value, embed ιeG xG) :=
  prod_of_fuel 20 (.eval five ctx []) (embed ιeG xG) _ (by kernel_rfl) (ok_complete _)

theorem read_planG : (invocationReceiverValue five ctx []).runState (embed ιeG xG) =
    (shiftExcept (shiftResult ⟨xG.needs.size, 2⟩) (.ok value), embed ιeG xG) := by
  rw [irv_value five ctx [] _ _ _ (.ok value) probe_planG eval_planG]
  show (Except.ok value, embed ιeG xG) = (Except.ok (shiftResult ⟨xG.needs.size, 2⟩ value), embed ιeG xG)
  rw [value_unshiftedG]

theorem tail_xG : (algorithmOfValue value (some args) ctx []).runState xG = (.error tailError, xG) :=
  prod_of_fuel 20 (.algorithmOfValue value (some args) ctx []) xG _ (by kernel_rfl) (error_complete tailError_complete)

theorem tail_planG :
    (algorithmOfValue (shiftResult ⟨xG.needs.size, 2⟩ value) (some args) ctx []).runState (embed ιdG xG) =
      (.error tailError, embed ιdG xG) :=
  prod_of_fuel 20 (.algorithmOfValue (shiftResult ⟨xG.needs.size, 2⟩ value) (some args) ctx []) (embed ιdG xG) _
    (by kernel_rfl) (error_complete tailError_complete)

theorem productionG_completeB :
    completeB ((evalFuel 30 (.evalCallCountedExpr edge args ctx [])).runState xG).1 = true := by decide +kernel

theorem productionG_completes : ProductionCompletes (evalCallCountedExpr edge args ctx []) xG := by
  have h := prod_of_fuel 30 (.evalCallCountedExpr edge args ctx []) xG _ rfl (complete_of_B productionG_completeB)
  unfold ProductionCompletes
  rw [show (evalCallCountedExpr edge args ctx []).runState xG = _ from h]
  exact complete_of_B productionG_completeB

/-- **`algorithm_bridge_grouped` APPLIED to `(5.Algorithm)(0)` at its plan's flight**, both sides
    from the one flight state (production's route decision is settled there, `settled`). -/
theorem bridge_grouped :
    Bridged (finalInsertion xG 0 (groupedShape five fb args ctx []) five)
      ((ordinaryCall productionPlanRoute 0 (groupedShape five fb args ctx []) .algorithm).runState xG)
      ((reCountValueBoundary <$> evalCallCountedExpr edge args ctx []).runState xG) :=
  algorithm_bridge_grouped_at 0 five fb args ctx [] xG caG (by intro p h; cases h) settled xG_cell rfl rfl rfl inv_xG
    (.ok value) xG read_xG read_planG (by decide +kernel)
    (fun v hv => by
      cases hv
      exact ⟨planCallees_of_B (by decide +kernel), .error tailError, xG, tail_xG, tail_planG, by decide +kernel⟩)
    productionG_completes

end Five

/-! ## `Empty.Algorithm(0)` and `(Empty.Algorithm)(0)`: the receiver read fails -/

namespace Missing

def emptyE : Expr := .resolve "Empty"
def args : OutputBundle := [.num 0]
def edge : Expr := .dotMember emptyE "Algorithm" fb none
def noAlg : Algorithm := alg [] [] [] []

/-! ### The dot form -/

def src : Expr := .dotMember emptyE "Algorithm" fb (some args)
def supplied : EvalState := ((supplyNeed src ctx []).runState EvalState.empty).2
def entry : EvalState := withState 0 .evaluating supplied
def x : EvalState := withRoute 0 .algorithm entry

def entryCell : NeedCell := { suspension := .expression src ctx [], state := .evaluating }
def ca : NeedCell := { suspension := .expression src ctx [], state := .evaluating, route := some .algorithm }

theorem entry_cell : entry.needs[0]? = some entryCell := by kernel_rfl
theorem x_cell : x.needs[0]? = some ca := by kernel_rfl

/-- The receiver's identity: the declared algorithm `Empty` (computed by the kernel). -/
def g : Algorithm :=
  match ((evalFuel 20 (.resolveDotReceiver? emptyE ctx)).runState entry).1 with
  | .ok (some a) => a
  | _ => noAlg

theorem miss : selectDotEdge ctx emptyE "Algorithm" (some g) = .ok (.miss .algorithm) := by kernel_rfl

/-- The identity probe finds the algorithm and changes nothing. -/
theorem probe_entry : (resolveDotReceiver? emptyE ctx).runState entry = (.ok (some g), entry) :=
  prod_of_fuel 20 (.resolveDotReceiver? emptyE ctx) entry _ (by kernel_rfl) (ok_complete _)

/-- **REACHED.** `x` is the flight of the plan cell supplied from the empty state. -/
theorem flight :
    (withCtx (dotShape emptyE fb args ctx []).ctxMsg
        (NeedPlan.routeOf productionPlanRoute.classify 0 (dotShape emptyE fb args ctx []))).runState entry =
      (.ok .algorithm, x) :=
  flight_dot 0 emptyE fb args ctx [] entry entry entryCell (some g) entry_cell rfl probe_entry miss (by kernel_rfl)

theorem supplied_eq : supplied =
    { EvalState.empty with needs := EvalState.empty.needs.push { suspension := .expression src ctx [] } } := by
  kernel_rfl

theorem inv_x : Inv x := by
  have h := inv_push empty_inv (.expression src ctx []) ⟨ctx_valid _, fun _ m => by cases m⟩
  rw [← supplied_eq] at h
  exact inv_flight h 0

theorem probe_x : (resolveDotReceiver? emptyE ctx).runState x = (.ok (some g), x) :=
  prod_of_fuel 20 (.resolveDotReceiver? emptyE ctx) x _ (by kernel_rfl) (ok_complete _)

/-- The receiver read's FAILURE (computed by the kernel: the missing output of `Empty`). -/
def readError : Error :=
  match ((evalFuel 30 (.referenceReceiverValue emptyE g ctx [])).runState x).1 with
  | .error e => e
  | .ok _ => .fuelExhausted

/-- Production's state after the failed read. -/
def x₄ : EvalState := ((evalFuel 30 (.referenceReceiverValue emptyE g ctx [])).runState x).2

theorem readError_complete : errorB readError = true := by decide +kernel

theorem reference_x : (referenceReceiverValue emptyE g ctx []).runState x = (.error readError, x₄) :=
  prod_of_fuel 30 (.referenceReceiverValue emptyE g ctx []) x _ (by kernel_rfl) (error_complete readError_complete)

/-- PRODUCTION's receiver read from the flight: it fails. -/
theorem read_x : (invocationReceiverValue emptyE ctx []).runState x = (.error readError, x₄) :=
  irv_reference emptyE ctx [] x x x₄ g (.error readError) probe_x reference_x

abbrev ιe : Insertion := planInsertion x.needs.size 0 edge ctx [] .evaluating

theorem probe_plan : (resolveDotReceiver? emptyE ctx).runState (embed ιe x) = (.ok (some g), embed ιe x) :=
  prod_of_fuel 20 (.resolveDotReceiver? emptyE ctx) (embed ιe x) _ (by kernel_rfl) (ok_complete _)

theorem reference_plan : (referenceReceiverValue emptyE g ctx []).runState (embed ιe x) =
    (.error readError, embed ιe x₄) :=
  prod_of_fuel 30 (.referenceReceiverValue emptyE g ctx []) (embed ιe x) _ (by kernel_rfl)
    (error_complete readError_complete)

/-- THE PLAN SIDE's receiver read: the same failure, the state under the insertion. -/
theorem read_plan : (invocationReceiverValue emptyE ctx []).runState (embed ιe x) =
    (shiftExcept (shiftResult ⟨x.needs.size, 2⟩) (.error readError), embed ιe x₄) :=
  irv_reference emptyE ctx [] (embed ιe x) (embed ιe x) (embed ιe x₄) g (.error readError) probe_plan reference_plan

theorem production_completeB : completeB ((evalFuel 40 (.evalCounted src ctx [])).runState x).1 = true := by
  decide +kernel

theorem production_completes : ProductionCompletes (evalCounted src ctx []) x := by
  have h := prod_of_fuel 40 (.evalCounted src ctx []) x _ rfl (complete_of_B production_completeB)
  unfold ProductionCompletes
  rw [show (evalCounted src ctx []).runState x = _ from h]
  exact complete_of_B production_completeB

/-- **`algorithm_bridge_dot` APPLIED to `Empty.Algorithm(0)`**: the receiver read fails; there is no
    tail entry, so the tail premises hold with nothing to check — and the bridge still concludes the
    full relation (the plan's receiver cell memoizes the failure). -/
theorem bridge_dot :
    Bridged (finalInsertion x 0 (dotShape emptyE fb args ctx []) emptyE)
      ((ordinaryCall productionPlanRoute 0 (dotShape emptyE fb args ctx []) .algorithm).runState x)
      ((reCountValueBoundary <$> evalCounted src ctx []).runState x) :=
  algorithm_bridge_dot_at 0 emptyE fb args ctx [] x x (some g) ca (by intro p h; cases h) x_cell rfl rfl rfl probe_x
    miss inv_x (.error readError) x₄ read_x read_plan (by decide +kernel) (fun v hv => by cases hv)
    production_completes

/-! ### The grouped form -/

def srcG : Expr := .call edge args
def suppliedG : EvalState := ((supplyNeed srcG ctx []).runState EvalState.empty).2
def entryG : EvalState := withState 0 .evaluating suppliedG
def xG : EvalState := withRoute 0 .algorithm entryG

def entryCellG : NeedCell := { suspension := .expression srcG ctx [], state := .evaluating }
def caG : NeedCell := { suspension := .expression srcG ctx [], state := .evaluating, route := some .algorithm }

theorem entryG_cell : entryG.needs[0]? = some entryCellG := by kernel_rfl
theorem xG_cell : xG.needs[0]? = some caG := by kernel_rfl

theorem decided_entry : (algorithmIntrinsicRoute emptyE ctx).runState entryG = (.ok true, entryG) :=
  prod_of_fuel 20 (.algorithmIntrinsicRoute emptyE ctx) entryG _ (by kernel_rfl) (ok_complete _)

/-- **REACHED.** `xG` is the flight of the grouped plan cell supplied from the empty state. -/
theorem flightG :
    (withCtx (groupedShape emptyE fb args ctx []).ctxMsg
        (NeedPlan.routeOf productionPlanRoute.classify 0 (groupedShape emptyE fb args ctx []))).runState entryG =
      (.ok .algorithm, xG) :=
  flight_grouped 0 emptyE fb args ctx [] entryG entryG entryCellG entryG_cell rfl decided_entry (by kernel_rfl)

theorem suppliedG_eq : suppliedG =
    { EvalState.empty with needs := EvalState.empty.needs.push { suspension := .expression srcG ctx [] } } := by
  kernel_rfl

theorem inv_xG : Inv xG := by
  have h := inv_push empty_inv (.expression srcG ctx []) ⟨ctx_valid _, fun _ m => by cases m⟩
  rw [← suppliedG_eq] at h
  exact inv_flight h 0

theorem settled : (withCtx (CtxMsg.call edge) (algorithmIntrinsicRoute emptyE ctx)).runState xG = (.ok true, xG) := by
  rw [ctx_run, show (algorithmIntrinsicRoute emptyE ctx).runState xG = (.ok true, xG) from
    prod_of_fuel 20 (.algorithmIntrinsicRoute emptyE ctx) xG _ (by kernel_rfl) (ok_complete _)]
  rfl

theorem probe_xG : (resolveDotReceiver? emptyE ctx).runState xG = (.ok (some g), xG) :=
  prod_of_fuel 20 (.resolveDotReceiver? emptyE ctx) xG _ (by kernel_rfl) (ok_complete _)

def x₄G : EvalState := ((evalFuel 30 (.referenceReceiverValue emptyE g ctx [])).runState xG).2

theorem reference_xG : (referenceReceiverValue emptyE g ctx []).runState xG = (.error readError, x₄G) :=
  prod_of_fuel 30 (.referenceReceiverValue emptyE g ctx []) xG _ (by kernel_rfl) (error_complete readError_complete)

theorem read_xG : (invocationReceiverValue emptyE ctx []).runState xG = (.error readError, x₄G) :=
  irv_reference emptyE ctx [] xG xG x₄G g (.error readError) probe_xG reference_xG

abbrev ιeG : Insertion := planInsertion xG.needs.size 0 edge ctx [] .evaluating

theorem probe_planG : (resolveDotReceiver? emptyE ctx).runState (embed ιeG xG) = (.ok (some g), embed ιeG xG) :=
  prod_of_fuel 20 (.resolveDotReceiver? emptyE ctx) (embed ιeG xG) _ (by kernel_rfl) (ok_complete _)

theorem reference_planG : (referenceReceiverValue emptyE g ctx []).runState (embed ιeG xG) =
    (.error readError, embed ιeG x₄G) :=
  prod_of_fuel 30 (.referenceReceiverValue emptyE g ctx []) (embed ιeG xG) _ (by kernel_rfl)
    (error_complete readError_complete)

theorem read_planG : (invocationReceiverValue emptyE ctx []).runState (embed ιeG xG) =
    (shiftExcept (shiftResult ⟨xG.needs.size, 2⟩) (.error readError), embed ιeG x₄G) :=
  irv_reference emptyE ctx [] (embed ιeG xG) (embed ιeG xG) (embed ιeG x₄G) g (.error readError) probe_planG
    reference_planG

theorem productionG_completeB :
    completeB ((evalFuel 40 (.evalCallCountedExpr edge args ctx [])).runState xG).1 = true := by decide +kernel

theorem productionG_completes : ProductionCompletes (evalCallCountedExpr edge args ctx []) xG := by
  have h := prod_of_fuel 40 (.evalCallCountedExpr edge args ctx []) xG _ rfl (complete_of_B productionG_completeB)
  unfold ProductionCompletes
  rw [show (evalCallCountedExpr edge args ctx []).runState xG = _ from h]
  exact complete_of_B productionG_completeB

/-- **`algorithm_bridge_grouped` APPLIED to `(Empty.Algorithm)(0)`**, both sides from the flight. -/
theorem bridge_grouped :
    Bridged (finalInsertion xG 0 (groupedShape emptyE fb args ctx []) emptyE)
      ((ordinaryCall productionPlanRoute 0 (groupedShape emptyE fb args ctx []) .algorithm).runState xG)
      ((reCountValueBoundary <$> evalCallCountedExpr edge args ctx []).runState xG) :=
  algorithm_bridge_grouped_at 0 emptyE fb args ctx [] xG caG (by intro p h; cases h) settled xG_cell rfl rfl rfl
    inv_xG (.error readError) x₄G read_xG read_planG (by decide +kernel) (fun v hv => by cases hv)
    productionG_completes

end Missing

/-! ## A call reference in the tail: the tail contract SATISFIED, and VIOLATED by the self-reference

No kernel-evaluable receiver read returns a call reference (a reference is the VALUE of a `meta`
parameter, and a parameter read is behind `activeDeclaration?`). The TAIL over a call reference is
kernel-evaluable, so the tail's two obligations — the contract at the plan side's insertion and the
preservation of the plan cell's unrecorded callee — are checked here on a concrete state for a call
reference, at the level of the tail:

* the state `t` is the flight of a plan cell (cell 1) in a heap that also holds the written
  invocation `Seven()` (cell 0), both supplied from the empty state;
* for the value `callRef 0` — a reference to another plan — production's `algorithmOfValue`
  establishes that plan's callee in a NEW cell past the insertion, projects it and runs the fresh
  call (the value 7): the plan side's run from the plan-side state is production's under the
  insertion, with the new cell and the callee record SHIFTED by two (`tail_inserted`,
  `shifted_callee`), and the plan cell stays `Unrecorded` (`tail_keeps`);
* for the value `callRef 1` — the plan cell's OWN reference, the input that refuted the old
  universal premise — production records the plan cell's callee: `Frame` is broken at its final
  state and the preservation obligation FAILS (`self_reference_breaks`, by the general
  `self_reference_breaks_frame_at_flight`). -/

namespace Reference

def seven0 : Expr := .call (.resolve "Seven") []
def five : Expr := .num 5
def edge : Expr := .dotMember five "Algorithm" fb none
def src : Expr := .dotMember five "Algorithm" fb (some [])

/-- Cell 0: the written invocation `Seven()`. -/
def s₀ : EvalState := ((supplyNeed seven0 ctx []).runState EvalState.empty).2
/-- Cell 1: the plan. -/
def supplied : EvalState := ((supplyNeed src ctx []).runState s₀).2
def entry : EvalState := withState 1 .evaluating supplied
/-- The plan's flight. -/
def t : EvalState := withRoute 1 .algorithm entry

def ca : NeedCell := { suspension := .expression src ctx [], state := .evaluating, route := some .algorithm }

theorem t_cell : t.needs[1]? = some ca := by kernel_rfl

theorem s₀_eq : s₀ =
    { EvalState.empty with needs := EvalState.empty.needs.push { suspension := .expression seven0 ctx [] } } := by
  kernel_rfl

theorem supplied_eq : supplied = { s₀ with needs := s₀.needs.push { suspension := .expression src ctx [] } } := by
  kernel_rfl

theorem inv_t : Inv t := by
  have h0 := inv_push empty_inv (.expression seven0 ctx []) ⟨ctx_valid _, fun _ m => by cases m⟩
  rw [← s₀_eq] at h0
  have h1 := inv_push h0 (.expression src ctx []) ⟨ctx_valid _, fun _ m => by cases m⟩
  rw [← supplied_eq] at h1
  exact inv_flight h1 1

/-- The plan side's insertion with the receiver cell completed with the reference. -/
abbrev ι : Insertion :=
  planInsertion t.needs.size 1 edge ctx [] (.completed (receiverMemo ⟨t.needs.size, 2⟩ (.ok (.callRef 0))))

/-- Production's tail outcome (computed by the kernel: the value 7). -/
def out : CountedResult :=
  match ((evalFuel 40 (.algorithmOfValue (.callRef 0) (some []) ctx [])).runState t).1 with
  | .ok r => r
  | .error _ => (.atom 0, 0)

/-- Production's final state. -/
def t₅ : EvalState := ((evalFuel 40 (.algorithmOfValue (.callRef 0) (some []) ctx [])).runState t).2

/-- PRODUCTION's tail over the reference: a success. -/
theorem tail_t : (algorithmOfValue (.callRef 0) (some []) ctx []).runState t = (.ok out, t₅) :=
  prod_of_fuel 40 (.algorithmOfValue (.callRef 0) (some []) ctx []) t _ (by kernel_rfl) (ok_complete _)

/-- THE PLAN SIDE's tail over the (shifted) reference, from the plan-side state: production's
    outcome, the final state production's under the insertion. -/
theorem tail_plan :
    (algorithmOfValue (shiftResult ⟨t.needs.size, 2⟩ (.callRef 0)) (some []) ctx []).runState (embed ι t) =
      (shiftExcept (shiftCounted ⟨t.needs.size, 2⟩) (.ok out), embed ι t₅) :=
  prod_of_fuel 40 (.algorithmOfValue (shiftResult ⟨t.needs.size, 2⟩ (.callRef 0)) (some []) ctx []) (embed ι t) _
    (by kernel_rfl) (ok_complete _)

/-- **The tail contract holds for the reference** at the plan side's insertion. -/
theorem tail_inserted :
    InsertedAt (fun s => s = t) ι shiftCounted
      (algorithmOfValue (shiftResult ⟨t.needs.size, 2⟩ (.callRef 0)) (some []) ctx [])
      (algorithmOfValue (.callRef 0) (some []) ctx []) :=
  insertedAt_singleton tail_t tail_plan

/-- **The preservation obligation holds for the reference**: the plan cell stays `Unrecorded`. -/
theorem tail_keeps :
    KeepsOn (fun s => s = t) (Unrecorded 1) (algorithmOfValue (.callRef 0) (some []) ctx []) := by
  intro s hs _
  subst hs
  rw [tail_t]
  show Unrecorded 1 t₅
  decide +kernel

/-- Production's tail allocates PAST the insertion address, and the value is the number 7. -/
theorem tail_allocates : t.needs.size < t₅.needs.size := by decide +kernel

/-- The captured plan's callee is recorded at the new cell in production and at that cell SHIFTED
    by the two inserted cells on the plan side. -/
theorem shifted_callee :
    (t₅.needs[0]?).bind NeedCell.callee = some t.needs.size ∧
    ((embed ι t₅).needs[0]?).bind NeedCell.callee = some (t.needs.size + 2) := by
  constructor <;> decide +kernel

theorem self_completeB :
    completeB ((evalFuel 40 (.algorithmOfValue (.callRef 1) (some []) ctx [])).runState t).1 = true := by
  decide +kernel

theorem self_completes : ProductionCompletes (algorithmOfValue (.callRef 1) (some []) ctx []) t := by
  have h := prod_of_fuel 40 (.algorithmOfValue (.callRef 1) (some []) ctx []) t _ rfl (complete_of_B self_completeB)
  unfold ProductionCompletes
  rw [show (algorithmOfValue (.callRef 1) (some []) ctx []).runState t = _ from h]
  exact complete_of_B self_completeB

/-- **The self-reference is not an admissible tail input here**: over the plan cell's OWN reference
    production records that cell's callee, so `Frame` fails at its final state. -/
theorem self_reference_breaks :
    ¬ Frame t.needs.size 1 ((algorithmOfValue (.callRef 1) (some []) ctx []).runState t).2 :=
  self_reference_breaks_frame_at_flight 1 t ca (dotShape five fb [] ctx []) five fb inv_t t_cell rfl rfl rfl rfl
    (by intro p h; cases h) [] ctx [] self_completes

/-- So the preservation obligation the bridges ask of the tail FAILS for the self-reference. -/
theorem self_reference_not_kept :
    ¬ KeepsOn (fun s => s = t) (Unrecorded 1) (algorithmOfValue (.callRef 1) (some []) ctx []) :=
  fun h => self_reference_breaks
    ⟨by decide +kernel,
     heapKept_size
       (KatLang.EvaluatorDiscipline.evalUnbounded_disciplined (.algorithmOfValue (.callRef 1) (some []) ctx []) t),
     h t rfl self_completes⟩

end Reference

end KatLang.PlanAlgorithmBridgeInstances
