import KatLangArityLaws.PlanAlgorithmBridgeSourceInstances

/-!
# The `.Algorithm` bridge applied: an effectful receiver, demanded twice, evaluated once (E-18 step 1, M2)

`Effectful` / `EffectfulG` — `Both(tick(), R).Algorithm(0)` with `Both(a, b) = if(a + a > 0, b, b)`: the
receiver's argument `tick()` is demanded twice and evaluated once (memo sharing), and the receiver is
read once on each side: the run's `tick()` counter is 1 at both final states.

Every instance is the proof script of `PlanAlgorithmBridgeSourceInstances` (see its header for the
method — proof-producing evaluation by `cbv` over the production definitions, standard axioms only —
and for what "reached" means): the source program with the one root row `Capture(P)`, its genuine
evaluation from the empty state (`captured`, `program_run`), the plan cell (`plan_cell`), its flight
(`flight`), the VALUE demand passing through that flight (`demand_passes`), every premise of the
final bridge theorem, and the theorem APPLIED (`bridge`).
-/

open KatLang KatLang.CallPlan KatLang.EvaluatorCore KatLang.PlanRouteBridge KatLang.HeapInsertion
open KatLang.PlanAlgorithmBridge KatLang.PlanAlgorithmBridgeInstances
open KatLang.AddressInvariant (Inv empty_inv CallPre production_sound_all)
open KatLang.HeapAddressValidity (ValidCtx)

namespace KatLang.PlanAlgorithmBridgeInstances.Source

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option cbv.maxSteps 20000000

/-! ## `Effectful`: the dot form -/

namespace Effectful
/-- `Both(tick(), R).Algorithm(0)` with `Both(a, b) = if(a + a > 0, b, b)` — an EFFECTFUL receiver with REPEATED DEMAND AND MEMO SHARING: `a` is demanded twice and evaluated once, so the run's `tick()` counter is 1 — on both sides. -/
def recv : Expr := callN "Both" [tickE, R]
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
    (((ordinaryCall productionPlanRoute 0 shape .algorithm).runState x).1 = .ok (.atom 0, 1) ∧ ((evalCounted src ctx []).runState x).1 = .ok (.atom 0, 1)) ∧
    (x.tickCounter = 0 ∧ ((ordinaryCall productionPlanRoute 0 shape .algorithm).runState x).2.tickCounter = 1 ∧ ((evalCounted src ctx []).runState x).2.tickCounter = 1) := by
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

theorem value :
    ((ordinaryCall productionPlanRoute 0 shape .algorithm).runState x).1 = .ok (.atom 0, 1) ∧
    ((evalCounted src ctx []).runState x).1 = .ok (.atom 0, 1) :=
  facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- **The receiver's effect happens ONCE on each side**, although `a` is demanded twice: the run's
    `tick()` counter is 0 at the flight and 1 at both final states. -/
theorem ticks : x.tickCounter = 0 ∧
    ((ordinaryCall productionPlanRoute 0 shape .algorithm).runState x).2.tickCounter = 1 ∧
    ((evalCounted src ctx []).runState x).2.tickCounter = 1 :=
  facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

end Effectful

/-! ## `EffectfulG`: the grouped form `(…​.Algorithm)(…)` -/

namespace EffectfulG
/-- `Both(tick(), R).Algorithm(0)` with `Both(a, b) = if(a + a > 0, b, b)` — an EFFECTFUL receiver with REPEATED DEMAND AND MEMO SHARING: `a` is demanded twice and evaluated once, so the run's `tick()` counter is 1 — on both sides. -/
def recv : Expr := callN "Both" [tickE, R]
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
    (((ordinaryCall productionPlanRoute 0 shape .algorithm).runState x).1 = .ok (.atom 0, 1) ∧ ((evalCallCountedExpr edge args ctx []).runState x).1 = .ok (.atom 0, 1)) ∧
    (x.tickCounter = 0 ∧ ((ordinaryCall productionPlanRoute 0 shape .algorithm).runState x).2.tickCounter = 1 ∧ ((evalCallCountedExpr edge args ctx []).runState x).2.tickCounter = 1) := by
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

theorem value :
    ((ordinaryCall productionPlanRoute 0 shape .algorithm).runState x).1 = .ok (.atom 0, 1) ∧
    ((evalCallCountedExpr edge args ctx []).runState x).1 = .ok (.atom 0, 1) :=
  facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- **The receiver's effect happens ONCE on each side**, although `a` is demanded twice: the run's
    `tick()` counter is 0 at the flight and 1 at both final states. -/
theorem ticks : x.tickCounter = 0 ∧
    ((ordinaryCall productionPlanRoute 0 shape .algorithm).runState x).2.tickCounter = 1 ∧
    ((evalCallCountedExpr edge args ctx []).runState x).2.tickCounter = 1 :=
  facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

end EffectfulG

end KatLang.PlanAlgorithmBridgeInstances.Source
