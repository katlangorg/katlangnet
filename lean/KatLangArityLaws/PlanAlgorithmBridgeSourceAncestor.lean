import KatLangArityLaws.PlanAlgorithmBridgeSourceInstances

/-!
# The `.Algorithm` bridge applied: a captured-ancestor parameter receiver (E-18 step 1, M2)

`Ancestor` / `AncestorG` — `r.Algorithm(0)` written in the nested body `Inner` of `PO(r)`: the receiver is a
parameter of the site's ANCESTOR, found through the recorded activation (`captured_ancestor`, `bound`).
The context is the one the source program's own binder built, read off the genuinely supplied plan
cell. ONE cell is inserted — the callee link, whose receiver is the parameter's own cell.

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

/-! ## `Ancestor`: a CAPTURED-ANCESTOR PARAMETER receiver, the dot form -/

namespace Ancestor
/-- The receiver: the parameter `r` of `PO`, read from the nested body `Inner`. -/
def args : OutputBundle := [.num 0]
def edge : Expr := .dotMember (.param "r") "Algorithm" fb none
/-- The plan's written source, as `Inner` writes it. -/
def src : Expr := .dotMember (.param "r") "Algorithm" fb (some args)
/-- THE SOURCE PROGRAM's one row: `PO(Capture(F(0)))`, with
    `PO(r) = { Inner = Capture(r.Algorithm(0)) ⏎ Inner }`: the parameter `r` is bound to the written
    call `Capture(F(0))`, whose VALUE is a reference. -/
def row : Expr := callN "PO" [capture (callN "F" [.num 0])]
def ctx : EvalCtx := ctxOf [row]

/-- The state the GENUINE evaluation of the row leaves, from the empty state. -/
def fin : EvalState := ((evalCounted row ctx []).runState EvalState.empty).2
/-- The plan cell: the cell the program's result — `Inner`'s captured reference — names. -/
def k : Nat := match ((evalCounted row ctx []).runState EvalState.empty).1 with | .ok (.callRef a, _) => a | _ => 0
/-- THE GENUINE CAPTURED-ANCESTOR CONTEXT: the context the source binder built for `Inner`'s body,
    read off the plan cell's suspension. Its head is `Inner`; `r` is `PO`'s parameter. -/
def ctxIn : EvalCtx := match fin.needs[k]? with | some { suspension := .expression _ c _, .. } => c | _ => ctx
def envIn : ValEnv := match fin.needs[k]? with | some { suspension := .expression _ _ v, .. } => v | _ => []
def shape : NeedPlan.CallShape := dotShape (.param "r") fb args ctxIn envIn

def entry : EvalState := withState k .evaluating fin
def entryCell : NeedCell := { suspension := .expression src ctxIn envIn, state := .evaluating }
def ca : NeedCell := { suspension := .expression src ctxIn envIn, state := .evaluating, route := some .algorithm }
def alg? : Option Algorithm :=
  match ((resolveDotReceiver? (.param "r") ctxIn).runState entry).1 with
  | .ok a => a
  | .error _ => none
/-- The probe's exit: the parameter's FIRST CALLABLE projection wrote its memo. -/
def probed : EvalState := ((resolveDotReceiver? (.param "r") ctxIn).runState entry).2
/-- THE COMPARISON STATE: the plan's flight. -/
def x : EvalState := withRoute k .algorithm probed
/-- The parameter's supplied cell, found through the captured activation. -/
def b : Nat := (KatLang.MemberStability.parameterAddressIn x.lexicalActivations "r" ctxIn).getD 0
def recvOut : Except Error Result := ((invocationReceiverValue (.param "r") ctxIn envIn).runState x).1
def x₄ : EvalState := ((invocationReceiverValue (.param "r") ctxIn envIn).runState x).2
def recvVal : Result := match recvOut with | .ok v => v | .error _ => .atom 0
def refAddr : Nat := match recvVal with | .callRef a => a | _ => 0
/-- The plan side's ONE inserted cell: its callee link, whose receiver is the parameter's own cell. -/
abbrev ι : Insertion := paramInsertion x.needs.size k edge ctxIn envIn b
/-- After production's read the parameter's cell holds the read VALUE (memo sharing: the plan side's
    link reads the same cell). -/
def cellB : NeedCell := match x₄.needs[b]? with | some c => c | none => { suspension := .ready (.atom 0, 0) }
def tailOut : Except Error CountedResult := ((algorithmOfValue recvVal (some args) ctxIn envIn).runState x₄).1
def x₅ : EvalState := ((algorithmOfValue recvVal (some args) ctxIn envIn).runState x₄).2
/-- EVERY evaluated fact of this instance, in ONE proof-producing evaluation (`cbv`); the theorems
    below are its projections. -/
theorem facts :
    ((evalCounted row ctx []).runState EvalState.empty = (.ok (.callRef k, 1), fin)) ∧
    ((evalProgramOutput (wireToCaller base (rootOf [row])) base []).runState EvalState.empty = (.ok (.callRef k), fin)) ∧
    (fin.needs[k]? = some { suspension := .expression src ctxIn envIn }) ∧
    ((ctxIn.head?.map fun site => site.params.contains "r") = some false ∧ (KatLang.MemberStability.capturedId? "r" ctxIn).isSome = true) ∧
    (entry.needs[k]? = some entryCell) ∧
    ((resolveDotReceiver? (.param "r") ctxIn).runState entry = (.ok alg?, probed)) ∧
    (selectDotEdge ctxIn (.param "r") "Algorithm" alg? = .ok (.miss .algorithm)) ∧
    (x.needs[k]? = some ca) ∧
    ((probed.needs[k]?).bind NeedCell.route = none) ∧
    ((resolveDotReceiver? (.param "r") ctxIn).runState x = (.ok alg?, x)) ∧
    (((NeedPlan.executeAlong productionPlanRoute k shape .algorithm).runState x).1.isIncomplete = false) ∧
    (ctx.needEnv = []) ∧
    (ctxIn.needEnv.all (fun p => decide (p.2 < entry.needs.size)) = true) ∧
    (KatLang.MemberStability.parameterAddressIn x.lexicalActivations "r" ctxIn = some b) ∧
    (decide (b < x.needs.size) = true) ∧
    (recvOut = .ok recvVal) ∧
    (recvVal = .callRef refAddr) ∧
    ((invocationReceiverValue (.param "r") ctxIn envIn).runState (embed ι x) = (shiftExcept (shiftResult ⟨x.needs.size, 1⟩) recvOut, embed ι x₄)) ∧
    (Unrecorded k x₄) ∧
    (planCalleesB x₄ = true) ∧
    (x₄.needs[b]? = some cellB) ∧
    (cellB.state = .completed (.ok (recvVal, 1))) ∧
    ((algorithmOfValue (shiftResult ⟨x.needs.size, 1⟩ recvVal) (some args) ctxIn envIn).runState (embed ι x₄) = (shiftExcept (shiftCounted ⟨x.needs.size, 1⟩) tailOut, embed ι x₅)) ∧
    (Unrecorded k x₅) ∧
    (decide (refAddr ≠ k) = true) ∧
    (completeB ((evalCounted src ctxIn envIn).runState x).1 = true) ∧
    (((ordinaryCall productionPlanRoute k shape .algorithm).runState x).1 = .ok (.atom 0, 1) ∧ ((evalCounted src ctxIn envIn).runState x).1 = .ok (.atom 0, 1)) ∧
    (((ordinaryCall productionPlanRoute k shape .algorithm).runState x).2.needs.size = ((reCountValueBoundary <$> evalCounted src ctxIn envIn).runState x).2.needs.size + 1) := by
  cbv
  all_goals (repeat' (first | rfl | constructor))


/-- **REACHED (1).** Production's evaluation of the source row from the empty state returns the
    reference `Inner` captured: the plan cell `k`. -/
theorem captured : (evalCounted row ctx []).runState EvalState.empty = (.ok (.callRef k, 1), fin) :=
  facts.1

/-- The same evaluation as `runResultM` enters it: the program root's zero-argument demand over the
    prelude context, from the empty state. -/
theorem program_run :
    (evalProgramOutput (wireToCaller base (rootOf [row])) base []).runState EvalState.empty =
      (.ok (.callRef k), fin) :=
  facts.2.1

/-- **REACHED (2).** Cell `k` is THE PLAN: the written source, supplied by the source program in
    `Inner`'s own context, suspended, with no route and no callee recorded. -/
theorem plan_cell : fin.needs[k]? = some { suspension := .expression src ctxIn envIn } :=
  facts.2.2.1

/-- The receiver is NOT a parameter of the site: `Inner` declares none, its ancestor `PO` owns
    `r` (the captured-ancestor read, through the recorded activation). -/
theorem captured_ancestor : (ctxIn.head?.map fun site => site.params.contains "r") = some false ∧
    (KatLang.MemberStability.capturedId? "r" ctxIn).isSome = true :=
  facts.2.2.2.1

theorem entry_cell : entry.needs[k]? = some entryCell :=
  facts.2.2.2.2.1

theorem probe_entry : (resolveDotReceiver? (.param "r") ctxIn).runState entry = (.ok alg?, probed) :=
  facts.2.2.2.2.2.1

theorem miss : selectDotEdge ctxIn (.param "r") "Algorithm" alg? = .ok (.miss .algorithm) :=
  facts.2.2.2.2.2.2.1

theorem x_cell : x.needs[k]? = some ca :=
  facts.2.2.2.2.2.2.2.1

theorem route_free : (probed.needs[k]?).bind NeedCell.route = none :=
  facts.2.2.2.2.2.2.2.2.1

/-- **REACHED (3).** `x` is the flight of the plan cell. -/
theorem flight :
    (withCtx shape.ctxMsg (NeedPlan.routeOf productionPlanRoute.classify k shape)).runState entry =
      (.ok .algorithm, x) :=
  flight_dot k (.param "r") fb args ctxIn envIn entry probed entryCell alg? entry_cell rfl probe_entry miss route_free
/-- At the flight the probe reads the projection's memo and changes nothing. -/
theorem probe_x : (resolveDotReceiver? (.param "r") ctxIn).runState x = (.ok alg?, x) :=
  facts.2.2.2.2.2.2.2.2.2.1

theorem demand_done :
    ((NeedPlan.executeAlong productionPlanRoute k shape .algorithm).runState x).1.isIncomplete = false :=
  facts.2.2.2.2.2.2.2.2.2.2.1

/-- **REACHED (4).** The production VALUE demand of the plan cell from the genuine state `fin` IS the
    completion shell over the plan's `.algorithm` execution from the flight `x`. -/
theorem demand_passes :
    (demandNeed k).runState fin =
      (let res := (NeedPlan.executeAlong productionPlanRoute k shape .algorithm).runState x
       (res.1, withState k (.completed res.1) res.2)) :=
  demand_passes_flight k fin x _ src ctxIn envIn shape .algorithm plan_cell rfl rfl rfl flight nofun demand_done

theorem ctx_needEnv : ctx.needEnv = [] :=
  facts.2.2.2.2.2.2.2.2.2.2.2.1

theorem ctx_valid (h : Array NeedCell) : ValidCtx h ctx := validCtx_nil h ctx ctx_needEnv
theorem ctxIn_all : ctxIn.needEnv.all (fun p => decide (p.2 < entry.needs.size)) = true :=
  facts.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem ctxIn_valid : ValidCtx entry.needs ctxIn := validCtx_of_all ctxIn_all
theorem inv_fin : Inv fin := inv_row row ctx (ctx_valid _)
theorem inv_x : Inv x := inv_flight_of_probe inv_fin k (.resolveDotReceiver? (.param "r") ctxIn) probe_entry ctxIn_valid

theorem bound : KatLang.MemberStability.parameterAddressIn x.lexicalActivations "r" ctxIn = some b :=
  facts.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem bound_lt : b < x.needs.size :=
  of_decide_eq_true facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-! ### Production's receiver read, and the plan side's (ONE inserted cell) -/

theorem recv_ok : recvOut = .ok recvVal :=
  facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- **The actual receiver read returns a call reference.** -/
theorem recv_reference : recvVal = .callRef refAddr :=
  facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem read_x : (invocationReceiverValue (.param "r") ctxIn envIn).runState x = (recvOut, x₄) := rfl
theorem read_plan : (invocationReceiverValue (.param "r") ctxIn envIn).runState (embed ι x) =
    (shiftExcept (shiftResult ⟨x.needs.size, 1⟩) recvOut, embed ι x₄) :=
  facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem read_unrecorded : Unrecorded k x₄ :=
  facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem read_callees : planCalleesB x₄ = true :=
  facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem cellB_at : x₄.needs[b]? = some cellB :=
  facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem cellB_done : cellB.state = .completed (.ok (recvVal, 1)) :=
  facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-! ### The admissible tail entry, production's tail and the plan side's -/

theorem tail_x : (algorithmOfValue recvVal (some args) ctxIn envIn).runState x₄ = (tailOut, x₅) := rfl
theorem tail_plan :
    (algorithmOfValue (shiftResult ⟨x.needs.size, 1⟩ recvVal) (some args) ctxIn envIn).runState (embed ι x₄) =
      (shiftExcept (shiftCounted ⟨x.needs.size, 1⟩) tailOut, embed ι x₅) :=
  facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem tail_unrecorded : Unrecorded k x₅ :=
  facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- The plan cell's own reference is NOT the receiver's result. -/
theorem ref_ne : refAddr ≠ k :=
  of_decide_eq_true facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem not_self : recvVal ≠ .callRef k := by
  rw [recv_reference]
  intro h
  exact ref_ne (Result.callRef.inj h)

theorem production_done : completeB ((evalCounted src ctxIn envIn).runState x).1 = true :=
  facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem production_completes : ProductionCompletes (evalCounted src ctxIn envIn) x := complete_of_B production_done

/-- **`algorithm_bridge_dot_param_at` APPLIED** at the plan's flight, every premise proved above. -/
theorem bridge :
    Bridged ι
      ((ordinaryCall productionPlanRoute k shape .algorithm).runState x)
      ((reCountValueBoundary <$> evalCounted src ctxIn envIn).runState x) :=
  algorithm_bridge_dot_param_at k "r" fb args ctxIn envIn x x alg? ca b x_cell rfl rfl rfl probe_x miss bound bound_lt
    inv_x recvOut x₄ read_x read_plan read_unrecorded
    (fun v hv => by
      have hv' : v = recvVal := by
        have h := recv_ok.symm.trans hv
        exact (Except.ok.inj h).symm
      subst hv'
      exact ⟨planCallees_of_B read_callees, ⟨cellB, 1, cellB_at, cellB_done⟩, tailOut, x₅, tail_x, tail_plan,
        tail_unrecorded⟩)
    production_completes

theorem inserted :
    Inserted ι ((ordinaryCall productionPlanRoute k shape .algorithm).runState x).2
      ((reCountValueBoundary <$> evalCounted src ctxIn envIn).runState x).2 := bridge.2

/-- Both sides return the value 0, and the plan side allocated exactly ONE cell more. -/
theorem value :
    ((ordinaryCall productionPlanRoute k shape .algorithm).runState x).1 = .ok (.atom 0, 1) ∧
    ((evalCounted src ctxIn envIn).runState x).1 = .ok (.atom 0, 1) :=
  facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem one_cell :
    ((ordinaryCall productionPlanRoute k shape .algorithm).runState x).2.needs.size =
      ((reCountValueBoundary <$> evalCounted src ctxIn envIn).runState x).2.needs.size + 1 :=
  facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

end Ancestor

/-! ## `AncestorG`: a CAPTURED-ANCESTOR PARAMETER receiver, the grouped form -/

namespace AncestorG
/-- The receiver: the parameter `r` of `POG`, read from the nested body `Inner`. -/
def args : OutputBundle := [.num 0]
def edge : Expr := .dotMember (.param "r") "Algorithm" fb none
/-- The plan's written source, as `Inner` writes it. -/
def src : Expr := .call edge args
/-- THE SOURCE PROGRAM's one row: `POG(Capture(F(0)))`, with
    `POG(r) = { Inner = Capture((r.Algorithm)(0)) ⏎ Inner }`: the parameter `r` is bound to the written
    call `Capture(F(0))`, whose VALUE is a reference. -/
def row : Expr := callN "POG" [capture (callN "F" [.num 0])]
def ctx : EvalCtx := ctxOf [row]

/-- The state the GENUINE evaluation of the row leaves, from the empty state. -/
def fin : EvalState := ((evalCounted row ctx []).runState EvalState.empty).2
/-- The plan cell: the cell the program's result — `Inner`'s captured reference — names. -/
def k : Nat := match ((evalCounted row ctx []).runState EvalState.empty).1 with | .ok (.callRef a, _) => a | _ => 0
/-- THE GENUINE CAPTURED-ANCESTOR CONTEXT: the context the source binder built for `Inner`'s body,
    read off the plan cell's suspension. Its head is `Inner`; `r` is `POG`'s parameter. -/
def ctxIn : EvalCtx := match fin.needs[k]? with | some { suspension := .expression _ c _, .. } => c | _ => ctx
def envIn : ValEnv := match fin.needs[k]? with | some { suspension := .expression _ _ v, .. } => v | _ => []
def shape : NeedPlan.CallShape := groupedShape (.param "r") fb args ctxIn envIn

def entry : EvalState := withState k .evaluating fin
def entryCell : NeedCell := { suspension := .expression src ctxIn envIn, state := .evaluating }
def ca : NeedCell := { suspension := .expression src ctxIn envIn, state := .evaluating, route := some .algorithm }
def probed : EvalState := ((algorithmIntrinsicRoute (.param "r") ctxIn).runState entry).2
/-- THE COMPARISON STATE: the plan's flight. -/
def x : EvalState := withRoute k .algorithm probed
/-- The parameter's supplied cell, found through the captured activation. -/
def b : Nat := (KatLang.MemberStability.parameterAddressIn x.lexicalActivations "r" ctxIn).getD 0
def recvOut : Except Error Result := ((invocationReceiverValue (.param "r") ctxIn envIn).runState x).1
def x₄ : EvalState := ((invocationReceiverValue (.param "r") ctxIn envIn).runState x).2
def recvVal : Result := match recvOut with | .ok v => v | .error _ => .atom 0
def refAddr : Nat := match recvVal with | .callRef a => a | _ => 0
/-- The plan side's ONE inserted cell: its callee link, whose receiver is the parameter's own cell. -/
abbrev ι : Insertion := paramInsertion x.needs.size k edge ctxIn envIn b
/-- After production's read the parameter's cell holds the read VALUE (memo sharing: the plan side's
    link reads the same cell). -/
def cellB : NeedCell := match x₄.needs[b]? with | some c => c | none => { suspension := .ready (.atom 0, 0) }
def tailOut : Except Error CountedResult := ((algorithmOfValue recvVal (some args) ctxIn envIn).runState x₄).1
def x₅ : EvalState := ((algorithmOfValue recvVal (some args) ctxIn envIn).runState x₄).2
/-- EVERY evaluated fact of this instance, in ONE proof-producing evaluation (`cbv`); the theorems
    below are its projections. -/
theorem facts :
    ((evalCounted row ctx []).runState EvalState.empty = (.ok (.callRef k, 1), fin)) ∧
    ((evalProgramOutput (wireToCaller base (rootOf [row])) base []).runState EvalState.empty = (.ok (.callRef k), fin)) ∧
    (fin.needs[k]? = some { suspension := .expression src ctxIn envIn }) ∧
    ((ctxIn.head?.map fun site => site.params.contains "r") = some false ∧ (KatLang.MemberStability.capturedId? "r" ctxIn).isSome = true) ∧
    (entry.needs[k]? = some entryCell) ∧
    ((algorithmIntrinsicRoute (.param "r") ctxIn).runState entry = (.ok true, probed)) ∧
    (x.needs[k]? = some ca) ∧
    ((probed.needs[k]?).bind NeedCell.route = none) ∧
    ((withCtx (CtxMsg.call edge) (algorithmIntrinsicRoute (.param "r") ctxIn)).runState x = (.ok true, x)) ∧
    (((NeedPlan.executeAlong productionPlanRoute k shape .algorithm).runState x).1.isIncomplete = false) ∧
    (ctx.needEnv = []) ∧
    (ctxIn.needEnv.all (fun p => decide (p.2 < entry.needs.size)) = true) ∧
    (KatLang.MemberStability.parameterAddressIn x.lexicalActivations "r" ctxIn = some b) ∧
    (decide (b < x.needs.size) = true) ∧
    (recvOut = .ok recvVal) ∧
    (recvVal = .callRef refAddr) ∧
    ((invocationReceiverValue (.param "r") ctxIn envIn).runState (embed ι x) = (shiftExcept (shiftResult ⟨x.needs.size, 1⟩) recvOut, embed ι x₄)) ∧
    (Unrecorded k x₄) ∧
    (planCalleesB x₄ = true) ∧
    (x₄.needs[b]? = some cellB) ∧
    (cellB.state = .completed (.ok (recvVal, 1))) ∧
    ((algorithmOfValue (shiftResult ⟨x.needs.size, 1⟩ recvVal) (some args) ctxIn envIn).runState (embed ι x₄) = (shiftExcept (shiftCounted ⟨x.needs.size, 1⟩) tailOut, embed ι x₅)) ∧
    (Unrecorded k x₅) ∧
    (decide (refAddr ≠ k) = true) ∧
    (completeB ((evalCallCountedExpr edge args ctxIn envIn).runState x).1 = true) ∧
    (((ordinaryCall productionPlanRoute k shape .algorithm).runState x).1 = .ok (.atom 0, 1) ∧ ((evalCallCountedExpr edge args ctxIn envIn).runState x).1 = .ok (.atom 0, 1)) ∧
    (((ordinaryCall productionPlanRoute k shape .algorithm).runState x).2.needs.size = ((reCountValueBoundary <$> evalCallCountedExpr edge args ctxIn envIn).runState x).2.needs.size + 1) := by
  cbv
  all_goals (repeat' (first | rfl | constructor))


/-- **REACHED (1).** Production's evaluation of the source row from the empty state returns the
    reference `Inner` captured: the plan cell `k`. -/
theorem captured : (evalCounted row ctx []).runState EvalState.empty = (.ok (.callRef k, 1), fin) :=
  facts.1

/-- The same evaluation as `runResultM` enters it: the program root's zero-argument demand over the
    prelude context, from the empty state. -/
theorem program_run :
    (evalProgramOutput (wireToCaller base (rootOf [row])) base []).runState EvalState.empty =
      (.ok (.callRef k), fin) :=
  facts.2.1

/-- **REACHED (2).** Cell `k` is THE PLAN: the written source, supplied by the source program in
    `Inner`'s own context, suspended, with no route and no callee recorded. -/
theorem plan_cell : fin.needs[k]? = some { suspension := .expression src ctxIn envIn } :=
  facts.2.2.1

/-- The receiver is NOT a parameter of the site: `Inner` declares none, its ancestor `POG` owns
    `r` (the captured-ancestor read, through the recorded activation). -/
theorem captured_ancestor : (ctxIn.head?.map fun site => site.params.contains "r") = some false ∧
    (KatLang.MemberStability.capturedId? "r" ctxIn).isSome = true :=
  facts.2.2.2.1

theorem entry_cell : entry.needs[k]? = some entryCell :=
  facts.2.2.2.2.1

theorem decided_entry : (algorithmIntrinsicRoute (.param "r") ctxIn).runState entry = (.ok true, probed) :=
  facts.2.2.2.2.2.1

theorem x_cell : x.needs[k]? = some ca :=
  facts.2.2.2.2.2.2.1

theorem route_free : (probed.needs[k]?).bind NeedCell.route = none :=
  facts.2.2.2.2.2.2.2.1

/-- **REACHED (3).** `x` is the flight of the grouped plan cell. -/
theorem flight :
    (withCtx shape.ctxMsg (NeedPlan.routeOf productionPlanRoute.classify k shape)).runState entry =
      (.ok .algorithm, x) :=
  flight_grouped k (.param "r") fb args ctxIn envIn entry probed entryCell entry_cell rfl decided_entry route_free
theorem settled :
    (withCtx (CtxMsg.call edge) (algorithmIntrinsicRoute (.param "r") ctxIn)).runState x = (.ok true, x) :=
  facts.2.2.2.2.2.2.2.2.1

theorem demand_done :
    ((NeedPlan.executeAlong productionPlanRoute k shape .algorithm).runState x).1.isIncomplete = false :=
  facts.2.2.2.2.2.2.2.2.2.1

/-- **REACHED (4).** The production VALUE demand of the plan cell from the genuine state `fin` IS the
    completion shell over the plan's `.algorithm` execution from the flight `x`. -/
theorem demand_passes :
    (demandNeed k).runState fin =
      (let res := (NeedPlan.executeAlong productionPlanRoute k shape .algorithm).runState x
       (res.1, withState k (.completed res.1) res.2)) :=
  demand_passes_flight k fin x _ src ctxIn envIn shape .algorithm plan_cell rfl rfl rfl flight nofun demand_done

theorem ctx_needEnv : ctx.needEnv = [] :=
  facts.2.2.2.2.2.2.2.2.2.2.1

theorem ctx_valid (h : Array NeedCell) : ValidCtx h ctx := validCtx_nil h ctx ctx_needEnv
theorem ctxIn_all : ctxIn.needEnv.all (fun p => decide (p.2 < entry.needs.size)) = true :=
  facts.2.2.2.2.2.2.2.2.2.2.2.1

theorem ctxIn_valid : ValidCtx entry.needs ctxIn := validCtx_of_all ctxIn_all
theorem inv_fin : Inv fin := inv_row row ctx (ctx_valid _)
theorem inv_x : Inv x := inv_flight_of_probe inv_fin k (.algorithmIntrinsicRoute (.param "r") ctxIn) decided_entry ctxIn_valid

theorem bound : KatLang.MemberStability.parameterAddressIn x.lexicalActivations "r" ctxIn = some b :=
  facts.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem bound_lt : b < x.needs.size :=
  of_decide_eq_true facts.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-! ### Production's receiver read, and the plan side's (ONE inserted cell) -/

theorem recv_ok : recvOut = .ok recvVal :=
  facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- **The actual receiver read returns a call reference.** -/
theorem recv_reference : recvVal = .callRef refAddr :=
  facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem read_x : (invocationReceiverValue (.param "r") ctxIn envIn).runState x = (recvOut, x₄) := rfl
theorem read_plan : (invocationReceiverValue (.param "r") ctxIn envIn).runState (embed ι x) =
    (shiftExcept (shiftResult ⟨x.needs.size, 1⟩) recvOut, embed ι x₄) :=
  facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem read_unrecorded : Unrecorded k x₄ :=
  facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem read_callees : planCalleesB x₄ = true :=
  facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem cellB_at : x₄.needs[b]? = some cellB :=
  facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem cellB_done : cellB.state = .completed (.ok (recvVal, 1)) :=
  facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-! ### The admissible tail entry, production's tail and the plan side's -/

theorem tail_x : (algorithmOfValue recvVal (some args) ctxIn envIn).runState x₄ = (tailOut, x₅) := rfl
theorem tail_plan :
    (algorithmOfValue (shiftResult ⟨x.needs.size, 1⟩ recvVal) (some args) ctxIn envIn).runState (embed ι x₄) =
      (shiftExcept (shiftCounted ⟨x.needs.size, 1⟩) tailOut, embed ι x₅) :=
  facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem tail_unrecorded : Unrecorded k x₅ :=
  facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- The plan cell's own reference is NOT the receiver's result. -/
theorem ref_ne : refAddr ≠ k :=
  of_decide_eq_true facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem not_self : recvVal ≠ .callRef k := by
  rw [recv_reference]
  intro h
  exact ref_ne (Result.callRef.inj h)

theorem production_done : completeB ((evalCallCountedExpr edge args ctxIn envIn).runState x).1 = true :=
  facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem production_completes : ProductionCompletes (evalCallCountedExpr edge args ctxIn envIn) x := complete_of_B production_done

/-- **`algorithm_bridge_grouped_param_at` APPLIED** at the plan's flight, every premise proved above. -/
theorem bridge :
    Bridged ι
      ((ordinaryCall productionPlanRoute k shape .algorithm).runState x)
      ((reCountValueBoundary <$> evalCallCountedExpr edge args ctxIn envIn).runState x) :=
  algorithm_bridge_grouped_param_at k "r" fb args ctxIn envIn x ca b settled x_cell rfl rfl rfl bound bound_lt
    inv_x recvOut x₄ read_x read_plan read_unrecorded
    (fun v hv => by
      have hv' : v = recvVal := by
        have h := recv_ok.symm.trans hv
        exact (Except.ok.inj h).symm
      subst hv'
      exact ⟨planCallees_of_B read_callees, ⟨cellB, 1, cellB_at, cellB_done⟩, tailOut, x₅, tail_x, tail_plan,
        tail_unrecorded⟩)
    production_completes

theorem inserted :
    Inserted ι ((ordinaryCall productionPlanRoute k shape .algorithm).runState x).2
      ((reCountValueBoundary <$> evalCallCountedExpr edge args ctxIn envIn).runState x).2 := bridge.2

/-- Both sides return the value 0, and the plan side allocated exactly ONE cell more. -/
theorem value :
    ((ordinaryCall productionPlanRoute k shape .algorithm).runState x).1 = .ok (.atom 0, 1) ∧
    ((evalCallCountedExpr edge args ctxIn envIn).runState x).1 = .ok (.atom 0, 1) :=
  facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem one_cell :
    ((ordinaryCall productionPlanRoute k shape .algorithm).runState x).2.needs.size =
      ((reCountValueBoundary <$> evalCallCountedExpr edge args ctxIn envIn).runState x).2.needs.size + 1 :=
  facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

end AncestorG

end KatLang.PlanAlgorithmBridgeInstances.Source
