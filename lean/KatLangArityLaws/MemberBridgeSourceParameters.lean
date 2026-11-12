import KatLangArityLaws.MemberBridgeSourceInstances

/-!
# The member bridge applied: parameter receivers and parameter-rooted paths (E-18 step 1, M1)

`ParamEmpty` (`b.V()`), `ParamRefSpreadNone` (`b.V(()*)` with `b` bound to a transparent reference),
`ParamPathEmpty` (`b.Sub.K()`), `ParamSpreadFails`: the plan is written in the body of `P…(b)`, in the
context the source program's own binder built; the probe is the parameter's FIRST CALLABLE
projection (`probe_wrote`), read back from its memo by every later navigation.

Every instance is the proof script of `MemberBridgeSourceInstances` (see its header for the method
and for what "reached" means): the source program with one root row, its genuine evaluation from the
empty state (`captured`, `program_run`), the plan cell (`plan_cell`), its flight (`flight`), the VALUE
demand passing through that flight (`demand_passes`), every premise of the member bridge — the
settled probe, the selection, the plan's projection, the receiver's navigation at the state the
callee origin is read in — and the theorem APPLIED (`bridge`).
-/

open KatLang KatLang.CallPlan KatLang.EvaluatorCore KatLang.PlanRouteBridge KatLang.MemberStability
open KatLang.PlanAlgorithmBridgeInstances (completeB complete_of_B)
open KatLang.PlanAlgorithmBridgeInstances.Source (demand_passes_flight)

namespace KatLang.MemberStabilityInstances

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option cbv.maxSteps 20000000

/-! ## `ParamEmpty`: `b.V()` inside `PV(b)`, called as `PV(Box)` — a PARAMETER receiver, empty bundle -/

namespace ParamEmpty
/-- The receiver is the parameter `b`, bound to `Box`: the probe is its FIRST CALLABLE projection. -/
def target : Expr := .param "b"
def N : Ident := "V"
def args : OutputBundle := []
def path : Expr := .dotMember target N (.resolve N) none
def src : Expr := .dotMember target N (.resolve N) (some args)
/-- THE SOURCE PROGRAM's one row: `PV(Box)`, with `PV(b) = Capture(b.V())`. -/
def row : Expr := callN "PV" [.resolve "Box"]
def ctx : EvalCtx := ctxOf [row]

def fin : EvalState := ((evalCounted row ctx []).runState EvalState.empty).2
/-- The plan cell: the cell the program's result names. -/
def k : Nat := match ((evalCounted row ctx []).runState EvalState.empty).1 with | .ok (.callRef a, _) => a | _ => 0
/-- THE GENUINE PARAMETER CONTEXT: the context the source binder built for `PV`'s body, read off
    the plan cell's suspension. -/
def ctxIn : EvalCtx := match fin.needs[k]? with | some { suspension := .expression _ c _, .. } => c | _ => ctx
def envIn : ValEnv := match fin.needs[k]? with | some { suspension := .expression _ _ v, .. } => v | _ => []
def shape : NeedPlan.CallShape := ⟨path, args, ctxIn, envIn, .dot target N (.resolve N)⟩

def entry : EvalState := withState k .evaluating fin
def entryCell : NeedCell := { suspension := .expression src ctxIn envIn, state := .evaluating }
/-- The parameter's supplied cell. -/
def b : Nat := (parameterAddressIn fin.lexicalActivations "b" ctxIn).getD 0
def alg? : Option Algorithm :=
  match ((resolveDotReceiver? target ctxIn).runState entry).1 with
  | .ok a => a
  | .error _ => none
/-- The probe's exit state: the parameter's FIRST CALLABLE projection wrote its memo. -/
def probed : EvalState := ((resolveDotReceiver? target ctxIn).runState entry).2
def owner : Algorithm := alg?.getD (alg [] [] [] [])
def p : PropDef := (Algorithm.lookupPropDefAny? owner N).getD { name := N, alg := owner, isPublic := false }
def x : EvalState := withRoute k .call probed
def tA : EvalState := ((resolveAliasTarget (childOfInContext owner p.alg ctxIn) ctxIn).runState x).2
def uF : EvalState := ((NeedSupply.form evalSupplySpread ctxIn envIn args).runState tA).2
/-- EVERY evaluated fact of this instance, in ONE proof-producing evaluation (`cbv`); the theorems
    below are its projections. -/
theorem facts :
    ((evalCounted row ctx []).runState EvalState.empty = (.ok (.callRef k, 1), fin)) ∧
    ((evalProgramOutput (wireToCaller base (rootOf [row])) base []).runState EvalState.empty = (.ok (.callRef k), fin)) ∧
    (fin.needs[k]? = some { suspension := .expression src ctxIn envIn }) ∧
    (entry.needs[k]? = some entryCell) ∧
    ((resolveDotReceiver? target ctxIn).runState entry = (.ok alg?, probed)) ∧
    ((entry.needs[b]?.map fun c => match c.callable with | .unprojected => true | _ => false) = some true ∧ (probed.needs[b]?.map fun c => match c.callable with | .projected (.ok (some _)) => true | _ => false) = some true) ∧
    (alg? = some owner) ∧
    (selectDotEdge ctxIn target N alg? = .ok (.member owner p)) ∧
    ((probed.needs[k]?).bind NeedCell.route = none) ∧
    (((NeedPlan.executeAlong productionPlanRoute k shape .call).runState x).1.isIncomplete = false) ∧
    ((resolveDotReceiver? target ctxIn).runState x = (.ok alg?, x)) ∧
    (x.nextRuntimeDeclaration = fin.nextRuntimeDeclaration) ∧
    ((projectNeedStructuralMember path ctxIn).runState x = (.ok (some (childOfInContext owner p.alg ctxIn)), x)) ∧
    ((projectedStructure target ctxIn).runState uF = (.ok (some owner), uF)) ∧
    (completeB ((evalCounted src ctxIn envIn).runState x).1 = true) ∧
    (((ordinaryCall productionPlanRoute k shape .call).runState x).1 = .ok (.atom 7, 1)) ∧
    (((ordinaryCall productionPlanRoute k shape .call).runState x).2.zeroArgPropertyCache.length = x.zeroArgPropertyCache.length + 1) := by
  cbv
  all_goals (repeat' (first | rfl | constructor))


theorem captured : (evalCounted row ctx []).runState EvalState.empty = (.ok (.callRef k, 1), fin) :=
  facts.1

theorem program_run :
    (evalProgramOutput (wireToCaller base (rootOf [row])) base []).runState EvalState.empty =
      (.ok (.callRef k), fin) :=
  facts.2.1

theorem plan_cell : fin.needs[k]? = some { suspension := .expression src ctxIn envIn } :=
  facts.2.2.1

theorem entry_cell : entry.needs[k]? = some entryCell :=
  facts.2.2.2.1

theorem probe_entry : (resolveDotReceiver? target ctxIn).runState entry = (.ok alg?, probed) :=
  facts.2.2.2.2.1

/-- The probe WROTE: the first navigation of a parameter receiver is not state-inert — the
    parameter's cell was unprojected, and holds the projection's memo afterwards. -/
theorem probe_wrote :
    (entry.needs[b]?.map fun c => match c.callable with | .unprojected => true | _ => false) = some true ∧
    (probed.needs[b]?.map fun c =>
      match c.callable with | .projected (.ok (some _)) => true | _ => false) = some true :=
  facts.2.2.2.2.2.1

theorem probe_owner : alg? = some owner :=
  facts.2.2.2.2.2.2.1

theorem selected : selectDotEdge ctxIn target N alg? = .ok (.member owner p) :=
  facts.2.2.2.2.2.2.2.1

theorem route_free : (probed.needs[k]?).bind NeedCell.route = none :=
  facts.2.2.2.2.2.2.2.2.1

theorem flight :
    (withCtx shape.ctxMsg (NeedPlan.routeOf productionPlanRoute.classify k shape)).runState entry =
      (.ok .call, x) :=
  flight_member k target N (.resolve N) args ctxIn envIn entry probed entryCell alg? _ entry_cell rfl probe_entry
    selected route_free
theorem demand_done :
    ((NeedPlan.executeAlong productionPlanRoute k shape .call).runState x).1.isIncomplete = false :=
  facts.2.2.2.2.2.2.2.2.2.1

theorem demand_passes :
    (demandNeed k).runState fin =
      (let res := (NeedPlan.executeAlong productionPlanRoute k shape .call).runState x
       (res.1, withState k (.completed res.1) res.2)) :=
  demand_passes_flight k fin x _ src ctxIn envIn shape .call plan_cell rfl rfl rfl flight nofun demand_done

theorem probe_x : (resolveDotReceiver? target ctxIn).runState x = (.ok alg?, x) :=
  facts.2.2.2.2.2.2.2.2.2.2.1

theorem not_minted : x.nextRuntimeDeclaration = fin.nextRuntimeDeclaration :=
  facts.2.2.2.2.2.2.2.2.2.2.2.1

theorem projection_x :
    (projectNeedStructuralMember path ctxIn).runState x = (.ok (some (childOfInContext owner p.alg ctxIn)), x) :=
  facts.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem settled_at_origin : (projectedStructure target ctxIn).runState uF = (.ok (some owner), uF) :=
  facts.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem settled_origin : ∀ g t cells u,
    (resolveAliasTarget (childOfInContext owner p.alg ctxIn) ctxIn).runState x = (.ok g, t) →
    (NeedSupply.form evalSupplySpread ctxIn envIn args).runState t = (.ok cells, u) →
    (projectedStructure target ctxIn).runState u = (.ok (some owner), u) := by
  intro g t cells u hr hf
  have ht : tA = t := congrArg Prod.snd hr
  subst ht
  have hu : uF = u := congrArg Prod.snd hf
  subst hu
  exact settled_at_origin

theorem production_done : completeB ((evalCounted src ctxIn envIn).runState x).1 = true :=
  facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem production_completes : ProductionCompletes (evalCounted src ctxIn envIn) x :=
  complete_of_B production_done

/-- **`member_bridge_settled` APPLIED** at the plan's flight, every premise proved above. -/
theorem bridge :
    (ordinaryCall productionPlanRoute k shape .call).runState x =
      (reCountValueBoundary <$> evalCounted src ctxIn envIn).runState x :=
  member_bridge_settled k target N (.resolve N) args ctxIn envIn x x alg? owner p probe_x selected projection_x
    settled_origin production_completes

/-- Both sides return the value 7. -/
theorem value : ((ordinaryCall productionPlanRoute k shape .call).runState x).1 = .ok (.atom 7, 1) :=
  facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- The zero-supply invocation PUBLISHED the member's cache entry (CACHE-PUB-1) — on both sides, by
    `bridge`. -/
theorem published :
    ((ordinaryCall productionPlanRoute k shape .call).runState x).2.zeroArgPropertyCache.length =
      x.zeroArgPropertyCache.length + 1 :=
  facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

end ParamEmpty

/-! ## `ParamRefSpreadNone`: `b.V(()*)` inside `PS(b)`, called as `PS(AB)` — a parameter bound to a TRANSPARENT REFERENCE, spread-first bundle forming no cell -/

namespace ParamRefSpreadNone
/-- The parameter `b` is bound to `AB = Box`: its projected CALLABLE is the reference's structure. -/
def target : Expr := .param "b"
def N : Ident := "V"
def args : OutputBundle := [.sequenceSpread (.emptySequence 0)]
def path : Expr := .dotMember target N (.resolve N) none
def src : Expr := .dotMember target N (.resolve N) (some args)
/-- THE SOURCE PROGRAM's one row: `PS(AB)`, with `PS(b) = Capture(b.V(()*))`. -/
def row : Expr := callN "PS" [.resolve "AB"]
def ctx : EvalCtx := ctxOf [row]

def fin : EvalState := ((evalCounted row ctx []).runState EvalState.empty).2
/-- The plan cell: the cell the program's result names. -/
def k : Nat := match ((evalCounted row ctx []).runState EvalState.empty).1 with | .ok (.callRef a, _) => a | _ => 0
/-- THE GENUINE PARAMETER CONTEXT: the context the source binder built for `PS`'s body, read off
    the plan cell's suspension. -/
def ctxIn : EvalCtx := match fin.needs[k]? with | some { suspension := .expression _ c _, .. } => c | _ => ctx
def envIn : ValEnv := match fin.needs[k]? with | some { suspension := .expression _ _ v, .. } => v | _ => []
def shape : NeedPlan.CallShape := ⟨path, args, ctxIn, envIn, .dot target N (.resolve N)⟩

def entry : EvalState := withState k .evaluating fin
def entryCell : NeedCell := { suspension := .expression src ctxIn envIn, state := .evaluating }
/-- The parameter's supplied cell. -/
def b : Nat := (parameterAddressIn fin.lexicalActivations "b" ctxIn).getD 0
def alg? : Option Algorithm :=
  match ((resolveDotReceiver? target ctxIn).runState entry).1 with
  | .ok a => a
  | .error _ => none
/-- The probe's exit state: the parameter's FIRST CALLABLE projection wrote its memo. -/
def probed : EvalState := ((resolveDotReceiver? target ctxIn).runState entry).2
def owner : Algorithm := alg?.getD (alg [] [] [] [])
def p : PropDef := (Algorithm.lookupPropDefAny? owner N).getD { name := N, alg := owner, isPublic := false }
def x : EvalState := withRoute k .call probed
def tA : EvalState := ((resolveAliasTarget (childOfInContext owner p.alg ctxIn) ctxIn).runState x).2
def uF : EvalState := ((NeedSupply.form evalSupplySpread ctxIn envIn args).runState tA).2
/-- EVERY evaluated fact of this instance, in ONE proof-producing evaluation (`cbv`); the theorems
    below are its projections. -/
theorem facts :
    ((evalCounted row ctx []).runState EvalState.empty = (.ok (.callRef k, 1), fin)) ∧
    ((evalProgramOutput (wireToCaller base (rootOf [row])) base []).runState EvalState.empty = (.ok (.callRef k), fin)) ∧
    (fin.needs[k]? = some { suspension := .expression src ctxIn envIn }) ∧
    (entry.needs[k]? = some entryCell) ∧
    ((resolveDotReceiver? target ctxIn).runState entry = (.ok alg?, probed)) ∧
    ((entry.needs[b]?.map fun c => match c.callable with | .unprojected => true | _ => false) = some true ∧ (probed.needs[b]?.map fun c => match c.callable with | .projected (.ok (some _)) => true | _ => false) = some true) ∧
    (alg? = some owner) ∧
    (selectDotEdge ctxIn target N alg? = .ok (.member owner p)) ∧
    ((probed.needs[k]?).bind NeedCell.route = none) ∧
    (((NeedPlan.executeAlong productionPlanRoute k shape .call).runState x).1.isIncomplete = false) ∧
    ((resolveDotReceiver? target ctxIn).runState x = (.ok alg?, x)) ∧
    (x.nextRuntimeDeclaration = fin.nextRuntimeDeclaration) ∧
    ((projectNeedStructuralMember path ctxIn).runState x = (.ok (some (childOfInContext owner p.alg ctxIn)), x)) ∧
    ((projectedStructure target ctxIn).runState uF = (.ok (some owner), uF)) ∧
    (completeB ((evalCounted src ctxIn envIn).runState x).1 = true) ∧
    (((ordinaryCall productionPlanRoute k shape .call).runState x).1 = .ok (.atom 7, 1)) ∧
    (((NeedSupply.form evalSupplySpread ctxIn envIn args).runState tA).1.toOption.map List.length = some 0) ∧
    (((ordinaryCall productionPlanRoute k shape .call).runState x).2.zeroArgPropertyCache.length = x.zeroArgPropertyCache.length + 1) := by
  cbv
  all_goals (repeat' (first | rfl | constructor))


theorem captured : (evalCounted row ctx []).runState EvalState.empty = (.ok (.callRef k, 1), fin) :=
  facts.1

theorem program_run :
    (evalProgramOutput (wireToCaller base (rootOf [row])) base []).runState EvalState.empty =
      (.ok (.callRef k), fin) :=
  facts.2.1

theorem plan_cell : fin.needs[k]? = some { suspension := .expression src ctxIn envIn } :=
  facts.2.2.1

theorem entry_cell : entry.needs[k]? = some entryCell :=
  facts.2.2.2.1

theorem probe_entry : (resolveDotReceiver? target ctxIn).runState entry = (.ok alg?, probed) :=
  facts.2.2.2.2.1

/-- The probe WROTE: the first navigation of a parameter receiver is not state-inert — the
    parameter's cell was unprojected, and holds the projection's memo afterwards. -/
theorem probe_wrote :
    (entry.needs[b]?.map fun c => match c.callable with | .unprojected => true | _ => false) = some true ∧
    (probed.needs[b]?.map fun c =>
      match c.callable with | .projected (.ok (some _)) => true | _ => false) = some true :=
  facts.2.2.2.2.2.1

theorem probe_owner : alg? = some owner :=
  facts.2.2.2.2.2.2.1

theorem selected : selectDotEdge ctxIn target N alg? = .ok (.member owner p) :=
  facts.2.2.2.2.2.2.2.1

theorem route_free : (probed.needs[k]?).bind NeedCell.route = none :=
  facts.2.2.2.2.2.2.2.2.1

theorem flight :
    (withCtx shape.ctxMsg (NeedPlan.routeOf productionPlanRoute.classify k shape)).runState entry =
      (.ok .call, x) :=
  flight_member k target N (.resolve N) args ctxIn envIn entry probed entryCell alg? _ entry_cell rfl probe_entry
    selected route_free
theorem demand_done :
    ((NeedPlan.executeAlong productionPlanRoute k shape .call).runState x).1.isIncomplete = false :=
  facts.2.2.2.2.2.2.2.2.2.1

theorem demand_passes :
    (demandNeed k).runState fin =
      (let res := (NeedPlan.executeAlong productionPlanRoute k shape .call).runState x
       (res.1, withState k (.completed res.1) res.2)) :=
  demand_passes_flight k fin x _ src ctxIn envIn shape .call plan_cell rfl rfl rfl flight nofun demand_done

theorem probe_x : (resolveDotReceiver? target ctxIn).runState x = (.ok alg?, x) :=
  facts.2.2.2.2.2.2.2.2.2.2.1

theorem not_minted : x.nextRuntimeDeclaration = fin.nextRuntimeDeclaration :=
  facts.2.2.2.2.2.2.2.2.2.2.2.1

theorem projection_x :
    (projectNeedStructuralMember path ctxIn).runState x = (.ok (some (childOfInContext owner p.alg ctxIn)), x) :=
  facts.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem settled_at_origin : (projectedStructure target ctxIn).runState uF = (.ok (some owner), uF) :=
  facts.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem settled_origin : ∀ g t cells u,
    (resolveAliasTarget (childOfInContext owner p.alg ctxIn) ctxIn).runState x = (.ok g, t) →
    (NeedSupply.form evalSupplySpread ctxIn envIn args).runState t = (.ok cells, u) →
    (projectedStructure target ctxIn).runState u = (.ok (some owner), u) := by
  intro g t cells u hr hf
  have ht : tA = t := congrArg Prod.snd hr
  subst ht
  have hu : uF = u := congrArg Prod.snd hf
  subst hu
  exact settled_at_origin

theorem production_done : completeB ((evalCounted src ctxIn envIn).runState x).1 = true :=
  facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem production_completes : ProductionCompletes (evalCounted src ctxIn envIn) x :=
  complete_of_B production_done

/-- **`member_bridge_settled` APPLIED** at the plan's flight, every premise proved above. -/
theorem bridge :
    (ordinaryCall productionPlanRoute k shape .call).runState x =
      (reCountValueBoundary <$> evalCounted src ctxIn envIn).runState x :=
  member_bridge_settled k target N (.resolve N) args ctxIn envIn x x alg? owner p probe_x selected projection_x
    settled_origin production_completes

/-- Both sides return the value 7. -/
theorem value : ((ordinaryCall productionPlanRoute k shape .call).runState x).1 = .ok (.atom 7, 1) :=
  facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- The supply formation runs the spread and forms no cell. -/
theorem formation :
    ((NeedSupply.form evalSupplySpread ctxIn envIn args).runState tA).1.toOption.map List.length = some 0 :=
  facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- The zero-supply invocation PUBLISHED the member's cache entry (CACHE-PUB-1) — on both sides, by
    `bridge`. -/
theorem published :
    ((ordinaryCall productionPlanRoute k shape .call).runState x).2.zeroArgPropertyCache.length =
      x.zeroArgPropertyCache.length + 1 :=
  facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

end ParamRefSpreadNone

/-! ## `ParamPathEmpty`: `b.Sub.K()` inside `PK(b)`, called as `PK(Lib)` — a PARAMETER-ROOTED PATH, empty bundle -/

namespace ParamPathEmpty
/-- The receiver `b.Sub` is a member path rooted at the parameter `b`, bound to `Lib`. -/
def target : Expr := (.dotMember (.param "b") "Sub" (.resolve "Sub") none)
def N : Ident := "K"
def args : OutputBundle := []
def path : Expr := .dotMember target N (.resolve N) none
def src : Expr := .dotMember target N (.resolve N) (some args)
/-- THE SOURCE PROGRAM's one row: `PK(Lib)`, with `PK(b) = Capture(b.Sub.K())`. -/
def row : Expr := callN "PK" [.resolve "Lib"]
def ctx : EvalCtx := ctxOf [row]

def fin : EvalState := ((evalCounted row ctx []).runState EvalState.empty).2
/-- The plan cell: the cell the program's result names. -/
def k : Nat := match ((evalCounted row ctx []).runState EvalState.empty).1 with | .ok (.callRef a, _) => a | _ => 0
/-- THE GENUINE PARAMETER CONTEXT: the context the source binder built for `PK`'s body, read off
    the plan cell's suspension. -/
def ctxIn : EvalCtx := match fin.needs[k]? with | some { suspension := .expression _ c _, .. } => c | _ => ctx
def envIn : ValEnv := match fin.needs[k]? with | some { suspension := .expression _ _ v, .. } => v | _ => []
def shape : NeedPlan.CallShape := ⟨path, args, ctxIn, envIn, .dot target N (.resolve N)⟩

def entry : EvalState := withState k .evaluating fin
def entryCell : NeedCell := { suspension := .expression src ctxIn envIn, state := .evaluating }
/-- The parameter's supplied cell. -/
def b : Nat := (parameterAddressIn fin.lexicalActivations "b" ctxIn).getD 0
def alg? : Option Algorithm :=
  match ((resolveDotReceiver? target ctxIn).runState entry).1 with
  | .ok a => a
  | .error _ => none
/-- The probe's exit state: the parameter's FIRST CALLABLE projection wrote its memo. -/
def probed : EvalState := ((resolveDotReceiver? target ctxIn).runState entry).2
def owner : Algorithm := alg?.getD (alg [] [] [] [])
def p : PropDef := (Algorithm.lookupPropDefAny? owner N).getD { name := N, alg := owner, isPublic := false }
def x : EvalState := withRoute k .call probed
def tA : EvalState := ((resolveAliasTarget (childOfInContext owner p.alg ctxIn) ctxIn).runState x).2
def uF : EvalState := ((NeedSupply.form evalSupplySpread ctxIn envIn args).runState tA).2
/-- EVERY evaluated fact of this instance, in ONE proof-producing evaluation (`cbv`); the theorems
    below are its projections. -/
theorem facts :
    ((evalCounted row ctx []).runState EvalState.empty = (.ok (.callRef k, 1), fin)) ∧
    ((evalProgramOutput (wireToCaller base (rootOf [row])) base []).runState EvalState.empty = (.ok (.callRef k), fin)) ∧
    (fin.needs[k]? = some { suspension := .expression src ctxIn envIn }) ∧
    (entry.needs[k]? = some entryCell) ∧
    ((resolveDotReceiver? target ctxIn).runState entry = (.ok alg?, probed)) ∧
    ((entry.needs[b]?.map fun c => match c.callable with | .unprojected => true | _ => false) = some true ∧ (probed.needs[b]?.map fun c => match c.callable with | .projected (.ok (some _)) => true | _ => false) = some true) ∧
    (alg? = some owner) ∧
    (selectDotEdge ctxIn target N alg? = .ok (.member owner p)) ∧
    ((probed.needs[k]?).bind NeedCell.route = none) ∧
    (((NeedPlan.executeAlong productionPlanRoute k shape .call).runState x).1.isIncomplete = false) ∧
    ((resolveDotReceiver? target ctxIn).runState x = (.ok alg?, x)) ∧
    (x.nextRuntimeDeclaration = fin.nextRuntimeDeclaration) ∧
    ((projectNeedStructuralMember path ctxIn).runState x = (.ok (some (childOfInContext owner p.alg ctxIn)), x)) ∧
    ((projectedStructure target ctxIn).runState uF = (.ok (some owner), uF)) ∧
    (completeB ((evalCounted src ctxIn envIn).runState x).1 = true) ∧
    (((ordinaryCall productionPlanRoute k shape .call).runState x).1 = .ok (.atom 3, 1)) ∧
    (((ordinaryCall productionPlanRoute k shape .call).runState x).2.zeroArgPropertyCache.length = x.zeroArgPropertyCache.length + 1) := by
  cbv
  all_goals (repeat' (first | rfl | constructor))


theorem captured : (evalCounted row ctx []).runState EvalState.empty = (.ok (.callRef k, 1), fin) :=
  facts.1

theorem program_run :
    (evalProgramOutput (wireToCaller base (rootOf [row])) base []).runState EvalState.empty =
      (.ok (.callRef k), fin) :=
  facts.2.1

theorem plan_cell : fin.needs[k]? = some { suspension := .expression src ctxIn envIn } :=
  facts.2.2.1

theorem entry_cell : entry.needs[k]? = some entryCell :=
  facts.2.2.2.1

theorem probe_entry : (resolveDotReceiver? target ctxIn).runState entry = (.ok alg?, probed) :=
  facts.2.2.2.2.1

/-- The probe WROTE: the first navigation of a parameter receiver is not state-inert — the
    parameter's cell was unprojected, and holds the projection's memo afterwards. -/
theorem probe_wrote :
    (entry.needs[b]?.map fun c => match c.callable with | .unprojected => true | _ => false) = some true ∧
    (probed.needs[b]?.map fun c =>
      match c.callable with | .projected (.ok (some _)) => true | _ => false) = some true :=
  facts.2.2.2.2.2.1

theorem probe_owner : alg? = some owner :=
  facts.2.2.2.2.2.2.1

theorem selected : selectDotEdge ctxIn target N alg? = .ok (.member owner p) :=
  facts.2.2.2.2.2.2.2.1

theorem route_free : (probed.needs[k]?).bind NeedCell.route = none :=
  facts.2.2.2.2.2.2.2.2.1

theorem flight :
    (withCtx shape.ctxMsg (NeedPlan.routeOf productionPlanRoute.classify k shape)).runState entry =
      (.ok .call, x) :=
  flight_member k target N (.resolve N) args ctxIn envIn entry probed entryCell alg? _ entry_cell rfl probe_entry
    selected route_free
theorem demand_done :
    ((NeedPlan.executeAlong productionPlanRoute k shape .call).runState x).1.isIncomplete = false :=
  facts.2.2.2.2.2.2.2.2.2.1

theorem demand_passes :
    (demandNeed k).runState fin =
      (let res := (NeedPlan.executeAlong productionPlanRoute k shape .call).runState x
       (res.1, withState k (.completed res.1) res.2)) :=
  demand_passes_flight k fin x _ src ctxIn envIn shape .call plan_cell rfl rfl rfl flight nofun demand_done

theorem probe_x : (resolveDotReceiver? target ctxIn).runState x = (.ok alg?, x) :=
  facts.2.2.2.2.2.2.2.2.2.2.1

theorem not_minted : x.nextRuntimeDeclaration = fin.nextRuntimeDeclaration :=
  facts.2.2.2.2.2.2.2.2.2.2.2.1

theorem projection_x :
    (projectNeedStructuralMember path ctxIn).runState x = (.ok (some (childOfInContext owner p.alg ctxIn)), x) :=
  facts.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem settled_at_origin : (projectedStructure target ctxIn).runState uF = (.ok (some owner), uF) :=
  facts.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem settled_origin : ∀ g t cells u,
    (resolveAliasTarget (childOfInContext owner p.alg ctxIn) ctxIn).runState x = (.ok g, t) →
    (NeedSupply.form evalSupplySpread ctxIn envIn args).runState t = (.ok cells, u) →
    (projectedStructure target ctxIn).runState u = (.ok (some owner), u) := by
  intro g t cells u hr hf
  have ht : tA = t := congrArg Prod.snd hr
  subst ht
  have hu : uF = u := congrArg Prod.snd hf
  subst hu
  exact settled_at_origin

theorem production_done : completeB ((evalCounted src ctxIn envIn).runState x).1 = true :=
  facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem production_completes : ProductionCompletes (evalCounted src ctxIn envIn) x :=
  complete_of_B production_done

/-- **`member_bridge_settled` APPLIED** at the plan's flight, every premise proved above. -/
theorem bridge :
    (ordinaryCall productionPlanRoute k shape .call).runState x =
      (reCountValueBoundary <$> evalCounted src ctxIn envIn).runState x :=
  member_bridge_settled k target N (.resolve N) args ctxIn envIn x x alg? owner p probe_x selected projection_x
    settled_origin production_completes

/-- Both sides return the value 3. -/
theorem value : ((ordinaryCall productionPlanRoute k shape .call).runState x).1 = .ok (.atom 3, 1) :=
  facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- The zero-supply invocation PUBLISHED the member's cache entry (CACHE-PUB-1) — on both sides, by
    `bridge`. -/
theorem published :
    ((ordinaryCall productionPlanRoute k shape .call).runState x).2.zeroArgPropertyCache.length =
      x.zeroArgPropertyCache.length + 1 :=
  facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

end ParamPathEmpty

/-! ## `ParamSpreadFails`: `b.G((1 / 0)*)` inside `PF(b)`, called as `PF(Box)` — a parameter receiver, a failing spread -/

namespace ParamSpreadFails
/-- The formation fails after the parameter's projection. -/
def target : Expr := .param "b"
def N : Ident := "G"
def args : OutputBundle := [.sequenceSpread (.binary .div (.num 1) (.num 0))]
def path : Expr := .dotMember target N (.resolve N) none
def src : Expr := .dotMember target N (.resolve N) (some args)
/-- THE SOURCE PROGRAM's one row: `PF(Box)`, with `PF(b) = Capture(b.G((1 / 0)*))`. -/
def row : Expr := callN "PF" [.resolve "Box"]
def ctx : EvalCtx := ctxOf [row]

def fin : EvalState := ((evalCounted row ctx []).runState EvalState.empty).2
/-- The plan cell: the cell the program's result names. -/
def k : Nat := match ((evalCounted row ctx []).runState EvalState.empty).1 with | .ok (.callRef a, _) => a | _ => 0
/-- THE GENUINE PARAMETER CONTEXT: the context the source binder built for `PF`'s body, read off
    the plan cell's suspension. -/
def ctxIn : EvalCtx := match fin.needs[k]? with | some { suspension := .expression _ c _, .. } => c | _ => ctx
def envIn : ValEnv := match fin.needs[k]? with | some { suspension := .expression _ _ v, .. } => v | _ => []
def shape : NeedPlan.CallShape := ⟨path, args, ctxIn, envIn, .dot target N (.resolve N)⟩

def entry : EvalState := withState k .evaluating fin
def entryCell : NeedCell := { suspension := .expression src ctxIn envIn, state := .evaluating }
/-- The parameter's supplied cell. -/
def b : Nat := (parameterAddressIn fin.lexicalActivations "b" ctxIn).getD 0
def alg? : Option Algorithm :=
  match ((resolveDotReceiver? target ctxIn).runState entry).1 with
  | .ok a => a
  | .error _ => none
/-- The probe's exit state: the parameter's FIRST CALLABLE projection wrote its memo. -/
def probed : EvalState := ((resolveDotReceiver? target ctxIn).runState entry).2
def owner : Algorithm := alg?.getD (alg [] [] [] [])
def p : PropDef := (Algorithm.lookupPropDefAny? owner N).getD { name := N, alg := owner, isPublic := false }
def x : EvalState := withRoute k .call probed
def tA : EvalState := ((resolveAliasTarget (childOfInContext owner p.alg ctxIn) ctxIn).runState x).2
def uF : EvalState := ((NeedSupply.form evalSupplySpread ctxIn envIn args).runState tA).2
/-- EVERY evaluated fact of this instance, in ONE proof-producing evaluation (`cbv`); the theorems
    below are its projections. -/
theorem facts :
    ((evalCounted row ctx []).runState EvalState.empty = (.ok (.callRef k, 1), fin)) ∧
    ((evalProgramOutput (wireToCaller base (rootOf [row])) base []).runState EvalState.empty = (.ok (.callRef k), fin)) ∧
    (fin.needs[k]? = some { suspension := .expression src ctxIn envIn }) ∧
    (entry.needs[k]? = some entryCell) ∧
    ((resolveDotReceiver? target ctxIn).runState entry = (.ok alg?, probed)) ∧
    ((entry.needs[b]?.map fun c => match c.callable with | .unprojected => true | _ => false) = some true ∧ (probed.needs[b]?.map fun c => match c.callable with | .projected (.ok (some _)) => true | _ => false) = some true) ∧
    (alg? = some owner) ∧
    (selectDotEdge ctxIn target N alg? = .ok (.member owner p)) ∧
    ((probed.needs[k]?).bind NeedCell.route = none) ∧
    (((NeedPlan.executeAlong productionPlanRoute k shape .call).runState x).1.isIncomplete = false) ∧
    ((resolveDotReceiver? target ctxIn).runState x = (.ok alg?, x)) ∧
    (x.nextRuntimeDeclaration = fin.nextRuntimeDeclaration) ∧
    ((projectNeedStructuralMember path ctxIn).runState x = (.ok (some (childOfInContext owner p.alg ctxIn)), x)) ∧
    ((projectedStructure target ctxIn).runState uF = (.ok (some owner), uF)) ∧
    (completeB ((evalCounted src ctxIn envIn).runState x).1 = true) ∧
    (((NeedSupply.form evalSupplySpread ctxIn envIn args).runState tA).1.toOption = none) ∧
    (((ordinaryCall productionPlanRoute k shape .call).runState x).1.toOption = none) := by
  cbv
  all_goals (repeat' (first | rfl | constructor))


theorem captured : (evalCounted row ctx []).runState EvalState.empty = (.ok (.callRef k, 1), fin) :=
  facts.1

theorem program_run :
    (evalProgramOutput (wireToCaller base (rootOf [row])) base []).runState EvalState.empty =
      (.ok (.callRef k), fin) :=
  facts.2.1

theorem plan_cell : fin.needs[k]? = some { suspension := .expression src ctxIn envIn } :=
  facts.2.2.1

theorem entry_cell : entry.needs[k]? = some entryCell :=
  facts.2.2.2.1

theorem probe_entry : (resolveDotReceiver? target ctxIn).runState entry = (.ok alg?, probed) :=
  facts.2.2.2.2.1

/-- The probe WROTE: the first navigation of a parameter receiver is not state-inert — the
    parameter's cell was unprojected, and holds the projection's memo afterwards. -/
theorem probe_wrote :
    (entry.needs[b]?.map fun c => match c.callable with | .unprojected => true | _ => false) = some true ∧
    (probed.needs[b]?.map fun c =>
      match c.callable with | .projected (.ok (some _)) => true | _ => false) = some true :=
  facts.2.2.2.2.2.1

theorem probe_owner : alg? = some owner :=
  facts.2.2.2.2.2.2.1

theorem selected : selectDotEdge ctxIn target N alg? = .ok (.member owner p) :=
  facts.2.2.2.2.2.2.2.1

theorem route_free : (probed.needs[k]?).bind NeedCell.route = none :=
  facts.2.2.2.2.2.2.2.2.1

theorem flight :
    (withCtx shape.ctxMsg (NeedPlan.routeOf productionPlanRoute.classify k shape)).runState entry =
      (.ok .call, x) :=
  flight_member k target N (.resolve N) args ctxIn envIn entry probed entryCell alg? _ entry_cell rfl probe_entry
    selected route_free
theorem demand_done :
    ((NeedPlan.executeAlong productionPlanRoute k shape .call).runState x).1.isIncomplete = false :=
  facts.2.2.2.2.2.2.2.2.2.1

theorem demand_passes :
    (demandNeed k).runState fin =
      (let res := (NeedPlan.executeAlong productionPlanRoute k shape .call).runState x
       (res.1, withState k (.completed res.1) res.2)) :=
  demand_passes_flight k fin x _ src ctxIn envIn shape .call plan_cell rfl rfl rfl flight nofun demand_done

theorem probe_x : (resolveDotReceiver? target ctxIn).runState x = (.ok alg?, x) :=
  facts.2.2.2.2.2.2.2.2.2.2.1

theorem not_minted : x.nextRuntimeDeclaration = fin.nextRuntimeDeclaration :=
  facts.2.2.2.2.2.2.2.2.2.2.2.1

theorem projection_x :
    (projectNeedStructuralMember path ctxIn).runState x = (.ok (some (childOfInContext owner p.alg ctxIn)), x) :=
  facts.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem settled_at_origin : (projectedStructure target ctxIn).runState uF = (.ok (some owner), uF) :=
  facts.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem settled_origin : ∀ g t cells u,
    (resolveAliasTarget (childOfInContext owner p.alg ctxIn) ctxIn).runState x = (.ok g, t) →
    (NeedSupply.form evalSupplySpread ctxIn envIn args).runState t = (.ok cells, u) →
    (projectedStructure target ctxIn).runState u = (.ok (some owner), u) := by
  intro g t cells u hr hf
  have ht : tA = t := congrArg Prod.snd hr
  subst ht
  have hu : uF = u := congrArg Prod.snd hf
  subst hu
  exact settled_at_origin

theorem production_done : completeB ((evalCounted src ctxIn envIn).runState x).1 = true :=
  facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem production_completes : ProductionCompletes (evalCounted src ctxIn envIn) x :=
  complete_of_B production_done

/-- **`member_bridge_settled` APPLIED** at the plan's flight, every premise proved above. -/
theorem bridge :
    (ordinaryCall productionPlanRoute k shape .call).runState x =
      (reCountValueBoundary <$> evalCounted src ctxIn envIn).runState x :=
  member_bridge_settled k target N (.resolve N) args ctxIn envIn x x alg? owner p probe_x selected projection_x
    settled_origin production_completes

/-- **The spread FAILS**: the supply formation's failure is the run's, on both sides; the callee
    origin is never read. -/
theorem formation_fails :
    ((NeedSupply.form evalSupplySpread ctxIn envIn args).runState tA).1.toOption = none :=
  facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem fails : ((ordinaryCall productionPlanRoute k shape .call).runState x).1.toOption = none :=
  facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

end ParamSpreadFails

end KatLang.MemberStabilityInstances
