import KatLangArityLaws.MemberBridgeSourceInstances

/-!
# The member bridge applied: reference chains and runtime-target aliases (E-18 step 1, M1)

`PathRefEmpty` (`ALS.K()`): a transparent reference whose row is a member path. `RuntimeEmpty` (`RTC.Pair()`), `RuntimeSpreadOne` (`RTC.G([5]*)`),
`RuntimeNamedOrdinary` (`RTA.G(2)`): RUNTIME-TARGET ALIASES — the first navigation WRITES (the alias's
binding cell, its CALLABLE projection); the navigation is settled afterwards.

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

/-! ## `PathRefEmpty`: `ALS.K()` — a transparent reference to a MEMBER PATH, empty bundle -/

namespace PathRefEmpty
/-- `ALS = Lib.Sub`: the reference's own row is a member path. -/
def target : Expr := .resolve "ALS"
def N : Ident := "K"
def args : OutputBundle := []
def path : Expr := .dotMember target N (.resolve N) none
/-- The plan's written source `ALS.K()`. -/
def src : Expr := .dotMember target N (.resolve N) (some args)
/-- THE SOURCE PROGRAM's one row: `Capture(ALS.K())`. -/
def row : Expr := capture src
def ctx : EvalCtx := ctxOf [row]
def shape : NeedPlan.CallShape := ⟨path, args, ctx, [], .dot target N (.resolve N)⟩

def fin : EvalState := ((evalCounted row ctx []).runState EvalState.empty).2
def entry : EvalState := withState 0 .evaluating fin
def entryCell : NeedCell := { suspension := .expression src ctx [], state := .evaluating }
/-- The receiver's identity as production's probe answers it. -/
def alg? : Option Algorithm :=
  match ((resolveDotReceiver? target ctx).runState entry).1 with
  | .ok a => a
  | .error _ => none
/-- The probe's exit state (the receiver's FIRST navigation: every first-time write is made). -/
def probed : EvalState := ((resolveDotReceiver? target ctx).runState entry).2
def owner : Algorithm := alg?.getD (alg [] [] [] [])
def p : PropDef := (Algorithm.lookupPropDefAny? owner N).getD { name := N, alg := owner, isPublic := false }
/-- THE COMPARISON STATE: the plan's flight on the member (`.call`) route. -/
def x : EvalState := withRoute 0 .call probed
/-- The state the member run reads its callee origin in: after the member's alias resolution … -/
def tA : EvalState := ((resolveAliasTarget (childOfInContext owner p.alg ctx) ctx).runState x).2
/-- … and the supply formation (whatever spread code it runs, whatever its outcome). -/
def uF : EvalState := ((NeedSupply.form evalSupplySpread ctx [] args).runState tA).2
/-- EVERY evaluated fact of this instance, in ONE proof-producing evaluation (`cbv`); the theorems
    below are its projections. -/
theorem facts :
    ((evalCounted row ctx []).runState EvalState.empty = (.ok (.callRef 0, 1), fin)) ∧
    ((evalProgramOutput (wireToCaller base (rootOf [row])) base []).runState EvalState.empty = (.ok (.callRef 0), fin)) ∧
    (fin.needs[0]? = some { suspension := .expression src ctx [] }) ∧
    (entry.needs[0]? = some entryCell) ∧
    ((resolveDotReceiver? target ctx).runState entry = (.ok alg?, probed)) ∧
    (alg? = some owner) ∧
    (selectDotEdge ctx target N alg? = .ok (.member owner p)) ∧
    ((probed.needs[0]?).bind NeedCell.route = none) ∧
    (((NeedPlan.executeAlong productionPlanRoute 0 shape .call).runState x).1.isIncomplete = false) ∧
    ((resolveDotReceiver? target ctx).runState x = (.ok alg?, x)) ∧
    (x.nextRuntimeDeclaration = fin.nextRuntimeDeclaration) ∧
    ((projectNeedStructuralMember path ctx).runState x = (.ok (some (childOfInContext owner p.alg ctx)), x)) ∧
    ((projectedStructure target ctx).runState uF = (.ok (some owner), uF)) ∧
    (completeB ((evalCounted src ctx []).runState x).1 = true) ∧
    (((ordinaryCall productionPlanRoute 0 shape .call).runState x).1 = .ok (.atom 3, 1)) ∧
    (((ordinaryCall productionPlanRoute 0 shape .call).runState x).2.zeroArgPropertyCache.length = x.zeroArgPropertyCache.length + 1) := by
  cbv
  all_goals (repeat' (first | rfl | constructor))


/-- **REACHED (1).** Production's evaluation of the source row from the empty state captures the
    written invocation: the reference to cell 0. -/
theorem captured : (evalCounted row ctx []).runState EvalState.empty = (.ok (.callRef 0, 1), fin) :=
  facts.1

theorem program_run :
    (evalProgramOutput (wireToCaller base (rootOf [row])) base []).runState EvalState.empty =
      (.ok (.callRef 0), fin) :=
  facts.2.1

/-- **REACHED (2).** Cell 0 is THE PLAN: suspended, no route recorded. -/
theorem plan_cell : fin.needs[0]? = some { suspension := .expression src ctx [] } :=
  facts.2.2.1

theorem entry_cell : entry.needs[0]? = some entryCell :=
  facts.2.2.2.1

theorem probe_entry : (resolveDotReceiver? target ctx).runState entry = (.ok alg?, probed) :=
  facts.2.2.2.2.1

theorem probe_owner : alg? = some owner :=
  facts.2.2.2.2.2.1

/-- Production's own dot decision: the DECLARED member `N` of the receiver's structure. -/
theorem selected : selectDotEdge ctx target N alg? = .ok (.member owner p) :=
  facts.2.2.2.2.2.2.1

theorem route_free : (probed.needs[0]?).bind NeedCell.route = none :=
  facts.2.2.2.2.2.2.2.1

/-- **REACHED (3).** `x` is the flight of the plan cell: its first route decision is the receiver
    probe and the dot decision, recorded as the `.call` route. -/
theorem flight :
    (withCtx shape.ctxMsg (NeedPlan.routeOf productionPlanRoute.classify 0 shape)).runState entry =
      (.ok .call, x) :=
  flight_member 0 target N (.resolve N) args ctx [] entry probed entryCell alg? _ entry_cell rfl probe_entry
    selected route_free
theorem demand_done :
    ((NeedPlan.executeAlong productionPlanRoute 0 shape .call).runState x).1.isIncomplete = false :=
  facts.2.2.2.2.2.2.2.2.1

/-- **REACHED (4).** The production VALUE demand of the plan cell passes through that flight. -/
theorem demand_passes :
    (demandNeed 0).runState fin =
      (let res := (NeedPlan.executeAlong productionPlanRoute 0 shape .call).runState x
       (res.1, withState 0 (.completed res.1) res.2)) :=
  demand_passes_flight 0 fin x _ src ctx [] shape .call plan_cell rfl rfl rfl flight nofun demand_done

/-- **The probe is settled at the flight**: it answers the same identity and changes nothing — and
    it minted no runtime declaration (`not_minted`): the non-minting domain. -/
theorem probe_x : (resolveDotReceiver? target ctx).runState x = (.ok alg?, x) :=
  facts.2.2.2.2.2.2.2.2.2.1

theorem not_minted : x.nextRuntimeDeclaration = fin.nextRuntimeDeclaration :=
  facts.2.2.2.2.2.2.2.2.2.2.1

/-- The plan's structural projection of the argumentless path reaches the selected member. -/
theorem projection_x :
    (projectNeedStructuralMember path ctx).runState x = (.ok (some (childOfInContext owner p.alg ctx)), x) :=
  facts.2.2.2.2.2.2.2.2.2.2.2.1

/-- **The receiver's navigation is settled where the origin is read.** -/
theorem settled_at_origin : (projectedStructure target ctx).runState uF = (.ok (some owner), uF) :=
  facts.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem settled_origin : ∀ g t cells u,
    (resolveAliasTarget (childOfInContext owner p.alg ctx) ctx).runState x = (.ok g, t) →
    (NeedSupply.form evalSupplySpread ctx [] args).runState t = (.ok cells, u) →
    (projectedStructure target ctx).runState u = (.ok (some owner), u) := by
  intro g t cells u hr hf
  have ht : tA = t := congrArg Prod.snd hr
  subst ht
  have hu : uF = u := congrArg Prod.snd hf
  subst hu
  exact settled_at_origin

theorem production_done : completeB ((evalCounted src ctx []).runState x).1 = true :=
  facts.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem production_completes : ProductionCompletes (evalCounted src ctx []) x := complete_of_B production_done

/-- **`member_bridge_settled` APPLIED** at the plan's flight, every premise proved above: the
    member-route ordinary call IS the re-counted production dot evaluation — outcome, error context,
    final state and publication. -/
theorem bridge :
    (ordinaryCall productionPlanRoute 0 shape .call).runState x =
      (reCountValueBoundary <$> evalCounted src ctx []).runState x :=
  member_bridge_settled 0 target N (.resolve N) args ctx [] x x alg? owner p probe_x selected projection_x
    settled_origin production_completes

/-- Both sides return the value 3. -/
theorem value : ((ordinaryCall productionPlanRoute 0 shape .call).runState x).1 = .ok (.atom 3, 1) :=
  facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- The zero-supply invocation PUBLISHED the member's cache entry (CACHE-PUB-1) — on both sides, by
    `bridge`. -/
theorem published :
    ((ordinaryCall productionPlanRoute 0 shape .call).runState x).2.zeroArgPropertyCache.length =
      x.zeroArgPropertyCache.length + 1 :=
  facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

end PathRefEmpty

/-! ## `RuntimeEmpty`: `RTC.Pair()` — a RUNTIME-TARGET ALIAS, empty bundle -/

namespace RuntimeEmpty
/-- `RTC = Capture(FM(0)).Algorithm`: the first navigation establishes the alias's binding cell, projects its CALLABLE through the `.Algorithm` link (demanding the receiver's VALUE) and continues the chase at the projected identity `FM`; every later navigation reads those records back. -/
def target : Expr := .resolve "RTC"
def N : Ident := "Pair"
def args : OutputBundle := []
def path : Expr := .dotMember target N (.resolve N) none
/-- The plan's written source `RTC.Pair()`. -/
def src : Expr := .dotMember target N (.resolve N) (some args)
/-- THE SOURCE PROGRAM's one row: `Capture(RTC.Pair())`. -/
def row : Expr := capture src
def ctx : EvalCtx := ctxOf [row]
def shape : NeedPlan.CallShape := ⟨path, args, ctx, [], .dot target N (.resolve N)⟩

def fin : EvalState := ((evalCounted row ctx []).runState EvalState.empty).2
def entry : EvalState := withState 0 .evaluating fin
def entryCell : NeedCell := { suspension := .expression src ctx [], state := .evaluating }
/-- The receiver's identity as production's probe answers it. -/
def alg? : Option Algorithm :=
  match ((resolveDotReceiver? target ctx).runState entry).1 with
  | .ok a => a
  | .error _ => none
/-- The probe's exit state (the receiver's FIRST navigation: every first-time write is made). -/
def probed : EvalState := ((resolveDotReceiver? target ctx).runState entry).2
def owner : Algorithm := alg?.getD (alg [] [] [] [])
def p : PropDef := (Algorithm.lookupPropDefAny? owner N).getD { name := N, alg := owner, isPublic := false }
/-- THE COMPARISON STATE: the plan's flight on the member (`.call`) route. -/
def x : EvalState := withRoute 0 .call probed
/-- The state the member run reads its callee origin in: after the member's alias resolution … -/
def tA : EvalState := ((resolveAliasTarget (childOfInContext owner p.alg ctx) ctx).runState x).2
/-- … and the supply formation (whatever spread code it runs, whatever its outcome). -/
def uF : EvalState := ((NeedSupply.form evalSupplySpread ctx [] args).runState tA).2
/-- EVERY evaluated fact of this instance, in ONE proof-producing evaluation (`cbv`); the theorems
    below are its projections. -/
theorem facts :
    ((evalCounted row ctx []).runState EvalState.empty = (.ok (.callRef 0, 1), fin)) ∧
    ((evalProgramOutput (wireToCaller base (rootOf [row])) base []).runState EvalState.empty = (.ok (.callRef 0), fin)) ∧
    (fin.needs[0]? = some { suspension := .expression src ctx [] }) ∧
    (entry.needs[0]? = some entryCell) ∧
    ((resolveDotReceiver? target ctx).runState entry = (.ok alg?, probed)) ∧
    (alg? = some owner) ∧
    (selectDotEdge ctx target N alg? = .ok (.member owner p)) ∧
    ((probed.needs[0]?).bind NeedCell.route = none) ∧
    (((NeedPlan.executeAlong productionPlanRoute 0 shape .call).runState x).1.isIncomplete = false) ∧
    ((resolveDotReceiver? target ctx).runState x = (.ok alg?, x)) ∧
    (x.nextRuntimeDeclaration = fin.nextRuntimeDeclaration) ∧
    ((projectNeedStructuralMember path ctx).runState x = (.ok (some (childOfInContext owner p.alg ctx)), x)) ∧
    ((projectedStructure target ctx).runState uF = (.ok (some owner), uF)) ∧
    (completeB ((evalCounted src ctx []).runState x).1 = true) ∧
    (((ordinaryCall productionPlanRoute 0 shape .call).runState x).1 = .ok (.sequenceValue [.atom 7, .atom 8], 1)) ∧
    (((ordinaryCall productionPlanRoute 0 shape .call).runState x).2.zeroArgPropertyCache.length = x.zeroArgPropertyCache.length + 1) ∧
    (decide (probed.aliasCells.length = entry.aliasCells.length + 1 ∧ entry.needs.size < probed.needs.size) = true) := by
  cbv
  all_goals (repeat' (first | rfl | constructor))


/-- **REACHED (1).** Production's evaluation of the source row from the empty state captures the
    written invocation: the reference to cell 0. -/
theorem captured : (evalCounted row ctx []).runState EvalState.empty = (.ok (.callRef 0, 1), fin) :=
  facts.1

theorem program_run :
    (evalProgramOutput (wireToCaller base (rootOf [row])) base []).runState EvalState.empty =
      (.ok (.callRef 0), fin) :=
  facts.2.1

/-- **REACHED (2).** Cell 0 is THE PLAN: suspended, no route recorded. -/
theorem plan_cell : fin.needs[0]? = some { suspension := .expression src ctx [] } :=
  facts.2.2.1

theorem entry_cell : entry.needs[0]? = some entryCell :=
  facts.2.2.2.1

theorem probe_entry : (resolveDotReceiver? target ctx).runState entry = (.ok alg?, probed) :=
  facts.2.2.2.2.1

theorem probe_owner : alg? = some owner :=
  facts.2.2.2.2.2.1

/-- Production's own dot decision: the DECLARED member `N` of the receiver's structure. -/
theorem selected : selectDotEdge ctx target N alg? = .ok (.member owner p) :=
  facts.2.2.2.2.2.2.1

theorem route_free : (probed.needs[0]?).bind NeedCell.route = none :=
  facts.2.2.2.2.2.2.2.1

/-- **REACHED (3).** `x` is the flight of the plan cell: its first route decision is the receiver
    probe and the dot decision, recorded as the `.call` route. -/
theorem flight :
    (withCtx shape.ctxMsg (NeedPlan.routeOf productionPlanRoute.classify 0 shape)).runState entry =
      (.ok .call, x) :=
  flight_member 0 target N (.resolve N) args ctx [] entry probed entryCell alg? _ entry_cell rfl probe_entry
    selected route_free
theorem demand_done :
    ((NeedPlan.executeAlong productionPlanRoute 0 shape .call).runState x).1.isIncomplete = false :=
  facts.2.2.2.2.2.2.2.2.1

/-- **REACHED (4).** The production VALUE demand of the plan cell passes through that flight. -/
theorem demand_passes :
    (demandNeed 0).runState fin =
      (let res := (NeedPlan.executeAlong productionPlanRoute 0 shape .call).runState x
       (res.1, withState 0 (.completed res.1) res.2)) :=
  demand_passes_flight 0 fin x _ src ctx [] shape .call plan_cell rfl rfl rfl flight nofun demand_done

/-- **The probe is settled at the flight**: it answers the same identity and changes nothing — and
    it minted no runtime declaration (`not_minted`): the non-minting domain. -/
theorem probe_x : (resolveDotReceiver? target ctx).runState x = (.ok alg?, x) :=
  facts.2.2.2.2.2.2.2.2.2.1

theorem not_minted : x.nextRuntimeDeclaration = fin.nextRuntimeDeclaration :=
  facts.2.2.2.2.2.2.2.2.2.2.1

/-- The plan's structural projection of the argumentless path reaches the selected member. -/
theorem projection_x :
    (projectNeedStructuralMember path ctx).runState x = (.ok (some (childOfInContext owner p.alg ctx)), x) :=
  facts.2.2.2.2.2.2.2.2.2.2.2.1

/-- **The receiver's navigation is settled where the origin is read.** -/
theorem settled_at_origin : (projectedStructure target ctx).runState uF = (.ok (some owner), uF) :=
  facts.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem settled_origin : ∀ g t cells u,
    (resolveAliasTarget (childOfInContext owner p.alg ctx) ctx).runState x = (.ok g, t) →
    (NeedSupply.form evalSupplySpread ctx [] args).runState t = (.ok cells, u) →
    (projectedStructure target ctx).runState u = (.ok (some owner), u) := by
  intro g t cells u hr hf
  have ht : tA = t := congrArg Prod.snd hr
  subst ht
  have hu : uF = u := congrArg Prod.snd hf
  subst hu
  exact settled_at_origin

theorem production_done : completeB ((evalCounted src ctx []).runState x).1 = true :=
  facts.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem production_completes : ProductionCompletes (evalCounted src ctx []) x := complete_of_B production_done

/-- **`member_bridge_settled` APPLIED** at the plan's flight, every premise proved above: the
    member-route ordinary call IS the re-counted production dot evaluation — outcome, error context,
    final state and publication. -/
theorem bridge :
    (ordinaryCall productionPlanRoute 0 shape .call).runState x =
      (reCountValueBoundary <$> evalCounted src ctx []).runState x :=
  member_bridge_settled 0 target N (.resolve N) args ctx [] x x alg? owner p probe_x selected projection_x
    settled_origin production_completes

/-- Both sides return the value (7, 8). -/
theorem value : ((ordinaryCall productionPlanRoute 0 shape .call).runState x).1 = .ok (.sequenceValue [.atom 7, .atom 8], 1) :=
  facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- The zero-supply invocation PUBLISHED the member's cache entry (CACHE-PUB-1) — on both sides, by
    `bridge`. -/
theorem published :
    ((ordinaryCall productionPlanRoute 0 shape .call).runState x).2.zeroArgPropertyCache.length =
      x.zeroArgPropertyCache.length + 1 :=
  facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- The receiver's first navigation WROTE (it is not state-inert): it recorded the alias's binding cell and allocated. -/
theorem probe_wrote : probed.aliasCells.length = entry.aliasCells.length + 1 ∧ entry.needs.size < probed.needs.size :=
  of_decide_eq_true facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

end RuntimeEmpty

/-! ## `RuntimeSpreadOne`: `RTC.G([5]*)` — a runtime-target alias, spread-first bundle forming one cell -/

namespace RuntimeSpreadOne
/-- As `RuntimeEmpty`, with one spread-formed cell: `G(5) = 5`. -/
def target : Expr := .resolve "RTC"
def N : Ident := "G"
def args : OutputBundle := [.sequenceSpread (.listLiteral [.num 5])]
def path : Expr := .dotMember target N (.resolve N) none
/-- The plan's written source `RTC.G([5]*)`. -/
def src : Expr := .dotMember target N (.resolve N) (some args)
/-- THE SOURCE PROGRAM's one row: `Capture(RTC.G([5]*))`. -/
def row : Expr := capture src
def ctx : EvalCtx := ctxOf [row]
def shape : NeedPlan.CallShape := ⟨path, args, ctx, [], .dot target N (.resolve N)⟩

def fin : EvalState := ((evalCounted row ctx []).runState EvalState.empty).2
def entry : EvalState := withState 0 .evaluating fin
def entryCell : NeedCell := { suspension := .expression src ctx [], state := .evaluating }
/-- The receiver's identity as production's probe answers it. -/
def alg? : Option Algorithm :=
  match ((resolveDotReceiver? target ctx).runState entry).1 with
  | .ok a => a
  | .error _ => none
/-- The probe's exit state (the receiver's FIRST navigation: every first-time write is made). -/
def probed : EvalState := ((resolveDotReceiver? target ctx).runState entry).2
def owner : Algorithm := alg?.getD (alg [] [] [] [])
def p : PropDef := (Algorithm.lookupPropDefAny? owner N).getD { name := N, alg := owner, isPublic := false }
/-- THE COMPARISON STATE: the plan's flight on the member (`.call`) route. -/
def x : EvalState := withRoute 0 .call probed
/-- The state the member run reads its callee origin in: after the member's alias resolution … -/
def tA : EvalState := ((resolveAliasTarget (childOfInContext owner p.alg ctx) ctx).runState x).2
/-- … and the supply formation (whatever spread code it runs, whatever its outcome). -/
def uF : EvalState := ((NeedSupply.form evalSupplySpread ctx [] args).runState tA).2
/-- EVERY evaluated fact of this instance, in ONE proof-producing evaluation (`cbv`); the theorems
    below are its projections. -/
theorem facts :
    ((evalCounted row ctx []).runState EvalState.empty = (.ok (.callRef 0, 1), fin)) ∧
    ((evalProgramOutput (wireToCaller base (rootOf [row])) base []).runState EvalState.empty = (.ok (.callRef 0), fin)) ∧
    (fin.needs[0]? = some { suspension := .expression src ctx [] }) ∧
    (entry.needs[0]? = some entryCell) ∧
    ((resolveDotReceiver? target ctx).runState entry = (.ok alg?, probed)) ∧
    (alg? = some owner) ∧
    (selectDotEdge ctx target N alg? = .ok (.member owner p)) ∧
    ((probed.needs[0]?).bind NeedCell.route = none) ∧
    (((NeedPlan.executeAlong productionPlanRoute 0 shape .call).runState x).1.isIncomplete = false) ∧
    ((resolveDotReceiver? target ctx).runState x = (.ok alg?, x)) ∧
    (x.nextRuntimeDeclaration = fin.nextRuntimeDeclaration) ∧
    ((projectNeedStructuralMember path ctx).runState x = (.ok (some (childOfInContext owner p.alg ctx)), x)) ∧
    ((projectedStructure target ctx).runState uF = (.ok (some owner), uF)) ∧
    (completeB ((evalCounted src ctx []).runState x).1 = true) ∧
    (((ordinaryCall productionPlanRoute 0 shape .call).runState x).1 = .ok (.atom 5, 1)) ∧
    (((NeedSupply.form evalSupplySpread ctx [] args).runState tA).1.toOption.map List.length = some 1) := by
  cbv
  all_goals (repeat' (first | rfl | constructor))


/-- **REACHED (1).** Production's evaluation of the source row from the empty state captures the
    written invocation: the reference to cell 0. -/
theorem captured : (evalCounted row ctx []).runState EvalState.empty = (.ok (.callRef 0, 1), fin) :=
  facts.1

theorem program_run :
    (evalProgramOutput (wireToCaller base (rootOf [row])) base []).runState EvalState.empty =
      (.ok (.callRef 0), fin) :=
  facts.2.1

/-- **REACHED (2).** Cell 0 is THE PLAN: suspended, no route recorded. -/
theorem plan_cell : fin.needs[0]? = some { suspension := .expression src ctx [] } :=
  facts.2.2.1

theorem entry_cell : entry.needs[0]? = some entryCell :=
  facts.2.2.2.1

theorem probe_entry : (resolveDotReceiver? target ctx).runState entry = (.ok alg?, probed) :=
  facts.2.2.2.2.1

theorem probe_owner : alg? = some owner :=
  facts.2.2.2.2.2.1

/-- Production's own dot decision: the DECLARED member `N` of the receiver's structure. -/
theorem selected : selectDotEdge ctx target N alg? = .ok (.member owner p) :=
  facts.2.2.2.2.2.2.1

theorem route_free : (probed.needs[0]?).bind NeedCell.route = none :=
  facts.2.2.2.2.2.2.2.1

/-- **REACHED (3).** `x` is the flight of the plan cell: its first route decision is the receiver
    probe and the dot decision, recorded as the `.call` route. -/
theorem flight :
    (withCtx shape.ctxMsg (NeedPlan.routeOf productionPlanRoute.classify 0 shape)).runState entry =
      (.ok .call, x) :=
  flight_member 0 target N (.resolve N) args ctx [] entry probed entryCell alg? _ entry_cell rfl probe_entry
    selected route_free
theorem demand_done :
    ((NeedPlan.executeAlong productionPlanRoute 0 shape .call).runState x).1.isIncomplete = false :=
  facts.2.2.2.2.2.2.2.2.1

/-- **REACHED (4).** The production VALUE demand of the plan cell passes through that flight. -/
theorem demand_passes :
    (demandNeed 0).runState fin =
      (let res := (NeedPlan.executeAlong productionPlanRoute 0 shape .call).runState x
       (res.1, withState 0 (.completed res.1) res.2)) :=
  demand_passes_flight 0 fin x _ src ctx [] shape .call plan_cell rfl rfl rfl flight nofun demand_done

/-- **The probe is settled at the flight**: it answers the same identity and changes nothing — and
    it minted no runtime declaration (`not_minted`): the non-minting domain. -/
theorem probe_x : (resolveDotReceiver? target ctx).runState x = (.ok alg?, x) :=
  facts.2.2.2.2.2.2.2.2.2.1

theorem not_minted : x.nextRuntimeDeclaration = fin.nextRuntimeDeclaration :=
  facts.2.2.2.2.2.2.2.2.2.2.1

/-- The plan's structural projection of the argumentless path reaches the selected member. -/
theorem projection_x :
    (projectNeedStructuralMember path ctx).runState x = (.ok (some (childOfInContext owner p.alg ctx)), x) :=
  facts.2.2.2.2.2.2.2.2.2.2.2.1

/-- **The receiver's navigation is settled where the origin is read.** -/
theorem settled_at_origin : (projectedStructure target ctx).runState uF = (.ok (some owner), uF) :=
  facts.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem settled_origin : ∀ g t cells u,
    (resolveAliasTarget (childOfInContext owner p.alg ctx) ctx).runState x = (.ok g, t) →
    (NeedSupply.form evalSupplySpread ctx [] args).runState t = (.ok cells, u) →
    (projectedStructure target ctx).runState u = (.ok (some owner), u) := by
  intro g t cells u hr hf
  have ht : tA = t := congrArg Prod.snd hr
  subst ht
  have hu : uF = u := congrArg Prod.snd hf
  subst hu
  exact settled_at_origin

theorem production_done : completeB ((evalCounted src ctx []).runState x).1 = true :=
  facts.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem production_completes : ProductionCompletes (evalCounted src ctx []) x := complete_of_B production_done

/-- **`member_bridge_settled` APPLIED** at the plan's flight, every premise proved above: the
    member-route ordinary call IS the re-counted production dot evaluation — outcome, error context,
    final state and publication. -/
theorem bridge :
    (ordinaryCall productionPlanRoute 0 shape .call).runState x =
      (reCountValueBoundary <$> evalCounted src ctx []).runState x :=
  member_bridge_settled 0 target N (.resolve N) args ctx [] x x alg? owner p probe_x selected projection_x
    settled_origin production_completes

/-- Both sides return the value 5. -/
theorem value : ((ordinaryCall productionPlanRoute 0 shape .call).runState x).1 = .ok (.atom 5, 1) :=
  facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- The supply formation runs the spread and forms one cell. -/
theorem formation :
    ((NeedSupply.form evalSupplySpread ctx [] args).runState tA).1.toOption.map List.length = some 1 :=
  facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

end RuntimeSpreadOne

/-! ## `RuntimeNamedOrdinary`: `RTA.G(2)` — a runtime-target alias over a NAMED static receiver, ordinary bundle -/

namespace RuntimeNamedOrdinary
/-- `RTA = RC.Algorithm` with `RC = Capture(FM(0))`: the receiver of the alias's row is a name; the projection reads `RC`'s VALUE through the property cache. -/
def target : Expr := .resolve "RTA"
def N : Ident := "G"
def args : OutputBundle := [.num 2]
def path : Expr := .dotMember target N (.resolve N) none
/-- The plan's written source `RTA.G(2)`. -/
def src : Expr := .dotMember target N (.resolve N) (some args)
/-- THE SOURCE PROGRAM's one row: `Capture(RTA.G(2))`. -/
def row : Expr := capture src
def ctx : EvalCtx := ctxOf [row]
def shape : NeedPlan.CallShape := ⟨path, args, ctx, [], .dot target N (.resolve N)⟩

def fin : EvalState := ((evalCounted row ctx []).runState EvalState.empty).2
def entry : EvalState := withState 0 .evaluating fin
def entryCell : NeedCell := { suspension := .expression src ctx [], state := .evaluating }
/-- The receiver's identity as production's probe answers it. -/
def alg? : Option Algorithm :=
  match ((resolveDotReceiver? target ctx).runState entry).1 with
  | .ok a => a
  | .error _ => none
/-- The probe's exit state (the receiver's FIRST navigation: every first-time write is made). -/
def probed : EvalState := ((resolveDotReceiver? target ctx).runState entry).2
def owner : Algorithm := alg?.getD (alg [] [] [] [])
def p : PropDef := (Algorithm.lookupPropDefAny? owner N).getD { name := N, alg := owner, isPublic := false }
/-- THE COMPARISON STATE: the plan's flight on the member (`.call`) route. -/
def x : EvalState := withRoute 0 .call probed
/-- The state the member run reads its callee origin in: after the member's alias resolution … -/
def tA : EvalState := ((resolveAliasTarget (childOfInContext owner p.alg ctx) ctx).runState x).2
/-- … and the supply formation (whatever spread code it runs, whatever its outcome). -/
def uF : EvalState := ((NeedSupply.form evalSupplySpread ctx [] args).runState tA).2
/-- EVERY evaluated fact of this instance, in ONE proof-producing evaluation (`cbv`); the theorems
    below are its projections. -/
theorem facts :
    ((evalCounted row ctx []).runState EvalState.empty = (.ok (.callRef 0, 1), fin)) ∧
    ((evalProgramOutput (wireToCaller base (rootOf [row])) base []).runState EvalState.empty = (.ok (.callRef 0), fin)) ∧
    (fin.needs[0]? = some { suspension := .expression src ctx [] }) ∧
    (entry.needs[0]? = some entryCell) ∧
    ((resolveDotReceiver? target ctx).runState entry = (.ok alg?, probed)) ∧
    (alg? = some owner) ∧
    (selectDotEdge ctx target N alg? = .ok (.member owner p)) ∧
    ((probed.needs[0]?).bind NeedCell.route = none) ∧
    (((NeedPlan.executeAlong productionPlanRoute 0 shape .call).runState x).1.isIncomplete = false) ∧
    ((resolveDotReceiver? target ctx).runState x = (.ok alg?, x)) ∧
    (x.nextRuntimeDeclaration = fin.nextRuntimeDeclaration) ∧
    ((projectNeedStructuralMember path ctx).runState x = (.ok (some (childOfInContext owner p.alg ctx)), x)) ∧
    ((projectedStructure target ctx).runState uF = (.ok (some owner), uF)) ∧
    (completeB ((evalCounted src ctx []).runState x).1 = true) ∧
    (((ordinaryCall productionPlanRoute 0 shape .call).runState x).1 = .ok (.atom 2, 1)) := by
  cbv
  all_goals (repeat' (first | rfl | constructor))


/-- **REACHED (1).** Production's evaluation of the source row from the empty state captures the
    written invocation: the reference to cell 0. -/
theorem captured : (evalCounted row ctx []).runState EvalState.empty = (.ok (.callRef 0, 1), fin) :=
  facts.1

theorem program_run :
    (evalProgramOutput (wireToCaller base (rootOf [row])) base []).runState EvalState.empty =
      (.ok (.callRef 0), fin) :=
  facts.2.1

/-- **REACHED (2).** Cell 0 is THE PLAN: suspended, no route recorded. -/
theorem plan_cell : fin.needs[0]? = some { suspension := .expression src ctx [] } :=
  facts.2.2.1

theorem entry_cell : entry.needs[0]? = some entryCell :=
  facts.2.2.2.1

theorem probe_entry : (resolveDotReceiver? target ctx).runState entry = (.ok alg?, probed) :=
  facts.2.2.2.2.1

theorem probe_owner : alg? = some owner :=
  facts.2.2.2.2.2.1

/-- Production's own dot decision: the DECLARED member `N` of the receiver's structure. -/
theorem selected : selectDotEdge ctx target N alg? = .ok (.member owner p) :=
  facts.2.2.2.2.2.2.1

theorem route_free : (probed.needs[0]?).bind NeedCell.route = none :=
  facts.2.2.2.2.2.2.2.1

/-- **REACHED (3).** `x` is the flight of the plan cell: its first route decision is the receiver
    probe and the dot decision, recorded as the `.call` route. -/
theorem flight :
    (withCtx shape.ctxMsg (NeedPlan.routeOf productionPlanRoute.classify 0 shape)).runState entry =
      (.ok .call, x) :=
  flight_member 0 target N (.resolve N) args ctx [] entry probed entryCell alg? _ entry_cell rfl probe_entry
    selected route_free
theorem demand_done :
    ((NeedPlan.executeAlong productionPlanRoute 0 shape .call).runState x).1.isIncomplete = false :=
  facts.2.2.2.2.2.2.2.2.1

/-- **REACHED (4).** The production VALUE demand of the plan cell passes through that flight. -/
theorem demand_passes :
    (demandNeed 0).runState fin =
      (let res := (NeedPlan.executeAlong productionPlanRoute 0 shape .call).runState x
       (res.1, withState 0 (.completed res.1) res.2)) :=
  demand_passes_flight 0 fin x _ src ctx [] shape .call plan_cell rfl rfl rfl flight nofun demand_done

/-- **The probe is settled at the flight**: it answers the same identity and changes nothing — and
    it minted no runtime declaration (`not_minted`): the non-minting domain. -/
theorem probe_x : (resolveDotReceiver? target ctx).runState x = (.ok alg?, x) :=
  facts.2.2.2.2.2.2.2.2.2.1

theorem not_minted : x.nextRuntimeDeclaration = fin.nextRuntimeDeclaration :=
  facts.2.2.2.2.2.2.2.2.2.2.1

/-- The plan's structural projection of the argumentless path reaches the selected member. -/
theorem projection_x :
    (projectNeedStructuralMember path ctx).runState x = (.ok (some (childOfInContext owner p.alg ctx)), x) :=
  facts.2.2.2.2.2.2.2.2.2.2.2.1

/-- **The receiver's navigation is settled where the origin is read.** -/
theorem settled_at_origin : (projectedStructure target ctx).runState uF = (.ok (some owner), uF) :=
  facts.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem settled_origin : ∀ g t cells u,
    (resolveAliasTarget (childOfInContext owner p.alg ctx) ctx).runState x = (.ok g, t) →
    (NeedSupply.form evalSupplySpread ctx [] args).runState t = (.ok cells, u) →
    (projectedStructure target ctx).runState u = (.ok (some owner), u) := by
  intro g t cells u hr hf
  have ht : tA = t := congrArg Prod.snd hr
  subst ht
  have hu : uF = u := congrArg Prod.snd hf
  subst hu
  exact settled_at_origin

theorem production_done : completeB ((evalCounted src ctx []).runState x).1 = true :=
  facts.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem production_completes : ProductionCompletes (evalCounted src ctx []) x := complete_of_B production_done

/-- **`member_bridge_settled` APPLIED** at the plan's flight, every premise proved above: the
    member-route ordinary call IS the re-counted production dot evaluation — outcome, error context,
    final state and publication. -/
theorem bridge :
    (ordinaryCall productionPlanRoute 0 shape .call).runState x =
      (reCountValueBoundary <$> evalCounted src ctx []).runState x :=
  member_bridge_settled 0 target N (.resolve N) args ctx [] x x alg? owner p probe_x selected projection_x
    settled_origin production_completes

/-- Both sides return the value 2. -/
theorem value : ((ordinaryCall productionPlanRoute 0 shape .call).runState x).1 = .ok (.atom 2, 1) :=
  facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2

end RuntimeNamedOrdinary

end KatLang.MemberStabilityInstances
