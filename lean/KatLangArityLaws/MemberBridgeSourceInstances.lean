import KatLangArityLaws.PlanAlgorithmBridgeSourceInstances
import KatLangArityLaws.MemberStability

/-!
# The member bridge APPLIED to genuine source programs (E-18 step 1, M1 — theorem-level instances)

`MemberStability.member_bridge_settled` is the member bridge for EVERY bundle: the member-route
ordinary call IS the re-counted production dot evaluation `t.N(args)` — outcome, error context,
final state, publication — whenever the receiver's navigation is settled at the one state where the
callee origin is read. Until now it had executable guards only (`MemberStabilityGuards.settledAt`).
This module and its three companions APPLY it, with every premise proved, on the receiver classes
the first-version theorems did not cover and on every kind of bundle:

| class | receivers | bundles |
| --- | --- | --- |
| transparent reference | `AB = Box`, the path reference `ALS = Lib.Sub` | empty, spread forming no cell, spread forming one cell, FAILING spread, ordinary |
| runtime-target alias | `RTC = Capture(FM(0)).Algorithm`, `RTA = RC.Algorithm` | empty, spread forming one cell, ordinary |
| name selected through `open` | `OBox` of the opened `OLib` | empty, spread forming no cell |
| nested member path | `Lib.Sub` | empty, spread forming one cell, failing spread |
| parameter and parameter-rooted path | `b`, `b.Sub`, `b` bound to a transparent reference | empty, spread forming no cell, failing spread |

## Method and reachability

As `PlanAlgorithmBridgeSourceInstances`: each instance fixes ONE source program — the declarations
below, the root opening `OLib`, and one root row that captures the written member call — whose
context is wired exactly as `runResultM` wires it; every run equation is proved by `cbv`
(proof-producing evaluation over the production definitions; the three standard axioms; no
`native_decide`, no replaced definition; in each namespace ONE theorem `facts` holds every evaluated
fact — one evaluation, shared — and the named theorems are its projections). The chain from the
source evaluation to the comparison
state is `captured` / `program_run` (production's evaluation of the row from the empty state),
`plan_cell` (cell `k` is the suspended plan in the program's own context), `flight` (the plan's first
route decision — the receiver probe and the dot decision — records the `.call` route and exits at
`x`) and `demand_passes` (the production VALUE demand of the plan cell IS the completion shell over
the plan's execution from `x`).

The bridge is then `member_bridge_settled` at `x`. Its premises, each a theorem of the instance:

* `probe_x` — production's probe at the flight answers the same identity and changes NOTHING: the
  navigation's first-time writes (a parameter's CALLABLE memo, an alias's binding cell and its
  projection — `probe_wrote`) were all made by the plan's own classification, and are read back;
* `not_minted` — the probe advanced no runtime-declaration identity (the non-minting domain; the
  minting class `MemberStabilityGuards.memberOriginRemintsRuntimeIdentity` stays outside);
* `selected`, `projection_x` — production's dot decision selects the declared member, and the plan's
  structural projection of the argumentless path reaches it;
* `settled_origin` — the receiver's navigation is settled at the state the member run reads its
  callee origin in, AFTER the member's alias resolution and the supply formation (`tA`, `uF`:
  whatever spread code the formation runs and whatever its outcome — a failing spread included);
* `production_completes`.

`settled_origin` is the premise `MemberStability.NavSettled` discharges in general; here it is
established on the actual states of the run.

## A boundary of provability (not of the bridge)

Two evaluator comparisons are made on PRINTED text: a property-cache key's `owner` component and an
alias binding cell's key are built with `reprStr`, whose pretty-printer (`Std.Format.pretty`, the
`partial` definition `be`) is an opaque constant of Lean core. Comparing two such strings built from
DIFFERENT scopes is therefore decidable by no kernel proof — not by evaluation and not symbolically.
An instance must not make such a comparison: so the spread operands here are written values (not
properties of another owner), the runtime-target alias's empty-bundle member has two output rows
(a one-row zero-parameter callee consults the alias-cell table, `valueViewCell?`), and the
parameter instances are written in the parameter owner's own body. The bridge theorem itself has no
such restriction; only the CONCRETE facts of a run that compares distinct printed keys are out of
the kernel's reach. Identical keys compare by reflexivity and are no obstacle. For the same reason
there is no instance over a CHAIN of two references (`AB2 = AB`): the chase's cycle check compares
the second step's printed key with the first's.
-/

open KatLang KatLang.CallPlan KatLang.EvaluatorCore KatLang.PlanRouteBridge KatLang.MemberStability
open KatLang.PlanAlgorithmBridgeInstances (completeB complete_of_B)
open KatLang.PlanAlgorithmBridgeInstances.Source (demand_passes_flight)

namespace KatLang.MemberStabilityInstances

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option cbv.maxSteps 20000000

/-! ## The source program -/

def metaParam (name : Ident) : CallableParameter := { name := name, kind := .metaRef }
def callN (f : Ident) (args : List Expr) : Expr := .call (.resolve f) args
def capture (e : Expr) : Expr := callN "Capture" [e]
def dot (t : Expr) (n : Ident) (args : Option OutputBundle) : Expr := .dotMember t n (.resolve n) args
def mul (a b : Expr) : Expr := .binary .mul a b
def add (a b : Expr) : Expr := .binary .add a b
def spreadOf (e : Expr) : Expr := .sequenceSpread e

/-- `{ G(x) = x * 10 ⏎ V = 7 }`. -/
def boxBlock : Algorithm :=
  algPrivate [] [] [("G", alg ["x"] [] [] [mul (.param "x") (.num 10)]), ("V", alg [] [] [] [.num 7])] []

/-- `FM(x) = { V = 7 ⏎ G(y) = y ⏎ Pair = { 7 ⏎ 8 } ⏎ x }`: a callable that declares members. -/
def fm : Algorithm :=
  algPrivate ["x"] []
    [("V", alg [] [] [] [.num 7]), ("G", alg ["y"] [] [] [.param "y"]), ("Pair", alg [] [] [] [.num 7, .num 8])]
    [.param "x"]

/-- `Capture(meta op) = op`; `Box`; `AB = Box` (a transparent reference);
    `Lib = { Sub = { H(x) = x + 1 ⏎ K = 3 } }`; `ALS = Lib.Sub` (a reference to a member path);
    `FM`; `RC = Capture(FM(0))`; `RTA = RC.Algorithm`, `RTC = Capture(FM(0)).Algorithm`
    (runtime-target aliases); the parameter owners `PV(b) = Capture(b.V())`,
    `PS(b) = Capture(b.V(()*))`, `PK(b) = Capture(b.Sub.K())`, `PF(b) = Capture(b.G((1 / 0)*))`;
    `OLib = { public OBox = Box's block }`, opened by the root. -/
def decls : List (Ident × Algorithm) :=
  [("Capture", algWithParameters [metaParam "op"] [] [] [.param "op"]),
   ("Box", boxBlock),
   ("AB", .alias none [] [] (.resolve "Box")),
   ("Lib", algPrivate [] [] [("Sub", algPrivate [] [] [
       ("H", alg ["x"] [] [] [add (.param "x") (.num 1)]), ("K", alg [] [] [] [.num 3])] [])] []),
   ("ALS", .alias none [] [] (dot (.resolve "Lib") "Sub" none)),
   ("FM", fm),
   ("RC", alg [] [] [] [capture (callN "FM" [.num 0])]),
   ("RTA", .alias none [] [] (dot (.resolve "RC") "Algorithm" none)),
   ("RTC", .alias none [] [] (dot (capture (callN "FM" [.num 0])) "Algorithm" none)),
   ("PV", alg ["b"] [] [] [capture (dot (.param "b") "V" (some []))]),
   ("PS", alg ["b"] [] [] [capture (dot (.param "b") "V" (some [spreadOf (.emptySequence 0)]))]),
   ("PK", alg ["b"] [] [] [capture (dot (dot (.param "b") "Sub" none) "K" (some []))]),
   ("PF", alg ["b"] [] [] [capture (dot (.param "b") "G" (some [spreadOf (.binary .div (.num 1) (.num 0))]))]),
   ("OLib", alg [] [] [publicProp "OBox" boxBlock] [])]

/-- The source program with the given root rows; the root opens `OLib`. -/
def program (rows : List Expr) : Expr := .algorithmExpr (algPrivate [] [.resolve "OLib"] decls rows)

/-- The program's root algorithm with the declaration identities `runResultM` assigns. -/
def rootOf (rows : List Expr) : Algorithm :=
  match (identifyPropertyExpr (program rows)).run' 0 with
  | .algorithmExpr a => a
  | _ => alg [] [] [] []

def base : EvalCtx := { callStack := [preludeAlg] }

/-- The context a program's root rows are evaluated in (`runResultM`'s wiring). -/
def ctxOf (rows : List Expr) : EvalCtx := base.push (wireToCaller base (rootOf rows))

/-! ## The flight of a dot-form plan, whatever its dot decision -/

/-- **The flight of a dot-form plan.** From the state where the VALUE shell marked the plan cell
    `evaluating`, the plan's FIRST route decision runs the receiver probe and the dot decision and
    records the selection's route: the flight state is the probe's exit with the route recorded. -/
theorem flight_member (a : Nat) (target : Expr) (N : Ident) (fallback : Expr) (args : OutputBundle) (ctx : EvalCtx)
    (env : ValEnv) (e e' : EvalState) (cell : NeedCell) (alg? : Option Algorithm) (sel : DotSelection)
    (hcell : e.needs[a]? = some cell) (hr : cell.route = none)
    (hprobe : (resolveDotReceiver? target ctx).runState e = (.ok alg?, e'))
    (hsel : selectDotEdge ctx target N alg? = .ok sel)
    (hstill : (e'.needs[a]?).bind NeedCell.route = none) :
    (withCtx (NeedPlan.CallShape.ctxMsg ⟨.dotMember target N fallback none, args, ctx, env, .dot target N fallback⟩)
        (NeedPlan.routeOf productionPlanRoute.classify a
          ⟨.dotMember target N fallback none, args, ctx, env, .dot target N fallback⟩)).runState e =
      (.ok (selectionRoute sel), withRoute a (selectionRoute sel) e') := by
  rw [KatLang.FiniteLoop.ctx_run, routeOf_fresh _ a _ e cell hcell hr]
  rw [classify_dot target N fallback args ctx env e e' alg? sel hprobe hsel]
  simp only [recordRoute, hstill]
  rfl

/-! ## `RefEmpty`: `AB.V()` — a TRANSPARENT REFERENCE, EMPTY bundle -/

namespace RefEmpty
/-- `AB = Box`: the receiver head is a transparent reference, navigated through its structure chase. -/
def target : Expr := .resolve "AB"
def N : Ident := "V"
def args : OutputBundle := []
def path : Expr := .dotMember target N (.resolve N) none
/-- The plan's written source `AB.V()`. -/
def src : Expr := .dotMember target N (.resolve N) (some args)
/-- THE SOURCE PROGRAM's one row: `Capture(AB.V())`. -/
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
    (((ordinaryCall productionPlanRoute 0 shape .call).runState x).1 = .ok (.atom 7, 1)) ∧
    (((NeedSupply.form evalSupplySpread ctx [] args).runState tA).1.toOption.map List.length = some 0) ∧
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

/-- Both sides return the value 7. -/
theorem value : ((ordinaryCall productionPlanRoute 0 shape .call).runState x).1 = .ok (.atom 7, 1) :=
  facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- The supply formation forms no cell. -/
theorem formation :
    ((NeedSupply.form evalSupplySpread ctx [] args).runState tA).1.toOption.map List.length = some 0 :=
  facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- The zero-supply invocation PUBLISHED the member's cache entry (CACHE-PUB-1) — on both sides, by
    `bridge`. -/
theorem published :
    ((ordinaryCall productionPlanRoute 0 shape .call).runState x).2.zeroArgPropertyCache.length =
      x.zeroArgPropertyCache.length + 1 :=
  facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

end RefEmpty

/-! ## `RefSpreadNone`: `AB.V(()*)` — a transparent reference, SPREAD-FIRST bundle forming NO cell -/

namespace RefSpreadNone
/-- The spread operand `()` is evaluated by the supply formation and supplies nothing. -/
def target : Expr := .resolve "AB"
def N : Ident := "V"
def args : OutputBundle := [.sequenceSpread (.emptySequence 0)]
def path : Expr := .dotMember target N (.resolve N) none
/-- The plan's written source `AB.V(()*)`. -/
def src : Expr := .dotMember target N (.resolve N) (some args)
/-- THE SOURCE PROGRAM's one row: `Capture(AB.V(()*))`. -/
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
    (((ordinaryCall productionPlanRoute 0 shape .call).runState x).1 = .ok (.atom 7, 1)) ∧
    (((NeedSupply.form evalSupplySpread ctx [] args).runState tA).1.toOption.map List.length = some 0) ∧
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

/-- Both sides return the value 7. -/
theorem value : ((ordinaryCall productionPlanRoute 0 shape .call).runState x).1 = .ok (.atom 7, 1) :=
  facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- The supply formation runs the spread and forms no cell. -/
theorem formation :
    ((NeedSupply.form evalSupplySpread ctx [] args).runState tA).1.toOption.map List.length = some 0 :=
  facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- The zero-supply invocation PUBLISHED the member's cache entry (CACHE-PUB-1) — on both sides, by
    `bridge`. -/
theorem published :
    ((ordinaryCall productionPlanRoute 0 shape .call).runState x).2.zeroArgPropertyCache.length =
      x.zeroArgPropertyCache.length + 1 :=
  facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

end RefSpreadNone

/-! ## `RefSpreadOne`: `AB.G([5]*)` — a transparent reference, SPREAD-FIRST bundle forming ONE cell -/

namespace RefSpreadOne
/-- The spread operand `[5]` supplies one Ready cell: `G(5) = 50`. -/
def target : Expr := .resolve "AB"
def N : Ident := "G"
def args : OutputBundle := [.sequenceSpread (.listLiteral [.num 5])]
def path : Expr := .dotMember target N (.resolve N) none
/-- The plan's written source `AB.G([5]*)`. -/
def src : Expr := .dotMember target N (.resolve N) (some args)
/-- THE SOURCE PROGRAM's one row: `Capture(AB.G([5]*))`. -/
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
    (((ordinaryCall productionPlanRoute 0 shape .call).runState x).1 = .ok (.atom 50, 1)) ∧
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

/-- Both sides return the value 50. -/
theorem value : ((ordinaryCall productionPlanRoute 0 shape .call).runState x).1 = .ok (.atom 50, 1) :=
  facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- The supply formation runs the spread and forms one cell. -/
theorem formation :
    ((NeedSupply.form evalSupplySpread ctx [] args).runState tA).1.toOption.map List.length = some 1 :=
  facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

end RefSpreadOne

/-! ## `RefSpreadFails`: `AB.G((1 / 0)*)` — a transparent reference, a FAILING SPREAD -/

namespace RefSpreadFails
/-- The spread operand fails: the formation fails, the origin is never read. -/
def target : Expr := .resolve "AB"
def N : Ident := "G"
def args : OutputBundle := [.sequenceSpread (.binary .div (.num 1) (.num 0))]
def path : Expr := .dotMember target N (.resolve N) none
/-- The plan's written source `AB.G((1 / 0)*)`. -/
def src : Expr := .dotMember target N (.resolve N) (some args)
/-- THE SOURCE PROGRAM's one row: `Capture(AB.G((1 / 0)*))`. -/
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
    (((NeedSupply.form evalSupplySpread ctx [] args).runState tA).1.toOption = none) ∧
    (((ordinaryCall productionPlanRoute 0 shape .call).runState x).1.toOption = none) := by
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

/-- **The spread FAILS**: the supply formation's failure is the run's, on both sides; the callee
    origin is never read. -/
theorem formation_fails :
    ((NeedSupply.form evalSupplySpread ctx [] args).runState tA).1.toOption = none :=
  facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem fails : ((ordinaryCall productionPlanRoute 0 shape .call).runState x).1.toOption = none :=
  facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

end RefSpreadFails

/-! ## `RefOrdinary`: `AB.G(2)` — a transparent reference, an ORDINARY bundle -/

namespace RefOrdinary
/-- A plain first argument: `G(2) = 20`. -/
def target : Expr := .resolve "AB"
def N : Ident := "G"
def args : OutputBundle := [.num 2]
def path : Expr := .dotMember target N (.resolve N) none
/-- The plan's written source `AB.G(2)`. -/
def src : Expr := .dotMember target N (.resolve N) (some args)
/-- THE SOURCE PROGRAM's one row: `Capture(AB.G(2))`. -/
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
    (((ordinaryCall productionPlanRoute 0 shape .call).runState x).1 = .ok (.atom 20, 1)) ∧
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

/-- Both sides return the value 20. -/
theorem value : ((ordinaryCall productionPlanRoute 0 shape .call).runState x).1 = .ok (.atom 20, 1) :=
  facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- The supply formation forms one suspended cell. -/
theorem formation :
    ((NeedSupply.form evalSupplySpread ctx [] args).runState tA).1.toOption.map List.length = some 1 :=
  facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

end RefOrdinary

end KatLang.MemberStabilityInstances
