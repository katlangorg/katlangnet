import KatLangArityLaws.NeedControl

open KatLang

/-!
# CallReference M1.5: invocation-plan laws over the AUTHORITATIVE definitions

Since M1.5 (October 2026) the invocation plan is part of `KatLang.lean` itself: a supplied cell
whose suspension is a supported written call IS a plan (identity = need address), its plan supply
lives in the production `NeedCell.plan` field, `NeedDemand.suspendedValue` executes the plan
(`NeedPlan.execute`) inside the ONE completion shell `NeedDemand.step`, and the public
`demandNeed` and the recursive `demandNeedRecursive` both install `productionPlanRoute`
(`resolveCalleeAlg`, `NeedPlan.normalizeCallee`, `evalSuppliedCallCounted`). META is
`NeedPlan.reify` (`reifyNeedCall`), explicit invocation `NeedPlan.invoke` (`invokeNeedCall`).
The M1 prototype state (`PlanState`, a plan table beside `EvalState`) is GONE.

Every theorem below is about those actual definitions. The quantified callbacks `ev`, `route`
and `demand` are exactly the parameters the production instantiates with `evalCounted`,
`productionPlanRoute` and `demandNeedRecursive` (`production_demand`, by `rfl`); since CallReference
S2 supply formation and preparation take the computed-spread capability `NeedSupply.SpreadEval`
(production `evalSupplySpread`, installed as `productionPlanRoute.spread`), quantified as `ev` in
the formation/preparation theorems and as `route.spread` in the execution theorems. Where a callback's
behavior matters, the assumption is a STRUCTURAL contract, never the conclusion:
* `Disciplined m`: `m` keeps every existing cell's suspension, completed VALUE and prepared plan
  supply. `NeedSupply.form`, `NeedPlan.prepare`, `NeedPlan.execute`, `NeedDemand.suspendedValue`,
  `NeedDemand.step`, `NeedPlan.reify` and `NeedPlan.invoke` are PROVED disciplined from their
  callbacks' discipline; that the `partial` production callbacks are disciplined is the one
  named opaque obligation `ProductionDiscipline` (source fact, executable guards). R7 (October
  2026): it is now a THEOREM, `KatLang.EvaluatorDiscipline.productionDiscipline_holds`
  (`KatLangArityLaws/EvaluatorDiscipline.lean`, which imports this file), in this exact general
  form; the `production_*` specializations below keep their hypothesis here and are restated
  without it there (`production_value_disciplined'`, …).
* `Oblivious a m` (only for `fresh_plan_is_ordinary_call`): `m` neither reads nor writes the plan
  record of cell `a`, over ALL valid input heaps and plan records. This is a sufficient
  abstract callback contract, NOT a property established for the production dispatch:
  dispatch can demand `a` when `a` is suspended. `CallPlanGuards.dispatchIsNotGloballyOblivious`
  pins that counterexample. Ordinary VALUE starts with `a` evaluating, a narrower invariant
  not expressed by this global contract; production conservativity remains executable evidence.

Not claimed (here; R7 adds the production bridge in `EvaluatorCore.lean` and discharges
`ProductionDiscipline` in `EvaluatorDiscipline.lean`): kernel refinement of the `partial` evaluator (`evalCounted`, `demandNeedRecursive`,
`evalSuppliedCallCounted`, `evalCallCountedExpr`) — that the ordinary call is `ordinaryCall` and
that the recursive edge installs `productionPlanRoute` are source facts, checked executably by
`InvocationPlanGuards`; C# concurrency, cancellation, terminality and resource accounting.
-/

namespace KatLang.CallPlan

theorem bind_run {α β : Type} (m : EvalM α) (f : α → EvalM β) (st : EvalState) :
    (m >>= f).runState st =
      (match m.runState st with
       | (.ok a, next) => (f a).runState next
       | (.error e, next) => (.error e, next)) :=
  KatLang.NeedControl.Allocation.bind_run m f st

theorem map_run {α β : Type} (f : α → β) (m : EvalM α) (st : EvalState) :
    (f <$> m).runState st =
      (match m.runState st with
       | (.ok a, next) => (.ok (f a), next)
       | (.error e, next) => (.error e, next)) :=
  KatLang.NeedControl.Collector.map_run f m st

theorem get_run (s : EvalState) : (get : EvalM EvalState).runState s = (.ok s, s) := rfl
theorem pure_run {α : Type} (a : α) (s : EvalState) : (pure a : EvalM α).runState s = (.ok a, s) := rfl
theorem modify_run (f : EvalState → EvalState) (s : EvalState) :
    (modify f : EvalM Unit).runState s = (.ok (), f s) := rfl
theorem throw_run {α : Type} (e : Error) (s : EvalState) :
    (throw e : EvalM α).runState s = (.error e, s) := rfl
theorem lift_run {α : Type} (o : Except Error α) (s : EvalState) :
    (monadLift o : EvalM α).runState s = (o, s) := by
  cases o <;> rfl
theorem evalAttempt_run {α : Type} (m : EvalM α) (s : EvalState) :
    (evalAttempt m).runState s =
      (if (m.runState s).1.isIncomplete then (.error .fuelExhausted, (m.runState s).2)
       else (.ok (m.runState s).1, (m.runState s).2)) := rfl

theorem captured_readonly (name : Ident) (ctx : EvalCtx) (s : EvalState) :
    ((capturedParameterActivation? name ctx).runState s).2 = s := by
  unfold capturedParameterActivation?
  repeat' (first | rfl | split | dsimp only | simp only [bind_run, get_run, pure_run, throw_run])

theorem captured_state {name : Ident} {ctx : EvalCtx} {s t : EvalState}
    {o : Except Error (Option ParameterActivation)}
    (h : (capturedParameterActivation? name ctx).runState s = (o, t)) : t = s := by
  have := captured_readonly name ctx s
  rw [h] at this
  exact this

theorem spread_slice_readonly (operand : Expr) (ctx : EvalCtx) (s : EvalState) :
    ((spreadCollectorSlice? operand ctx).runState s).2 = s := by
  unfold spreadCollectorSlice?
  repeat' (first | rfl | split | dsimp only | simp only [bind_run, get_run, pure_run, throw_run])
  all_goals exact captured_state (by assumption)


theorem supply_cases (source : Expr) (caller : EvalCtx) (values : ValEnv) (s : EvalState) :
    ((supplyNeed source caller values).runState s).2 = s ∨
    ((supplyNeed source caller values).runState s).2 =
      { s with needs := s.needs.push { suspension := .expression source caller values } } := by
  by_cases hp : ∃ name, source = .param name
  · obtain ⟨name, rfl⟩ := hp
    cases h : (capturedParameterActivation? name caller).runState s with
    | mk o t =>
      obtain rfl := captured_state h
      cases o with
      | error e =>
        left
        unfold supplyNeed
        simp only [bind_run, h]
      | ok activation =>
        cases hl : lookupAssoc name (activation.map ParameterActivation.needs |>.getD caller.needEnv) with
        | none =>
          right
          rw [KatLang.NeedControl.Allocation.supply_unbound_param name caller values t activation h hl]
        | some a =>
          left
          rw [KatLang.NeedControl.Allocation.supply_param_transports name caller values t activation a h hl]
  · right
    have hn : ∀ name, source ≠ .param name := fun name he => hp ⟨name, he⟩
    rw [KatLang.NeedControl.Allocation.supply_nonparameter source caller values s hn]


/-! ## Heap discipline -/

structure CellKept (c c' : NeedCell) : Prop where
  suspension : c'.suspension = c.suspension
  completed : ∀ o, c.state = .completed o → c'.state = .completed o
  prepared : ∀ o, c.plan = .prepared o → c'.plan = .prepared o
  /-- META-S3-4: a recorded plan route is never rewritten (`NeedPlan.routeOf`, first writer wins). -/
  routed : ∀ r, c.route = some r → c'.route = some r

theorem CellKept.refl (c : NeedCell) : CellKept c c := ⟨rfl, fun _ h => h, fun _ h => h, fun _ h => h⟩

theorem CellKept.trans {c d e : NeedCell} (h1 : CellKept c d) (h2 : CellKept d e) : CellKept c e :=
  ⟨h2.suspension.trans h1.suspension, fun o h => h2.completed o (h1.completed o h),
    fun o h => h2.prepared o (h1.prepared o h), fun r h => h2.routed r (h1.routed r h)⟩

def HeapKept (h h' : Array NeedCell) : Prop :=
  ∀ (a : Nat) (c : NeedCell), h[a]? = some c → ∃ c', h'[a]? = some c' ∧ CellKept c c'

theorem HeapKept.refl (h : Array NeedCell) : HeapKept h h := fun _ c hc => ⟨c, hc, CellKept.refl c⟩

theorem HeapKept.trans {h1 h2 h3 : Array NeedCell} (k1 : HeapKept h1 h2) (k2 : HeapKept h2 h3) :
    HeapKept h1 h3 := by
  intro a c hc
  obtain ⟨d, hd, kd⟩ := k1 a c hc
  obtain ⟨e, he, ke⟩ := k2 a d hd
  exact ⟨e, he, kd.trans ke⟩

theorem HeapKept.push (h : Array NeedCell) (c : NeedCell) : HeapKept h (h.push c) := by
  intro a d hd
  refine ⟨d, ?_, CellKept.refl d⟩
  have hlt : a < h.size := by
    rcases Nat.lt_or_ge a h.size with hl | hl
    · exact hl
    · rw [Array.getElem?_eq_none hl] at hd; cases hd
  rw [Array.getElem?_push]
  simp [Nat.ne_of_lt hlt, hd]

/-- A computation is DISCIPLINED when it keeps every existing cell's suspension, completed
    VALUE and prepared plan supply (it may allocate cells, project CALLABLE, begin VALUE of a
    suspended cell, prepare an unprepared plan, and change any non-heap state). By source
    inspection every production write is one of: `allocateNeed` (push), the CALLABLE memo of
    `projectNeedCallable`, the plan write of `NeedPlan.prepare` and the state writes of
    `NeedDemand.step` — the last two are proved disciplined below. -/
def Disciplined {α : Type} (m : EvalM α) : Prop :=
  ∀ s, HeapKept s.needs (m.runState s).2.needs

theorem disciplined_of_needs {α : Type} (m : EvalM α)
    (h : ∀ s, (m.runState s).2.needs = s.needs) : Disciplined m := by
  intro s
  rw [h s]
  exact HeapKept.refl _

theorem Disciplined.bind {α β : Type} {m : EvalM α} {f : α → EvalM β}
    (hm : Disciplined m) (hf : ∀ x, Disciplined (f x)) : Disciplined (m >>= f) := by
  intro s
  rw [bind_run]
  have k := hm s
  cases hr : m.runState s with
  | mk out t =>
    rw [hr] at k
    cases out with
    | error e => exact k
    | ok x => exact k.trans (hf x t)

theorem Disciplined.map {α β : Type} {m : EvalM α} (f : α → β) (hm : Disciplined m) :
    Disciplined (f <$> m) := by
  intro s
  rw [map_run]
  have k := hm s
  cases hr : m.runState s with
  | mk out t =>
    rw [hr] at k
    cases out <;> exact k

theorem disciplined_pure {α : Type} (a : α) : Disciplined (pure a : EvalM α) :=
  disciplined_of_needs _ (fun _ => rfl)

theorem disciplined_get : Disciplined (get : EvalM EvalState) :=
  disciplined_of_needs _ (fun _ => rfl)

theorem disciplined_throw {α : Type} (e : Error) : Disciplined (throw e : EvalM α) :=
  disciplined_of_needs _ (fun _ => rfl)

theorem disciplined_evalError {α : Type} (e : Error) : Disciplined (EvalM.error e : EvalM α) :=
  disciplined_of_needs _ (fun _ => rfl)

theorem disciplined_lift {α : Type} (o : Except Error α) : Disciplined (monadLift o : EvalM α) :=
  disciplined_of_needs _ (fun s => by rw [lift_run])

theorem Disciplined.attempt {α : Type} {m : EvalM α} (hm : Disciplined m) :
    Disciplined (evalAttempt m) := by
  intro s
  rw [evalAttempt_run]
  split <;> exact hm s

theorem Disciplined.withCtx {α : Type} {m : EvalM α} (c : String) (hm : Disciplined m) :
    Disciplined (withCtx c m) := by
  unfold KatLang.withCtx
  refine Disciplined.bind hm.attempt (fun r => ?_)
  cases r with
  | ok x => exact disciplined_pure x
  | error e => exact disciplined_evalError _

/-- META-DIAG-1: a META capture keeps the heap discipline of its capture. -/
theorem Disciplined.captureMeta (name : Ident) {m : EvalM Nat} (hm : Disciplined m) :
    Disciplined (NeedBinder.captureMeta name m) := by
  intro s
  have k := hm s
  show HeapKept s.needs ((NeedBinder.captureMeta name m).runState s).2.needs
  rw [NeedBinder.captureMeta_runState]
  revert k
  rcases m.runState s with ⟨r, t⟩
  intro k
  cases r <;> exact k

theorem disciplined_allocate (suspension : NeedSuspension) : Disciplined (allocateNeed suspension) := by
  intro s
  rw [KatLang.NeedControl.Allocation.allocate_run]
  exact HeapKept.push _ _

theorem disciplined_supply (source : Expr) (caller : EvalCtx) (values : ValEnv) :
    Disciplined (supplyNeed source caller values) := by
  intro s
  rcases supply_cases source caller values s with h | h <;> rw [h]
  · exact HeapKept.refl _
  · exact HeapKept.push _ _

theorem disciplined_mapM {α β : Type} (f : α → EvalM β) (hf : ∀ x, Disciplined (f x)) (xs : List α) :
    Disciplined (xs.mapM f) := by
  suffices h : ∀ (acc : List β), Disciplined (List.mapM.loop f xs acc) from h []
  induction xs with
  | nil => intro acc; exact disciplined_pure _
  | cons x rest ih =>
    intro acc
    exact Disciplined.bind (hf x) (fun y => ih (y :: acc))

theorem disciplined_slice (operand : Expr) (ctx : EvalCtx) :
    Disciplined (spreadCollectorSlice? operand ctx) :=
  disciplined_of_needs _ (fun s => by rw [spread_slice_readonly])

theorem disciplined_source (a : Nat) : Disciplined (needWrittenSource? a) :=
  disciplined_of_needs _ (fun s => by rw [KatLang.NeedControl.Provenance.source_run])

theorem disciplined_slot (ev : NeedSupply.SpreadEval)
    (hev : ∀ e c v, Disciplined (ev e c v)) (ctx : EvalCtx) (env : ValEnv) (e : Expr) :
    Disciplined (NeedSupply.slot ev ctx env e) := by
  cases e with
  | sequenceSpread operand =>
    refine Disciplined.bind (disciplined_slice operand ctx) (fun known => ?_)
    cases known with
    | some slice =>
      exact disciplined_mapM _ (fun a => Disciplined.bind (disciplined_source a)
        (fun _ => disciplined_pure _)) slice
    | none =>
      refine Disciplined.bind (hev _ _ _) (fun supplied => ?_)
      cases supplied with
      | items values =>
        exact disciplined_mapM _
          (fun v => Disciplined.bind (disciplined_allocate _) (fun _ => disciplined_pure _)) values
      | cells cells => exact disciplined_pure _
  | _ => exact Disciplined.bind (disciplined_supply _ _ _) (fun _ => disciplined_pure _)

theorem disciplined_form (ev : NeedSupply.SpreadEval)
    (hev : ∀ e c v, Disciplined (ev e c v)) (ctx : EvalCtx) (env : ValEnv) (args : OutputBundle) :
    Disciplined (NeedSupply.form ev ctx env args) := by
  induction args with
  | nil => exact disciplined_pure _
  | cons e rest ih =>
    exact Disciplined.bind (disciplined_slot ev hev ctx env e)
      (fun _ => Disciplined.bind ih (fun _ => disciplined_pure _))


/-- The plan write of `NeedPlan.setSupply`, as a state function. -/
def withPlan (a : Nat) (p : NeedPlanSupply) (s : EvalState) : EvalState :=
  { s with needs := s.needs.modify a (fun c => { c with plan := p }) }

theorem setSupply_run (a : Nat) (p : NeedPlanSupply) (s : EvalState) :
    (NeedPlan.setSupply a p).runState s = (.ok (), withPlan a p s) := rfl

/-! ## The four cases of the plan's supply preparation (actual `NeedPlan.prepare`) -/

theorem prepare_invalid (ev : NeedSupply.SpreadEval) (a : Nat)
    (shape : NeedPlan.CallShape) (s : EvalState) (h : s.needs[a]? = none) :
    (NeedPlan.prepare ev a shape).runState s = (.error (.illegalInEval "invalid need address"), s) := by
  simp only [NeedPlan.prepare, bind_run, get_run, h]
  rfl

/-- **Memoized preparation.** A prepared plan returns its recorded outcome — cells or an
    ordinary failure — changes nothing, and runs no evaluator: the result does not depend on
    `ev` at all. -/
theorem prepare_prepared (ev : NeedSupply.SpreadEval) (a : Nat)
    (shape : NeedPlan.CallShape) (s : EvalState) (cell : NeedCell)
    (outcome : Except Error (List NeedSupply.Sourced))
    (h : s.needs[a]? = some cell) (hp : cell.plan = .prepared outcome) :
    (NeedPlan.prepare ev a shape).runState s = (outcome, s) := by
  simp only [NeedPlan.prepare, bind_run, get_run, h, hp]
  cases outcome <;> rfl

/-- A reentrant preparation is a cycle, with no effect. -/
theorem prepare_preparing (ev : NeedSupply.SpreadEval) (a : Nat)
    (shape : NeedPlan.CallShape) (s : EvalState) (cell : NeedCell)
    (h : s.needs[a]? = some cell) (hp : cell.plan = .preparing) :
    (NeedPlan.prepare ev a shape).runState s = (.error .demandCycle, s) := by
  simp only [NeedPlan.prepare, bind_run, get_run, h, hp]
  rfl

/-- **First preparation.** An unprepared plan marks itself `preparing`, runs the ONE former
    `NeedSupply.form` exactly once over the plan's own written arguments in the plan's CALLER
    context, and records the outcome (success or failure) as `prepared`. -/
theorem prepare_unprepared (ev : NeedSupply.SpreadEval) (a : Nat)
    (shape : NeedPlan.CallShape) (s : EvalState) (cell : NeedCell)
    (h : s.needs[a]? = some cell) (hp : cell.plan = .unprepared)
    (hcomplete : ((NeedSupply.form ev shape.caller shape.values shape.args).runState
      (withPlan a .preparing s)).1.isIncomplete = false) :
    (NeedPlan.prepare ev a shape).runState s =
      (let r := (NeedSupply.form ev shape.caller shape.values shape.args).runState (withPlan a .preparing s)
       (r.1, withPlan a (.prepared r.1) r.2)) := by
  simp only [NeedPlan.prepare, bind_run, get_run, h, hp, setSupply_run, evalAttempt_run]
  revert hcomplete
  cases (NeedSupply.form ev shape.caller shape.values shape.args).runState (withPlan a .preparing s) with
  | mk out t =>
    intro hcomplete
    cases out with
    | ok _ => rfl
    | error e => cases e <;> first | rfl | (simp [Except.isIncomplete] at hcomplete)

/-- R7: an INCOMPLETE formation records nothing: the plan stays `preparing` and the incomplete
    outcome propagates with the formation's state. -/
theorem prepare_unprepared_incomplete (ev : NeedSupply.SpreadEval) (a : Nat)
    (shape : NeedPlan.CallShape) (s : EvalState) (cell : NeedCell)
    (h : s.needs[a]? = some cell) (hp : cell.plan = .unprepared)
    (hinc : ((NeedSupply.form ev shape.caller shape.values shape.args).runState
      (withPlan a .preparing s)).1.isIncomplete = true) :
    (NeedPlan.prepare ev a shape).runState s =
      (.error .fuelExhausted, ((NeedSupply.form ev shape.caller shape.values shape.args).runState
        (withPlan a .preparing s)).2) := by
  simp only [NeedPlan.prepare, bind_run, get_run, h, hp, setSupply_run, evalAttempt_run, hinc, if_true]


theorem modify_get (h : Array NeedCell) (a b : Nat) (f : NeedCell → NeedCell) :
    (h.modify a f)[b]? = if a = b then (h[b]?).map f else h[b]? := by
  rw [Array.getElem?_modify]

/-- A write at `a` whose result keeps the cell (per `CellKept`) keeps the heap. -/
theorem HeapKept.modify (h : Array NeedCell) (a : Nat) (f : NeedCell → NeedCell)
    (hf : ∀ c, h[a]? = some c → CellKept c (f c)) : HeapKept h (h.modify a f) := by
  intro b c hc
  rw [modify_get]
  by_cases hab : a = b
  · subst hab
    exact ⟨f c, by simp [hc], hf c hc⟩
  · exact ⟨c, by simp [hab, hc], CellKept.refl c⟩

/-- The one-cell bookkeeping write `modify a g` where `g` keeps the suspension: every other cell
    is untouched, and cell `a` keeps its suspension. -/
theorem bookkeeping_get (h : Array NeedCell) (a b : Nat) (g : NeedCell → NeedCell) (c : NeedCell)
    (hc : (h.modify a g)[b]? = some c) :
    (a = b ∧ ∃ c₀, h[b]? = some c₀ ∧ c = g c₀) ∨ (a ≠ b ∧ h[b]? = some c) := by
  rw [modify_get] at hc
  by_cases hab : a = b
  · left
    refine ⟨hab, ?_⟩
    simp only [hab, if_true] at hc
    cases h0 : h[b]? with
    | none => rw [h0] at hc; cases hc
    | some c₀ => rw [h0] at hc; exact ⟨c₀, rfl, (Option.some.inj hc).symm⟩
  · right
    simp only [hab, if_false] at hc
    exact ⟨hab, hc⟩

theorem keep_withPlan_preparing (s : EvalState) (a : Nat) (cell : NeedCell)
    (h : s.needs[a]? = some cell) (hp : cell.plan = .unprepared) :
    HeapKept s.needs (withPlan a .preparing s).needs := by
  intro b c hc
  by_cases hab : a = b
  · subst hab
    rw [h] at hc; cases hc
    refine ⟨{ cell with plan := .preparing }, by simp [withPlan, modify_get, h], rfl, fun _ ho => ho, ?_,
      fun _ ho => ho⟩
    intro o ho; rw [hp] at ho; cases ho
  · exact ⟨c, by simp [withPlan, modify_get, hab, hc], CellKept.refl c⟩


/-- **Preparation is disciplined**: it writes only the plan record of its own cell `a`, and
    only from `unprepared`; any formation effect is a disciplined evaluator's. -/
theorem disciplined_prepare (ev : NeedSupply.SpreadEval)
    (hev : ∀ e c v, Disciplined (ev e c v)) (a : Nat) (shape : NeedPlan.CallShape) :
    Disciplined (NeedPlan.prepare ev a shape) := by
  intro s
  cases h : s.needs[a]? with
  | none => rw [prepare_invalid ev a shape s h]; exact HeapKept.refl _
  | some cell =>
    cases hp : cell.plan with
    | prepared o => rw [prepare_prepared ev a shape s cell o h hp]; exact HeapKept.refl _
    | preparing => rw [prepare_preparing ev a shape s cell h hp]; exact HeapKept.refl _
    | unprepared =>
      cases hinc : ((NeedSupply.form ev shape.caller shape.values shape.args).runState
          (withPlan a .preparing s)).1.isIncomplete with
      | true =>
        rw [prepare_unprepared_incomplete ev a shape s cell h hp hinc]
        exact (keep_withPlan_preparing s a cell h hp).trans
          (disciplined_form ev hev shape.caller shape.values shape.args (withPlan a .preparing s))
      | false =>
      rw [prepare_unprepared ev a shape s cell h hp hinc]
      dsimp only
      generalize hr : (NeedSupply.form ev shape.caller shape.values shape.args).runState
        (withPlan a .preparing s) = r
      have kf := disciplined_form ev hev shape.caller shape.values shape.args (withPlan a .preparing s)
      rw [hr] at kf
      intro b c hc
      by_cases hab : a = b
      · subst hab
        rw [h] at hc
        cases hc
        -- cell `a`: through the `preparing` mark, the formation and the record.
        have h1 : (withPlan a .preparing s).needs[a]? = some { cell with plan := .preparing } := by
          simp [withPlan, modify_get, h]
        obtain ⟨c1, hc1, k1⟩ := kf a _ h1
        refine ⟨{ c1 with plan := .prepared r.1 }, by simp [withPlan, modify_get, hc1], ?_⟩
        refine ⟨k1.suspension, fun o ho => k1.completed o ho, fun o ho => ?_, fun r hr => k1.routed r hr⟩
        rw [hp] at ho
        cases ho
      · have h1 : (withPlan a .preparing s).needs[b]? = some c := by
          simp [withPlan, modify_get, hab, hc]
        obtain ⟨c1, hc1, k1⟩ := kf b c h1
        exact ⟨c1, by simp [withPlan, modify_get, hab, hc1], k1⟩

/-- A route's effective shape keeps the plan's captured caller context and values (only an
    extension changes the callee and the bundle). -/
@[simp] theorem effective_caller (shape : NeedPlan.CallShape) (r : PlanRoute) :
    (NeedPlan.effective shape r).caller = shape.caller := by
  cases r <;> simp only [NeedPlan.effective] <;> split <;> rfl

@[simp] theorem effective_values (shape : NeedPlan.CallShape) (r : PlanRoute) :
    (NeedPlan.effective shape r).values = shape.values := by
  cases r <;> simp only [NeedPlan.effective] <;> split <;> rfl

/-- The route write of `NeedPlan.setRoute`, as a state function (META-S3-4). -/
def withRoute (a : Nat) (r : PlanRoute) (s : EvalState) : EvalState :=
  { s with needs := s.needs.modify a (fun c => { c with route := some r }) }

theorem setRoute_run (a : Nat) (r : PlanRoute) (s : EvalState) :
    (NeedPlan.setRoute a r).runState s = (.ok (), withRoute a r s) := rfl

/-- The callee write of `NeedPlan.setCallee`, as a state function. -/
def withCallee (a c : Nat) (s : EvalState) : EvalState :=
  { s with needs := s.needs.modify a (fun cell => { cell with callee := some c }) }

theorem setCallee_run (a c : Nat) (s : EvalState) :
    (NeedPlan.setCallee a c).runState s = (.ok (), withCallee a c s) := rfl

/-- A FIRST route record keeps every cell (it writes neither suspension, VALUE nor supply, and only
    an unrecorded route). -/
theorem keep_withRoute (s : EvalState) (a : Nat) (r : PlanRoute)
    (hnone : ∀ c, s.needs[a]? = some c → c.route = none) :
    HeapKept s.needs (withRoute a r s).needs :=
  HeapKept.modify _ a _ (fun c hc => ⟨rfl, fun _ h => h, fun _ h => h,
    fun r' h => by rw [hnone c hc] at h; cases h⟩)

/-- A callee record keeps every cell. -/
theorem keep_withCallee (s : EvalState) (a c : Nat) :
    HeapKept s.needs (withCallee a c s).needs :=
  HeapKept.modify _ a _ (fun _ _ => ⟨rfl, fun _ h => h, fun _ h => h, fun _ h => h⟩)

theorem disciplined_setCallee (a c : Nat) : Disciplined (NeedPlan.setCallee a c) := by
  intro s; rw [setCallee_run]; exact keep_withCallee s a c

/-! ## The plan's ROUTE (META-S3-4): one record, written by the first classification -/

theorem routeOf_invalid (classify : NeedPlan.CallShape → EvalM PlanRoute) (a : Nat)
    (shape : NeedPlan.CallShape) (s : EvalState) (h : s.needs[a]? = none) :
    (NeedPlan.routeOf classify a shape).runState s = (.error (.illegalInEval "invalid need address"), s) := by
  simp only [NeedPlan.routeOf, bind_run, get_run, h]
  rfl

/-- **Route stickiness.** A recorded route is returned as it is: nothing is classified, nothing
    changes. -/
theorem routeOf_recorded (classify : NeedPlan.CallShape → EvalM PlanRoute) (a : Nat)
    (shape : NeedPlan.CallShape) (s : EvalState) (cell : NeedCell) (r : PlanRoute)
    (h : s.needs[a]? = some cell) (hr : cell.route = some r) :
    (NeedPlan.routeOf classify a shape).runState s = (.ok r, s) := by
  simp only [NeedPlan.routeOf, bind_run, get_run, h, hr]
  rfl

/-- The record step after a classification: a route recorded meanwhile wins; otherwise `r` is
    recorded. -/
def recordRoute (a : Nat) (r : PlanRoute) (t : EvalState) : PlanRoute × EvalState :=
  match (t.needs[a]?).bind NeedCell.route with
  | some recorded => (recorded, t)
  | none => (r, withRoute a r t)

/-- **First classification.** An unrecorded route runs the classifier ONCE over the plan's shape
    and records a successful result (unless the route was recorded meanwhile, whose record wins); a
    failure records nothing and propagates. -/
theorem routeOf_fresh (classify : NeedPlan.CallShape → EvalM PlanRoute) (a : Nat)
    (shape : NeedPlan.CallShape) (s : EvalState) (cell : NeedCell)
    (h : s.needs[a]? = some cell) (hr : cell.route = none) :
    (NeedPlan.routeOf classify a shape).runState s =
      (match (classify shape).runState s with
       | (.ok r, t) => (.ok (recordRoute a r t).1, (recordRoute a r t).2)
       | (.error e, t) => (.error e, t)) := by
  simp only [NeedPlan.routeOf, bind_run, get_run, h, hr]
  rcases (classify shape).runState s with ⟨_ | r, t⟩
  · rfl
  · simp only [recordRoute]
    cases hb : (t.needs[a]?).bind NeedCell.route <;> first | rfl | (simp only [hb]; rfl)

theorem keep_recordRoute (a : Nat) (r : PlanRoute) (t : EvalState) :
    HeapKept t.needs (recordRoute a r t).2.needs := by
  unfold recordRoute
  split
  · exact HeapKept.refl _
  · rename_i hno
    exact keep_withRoute t a r (fun c hc => by simpa [hc] using hno)

theorem disciplined_setRoute_first (a : Nat) (r : PlanRoute) (s : EvalState)
    (hnone : ∀ c, s.needs[a]? = some c → c.route = none) :
    HeapKept s.needs ((NeedPlan.setRoute a r).runState s).2.needs := by
  rw [setRoute_run]; exact keep_withRoute s a r hnone

theorem disciplined_routeOf (classify : NeedPlan.CallShape → EvalM PlanRoute)
    (hclassify : ∀ shape, Disciplined (classify shape)) (a : Nat) (shape : NeedPlan.CallShape) :
    Disciplined (NeedPlan.routeOf classify a shape) := by
  intro s
  cases h : s.needs[a]? with
  | none => rw [routeOf_invalid classify a shape s h]; exact HeapKept.refl _
  | some cell =>
    cases hr : cell.route with
    | some r => rw [routeOf_recorded classify a shape s cell r h hr]; exact HeapKept.refl _
    | none =>
      rw [routeOf_fresh classify a shape s cell h hr]
      have k := hclassify shape s
      rcases hc : (classify shape).runState s with ⟨_ | r, t⟩ <;> rw [hc] at k
      · exact k
      · exact k.trans (keep_recordRoute a r t)

/-- **The callee cell's establishment is disciplined**: the route (its classifier's discipline), at
    most one supplied cell (`supplyNeed`) and the callee record. -/
theorem disciplined_calleeCell (classify : NeedPlan.CallShape → EvalM PlanRoute)
    (hclassify : ∀ shape, Disciplined (classify shape)) (a : Nat) :
    Disciplined (NeedPlan.calleeCell classify a) := by
  have hjoin : ∀ (eff : NeedPlan.CallShape), Disciplined (do
      let c ← supplyNeed eff.callee eff.caller eff.values
      NeedPlan.setCallee a c
      pure c : EvalM Nat) := fun eff =>
    Disciplined.bind (disciplined_supply _ _ _) (fun c =>
      Disciplined.bind (disciplined_setCallee a c) (fun _ => disciplined_pure _))
  unfold NeedPlan.calleeCell
  refine Disciplined.bind disciplined_get (fun st => ?_)
  split
  next cell _ =>
    split
    next => exact disciplined_pure _
    next =>
      split
      next => exact disciplined_throw _
      next shape _ =>
        refine Disciplined.bind (disciplined_routeOf classify hclassify a shape) (fun r => ?_)
        dsimp only
        split
        next => exact Disciplined.bind (disciplined_throw _) (fun _ => hjoin _)
        next => exact hjoin _
  next => exact disciplined_throw _

theorem disciplined_calleeAlong (route : NeedPlan.Route)
    (htarget : ∀ f c, Disciplined (route.target f c))
    (hclassify : ∀ shape, Disciplined (route.classify shape))
    (hproject : ∀ c, Disciplined (route.project c))
    (a : Nat) (eff : NeedPlan.CallShape) (r : PlanRoute) :
    Disciplined (NeedPlan.calleeAlong route a eff r) := by
  cases r with
  | algorithm =>
    simp only [NeedPlan.calleeAlong]
    refine Disciplined.bind (disciplined_calleeCell route.classify hclassify a) (fun c => ?_)
    refine Disciplined.bind (hproject c) (fun o => ?_)
    cases o with
    | some _ => exact disciplined_pure _
    | none => exact disciplined_throw _
  | intrinsic => exact disciplined_throw _
  | call => exact htarget _ _
  | extension => exact htarget _ _

/-- META-S3-4-DIAG: the dispatch name is a pure read of the heap — it changes nothing. -/
theorem dispatchName_run (a : Nat) (eff : NeedPlan.CallShape) (r : PlanRoute) (s : EvalState) :
    (NeedPlan.dispatchName a eff r).runState s = (.ok (NeedPlan.dispatchNameIn s.needs a eff r), s) := rfl

theorem disciplined_dispatchName (a : Nat) (eff : NeedPlan.CallShape) (r : PlanRoute) :
    Disciplined (NeedPlan.dispatchName a eff r) := by
  unfold NeedPlan.dispatchName
  exact Disciplined.bind disciplined_get (fun _ => disciplined_pure _)

/-- CACHE-PUB-1: the dispatch ORIGIN is a pure read of the heap — it changes nothing. -/
theorem dispatchOrigin_run (a : Nat) (eff : NeedPlan.CallShape) (r : PlanRoute) (s : EvalState) :
    (NeedPlan.dispatchOrigin a eff r).runState s = (.ok (NeedPlan.dispatchOriginIn s.needs a eff r), s) := rfl

theorem disciplined_dispatchOrigin (a : Nat) (eff : NeedPlan.CallShape) (r : PlanRoute) :
    Disciplined (NeedPlan.dispatchOrigin a eff r) := by
  unfold NeedPlan.dispatchOrigin
  exact Disciplined.bind disciplined_get (fun _ => disciplined_pure _)

/-- **One plan execution along a route is disciplined** whenever its installed callbacks are. -/
theorem disciplined_executeAlong (route : NeedPlan.Route)
    (hspread : ∀ e c v, Disciplined (route.spread e c v))
    (htarget : ∀ f c, Disciplined (route.target f c))
    (hnormal : ∀ g c, Disciplined (route.normalize g c))
    (hdispatch : ∀ o g cells c v n, Disciplined (route.dispatch o g cells c v n))
    (hclassify : ∀ shape, Disciplined (route.classify shape))
    (hproject : ∀ c, Disciplined (route.project c))
    (a : Nat) (shape : NeedPlan.CallShape) (r : PlanRoute) :
    Disciplined (NeedPlan.executeAlong route a shape r) := by
  unfold NeedPlan.executeAlong
  exact Disciplined.bind (Disciplined.withCtx _
      (disciplined_calleeAlong route htarget hclassify hproject a _ r)) (fun callee =>
    Disciplined.bind (disciplined_dispatchName a _ r) (fun name =>
    Disciplined.bind (disciplined_dispatchOrigin a _ r) (fun origin =>
    Disciplined.bind (Disciplined.withCtx _ (Disciplined.bind (hnormal _ _) (fun normal =>
      Disciplined.bind (disciplined_prepare route.spread hspread a _) (fun cells => hdispatch _ _ _ _ _ _))))
      (fun _ => disciplined_pure _))))

/-- **One plan execution is disciplined** whenever its installed callbacks are. -/
theorem disciplined_execute (route : NeedPlan.Route)
    (hspread : ∀ e c v, Disciplined (route.spread e c v))
    (htarget : ∀ f c, Disciplined (route.target f c))
    (hnormal : ∀ g c, Disciplined (route.normalize g c))
    (hdispatch : ∀ o g cells c v n, Disciplined (route.dispatch o g cells c v n))
    (hclassify : ∀ shape, Disciplined (route.classify shape))
    (hproject : ∀ c, Disciplined (route.project c))
    (a : Nat) (shape : NeedPlan.CallShape) :
    Disciplined (NeedPlan.execute route a shape) := by
  unfold NeedPlan.execute
  refine Disciplined.bind (Disciplined.withCtx _ (disciplined_routeOf route.classify hclassify a shape)) (fun r => ?_)
  cases r with
  | intrinsic => exact disciplined_throw _
  | _ => exact disciplined_executeAlong route hspread htarget hnormal hdispatch hclassify hproject a shape _

theorem disciplined_suspendedValue (ev : Expr → EvalCtx → ValEnv → EvalM CountedResult)
    (route : NeedPlan.Route) (demand : Nat → EvalM CountedResult)
    (hev : ∀ e c v, Disciplined (ev e c v))
    (hspread : ∀ e c v, Disciplined (route.spread e c v))
    (htarget : ∀ f c, Disciplined (route.target f c))
    (hnormal : ∀ g c, Disciplined (route.normalize g c))
    (hdispatch : ∀ o g cells c v n, Disciplined (route.dispatch o g cells c v n))
    (hclassify : ∀ shape, Disciplined (route.classify shape))
    (hproject : ∀ c, Disciplined (route.project c))
    (hdemand : ∀ b, Disciplined (demand b)) (a : Nat) (suspension : NeedSuspension) :
    Disciplined (NeedDemand.suspendedValue ev route demand a suspension) := by
  cases suspension with
  | ready value => exact disciplined_pure _
  | expression e c v =>
    simp only [NeedDemand.suspendedValue]
    split
    · refine Disciplined.bind (Disciplined.withCtx _ (disciplined_routeOf route.classify hclassify a _)) (fun r => ?_)
      cases r with
      | intrinsic => exact Disciplined.map _ (hev e c v)
      | _ => exact disciplined_executeAlong route hspread htarget hnormal hdispatch hclassify hproject a _ _
    · exact Disciplined.map _ (hev e c v)
  | collector slice =>
    exact Disciplined.bind (disciplined_mapM _ (fun b => Disciplined.map _ (hdemand b)) slice)
      (fun _ => disciplined_pure _)

/-- The completion-shell state write, as a state function. -/
def withState (a : Nat) (st : NeedState) (s : EvalState) : EvalState :=
  { s with needs := s.needs.modify a (fun c => { c with state := st }) }

/-- **The VALUE completion shell is disciplined** whenever its callbacks are: it begins and
    completes only a SUSPENDED cell, so no completed VALUE is ever overwritten, and it touches
    no suspension and no prepared plan. -/
theorem disciplined_step (ev : Expr → EvalCtx → ValEnv → EvalM CountedResult)
    (route : NeedPlan.Route) (demand : Nat → EvalM CountedResult)
    (hev : ∀ e c v, Disciplined (ev e c v))
    (hspread : ∀ e c v, Disciplined (route.spread e c v))
    (htarget : ∀ f c, Disciplined (route.target f c))
    (hnormal : ∀ g c, Disciplined (route.normalize g c))
    (hdispatch : ∀ o g cells c v n, Disciplined (route.dispatch o g cells c v n))
    (hclassify : ∀ shape, Disciplined (route.classify shape))
    (hproject : ∀ c, Disciplined (route.project c))
    (hdemand : ∀ b, Disciplined (demand b)) (a : Nat) :
    Disciplined (NeedDemand.step ev route demand a) := by
  intro s
  cases h : s.needs[a]? with
  | none =>
    rw [KatLang.NeedControl.Production.invalid_address ev route demand a s h]
    exact HeapKept.refl _
  | some cell =>
    cases hs : cell.state with
    | completed o =>
      rw [KatLang.NeedControl.Memo.completed_sticky ev route demand a s cell o h hs]
      exact HeapKept.refl _
    | evaluating =>
      rw [KatLang.NeedControl.Production.evaluating_cycle ev route demand a s cell h hs]
      exact HeapKept.refl _
    | suspended =>
      have kv := disciplined_suspendedValue ev route demand hev hspread htarget hnormal hdispatch hclassify hproject hdemand a
        cell.suspension (withState a .evaluating s)
      generalize hr : (NeedDemand.suspendedValue ev route demand a cell.suspension).runState
        (withState a .evaluating s) = r at kv
      rcases r with ⟨outcome, t⟩
      cases hinc : outcome.isIncomplete with
      | true =>
        rw [KatLang.NeedControl.Memo.suspended_incomplete ev route demand a s t cell outcome h hs hr hinc]
        refine HeapKept.trans ?_ kv
        intro b c hc
        by_cases hab : a = b
        · subst hab
          rw [h] at hc; cases hc
          refine ⟨{ cell with state := .evaluating }, by simp [withState, modify_get, h], rfl, ?_, fun _ ho => ho,
            fun _ ho => ho⟩
          intro o ho; rw [hs] at ho; cases ho
        · exact ⟨c, by simp [withState, modify_get, hab, hc], CellKept.refl c⟩
      | false =>
      rw [KatLang.NeedControl.Memo.suspended_retains_state ev route demand a s t cell outcome h hs hr hinc]
      intro b c hc
      by_cases hab : a = b
      · subst hab
        rw [h] at hc
        cases hc
        have h1 : (withState a .evaluating s).needs[a]? = some { cell with state := .evaluating } := by
          simp [withState, modify_get, h]
        obtain ⟨c1, hc1, k1⟩ := kv a _ h1
        refine ⟨{ c1 with state := .completed outcome }, by simp [modify_get, hc1], ?_⟩
        refine ⟨k1.suspension, fun o ho => ?_, fun o ho => k1.prepared o ho, fun r hr => k1.routed r hr⟩
        rw [hs] at ho
        cases ho
      · have h1 : (withState a .evaluating s).needs[b]? = some c := by
          simp [withState, modify_get, hab, hc]
        obtain ⟨c1, hc1, k1⟩ := kv b c h1
        exact ⟨c1, by simp [modify_get, hab, hc1], k1⟩


/-! ## META: stable, inert reification (actual `NeedPlan.reify`) -/

theorem reify_run (a : Nat) (s : EvalState) :
    (NeedPlan.reify a).runState s = (NeedPlan.reifyResult s.needs a, s) := by
  simp only [NeedPlan.reify, bind_run, get_run]
  cases NeedPlan.reifyResult s.needs a <;> rfl

/-- **Capture inertia.** META leaves the WHOLE run state as it was: no target resolution or
    execution, no argument VALUE demand, no supply preparation (the plan record is unchanged),
    no spread, no allocation, no binding context. -/
theorem reify_inert (a : Nat) (s : EvalState) : ((NeedPlan.reify a).runState s).2 = s := by
  rw [reify_run]

/-- **Plan identity.** A supplied call reifies to the reference whose plan is its own address. -/
theorem reify_identity (a : Nat) (s : EvalState) (shape : NeedPlan.CallShape)
    (h : NeedPlan.shapeAt? s.needs a = some shape) :
    (NeedPlan.reify a).runState s = (.ok ⟨a⟩, s) := by
  rw [reify_run]
  simp [NeedPlan.reifyResult, h]

/-- Two META observations of one address yield the same identity and leave the state as it was. -/
theorem reify_repeated (a : Nat) (s : EvalState) :
    (do let r₁ ← NeedPlan.reify a; let r₂ ← NeedPlan.reify a; pure (r₁, r₂) : EvalM _).runState s =
      (match NeedPlan.reifyResult s.needs a with
       | .ok r => .ok (r, r)
       | .error e => .error e, s) := by
  rw [bind_run, reify_run]
  cases h : NeedPlan.reifyResult s.needs a with
  | error e => rfl
  | ok r => simp only [bind_run, reify_run, h]; rfl

/-- META refuses what is not a supported supplied call, with no effect. -/
theorem reify_refuses (a : Nat) (s : EvalState) (h : NeedPlan.shapeAt? s.needs a = none) :
    (NeedPlan.reify a).runState s = (.error NeedPlan.metaRefusal, s) := by
  rw [reify_run]
  simp [NeedPlan.reifyResult, h]

theorem disciplined_reify (a : Nat) : Disciplined (NeedPlan.reify a) :=
  disciplined_of_needs _ (fun s => by rw [reify_inert])

/-- A disciplined computation never changes which plan a cell is. -/
theorem shapeAt_kept {h h' : Array NeedCell} (k : HeapKept h h') (a : Nat)
    (shape : NeedPlan.CallShape) (hs : NeedPlan.shapeAt? h a = some shape) :
    NeedPlan.shapeAt? h' a = some shape := by
  unfold NeedPlan.shapeAt? at hs ⊢
  cases hc : h[a]? with
  | none => rw [hc] at hs; cases hs
  | some c =>
    rw [hc] at hs
    obtain ⟨c', hc', kc⟩ := k a c hc
    rw [hc']
    show NeedPlan.ofSuspension? c'.suspension = some shape
    rw [kc.suspension]
    exact hs

/-- **Stable reification after any disciplined observation**: after VALUE (successful OR
    failed), after explicit invocations, after forwarding, META still reifies the same plan. -/
theorem meta_after {α : Type} (m : EvalM α) (hm : Disciplined m) (a : Nat) (s : EvalState)
    (shape : NeedPlan.CallShape) (hs : NeedPlan.shapeAt? s.needs a = some shape) :
    (NeedPlan.reify a).runState (m.runState s).2 = (.ok ⟨a⟩, (m.runState s).2) :=
  reify_identity a _ shape (shapeAt_kept (hm s) a shape hs)

/-! ## Explicit invocation (actual `NeedPlan.invoke`) -/

theorem invoke_run (route : NeedPlan.Route)
    (a : Nat) (s : EvalState) (shape : NeedPlan.CallShape)
    (h : NeedPlan.shapeAt? s.needs a = some shape) :
    (NeedPlan.invoke route ⟨a⟩).runState s = (NeedPlan.execute route a shape).runState s := by
  simp only [NeedPlan.invoke, bind_run, get_run, h]

theorem invoke_refuses (route : NeedPlan.Route)
    (a : Nat) (s : EvalState) (h : NeedPlan.shapeAt? s.needs a = none) :
    (NeedPlan.invoke route ⟨a⟩).runState s = (.error NeedPlan.metaRefusal, s) := by
  simp only [NeedPlan.invoke, bind_run, get_run, h]
  rfl

theorem disciplined_invoke (route : NeedPlan.Route)
    (hspread : ∀ e c v, Disciplined (route.spread e c v))
    (htarget : ∀ f c, Disciplined (route.target f c))
    (hnormal : ∀ g c, Disciplined (route.normalize g c))
    (hdispatch : ∀ o g cells c v n, Disciplined (route.dispatch o g cells c v n))
    (hclassify : ∀ shape, Disciplined (route.classify shape))
    (hproject : ∀ c, Disciplined (route.project c))
    (r : NeedPlan.CallReference) : Disciplined (NeedPlan.invoke route r) := by
  intro s
  cases h : NeedPlan.shapeAt? s.needs r.plan with
  | none => rw [invoke_refuses route r.plan s h]; exact HeapKept.refl _
  | some shape =>
    rw [invoke_run route r.plan s shape h]
    exact disciplined_execute route hspread htarget hnormal hdispatch hclassify hproject r.plan shape s

/-! ## The original VALUE and the plan's supply survive every disciplined computation -/

/-- **VALUE completion independence.** Once the original cell's VALUE completed (success or
    ordinary failure), no disciplined computation — META, any number of explicit invocations,
    forwarding — changes it: the next VALUE demand returns the same outcome and does nothing. -/
theorem completed_survives {α : Type} (m : EvalM α) (hm : Disciplined m)
    (ev : Expr → EvalCtx → ValEnv → EvalM CountedResult) (route : NeedPlan.Route)
    (demand : Nat → EvalM CountedResult) (a : Nat) (s : EvalState) (cell : NeedCell)
    (outcome : Except Error CountedResult)
    (hc : s.needs[a]? = some cell) (hs : cell.state = .completed outcome) :
    (NeedDemand.step ev route demand a).runState (m.runState s).2 = (outcome, (m.runState s).2) := by
  obtain ⟨c', hc', k⟩ := hm s a cell hc
  exact KatLang.NeedControl.Memo.completed_sticky ev route demand a _ c' outcome hc' (k.completed outcome hs)

/-- **Single preparation.** Once a plan's supply is prepared (cells or an ordinary failure), every
    later preparation after any disciplined computation returns exactly that outcome, changes
    nothing and runs no evaluator: `NeedSupply.form` never runs again for this plan. -/
theorem prepared_survives {α : Type} (m : EvalM α) (hm : Disciplined m)
    (ev : NeedSupply.SpreadEval) (a : Nat) (shape : NeedPlan.CallShape)
    (s : EvalState) (cell : NeedCell) (outcome : Except Error (List NeedSupply.Sourced))
    (hc : s.needs[a]? = some cell) (hp : cell.plan = .prepared outcome) :
    (NeedPlan.prepare ev a shape).runState (m.runState s).2 = (outcome, (m.runState s).2) := by
  obtain ⟨c', hc', k⟩ := hm s a cell hc
  exact prepare_prepared ev a shape _ c' outcome hc' (k.prepared outcome hp)

/-- The first preparation records exactly the outcome of its one formation (given a
    disciplined evaluator, which keeps the cell present). -/
theorem prepare_records (ev : NeedSupply.SpreadEval)
    (hev : ∀ e c v, Disciplined (ev e c v)) (a : Nat) (shape : NeedPlan.CallShape)
    (s : EvalState) (cell : NeedCell) (h : s.needs[a]? = some cell) (hp : cell.plan = .unprepared)
    (hcomplete : ((NeedSupply.form ev shape.caller shape.values shape.args).runState
      (withPlan a .preparing s)).1.isIncomplete = false) :
    ∃ c', ((NeedPlan.prepare ev a shape).runState s).2.needs[a]? = some c' ∧
      c'.plan = .prepared ((NeedPlan.prepare ev a shape).runState s).1 ∧
      ((NeedPlan.prepare ev a shape).runState s).1 =
        ((NeedSupply.form ev shape.caller shape.values shape.args).runState (withPlan a .preparing s)).1 := by
  rw [prepare_unprepared ev a shape s cell h hp hcomplete]
  dsimp only
  have h1 : (withPlan a .preparing s).needs[a]? = some { cell with plan := .preparing } := by
    simp [withPlan, modify_get, h]
  obtain ⟨c1, hc1, _⟩ := disciplined_form ev hev shape.caller shape.values shape.args _ a _ h1
  refine ⟨{ c1 with plan := .prepared _ }, ?_, rfl, rfl⟩
  simp only [withPlan] at hc1 ⊢
  simp [modify_get, hc1]

/-! ## One shared supply for VALUE and every invocation -/

/-- A plan's computation along route `r` over given argument cells: `executeAlong` with the supply
    already formed. -/
def callOver (route : NeedPlan.Route) (a : Nat) (shape : NeedPlan.CallShape) (r : PlanRoute)
    (cells : List NeedSupply.Sourced) : EvalM CountedResult := do
  let eff := NeedPlan.effective shape r
  let callee ← withCtx shape.ctxMsg (NeedPlan.calleeAlong route a eff r)
  let name ← NeedPlan.dispatchName a eff r
  let origin ← NeedPlan.dispatchOrigin a eff r
  let result ← withCtx shape.ctxMsg (do
    let normal ← route.normalize callee eff.caller
    route.dispatch origin normal cells eff.caller eff.values name)
  pure (reCountValueBoundary result)

theorem withCtx_run {α : Type} (c : String) (m : EvalM α) (st : EvalState) :
    (withCtx c m).runState st =
      (match m.runState st with
       | (.ok a, t) => (.ok a, t)
       | (.error e, t) =>
         (.error (if (Except.error e : Except Error Unit).isIncomplete then e else Error.withContext c e), t)) := by
  simp only [withCtx, bind_run, evalAttempt_run]
  rcases m.runState st with ⟨out, t⟩
  cases out with
  | ok a => rfl
  | error e => cases e <;> rfl

/-- With its route recorded, a plan's execution IS its execution along that route: the route is
    read, not classified again, and changes nothing. -/
theorem execute_recorded (route : NeedPlan.Route) (a : Nat) (shape : NeedPlan.CallShape)
    (s : EvalState) (cell : NeedCell) (r : PlanRoute)
    (hc : s.needs[a]? = some cell) (hr : cell.route = some r) (hi : r ≠ .intrinsic) :
    (NeedPlan.execute route a shape).runState s = (NeedPlan.executeAlong route a shape r).runState s := by
  simp only [NeedPlan.execute, bind_run, withCtx_run, routeOf_recorded route.classify a shape s cell r hc hr]
  all_goals (try (cases r <;> first | rfl | exact absurd rfl hi))

/-- **A prepared plan executes over exactly its cells.** With prepared cells, one plan execution
    along a route is `callOver` those cells: the dispatch receives the recorded supply, never a
    re-formed one (given a disciplined callee phase and normalization, which keep the record). -/
theorem executeAlong_prepared (route : NeedPlan.Route) (a : Nat) (shape : NeedPlan.CallShape) (r : PlanRoute)
    (hcallee : ∀ eff, Disciplined (NeedPlan.calleeAlong route a eff r))
    (hnormal : ∀ g c, Disciplined (route.normalize g c))
    (s : EvalState) (cell : NeedCell)
    (cells : List NeedSupply.Sourced)
    (hc : s.needs[a]? = some cell) (hp : cell.plan = .prepared (.ok cells)) :
    (NeedPlan.executeAlong route a shape r).runState s = (callOver route a shape r cells).runState s := by
  simp only [NeedPlan.executeAlong, callOver, bind_run, withCtx_run, dispatchName_run, dispatchOrigin_run]
  have k1 := hcallee (NeedPlan.effective shape r) s
  generalize hr1 : (NeedPlan.calleeAlong route a (NeedPlan.effective shape r) r).runState s = r1 at k1
  rcases r1 with ⟨o1, t1⟩
  cases o1 with
  | error e => rfl
  | ok callee =>
    dsimp only
    have k2 := hnormal callee (NeedPlan.effective shape r).caller t1
    generalize hr2 : (route.normalize callee (NeedPlan.effective shape r).caller).runState t1 = r2 at k2
    rcases r2 with ⟨o2, t2⟩
    cases o2 with
    | error e => rfl
    | ok normal =>
      dsimp only
      obtain ⟨c2, hc2, kc⟩ := (k1.trans k2) a cell hc
      rw [prepare_prepared route.spread a _ t2 c2 (.ok cells) hc2 (kc.prepared _ hp)]

/-- **A prepared plan with a recorded route executes over exactly its cells** (META-S3-4: every
    callable route — call, member, `.Algorithm`, extension). -/
theorem execute_prepared (route : NeedPlan.Route)
    (htarget : ∀ f c, Disciplined (route.target f c))
    (hnormal : ∀ g c, Disciplined (route.normalize g c))
    (hclassify : ∀ shape, Disciplined (route.classify shape))
    (hproject : ∀ c, Disciplined (route.project c))
    (a : Nat) (shape : NeedPlan.CallShape) (s : EvalState) (cell : NeedCell) (r : PlanRoute)
    (cells : List NeedSupply.Sourced)
    (hc : s.needs[a]? = some cell) (hr : cell.route = some r) (hi : r ≠ .intrinsic)
    (hp : cell.plan = .prepared (.ok cells)) :
    (NeedPlan.execute route a shape).runState s = (callOver route a shape r cells).runState s := by
  rw [execute_recorded route a shape s cell r hc hr hi]
  exact executeAlong_prepared route a shape r
    (fun eff => disciplined_calleeAlong route htarget hclassify hproject a eff r) hnormal s cell cells hc hp

/-- **The original VALUE of a plan whose route is recorded and callable is its execution**
    (META-S3-4): the completion shell's suspended computation reads the route and runs
    `executeAlong`, exactly as `execute` does. -/
theorem suspendedValue_recorded (ev : Expr → EvalCtx → ValEnv → EvalM CountedResult)
    (route : NeedPlan.Route) (demand : Nat → EvalM CountedResult) (a : Nat)
    (e : Expr) (c : EvalCtx) (v : ValEnv) (shape : NeedPlan.CallShape)
    (hshape : NeedPlan.callShape? e c v = some shape)
    (s : EvalState) (cell : NeedCell) (r : PlanRoute)
    (hc : s.needs[a]? = some cell) (hr : cell.route = some r) (hi : r ≠ .intrinsic) :
    (NeedDemand.suspendedValue ev route demand a (.expression e c v)).runState s =
      (NeedPlan.execute route a shape).runState s := by
  rw [execute_recorded route a shape s cell r hc hr hi]
  simp only [NeedDemand.suspendedValue, hshape, bind_run, withCtx_run,
    routeOf_recorded route.classify a shape s cell r hc hr]
  all_goals (try (cases r <;> first | rfl | exact absurd rfl hi))

/-- **Invocation and VALUE share the prepared supply.** With the plan's route recorded and its
    cells prepared, an explicit invocation is `callOver` those cells, and VALUE of the
    still-suspended original cell is the completion shell around `callOver` the SAME cells. -/
theorem invoke_and_value_share_cells (ev : Expr → EvalCtx → ValEnv → EvalM CountedResult)
    (route : NeedPlan.Route) (demand : Nat → EvalM CountedResult)
    (htarget : ∀ f c, Disciplined (route.target f c))
    (hnormal : ∀ g c, Disciplined (route.normalize g c))
    (hclassify : ∀ shape, Disciplined (route.classify shape))
    (hproject : ∀ c, Disciplined (route.project c))
    (a : Nat) (s : EvalState) (cell : NeedCell) (shape : NeedPlan.CallShape) (r : PlanRoute)
    (cells : List NeedSupply.Sourced)
    (hc : s.needs[a]? = some cell) (hshape : NeedPlan.ofSuspension? cell.suspension = some shape)
    (hr : cell.route = some r) (hi : r ≠ .intrinsic)
    (hp : cell.plan = .prepared (.ok cells)) (hs : cell.state = .suspended)
    (hcomplete : ((callOver route a shape r cells).runState (withState a .evaluating s)).1.isIncomplete = false) :
    (NeedPlan.invoke route ⟨a⟩).runState s = (callOver route a shape r cells).runState s ∧
    (NeedDemand.step ev route demand a).runState s =
      (let res := (callOver route a shape r cells).runState (withState a .evaluating s)
       (res.1, withState a (.completed res.1) res.2)) := by
  have hsa : NeedPlan.shapeAt? s.needs a = some shape := by simp [NeedPlan.shapeAt?, hc, hshape]
  refine ⟨?_, ?_⟩
  · rw [invoke_run route a s shape hsa]
    exact execute_prepared route htarget hnormal hclassify hproject a shape s cell r cells hc hr hi hp
  · have he : (withState a .evaluating s).needs[a]? = some { cell with state := .evaluating } := by
      simp [withState, modify_get, hc]
    obtain ⟨e, c, v, hsus, hcs⟩ : ∃ e c v, cell.suspension = .expression e c v ∧
        NeedPlan.callShape? e c v = some shape := by
      cases hsus : cell.suspension with
      | expression e c v =>
        rw [hsus] at hshape
        exact ⟨e, c, v, rfl, hshape⟩
      | ready _ => rw [hsus] at hshape; cases hshape
      | collector _ => rw [hsus] at hshape; cases hshape
    have hr' := execute_prepared route htarget hnormal hclassify hproject a shape (withState a .evaluating s)
      { cell with state := .evaluating } r cells he hr hi hp
    have hv := suspendedValue_recorded ev route demand a e c v shape hcs (withState a .evaluating s)
      { cell with state := .evaluating } r he hr hi
    rw [hr'] at hv
    rw [← hsus] at hv
    generalize hres : (callOver route a shape r cells).runState (withState a .evaluating s) = res at hv hcomplete
    rcases res with ⟨o, t⟩
    exact KatLang.NeedControl.Memo.suspended_retains_state ev route demand a s t cell o hc hs hv hcomplete

/-! ## Observation order -/

/-- **META → VALUE and VALUE → META agree**, observing BOTH outcomes even when VALUE fails (no
    monadic short-circuit): the same reference, the same VALUE outcome and the same final state.
    The only assumption is the structural discipline of the installed callbacks. -/
theorem meta_value_orders (ev : Expr → EvalCtx → ValEnv → EvalM CountedResult)
    (route : NeedPlan.Route) (demand : Nat → EvalM CountedResult)
    (hev : ∀ e c v, Disciplined (ev e c v))
    (hspread : ∀ e c v, Disciplined (route.spread e c v))
    (htarget : ∀ f c, Disciplined (route.target f c))
    (hnormal : ∀ g c, Disciplined (route.normalize g c))
    (hdispatch : ∀ o g cells c v n, Disciplined (route.dispatch o g cells c v n))
    (hclassify : ∀ shape, Disciplined (route.classify shape))
    (hproject : ∀ c, Disciplined (route.project c))
    (hdemand : ∀ b, Disciplined (demand b))
    (a : Nat) (s : EvalState) (shape : NeedPlan.CallShape)
    (hshape : NeedPlan.shapeAt? s.needs a = some shape) :
    (let metaFirst := (NeedPlan.reify a).runState s
     let value := (NeedDemand.step ev route demand a).runState metaFirst.2
     (metaFirst.1, value.1, value.2)) =
    (let value := (NeedDemand.step ev route demand a).runState s
     let metaAfter := (NeedPlan.reify a).runState value.2
     (metaAfter.1, value.1, metaAfter.2)) := by
  have hstep := disciplined_step ev route demand hev hspread htarget hnormal hdispatch hclassify hproject hdemand a
  simp only [reify_identity a s shape hshape,
    meta_after _ hstep a s shape hshape]


/-! ## Production connection: the authoritative VALUE route IS the plan route -/

/-- The public VALUE entry point installs the production plan route in the ONE shell. -/
theorem production_demand (a : Nat) :
    demandNeed a = NeedDemand.step (evalSuppliedAt a) productionPlanRoute demandNeedRecursive a := rfl

theorem production_route :
    productionPlanRoute = ⟨resolveCalleeAlg, NeedPlan.normalizeCallee, evalSuppliedCallCounted, evalSupplySpread,
      classifyPlanRouteWith resolveDotReceiver? algorithmIntrinsicRoute, projectNeedCallable⟩ := rfl

theorem production_reify (a : Nat) : reifyNeedCall a = NeedPlan.reify a := rfl

theorem production_invoke (r : NeedPlan.CallReference) :
    invokeNeedCall r = NeedPlan.invoke productionPlanRoute r := rfl

/-- **A supported supplied invocation's suspended computation routes it** (META-S3-4): the plan's
    route under the written form's own context, then — for every callable route — the plan's
    execution along it, and — for a non-callable intrinsic route — the ordinary evaluation (D-1A). -/
theorem suspended_call_routes (ev : Expr → EvalCtx → ValEnv → EvalM CountedResult)
    (route : NeedPlan.Route) (demand : Nat → EvalM CountedResult) (a : Nat)
    (e : Expr) (c : EvalCtx) (v : ValEnv) (shape : NeedPlan.CallShape)
    (h : NeedPlan.callShape? e c v = some shape) :
    NeedDemand.suspendedValue ev route demand a (.expression e c v) = (do
      match ← withCtx shape.ctxMsg (NeedPlan.routeOf route.classify a shape) with
      | .intrinsic => reCountValueBoundary <$> ev e c v
      | r => NeedPlan.executeAlong route a shape r) := by
  simp only [NeedDemand.suspendedValue, h]
  rfl

/-- **A supported supplied invocation's suspended computation IS its plan execution** whenever its
    route is not the non-callable intrinsic: both read (or establish) the same route first and then
    run `executeAlong`. -/
theorem suspended_call_is_plan (ev : Expr → EvalCtx → ValEnv → EvalM CountedResult)
    (route : NeedPlan.Route) (demand : Nat → EvalM CountedResult) (a : Nat)
    (e : Expr) (c : EvalCtx) (v : ValEnv) (shape : NeedPlan.CallShape)
    (h : NeedPlan.callShape? e c v = some shape) (s : EvalState)
    (hcallable : ((withCtx shape.ctxMsg (NeedPlan.routeOf route.classify a shape)).runState s).1 ≠ .ok .intrinsic) :
    (NeedDemand.suspendedValue ev route demand a (.expression e c v)).runState s =
      (NeedPlan.execute route a shape).runState s := by
  rw [suspended_call_routes ev route demand a e c v shape h]
  simp only [NeedPlan.execute, bind_run]
  revert hcallable
  rcases (withCtx shape.ctxMsg (NeedPlan.routeOf route.classify a shape)).runState s with ⟨_ | r, t⟩
  · intro _; rfl
  · intro hcallable
    cases r with
    | intrinsic => exact absurd rfl hcallable
    | _ => rfl

/-- **A captured non-callable intrinsic keeps its ordinary VALUE** (D-1A): with that route, the
    suspended computation is the ordinary evaluation of the written expression (after the route). -/
theorem suspended_intrinsic_is_ordinary (ev : Expr → EvalCtx → ValEnv → EvalM CountedResult)
    (route : NeedPlan.Route) (demand : Nat → EvalM CountedResult) (a : Nat)
    (e : Expr) (c : EvalCtx) (v : ValEnv) (shape : NeedPlan.CallShape)
    (h : NeedPlan.callShape? e c v = some shape) (s : EvalState) (cell : NeedCell)
    (hc : s.needs[a]? = some cell) (hr : cell.route = some .intrinsic) :
    (NeedDemand.suspendedValue ev route demand a (.expression e c v)).runState s =
      (reCountValueBoundary <$> ev e c v).runState s := by
  rw [suspended_call_routes ev route demand a e c v shape h]
  simp only [bind_run, withCtx_run, routeOf_recorded route.classify a shape s cell .intrinsic hc hr]

/-- **Conservative extension of the shell.** Every other expression cell keeps the pre-M1.5
    computation (`reCountValueBoundary <$> ev e c v`); Ready and collector cells are untouched. -/
theorem suspended_other_is_ordinary (ev : Expr → EvalCtx → ValEnv → EvalM CountedResult)
    (route : NeedPlan.Route) (demand : Nat → EvalM CountedResult) (a : Nat)
    (e : Expr) (c : EvalCtx) (v : ValEnv) (h : NeedPlan.callShape? e c v = none) :
    NeedDemand.suspendedValue ev route demand a (.expression e c v) = reCountValueBoundary <$> ev e c v := by
  simp [NeedDemand.suspendedValue, h]

/-- **THE INVOCATION DOMAIN** (META-S3-4, CR-2, D-2A): a written expression is a plan exactly when it
    is a written call whose callee is a name, a parameter or an argumentless dot path, or an
    argument-bearing dot edge (an explicitly empty list included). Every other form — values,
    names, argumentless dot edges, computed callees, collectors' sources — is no plan. The
    decision reads only the expression's outer syntax. -/
theorem callShape_supported (source : Expr) (c : EvalCtx) (v : ValEnv) :
    (NeedPlan.callShape? source c v).isSome = (match source with
      | .call (.resolve _) _ | .call (.param _) _ | .call (.dotMember _ _ _ none) _ => true
      | .dotMember _ _ _ (some _) => true
      | _ => false) := by
  cases source with
  | call f args =>
    cases f with
    | dotMember r n fb argsOpt => cases argsOpt <;> rfl
    | _ => rfl
  | dotMember r n fb argsOpt => cases argsOpt <;> rfl
  | _ => rfl

/-- An argumentless dot edge (`5.Inc`, `Box.G`) is never a plan (D-2A, DOT-09). -/
theorem argumentless_edge_not_plan (r : Expr) (n : Ident) (fb : Expr) (c : EvalCtx) (v : ValEnv) :
    NeedPlan.callShape? (.dotMember r n fb none) c v = none := rfl

/-- An argument-bearing dot edge is a dot-form plan whose callee is its argumentless edge and whose
    written bundle is its own argument list. -/
theorem dot_edge_shape (r : Expr) (n : Ident) (fb : Expr) (args : OutputBundle) (c : EvalCtx) (v : ValEnv) :
    NeedPlan.callShape? (.dotMember r n fb (some args)) c v =
      some ⟨.dotMember r n fb none, args, c, v, .dot r n fb⟩ := rfl

/-- **The production VALUE of a suspended supported call executes its plan**: `demandNeed` is
    the completion shell around `NeedPlan.execute productionPlanRoute`, whose supply
    is the cell's own `NeedPlan.prepare` — here for a plan whose callable route is recorded (META-S3-4;
    an unrecorded route is established by the same first step, `suspended_call_is_plan`). -/
theorem production_value_executes_plan (a : Nat) (s : EvalState) (cell : NeedCell)
    (e : Expr) (c : EvalCtx) (v : ValEnv) (shape : NeedPlan.CallShape) (r : PlanRoute)
    (hc : s.needs[a]? = some cell) (hsus : cell.suspension = .expression e c v)
    (hshape : NeedPlan.callShape? e c v = some shape) (hs : cell.state = .suspended)
    (hr : cell.route = some r) (hi : r ≠ .intrinsic)
    (hcomplete : ((NeedPlan.execute productionPlanRoute a shape).runState
      (withState a .evaluating s)).1.isIncomplete = false) :
    (demandNeed a).runState s =
      (let res := (NeedPlan.execute productionPlanRoute a shape).runState (withState a .evaluating s)
       (res.1, withState a (.completed res.1) res.2)) := by
  rw [production_demand]
  have he : (withState a .evaluating s).needs[a]? = some { cell with state := .evaluating } := by
    simp [withState, modify_get, hc]
  have hv := suspendedValue_recorded (evalSuppliedAt a) productionPlanRoute demandNeedRecursive a e c v shape
    hshape (withState a .evaluating s) { cell with state := .evaluating } r he hr hi
  rw [← hsus] at hv
  generalize hres : (NeedPlan.execute productionPlanRoute a shape).runState
    (withState a .evaluating s) = res at hcomplete
  rcases res with ⟨o, t⟩
  rw [hres] at hv
  exact KatLang.NeedControl.Memo.suspended_retains_state _ _ _ a s t cell o hc hs hv hcomplete

/-- (Historical name of the M1.5 boundary; R7 PROVES it: `productionDiscipline_holds` in
    `KatLangArityLaws/EvaluatorDiscipline.lean`.) The production callbacks are disciplined (they keep every existing cell's suspension, completed VALUE and
    prepared plan). By source inspection the evaluator writes the heap only through
    `allocateNeed`, `projectNeedCallable`'s CALLABLE memo, `NeedPlan.prepare`, `NeedDemand.step`
    and the memo records `NeedPlan.setCallee` / `NeedLink.setReceiver` / `NeedPlan.setRoute`
    (META-S3-1/S3-4: they write only the `callee` / `receiver` / `route` field, kept by `CellKept`),
    `prepare` and `step` proved disciplined here; Lean cannot unfold the `partial` definitions, so
    this is an explicit hypothesis, exercised by `InvocationPlanGuards`. META-S3-4 adds the route
    classifier and the CALLABLE projection the plan route installs. -/
def ProductionDiscipline : Prop :=
  (∀ a e c v, Disciplined (evalSuppliedAt a e c v)) ∧
  (∀ f c, Disciplined (resolveCalleeAlg f c)) ∧
  (∀ g c, Disciplined (NeedPlan.normalizeCallee g c)) ∧
  (∀ o g cells c v n, Disciplined (evalSuppliedCallCounted o g cells c v n)) ∧
  (∀ b, Disciplined (demandNeedRecursive b)) ∧
  (∀ e c v, Disciplined (evalSupplySpread e c v)) ∧
  (∀ shape, Disciplined (classifyPlanRouteWith resolveDotReceiver? algorithmIntrinsicRoute shape)) ∧
  (∀ b, Disciplined (projectNeedCallable b))

theorem production_value_disciplined (hp : ProductionDiscipline) (a : Nat) :
    Disciplined (demandNeed a) :=
  disciplined_step _ productionPlanRoute _ (hp.1 a) hp.2.2.2.2.2.1 hp.2.1 hp.2.2.1 hp.2.2.2.1
    hp.2.2.2.2.2.2.1 hp.2.2.2.2.2.2.2 hp.2.2.2.2.1 a

theorem production_invoke_disciplined (hp : ProductionDiscipline) (r : NeedPlan.CallReference) :
    Disciplined (invokeNeedCall r) :=
  disciplined_invoke productionPlanRoute hp.2.2.2.2.2.1 hp.2.1 hp.2.2.1 hp.2.2.2.1
    hp.2.2.2.2.2.2.1 hp.2.2.2.2.2.2.2 r

/-- Production: META after the production VALUE (success or failure) reifies the same plan. -/
theorem production_value_then_meta (hp : ProductionDiscipline) (a : Nat) (s : EvalState)
    (shape : NeedPlan.CallShape) (hs : NeedPlan.shapeAt? s.needs a = some shape) :
    (reifyNeedCall a).runState ((demandNeed a).runState s).2 = (.ok ⟨a⟩, ((demandNeed a).runState s).2) :=
  meta_after _ (production_value_disciplined hp a) a s shape hs

/-- Production: any number of explicit invocations never change a completed original VALUE. -/
theorem production_invocations_keep_value (hp : ProductionDiscipline) (a : Nat) (s : EvalState)
    (cell : NeedCell) (outcome : Except Error CountedResult) (hc : s.needs[a]? = some cell)
    (hs : cell.state = .completed outcome) (refs : List NeedPlan.CallReference) :
    (demandNeed a).runState ((refs.mapM invokeNeedCall).runState s).2 =
      (outcome, ((refs.mapM invokeNeedCall).runState s).2) :=
  completed_survives _ (disciplined_mapM _ (production_invoke_disciplined hp) refs) _ _ _ a s cell
    outcome hc hs

/-- Production: META → VALUE and VALUE → META agree (both outcomes, the same final state). -/
theorem production_meta_value_orders (hp : ProductionDiscipline) (a : Nat) (s : EvalState)
    (shape : NeedPlan.CallShape) (hshape : NeedPlan.shapeAt? s.needs a = some shape) :
    (let metaFirst := (reifyNeedCall a).runState s
     let value := (demandNeed a).runState metaFirst.2
     (metaFirst.1, value.1, value.2)) =
    (let value := (demandNeed a).runState s
     let metaAfter := (reifyNeedCall a).runState value.2
     (metaAfter.1, value.1, metaAfter.2)) :=
  meta_value_orders _ productionPlanRoute _ (hp.1 a) hp.2.2.2.2.2.1 hp.2.1 hp.2.2.1 hp.2.2.2.1
    hp.2.2.2.2.2.2.1 hp.2.2.2.2.2.2.2 hp.2.2.2.2.1 a s shape hshape

/-! ## Transparent forwarding (actual `supplyNeed`) -/

/-- One forwarding hop: a parameter bound to `a`, supplied onward, transports `a` itself; no cell
    is allocated, no state changes. -/
theorem forward_hop (name : Ident) (ctx : EvalCtx) (env : ValEnv) (s : EvalState)
    (activation : Option ParameterActivation) (a : Nat)
    (hc : (capturedParameterActivation? name ctx).runState s = (.ok activation, s))
    (ha : lookupAssoc name (activation.map ParameterActivation.needs |>.getD ctx.needEnv) = some a) :
    (supplyNeed (.param name) ctx env).runState s = (.ok a, s) :=
  KatLang.NeedControl.Allocation.supply_param_transports name ctx env s activation a hc ha

/-- The binder half of a hop: a plain parameter is bound to the supplied cell itself. -/
theorem binder_transports {m : Type → Type} [Monad m] [MonadExceptOf Error m]
    (allocate : NeedSuspension → m Nat) (a : Nat) :
    NeedBinder.sourceAddress allocate (.cell a) = pure a := rfl

theorem prepended_binding_reads (name : Ident) (a : Nat) (rest : NeedEnv) :
    lookupAssoc name ([(name, a)] ++ rest) = some a := by
  simp [lookupAssoc]

/-- A chain of forwarding hops: each hop supplies its own parameter onward. -/
def forwardChain : List (Ident × EvalCtx × ValEnv) → Nat → EvalM Nat
  | [], a => pure a
  | (name, ctx, env) :: rest, _ => do
    let next ← supplyNeed (.param name) ctx env
    forwardChain rest next

/-- **Forwarding identity across any number of hops.** -/
theorem forward_chain_identity (hops : List (Ident × EvalCtx × ValEnv)) (a : Nat) (s : EvalState)
    (hbound : ∀ hop ∈ hops, ∃ activation,
      (capturedParameterActivation? hop.1 hop.2.1).runState s = (.ok activation, s) ∧
      lookupAssoc hop.1 (activation.map ParameterActivation.needs |>.getD hop.2.1.needEnv) = some a) :
    (forwardChain hops a).runState s = (.ok a, s) := by
  induction hops with
  | nil => rfl
  | cons hop rest ih =>
    obtain ⟨name, ctx, env⟩ := hop
    obtain ⟨activation, hc, ha⟩ := hbound (name, ctx, env) (List.mem_cons_self ..)
    simp only [forwardChain, bind_run, forward_hop name ctx env s activation a hc ha]
    exact ih (fun hop hmem => hbound hop (List.mem_cons_of_mem _ hmem))

/-- After forwarding, META, invocation and VALUE at the far end are those of the ORIGINAL plan:
    the plan's callee and caller context come from the original cell, never from a forwarding
    scope (no re-resolution there). -/
theorem forwarded_is_original (hops : List (Ident × EvalCtx × ValEnv)) (a : Nat) (s : EvalState)
    (hbound : ∀ hop ∈ hops, ∃ activation,
      (capturedParameterActivation? hop.1 hop.2.1).runState s = (.ok activation, s) ∧
      lookupAssoc hop.1 (activation.map ParameterActivation.needs |>.getD hop.2.1.needEnv) = some a)
    (ev : Expr → EvalCtx → ValEnv → EvalM CountedResult) (route : NeedPlan.Route)
    (demand : Nat → EvalM CountedResult) :
    (forwardChain hops a >>= NeedPlan.reify).runState s = (NeedPlan.reify a).runState s ∧
    (forwardChain hops a >>= fun b => NeedPlan.invoke route ⟨b⟩).runState s =
      (NeedPlan.invoke route ⟨a⟩).runState s ∧
    (forwardChain hops a >>= NeedDemand.step ev route demand).runState s =
      (NeedDemand.step ev route demand a).runState s := by
  simp only [bind_run, forward_chain_identity hops a s hbound, and_self]

/-! ## Independence and deliberate sharing -/

theorem distinct_cells_distinct_plans (a b : Nat) (h : a ≠ b) :
    (⟨a⟩ : NeedPlan.CallReference) ≠ ⟨b⟩ := by
  intro heq
  exact h (NeedPlan.CallReference.mk.inj heq)

theorem withPlan_size (a : Nat) (p : NeedPlanSupply) (s : EvalState) :
    (withPlan a p s).needs.size = s.needs.size := by
  simp [withPlan]

/-- A fresh plan whose one argument is an ordinary written computation (not a parameter, not a
    spread) prepares ONE newly allocated cell at the heap end. -/
theorem prepare_allocates_fresh_cell (ev : NeedSupply.SpreadEval)
    (a : Nat) (shape : NeedPlan.CallShape) (s : EvalState) (cell : NeedCell) (e : Expr)
    (h : s.needs[a]? = some cell) (hp : cell.plan = .unprepared)
    (hargs : shape.args = [e]) (hn : ∀ name, e ≠ .param name)
    (hs : ∀ operand, e ≠ .sequenceSpread operand) :
    ((NeedPlan.prepare ev a shape).runState s).1 = .ok [(s.needs.size, some e)] ∧
    ((NeedPlan.prepare ev a shape).runState s).2.needs.size = s.needs.size + 1 := by
  have hsup := KatLang.NeedControl.Allocation.supply_nonparameter e shape.caller shape.values
    (withPlan a .preparing s) hn
  have hf := KatLang.NeedControl.Formation.ordinary_singleton ev shape.caller shape.values e
    (withPlan a .preparing s) _ _ hs hsup
  rw [prepare_unprepared ev a shape s cell h hp (by rw [hargs, hf]; rfl)]
  rw [hargs, hf]
  simp [withPlan_size]

/-- **Distinct dynamic occurrences.** Two plans prepared one after the other, each over the SAME
    ordinary written argument, receive DIFFERENT, newly allocated argument cells. -/
theorem two_plans_distinct_argument_cells (ev : NeedSupply.SpreadEval)
    (a b : Nat) (sa sb : NeedPlan.CallShape) (s : EvalState) (ca cb : NeedCell) (e : Expr)
    (ha : s.needs[a]? = some ca) (hpa : ca.plan = .unprepared)
    (hb : ((NeedPlan.prepare ev a sa).runState s).2.needs[b]? = some cb) (hpb : cb.plan = .unprepared)
    (hea : sa.args = [e]) (heb : sb.args = [e]) (hn : ∀ name, e ≠ .param name)
    (hs : ∀ operand, e ≠ .sequenceSpread operand) :
    ∃ x y, ((NeedPlan.prepare ev a sa).runState s).1 = .ok [(x, some e)] ∧
      ((NeedPlan.prepare ev b sb).runState ((NeedPlan.prepare ev a sa).runState s).2).1 = .ok [(y, some e)] ∧
      x < y := by
  obtain ⟨h1, h2⟩ := prepare_allocates_fresh_cell ev a sa s ca e ha hpa hea hn hs
  obtain ⟨h3, _⟩ := prepare_allocates_fresh_cell ev b sb _ cb e hb hpb heb hn hs
  exact ⟨_, _, h1, h3, by omega⟩


/-! ## A fresh plan is the ordinary call (simulation up to the plan record) -/

theorem withPlan_withPlan (a : Nat) (p q : NeedPlanSupply) (s : EvalState) :
    withPlan a p (withPlan a q s) = withPlan a p s := by
  simp only [withPlan]
  congr 1
  apply Array.ext_getElem?
  intro i
  simp only [modify_get]
  by_cases h : a = i <;> simp [h] <;> rfl

theorem withPlan_self (a : Nat) (p : NeedPlanSupply) (s : EvalState) (cell : NeedCell)
    (h : s.needs[a]? = some cell) (hp : cell.plan = p) : withPlan a p s = s := by
  cases s
  simp only [withPlan]
  congr 1
  apply Array.ext_getElem?
  intro i
  simp only [modify_get]
  by_cases hi : a = i
  · subst hi
    simp only [h, if_true, Option.map_some]
    rw [← hp]
  · simp [hi]

/-- `m` neither reads nor writes the plan record of a VALID cell `a`: started from a state that
    differs only in that record, it has the same outcome and the same difference.
    This quantifies over all heaps, including a suspended `a`; production dispatch does not
    satisfy it globally. It is only a sufficient contract for the conditional simulation below. -/
def Oblivious {α : Type} (a : Nat) (m : EvalM α) : Prop :=
  ∀ s p, a < s.needs.size → m.runState (withPlan a p s) = ((m.runState s).1, withPlan a p (m.runState s).2)

/-- The ordinary call composition of a plan's written invocation along route `r` — the phase order
    of the production `evalCallCountedExpr` → `evalResolvedCallCounted` (the latter forms the supply
    with `NeedSupply.form evalSupplySpread` and dispatches through `evalSuppliedCallCounted`, the
    same dispatch `productionPlanRoute` installs) over the route's callee and effective bundle
    (META-S3-4: an extension is the call `F(t, args)`, `effective`). The correspondence with the
    `partial` production definitions is a source fact, checked executably by
    `InvocationPlanGuards.agrees` and `InvocationRouteGuards`. -/
def ordinaryCall (route : NeedPlan.Route) (a : Nat)
    (shape : NeedPlan.CallShape) (r : PlanRoute) : EvalM CountedResult := do
  let eff := NeedPlan.effective shape r
  let callee ← withCtx shape.ctxMsg (NeedPlan.calleeAlong route a eff r)
  let name ← NeedPlan.dispatchName a eff r
  let origin ← NeedPlan.dispatchOrigin a eff r
  let result ← withCtx shape.ctxMsg (do
    let normal ← route.normalize callee eff.caller
    let cells ← NeedSupply.form route.spread eff.caller eff.values eff.args
    route.dispatch origin normal cells eff.caller eff.values name)
  pure (reCountValueBoundary result)

theorem valid_of_get {h : Array NeedCell} {a : Nat} {c : NeedCell} (hc : h[a]? = some c) :
    a < h.size := by
  rcases Nat.lt_or_ge a h.size with hl | hl
  · exact hl
  · rw [Array.getElem?_eq_none hl] at hc; cases hc

/-- An oblivious step from a state whose record at `a` is `p` ends in a state whose record is `p`. -/
theorem oblivious_keeps_record {α : Type} {m : EvalM α} {a : Nat} (hm : Oblivious a m)
    (p : NeedPlanSupply) (s : EvalState) (cell : NeedCell) (h : s.needs[a]? = some cell)
    (hp : cell.plan = p) : (m.runState s).2 = withPlan a p (m.runState s).2 := by
  have e := hm s p (valid_of_get h)
  rw [withPlan_self a p s cell h hp] at e
  exact congrArg Prod.snd e

/-- **A fresh plan is the ordinary call.** On a plan whose route `r` is recorded (callable) and whose
    supply is not yet prepared, one plan execution has EXACTLY the outcome of the ordinary call
    composition along that route, and its final state differs from the ordinary one at most in the
    plan record of the plan's own cell. Assumptions: the callbacks are disciplined (they keep the
    cell present) and oblivious of that cell's plan record — both structural contracts of the
    callbacks, not of the result. Dispatch needs this contract only at the ONE name read after the
    callee phase, not at every string; on non-`.Algorithm` routes this is the original written-name
    contract. -/
theorem fresh_plan_is_ordinary_call
    (route : NeedPlan.Route) (a : Nat) (shape : NeedPlan.CallShape) (r : PlanRoute)
    (s : EvalState) (cell : NeedCell)
    (hc : s.needs[a]? = some cell) (hp : cell.plan = .unprepared)
    (hr : cell.route = some r) (hi : r ≠ .intrinsic)
    (hev : ∀ e c v, Disciplined (route.spread e c v))
    (dcallee : Disciplined (NeedPlan.calleeAlong route a (NeedPlan.effective shape r) r))
    (dnormal : ∀ g c, Disciplined (route.normalize g c))
    (ocallee : Oblivious a (NeedPlan.calleeAlong route a (NeedPlan.effective shape r) r))
    (onormal : ∀ g c, Oblivious a (route.normalize g c))
    (oform : Oblivious a (NeedSupply.form route.spread (NeedPlan.effective shape r).caller
      (NeedPlan.effective shape r).values (NeedPlan.effective shape r).args))
    (odispatch : ∀ g cells, Oblivious a
      (route.dispatch
        (NeedPlan.dispatchOriginIn
          ((NeedPlan.calleeAlong route a (NeedPlan.effective shape r) r).runState s).2.needs
          a (NeedPlan.effective shape r) r)
        g cells (NeedPlan.effective shape r).caller (NeedPlan.effective shape r).values
        (NeedPlan.dispatchNameIn
          ((NeedPlan.calleeAlong route a (NeedPlan.effective shape r) r).runState s).2.needs
          a (NeedPlan.effective shape r) r))) :
    ((NeedPlan.execute route a shape).runState s).1 = ((ordinaryCall route a shape r).runState s).1 ∧
    (((NeedPlan.execute route a shape).runState s).2 = ((ordinaryCall route a shape r).runState s).2 ∨
      (∃ o, ((NeedPlan.execute route a shape).runState s).2 =
        withPlan a (.prepared o) ((ordinaryCall route a shape r).runState s).2) ∨
      (((NeedPlan.execute route a shape).runState s).1 = .error .fuelExhausted ∧
        ((NeedPlan.execute route a shape).runState s).2 =
          withPlan a .preparing ((ordinaryCall route a shape r).runState s).2)) := by
  rw [execute_recorded route a shape s cell r hc hr hi]
  generalize heff : NeedPlan.effective shape r = eff at dcallee ocallee oform odispatch
  simp only [NeedPlan.executeAlong, ordinaryCall, bind_run, withCtx_run, heff, dispatchName_run, dispatchOrigin_run]
  have k1 := dcallee s
  have r1keep := oblivious_keeps_record ocallee .unprepared s cell hc hp
  generalize hr1 : (NeedPlan.calleeAlong route a eff r).runState s = r1 at k1 r1keep odispatch
  rcases r1 with ⟨o1, t1⟩
  cases o1 with
  | error e => exact ⟨rfl, Or.inl rfl⟩
  | ok callee =>
    dsimp only at r1keep odispatch ⊢
    obtain ⟨c1, hc1, kc1⟩ := k1 a cell hc
    have hp1 : c1.plan = .unprepared := by
      have := congrArg (fun st : EvalState => (st.needs[a]?).map NeedCell.plan) r1keep
      simp [withPlan, modify_get, hc1] at this
      exact this
    have k2 := dnormal callee eff.caller t1
    have r2keep := oblivious_keeps_record (onormal callee eff.caller) .unprepared t1 c1 hc1 hp1
    generalize hr2 : (route.normalize callee eff.caller).runState t1 = r2 at k2 r2keep
    rcases r2 with ⟨o2, t2⟩
    cases o2 with
    | error e => exact ⟨rfl, Or.inl rfl⟩
    | ok normal =>
      dsimp only at r2keep ⊢
      obtain ⟨c2, hc2, kc2⟩ := k2 a c1 hc1
      have hp2 : c2.plan = .unprepared := by
        have := congrArg (fun st : EvalState => (st.needs[a]?).map NeedCell.plan) r2keep
        simp [withPlan, modify_get, hc2] at this
        exact this
      cases hinc : ((NeedSupply.form route.spread eff.caller eff.values eff.args).runState
          t2).1.isIncomplete with
      | true =>
        have hinc' : ((NeedSupply.form route.spread eff.caller eff.values eff.args).runState
            (withPlan a .preparing t2)).1.isIncomplete = true := by
          rw [oform t2 .preparing (valid_of_get hc2)]; exact hinc
        rw [prepare_unprepared_incomplete route.spread a eff t2 c2 hc2 hp2 hinc',
          oform t2 .preparing (valid_of_get hc2)]
        generalize hr3 : (NeedSupply.form route.spread eff.caller eff.values eff.args).runState t2 = r3
          at hinc
        rcases r3 with ⟨o3, t3⟩
        dsimp only at hinc ⊢
        rw [Except.isIncomplete_eq_true hinc]
        exact ⟨rfl, Or.inr (Or.inr ⟨rfl, rfl⟩)⟩
      | false =>
      rw [prepare_unprepared route.spread a eff t2 c2 hc2 hp2
        (by rw [oform t2 .preparing (valid_of_get hc2)]; exact hinc)]
      dsimp only
      rw [oform t2 .preparing (valid_of_get hc2)]
      generalize hr3 : (NeedSupply.form route.spread eff.caller eff.values eff.args).runState t2 = r3
        at hinc
      rcases r3 with ⟨o3, t3⟩
      dsimp only at hinc ⊢
      rw [withPlan_withPlan]
      cases o3 with
      | error e => exact ⟨rfl, Or.inr (Or.inl ⟨.error e, rfl⟩)⟩
      | ok cells =>
        dsimp only
        have hv3 : a < t3.needs.size := by
          obtain ⟨c3, hc3, _⟩ := disciplined_form route.spread hev eff.caller eff.values eff.args t2 a c2 hc2
          rw [hr3] at hc3
          exact valid_of_get hc3
        rw [odispatch normal cells t3 (.prepared (.ok cells)) hv3]
        generalize (route.dispatch (NeedPlan.dispatchOriginIn t1.needs a eff r) normal cells eff.caller eff.values
          (NeedPlan.dispatchNameIn t1.needs a eff r)).runState t3 = r4
        rcases r4 with ⟨o4, t4⟩
        cases o4 with
        | error e => exact ⟨rfl, Or.inr (Or.inl ⟨.ok cells, rfl⟩)⟩
        | ok v => exact ⟨rfl, Or.inr (Or.inl ⟨.ok cells, rfl⟩)⟩


theorem captured_withPlan (name : Ident) (ctx : EvalCtx) (a : Nat) (p : NeedPlanSupply)
    (s : EvalState) :
    (capturedParameterActivation? name ctx).runState (withPlan a p s) =
      (((capturedParameterActivation? name ctx).runState s).1, withPlan a p s) := by
  unfold capturedParameterActivation?
  repeat' (first | rfl | split | dsimp only | simp only [bind_run, get_run, pure_run, throw_run])

/-- **Deliberate sharing.** A fresh plan whose argument is a parameter bound to an existing cell
    `c` prepares exactly `c` itself: nothing is allocated, and the only state change is the plan
    record. Two plans transporting the same parameter therefore share that cell, and only it. -/
theorem prepare_transports_parameter (ev : NeedSupply.SpreadEval)
    (a : Nat) (shape : NeedPlan.CallShape) (s : EvalState) (cell : NeedCell) (name : Ident)
    (c : Nat) (activation : Option ParameterActivation)
    (h : s.needs[a]? = some cell) (hp : cell.plan = .unprepared)
    (hargs : shape.args = [.param name])
    (hc : (capturedParameterActivation? name shape.caller).runState s = (.ok activation, s))
    (hl : lookupAssoc name (activation.map ParameterActivation.needs |>.getD shape.caller.needEnv) = some c) :
    (NeedPlan.prepare ev a shape).runState s =
      (.ok [(c, some (.param name))], withPlan a (.prepared (.ok [(c, some (.param name))])) s) := by
  have hc' : (capturedParameterActivation? name shape.caller).runState (withPlan a .preparing s) =
      (.ok activation, withPlan a .preparing s) := by
    rw [captured_withPlan, hc]
  have hsup := KatLang.NeedControl.Allocation.supply_param_transports name shape.caller shape.values
    (withPlan a .preparing s) activation c hc' hl
  have hf := KatLang.NeedControl.Formation.ordinary_singleton ev shape.caller shape.values (.param name)
    (withPlan a .preparing s) _ _ (fun _ h => by cases h) hsup
  rw [prepare_unprepared ev a shape s cell h hp (by rw [hargs, hf]; rfl)]
  rw [hargs, hf]
  simp only [withPlan_withPlan]

/-- Non-vacuity of `fresh_plan_is_ordinary_call`'s callback contracts: heap-free callbacks (and
    an argument-free plan) satisfy all of them. This witnesses abstract satisfiability only,
    not applicability to the partial production callbacks. -/
theorem oblivious_pure {α : Type} (a : Nat) (x : α) : Oblivious a (pure x : EvalM α) :=
  fun _ _ _ => rfl

theorem fresh_plan_contracts_satisfiable (a : Nat) (callee : Expr) (caller : EvalCtx) (values : ValEnv)
    (alg : Algorithm) (out : CountedResult) :
    let route : NeedPlan.Route :=
      ⟨fun _ _ => pure alg, fun g _ => pure g, fun _ _ _ _ _ _ => pure out, fun _ _ _ => pure (.items []),
       fun _ => pure .call, fun _ => pure none⟩
    let shape : NeedPlan.CallShape := ⟨callee, [], caller, values, .call⟩
    let eff := NeedPlan.effective shape .call
    (∀ e c v, Disciplined (route.spread e c v)) ∧
    Disciplined (NeedPlan.calleeAlong route a eff .call) ∧ (∀ g c, Disciplined (route.normalize g c)) ∧
    Oblivious a (NeedPlan.calleeAlong route a eff .call) ∧ (∀ g c, Oblivious a (route.normalize g c)) ∧
    Oblivious a (NeedSupply.form route.spread eff.caller eff.values eff.args) ∧
    (∀ o g cells, Oblivious a (route.dispatch o g cells eff.caller eff.values (openExprName eff.callee))) :=
  ⟨fun _ _ _ => disciplined_pure _, disciplined_pure _, fun _ _ => disciplined_pure _,
   oblivious_pure a _, fun _ _ => oblivious_pure a _, oblivious_pure a _,
   fun _ _ _ => oblivious_pure a _⟩

end KatLang.CallPlan
