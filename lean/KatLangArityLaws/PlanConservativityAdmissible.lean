import KatLangArityLaws.PlanConservativity
import KatLangArityLaws.PlanActiveCells

open KatLang KatLang.CallPlan KatLang.EvaluatorCore KatLang.PlanConservativity

/-!
# Plan conservativity: admissible contracts, the active mark, and the reference-free instance (E-18)

`PlanConservativity.production_fresh_plan_on` states the fresh-plan simulation of a call or
extension plan under two UNRESTRICTED contracts that no reference-excluding invariant can meet
(`PlanConservativityGuards.referenceExclusionsFailPush`, `unrestrictedDispatchCreatesRef`):

* `PushClosed P` — `P` survives a push of ANY cell, including a Ready `callRef a`;
* `PlanCalls Q` — the call domain contains EVERY argument of the route's four operation families,
  including a dispatch to a `meta` callee.

This module replaces them by contracts restricted to ADMISSIBLE inputs and proves the simulation
under them. Nothing here changes a definition of `KatLang.lean`.

* **Admissible allocation** `FormAdmissible P ctx env R`: `P` survives the two pushes supply
  formation over `(ctx, env)` can perform — a suspended `.expression e ctx env` cell, and a Ready
  cell holding a value satisfying `R`. With the output contract `OutSat P (SpreadOk R)` of the
  plan's computed spreads, `form_on_adm` proves formation oblivious and `P`-keeping;
  `formAdmissible_of_pushClosed` shows the old contract is a special case.
* **Admissible calls** `PlanCallsOn Q RT RN eff`: the call domain contains only the plan's OWN
  callee resolution and written spread expressions (at its effective caller context and values), normalization of
  callees satisfying `RT`, and dispatches to normalized callees satisfying `RN`; `RT`/`RN` are
  carried by the output contracts `OutSat P RT` (callee) and `OutSat P RN` (normalization).
  `planCallsOn_of_planCalls` shows the old contract is a special case.
* **The admissible simulation** `fresh_plan_is_ordinary_call_adm` and its production instances
  `production_fresh_plan_adm`, `production_value_is_ordinary_adm`,
  `production_value_is_evalCallCountedExpr_adm`: the conclusions of the `_on` theorems, verbatim,
  under production-level two-run facts `Keeps P (evalUnbounded c)` / `ObliviousOn P a
  (evalUnbounded c)` for `c` in the admissible domain. `production_fresh_plan_on_of_adm` re-derives
  the old theorem from the new one.
* **The active mark, discharged for all bodies.** `Active a` (the plan's cell is `evaluating`) is
  kept by EVERY production operation (`keeps_active_production`, from
  `ActiveCells.evalUnbounded_actDisc`, a per-body proof over all 104 `EvalCall` bodies).
  `keeps_production_active` therefore reduces `Keeps (Active a ∧ R)` to the body obligation
  `BodyKeepsGiven Q (Active a) R`, in which a body may assume the mark at both ends;
  `oblivious_production_of_keeps` takes the keeping fact at fuel level instead of `BodyKeeps`.
* **The reference-free instance.** `ActiveRefFree a` = `Active a` ∧ `StoredRefFree` (no stored
  value — completed or Ready cell, captured value environment, property cache, lexical activation —
  contains a call reference or argument view; the Prop form of the guards' `refFree`).
  `formAdmissible_activeRefFree` proves the admissible allocation contract at it for every
  reference-free value environment, and `production_fresh_plan_refFree` instantiates the
  simulation there.

NOT proved here: `BodyKeepsGiven Q (Active a) StoredRefFree`, `BodyObliviousOn Q (ActiveRefFree a) a`,
or the three output contracts, for any non-trivial admissible domain. `StoredRefFree` is in fact
NOT preserved by loop-only runs: Lean's `while`/`repeat` bind their step through the builtin
`meta step` parameter, which stores a Ready `callRef` adapter for the STEP cell
(`PlanConservativityAdmissibleGuards.loopRunStoresReference`, which also checks a reference to a
still-suspended plan); conservativity still holds there
while the stored reference does not reach `a` (both are executable observations, not a sufficiency
theorem). A loop-covering invariant must therefore exclude
REACHABILITY of `a` from stored references (the guards' `unreachableFromRefs`), not references in
general; see the ledger row E-18.
-/

namespace KatLang.PlanConservativityAdmissible

/-! ## Output contracts and output-aware composition -/

/-- Every successful outcome of `m` from a state satisfying `P` satisfies `R`. -/
def OutSat {α : Type} (P : EvalState → Prop) (R : α → Prop) (m : EvalM α) : Prop :=
  ∀ s x t, P s → m.runState s = (.ok x, t) → R x

theorem outSat_true {α : Type} (P : EvalState → Prop) (m : EvalM α) : OutSat P (fun _ => True) m :=
  fun _ _ _ _ _ => trivial

theorem Keeps.bind_out {α β : Type} {P : EvalState → Prop} {R : α → Prop} {m : EvalM α}
    {f : α → EvalM β} (hm : Keeps P m) (ho : OutSat P R m) (hf : ∀ x, R x → Keeps P (f x)) :
    Keeps P (m >>= f) := by
  intro s hP hne
  rw [bind_run] at hne ⊢
  have hk := hm s hP
  rcases hr : m.runState s with ⟨o, t⟩
  rw [hr] at hk hne
  cases o with
  | error e => simp only at hne ⊢; exact hk (by simpa using hne)
  | ok x => exact hf x (ho s x t hP hr) t (hk (by intro h; cases h)) hne

theorem ObliviousOn.bind_out {α β : Type} {P : EvalState → Prop} {R : α → Prop} {a : Nat}
    {m : EvalM α} {f : α → EvalM β} (hm : ObliviousOn P a m) (hk : Keeps P m) (hd : Disciplined m)
    (ho : OutSat P R m) (hf : ∀ x, R x → ObliviousOn P a (f x)) : ObliviousOn P a (m >>= f) := by
  intro s p hP hv
  rw [bind_run, bind_run, hm s p hP hv]
  have hk' := hk s hP
  have hv' := size_of_disciplined hd a s hv
  rcases hr : m.runState s with ⟨o, t⟩
  rw [hr] at hk' hv'
  cases o with
  | error e => rfl
  | ok x => exact hf x (ho s x t hP hr) t p (hk' (by intro h; cases h)) hv'

theorem Keeps.mapM_mem {α β : Type} {P : EvalState → Prop} (f : α → EvalM β) (xs : List α)
    (hk : ∀ x ∈ xs, Keeps P (f x)) : Keeps P (xs.mapM f) := by
  suffices h : ∀ (acc : List β), Keeps P (List.mapM.loop f xs acc) from h []
  induction xs with
  | nil => intro acc; exact keeps_pure P _
  | cons x rest ih =>
    intro acc
    exact Keeps.bind (hk x (List.mem_cons_self ..))
      (fun y => ih (fun z hz => hk z (List.mem_cons_of_mem _ hz)) (y :: acc))

theorem ObliviousOn.mapM_mem {α β : Type} {P : EvalState → Prop} {a : Nat} (f : α → EvalM β)
    (xs : List α) (ho : ∀ x ∈ xs, ObliviousOn P a (f x)) (hk : ∀ x ∈ xs, Keeps P (f x))
    (hd : ∀ x, Disciplined (f x)) : ObliviousOn P a (xs.mapM f) := by
  suffices h : ∀ (acc : List β), ObliviousOn P a (List.mapM.loop f xs acc) from h []
  induction xs with
  | nil => intro acc; exact oblivious_pure' P a _
  | cons x rest ih =>
    intro acc
    exact ObliviousOn.bind (ho x (List.mem_cons_self ..)) (hk x (List.mem_cons_self ..)) (hd x)
      (fun y => ih (fun z hz => ho z (List.mem_cons_of_mem _ hz))
        (fun z hz => hk z (List.mem_cons_of_mem _ hz)) (y :: acc))

/-! ## The admissible allocation contract -/

/-- `P` survives exactly the pushes supply formation over `(ctx, env)` performs: a fresh
    suspended expression cell of that caller, and a fresh Ready cell holding a value satisfying
    `R` (a computed spread's item). -/
structure FormAdmissible (P : EvalState → Prop) (ctx : EvalCtx) (env : ValEnv) (R : Result → Prop) :
    Prop where
  expr : ∀ s e, P s → P { s with needs := s.needs.push { suspension := .expression e ctx env } }
  ready : ∀ s v, P s → R v →
    P { s with needs := s.needs.push { suspension := .ready (v, Result.valueCount v) } }

theorem formAdmissible_of_pushClosed {P : EvalState → Prop} (hpush : PushClosed P) (ctx : EvalCtx)
    (env : ValEnv) (R : Result → Prop) : FormAdmissible P ctx env R :=
  ⟨fun s _ hP => hpush s _ hP, fun s _ hP _ => hpush s _ hP⟩

/-- What a computed spread may contribute under an item contract `R`. -/
def SpreadOk (R : Result → Prop) : SpreadSupply → Prop
  | .items values => ∀ v ∈ values, R v
  | .cells _ => True

theorem keeps_supply_adm {P : EvalState → Prop} {ctx : EvalCtx} {env : ValEnv} {R : Result → Prop}
    (hadm : FormAdmissible P ctx env R) (e : Expr) : Keeps P (supplyNeed e ctx env) := by
  intro s hP _
  rcases supply_cases e ctx env s with h | h <;> rw [h]
  · exact hP
  · exact hadm.expr s e hP

theorem keeps_ready_adm {P : EvalState → Prop} {ctx : EvalCtx} {env : ValEnv} {R : Result → Prop}
    (hadm : FormAdmissible P ctx env R) (v : Result) (hv : R v) :
    Keeps P (readyNeed (v, Result.valueCount v)) := by
  intro s hP _
  show P ((allocateNeed _).runState s).2
  rw [KatLang.NeedControl.Allocation.allocate_run]
  exact hadm.ready s v hP hv

/-- **Admissible slot keeping.** -/
theorem slot_keeps_adm (P : EvalState → Prop) (ctx : EvalCtx) (env : ValEnv) (R : Result → Prop)
    (hadm : FormAdmissible P ctx env R) (ev : NeedSupply.SpreadEval)
    (args : OutputBundle)
    (hkev : ∀ e, .sequenceSpread e ∈ args → Keeps P (ev (.sequenceSpread e) ctx env))
    (hsev : ∀ e, .sequenceSpread e ∈ args → OutSat P (SpreadOk R) (ev (.sequenceSpread e) ctx env))
    (e : Expr) (he : e ∈ args) :
    Keeps P (NeedSupply.slot ev ctx env e) := by
  cases e with
  | sequenceSpread operand =>
    refine Keeps.bind (keeps_of_state P _ (fun s => spread_slice_readonly operand ctx s)) (fun known => ?_)
    cases known with
    | some slice =>
      exact Keeps.mapM _ (fun b => Keeps.bind
        (keeps_of_state P _ (fun s => by rw [KatLang.NeedControl.Provenance.source_run]))
        (fun _ => keeps_pure P _)) slice
    | none =>
      refine Keeps.bind_out (hkev _ he) (hsev _ he) (fun supplied hok => ?_)
      cases supplied with
      | items values =>
        exact Keeps.mapM_mem _ values (fun v hv =>
          Keeps.bind (keeps_ready_adm hadm v (hok v hv)) (fun _ => keeps_pure P _))
      | cells cells => exact keeps_pure P _
  | _ => exact Keeps.bind (keeps_supply_adm hadm _) (fun _ => keeps_pure P _)

/-- **Admissible slot obliviousness.** -/
theorem slot_oblivious_adm (P : EvalState → Prop) (a : Nat) (ctx : EvalCtx) (env : ValEnv)
    (R : Result → Prop) (hadm : FormAdmissible P ctx env R) (ev : NeedSupply.SpreadEval)
    (hdev : ∀ e c v, Disciplined (ev e c v)) (args : OutputBundle)
    (hkev : ∀ e, .sequenceSpread e ∈ args → Keeps P (ev (.sequenceSpread e) ctx env))
    (hsev : ∀ e, .sequenceSpread e ∈ args → OutSat P (SpreadOk R) (ev (.sequenceSpread e) ctx env))
    (hoev : ∀ e, .sequenceSpread e ∈ args → ObliviousOn P a (ev (.sequenceSpread e) ctx env))
    (e : Expr) (he : e ∈ args) : ObliviousOn P a (NeedSupply.slot ev ctx env e) := by
  cases e with
  | sequenceSpread operand =>
    refine ObliviousOn.bind (ObliviousOn.of_oblivious P (oblivious_slice a operand ctx))
      (keeps_of_state P _ (fun s => spread_slice_readonly operand ctx s)) (disciplined_slice operand ctx)
      (fun known => ?_)
    cases known with
    | some slice =>
      exact ObliviousOn.mapM _
        (fun b => ObliviousOn.bind (ObliviousOn.of_oblivious P (oblivious_source a b))
          (keeps_of_state P _ (fun s => by rw [KatLang.NeedControl.Provenance.source_run]))
          (disciplined_source b) (fun _ => oblivious_pure' P a _))
        (fun b => Keeps.bind (keeps_of_state P _ (fun s => by rw [KatLang.NeedControl.Provenance.source_run]))
          (fun _ => keeps_pure P _))
        (fun b => Disciplined.bind (disciplined_source b) (fun _ => disciplined_pure _)) slice
    | none =>
      refine ObliviousOn.bind_out (hoev _ he) (hkev _ he) (hdev _ _ _) (hsev _ he) (fun supplied hok => ?_)
      cases supplied with
      | items values =>
        exact ObliviousOn.mapM_mem _ values
          (fun v _ => ObliviousOn.bind (ObliviousOn.of_oblivious P (oblivious_allocate a _))
            (keeps_ready_adm hadm v (hok v ‹_›)) (disciplined_allocate _) (fun _ => oblivious_pure' P a _))
          (fun v hv => Keeps.bind (keeps_ready_adm hadm v (hok v hv)) (fun _ => keeps_pure P _))
          (fun v => Disciplined.bind (disciplined_allocate _) (fun _ => disciplined_pure _))
      | cells cells => exact oblivious_pure' P a _
  | _ =>
    exact ObliviousOn.bind (ObliviousOn.of_oblivious P (oblivious_supply a _ _ _)) (keeps_supply_adm hadm _)
      (disciplined_supply _ _ _) (fun _ => oblivious_pure' P a _)

/-- **Admissible supply formation**: oblivious and `P`-keeping over `(ctx, env)` whenever the
    allocation contract holds there and the spread capability, on the bundle's written spread
    expressions at `(ctx, env)`, is oblivious, `P`-keeping and returns admissible items. -/
theorem form_on_adm (P : EvalState → Prop) (a : Nat) (ctx : EvalCtx) (env : ValEnv) (R : Result → Prop)
    (hadm : FormAdmissible P ctx env R) (ev : NeedSupply.SpreadEval)
    (hdev : ∀ e c v, Disciplined (ev e c v)) (args : OutputBundle)
    (hkev : ∀ e, .sequenceSpread e ∈ args → Keeps P (ev (.sequenceSpread e) ctx env))
    (hsev : ∀ e, .sequenceSpread e ∈ args → OutSat P (SpreadOk R) (ev (.sequenceSpread e) ctx env))
    (hoev : ∀ e, .sequenceSpread e ∈ args → ObliviousOn P a (ev (.sequenceSpread e) ctx env)) :
    ObliviousOn P a (NeedSupply.form ev ctx env args) ∧ Keeps P (NeedSupply.form ev ctx env args) := by
  revert hkev hsev hoev
  induction args with
  | nil => intro _ _ _; exact ⟨oblivious_pure' P a _, keeps_pure P _⟩
  | cons e rest ih =>
    intro hkev hsev hoev
    have hs := slot_oblivious_adm P a ctx env R hadm ev hdev (e :: rest)
      hkev hsev hoev e (List.mem_cons_self ..)
    have ks := slot_keeps_adm P ctx env R hadm ev (e :: rest)
      hkev hsev e (List.mem_cons_self ..)
    have hrest := ih (fun x hx => hkev x (List.mem_cons_of_mem _ hx))
      (fun x hx => hsev x (List.mem_cons_of_mem _ hx))
      (fun x hx => hoev x (List.mem_cons_of_mem _ hx))
    have drest := disciplined_form ev hdev ctx env rest
    exact ⟨ObliviousOn.bind hs ks (disciplined_slot ev hdev ctx env e) (fun _ =>
        ObliviousOn.bind hrest.1 hrest.2 drest (fun _ => oblivious_pure' P a _)),
      Keeps.bind ks (fun _ => Keeps.bind hrest.2 (fun _ => keeps_pure P _))⟩

/-! ## The admissible fresh-plan simulation -/

/-- `fresh_plan_is_ordinary_call_on` with its normalization and dispatch contracts restricted:
    normalization only of callees the callee phase can return (`RT`, carried by `scallee`) at the
    plan's effective caller, dispatch only to normalized callees satisfying `RN` (carried by
    `snormal`). The conclusion is verbatim. -/
theorem fresh_plan_is_ordinary_call_adm (P : EvalState → Prop) (RT RN : Algorithm → Prop)
    (route : NeedPlan.Route) (a : Nat) (shape : NeedPlan.CallShape) (r : PlanRoute)
    (s : EvalState) (cell : NeedCell) (hP : P s)
    (hc : s.needs[a]? = some cell) (hp : cell.plan = .unprepared)
    (hr : cell.route = some r) (hi : r ≠ .intrinsic)
    (hev : ∀ e c v, Disciplined (route.spread e c v))
    (dcallee : Disciplined (NeedPlan.calleeAlong route a (NeedPlan.effective shape r) r))
    (dnormal : ∀ g c, Disciplined (route.normalize g c))
    (kcallee : Keeps P (NeedPlan.calleeAlong route a (NeedPlan.effective shape r) r))
    (scallee : OutSat P RT (NeedPlan.calleeAlong route a (NeedPlan.effective shape r) r))
    (knormal : ∀ g, RT g → Keeps P (route.normalize g (NeedPlan.effective shape r).caller))
    (snormal : ∀ g, RT g → OutSat P RN (route.normalize g (NeedPlan.effective shape r).caller))
    (kform : Keeps P (NeedSupply.form route.spread (NeedPlan.effective shape r).caller
      (NeedPlan.effective shape r).values (NeedPlan.effective shape r).args))
    (ocallee : ObliviousOn P a (NeedPlan.calleeAlong route a (NeedPlan.effective shape r) r))
    (onormal : ∀ g, RT g → ObliviousOn P a (route.normalize g (NeedPlan.effective shape r).caller))
    (oform : ObliviousOn P a (NeedSupply.form route.spread (NeedPlan.effective shape r).caller
      (NeedPlan.effective shape r).values (NeedPlan.effective shape r).args))
    (odispatch : ∀ g cells, RN g → ObliviousOn P a
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
  generalize heff : NeedPlan.effective shape r = eff at dcallee kcallee scallee knormal snormal kform ocallee onormal oform odispatch
  simp only [NeedPlan.executeAlong, ordinaryCall, bind_run, withCtx_run, heff, dispatchName_run, dispatchOrigin_run]
  have k1 := dcallee s
  have r1keep := oblivious_on_keeps_record ocallee .unprepared s hP cell hc hp
  have hP1 := kcallee s hP
  have hs1 := scallee s
  generalize hr1 : (NeedPlan.calleeAlong route a eff r).runState s = r1 at k1 r1keep odispatch hP1 hs1
  rcases r1 with ⟨o1, t1⟩
  cases o1 with
  | error e => exact ⟨rfl, Or.inl rfl⟩
  | ok callee =>
    dsimp only at r1keep odispatch hP1 ⊢
    have hP1 := hP1 (by intro h; cases h)
    have hRT : RT callee := hs1 callee t1 hP rfl
    obtain ⟨c1, hc1, kc1⟩ := k1 a cell hc
    have hp1 : c1.plan = .unprepared := by
      have := congrArg (fun st : EvalState => (st.needs[a]?).map NeedCell.plan) r1keep
      simp [withPlan, modify_get, hc1] at this
      exact this
    have k2 := dnormal callee eff.caller t1
    have r2keep := oblivious_on_keeps_record (onormal callee hRT) .unprepared t1 hP1 c1 hc1 hp1
    have hP2 := knormal callee hRT t1 hP1
    have hs2 := snormal callee hRT t1
    generalize hr2 : (route.normalize callee eff.caller).runState t1 = r2 at k2 r2keep hP2 hs2
    rcases r2 with ⟨o2, t2⟩
    cases o2 with
    | error e => exact ⟨rfl, Or.inl rfl⟩
    | ok normal =>
      dsimp only at r2keep hP2 ⊢
      have hP2 := hP2 (by intro h; cases h)
      have hRN : RN normal := hs2 normal t2 hP1 rfl
      obtain ⟨c2, hc2, kc2⟩ := k2 a c1 hc1
      have hp2 : c2.plan = .unprepared := by
        have := congrArg (fun st : EvalState => (st.needs[a]?).map NeedCell.plan) r2keep
        simp [withPlan, modify_get, hc2] at this
        exact this
      have of2 := oform t2 .preparing hP2 (valid_of_get hc2)
      have hP3 := kform t2 hP2
      cases hinc : ((NeedSupply.form route.spread eff.caller eff.values eff.args).runState
          t2).1.isIncomplete with
      | true =>
        have hinc' : ((NeedSupply.form route.spread eff.caller eff.values eff.args).runState
            (withPlan a .preparing t2)).1.isIncomplete = true := by
          rw [of2]; exact hinc
        rw [prepare_unprepared_incomplete route.spread a eff t2 c2 hc2 hp2 hinc', of2]
        generalize hr3 : (NeedSupply.form route.spread eff.caller eff.values eff.args).runState t2 = r3
          at hinc
        rcases r3 with ⟨o3, t3⟩
        dsimp only at hinc ⊢
        rw [Except.isIncomplete_eq_true hinc]
        exact ⟨rfl, Or.inr (Or.inr ⟨rfl, rfl⟩)⟩
      | false =>
      rw [prepare_unprepared route.spread a eff t2 c2 hc2 hp2 (by rw [of2]; exact hinc)]
      dsimp only
      rw [of2]
      generalize hr3 : (NeedSupply.form route.spread eff.caller eff.values eff.args).runState t2 = r3
        at hinc hP3
      rcases r3 with ⟨o3, t3⟩
      dsimp only at hinc hP3 ⊢
      rw [withPlan_withPlan]
      cases o3 with
      | error e => exact ⟨rfl, Or.inr (Or.inl ⟨.error e, rfl⟩)⟩
      | ok cells =>
        dsimp only
        have hP3 := hP3 (by intro h; cases h)
        have hv3 : a < t3.needs.size := by
          obtain ⟨c3, hc3, _⟩ := disciplined_form route.spread hev eff.caller eff.values eff.args t2 a c2 hc2
          rw [hr3] at hc3
          exact valid_of_get hc3
        rw [odispatch normal cells hRN t3 (.prepared (.ok cells)) hP3 hv3]
        generalize (route.dispatch (NeedPlan.dispatchOriginIn t1.needs a eff r) normal cells eff.caller eff.values
          (NeedPlan.dispatchNameIn t1.needs a eff r)).runState t3 = r4
        rcases r4 with ⟨o4, t4⟩
        cases o4 with
        | error e => exact ⟨rfl, Or.inr (Or.inl ⟨.ok cells, rfl⟩)⟩
        | ok v => exact ⟨rfl, Or.inr (Or.inl ⟨.ok cells, rfl⟩)⟩

/-! ## The admissible call domain and the production instance -/

/-- **The admissible call domain** of a written (call or extension) route over its effective shape
    `eff`: the plan's own callee resolution and written spread expressions, normalization of callees
    satisfying `RT`, and dispatch — under the route's written origin and dispatch name — of
    normalized callees satisfying `RN`. Unlike `PlanCalls`, no other argument is included. -/
def PlanCallsOn (Q : EvalCall → Prop) (RT RN : Algorithm → Prop) (eff : NeedPlan.CallShape)
    (r : PlanRoute) : Prop :=
  Q (.resolveCalleeAlg eff.callee eff.caller) ∧
  (∀ g, RT g → Q (.needPlanNormalizeCallee g eff.caller)) ∧
  (∀ e, .sequenceSpread e ∈ eff.args → Q (.evalSupplySpread (.sequenceSpread e) eff.caller eff.values)) ∧
  (∀ g cells, RN g → Q (.evalSuppliedCallCounted (.written eff.callee eff.caller) g cells eff.caller
    eff.values (NeedPlan.writtenDispatchName eff r)))

theorem planCallsOn_of_planCalls {Q : EvalCall → Prop} (hQ : PlanCalls Q) (RT RN : Algorithm → Prop)
    (eff : NeedPlan.CallShape) (r : PlanRoute) : PlanCallsOn Q RT RN eff r :=
  ⟨hQ.1 _ _, fun g _ => hQ.2.1 g _, fun e _ => hQ.2.2.1 (.sequenceSpread e) _ _,
    fun g cells _ => hQ.2.2.2 _ g cells _ _ _⟩

/-- **The output contracts** of a written route's own operations at its effective shape: the
    callee phase returns `RT` callees, normalization maps them to `RN` callees, and every written
    spread operand returns items satisfying `R`. -/
structure PlanOutputs (P : EvalState → Prop) (RT RN : Algorithm → Prop) (R : Result → Prop)
    (eff : NeedPlan.CallShape) : Prop where
  callee : OutSat P RT (resolveCalleeAlg eff.callee eff.caller)
  normalize : ∀ g, RT g → OutSat P RN (NeedPlan.normalizeCallee g eff.caller)
  spread : ∀ e, .sequenceSpread e ∈ eff.args →
    OutSat P (SpreadOk R) (evalSupplySpread (.sequenceSpread e) eff.caller eff.values)

theorem planOutputs_true (P : EvalState → Prop) (eff : NeedPlan.CallShape) :
    PlanOutputs P (fun _ => True) (fun _ => True) (fun _ => True) eff :=
  ⟨outSat_true _ _, fun _ _ => outSat_true _ _, fun _ _ _ x _ _ _ => by cases x <;> simp [SpreadOk]⟩

/-- **Production fresh-plan simulation under ADMISSIBLE contracts.** For an invariant `P` whose
    production two-run facts hold on a call domain `Q` (`kprod`, `oprod`), whose allocation
    contract holds at the plan's effective caller and values (`hadm`), which contains the plan's
    admissible calls (`hQ`) and whose output contracts hold (`hout`): one production execution of
    a FRESH call or extension plan from a state satisfying `P` is the ordinary call composition up
    to the plan's own record. -/
theorem production_fresh_plan_adm (Q : EvalCall → Prop) (P : EvalState → Prop) (a : Nat)
    (RT RN : Algorithm → Prop) (R : Result → Prop)
    (kprod : ∀ c, Q c → Keeps P (evalUnbounded c)) (oprod : ∀ c, Q c → ObliviousOn P a (evalUnbounded c))
    (shape : NeedPlan.CallShape) (r : PlanRoute)
    (hadm : FormAdmissible P (NeedPlan.effective shape r).caller (NeedPlan.effective shape r).values R)
    (hQ : PlanCallsOn Q RT RN (NeedPlan.effective shape r) r)
    (hout : PlanOutputs P RT RN R (NeedPlan.effective shape r))
    (s : EvalState) (cell : NeedCell) (hP : P s)
    (hc : s.needs[a]? = some cell) (hp : cell.plan = .unprepared)
    (hr : cell.route = some r) (hi : r ≠ .intrinsic) (ha : r ≠ .algorithm) :
    ((NeedPlan.execute productionPlanRoute a shape).runState s).1 =
      ((ordinaryCall productionPlanRoute a shape r).runState s).1 ∧
    (((NeedPlan.execute productionPlanRoute a shape).runState s).2 =
        ((ordinaryCall productionPlanRoute a shape r).runState s).2 ∨
      (∃ o, ((NeedPlan.execute productionPlanRoute a shape).runState s).2 =
        withPlan a (.prepared o) ((ordinaryCall productionPlanRoute a shape r).runState s).2) ∨
      (((NeedPlan.execute productionPlanRoute a shape).runState s).1 = .error .fuelExhausted ∧
        ((NeedPlan.execute productionPlanRoute a shape).runState s).2 =
          withPlan a .preparing ((ordinaryCall productionPlanRoute a shape r).runState s).2)) := by
  obtain ⟨qt, qn, qs, qd⟩ := hQ
  have hd := KatLang.EvaluatorDiscipline.productionDiscipline_holds
  have htarget := calleeAlong_target productionPlanRoute a (NeedPlan.effective shape r) r ha hi
  have dsp : ∀ e c v, Disciplined (productionPlanRoute.spread e c v) := hd.2.2.2.2.2.1
  have hform := form_on_adm P a _ _ R hadm productionPlanRoute.spread dsp (NeedPlan.effective shape r).args
    (fun e he => kprod _ (qs e he)) hout.spread (fun e he => oprod _ (qs e he))
  refine fresh_plan_is_ordinary_call_adm P RT RN productionPlanRoute a shape r s cell hP hc hp hr hi dsp
    (by rw [htarget]; exact hd.2.1 _ _) hd.2.2.1
    (by rw [htarget]; exact kprod _ qt)
    (by rw [htarget]; exact hout.callee)
    (fun g hg => kprod _ (qn g hg))
    hout.normalize
    hform.2
    (by rw [htarget]; exact oprod _ qt)
    (fun g hg => oprod _ (qn g hg))
    hform.1
    (fun g cells hg => ?_)
  rw [dispatchOriginIn_callable _ a _ r ha, dispatchNameIn_callable _ a _ r ha]
  exact oprod _ (qd g cells hg)

/-- The old production theorem is the admissible one at the trivial output contracts. -/
theorem production_fresh_plan_on_of_adm (Q : EvalCall → Prop) (P : EvalState → Prop) (a : Nat)
    (hkB : BodyKeeps Q P) (hoB : BodyObliviousOn Q P a) (hpush : PushClosed P) (hQ : PlanCalls Q)
    (shape : NeedPlan.CallShape) (r : PlanRoute) (s : EvalState) (cell : NeedCell) (hP : P s)
    (hc : s.needs[a]? = some cell) (hp : cell.plan = .unprepared)
    (hr : cell.route = some r) (hi : r ≠ .intrinsic) (ha : r ≠ .algorithm) :
    ((NeedPlan.execute productionPlanRoute a shape).runState s).1 =
      ((ordinaryCall productionPlanRoute a shape r).runState s).1 ∧
    (((NeedPlan.execute productionPlanRoute a shape).runState s).2 =
        ((ordinaryCall productionPlanRoute a shape r).runState s).2 ∨
      (∃ o, ((NeedPlan.execute productionPlanRoute a shape).runState s).2 =
        withPlan a (.prepared o) ((ordinaryCall productionPlanRoute a shape r).runState s).2) ∨
      (((NeedPlan.execute productionPlanRoute a shape).runState s).1 = .error .fuelExhausted ∧
        ((NeedPlan.execute productionPlanRoute a shape).runState s).2 =
          withPlan a .preparing ((ordinaryCall productionPlanRoute a shape r).runState s).2)) :=
  production_fresh_plan_adm Q P a (fun _ => True) (fun _ => True) (fun _ => True)
    (fun c hq => keeps_production Q P hkB c hq) (fun c hq => oblivious_production Q P a hkB hoB c hq)
    shape r (formAdmissible_of_pushClosed hpush _ _ _)
    (planCallsOn_of_planCalls hQ _ _ _ r) (planOutputs_true P _) s cell hP hc hp hr hi ha

/-- **Production VALUE of a fresh plan under admissible contracts.** -/
theorem production_value_is_ordinary_adm (Q : EvalCall → Prop) (P : EvalState → Prop) (a : Nat)
    (RT RN : Algorithm → Prop) (R : Result → Prop)
    (kprod : ∀ c, Q c → Keeps P (evalUnbounded c)) (oprod : ∀ c, Q c → ObliviousOn P a (evalUnbounded c))
    (s : EvalState) (cell : NeedCell) (e : Expr) (c : EvalCtx) (v : ValEnv)
    (shape : NeedPlan.CallShape) (r : PlanRoute)
    (hadm : FormAdmissible P (NeedPlan.effective shape r).caller (NeedPlan.effective shape r).values R)
    (hQ : PlanCallsOn Q RT RN (NeedPlan.effective shape r) r)
    (hout : PlanOutputs P RT RN R (NeedPlan.effective shape r))
    (hc : s.needs[a]? = some cell) (hsus : cell.suspension = .expression e c v)
    (hshape : NeedPlan.callShape? e c v = some shape) (hs : cell.state = .suspended)
    (hp : cell.plan = .unprepared) (hr : cell.route = some r) (hi : r ≠ .intrinsic) (ha : r ≠ .algorithm)
    (hP : P (withState a .evaluating s))
    (hcomplete : ((NeedPlan.execute productionPlanRoute a shape).runState
      (withState a .evaluating s)).1.isIncomplete = false) :
    ((demandNeed a).runState s).1 =
      ((ordinaryCall productionPlanRoute a shape r).runState (withState a .evaluating s)).1 ∧
    ∃ t, ((demandNeed a).runState s).2 = withState a (.completed ((demandNeed a).runState s).1) t ∧
      (t = ((ordinaryCall productionPlanRoute a shape r).runState (withState a .evaluating s)).2 ∨
       ∃ o, t = withPlan a (.prepared o)
         ((ordinaryCall productionPlanRoute a shape r).runState (withState a .evaluating s)).2) := by
  have hv := production_value_executes_plan a s cell e c v shape r hc hsus hshape hs hr hi hcomplete
  have he : (withState a .evaluating s).needs[a]? = some { cell with state := .evaluating } := by
    simp [withState, modify_get, hc]
  have hf := production_fresh_plan_adm Q P a RT RN R kprod oprod shape r hadm hQ hout
    (withState a .evaluating s) { cell with state := .evaluating } hP he hp hr hi ha
  rw [hv]
  dsimp only
  refine ⟨hf.1, _, rfl, ?_⟩
  rcases hf.2 with h | h | ⟨hfe, _⟩
  · exact Or.inl h
  · exact Or.inr h
  · rw [hfe] at hcomplete; cases hcomplete

/-- **Production VALUE of a fresh written call is the ordinary `evalCallCountedExpr`, under
    admissible contracts.** -/
theorem production_value_is_evalCallCountedExpr_adm (Q : EvalCall → Prop) (P : EvalState → Prop)
    (a : Nat) (RT RN : Algorithm → Prop) (R : Result → Prop)
    (kprod : ∀ c, Q c → Keeps P (evalUnbounded c)) (oprod : ∀ c, Q c → ObliviousOn P a (evalUnbounded c))
    (s : EvalState) (cell : NeedCell) (f : Expr) (args : OutputBundle) (c : EvalCtx) (v : ValEnv)
    (hadm : FormAdmissible P c v R)
    (hQ : PlanCallsOn Q RT RN ⟨f, args, c, v, .call⟩ .call)
    (hout : PlanOutputs P RT RN R ⟨f, args, c, v, .call⟩)
    (hc : s.needs[a]? = some cell) (hsus : cell.suspension = .expression (.call f args) c v)
    (hshape : NeedPlan.callShape? (.call f args) c v = some ⟨f, args, c, v, .call⟩)
    (hs : cell.state = .suspended) (hp : cell.plan = .unprepared) (hr : cell.route = some .call)
    (hl : linkEdge? f = none) (hP : P (withState a .evaluating s))
    (hcomp : ProductionCompletes (evalCallCountedExpr f args c v) (withState a .evaluating s)) :
    ((demandNeed a).runState s).1 =
      ((reCountValueBoundary <$> evalCallCountedExpr f args c v).runState (withState a .evaluating s)).1 ∧
    ∃ t, ((demandNeed a).runState s).2 = withState a (.completed ((demandNeed a).runState s).1) t ∧
      (t = ((reCountValueBoundary <$> evalCallCountedExpr f args c v).runState (withState a .evaluating s)).2 ∨
       ∃ o, t = withPlan a (.prepared o)
         ((reCountValueBoundary <$> evalCallCountedExpr f args c v).runState (withState a .evaluating s)).2) := by
  have hw := written_call_is_evalCallCountedExpr f args c v hl _ hcomp
  have hne : ((writtenCall (CtxMsg.call f) ⟨f, args, c, v, .call⟩).runState (withState a .evaluating s)).1 ≠
      .error .fuelExhausted := by
    rw [hw, map_run]
    have := hcomp
    unfold ProductionCompletes at this
    revert this
    rcases (evalCallCountedExpr f args c v).runState (withState a .evaluating s) with ⟨o, t⟩
    cases o <;> simp
  have ho : (ordinaryCall productionPlanRoute a ⟨f, args, c, v, .call⟩ .call).runState (withState a .evaluating s) =
      (writtenCall (CtxMsg.call f) ⟨f, args, c, v, .call⟩).runState (withState a .evaluating s) :=
    ordinaryCall_is_written_call a ⟨f, args, c, v, .call⟩ .call (by decide) (by decide) (fun _ => rfl)
      (withState a .evaluating s) hne
  have he : (withState a .evaluating s).needs[a]? = some { cell with state := .evaluating } := by
    simp [withState, modify_get, hc]
  have hf := production_fresh_plan_adm Q P a RT RN R kprod oprod ⟨f, args, c, v, .call⟩ .call hadm hQ hout
    (withState a .evaluating s) { cell with state := .evaluating } hP he hp hr (by decide) (by decide)
  have hcomplete : ((NeedPlan.execute productionPlanRoute a ⟨f, args, c, v, .call⟩).runState
      (withState a .evaluating s)).1.isIncomplete = false := by
    rw [hf.1, ho, hw]
    have := hcomp
    unfold ProductionCompletes at this
    revert this
    rw [map_run]
    rcases (evalCallCountedExpr f args c v).runState (withState a .evaluating s) with ⟨o, t⟩
    cases o with
    | ok _ => intro _; rfl
    | error e => intro h; cases e <;> first | rfl | exact absurd rfl h
  have hv := production_value_is_ordinary_adm Q P a RT RN R kprod oprod s cell (.call f args) c v
    ⟨f, args, c, v, .call⟩ .call hadm hQ hout hc hsus hshape hs hp hr (by decide) (by decide) hP hcomplete
  have heq : (ordinaryCall productionPlanRoute a ⟨f, args, c, v, .call⟩ .call).runState (withState a .evaluating s) =
      (reCountValueBoundary <$> evalCallCountedExpr f args c v).runState (withState a .evaluating s) := by
    rw [ho]; exact hw
  rw [heq] at hv
  exact hv

/-! ## The active mark: discharged for every body -/

/-- The plan's cell `a` is `evaluating` (the completion shell's mark at the flight state). -/
def Active (a : Nat) (s : EvalState) : Prop := ∃ c, s.needs[a]? = some c ∧ c.state = .evaluating

theorem active_of_actHeapKept {a : Nat} {s t : EvalState}
    (k : KatLang.ActiveCells.ActHeapKept s.needs t.needs) (h : Active a s) : Active a t := by
  obtain ⟨c, hc, hs⟩ := h
  obtain ⟨c', hc', kc⟩ := k a c hc
  exact ⟨c', hc', kc.active hs⟩

/-- **Every production operation keeps the active mark**, from every state (all 104 bodies,
    `ActiveCells.evalStep_actDisc`). -/
theorem keeps_active_production (a : Nat) (c : EvalCall) : Keeps (Active a) (evalUnbounded c) :=
  fun s h _ => active_of_actHeapKept (KatLang.ActiveCells.evalUnbounded_actDisc c s) h

theorem keeps_active_fuel (a : Nat) (n : Nat) (c : EvalCall) : Keeps (Active a) (evalFuel n c) :=
  fun s h hne => active_of_actHeapKept (KatLang.ActiveCells.evalFuel_actDisc n c s ((evalFuel_completes_iff n c s).2 hne)) h

theorem withState_evaluating_active (a : Nat) (s : EvalState) (cell : NeedCell)
    (hc : s.needs[a]? = some cell) : Active a (withState a .evaluating s) :=
  ⟨{ cell with state := .evaluating }, by simp [withState, modify_get, hc], rfl⟩

/-- The per-body keeping obligation for `A ∧ R` when `A` is kept globally: from `A ∧ R`, a
    completed body run that ends in `A` ends in `R`. -/
def BodyKeepsGiven (Q : EvalCall → Prop) (A R : EvalState → Prop) : Prop :=
  ∀ rec : EvalRec, (∀ c, Q c → Keeps (fun s => A s ∧ R s) (rec c)) → ∀ c, Q c → ∀ s, A s → R s →
    ((evalStep rec c).runState s).1 ≠ .error .fuelExhausted → A ((evalStep rec c).runState s).2 →
    R ((evalStep rec c).runState s).2

theorem bodyKeeps_given_of_bodyKeeps {Q : EvalCall → Prop} {A R : EvalState → Prop}
    (h : BodyKeeps Q (fun s => A s ∧ R s)) : BodyKeepsGiven Q A R :=
  fun rec hrec c hq s hA hR hne _ => (h rec hrec c hq s ⟨hA, hR⟩ hne).2

theorem keeps_fuel_active (Q : EvalCall → Prop) (R : EvalState → Prop) (a : Nat)
    (hbody : BodyKeepsGiven Q (Active a) R) :
    ∀ n c, Q c → Keeps (fun s => Active a s ∧ R s) (evalFuel n c) := by
  intro n
  induction n with
  | zero => intro c _ s _ hne; exact absurd rfl hne
  | succ n ih =>
    intro c hq s hP hne
    have hA := keeps_active_fuel a (n + 1) c s hP.1 hne
    rw [evalFuel_succ] at hne hA ⊢
    by_cases hc : ((evalStep (evalFuel n) c).runState s).1 = .error .fuelExhausted
    · rw [normalize_of_incomplete _ s hc] at hne; exact absurd rfl hne
    · rw [normalize_of_complete _ s hc] at hA ⊢
      exact ⟨hA, hbody _ ih c hq s hP.1 hP.2 hc hA⟩

/-- **Keeping `Active a ∧ R` over production** reduces to the `R`-half of the body obligation. -/
theorem keeps_production_active (Q : EvalCall → Prop) (R : EvalState → Prop) (a : Nat)
    (hbody : BodyKeepsGiven Q (Active a) R) (c : EvalCall) (hq : Q c) :
    Keeps (fun s => Active a s ∧ R s) (evalUnbounded c) := by
  intro s hP hne
  have hc : ProductionCompletes (evalUnbounded c) s := hne
  obtain ⟨m, hr, hm⟩ := (production_completes_iff c s _).1 ⟨rfl, hc⟩
  rw [← hr]
  exact keeps_fuel_active Q R a hbody m c hq s hP ((evalFuel_completes_iff m c s).1 hm)

/-- `oblivious_fuel` with its keeping premise taken at fuel level (e.g. `keeps_fuel_active`). -/
theorem oblivious_fuel_of_keeps (Q : EvalCall → Prop) (P : EvalState → Prop) (a : Nat)
    (hkeep : ∀ n c, Q c → Keeps P (evalFuel n c)) (hbody : BodyObliviousOn Q P a) :
    ∀ n c, Q c → ObliviousOn P a (evalFuel n c) := by
  intro n
  induction n with
  | zero =>
    intro c _ s p _ _
    show ((EvalM.incomplete : EvalM c.Ret).runState (withPlan a p s)) = (_, withPlan a p {})
    rw [withPlan_empty]; rfl
  | succ n ih =>
    intro c hq
    exact normalize_oblivious P a _ (hbody _ (hkeep n) ih c hq)

/-- `oblivious_production` with its keeping premise taken at fuel level. -/
theorem oblivious_production_of_keeps (Q : EvalCall → Prop) (P : EvalState → Prop) (a : Nat)
    (hkeep : ∀ n c, Q c → Keeps P (evalFuel n c)) (hbody : BodyObliviousOn Q P a)
    (c : EvalCall) (hq : Q c) : ObliviousOn P a (evalUnbounded c) := by
  intro s p hP hv
  have hfuel := fun m => oblivious_fuel_of_keeps Q P a hkeep hbody m c hq s p hP hv
  by_cases hc : ProductionCompletes (evalUnbounded c) s
  · obtain ⟨m, hr, hm⟩ := (production_completes_iff c s _).1 ⟨rfl, hc⟩
    have hm' : Completes (evalFuel m c) (withPlan a p s) := by
      rw [evalFuel_completes_iff, hfuel m]
      exact (evalFuel_completes_iff m c s).1 hm
    have hp := ((production_completes_iff c (withPlan a p s) _).2 ⟨m, rfl, hm'⟩).1
    rw [hp, hfuel m, hr]
  · rw [production_incomplete_state c s hc]
    apply production_incomplete_state c (withPlan a p s)
    intro hc'
    obtain ⟨m, _, hm⟩ := (production_completes_iff c (withPlan a p s) _).1 ⟨rfl, hc'⟩
    apply hc
    have hm2 : Completes (evalFuel m c) s := by
      rw [evalFuel_completes_iff]
      have := (evalFuel_completes_iff m c _).1 hm
      rw [hfuel m] at this
      exact this
    exact ((production_completes_iff c s _).2 ⟨m, rfl, hm2⟩).2

/-! ## The reference-free instance -/

/-- No call reference or argument view in a value environment. -/
def envRefFreeB (env : ValEnv) : Bool := env.all fun p => !p.2.containsCallRef

/-- No call reference or argument view stored by a cell: its completed VALUE, its Ready value or
    its captured value environment. -/
def cellRefFreeB (c : NeedCell) : Bool :=
  (match c.state with
   | .completed (.ok (v, _)) => !v.containsCallRef
   | _ => true) &&
  (match c.suspension with
   | .ready (v, _) => !v.containsCallRef
   | .expression _ _ values => envRefFreeB values
   | .collector _ => true)

/-- **No stored reference at all** (the Prop form of `PlanConservativityGuards.refFree`'s state
    half): no cell, property-cache entry or lexical activation stores a value containing a call
    reference or argument view. -/
def storedRefFreeB (s : EvalState) : Bool :=
  s.needs.toList.all cellRefFreeB &&
  s.zeroArgPropertyCache.all (fun p => !p.2.1.containsCallRef) &&
  s.lexicalActivations.toList.all (fun act => envRefFreeB act.values)

def StoredRefFree (s : EvalState) : Prop := storedRefFreeB s = true

/-- The concrete candidate: the plan's cell is `evaluating` and no reference is stored. -/
def ActiveRefFree (a : Nat) (s : EvalState) : Prop := Active a s ∧ StoredRefFree s

theorem active_push {a : Nat} {s : EvalState} (c : NeedCell) (h : Active a s) :
    Active a { s with needs := s.needs.push c } := by
  obtain ⟨d, hd, hs⟩ := h
  refine ⟨d, ?_, hs⟩
  show (s.needs.push c)[a]? = some d
  rw [Array.getElem?_push]
  simp [Nat.ne_of_lt (KatLang.ActiveCells.lt_of_get hd), hd]

theorem storedRefFree_push {s : EvalState} (c : NeedCell) (h : StoredRefFree s)
    (hc : cellRefFreeB c = true) : StoredRefFree { s with needs := s.needs.push c } := by
  unfold StoredRefFree storedRefFreeB at *
  simp only [Bool.and_eq_true] at h ⊢
  refine ⟨⟨?_, h.1.2⟩, h.2⟩
  rw [Array.toList_push, List.all_append]
  simp only [Bool.and_eq_true]
  exact ⟨h.1.1, by simp [hc]⟩

/-- **The admissible allocation contract holds at `ActiveRefFree a`** for every reference-free
    value environment, with reference-free spread items. (`PushClosed` fails there:
    `PlanConservativityGuards.referenceExclusionsFailPush`.) -/
theorem formAdmissible_activeRefFree (a : Nat) (ctx : EvalCtx) (env : ValEnv)
    (henv : envRefFreeB env = true) :
    FormAdmissible (ActiveRefFree a) ctx env (fun v => v.containsCallRef = false) :=
  ⟨fun s e h => ⟨active_push _ h.1, storedRefFree_push _ h.2 (by simp [cellRefFreeB, henv])⟩,
   fun s v h hv => ⟨active_push _ h.1, storedRefFree_push _ h.2 (by simp [cellRefFreeB, hv])⟩⟩

/-- **The fresh-plan simulation at `ActiveRefFree a`.** For a call domain `Q` on which every body
    keeps the reference-free half given the active mark (`hkB`; the active half is discharged by
    `keeps_active_production`) and is oblivious (`hoB`), containing the plan's admissible calls,
    with the output contracts and a reference-free captured value environment: one production
    execution of a fresh call or extension plan at an `ActiveRefFree` state is the ordinary call up
    to the plan's own record. -/
theorem production_fresh_plan_refFree (Q : EvalCall → Prop) (a : Nat) (RT RN : Algorithm → Prop)
    (hkB : BodyKeepsGiven Q (Active a) StoredRefFree) (hoB : BodyObliviousOn Q (ActiveRefFree a) a)
    (shape : NeedPlan.CallShape) (r : PlanRoute)
    (henv : envRefFreeB (NeedPlan.effective shape r).values = true)
    (hQ : PlanCallsOn Q RT RN (NeedPlan.effective shape r) r)
    (hout : PlanOutputs (ActiveRefFree a) RT RN (fun v => v.containsCallRef = false)
      (NeedPlan.effective shape r))
    (s : EvalState) (cell : NeedCell) (hP : ActiveRefFree a s)
    (hc : s.needs[a]? = some cell) (hp : cell.plan = .unprepared)
    (hr : cell.route = some r) (hi : r ≠ .intrinsic) (ha : r ≠ .algorithm) :
    ((NeedPlan.execute productionPlanRoute a shape).runState s).1 =
      ((ordinaryCall productionPlanRoute a shape r).runState s).1 ∧
    (((NeedPlan.execute productionPlanRoute a shape).runState s).2 =
        ((ordinaryCall productionPlanRoute a shape r).runState s).2 ∨
      (∃ o, ((NeedPlan.execute productionPlanRoute a shape).runState s).2 =
        withPlan a (.prepared o) ((ordinaryCall productionPlanRoute a shape r).runState s).2) ∨
      (((NeedPlan.execute productionPlanRoute a shape).runState s).1 = .error .fuelExhausted ∧
        ((NeedPlan.execute productionPlanRoute a shape).runState s).2 =
          withPlan a .preparing ((ordinaryCall productionPlanRoute a shape r).runState s).2)) :=
  production_fresh_plan_adm Q (ActiveRefFree a) a RT RN (fun v => v.containsCallRef = false)
    (fun c hq => keeps_production_active Q StoredRefFree a hkB c hq)
    (fun c hq => oblivious_production_of_keeps Q (ActiveRefFree a) a
      (keeps_fuel_active Q StoredRefFree a hkB) hoB c hq)
    shape r (formAdmissible_activeRefFree a _ _ henv) hQ hout s cell hP hc hp hr hi ha

end KatLang.PlanConservativityAdmissible
