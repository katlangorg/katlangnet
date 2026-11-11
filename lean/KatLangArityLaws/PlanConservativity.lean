import KatLangArityLaws.EvaluatorDiscipline

open KatLang KatLang.CallPlan KatLang.EvaluatorCore

/-!
# Plan conservativity over reachable states (ledger E-18)

`CallPlan.fresh_plan_is_ordinary_call` (`InvocationPlan.lean`) relates ONE execution of a fresh
invocation plan to `ordinaryCall` under the global callback contract `Oblivious a`, which
production does not satisfy (`CallPlanGuards.dispatchIsNotGloballyOblivious`). This module replaces
that contract by a RELATIVIZED one and builds everything around it that can be proved without
choosing the invariant; `PlanConservativityGuards.lean` tests the candidate invariants on the
authoritative evaluator. Proved here, with standard axioms only:

* **The relativized contract.** `ObliviousOn P a m`: from every state satisfying `P`, changing the
  plan record of the valid cell `a` changes neither `m`'s outcome nor anything else of its final
  state. `Keeps P m`: a completed run of `m` from `P` ends in `P`. `Oblivious a` is the
  `P = True` instance (`oblivious_iff_on_true`).
* **The relativized simulation** `fresh_plan_is_ordinary_call_on`: the M1.5 statement, verbatim in its
  conclusion, with `ObliviousOn P a` and `Keeps P` for the callee, normalization and formation
  phases (the dispatch needs only `ObliviousOn`) and `P` at the entry state.
* **The two-run transfer** `oblivious_fuel` / `oblivious_production` (with `keeps_fuel` /
  `keeps_production`): over a call domain `Q`, if every evaluator BODY keeps `P` (`BodyKeeps`)
  and is oblivious on `P` (`BodyObliviousOn`) whenever its recursive answer is, then so is every
  completed or incomplete run of the core at every fuel and every production operation. Completion
  agrees on both sides (an incomplete core run forgets its state, and `withPlan a p {} = {}`).
* **Supply formation** (`slot_oblivious`, `slot_keeps`, `form_on`): `NeedSupply.form` is oblivious
  and keeps an allocation-closed `P` (`PushClosed`) whenever its spread capability is; the
  primitives (`supplyNeed`, allocation, known-slice and written-source reads) are oblivious on
  every heap.
* **The production instance** `production_fresh_plan_on` and **VALUE** `production_value_is_ordinary_on`:
  for a call or extension route, the remaining invariant contracts are `BodyKeeps Q P`,
  `BodyObliviousOn Q P a`, `PushClosed P`, `PlanCalls Q` and `P` at entry, in addition to the
  structural fresh-cell/route premises and VALUE completion. `ProductionDiscipline` is discharged
  by `productionDiscipline_holds`.
* **STEP 1: `ordinaryCall` IS production** (no conservativity premise):
  `ordinaryCall_is_written_call_named` (call and extension routes, the member call of a dot edge
  included; completed runs of the written call, named by the route's own dispatch name
  `NeedPlan.writtenDispatchName`), `ordinaryCall_is_written_call` (the same off the member call,
  where that name is the written callee's), `resolved_call_is_production`
  (normalization + formation + dispatch = the production `evalResolvedCallCounted`, using
  `resolveAliasTarget_not_alias`: production alias resolution never returns an alias) and
  `written_call_is_evalCallCountedExpr` (a written call whose callee is no `X.Algorithm` link).
  `production_value_is_evalCallCountedExpr_on` composes them: production VALUE of a fresh written
  call is the shell around the re-counted `evalCallCountedExpr`, up to the plan record, under the
  same invariant contracts and the stated structural/completion premises.

NOT proved: the invariant contracts for ANY non-trivial production `P`. The simulation conclusion
is FALSE under the entry hypotheses "`a` is `evaluating`" and
"`a` is `evaluating` and no stored value is `callRef a` / `argView a`": a reachable state built from
`EvalState.empty` by a META program (`R = Capture(Wrap(Inner((Capture(R.Arguments*).Invoke())*)))`,
`first(R.Arguments)`) satisfies both and makes the plan-routed and the ordinary outcome DIFFER
(`PlanConservativityGuards.selfInvokeOutcomeDiffers`; `obligations_fail_at` is the kernel half of
that refutation for allocation-closed invariants). These guards refute the simulation on the
candidate states; they do not by themselves instantiate `obligations_fail_at` for `noStoredRef`,
which is NOT `PushClosed`. Neither are `unreachableFromRefs` or `refFree`: an arbitrary push can
store `callRef a`. Moreover, `PlanCalls Q` includes all arguments to its four operation families,
so it does not admit a META-free restriction of those calls. `unrestrictedDispatchCreatesRef`
exhibits a META dispatch from a reference-free flight state that stores a reference to `a`,
refuting preservation for that proposed invariant under the current call domain. A META-free
theorem needs allocation and call contracts restricted by admissible inputs, as well as the
per-body proof; the present generic production instance does not supply them.
`PlanConservativityAdmissible.lean` (November 11 2026) supplies the admissible contracts
(`FormAdmissible`, `PlanCallsOn`, `PlanOutputs`; `production_fresh_plan_adm`, instantiated at
`evaluating` ∧ `refFree` by `production_fresh_plan_refFree`) and discharges the `evaluating` half
for every body (`PlanActiveCells.lean`); the reference-free half and every body's obliviousness
remain open, and `refFree` itself is not kept by loop-only runs
(`PlanConservativityAdmissibleGuards.loopRunStoresReference`).

The remaining step-1 routes are in `PlanRouteBridge.lean`. The extension route IS the production
dot evaluation (`ordinaryCall_extension_is_dot_call`, through the E-17 dot funnel). The member route
IS the production dot evaluation too (`member_bridge`: one run from one entry state), since the E-18
member-route correction of November 11 2026 named the planned member dispatch by its member
(`NeedPlan.writtenDispatchName`) — for a plain first argument over a member-selecting receiver
(a parameter head additionally requires a structure-normal supplied CALLABLE)
and for every bundle over a state-inert receiver; an empty or spread-first bundle over any other
receiver is stated relative to the origin agreement (`member_bridge_of_origin`) and not discharged.
The `.Algorithm` route is only decomposed into production operations
(`ordinaryCall_algorithm_is_production` equates it with the proof-local `algorithmPlanCall`, not the
ordinary evaluator). Its receiver READ was a language-visible difference — a receiver without output
failed with its own missing output under a property frame on the plan route — until the E-18
receiver-read correction of November 11 2026 gave the plan's retained receiver cell the ordinary
invocation receiver evaluator (`NeedInvocationRole`, `EvalBody.invocationReceiverValue` in
`KatLang.lean`; `receiver_cell_reads_invocation_receiver`, `invocationReceiverValue_eq`; regression
`algorithmReceiverFailureAgrees`). Exact final-state equality is still false
(`algorithmHeapDiffers`: the plan allocates its link and receiver cells), so the outcome bridge needs
an address-renaming simulation and is not stated. Step 1 is NOT complete.
-/

namespace KatLang.PlanConservativity


/-! ## The relativized contract -/

def ObliviousOn {α : Type} (P : EvalState → Prop) (a : Nat) (m : EvalM α) : Prop :=
  ∀ s p, P s → a < s.needs.size →
    m.runState (withPlan a p s) = ((m.runState s).1, withPlan a p (m.runState s).2)

def Keeps {α : Type} (P : EvalState → Prop) (m : EvalM α) : Prop :=
  ∀ s, P s → (m.runState s).1 ≠ .error .fuelExhausted → P (m.runState s).2

theorem oblivious_iff_on_true {α : Type} (a : Nat) (m : EvalM α) :
    Oblivious a m ↔ ObliviousOn (fun _ => True) a m :=
  ⟨fun h s p _ hv => h s p hv, fun h s p hv => h s p trivial hv⟩

theorem withPlan_empty (a : Nat) (p : NeedPlanSupply) : withPlan a p ({} : EvalState) = {} := by
  simp [withPlan]

theorem normalize_oblivious {α : Type} (P : EvalState → Prop) (a : Nat) (m : EvalM α)
    (h : ObliviousOn P a m) : ObliviousOn P a m.normalizeIncomplete := by
  intro s p hP hv
  have e := h s p hP hv
  by_cases hc : (m.runState s).1 = .error .fuelExhausted
  · rw [normalize_of_incomplete m s hc,
      normalize_of_incomplete m (withPlan a p s) (by rw [e]; exact hc), withPlan_empty]
  · rw [normalize_of_complete m s hc, normalize_of_complete m (withPlan a p s) (by rw [e]; exact hc), e]

theorem normalize_keeps {α : Type} (P : EvalState → Prop) (m : EvalM α)
    (h : Keeps P m) : Keeps P m.normalizeIncomplete := by
  intro s hP hne
  by_cases hc : (m.runState s).1 = .error .fuelExhausted
  · rw [normalize_of_incomplete m s hc] at hne; exact absurd rfl hne
  · rw [normalize_of_complete m s hc] at hne ⊢; exact h s hP hne

/-! ## The two-run transfer -/

def BodyKeeps (Q : EvalCall → Prop) (P : EvalState → Prop) : Prop :=
  ∀ rec : EvalRec, (∀ c, Q c → Keeps P (rec c)) → ∀ c, Q c → Keeps P (evalStep rec c)

def BodyObliviousOn (Q : EvalCall → Prop) (P : EvalState → Prop) (a : Nat) : Prop :=
  ∀ rec : EvalRec, (∀ c, Q c → Keeps P (rec c)) → (∀ c, Q c → ObliviousOn P a (rec c)) →
    ∀ c, Q c → ObliviousOn P a (evalStep rec c)

theorem keeps_fuel (Q : EvalCall → Prop) (P : EvalState → Prop) (hbody : BodyKeeps Q P) :
    ∀ n c, Q c → Keeps P (evalFuel n c) := by
  intro n
  induction n with
  | zero => intro c _ s _ hne; exact absurd rfl hne
  | succ n ih => intro c hq; exact normalize_keeps P _ (hbody _ ih c hq)

theorem oblivious_fuel (Q : EvalCall → Prop) (P : EvalState → Prop) (a : Nat)
    (hkeep : BodyKeeps Q P) (hbody : BodyObliviousOn Q P a) :
    ∀ n c, Q c → ObliviousOn P a (evalFuel n c) := by
  intro n
  induction n with
  | zero =>
    intro c _ s p _ _
    show ((EvalM.incomplete : EvalM c.Ret).runState (withPlan a p s)) = (_, withPlan a p {})
    rw [withPlan_empty]; rfl
  | succ n ih =>
    intro c hq
    exact normalize_oblivious P a _ (hbody _ (keeps_fuel Q P hkeep n) ih c hq)

theorem keeps_production (Q : EvalCall → Prop) (P : EvalState → Prop) (hbody : BodyKeeps Q P)
    (c : EvalCall) (hq : Q c) : Keeps P (evalUnbounded c) := by
  intro s hP hne
  have hc : ProductionCompletes (evalUnbounded c) s := hne
  obtain ⟨m, hr, hm⟩ := (production_completes_iff c s _).1 ⟨rfl, hc⟩
  rw [← hr]
  exact keeps_fuel Q P hbody m c hq s hP ((evalFuel_completes_iff m c s).1 hm)

theorem oblivious_production (Q : EvalCall → Prop) (P : EvalState → Prop) (a : Nat)
    (hkeep : BodyKeeps Q P) (hbody : BodyObliviousOn Q P a)
    (c : EvalCall) (hq : Q c) : ObliviousOn P a (evalUnbounded c) := by
  intro s p hP hv
  have hfuel := fun m => oblivious_fuel Q P a hkeep hbody m c hq s p hP hv
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

/-! ## The fresh-plan simulation under a relativized contract -/

theorem oblivious_on_keeps_record {α : Type} {P : EvalState → Prop} {m : EvalM α} {a : Nat}
    (hm : ObliviousOn P a m) (p : NeedPlanSupply) (s : EvalState) (hP : P s) (cell : NeedCell)
    (h : s.needs[a]? = some cell) (hp : cell.plan = p) : (m.runState s).2 = withPlan a p (m.runState s).2 := by
  have e := hm s p hP (valid_of_get h)
  rw [withPlan_self a p s cell h hp] at e
  exact congrArg Prod.snd e

theorem fresh_plan_is_ordinary_call_on (P : EvalState → Prop)
    (route : NeedPlan.Route) (a : Nat) (shape : NeedPlan.CallShape) (r : PlanRoute)
    (s : EvalState) (cell : NeedCell) (hP : P s)
    (hc : s.needs[a]? = some cell) (hp : cell.plan = .unprepared)
    (hr : cell.route = some r) (hi : r ≠ .intrinsic)
    (hev : ∀ e c v, Disciplined (route.spread e c v))
    (dcallee : Disciplined (NeedPlan.calleeAlong route a (NeedPlan.effective shape r) r))
    (dnormal : ∀ g c, Disciplined (route.normalize g c))
    (kcallee : Keeps P (NeedPlan.calleeAlong route a (NeedPlan.effective shape r) r))
    (knormal : ∀ g c, Keeps P (route.normalize g c))
    (kform : Keeps P (NeedSupply.form route.spread (NeedPlan.effective shape r).caller
      (NeedPlan.effective shape r).values (NeedPlan.effective shape r).args))
    (ocallee : ObliviousOn P a (NeedPlan.calleeAlong route a (NeedPlan.effective shape r) r))
    (onormal : ∀ g c, ObliviousOn P a (route.normalize g c))
    (oform : ObliviousOn P a (NeedSupply.form route.spread (NeedPlan.effective shape r).caller
      (NeedPlan.effective shape r).values (NeedPlan.effective shape r).args))
    (odispatch : ∀ g cells, ObliviousOn P a
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
  generalize heff : NeedPlan.effective shape r = eff at dcallee kcallee kform ocallee oform odispatch
  simp only [NeedPlan.executeAlong, ordinaryCall, bind_run, withCtx_run, heff, dispatchName_run, dispatchOrigin_run]
  have k1 := dcallee s
  have r1keep := oblivious_on_keeps_record ocallee .unprepared s hP cell hc hp
  have hP1 := kcallee s hP
  generalize hr1 : (NeedPlan.calleeAlong route a eff r).runState s = r1 at k1 r1keep odispatch hP1
  rcases r1 with ⟨o1, t1⟩
  cases o1 with
  | error e => exact ⟨rfl, Or.inl rfl⟩
  | ok callee =>
    dsimp only at r1keep odispatch hP1 ⊢
    have hP1 := hP1 (by intro h; cases h)
    obtain ⟨c1, hc1, kc1⟩ := k1 a cell hc
    have hp1 : c1.plan = .unprepared := by
      have := congrArg (fun st : EvalState => (st.needs[a]?).map NeedCell.plan) r1keep
      simp [withPlan, modify_get, hc1] at this
      exact this
    have k2 := dnormal callee eff.caller t1
    have r2keep := oblivious_on_keeps_record (onormal callee eff.caller) .unprepared t1 hP1 c1 hc1 hp1
    have hP2 := knormal callee eff.caller t1 hP1
    generalize hr2 : (route.normalize callee eff.caller).runState t1 = r2 at k2 r2keep hP2
    rcases r2 with ⟨o2, t2⟩
    cases o2 with
    | error e => exact ⟨rfl, Or.inl rfl⟩
    | ok normal =>
      dsimp only at r2keep hP2 ⊢
      have hP2 := hP2 (by intro h; cases h)
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
        rw [odispatch normal cells t3 (.prepared (.ok cells)) hP3 hv3]
        generalize (route.dispatch (NeedPlan.dispatchOriginIn t1.needs a eff r) normal cells eff.caller eff.values
          (NeedPlan.dispatchNameIn t1.needs a eff r)).runState t3 = r4
        rcases r4 with ⟨o4, t4⟩
        cases o4 with
        | error e => exact ⟨rfl, Or.inr (Or.inl ⟨.ok cells, rfl⟩)⟩
        | ok v => exact ⟨rfl, Or.inr (Or.inl ⟨.ok cells, rfl⟩)⟩


/-! ## Composition and the primitives of supply formation -/

theorem ObliviousOn.of_oblivious {α : Type} (P : EvalState → Prop) {a : Nat} {m : EvalM α}
    (h : Oblivious a m) : ObliviousOn P a m := fun s p _ hv => h s p hv

theorem size_of_disciplined {α : Type} {m : EvalM α} (hd : Disciplined m) (a : Nat) (s : EvalState)
    (hv : a < s.needs.size) : a < (m.runState s).2.needs.size := by
  obtain ⟨c, hc⟩ : ∃ c, s.needs[a]? = some c := ⟨_, Array.getElem?_eq_getElem hv⟩
  obtain ⟨c', hc', _⟩ := hd s a c hc
  exact valid_of_get hc'

theorem ObliviousOn.bind {α β : Type} {P : EvalState → Prop} {a : Nat} {m : EvalM α} {f : α → EvalM β}
    (hm : ObliviousOn P a m) (hk : Keeps P m) (hd : Disciplined m)
    (hf : ∀ x, ObliviousOn P a (f x)) : ObliviousOn P a (m >>= f) := by
  intro s p hP hv
  rw [bind_run, bind_run, hm s p hP hv]
  have hk' := hk s hP
  have hv' := size_of_disciplined hd a s hv
  rcases hr : m.runState s with ⟨o, t⟩
  rw [hr] at hk' hv'
  cases o with
  | error e => rfl
  | ok x => exact hf x t p (hk' (by intro h; cases h)) hv'

theorem Keeps.bind {α β : Type} {P : EvalState → Prop} {m : EvalM α} {f : α → EvalM β}
    (hm : Keeps P m) (hf : ∀ x, Keeps P (f x)) : Keeps P (m >>= f) := by
  intro s hP hne
  rw [bind_run] at hne ⊢
  have hk := hm s hP
  rcases hr : m.runState s with ⟨o, t⟩
  rw [hr] at hk hne
  cases o with
  | error e => simp only at hne ⊢; exact hk (by simpa using hne)
  | ok x => exact hf x t (hk (by intro h; cases h)) hne

theorem keeps_pure {α : Type} (P : EvalState → Prop) (x : α) : Keeps P (pure x : EvalM α) :=
  fun _ hP _ => hP

theorem keeps_of_state {α : Type} (P : EvalState → Prop) (m : EvalM α)
    (h : ∀ s, (m.runState s).2 = s) : Keeps P m := fun s hP _ => by rw [h s]; exact hP

theorem oblivious_pure' {α : Type} (P : EvalState → Prop) (a : Nat) (x : α) :
    ObliviousOn P a (pure x : EvalM α) := fun _ _ _ _ => rfl

/-- `P` survives a push of ANY cell, including Ready references. Reference-exclusion predicates
    generally fail this contract; it is stronger than preservation under META-free allocation. -/
def PushClosed (P : EvalState → Prop) : Prop :=
  ∀ s (c : NeedCell), P s → P { s with needs := s.needs.push c }

theorem withPlan_push (a : Nat) (p : NeedPlanSupply) (s : EvalState) (c : NeedCell)
    (hv : a < s.needs.size) :
    withPlan a p { s with needs := s.needs.push c } = { withPlan a p s with needs := (withPlan a p s).needs.push c } := by
  simp only [withPlan]
  congr 1
  apply Array.ext_getElem?
  intro i
  simp only [modify_get, Array.getElem?_push, Array.size_modify]
  by_cases hai : a = i
  · subst hai
    simp [Nat.ne_of_lt hv]
  · simp [hai]

theorem oblivious_allocate (a : Nat) (susp : NeedSuspension) : Oblivious a (allocateNeed susp) := by
  intro s p hv
  rw [KatLang.NeedControl.Allocation.allocate_run, KatLang.NeedControl.Allocation.allocate_run,
    withPlan_size, withPlan_push a p s _ hv]

theorem keeps_allocate (P : EvalState → Prop) (hpush : PushClosed P) (susp : NeedSuspension) :
    Keeps P (allocateNeed susp) := by
  intro s hP _
  rw [KatLang.NeedControl.Allocation.allocate_run]
  exact hpush s _ hP

theorem oblivious_captured (a : Nat) (name : Ident) (ctx : EvalCtx) :
    Oblivious a (capturedParameterActivation? name ctx) := by
  intro s p _
  rw [captured_withPlan, captured_readonly]

theorem oblivious_supply (a : Nat) (source : Expr) (caller : EvalCtx) (values : ValEnv) :
    Oblivious a (supplyNeed source caller values) := by
  intro s p hv
  by_cases hp : ∃ name, source = .param name
  · obtain ⟨name, rfl⟩ := hp
    have hcw := captured_withPlan name caller a p s
    cases h : (capturedParameterActivation? name caller).runState s with
    | mk o t =>
      obtain rfl := captured_state h
      rw [h] at hcw
      cases o with
      | error e =>
        unfold supplyNeed
        simp only [bind_run, h, hcw]
      | ok activation =>
        cases hl : lookupAssoc name (activation.map ParameterActivation.needs |>.getD caller.needEnv) with
        | none =>
          rw [KatLang.NeedControl.Allocation.supply_unbound_param name caller values _ activation h hl,
            KatLang.NeedControl.Allocation.supply_unbound_param name caller values _ activation hcw hl,
            withPlan_size, withPlan_push a p _ _ hv]
        | some b =>
          rw [KatLang.NeedControl.Allocation.supply_param_transports name caller values _ activation b h hl,
            KatLang.NeedControl.Allocation.supply_param_transports name caller values _ activation b hcw hl]
  · have hn : ∀ name, source ≠ .param name := fun name he => hp ⟨name, he⟩
    rw [KatLang.NeedControl.Allocation.supply_nonparameter source caller values _ hn,
      KatLang.NeedControl.Allocation.supply_nonparameter source caller values _ hn,
      withPlan_size, withPlan_push a p _ _ hv]

theorem keeps_supply (P : EvalState → Prop) (hpush : PushClosed P) (source : Expr) (caller : EvalCtx)
    (values : ValEnv) : Keeps P (supplyNeed source caller values) := by
  intro s hP _
  rcases supply_cases source caller values s with h | h <;> rw [h]
  · exact hP
  · exact hpush s _ hP

theorem withPlan_suspension (a : Nat) (p : NeedPlanSupply) (s : EvalState) (b : Nat) :
    ((withPlan a p s).needs[b]?).map NeedCell.suspension = (s.needs[b]?).map NeedCell.suspension := by
  simp only [withPlan, modify_get]
  by_cases hab : a = b
  · subst hab; cases s.needs[a]? <;> simp
  · simp [hab]

theorem sourceAt_withPlan (a : Nat) (p : NeedPlanSupply) (s : EvalState) (b : Nat) :
    KatLang.NeedControl.Provenance.sourceAt (withPlan a p s).needs b =
      KatLang.NeedControl.Provenance.sourceAt s.needs b := by
  have h := withPlan_suspension a p s b
  unfold KatLang.NeedControl.Provenance.sourceAt
  revert h
  cases (withPlan a p s).needs[b]? <;> cases s.needs[b]? <;> intro h <;> simp at h
  · rfl
  · rename_i c d; rcases c with ⟨sc⟩; rcases d with ⟨sd⟩; simp only at h; subst h
    cases sc <;> rfl

theorem oblivious_source (a b : Nat) : Oblivious a (needWrittenSource? b) := by
  intro s p _
  rw [KatLang.NeedControl.Provenance.source_run, KatLang.NeedControl.Provenance.source_run,
    sourceAt_withPlan]

theorem oblivious_collectorSliceAt (a b : Nat) : Oblivious a (collectorSliceAt? b) := by
  intro s p _
  have h := withPlan_suspension a p s b
  simp only [collectorSliceAt?, bind_run, get_run]
  revert h
  cases hw : (withPlan a p s).needs[b]? <;> cases hs : s.needs[b]? <;> intro h <;> simp at h
  · rfl
  · rename_i c d; rcases c with ⟨sc⟩; rcases d with ⟨sd⟩; simp only at h; subst h
    cases sc <;> rfl

theorem oblivious_parameterNeedAddress (a : Nat) (name : Ident) (ctx : EvalCtx) :
    Oblivious a (parameterNeedAddress? name ctx) := by
  intro s p _
  have hcw := captured_withPlan name ctx a p s
  simp only [parameterNeedAddress?, bind_run, hcw]
  rcases h : (capturedParameterActivation? name ctx).runState s with ⟨o, t⟩
  obtain rfl := captured_state h
  cases o <;> rfl

theorem Oblivious.bind' {α β : Type} {a : Nat} {m : EvalM α} {f : α → EvalM β}
    (hm : Oblivious a m) (hd : Disciplined m) (hf : ∀ x, Oblivious a (f x)) : Oblivious a (m >>= f) := by
  intro s p hv
  rw [bind_run, bind_run, hm s p hv]
  have hv' := size_of_disciplined hd a s hv
  rcases hr : m.runState s with ⟨o, t⟩
  rw [hr] at hv'
  cases o with
  | error e => rfl
  | ok x => exact hf x t p hv'

theorem oblivious_slice (a : Nat) (operand : Expr) (ctx : EvalCtx) :
    Oblivious a (spreadCollectorSlice? operand ctx) := by
  unfold spreadCollectorSlice?
  cases operand
  case param name =>
    refine Oblivious.bind' (oblivious_parameterNeedAddress a name ctx)
      (disciplined_of_needs _ (fun s => by rw [parameter_address_readonly])) (fun found => ?_)
    cases found with
    | none => exact fun _ _ _ => rfl
    | some b => exact oblivious_collectorSliceAt a b
  all_goals exact fun _ _ _ => rfl

theorem ObliviousOn.mapM {α β : Type} {P : EvalState → Prop} {a : Nat} (f : α → EvalM β)
    (ho : ∀ x, ObliviousOn P a (f x)) (hk : ∀ x, Keeps P (f x)) (hd : ∀ x, Disciplined (f x))
    (xs : List α) : ObliviousOn P a (xs.mapM f) := by
  suffices h : ∀ (acc : List β), ObliviousOn P a (List.mapM.loop f xs acc) from h []
  induction xs with
  | nil => intro acc; exact oblivious_pure' P a _
  | cons x rest ih => intro acc; exact ObliviousOn.bind (ho x) (hk x) (hd x) (fun y => ih (y :: acc))

theorem Keeps.mapM {α β : Type} {P : EvalState → Prop} (f : α → EvalM β) (hk : ∀ x, Keeps P (f x))
    (xs : List α) : Keeps P (xs.mapM f) := by
  suffices h : ∀ (acc : List β), Keeps P (List.mapM.loop f xs acc) from h []
  induction xs with
  | nil => intro acc; exact keeps_pure P _
  | cons x rest ih => intro acc; exact Keeps.bind (hk x) (fun y => ih (y :: acc))

theorem slot_keeps (P : EvalState → Prop) (hpush : PushClosed P) (ev : NeedSupply.SpreadEval)
    (hkev : ∀ e c v, Keeps P (ev e c v)) (ctx : EvalCtx) (env : ValEnv) (e : Expr) :
    Keeps P (NeedSupply.slot ev ctx env e) := by
  have kalloc := keeps_allocate P hpush
  cases e with
  | sequenceSpread operand =>
    refine Keeps.bind (keeps_of_state P _ (fun s => spread_slice_readonly operand ctx s)) (fun known => ?_)
    cases known with
    | some slice =>
      exact Keeps.mapM _ (fun b => Keeps.bind
        (keeps_of_state P _ (fun s => by rw [KatLang.NeedControl.Provenance.source_run]))
        (fun _ => keeps_pure P _)) slice
    | none =>
      refine Keeps.bind (hkev _ _ _) (fun supplied => ?_)
      cases supplied with
      | items values => exact Keeps.mapM _ (fun v => Keeps.bind (kalloc _) (fun _ => keeps_pure P _)) values
      | cells cells => exact keeps_pure P _
  | _ => exact Keeps.bind (keeps_supply P hpush _ _ _) (fun _ => keeps_pure P _)

/-- **A supply slot is oblivious of a plan record** whenever its computed-spread capability is
    (and keeps `P` and is disciplined). -/
theorem slot_oblivious (P : EvalState → Prop) (a : Nat) (hpush : PushClosed P) (ev : NeedSupply.SpreadEval)
    (hdev : ∀ e c v, Disciplined (ev e c v)) (hkev : ∀ e c v, Keeps P (ev e c v))
    (hoev : ∀ e c v, ObliviousOn P a (ev e c v)) (ctx : EvalCtx) (env : ValEnv) (e : Expr) :
    ObliviousOn P a (NeedSupply.slot ev ctx env e) := by
  have kalloc := keeps_allocate P hpush
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
      refine ObliviousOn.bind (hoev _ _ _) (hkev _ _ _) (hdev _ _ _) (fun supplied => ?_)
      cases supplied with
      | items values =>
        exact ObliviousOn.mapM _
          (fun v => ObliviousOn.bind (ObliviousOn.of_oblivious P (oblivious_allocate a _)) (kalloc _)
            (disciplined_allocate _) (fun _ => oblivious_pure' P a _))
          (fun v => Keeps.bind (kalloc _) (fun _ => keeps_pure P _))
          (fun v => Disciplined.bind (disciplined_allocate _) (fun _ => disciplined_pure _)) values
      | cells cells => exact oblivious_pure' P a _
  | _ =>
    exact ObliviousOn.bind (ObliviousOn.of_oblivious P (oblivious_supply a _ _ _)) (keeps_supply P hpush _ _ _)
      (disciplined_supply _ _ _) (fun _ => oblivious_pure' P a _)

theorem form_on (P : EvalState → Prop) (a : Nat) (hpush : PushClosed P) (ev : NeedSupply.SpreadEval)
    (hdev : ∀ e c v, Disciplined (ev e c v)) (hkev : ∀ e c v, Keeps P (ev e c v))
    (hoev : ∀ e c v, ObliviousOn P a (ev e c v)) (ctx : EvalCtx) (env : ValEnv) (args : OutputBundle) :
    ObliviousOn P a (NeedSupply.form ev ctx env args) ∧ Keeps P (NeedSupply.form ev ctx env args) := by
  induction args with
  | nil => exact ⟨oblivious_pure' P a _, keeps_pure P _⟩
  | cons e rest ih =>
    have hs : ObliviousOn P a (NeedSupply.slot ev ctx env e) ∧ Keeps P (NeedSupply.slot ev ctx env e) :=
      ⟨slot_oblivious P a hpush ev hdev hkev hoev ctx env e, slot_keeps P hpush ev hkev ctx env e⟩
    have drest := disciplined_form ev hdev ctx env rest
    exact ⟨ObliviousOn.bind hs.1 hs.2 (disciplined_slot ev hdev ctx env e) (fun _ =>
        ObliviousOn.bind ih.1 ih.2 drest (fun _ => oblivious_pure' P a _)),
      Keeps.bind hs.2 (fun _ => Keeps.bind ih.2 (fun _ => keeps_pure P _))⟩

/-! ## The production instance -/

theorem calleeAlong_target (route : NeedPlan.Route) (a : Nat) (eff : NeedPlan.CallShape) (r : PlanRoute)
    (ha : r ≠ .algorithm) (hi : r ≠ .intrinsic) :
    NeedPlan.calleeAlong route a eff r = route.target eff.callee eff.caller := by
  cases r
  · rfl
  · exact absurd rfl ha
  · rfl
  · exact absurd rfl hi

/-- A sufficient, UNRESTRICTED call domain for the production instance: every argument to these
    operation families is included. A META-free domain needs a more selective contract. -/
def PlanCalls (Q : EvalCall → Prop) : Prop :=
  (∀ f c, Q (.resolveCalleeAlg f c)) ∧ (∀ g c, Q (.needPlanNormalizeCallee g c)) ∧
  (∀ e c v, Q (.evalSupplySpread e c v)) ∧ (∀ o g cells c v n, Q (.evalSuppliedCallCounted o g cells c v n))

/-- **Production fresh-plan simulation, relativized.** For every invariant `P` and call domain `Q`
    whose per-body obligations hold (`BodyKeeps`, `BodyObliviousOn`), which survives allocation and
    which contains the plan route's calls, one production execution of a FRESH call or extension plan
    from a state satisfying `P` is the ordinary call composition up to the plan's own record. -/
theorem production_fresh_plan_on (Q : EvalCall → Prop) (P : EvalState → Prop) (a : Nat)
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
          withPlan a .preparing ((ordinaryCall productionPlanRoute a shape r).runState s).2)) := by
  obtain ⟨qt, qn, qs, qd⟩ := hQ
  have hd := KatLang.EvaluatorDiscipline.productionDiscipline_holds
  have htarget := calleeAlong_target productionPlanRoute a (NeedPlan.effective shape r) r ha hi
  have dsp : ∀ e c v, Disciplined (productionPlanRoute.spread e c v) := hd.2.2.2.2.2.1
  have ksp : ∀ e c v, Keeps P (productionPlanRoute.spread e c v) :=
    fun e c v => keeps_production Q P hkB _ (qs e c v)
  have osp : ∀ e c v, ObliviousOn P a (productionPlanRoute.spread e c v) :=
    fun e c v => oblivious_production Q P a hkB hoB _ (qs e c v)
  have hform := form_on P a hpush productionPlanRoute.spread dsp ksp osp
  refine fresh_plan_is_ordinary_call_on P productionPlanRoute a shape r s cell hP hc hp hr hi dsp
    (by rw [htarget]; exact hd.2.1 _ _) hd.2.2.1
    (by rw [htarget]; exact keeps_production Q P hkB _ (qt _ _))
    (fun g c => keeps_production Q P hkB _ (qn g c))
    (hform _ _ _).2
    (by rw [htarget]; exact oblivious_production Q P a hkB hoB _ (qt _ _))
    (fun g c => oblivious_production Q P a hkB hoB _ (qn g c))
    (hform _ _ _).1
    (fun g cells => oblivious_production Q P a hkB hoB _ (qd _ _ _ _ _ _))

/-- **Production VALUE of a fresh plan, relativized.** Under the same obligations, with `P` holding
    once the completion shell has marked the cell `evaluating`, the public VALUE demand of a
    suspended, fresh call or extension plan has exactly the ordinary call's outcome, and its final
    state is the ordinary one up to the plan's own record, completed with that outcome. -/
theorem production_value_is_ordinary_on (Q : EvalCall → Prop) (P : EvalState → Prop) (a : Nat)
    (hkB : BodyKeeps Q P) (hoB : BodyObliviousOn Q P a) (hpush : PushClosed P) (hQ : PlanCalls Q)
    (s : EvalState) (cell : NeedCell) (e : Expr) (c : EvalCtx) (v : ValEnv)
    (shape : NeedPlan.CallShape) (r : PlanRoute)
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
  have hf := production_fresh_plan_on Q P a hkB hoB hpush hQ shape r (withState a .evaluating s)
    { cell with state := .evaluating } hP he hp hr hi ha
  rw [hv]
  dsimp only
  refine ⟨hf.1, _, rfl, ?_⟩
  rcases hf.2 with h | h | ⟨hfe, _⟩
  · exact Or.inl h
  · exact Or.inr h
  · rw [hfe] at hcomplete; cases hcomplete

/-! ## Step 1: the proof-local ordinary call IS the production ordinary call -/

def isAliasAlg : Algorithm → Bool
  | .alias .. => true
  | _ => false

theorem ok_of_bind {α β : Type} {m : EvalM α} {f : α → EvalM β} {s : EvalState} {y : β} {t : EvalState}
    (h : (m >>= f).runState s = (.ok y, t)) :
    ∃ x t1, m.runState s = (.ok x, t1) ∧ (f x).runState t1 = (.ok y, t) := by
  rw [bind_run] at h
  rcases hm : m.runState s with ⟨o, t1⟩
  rw [hm] at h
  cases o with
  | error e => cases h
  | ok x => exact ⟨x, t1, rfl, h⟩

def ChaseOk (rec : EvalRec) : Prop :=
  ∀ a ctx visited last s x l t,
    (rec (.resolveAliasChase true true a ctx visited last)).runState s = (.ok (.identity x l), t) →
      isAliasAlg x = false

theorem chase_body (rec : EvalRec) (hrec : ChaseOk rec) : ChaseOk (evalStep rec) := by
  intro a ctx visited last s x l t h
  change (EvalBody.resolveAliasChase rec true true a ctx visited last).runState s = _ at h
  unfold EvalBody.resolveAliasChase at h
  split at h
  · simp only [Bool.not_true, Bool.false_and, Bool.false_eq_true, ite_false] at h
    split at h
    · cases h
    · obtain ⟨b, t1, _, h⟩ := ok_of_bind h
      split at h
      · obtain ⟨step, t2, _, h⟩ := ok_of_bind h
        split at h
        · cases h
        · exact hrec _ _ _ _ _ _ _ _ h
      · obtain ⟨next, t2, _, h⟩ := ok_of_bind h
        exact hrec _ _ _ _ _ _ _ _ h
  · rename_i other hno
    simp only [pure_run] at h
    cases h
    revert hno
    cases a <;> intro hno <;> first | rfl | exact absurd rfl (hno _ _ _ _ _ _)

theorem chase_fuel : ∀ n, ChaseOk (evalFuel n) := by
  intro n
  induction n with
  | zero => intro a ctx visited last s x l t h; cases h
  | succ n ih =>
    intro a ctx visited last s x l t h
    rw [evalFuel_succ] at h
    by_cases hc : ((evalStep (evalFuel n) (.resolveAliasChase true true a ctx visited last)).runState s).1 =
        .error .fuelExhausted
    · rw [normalize_of_incomplete _ s hc] at h; cases h
    · rw [normalize_of_complete _ s hc] at h
      exact chase_body _ ih a ctx visited last s x l t h

theorem chase_production : ChaseOk evalUnbounded := by
  intro a ctx visited last s x l t h
  have hc : ProductionCompletes (evalUnbounded (.resolveAliasChase true true a ctx visited last)) s := by
    unfold ProductionCompletes; rw [h]; intro h'; cases h'
  obtain ⟨m, hr, _⟩ := (production_completes_iff _ s _).1 ⟨rfl, hc⟩
  rw [h] at hr
  exact chase_fuel m a ctx visited last s x l t hr

theorem aliasPropertyView_not_alias (g : Algorithm) : isAliasAlg g.aliasPropertyView = false := by
  cases g <;> rfl

/-- **Production alias resolution ends at a non-alias.** -/
theorem resolveAliasTarget_not_alias (g : Algorithm) (c : EvalCtx) (s t : EvalState) (g' : Algorithm)
    (h : (resolveAliasTarget g c).runState s = (.ok g', t)) : isAliasAlg g' = false := by
  have hc : ProductionCompletes (resolveAliasTarget g c) s := by
    unfold ProductionCompletes; rw [h]; intro h'; cases h'
  have hu := production_unfolds (.resolveAliasTarget g c) s hc
  change (evalUnbounded (.resolveAliasTarget g c)).runState s = _ at h
  rw [← hu] at h
  change (EvalBody.resolveAliasTarget evalUnbounded g c).runState s = _ at h
  unfold EvalBody.resolveAliasTarget at h
  obtain ⟨e, t1, he, h⟩ := ok_of_bind h
  cases e with
  | identity target last =>
    simp only [pure_run] at h; cases h
    exact chase_production g c [] none s _ _ _ he
  | valueView alias => simp only [pure_run] at h; cases h; exact aliasPropertyView_not_alias _
  | runtime alias => simp only [pure_run] at h; cases h; exact aliasPropertyView_not_alias _

theorem normalize_alias (g : Algorithm) (c : EvalCtx) (hg : isAliasAlg g = true) :
    NeedPlan.normalizeCallee g c = resolveAliasTarget g c := by
  have h := delegation_equation (.needPlanNormalizeCallee g c) (.resolveAliasTarget g c) (fun x => pure x)
    (fun rec => by
      cases g <;> simp [isAliasAlg] at hg
      exact (EvalM.bind_pure' _).symm)
    (fun _ _ => nofun)
  exact h.trans (EvalM.bind_pure' _)

theorem normalize_not_alias (g : Algorithm) (c : EvalCtx) (hg : isAliasAlg g = false) :
    NeedPlan.normalizeCallee g c = pure g := by
  apply EvalM.ext; intro s
  have h1 : (evalFuel 1 (.needPlanNormalizeCallee g c)).runState s = (.ok g, s) := by
    cases g <;> first | rfl | simp [isAliasAlg] at hg
  exact ((production_completes_iff _ s _).2
    ⟨1, h1, (evalFuel_completes_iff 1 _ s).2 (by rw [h1]; nofun)⟩).1

theorem resolved_body_not_alias (rec : EvalRec) (g : Algorithm) (args : OutputBundle) (c : EvalCtx) (v : ValEnv)
    (name : String) (origin : CalleeOrigin) (hg : isAliasAlg g = false) :
    EvalBody.evalResolvedCallCounted rec g args c v name origin =
      (do let cells ← NeedSupply.form rec.evalSupplySpread c v args
          rec.evalSuppliedCallCounted origin g cells c v name) := by
  cases g <;> first | rfl | simp [isAliasAlg] at hg

/-- **The resolved-callee phase of the ordinary call IS production.** On a completed run, the
    plan route's normalization, supply formation and dispatch compose to exactly the production
    `evalResolvedCallCounted` (whose alias arm resolves once, and production resolution never
    returns an alias, `resolveAliasTarget_not_alias`). -/
theorem resolved_call_is_production (callee : Algorithm) (args : OutputBundle) (c : EvalCtx) (v : ValEnv)
    (name : String) (origin : CalleeOrigin) (t : EvalState)
    (hc : ProductionCompletes (evalResolvedCallCounted callee args c v name origin) t) :
    (do let normal ← NeedPlan.normalizeCallee callee c
        let cells ← NeedSupply.form evalSupplySpread c v args
        evalSuppliedCallCounted origin normal cells c v name).runState t =
      (evalResolvedCallCounted callee args c v name origin).runState t := by
  have hu := production_unfolds (.evalResolvedCallCounted callee args c v name origin) t hc
  change _ = (evalUnbounded (.evalResolvedCallCounted callee args c v name origin)).runState t
  rw [← hu]
  change _ = (EvalBody.evalResolvedCallCounted evalUnbounded callee args c v name origin).runState t
  cases hg : isAliasAlg callee with
  | false =>
    rw [normalize_not_alias callee c hg, resolved_body_not_alias _ _ _ _ _ _ _ hg]
    simp only [bind_run, pure_run]
    rfl
  | true =>
    rw [normalize_alias callee c hg]
    have hbody : EvalBody.evalResolvedCallCounted evalUnbounded callee args c v name origin =
        (resolveAliasTarget callee c >>= fun target => evalResolvedCallCounted target args c v name origin) := by
      cases callee <;> simp [isAliasAlg] at hg; rfl
    rw [hbody, bind_run, bind_run]
    rcases hr : (resolveAliasTarget callee c).runState t with ⟨o, t1⟩
    cases o with
    | error e => rfl
    | ok g =>
      dsimp only
      have hg' := resolveAliasTarget_not_alias callee c t t1 g hr
      -- the inner production call completes, because the whole one does
      have hin : ProductionCompletes (evalResolvedCallCounted g args c v name origin) t1 := by
        have hwhole := hc
        unfold ProductionCompletes at hwhole ⊢
        change ((evalUnbounded (.evalResolvedCallCounted callee args c v name origin)).runState t).1 ≠ _ at hwhole
        rw [← hu] at hwhole
        change ((EvalBody.evalResolvedCallCounted evalUnbounded callee args c v name origin).runState t).1 ≠ _ at hwhole
        rw [hbody, bind_run, hr] at hwhole
        exact hwhole
      have hu2 := production_unfolds (.evalResolvedCallCounted g args c v name origin) t1 hin
      change _ = (evalUnbounded (.evalResolvedCallCounted g args c v name origin)).runState t1
      rw [← hu2]
      change _ = (EvalBody.evalResolvedCallCounted evalUnbounded g args c v name origin).runState t1
      rw [resolved_body_not_alias _ _ _ _ _ _ _ hg']
      rfl

/-- The production ORDINARY written call of an effective shape under the error context `msg`, its
    dispatch named `name`: the production callee law, then the production `evalResolvedCallCounted`
    with the written origin. -/
def writtenCallNamed (msg : String) (eff : NeedPlan.CallShape) (name : String) : EvalM CountedResult := do
  let callee ← withCtx msg (resolveCalleeAlg eff.callee eff.caller)
  let result ← withCtx msg (evalResolvedCallCounted callee eff.args eff.caller eff.values
    name (.written eff.callee eff.caller))
  pure (reCountValueBoundary result)

/-- The production ORDINARY written call of an effective shape under the error context `msg`:
    `evalCallCountedExpr`'s callee and resolved-dispatch phases, named by the written callee. -/
def writtenCall (msg : String) (eff : NeedPlan.CallShape) : EvalM CountedResult :=
  writtenCallNamed msg eff (openExprName eff.callee)

theorem withCtx_incomplete {α : Type} (msg : String) (m : EvalM α) (t : EvalState)
    (h : (m.runState t).1 = .error .fuelExhausted) :
    ((withCtx msg m).runState t).1 = .error .fuelExhausted := by
  rw [withCtx_run]
  rcases hm : m.runState t with ⟨o, t'⟩
  rw [hm] at h
  simp only at h
  subst h
  rfl

theorem dispatchNameIn_callable (needs : Array NeedCell) (a : Nat) (eff : NeedPlan.CallShape) (r : PlanRoute)
    (ha : r ≠ .algorithm) : NeedPlan.dispatchNameIn needs a eff r = NeedPlan.writtenDispatchName eff r := by
  cases r <;> first | rfl | exact absurd rfl ha

theorem dispatchOriginIn_callable (needs : Array NeedCell) (a : Nat) (eff : NeedPlan.CallShape) (r : PlanRoute)
    (ha : r ≠ .algorithm) : NeedPlan.dispatchOriginIn needs a eff r = .written eff.callee eff.caller := by
  cases r <;> first | rfl | exact absurd rfl ha

/-- Off the member call of a dot edge, a written route's dispatch name is its effective written
    callee (`writtenDispatchName`'s only other case is the member name, E-18 member-route correction). -/
theorem writtenDispatchName_callee (eff : NeedPlan.CallShape) (r : PlanRoute)
    (hm : r = .call → eff.form = .call) : NeedPlan.writtenDispatchName eff r = openExprName eff.callee := by
  cases r with
  | call => simp [NeedPlan.writtenDispatchName, hm rfl]
  | algorithm => rfl
  | extension => rfl
  | intrinsic => rfl

/-- **STEP 1: `ordinaryCall` IS the production written call, named by its route.** Along a call or
    extension route — the member call of a dot edge included — on every run where the production
    written call of the route's effective shape completes, the proof-local
    `ordinaryCall productionPlanRoute` is exactly it: the production callee resolution, then the
    production `evalResolvedCallCounted` over the effective bundle, under the plan's own written-form
    context, named by `NeedPlan.writtenDispatchName` (the member `N` for a member call `t.N(args)`,
    the effective written callee otherwise). -/
theorem ordinaryCall_is_written_call_named (a : Nat) (shape : NeedPlan.CallShape) (r : PlanRoute)
    (ha : r ≠ .algorithm) (hi : r ≠ .intrinsic) (s : EvalState)
    (hcomp : ((writtenCallNamed shape.ctxMsg (NeedPlan.effective shape r)
      (NeedPlan.writtenDispatchName (NeedPlan.effective shape r) r)).runState s).1 ≠ .error .fuelExhausted) :
    (ordinaryCall productionPlanRoute a shape r).runState s =
      (writtenCallNamed shape.ctxMsg (NeedPlan.effective shape r)
        (NeedPlan.writtenDispatchName (NeedPlan.effective shape r) r)).runState s := by
  unfold ordinaryCall writtenCallNamed at *
  dsimp only at hcomp ⊢
  rw [calleeAlong_target productionPlanRoute a _ r ha hi]
  simp only [bind_run, dispatchName_run, dispatchOrigin_run, dispatchNameIn_callable _ a _ r ha,
    dispatchOriginIn_callable _ a _ r ha] at hcomp ⊢
  generalize NeedPlan.writtenDispatchName (NeedPlan.effective shape r) r = name at hcomp ⊢
  generalize NeedPlan.effective shape r = eff at hcomp ⊢
  rcases h1 : (withCtx shape.ctxMsg (productionPlanRoute.target eff.callee eff.caller)).runState s with ⟨o1, t1⟩
  change (withCtx shape.ctxMsg (resolveCalleeAlg eff.callee eff.caller)).runState s = _ at h1
  rw [h1] at hcomp ⊢
  cases o1 with
  | error e => rfl
  | ok callee =>
    dsimp only at hcomp ⊢
    have hin : ProductionCompletes (evalResolvedCallCounted callee eff.args eff.caller eff.values
        name (.written eff.callee eff.caller)) t1 := by
      intro hinc
      apply hcomp
      have := withCtx_incomplete shape.ctxMsg _ t1 hinc
      revert this
      rcases (withCtx shape.ctxMsg (evalResolvedCallCounted callee eff.args eff.caller eff.values
        name (.written eff.callee eff.caller))).runState t1 with ⟨o, t2⟩
      intro h; simp only at h; subst h; rfl
    have he := resolved_call_is_production callee eff.args eff.caller eff.values
      name (.written eff.callee eff.caller) t1 hin
    have hw : (withCtx shape.ctxMsg (do
        let normal ← productionPlanRoute.normalize callee eff.caller
        let cells ← NeedSupply.form productionPlanRoute.spread eff.caller eff.values eff.args
        productionPlanRoute.dispatch (.written eff.callee eff.caller) normal cells eff.caller eff.values
          name)).runState t1 =
        (withCtx shape.ctxMsg (evalResolvedCallCounted callee eff.args eff.caller eff.values
          name (.written eff.callee eff.caller))).runState t1 := by
      have he' : (do
          let normal ← productionPlanRoute.normalize callee eff.caller
          let cells ← NeedSupply.form productionPlanRoute.spread eff.caller eff.values eff.args
          productionPlanRoute.dispatch (.written eff.callee eff.caller) normal cells eff.caller eff.values
            name).runState t1 =
          (evalResolvedCallCounted callee eff.args eff.caller eff.values
            name (.written eff.callee eff.caller)).runState t1 := he
      rw [withCtx_run, withCtx_run, he']
    rw [hw]

/-- **STEP 1: `ordinaryCall` IS the production written call.** Along a call or extension route
    whose dispatch is named by its effective written callee — every such route but the member call
    of a dot edge, which is named by its member (`hm`; E-18 member-route correction, November 11
    2026: `ordinaryCall_is_written_call_named` states that case too, and
    `PlanRouteBridge.member_bridge` identifies it with ordinary dot evaluation) —
    on every run where the production written call of the route's effective shape completes, the
    proof-local `ordinaryCall productionPlanRoute` is exactly it: the production callee resolution,
    then the production `evalResolvedCallCounted` over the effective bundle, under the plan's own
    written-form context. -/
theorem ordinaryCall_is_written_call (a : Nat) (shape : NeedPlan.CallShape) (r : PlanRoute)
    (ha : r ≠ .algorithm) (hi : r ≠ .intrinsic) (hm : r = .call → shape.form = .call) (s : EvalState)
    (hcomp : ((writtenCall shape.ctxMsg (NeedPlan.effective shape r)).runState s).1 ≠ .error .fuelExhausted) :
    (ordinaryCall productionPlanRoute a shape r).runState s =
      (writtenCall shape.ctxMsg (NeedPlan.effective shape r)).runState s := by
  have hname : NeedPlan.writtenDispatchName (NeedPlan.effective shape r) r =
      openExprName (NeedPlan.effective shape r).callee :=
    writtenDispatchName_callee _ r (fun h => by subst h; exact hm rfl)
  unfold writtenCall at hcomp ⊢
  rw [← hname] at hcomp ⊢
  exact ordinaryCall_is_written_call_named a shape r ha hi s hcomp

/-- For a written call `f(args)` whose callee is not an `X.Algorithm` link, the written call IS the
    production `evalCallCountedExpr` (re-counted at the value boundary), on every completed run. -/
theorem written_call_is_evalCallCountedExpr (f : Expr) (args : OutputBundle) (c : EvalCtx) (v : ValEnv)
    (hl : linkEdge? f = none) (s : EvalState)
    (hc : ProductionCompletes (evalCallCountedExpr f args c v) s) :
    (writtenCall (CtxMsg.call f) ⟨f, args, c, v, .call⟩).runState s =
      (reCountValueBoundary <$> evalCallCountedExpr f args c v).runState s := by
  have hu : (evalCallCountedExpr f args c v).runState s =
      (EvalBody.evalCallCountedExpr evalUnbounded f args c v).runState s :=
    (production_unfolds (.evalCallCountedExpr f args c v) s hc).symm
  rw [map_run, hu]
  unfold EvalBody.evalCallCountedExpr writtenCall writtenCallNamed
  rw [hl]
  simp only [bind_run, resolveCalleeAlg, evalResolvedCallCounted, EvalRec.resolveCalleeAlg,
    EvalRec.evalResolvedCallCounted]
  rcases (withCtx (CtxMsg.call f) (evalUnbounded (.resolveCalleeAlg f c))).runState s with ⟨o1, t1⟩
  cases o1 with
  | error e => rfl
  | ok callee =>
    dsimp only
    rcases (withCtx (CtxMsg.call f) (evalUnbounded (.evalResolvedCallCounted callee args c v (openExprName f)
      (.written f c)))).runState t1 with ⟨o2, t2⟩
    cases o2 <;> rfl


/-! ## Step 6: the production VALUE of a fresh written call, relativized -/

/-- **Production VALUE of a fresh written call is the ordinary written call (relativized).** For a
    suspended, fresh plan cell whose written call `f(args)` (callee no `X.Algorithm` link) has its
    `.call` route recorded, under the per-body obligations of `(Q, P)` and with `P` holding once the
    shell has marked the cell `evaluating`: the public VALUE demand has exactly the outcome of the
    production `evalCallCountedExpr` (re-counted) run from that evaluating state, and its final state
    is that run's final state up to the plan's own record, completed with that outcome. The premise
    `hcomp` is completion of the ordinary run only. -/
theorem production_value_is_evalCallCountedExpr_on (Q : EvalCall → Prop) (P : EvalState → Prop) (a : Nat)
    (hkB : BodyKeeps Q P) (hoB : BodyObliviousOn Q P a) (hpush : PushClosed P) (hQ : PlanCalls Q)
    (s : EvalState) (cell : NeedCell) (f : Expr) (args : OutputBundle) (c : EvalCtx) (v : ValEnv)
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
  have hf := production_fresh_plan_on Q P a hkB hoB hpush hQ ⟨f, args, c, v, .call⟩ .call
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
  have hv := production_value_is_ordinary_on Q P a hkB hoB hpush hQ s cell (.call f args) c v
    ⟨f, args, c, v, .call⟩ .call hc hsus hshape hs hp hr (by decide) (by decide) hP hcomplete
  have heq : (ordinaryCall productionPlanRoute a ⟨f, args, c, v, .call⟩ .call).runState (withState a .evaluating s) =
      (reCountValueBoundary <$> evalCallCountedExpr f args c v).runState (withState a .evaluating s) := by
    rw [ho]; exact hw
  rw [heq] at hv
  exact hv

/-- **What a counterexample refutes.** If, at some state `x` satisfying `P`, one production
    execution of a fresh call or extension plan has an outcome different from the ordinary call,
    then no allocation-closed `P` containing `x` satisfies the per-body obligations over a call
    domain containing the plan route's calls. (`PlanConservativityGuards` exhibits such an `x`,
    reachable from `EvalState.empty`, with the plan's cell `evaluating` and no stored reference
    to it.) -/
theorem obligations_fail_at (Q : EvalCall → Prop) (P : EvalState → Prop) (a : Nat)
    (hpush : PushClosed P) (hQ : PlanCalls Q)
    (shape : NeedPlan.CallShape) (r : PlanRoute) (x : EvalState) (cell : NeedCell) (hP : P x)
    (hc : x.needs[a]? = some cell) (hp : cell.plan = .unprepared)
    (hr : cell.route = some r) (hi : r ≠ .intrinsic) (ha : r ≠ .algorithm)
    (hdiff : ((NeedPlan.execute productionPlanRoute a shape).runState x).1 ≠
      ((ordinaryCall productionPlanRoute a shape r).runState x).1) :
    ¬ (BodyKeeps Q P ∧ BodyObliviousOn Q P a) := fun ⟨hk, ho⟩ =>
  hdiff (production_fresh_plan_on Q P a hk ho hpush hQ shape r x cell hP hc hp hr hi ha).1

end KatLang.PlanConservativity
