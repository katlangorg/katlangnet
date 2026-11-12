import KatLangArityLaws.MemberSettled
import KatLangArityLaws.RuntimeAlias

open KatLang KatLang.CallPlan KatLang.EvaluatorCore KatLang.PlanRouteBridge KatLang.MemberStability
open KatLang.MemberSettled KatLang.EvaluatorCacheLaws
open KatLang.MemoLinks (LinkHeapKept LinkKept)
open Lean.Order

/-!
# Identity navigation is RE-READABLE (ledger E-18, step 1, M1)

`MemberSettled` derives settled receiver navigation from the production probe for names, opened
names and a transparent reference to a named non-alias target, by UNFOLDING the alias chase of each
shape. This module proves the general fact those unfoldings are instances of:

> **A completed identity navigation that minted no runtime identity is RE-READ from every
> navigation extension of its exit state**: the same outcome — value OR failure — and no write.

It is one fuel induction over the production bodies of identity navigation (the alias chase, its
route decision, the structure chase, the receiver probe, the structural projection, the `.Algorithm`
route fact, a parameter's projection), so it covers what no shape-by-shape unfolding did:

* a RUNTIME-TARGET alias (`A = R.Algorithm`): its route decision, its recorded binding cell
  (`NavExt.aliasCell`) and that cell's completed CALLABLE (`LinkKept.callable`) are all read back;
* a transparent reference whose row is a MEMBER PATH (`A = Lib.Sub`) and a chain of ANY length
  (`A = B`, `B = C`, …);
* every alias KEY COMPARISON of the chase (`aliasChaseKey`, built with `reprStr`): the re-run makes
  the SAME comparisons on the same keys, so the theorem never has to decide one — the comparison
  the kernel cannot evaluate is not a premise of anything here;
* FAILURES, which the chase's route decision catches (`EvalBody.aliasStepIsRuntime`): a decision
  that failed fails again, because a completed failure is published and an IN-FLIGHT mark is kept
  (`LinkKept.projecting`) — re-entering the flight is `demandCycle` at both states.

## The calculus

`RRat s m` — the run of `m` from `s`, if complete, is a navigation extension and, if it minted
nothing, repeats from every navigation extension of its exit; `RR m` at every state. Closed under
`bind`, `evalAttempt` and the lookup combinators; every state-free computation is one
(`rr_of_sf`), so the whole lexical lookup is (`MemberSettled.sf_lookupLexicalPropertyRaw`).

## The three leaves

* `identifyRuntimeAlgorithm` MINTS: it advances the counter, so the no-mint premise excludes it.
  That premise is observable and necessary (`MemberStabilityGuards.memberOriginRemintsRuntimeIdentity`).
* `aliasBindingCellRecorded` records under a key its own lookup did not find; from the exit state on
  the record is read (`NavExt.aliasCell`).
* `projectNeedCallable a` runs ARBITRARY code inside its flight (a link's receiver VALUE, body
  entries, mints) and publishes; from the exit state on the sticky outcome is read
  (`projection_reread`). No premise on the flight: it is memoized, not re-run.

## The navigation core `navFuel`

Two reads of identity navigation are stable only on RECORDED data: a parameter read through a
captured activation (`capturedParameterActivation?` reads `lexicalActivations[id]?`, and an
unrecorded `id` falls back to the context's own tier — the answer changes once that index is
recorded: `OwnerContextStability.dangling_reference_breaks_stability`), and a projection of an
address outside the heap (an address fault now, a cell later). No production run from a reachable
state makes either read, but that is a WHOLE-RUN invariant of the evaluator which is not proved
(captured-activation validity is not in `AddressInvariant.Inv`); it cannot be a premise on the
navigation's entry state either, because the navigation's own flights extend the heap and the
activation array before the read.

`navFuel n` is production's total core RESTRICTED to the runs that make neither read: the same
bodies (`evalStep`), the same projection flights (`evalFuel`), with a call refused — incomplete —
exactly when it is not an identity-navigation call, when a parameter it transports has an
unrecorded captured activation or no cell, or when it projects an address outside the heap
(`navAdmits`). It is no second evaluator: `navFuel n ⊑ evalFuel n` (`navFuel_le`), so a completed
navigation run IS the production run (`NavRuns.production`); and it is executable, so an instance
establishes it by evaluation. `NavRuns c s r` is "the navigation core completes `c` from `s` with
`r`".

## Result

`navigation_reread`: for every call, a completed navigation run that minted nothing is the
production run, is a navigation extension, and is re-read — by production and by the navigation core
— from every navigation extension of its exit state.

NOT claimed: anything about a navigation that mints (`MemberStabilityGuards`); that every reachable
production navigation is a navigation-core run (the missing whole-run invariants above); anything
about C#.
-/

namespace KatLang.NavigationReread

/-! ## The calculus -/

/-- **Re-readable at `s`.** If the run of `m` from `s` completes, its exit state is a navigation
    extension of `s`, and — when it minted no runtime identity — the run repeats, outcome for
    outcome and without a write, from every navigation extension of that exit state. -/
def RRat {α : Type} (s : EvalState) (m : EvalM α) : Prop :=
  (m.runState s).1 ≠ .error .fuelExhausted →
    NavExt s (m.runState s).2 ∧
    ((m.runState s).2.nextRuntimeDeclaration = s.nextRuntimeDeclaration →
      ∀ u, NavExt (m.runState s).2 u → m.runState u = ((m.runState s).1, u))

/-- Re-readable from every state. -/
def RR {α : Type} (m : EvalM α) : Prop := ∀ s, RRat s m

theorem RRat.of_run {α : Type} {s t : EvalState} {m : EvalM α} {o : Except Error α}
    (h : m.runState s = (o, t)) (hext : NavExt s t)
    (hre : t.nextRuntimeDeclaration = s.nextRuntimeDeclaration → ∀ u, NavExt t u → m.runState u = (o, u)) :
    RRat s m := by
  intro _
  rw [h]
  exact ⟨hext, hre⟩

/-- A state-free computation is re-readable. -/
theorem rr_of_sf {α : Type} {m : EvalM α} (h : StateFree m) : RR m := by
  obtain ⟨o, ho⟩ := h
  intro s
  exact RRat.of_run (ho s) (NavExt.refl s) (fun _ u _ => ho u)

theorem rr_pure {α : Type} (a : α) : RR (pure a : EvalM α) := rr_of_sf (sf_pure a)
theorem rr_throw {α : Type} (e : Error) : RR (throw e : EvalM α) := rr_of_sf (sf_throw e)
theorem rr_evalError {α : Type} (e : Error) : RR (EvalM.error e : EvalM α) := rr_of_sf (sf_evalError e)
theorem rr_throwOf {α : Type} (e : Error) : RR (MonadExceptOf.throw e : EvalM α) := rr_of_sf (sf_throwOf e)
theorem rr_raw_throw {α : Type} (e : Error) : RR (⟨throw e⟩ : EvalM α) := rr_of_sf (sf_raw_throw e)
theorem rr_raw_pure {α : Type} (a : α) : RR (⟨pure a⟩ : EvalM α) := rr_of_sf (sf_raw_pure a)
theorem rr_lift {α : Type} (o : Except Error α) : RR (monadLift o : EvalM α) := rr_of_sf (sf_lift o)

/-- Sequencing, with the continuation taken at the state the first computation actually reached. -/
theorem RRat.bind {α β : Type} {s : EvalState} {m : EvalM α} {f : α → EvalM β}
    (hm : RRat s m) (hf : ∀ a t, m.runState s = (.ok a, t) → RRat t (f a)) : RRat s (m >>= f) := by
  intro hdone
  rcases hrun : m.runState s with ⟨o, t⟩
  cases o with
  | error e =>
    have hb : (m >>= f).runState s = (.error e, t) := by rw [bind_run, hrun]
    rw [hb] at hdone
    have hne : e ≠ .fuelExhausted := fun he => hdone (by rw [he])
    have hm' := hm (by rw [hrun]; exact fun h => hne (Except.error.inj h))
    rw [hrun] at hm'
    rw [hb]
    refine ⟨hm'.1, fun hc u hu => ?_⟩
    rw [bind_run, hm'.2 hc u hu]
  | ok a =>
    have hb : (m >>= f).runState s = (f a).runState t := by rw [bind_run, hrun]
    rw [hb] at hdone
    have hm' := hm (by rw [hrun]; nofun)
    rw [hrun] at hm'
    have hf' := hf a t hrun hdone
    rw [hb]
    refine ⟨hm'.1.trans hf'.1, fun hc u hu => ?_⟩
    have h1 := hm'.1.runtime_mono
    have h2 := hf'.1.runtime_mono
    have hct : t.nextRuntimeDeclaration = s.nextRuntimeDeclaration := by
      simp only at h1 hc; omega
    have hcf : ((f a).runState t).2.nextRuntimeDeclaration = t.nextRuntimeDeclaration := by
      simp only at h1 hc; omega
    rw [bind_run, hm'.2 hct u (hf'.1.trans hu)]
    exact hf'.2 hcf u hu

theorem RR.bind {α β : Type} {m : EvalM α} {f : α → EvalM β} (hm : RR m) (hf : ∀ a, RR (f a)) :
    RR (m >>= f) := fun s => RRat.bind (hm s) (fun a t _ => hf a t)

theorem rr_bind {α β : Type} {m : EvalM α} {f : α → EvalM β} (hm : RR m) (hf : ∀ a, RR (f a)) :
    RR (m >>= f) := RR.bind hm hf

theorem rr_map {α β : Type} (f : α → β) {m : EvalM α} (hm : RR m) : RR (f <$> m) :=
  rr_bind (f := Function.comp pure f) hm (fun x => rr_pure (f x))

/-- A caught failure is re-read as that failure: `evalAttempt` keeps the calculus closed. -/
theorem RRat.attempt {α : Type} {s : EvalState} {m : EvalM α} (hm : RRat s m) : RRat s (evalAttempt m) := by
  intro hdone
  rcases hrun : m.runState s with ⟨o, t⟩
  cases hinc : o.isIncomplete with
  | true =>
    have ho := Except.isIncomplete_eq_true hinc
    subst ho
    rw [evalAttempt_runState_of_incomplete m s t hrun] at hdone
    exact absurd rfl hdone
  | false =>
    have ha := evalAttempt_runState_of_complete m s t o hrun hinc
    have hne : o ≠ .error .fuelExhausted := by
      intro h; subst h; cases hinc
    have hm' := hm (by rw [hrun]; exact hne)
    rw [hrun] at hm'
    rw [ha]
    exact ⟨hm'.1, fun hc u hu => evalAttempt_runState_of_complete m u u o (hm'.2 hc u hu) hinc⟩

theorem rr_attempt {α : Type} {m : EvalM α} (hm : RR m) : RR (evalAttempt m) := fun s => (hm s).attempt

theorem rr_withCtx {α : Type} (c : String) {m : EvalM α} (hm : RR m) : RR (withCtx c m) := by
  unfold withCtx
  refine rr_bind (rr_attempt hm) (fun r => ?_)
  cases r with
  | ok x => exact rr_pure x
  | error e => exact rr_evalError _

/-! ## The leaves -/

/-- The counter's one writer advances it: under the no-mint premise there is nothing to re-read. -/
theorem rr_identifyRuntime (a : Algorithm) : RR (identifyRuntimeAlgorithm a) := by
  intro s _
  refine ⟨⟨MemoExt.refl _ |>.trans ⟨HeapKept.refl _, LinkHeapKept.refl _, .of_eq rfl⟩,
    ⟨fun _ _ h => h, Nat.le_succ _⟩⟩, fun hc => ?_⟩
  exact absurd hc (Nat.succ_ne_self _)

/-- THE ALIAS TABLE'S ONE WRITER, re-read: a non-parameter row's binding cell is read from the record
    its first use made (`NavExt.aliasCell`). -/
theorem rr_aliasBindingCell (wired : Algorithm) (target : Expr) (ctx : EvalCtx) (hnp : ∀ n, target ≠ .param n) :
    RR (aliasBindingCell wired target ctx) := by
  intro s
  cases hl : lookupAssoc (aliasCellKey wired) s.aliasCells with
  | some a0 =>
    exact RRat.of_run (KatLang.RuntimeAliasLaws.aliasBindingCell_recorded wired target ctx s a0 hnp hl)
      (NavExt.refl s)
      (fun _ u hu => KatLang.RuntimeAliasLaws.aliasBindingCell_recorded wired target ctx u a0 hnp (hu.aliasCell hl))
  | none =>
    obtain ⟨c, u, _, hneeds, _, hrun⟩ :=
      KatLang.RuntimeAliasLaws.aliasBindingCell_establishes wired target ctx s hnp hl
    have heq := KatLang.RuntimeAliasLaws.aliasBindingCell_nonparameter wired target ctx hnp
    have hact := pres_aliasBindingCellRecorded (R := KatLang.OwnerContextStability.ActivationPrefix) wired target ctx s
    have hkept := pres_aliasBindingCellRecorded (R := NavKept) wired target ctx s
    rw [← heq, hrun] at hact hkept
    refine RRat.of_run hrun ⟨⟨?_, ?_, hact⟩, hkept⟩ (fun _ v hv => ?_)
    · show HeapKept s.needs (u.needs.push _)
      rw [hneeds]; exact HeapKept.push _ _
    · show LinkHeapKept s.needs (u.needs.push _)
      rw [hneeds]; exact LinkHeapKept.push _ _
    · exact KatLang.RuntimeAliasLaws.aliasBindingCell_recorded wired target ctx v _ hnp
        (hv.aliasCell (by simp [lookupAssoc]))

/-! ### The memoized projection -/

/-- What a completed production projection leaves at its cell: the entry mark was in flight and the
    re-entry failed without a write, or the cell now holds the run's own outcome as its completed
    CALLABLE — whether this run projected it or found it projected. -/
theorem projection_published (a : Nat) (s : EvalState) (cell : NeedCell) (hcell : s.needs[a]? = some cell)
    (hdone : ProductionCompletes (projectNeedCallable a) s) :
    (cell.callable = .projecting ∧ (projectNeedCallable a).runState s = (.error .demandCycle, s)) ∨
    ∃ c', ((projectNeedCallable a).runState s).2.needs[a]? = some c' ∧
      c'.callable = .projected ((projectNeedCallable a).runState s).1 := by
  have hu := production_unfolds (.projectNeedCallable a) s hdone
  have hstep : (NeedProjection.step (NeedProjection.suspended (EvalRec.projectNeedWrittenAt evalUnbounded a)) a).runState s =
      (projectNeedCallable a).runState s := hu
  cases hcal : cell.callable with
  | projected outcome =>
    right
    rw [← hstep, KatLang.NeedControl.Projection.projected_sticky _ a s cell outcome hcell hcal]
    exact ⟨cell, hcell, hcal⟩
  | projecting =>
    left
    refine ⟨rfl, ?_⟩
    rw [← hstep, KatLang.NeedControl.Projection.projecting_reentry_cycle _ a s cell hcell hcal]
  | unprojected =>
    right
    obtain ⟨c', hc', -⟩ := KatLang.EvaluatorDiscipline.evalUnbounded_disciplined (.projectNeedCallable a) s a cell hcell
    have hc'' : ((projectNeedCallable a).runState s).2.needs[a]? = some c' := hc'
    rcases hrun : (NeedProjection.suspended (EvalRec.projectNeedWrittenAt evalUnbounded a) cell.suspension).runState
        (KatLang.NeedControl.Projection.setCallable a .projecting s) with ⟨outcome, t₀⟩
    cases hinc : outcome.isIncomplete with
    | true =>
      have hoe := Except.isIncomplete_eq_true hinc
      subst hoe
      have hbad : (NeedProjection.step (NeedProjection.suspended (EvalRec.projectNeedWrittenAt evalUnbounded a)) a).runState s =
          (.error .fuelExhausted, t₀) := by
        simp only [NeedProjection.step, bind_run, get_run, hcell, hcal, EvalM.modify_runState]
        simp only [KatLang.NeedControl.Projection.setCallable] at hrun
        rw [evalAttempt_runState_of_incomplete _ _ _ hrun]
      rw [hstep] at hbad
      exact absurd (by rw [hbad]) hdone
    | false =>
      have hpub := KatLang.NeedControl.Projection.unprojected_publishes _ a s t₀ cell outcome hcell hcal hrun hinc
      rw [hstep] at hpub
      rw [hpub] at hc'' ⊢
      refine ⟨c', hc'', ?_⟩
      simp only [KatLang.NeedControl.Projection.setCallable, Array.getElem?_modify, ite_true] at hc''
      cases hcur : t₀.needs[a]? with
      | none => rw [hcur] at hc''; cases hc''
      | some current =>
        rw [hcur] at hc''
        simp only [Option.map_some] at hc''
        injection hc'' with hc''
        rw [← hc'']

/-- **A completed projection is re-read by the BODY ITSELF, whatever the evaluator answer**: from
    every navigation extension of the exit state the projection shell returns the same outcome —
    the published value or failure, or `demandCycle` for a mark still in flight
    (`LinkKept.projecting`) — and never consults its callback. -/
theorem projection_reread (a : Nat) (s : EvalState) (hvalid : s.needs[a]?.isSome = true)
    (hdone : ProductionCompletes (projectNeedCallable a) s) (u : EvalState)
    (hu : NavExt ((projectNeedCallable a).runState s).2 u) (project : NeedSuspension → EvalM (Option Algorithm)) :
    (NeedProjection.step project a).runState u = (((projectNeedCallable a).runState s).1, u) ∧
      u.needs[a]?.isSome = true := by
  cases hcell : s.needs[a]? with
  | none => rw [hcell] at hvalid; cases hvalid
  | some cell =>
    rcases projection_published a s cell hcell hdone with ⟨hflight, hrun⟩ | ⟨c', hc', hpub⟩
    · rw [hrun] at hu ⊢
      obtain ⟨cell', hcell', hk⟩ := hu.memo.links a cell hcell
      exact ⟨KatLang.NeedControl.Projection.projecting_reentry_cycle project a u cell' hcell' (hk.projecting hflight),
        by rw [hcell']; rfl⟩
    · obtain ⟨cell', hcell', hk⟩ := hu.memo.links a c' hc'
      exact ⟨KatLang.NeedControl.Projection.projected_sticky project a u cell' _ hcell' (hk.callable _ hpub),
        by rw [hcell']; rfl⟩

/-! ### A parameter read -/

/-- **Anchored**: the parameter's captured activation, if it has one, is RECORDED at `s`. -/
def anchored (x : Ident) (ctx : EvalCtx) (s : EvalState) : Bool :=
  match capturedId? x ctx with
  | some id => decide (id < s.lexicalActivations.size)
  | none => true

theorem anchored_spec {x : Ident} {ctx : EvalCtx} {s : EvalState} (h : anchored x ctx s = true) :
    ∀ id, capturedId? x ctx = some id → id < s.lexicalActivations.size := by
  intro id hid
  unfold anchored at h
  rw [hid] at h
  exact of_decide_eq_true h

theorem anchored_mono {x : Ident} {ctx : EvalCtx} {s u : EvalState}
    (hp : KatLang.OwnerContextStability.ActivationPrefix s u) (h : anchored x ctx s = true) :
    anchored x ctx u = true := by
  unfold anchored at h ⊢
  cases hid : capturedId? x ctx with
  | none => rfl
  | some id =>
    rw [hid] at h
    exact decide_eq_true (Nat.lt_of_lt_of_le (of_decide_eq_true h) hp.size_le)

/-- An anchored parameter's projection is re-read: the supplied cell is found through the same
    recorded activation, and its projection is re-read. -/
theorem rrat_projectParameterWith (project : Nat → EvalM (Option Algorithm)) (hp : ∀ a, RR (project a))
    (x : Ident) (ctx : EvalCtx) (s : EvalState) (hanch : anchored x ctx s = true) :
    RRat s (projectParameterWith project x ctx) := by
  have hact := anchored_spec hanch
  intro hdone
  rw [projectParameterWith_run] at hdone ⊢
  cases haddr : parameterAddressIn s.lexicalActivations x ctx with
  | none =>
    refine ⟨NavExt.refl s, fun _ u hu => ?_⟩
    rw [projectParameterWith_run, parameterAddressIn_stable x ctx s u hu.memo.activations hact, haddr]
  | some address =>
    rw [haddr] at hdone
    have h := hp address s hdone
    refine ⟨h.1, fun hc u hu => ?_⟩
    rw [projectParameterWith_run,
      parameterAddressIn_stable x ctx s u (h.1.memo.activations.trans hu.memo.activations) hact, haddr]
    exact h.2 hc u hu

/-! ## The calculus over an upward-closed domain

Some leaves are re-readable only where a fact holds that every navigation extension keeps (an
anchored parameter). `RRon P m`: re-readable from every state of `P`. -/

/-- Re-readable from every state of `P`. -/
def RRon {α : Type} (P : EvalState → Prop) (m : EvalM α) : Prop := ∀ s, P s → RRat s m

theorem rron_of_rr {α : Type} {P : EvalState → Prop} {m : EvalM α} (h : RR m) : RRon P m := fun s _ => h s

theorem rr_of_rron {α : Type} {m : EvalM α} (h : RRon (fun _ => True) m) : RR m := fun s => h s trivial

/-- The exit state of a completed run from `s` is a navigation extension of `s`. -/
theorem RRat.ext_of_ok {α : Type} {s t : EvalState} {m : EvalM α} {a : α} (hm : RRat s m)
    (hrun : m.runState s = (.ok a, t)) : NavExt s t := by
  have h := hm (by rw [hrun]; nofun)
  rw [hrun] at h
  exact h.1

section Domain
variable {P : EvalState → Prop}

theorem rron_bind (hP : ∀ s t, NavExt s t → P s → P t) {α β : Type} {m : EvalM α} {f : α → EvalM β}
    (hm : RRon P m) (hf : ∀ a, RRon P (f a)) : RRon P (m >>= f) :=
  fun s hs => RRat.bind (hm s hs) (fun a t hrun => hf a t (hP s t ((hm s hs).ext_of_ok hrun) hs))

theorem rron_map (hP : ∀ s t, NavExt s t → P s → P t) {α β : Type} (f : α → β) {m : EvalM α}
    (hm : RRon P m) : RRon P (f <$> m) :=
  rron_bind hP (f := Function.comp pure f) hm (fun x => rron_of_rr (rr_pure (f x)))

theorem rron_attempt {α : Type} {m : EvalM α} (hm : RRon P m) : RRon P (evalAttempt m) :=
  fun s hs => (hm s hs).attempt

theorem rron_withCtx (hP : ∀ s t, NavExt s t → P s → P t) {α : Type} (c : String) {m : EvalM α}
    (hm : RRon P m) : RRon P (withCtx c m) := by
  unfold withCtx
  refine rron_bind hP (rron_attempt hm) (fun r => ?_)
  cases r with
  | ok x => exact rron_of_rr (rr_pure x)
  | error e => exact rron_of_rr (rr_evalError _)

theorem rron_pure {α : Type} (a : α) : RRon P (pure a : EvalM α) := rron_of_rr (rr_pure a)
theorem rron_throw {α : Type} (e : Error) : RRon P (throw e : EvalM α) := rron_of_rr (rr_throw e)
theorem rron_evalError {α : Type} (e : Error) : RRon P (EvalM.error e : EvalM α) := rron_of_rr (rr_evalError e)
theorem rron_throwOf {α : Type} (e : Error) : RRon P (MonadExceptOf.throw e : EvalM α) := rron_of_rr (rr_throwOf e)
theorem rron_raw_throw {α : Type} (e : Error) : RRon P (⟨throw e⟩ : EvalM α) := rron_of_rr (rr_raw_throw e)
theorem rron_raw_pure {α : Type} (a : α) : RRon P (⟨pure a⟩ : EvalM α) := rron_of_rr (rr_raw_pure a)
theorem rron_lift {α : Type} (o : Except Error α) : RRon P (monadLift o : EvalM α) := rron_of_rr (rr_lift o)
theorem rron_identifyRuntime (a : Algorithm) : RRon P (identifyRuntimeAlgorithm a) :=
  rron_of_rr (rr_identifyRuntime a)
theorem rron_lookup (a : Algorithm) (n : Ident) (c : EvalCtx) : RRon P (lookupLexicalPropertyRaw a n c) :=
  rron_of_rr (rr_of_sf (sf_lookupLexicalPropertyRaw a n c))

end Domain

open Lean Meta Elab Tactic in
/-- The computation of an `RRon` goal. -/
def rrComputation? (ty : Lean.Expr) : Option Lean.Expr :=
  if ty.isAppOf ``KatLang.NavigationReread.RRon then some ty.appArg! else none

open Lean Meta Elab Tactic in
elab "rr_unfold_head" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let ty ← instantiateMVars (← goal.getType)
    let some m := rrComputation? ty | throwError "rr_unfold_head: not a re-read goal"
    let m := m.headBeta
    let some c := m.getAppFn.constName? | throwError "rr_unfold_head: no head constant"
    if c ∈ [``Bind.bind, ``Pure.pure, ``Functor.map, ``KatLang.evalAttempt, ``ForIn.forIn,
        ``MonadState.get, ``MonadStateOf.get, ``MonadState.set, ``MonadStateOf.set,
        ``MonadState.modifyGet, ``modify, ``get, ``set, ``List.forM, ``List.mapM, ``List.foldlM,
        ``KatLang.withCtx, ``throw, ``MonadExcept.throw, ``MonadExceptOf.throw, ``throwThe,
        ``KatLang.EvalM.error, ``KatLang.aliasBindingCell, ``KatLang.identifyRuntimeAlgorithm,
        ``KatLang.lookupLexicalPropertyRaw, ``KatLang.aliasStepNavigateWith,
        ``KatLang.aliasRouteIsIntrinsicWith, ``KatLang.resolveAliasStepWith,
        ``KatLang.staticPathSelectWith] then
      throwError "rr_unfold_head: combinator"
    let g' ← Lean.Meta.unfoldTarget goal c
    let ty' ← instantiateMVars (← g'.getType)
    if (ty'.find? (fun e => e.isConstOf c)).isSome then
      throwError "rr_unfold_head: recursive definition"
    replaceMainGoal [g']

open Lean Meta Elab Tactic in
elab "rr_zeta" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let ty ← instantiateMVars (← goal.getType)
    let some m := rrComputation? ty | throwError "rr_zeta: not a re-read goal"
    let mut e := m
    let mut n := 0
    for _ in [0:10000] do
      match e with
      | Lean.Expr.letE _ _ v b _ => e := b.instantiate1 v; n := n + 1
      | Lean.Expr.mdata _ e' => e := e'
      | _ => break
    if n == 0 then throwError "rr_zeta: no local definition"
    replaceMainGoal [← goal.replaceTargetDefEq (ty.updateApp! ty.appFn! e)]

open Lean Meta Elab Tactic in
elab "rr_whnf_core" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let ty ← instantiateMVars (← goal.getType)
    let some m := rrComputation? ty | throwError "rr_whnf_core: not a re-read goal"
    let m' ← whnfCore m
    if m' == m then throwError "rr_whnf_core: no progress"
    replaceMainGoal [← goal.replaceTargetDefEq (ty.updateApp! ty.appFn! m')]

set_option hygiene false in
/-- Syntax-directed re-readability over the domain `P` (its upward closure is the local `hP`): the
    combinator lemmas, case splits and unfolding. No rule for a read or a write of the state: every
    such leaf must be a hypothesis. -/
macro "rr_tac" : tactic => `(tactic| without_info_trees ((try pres_unfold_rec) <;> (try dsimp only at *) <;> repeat' (first
  | pres_hyp
  | pres_absurd
  | (with_reducible apply rron_withCtx hP)
  | (with_reducible apply rron_attempt)
  | (with_reducible apply rron_map hP)
  | (with_reducible apply rron_bind hP)
  | (with_reducible apply rron_pure)
  | (with_reducible apply rron_throw)
  | (with_reducible apply rron_throwOf)
  | (with_reducible apply rron_raw_throw)
  | (with_reducible apply rron_raw_pure)
  | (with_reducible apply rron_evalError)
  | (with_reducible apply rron_lift)
  | (with_reducible apply rron_identifyRuntime)
  | (with_reducible apply rron_lookup)
  | split
  | pres_intro
  | rr_zeta
  | rr_whnf_core
  | rr_unfold_head)))

/-! ## The navigation helpers -/

section Helpers
variable {P : EvalState → Prop} (hP : ∀ s t, NavExt s t → P s → P t)
include hP

theorem rron_aliasStepNavigateWith (structureOf : Algorithm → EvalCtx → EvalM (Option Algorithm))
    (h : ∀ a c, RRon P (structureOf a c)) (stepCtx : EvalCtx) (notStatic : Error) (steps : List Ident) :
    ∀ (value : Algorithm) (last : Option ResolvedProperty) (receiverName : String),
      RRon P (aliasStepNavigateWith structureOf stepCtx notStatic value last receiverName steps) := by
  induction steps with
  | nil => intro value last receiverName; unfold aliasStepNavigateWith; rr_tac
  | cons member rest ih => intro value last receiverName; unfold aliasStepNavigateWith; rr_tac

theorem rron_staticPathSelectWith (structureOf : Algorithm → EvalCtx → EvalM (Option Algorithm))
    (h : ∀ a c, RRon P (structureOf a c)) (owner : Algorithm) (target : Expr) (stepCtx : EvalCtx) :
    RRon P (staticPathSelectWith structureOf owner target stepCtx) := by
  have hn := fun stepCtx notStatic steps value last receiverName =>
    rron_aliasStepNavigateWith hP structureOf h stepCtx notStatic steps value last receiverName
  unfold staticPathSelectWith; rr_tac

theorem rron_resolveAliasStepWith (structureOf : Algorithm → EvalCtx → EvalM (Option Algorithm))
    (h : ∀ a c, RRon P (structureOf a c)) (step : Algorithm) (target : Expr) (ctx : EvalCtx) :
    RRon P (resolveAliasStepWith structureOf step target ctx) :=
  rron_staticPathSelectWith hP structureOf h step target (ctx.push step)

theorem rron_aliasRouteIsIntrinsicWith (structureOf : Algorithm → EvalCtx → EvalM (Option Algorithm))
    (h : ∀ a c, RRon P (structureOf a c)) (receiver : Expr) (ctx : EvalCtx) :
    RRon P (aliasRouteIsIntrinsicWith structureOf receiver ctx) := by
  have hn := fun stepCtx notStatic steps value last receiverName =>
    rron_aliasStepNavigateWith hP structureOf h stepCtx notStatic steps value last receiverName
  unfold aliasRouteIsIntrinsicWith; rr_tac

end Helpers

set_option hygiene false in
/-- `rr_tac` with the navigation helpers (their structure reader left as a goal). -/
macro "rr_nav" : tactic => `(tactic| without_info_trees ((try pres_unfold_rec) <;> (try dsimp only at *) <;> repeat' (first
  | pres_hyp
  | pres_absurd
  | (with_reducible apply rron_aliasRouteIsIntrinsicWith hP)
  | (with_reducible apply rron_resolveAliasStepWith hP)
  | (with_reducible apply rron_withCtx hP)
  | (with_reducible apply rron_attempt)
  | (with_reducible apply rron_map hP)
  | (with_reducible apply rron_bind hP)
  | (with_reducible apply rron_pure)
  | (with_reducible apply rron_throw)
  | (with_reducible apply rron_throwOf)
  | (with_reducible apply rron_raw_throw)
  | (with_reducible apply rron_raw_pure)
  | (with_reducible apply rron_evalError)
  | (with_reducible apply rron_lift)
  | (with_reducible apply rron_identifyRuntime)
  | (with_reducible apply rron_lookup)
  | split
  | pres_intro
  | rr_zeta
  | rr_whnf_core
  | rr_unfold_head)))

/-! ## The bodies of identity navigation

Each production body of identity navigation is re-readable whenever its recursive answer is — the
per-body step of the fuel induction. The two bodies with a parameter read take that read's leaf as
a premise. -/

section Bodies
variable {P : EvalState → Prop} (hP : ∀ s t, NavExt s t → P s → P t)
variable (rec : EvalRec) (hrec : ∀ c, RRon P (rec c))
include hP hrec

theorem rron_body_aliasStepIsRuntime (step : Algorithm) (target : Expr) (ctx : EvalCtx) (visited : List String) :
    RRon P (EvalBody.aliasStepIsRuntime rec step target ctx visited) := by
  unfold EvalBody.aliasStepIsRuntime; rr_nav

/-- THE ALIAS CHASE over an alias: its route decision, its runtime step (the binding cell, a
    premise; its projection) or its static step, and the chase of what it selects. -/
theorem rron_body_chase_alias (fc pr : Bool) (parent : Option ScopeCtx) (opens : List Expr) (props : List PropDef)
    (target : Expr) (id : Option PropertyIdentity) (reference : Bool) (ctx : EvalCtx) (visited : List String)
    (last : Option (Algorithm × PropDef))
    (hcell : RRon P (aliasBindingCell (.alias parent opens props target id reference) target ctx)) :
    RRon P (EvalBody.resolveAliasChase rec fc pr (.alias parent opens props target id reference) ctx visited last) := by
  unfold EvalBody.resolveAliasChase; rr_nav

omit hP hrec in
theorem rron_body_chase_other (fc pr : Bool) (a : Algorithm) (ctx : EvalCtx) (visited : List String)
    (last : Option (Algorithm × PropDef)) (ha : KatLang.PlanConservativity.isAliasAlg a = false) :
    RRon P (EvalBody.resolveAliasChase rec fc pr a ctx visited last) := by
  cases a with
  | «alias» p op pr' t id reference => simp [KatLang.PlanConservativity.isAliasAlg] at ha
  | mk p pp op pr' out id => exact rron_pure _
  | builtin b => exact rron_pure _
  | conditional p op bs id => exact rron_pure _

theorem rron_body_resolveAliasStructure (a : Algorithm) (ctx : EvalCtx) :
    RRon P (EvalBody.resolveAliasStructure rec a ctx) := by
  unfold EvalBody.resolveAliasStructure; rr_nav

theorem rron_body_resolveDotReceiver? (e : Expr) (ctx : EvalCtx) :
    RRon P (EvalBody.resolveDotReceiver? rec e ctx) := by
  unfold EvalBody.resolveDotReceiver?; rr_nav

theorem rron_body_projectNeedStructuralMember (e : Expr) (ctx : EvalCtx) :
    RRon P (EvalBody.projectNeedStructuralMember rec e ctx) := by
  unfold EvalBody.projectNeedStructuralMember; rr_nav

theorem rron_body_algorithmIntrinsicRoute (receiver : Expr) (ctx : EvalCtx) :
    RRon P (EvalBody.algorithmIntrinsicRoute rec receiver ctx) := by
  unfold EvalBody.algorithmIntrinsicRoute; rr_nav

end Bodies

/-! ## The navigation core -/

/-- The receiver shapes `resolveAlg` is asked for by identity navigation: a dot result, a capture or
    a written value head (it mints, or refuses). A name, a block or a parameter never reaches it
    from the receiver probe; the navigation core does not answer them. -/
def resolveAlgAdmits : Expr → Bool
  | .resolve _ => false
  | .algorithmExpr _ => false
  | .param _ => false
  | _ => true

/-- A chase step of an alias whose row is a PARAMETER transports that parameter's own cell: the read
    is admitted where the parameter is anchored and has a cell. Every other chase is admitted. -/
def paramRowAdmits (a : Algorithm) (ctx : EvalCtx) (s : EvalState) : Bool :=
  match a with
  | .alias _ _ _ (.param y) _ _ =>
      anchored y (ctx.push a) s && (parameterAddressIn s.lexicalActivations y (ctx.push a)).isSome
  | _ => true

/-- **What the navigation core answers, and where.** The calls of identity navigation; a parameter
    read only where it is anchored; a projection only of an address inside the heap. -/
def navAdmits : EvalCall → EvalState → Bool
  | .aliasStepIsRuntime _ _ _ _, _ => true
  | .resolveAliasChase _ _ a ctx _ _, s => paramRowAdmits a ctx s
  | .resolveAliasStructure _ _, _ => true
  | .resolveDotReceiver? _ _, _ => true
  | .projectNeedStructuralMember _ _, _ => true
  | .algorithmIntrinsicRoute _ _, _ => true
  | .projectParameterCallable x ctx, s => anchored x ctx s
  | .projectNeedCallable a, s => s.needs[a]?.isSome
  | .resolveAlg e _, _ => resolveAlgAdmits e
  | _, _ => false

/-- A CALLABLE projection: the one call the navigation core hands to production's core whole. -/
def isProjection : EvalCall → Bool
  | .projectNeedCallable _ => true
  | _ => false

/-- **THE NAVIGATION CORE.** Production's total core restricted to identity navigation over recorded
    data: the same bodies over itself, a CALLABLE projection run by production's core (its flight is
    arbitrary production code), and a call that is not admitted refused as incomplete. -/
def navFuel : Nat → EvalRec
  | 0 => fun _ => EvalM.incomplete
  | Nat.succ n => fun c => ⟨fun s =>
      if navAdmits c s then
        (if isProjection c then evalFuel (n + 1) c else (evalStep (navFuel n) c).normalizeIncomplete).runState s
      else (.error .fuelExhausted, {})⟩

theorem navFuel_succ_run (n : Nat) (c : EvalCall) (s : EvalState) :
    (navFuel (n + 1) c).runState s =
      if navAdmits c s then
        (if isProjection c then evalFuel (n + 1) c else (evalStep (navFuel n) c).normalizeIncomplete).runState s
      else (.error .fuelExhausted, {}) := rfl

/-- **The navigation core is a restriction of production's core**: where it completes, it IS the
    core's run. -/
theorem navFuel_le (n : Nat) : navFuel n ⊑ evalFuel n := by
  induction n with
  | zero => exact fun _ _ => .inl rfl
  | succ n ih =>
    intro c s
    by_cases hadm : navAdmits c s = true
    · by_cases hproj : isProjection c = true
      · right
        rw [navFuel_succ_run, ite_eq_left hadm, ite_eq_left hproj]
      · have hstep := normalize_mono (evalStep_monotone _ _ ih c) s
        rcases hstep with hi | he
        · left
          unfold EvalM.IsIncompleteAt at hi ⊢
          rw [navFuel_succ_run, ite_eq_left hadm, ite_eq_right hproj]
          exact hi
        · right
          rw [navFuel_succ_run, evalFuel_succ, ite_eq_left hadm, ite_eq_right hproj]
          exact he
    · left
      unfold EvalM.IsIncompleteAt
      rw [navFuel_succ_run, ite_eq_right hadm]

/-- **Navigation runs.** The navigation core completes `c` from `s` with `r`. -/
def NavRuns (c : EvalCall) (s : EvalState) (r : Except Error c.Ret × EvalState) : Prop :=
  ∃ n, (navFuel n c).runState s = r ∧ r.1 ≠ .error .fuelExhausted

/-- A completed navigation-core run is the core's run at that fuel. -/
theorem navFuel_eq_core (n : Nat) (c : EvalCall) (s : EvalState)
    (h : ((navFuel n c).runState s).1 ≠ .error .fuelExhausted) :
    (navFuel n c).runState s = (evalFuel n c).runState s := by
  rcases navFuel_le n c s with hi | he
  · exact absurd (by unfold EvalM.IsIncompleteAt at hi; rw [hi]) h
  · exact he

/-- **A navigation run IS the production run.** -/
theorem NavRuns.production {c : EvalCall} {s : EvalState} {r : Except Error c.Ret × EvalState}
    (h : NavRuns c s r) : (evalUnbounded c).runState s = r := by
  obtain ⟨n, hrun, hne⟩ := h
  have heq := navFuel_eq_core n c s (by rw [hrun]; exact hne)
  exact production_of_fuel n c s r (heq.symm.trans hrun) hne

/-! ### Admission is kept by every navigation extension -/

theorem parameterAddress_kept {x : Ident} {ctx : EvalCtx} {s u : EvalState} (h : NavExt s u)
    (hanch : anchored x ctx s = true) :
    parameterAddressIn u.lexicalActivations x ctx = parameterAddressIn s.lexicalActivations x ctx :=
  parameterAddressIn_stable x ctx s u h.memo.activations (anchored_spec hanch)

theorem paramRowAdmits_mono {a : Algorithm} {ctx : EvalCtx} {s u : EvalState} (h : NavExt s u)
    (hadm : paramRowAdmits a ctx s = true) : paramRowAdmits a ctx u = true := by
  unfold paramRowAdmits at hadm ⊢
  split
  · rename_i parent opens props y id reference
    simp only [Bool.and_eq_true] at hadm ⊢
    exact ⟨anchored_mono h.memo.activations hadm.1, by rw [parameterAddress_kept h hadm.1]; exact hadm.2⟩
  · rfl

theorem navAdmits_mono {c : EvalCall} {s u : EvalState} (h : NavExt s u) (hadm : navAdmits c s = true) :
    navAdmits c u = true := by
  cases c
  case resolveAliasChase fc pr a ctx visited last => exact paramRowAdmits_mono h hadm
  case projectParameterCallable x ctx => exact anchored_mono h.memo.activations hadm
  case projectNeedCallable a =>
    show u.needs[a]?.isSome = true
    have hadm' : s.needs[a]?.isSome = true := hadm
    cases hc : s.needs[a]? with
    | none => rw [hc] at hadm'; cases hadm'
    | some cell =>
      obtain ⟨c', hc', -⟩ := h.memo.heap a cell hc
      rw [hc']; rfl
  all_goals exact hadm

/-! ## The fuel induction -/

/-- Normalizing the incomplete outcome keeps re-readability. -/
theorem RRat.normalize {α : Type} {s : EvalState} {m : EvalM α} (hm : RRat s m) : RRat s m.normalizeIncomplete := by
  intro hdone
  by_cases hraw : (m.runState s).1 = .error .fuelExhausted
  · rw [normalize_of_incomplete m s hraw] at hdone
    exact absurd rfl hdone
  · have h := hm hraw
    rw [normalize_of_complete m s hraw]
    refine ⟨h.1, fun hc u hu => ?_⟩
    have hu' := h.2 hc u hu
    rw [normalize_of_complete m u (by rw [hu']; exact hraw), hu']

/-- A parameter-row alias's binding cell, where the navigation core admits its chase: the
    parameter's own cell, found through the recorded activation. -/
theorem rron_paramRow_cell (parent : Option ScopeCtx) (opens : List Expr) (props : List PropDef) (y : Ident)
    (id : Option PropertyIdentity) (reference : Bool) (ctx : EvalCtx) :
    RRon (fun t => paramRowAdmits (.alias parent opens props (.param y) id reference) ctx t = true)
      (aliasBindingCell (.alias parent opens props (.param y) id reference) (.param y) ctx) := by
  intro s hs
  have hs' : (anchored y (ctx.push (.alias parent opens props (.param y) id reference)) s &&
      (parameterAddressIn s.lexicalActivations y (ctx.push (.alias parent opens props (.param y) id reference))).isSome) = true := hs
  simp only [Bool.and_eq_true] at hs'
  obtain ⟨hanch, hfound⟩ := hs'
  cases haddr : parameterAddressIn s.lexicalActivations y (ctx.push (.alias parent opens props (.param y) id reference)) with
  | none => rw [haddr] at hfound; cases hfound
  | some p =>
    have hrun : ∀ u, parameterAddressIn u.lexicalActivations y
        (ctx.push (.alias parent opens props (.param y) id reference)) = some p →
        (aliasBindingCell (.alias parent opens props (.param y) id reference) (.param y) ctx).runState u = (.ok p, u) :=
      fun u hu => KatLang.RuntimeAliasLaws.aliasBindingCell_parameter_transport _ y ctx u _ p
        (captured_run y _ u) hu
    exact RRat.of_run (hrun s haddr) (NavExt.refl s)
      (fun _ u hu => hrun u (by rw [parameterAddress_kept hu hanch]; exact haddr))

/-- **THE FUEL INDUCTION.** Every answer of the navigation core, at every fuel and for every call,
    is re-readable. -/
theorem navFuel_rr (n : Nat) : ∀ (c : EvalCall), RR (navFuel n c) := by
  induction n with
  | zero => exact fun _ _ hdone => absurd rfl hdone
  | succ n ih =>
    intro c s hdone
    rw [navFuel_succ_run] at hdone
    by_cases hadm : navAdmits c s = true
    case neg =>
      rw [ite_eq_right hadm] at hdone
      exact absurd rfl hdone
    -- the body, or the projection, re-readable at `s`
    have hbody : RRat s (if isProjection c then evalFuel (n + 1) c
        else (evalStep (navFuel n) c).normalizeIncomplete) := by
      cases c
      case projectNeedCallable a =>
        show RRat s (evalFuel (n + 1) (.projectNeedCallable a))
        intro hd
        have hvalid : s.needs[a]?.isSome = true := hadm
        have hprod := (production_completes_iff (.projectNeedCallable a) s _).2
          ⟨n + 1, rfl, (evalFuel_completes_iff (n + 1) _ s).2 hd⟩
        rw [← hprod.1]
        refine ⟨production_navExt (.projectNeedCallable a) s, fun _ u hu => ?_⟩
        have hre := (projection_reread a s hvalid hprod.2 u hu
          (NeedProjection.suspended (EvalRec.projectNeedWrittenAt (evalFuel n) a))).1
        have hne : ((evalUnbounded (.projectNeedCallable a)).runState s).1 ≠ .error .fuelExhausted := hprod.2
        exact fuel_succ_of_body n (.projectNeedCallable a) u _ hre hne
      case aliasStepIsRuntime step target ctx visited =>
        exact (rr_of_rron (rron_body_aliasStepIsRuntime (fun _ _ _ _ => trivial) (navFuel n)
          (fun c => rron_of_rr (ih c)) step target ctx visited) s).normalize
      case resolveAliasStructure a ctx =>
        exact (rr_of_rron (rron_body_resolveAliasStructure (fun _ _ _ _ => trivial) (navFuel n)
          (fun c => rron_of_rr (ih c)) a ctx) s).normalize
      case resolveDotReceiver? e ctx =>
        exact (rr_of_rron (rron_body_resolveDotReceiver? (fun _ _ _ _ => trivial) (navFuel n)
          (fun c => rron_of_rr (ih c)) e ctx) s).normalize
      case projectNeedStructuralMember e ctx =>
        exact (rr_of_rron (rron_body_projectNeedStructuralMember (fun _ _ _ _ => trivial) (navFuel n)
          (fun c => rron_of_rr (ih c)) e ctx) s).normalize
      case algorithmIntrinsicRoute receiver ctx =>
        exact (rr_of_rron (rron_body_algorithmIntrinsicRoute (fun _ _ _ _ => trivial) (navFuel n)
          (fun c => rron_of_rr (ih c)) receiver ctx) s).normalize
      case projectParameterCallable x ctx =>
        exact (rrat_projectParameterWith (EvalRec.projectNeedCallable (navFuel n))
          (fun a => ih (.projectNeedCallable a)) x ctx s hadm).normalize
      case resolveAlg e ctx =>
        have he : resolveAlgAdmits e = true := hadm
        refine RRat.normalize ?_
        show RRat s (EvalBody.resolveAlg (navFuel n) e ctx)
        cases e <;> first
          | (simp [resolveAlgAdmits] at he; done)
          | exact rr_of_sf (sf_evalError _) s
          | exact rr_identifyRuntime _ s
      case resolveAliasChase fc pr a ctx visited last =>
        refine RRat.normalize ?_
        show RRat s (EvalBody.resolveAliasChase (navFuel n) fc pr a ctx visited last)
        have hpa : paramRowAdmits a ctx s = true := hadm
        cases a with
        | mk p pp op pr' out id => exact rr_pure _ s
        | builtin b => exact rr_pure _ s
        | conditional p op bs id => exact rr_pure _ s
        | «alias» parent opens props target id reference =>
          by_cases hp : ∃ y, target = .param y
          · obtain ⟨y, rfl⟩ := hp
            exact rron_body_chase_alias
              (P := fun t => paramRowAdmits (.alias parent opens props (.param y) id reference) ctx t = true)
              (fun _ _ h hs => paramRowAdmits_mono h hs) (navFuel n) (fun c => rron_of_rr (ih c))
              fc pr parent opens props (.param y) id reference ctx visited last
              (rron_paramRow_cell parent opens props y id reference ctx) s hpa
          · have hnp : ∀ y, target ≠ .param y := fun y h => hp ⟨y, h⟩
            exact rr_of_rron (rron_body_chase_alias (fun _ _ _ _ => trivial) (navFuel n)
              (fun c => rron_of_rr (ih c)) fc pr parent opens props target id reference ctx visited last
              (rron_of_rr (rr_aliasBindingCell _ target ctx hnp))) s
      all_goals (simp [navAdmits] at hadm)
    rw [ite_eq_left hadm] at hdone
    have h := hbody hdone
    rw [navFuel_succ_run, ite_eq_left hadm]
    refine ⟨h.1, fun hc u hu => ?_⟩
    rw [navFuel_succ_run, ite_eq_left (navAdmits_mono (h.1.trans hu) hadm)]
    exact h.2 hc u hu

/-! ## The theorem -/

/-- **IDENTITY NAVIGATION IS RE-READABLE.** For EVERY call: a navigation run from `s` with outcome
    `o` and exit state `t` that minted no runtime identity
    * is the production run (`NavRuns.production`),
    * is a navigation extension, and
    * is RE-READ from every navigation extension `u` of `t`: production returns `o` — the value, or
      the same failure — and writes nothing, and the navigation core does the same.

    No shape premise: a runtime-target alias, a transparent reference with a name or member-path
    row, a chain of any length, a nested or parameter-rooted member path. No key premise: the
    chase's `reprStr`-built keys are compared alike at both states. -/
theorem navigation_reread (c : EvalCall) (s t : EvalState) (o : Except Error c.Ret)
    (hnav : NavRuns c s (o, t)) (hmint : t.nextRuntimeDeclaration = s.nextRuntimeDeclaration) :
    NavExt s t ∧ ∀ u, NavExt t u → (evalUnbounded c).runState u = (o, u) ∧ NavRuns c u (o, u) := by
  obtain ⟨n, hrun, hne⟩ := hnav
  have h := navFuel_rr n c s (by rw [hrun]; exact hne)
  rw [hrun] at h
  refine ⟨h.1, fun u hu => ?_⟩
  have hu' : NavRuns c u (o, u) := ⟨n, h.2 hmint u hu, hne⟩
  exact ⟨hu'.production, hu'⟩

end KatLang.NavigationReread
