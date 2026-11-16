import KatLangArityLaws.SupplyCorrespondence
import KatLangArityLaws.WhileRoundProduction

open KatLang KatLang.EvaluatorCore KatLang.BinderTrace KatLang.SupplyCorrespondence
open KatLang.NeedControl.Schedule

/-!
# The production channels meet the correspondence premises of R6 (November 2026)

`KatLangArityLaws/SupplyCorrespondence.lean` proves the callback / direct-call binder correspondence
over two Ready supplies for ANY channel record, under two premises about the channels: the recursive
collector edge corresponds (`hrec`) and the CALLABLE channel corresponds (`hcal`). They were left as
premises because, when that module was written, the production channels (`demandNeedRecursive`,
`projectNeedCallable`) were `partial` definitions: opaque constants, about which no theorem could be
proved. Since R7 they are the total core under its fuel search, and both premises are THEOREMS of the
production channels. This module proves them and restates the R6 theorems for production with no
channel premise.

* **CALLABLE** (`production_callable_sim`, `binding_callable_sim`). On a Ready or collector cell the
  projection shell never consults the written projection: it returns the memo, reports a cycle on an
  active projection, or publishes the successful absence of identity
  (`projection_run_of_identityless`, from `NeedControl.Projection`). So the core body of
  `projectNeedCallable` consults no evaluator answer there and its run is production's outright
  (`production_projection_run`, through `production_of_answer_free_or_reset`).
* **VALUE, the recursive collector edge** (`production_recursive_edge_sim`). By induction on fuel.
  The core at fuel `n` forgets its state on exhaustion, so it is NOT a simulation on related heaps;
  the same core with the production exhaustion convention — the entry state returned,
  `fuelDemand n` — is, by the existing shell theorem `step_sim` at every level
  (`fuelDemand_sim`). The two conventions give the same shell run wherever it completes, and are
  incomplete together (`step_coh`, over the collector traversal `schedule_coh`), and a production
  demand is `fuelDemand m` at every sufficiently large `m` (`production_demand_eventually`).
* **The R6 theorems at production** (`production_capabilities_correspond`,
  `binding_capabilities_correspond`, `production_ready_supplies_bind_correspondingly`,
  `production_ready_supplies_select_correspondingly`): for the public channels
  `⟨demandNeed, projectNeedCallable⟩` and for the evaluator's own binder channels
  `bindingChannels`, with NO premise on the channels.

Unchanged: the general theorems of `SupplyCorrespondence.lean` keep `hrec` and `hcal`, because they
quantify over every channel record and the premises are false for some. The observation boundary is
unchanged too: these are BINDING runs over Ready and collector cells. Suspended expression cells are
not in `HeapCorr`, and callback ≡ direct-call EVALUATION stays open (Q-66; ledger E-8). Nothing here
concerns C#.
-/

namespace KatLang.SupplyCorrespondence.Production

/-! ## 0. Answer-free bodies, exhaustion included -/

/-- A body run that never consults the evaluator answer at `s` is production's run there — also
    when it is the incomplete outcome, provided it then returns its entry state (the production
    exhaustion convention). `production_of_answer_free` is the completed case. -/
theorem production_of_answer_free_or_reset (c : EvalCall) (s : EvalState)
    (r : Except Error c.Ret × EvalState) (h : ∀ rec, (evalStep rec c).runState s = r)
    (hr : r.1 = .error .fuelExhausted → r.2 = s) :
    (evalUnbounded c).runState s = r := by
  by_cases hne : r.1 = .error .fuelExhausted
  · have hinc : ¬ ProductionCompletes (evalUnbounded c) s := by
      intro hc
      have hu := production_unfolds c s hc
      rw [h] at hu
      exact hc (by rw [← hu]; exact hne)
    rw [production_incomplete_state c s hinc]
    rcases r with ⟨o, u⟩
    simp only at hne hr
    subst hne
    rw [hr rfl]
  · exact KatLang.WhileRoundProduction.production_of_answer_free c s r h hne

/-! ## 1. The CALLABLE channel -/

/-- The run of the projection shell on a cell that carries no written expression. -/
def projectionRun (cell : NeedCell) (a : Nat) (s : EvalState) : Except Error (Option Algorithm) × EvalState :=
  match cell.callable with
  | .projected outcome => (outcome, s)
  | .projecting => (.error .demandCycle, s)
  | .unprojected => (.ok none, KatLang.NeedControl.Projection.setCallable a (.projected (.ok none)) s)

/-- On a Ready or collector cell the projection shell answers from the cell's memo and suspension
    alone, whatever the written projection. -/
theorem projection_run_of_identityless (written : Expr → EvalCtx → EvalM (Option Algorithm)) (a : Nat)
    (s : EvalState) (cell : NeedCell) (hc : s.needs[a]? = some cell)
    (hid : ∀ source caller values, cell.suspension ≠ .expression source caller values) :
    (NeedProjection.step (NeedProjection.suspended written) a).runState s = projectionRun cell a s := by
  unfold projectionRun
  cases hs : cell.callable with
  | projected outcome => exact KatLang.NeedControl.Projection.projected_sticky _ a s cell outcome hc hs
  | projecting => exact KatLang.NeedControl.Projection.projecting_reentry_cycle _ a s cell hc hs
  | unprojected =>
    exact KatLang.NeedControl.Projection.identityless_projection written a s cell hc hs
      (fun source caller values h => absurd h (hid source caller values))

/-- An incomplete projection run of such a cell is a memo read: the state is the entry state. -/
theorem projectionRun_incomplete_state (cell : NeedCell) (a : Nat) (s : EvalState)
    (h : (projectionRun cell a s).1 = .error .fuelExhausted) : (projectionRun cell a s).2 = s := by
  unfold projectionRun at h ⊢
  cases hs : cell.callable with
  | projected outcome => rfl
  | projecting => rfl
  | unprojected => rw [hs] at h; cases h

/-- **Production.** `projectNeedCallable` on a Ready or collector cell is that run: the production
    projection answers such a cell from its memo and suspension alone. -/
theorem production_projection_run (a : Nat) (s : EvalState) (cell : NeedCell)
    (hc : s.needs[a]? = some cell)
    (hid : ∀ source caller values, cell.suspension ≠ .expression source caller values) :
    (projectNeedCallable a).runState s = projectionRun cell a s :=
  production_of_answer_free_or_reset (.projectNeedCallable a) s _
    (fun rec => projection_run_of_identityless (rec.projectNeedWrittenAt a) a s cell hc hid)
    (projectionRun_incomplete_state cell a s)

theorem identityless_of_corr {t : Table} : ∀ {sp1 sp2 : NeedSuspension}, SuspCorr t sp1 sp2 →
    (∀ source caller values, sp1 ≠ .expression source caller values) ∧
    (∀ source caller values, sp2 ≠ .expression source caller values)
  | .ready _, .ready _, _ => ⟨fun _ _ _ h => (nomatch h), fun _ _ _ h => (nomatch h)⟩
  | .collector _, .collector _, _ => ⟨fun _ _ _ h => (nomatch h), fun _ _ _ h => (nomatch h)⟩
  | .expression _ _ _, _, h => by cases h
  | .ready _, .expression _ _ _, h => by cases h
  | .ready _, .collector _, h => by cases h
  | .collector _, .expression _ _ _, h => by cases h
  | .collector _, .ready _, h => by cases h

theorem callable_update_corr (t : Table) (v : NeedCallableState) :
    ∀ c1 c2, CellCorr t c1 c2 → CellCorr t { c1 with callable := v } { c2 with callable := v } :=
  fun _ _ hc => ⟨hc.1, hc.2.1, rfl, hc.2.2.2⟩

/-- Two runs that are the projection run of corresponding cells correspond. -/
theorem projectionRun_corr (t : Table) (a1 a2 : Nat) (ha : Addr t a1 a2) (s1 s2 : EvalState)
    (hR : HeapCorr t s1 s2) (c1 c2 : NeedCell) (hcal : c1.callable = c2.callable) :
    RunCorr HeapCorr (fun _ v w => v = w) t (projectionRun c1 a1 s1) (projectionRun c2 a2 s2) := by
  unfold projectionRun
  rw [← hcal]
  cases c1.callable with
  | projected outcome => exact ⟨t, extends_refl t, hR, by cases outcome <;> simp [ResCorr]⟩
  | projecting => exact ⟨t, extends_refl t, hR, rfl⟩
  | unprojected =>
    exact ⟨t, extends_refl t,
      heap_modify t s1 s2 a1 a2 (fun c => { c with callable := .projected (.ok none) }) hR ha
        (callable_update_corr t _), rfl⟩

/-- **`hcal` at production**: the public CALLABLE channel `projectNeedCallable` corresponds on
    corresponding cells. -/
theorem production_callable_sim (t : Table) (a1 a2 : Nat) (ha : Addr t a1 a2) :
    Sim HeapCorr (fun _ v w => v = w) t (projectNeedCallable a1) (projectNeedCallable a2) := by
  intro s1 s2 hR
  obtain ⟨c1, c2, h1, h2, hc⟩ := hR.1 _ ha
  obtain ⟨hid1, hid2⟩ := identityless_of_corr hc.1
  show RunCorr HeapCorr _ t ((projectNeedCallable a1).runState s1) ((projectNeedCallable a2).runState s2)
  rw [production_projection_run a1 s1 c1 h1 hid1, production_projection_run a2 s2 c2 h2 hid2]
  exact projectionRun_corr t a1 a2 ha s1 s2 hR c1 c2 hc.2.2.1

/-- **`hcal` for the evaluator's binder channels**: the CALLABLE shell of `bindingChannels` (the
    projection shell over the production written projection) corresponds on corresponding cells. -/
theorem binding_callable_sim (t : Table) (a1 a2 : Nat) (ha : Addr t a1 a2) :
    Sim HeapCorr (fun _ v w => v = w) t (bindingChannels.callable a1) (bindingChannels.callable a2) := by
  intro s1 s2 hR
  obtain ⟨c1, c2, h1, h2, hc⟩ := hR.1 _ ha
  obtain ⟨hid1, hid2⟩ := identityless_of_corr hc.1
  show RunCorr HeapCorr _ t
    ((NeedProjection.step (NeedProjection.suspended (projectNeedWrittenAt a1)) a1).runState s1)
    ((NeedProjection.step (NeedProjection.suspended (projectNeedWrittenAt a2)) a2).runState s2)
  rw [projection_run_of_identityless _ a1 s1 c1 h1 hid1, projection_run_of_identityless _ a2 s2 c2 h2 hid2]
  exact projectionRun_corr t a1 a2 ha s1 s2 hR c1 c2 hc.2.2.1

/-! ## 2. Exhaustion coherence of the VALUE shell -/

/-- Two runs are COHERENT: both are the incomplete outcome, or the first completes and the second
    is the very same run. -/
def Coh {α : Type} (r r' : Except Error α × EvalState) : Prop :=
  (r.1 = .error .fuelExhausted ∧ r'.1 = .error .fuelExhausted) ∨ (r.1 ≠ .error .fuelExhausted ∧ r' = r)

theorem coh_refl {α : Type} (r : Except Error α × EvalState) : Coh r r := by
  by_cases h : r.1 = .error .fuelExhausted
  · exact .inl ⟨h, h⟩
  · exact .inr ⟨h, rfl⟩

theorem coh_of_eq {α : Type} {r r' : Except Error α × EvalState} (h : r' = r) : Coh r r' := by
  subst h; exact coh_refl _

/-- Coherence is kept by a map of the outcome that keeps the incomplete outcome apart. -/
theorem coh_mapOutcome {α β : Type} (g : Except Error α → Except Error β)
    (hg : ∀ o, g o = .error .fuelExhausted ↔ o = .error .fuelExhausted)
    {r r' : Except Error α × EvalState} (h : Coh r r') : Coh (g r.1, r.2) (g r'.1, r'.2) := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact .inl ⟨(hg _).2 h1, (hg _).2 h2⟩
  · subst h2; exact .inr ⟨fun h => h1 ((hg _).1 h), rfl⟩

theorem map_fuel_iff {α β : Type} (f : α → β) (o : Except Error α) :
    o.map f = .error .fuelExhausted ↔ o = .error .fuelExhausted := by
  cases o with
  | ok v => constructor <;> intro h <;> cases h
  | error e => constructor <;> intro h <;> (injection h with h; subst h; rfl)

theorem nest_fuel_iff {α : Type} (o : Except Error α) :
    o.mapError Error.nestMissingOutput = .error .fuelExhausted ↔ o = .error .fuelExhausted := by
  cases o with
  | ok v => constructor <;> intro h <;> cases h
  | error e =>
    constructor
    · intro h
      injection h with h
      cases e <;> first | rfl | cases h
    · intro h; injection h with h; subst h; rfl

/-- The value projection of a coherent demand is coherent. -/
theorem coh_fst (recur recur' : Nat → EvalM CountedResult)
    (h : ∀ b s, Coh ((recur b).runState s) ((recur' b).runState s)) (b : Nat) (s : EvalState) :
    Coh ((Prod.fst <$> recur b).runState s) ((Prod.fst <$> recur' b).runState s) := by
  have e : ∀ m : EvalM CountedResult, (Prod.fst <$> m).runState s =
      (((m.runState s).1.map Prod.fst), (m.runState s).2) := by
    intro m
    rw [KatLang.NeedControl.Collector.map_run]
    rcases m.runState s with ⟨o, u⟩
    cases o <;> rfl
  rw [e, e]
  exact coh_mapOutcome (fun o => o.map Prod.fst) (map_fuel_iff _) (h b s)

/-- The collector traversal over two coherent demands is coherent. -/
theorem schedule_coh {β : Type} (f f' : Nat → EvalM β)
    (h : ∀ a s, Coh ((f a).runState s) ((f' a).runState s)) :
    ∀ (xs : List Nat) (s : EvalState), Coh (schedule f xs s) (schedule f' xs s)
  | [], s => coh_refl _
  | a :: rest, s => by
      rcases hr : (f a).runState s with ⟨o, u⟩
      rcases hr' : (f' a).runState s with ⟨o', u'⟩
      have hh := h a s
      rw [hr, hr'] at hh
      rcases hh with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · simp only at h1 h2
        subst h1; subst h2
        refine .inl ⟨?_, ?_⟩ <;> simp only [schedule, hr, hr']
      · cases h2
        cases o with
        | error e => exact coh_of_eq (by simp only [schedule, hr, hr'])
        | ok v =>
          have ih := schedule_coh f f' h rest u
          rcases hs : schedule f rest u with ⟨p, w⟩
          rcases hs' : schedule f' rest u with ⟨p', w'⟩
          rw [hs, hs'] at ih
          rcases ih with ⟨g1, g2⟩ | ⟨g1, g2⟩
          · simp only at g1 g2
            subst g1; subst g2
            refine .inl ⟨?_, ?_⟩ <;> simp only [schedule, hr, hr', hs, hs']
          · cases g2
            exact coh_of_eq (by simp only [schedule, hr, hr', hs, hs'])

/-- Collector materialization over two coherent demands is coherent. -/
theorem materialize_coh (recur recur' : Nat → EvalM CountedResult)
    (h : ∀ b s, Coh ((recur b).runState s) ((recur' b).runState s)) (slice : List Nat) (s : EvalState) :
    Coh ((NeedDemand.materialize recur slice).runState s) ((NeedDemand.materialize recur' slice).runState s) := by
  rw [collector_schedule, collector_schedule]
  exact coh_mapOutcome (fun o => o.map makeCollectionListResult) (map_fuel_iff _)
    (schedule_coh _ _ (coh_fst recur recur' h) slice s)

/-- The suspended computation of a cell depends on the recursive demand only in its collector arm,
    coherently. -/
theorem suspendedValue_coh (ev : Expr → EvalCtx → ValEnv → EvalM CountedResult) (route : NeedPlan.Route)
    (recur recur' : Nat → EvalM CountedResult)
    (h : ∀ b s, Coh ((recur b).runState s) ((recur' b).runState s)) (a : Nat) (s : EvalState) :
    ∀ sp : NeedSuspension,
      Coh ((NeedDemand.suspendedValue ev route recur a sp).runState s)
        ((NeedDemand.suspendedValue ev route recur' a sp).runState s)
  | .ready _ => coh_refl _
  | .expression _ _ _ => coh_refl _
  | .collector slice => by
      show Coh (runEval (withNestedMissingOutput (NeedDemand.materialize recur slice)) s)
        (runEval (withNestedMissingOutput (NeedDemand.materialize recur' slice)) s)
      rw [nested_run, nested_run]
      exact coh_mapOutcome (fun o => o.mapError Error.nestMissingOutput) nest_fuel_iff
        (materialize_coh recur recur' h slice s)

/-- **Exhaustion coherence of the VALUE shell.** Two recursive demands that are incomplete together
    and otherwise equal give shell runs that are incomplete together and otherwise equal. -/
theorem step_coh (ev : Expr → EvalCtx → ValEnv → EvalM CountedResult) (route : NeedPlan.Route)
    (recur recur' : Nat → EvalM CountedResult)
    (h : ∀ b s, Coh ((recur b).runState s) ((recur' b).runState s)) (a : Nat) (s : EvalState) :
    Coh ((NeedDemand.step ev route recur a).runState s) ((NeedDemand.step ev route recur' a).runState s) := by
  cases hc : s.needs[a]? with
  | none =>
    rw [KatLang.NeedControl.Production.invalid_address ev route recur a s hc,
      KatLang.NeedControl.Production.invalid_address ev route recur' a s hc]
    exact coh_refl _
  | some cell =>
    cases hs : cell.state with
    | completed outcome =>
      rw [KatLang.NeedControl.Memo.completed_sticky ev route recur a s cell outcome hc hs,
        KatLang.NeedControl.Memo.completed_sticky ev route recur' a s cell outcome hc hs]
      exact coh_refl _
    | evaluating =>
      rw [KatLang.NeedControl.Production.evaluating_cycle ev route recur a s cell hc hs,
        KatLang.NeedControl.Production.evaluating_cycle ev route recur' a s cell hc hs]
      exact coh_refl _
    | suspended =>
      have hsv := suspendedValue_coh ev route recur recur' h a
        { s with needs := s.needs.modify a (fun c => { c with state := .evaluating }) } cell.suspension
      rcases hv : (NeedDemand.suspendedValue ev route recur a cell.suspension).runState
          { s with needs := s.needs.modify a (fun c => { c with state := .evaluating }) } with ⟨o, u⟩
      rcases hv' : (NeedDemand.suspendedValue ev route recur' a cell.suspension).runState
          { s with needs := s.needs.modify a (fun c => { c with state := .evaluating }) } with ⟨o', u'⟩
      rw [hv, hv'] at hsv
      rcases hsv with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · simp only at h1 h2
        subst h1; subst h2
        rw [KatLang.NeedControl.Memo.suspended_incomplete ev route recur a s u cell _ hc hs hv rfl,
          KatLang.NeedControl.Memo.suspended_incomplete ev route recur' a s u' cell _ hc hs hv' rfl]
        exact .inl ⟨rfl, rfl⟩
      · cases h2
        simp only at h1
        have hinc : o.isIncomplete = false := by
          cases hi : o.isIncomplete with
          | false => rfl
          | true => exact absurd (Except.isIncomplete_eq_true hi) h1
        rw [KatLang.NeedControl.Memo.suspended_retains_state ev route recur a s u cell o hc hs hv hinc,
          KatLang.NeedControl.Memo.suspended_retains_state ev route recur' a s u cell o hc hs hv' hinc]
        exact coh_refl _

/-! ## 3. The recursive VALUE edge, by fuel -/

/-- `m` with the PRODUCTION exhaustion convention: an incomplete run returns its entry state. -/
def resetIncomplete {α : Type} (m : EvalM α) : EvalM α :=
  ⟨fun s => if (m.runState s).1.isIncomplete then (.error .fuelExhausted, s) else m.runState s⟩

theorem reset_run_incomplete {α : Type} (m : EvalM α) (s : EvalState)
    (h : (m.runState s).1 = .error .fuelExhausted) :
    (resetIncomplete m).runState s = (.error .fuelExhausted, s) := by
  show (if (m.runState s).1.isIncomplete then _ else _) = _
  rw [h]; rfl

theorem reset_run_complete {α : Type} (m : EvalM α) (s : EvalState)
    (h : (m.runState s).1 ≠ .error .fuelExhausted) :
    (resetIncomplete m).runState s = m.runState s := by
  show (if (m.runState s).1.isIncomplete then _ else _) = _
  cases hi : (m.runState s).1.isIncomplete with
  | false => rfl
  | true => exact absurd (Except.isIncomplete_eq_true hi) h

/-- The recursive VALUE demand of the core at fuel `n`, under the production exhaustion convention. -/
def fuelDemand (n : Nat) (a : Nat) : EvalM CountedResult :=
  resetIncomplete (evalFuel n (.demandNeedRecursive a))

/-- The core's demand and `fuelDemand` are coherent. -/
theorem fuel_coh (n : Nat) (b : Nat) (s : EvalState) :
    Coh ((evalFuel n (.demandNeedRecursive b)).runState s) ((fuelDemand n b).runState s) := by
  by_cases h : ((evalFuel n (.demandNeedRecursive b)).runState s).1 = .error .fuelExhausted
  · exact .inl ⟨h, by unfold fuelDemand; rw [reset_run_incomplete _ _ h]⟩
  · exact .inr ⟨h, reset_run_complete _ _ h⟩

/-- The VALUE shell the core runs at fuel `n + 1`, over the core at fuel `n`. -/
abbrev coreShell (n : Nat) (a : Nat) : EvalM CountedResult :=
  NeedDemand.step ((evalFuel n).evalSuppliedAt a) (evalFuel n).planRoute (evalFuel n).demandNeedRecursive a

/-- The same shell over `fuelDemand n` as its recursive demand. -/
abbrev resetShell (n : Nat) (a : Nat) : EvalM CountedResult :=
  NeedDemand.step ((evalFuel n).evalSuppliedAt a) (evalFuel n).planRoute (fuelDemand n) a

theorem shell_coh (n : Nat) (a : Nat) (s : EvalState) :
    Coh ((coreShell n a).runState s) ((resetShell n a).runState s) :=
  step_coh _ _ _ _ (fun b s => fuel_coh n b s) a s

theorem fuelDemand_succ_incomplete (n : Nat) (a : Nat) (s : EvalState)
    (h : ((coreShell n a).runState s).1 = .error .fuelExhausted) :
    (fuelDemand (n + 1) a).runState s = (.error .fuelExhausted, s) := by
  refine reset_run_incomplete _ s ?_
  rw [evalFuel_succ]
  rw [show evalStep (evalFuel n) (.demandNeedRecursive a) = coreShell n a from rfl,
    normalize_of_incomplete _ s h]

theorem fuelDemand_succ_complete (n : Nat) (a : Nat) (s : EvalState)
    (h : ((coreShell n a).runState s).1 ≠ .error .fuelExhausted) :
    (fuelDemand (n + 1) a).runState s = (coreShell n a).runState s := by
  have e : (evalFuel (n + 1) (.demandNeedRecursive a)).runState s = (coreShell n a).runState s := by
    rw [evalFuel_succ]
    rw [show evalStep (evalFuel n) (.demandNeedRecursive a) = coreShell n a from rfl,
      normalize_of_complete _ s h]
  unfold fuelDemand
  rw [reset_run_complete _ s (by rw [e]; exact h), e]

/-- **The recursive VALUE edge is a simulation at every fuel**, under the production exhaustion
    convention: by `step_sim` at each level. -/
theorem fuelDemand_sim : ∀ (n : Nat) (t : Table) (b1 b2 : Nat), Addr t b1 b2 →
    Sim HeapCorr (fun _ v w => v = w) t (fuelDemand n b1) (fuelDemand n b2)
  | 0, t, _, _, _ => fun _ _ hR => ⟨t, extends_refl t, hR, rfl⟩
  | Nat.succ n, t, b1, b2, hb => by
      intro s1 s2 hR
      have hsim : RunCorr HeapCorr (fun _ v w => v = w) t ((resetShell n b1).runState s1)
          ((resetShell n b2).runState s2) :=
        step_sim (fun a => (evalFuel n).evalSuppliedAt a) (evalFuel n).planRoute (fuelDemand n)
          (fun t' c1 c2 hc => fuelDemand_sim n t' c1 c2 hc) t b1 b2 hb s1 s2 hR
      have hc1 := shell_coh n b1 s1
      have hc2 := shell_coh n b2 s2
      show RunCorr HeapCorr _ t ((fuelDemand (n + 1) b1).runState s1) ((fuelDemand (n + 1) b2).runState s2)
      obtain ⟨t', hext, hR', hres⟩ := hsim
      rcases hc1 with ⟨a1, a1'⟩ | ⟨a1, a1'⟩
      · -- side 1 is incomplete, so the reset shell of side 1 is, hence side 2's, hence side 2
        have a2' : ((resetShell n b2).runState s2).1 = .error .fuelExhausted := by
          rw [a1'] at hres
          rcases hq : ((resetShell n b2).runState s2).1 with e | v
          · rw [hq] at hres; simp only [ResCorr] at hres; rw [← hres]
          · rw [hq] at hres; simp only [ResCorr] at hres
        have a2 : ((coreShell n b2).runState s2).1 = .error .fuelExhausted := by
          rcases hc2 with ⟨g, _⟩ | ⟨g, g'⟩
          · exact g
          · rw [g'] at a2'; exact absurd a2' g
        rw [fuelDemand_succ_incomplete n b1 s1 a1, fuelDemand_succ_incomplete n b2 s2 a2]
        exact ⟨t, extends_refl t, hR, rfl⟩
      · -- side 1 completes: the reset shell is the core shell, and side 2 completes with it
        have b2' : ((resetShell n b2).runState s2).1 ≠ .error .fuelExhausted := by
          intro hq
          rw [a1'] at hres
          rw [hq] at hres
          rcases hp : ((coreShell n b1).runState s1).1 with e | v
          · rw [hp] at hres; simp only [ResCorr] at hres
            exact a1 (by rw [hp, hres])
          · rw [hp] at hres; simp only [ResCorr] at hres
        have hc2' : ((coreShell n b2).runState s2).1 ≠ .error .fuelExhausted ∧
            (resetShell n b2).runState s2 = (coreShell n b2).runState s2 := by
          rcases hc2 with ⟨_, g'⟩ | ⟨g, g'⟩
          · exact absurd g' b2'
          · exact ⟨g, g'⟩
        rw [fuelDemand_succ_complete n b1 s1 a1, fuelDemand_succ_complete n b2 s2 hc2'.1, ← a1', ← hc2'.2]
        exact ⟨t', hext, hR', hres⟩

/-- A production demand is the core's demand under the production exhaustion convention at every
    sufficiently large fuel: its completed run from the fuel that completes it on, and the incomplete
    outcome at the entry state when no fuel completes it. -/
theorem production_demand_eventually (a : Nat) (s : EvalState) :
    ∃ m0, ∀ m, m0 ≤ m → (demandNeedRecursive a).runState s = (fuelDemand m a).runState s := by
  show ∃ m0, ∀ m, m0 ≤ m →
    (evalUnbounded (.demandNeedRecursive a)).runState s = (fuelDemand m a).runState s
  by_cases hc : ProductionCompletes (evalUnbounded (.demandNeedRecursive a)) s
  · obtain ⟨m0, hr, hm⟩ := (production_completes_iff (.demandNeedRecursive a) s _).1 ⟨rfl, hc⟩
    refine ⟨m0, fun m hle => ?_⟩
    have hst := completed_stable hle (.demandNeedRecursive a) s hm
    have hne : ((evalFuel m (.demandNeedRecursive a)).runState s).1 ≠ .error .fuelExhausted := by
      rw [hst, hr]; exact hc
    unfold fuelDemand
    rw [reset_run_complete _ s hne, hst, hr]
  · refine ⟨0, fun m _ => ?_⟩
    have hinc : ((evalFuel m (.demandNeedRecursive a)).runState s).1 = .error .fuelExhausted := by
      apply Classical.byContradiction
      intro hne
      exact hc ((production_completes_iff (.demandNeedRecursive a) s _).2
        ⟨m, rfl, (evalFuel_completes_iff m _ s).2 hne⟩).2
    unfold fuelDemand
    rw [production_incomplete_state _ s hc, reset_run_incomplete _ s hinc]

/-- **`hrec` at production**: the recursive VALUE edge `demandNeedRecursive` corresponds on
    corresponding cells — completed, evaluating, Ready and collector cells alike, a collector's
    slice demanded through the same edge. -/
theorem production_recursive_edge_sim (t : Table) (b1 b2 : Nat) (hb : Addr t b1 b2) :
    Sim HeapCorr (fun _ v w => v = w) t (demandNeedRecursive b1) (demandNeedRecursive b2) := by
  intro s1 s2 hR
  obtain ⟨m1, h1⟩ := production_demand_eventually b1 s1
  obtain ⟨m2, h2⟩ := production_demand_eventually b2 s2
  show RunCorr HeapCorr _ t ((demandNeedRecursive b1).runState s1) ((demandNeedRecursive b2).runState s2)
  rw [h1 (max m1 m2) (Nat.le_max_left _ _), h2 (max m1 m2) (Nat.le_max_right _ _)]
  exact fuelDemand_sim (max m1 m2) t b1 b2 hb s1 s2 hR

/-! ## 4. The R6 theorems at production, without channel premises -/

/-- THE PUBLIC CHANNELS CORRESPOND under `HeapCorr`, with no premise: `heap_corr_capabilities` at
    `⟨demandNeed, projectNeedCallable⟩`, its two channel premises discharged above. -/
theorem production_capabilities_correspond :
    CapCorr HeapCorr (⟨demandNeed, projectNeedCallable⟩ : NeedChannels).capabilities
      (⟨demandNeed, projectNeedCallable⟩ : NeedChannels).capabilities :=
  heap_corr_capabilities ⟨demandNeed, projectNeedCallable⟩ (fun a => evalSuppliedAt a) productionPlanRoute
    demandNeedRecursive public_channels_value production_recursive_edge_sim production_callable_sim

/-- THE EVALUATOR'S BINDER CHANNELS CORRESPOND under `HeapCorr`, with no premise: the channels every
    binder call site of the evaluator passes (`EvaluatorCore.bindingChannels_is_core`). -/
theorem binding_capabilities_correspond :
    CapCorr HeapCorr bindingChannels.capabilities bindingChannels.capabilities :=
  heap_corr_capabilities bindingChannels (fun a => evalSuppliedAt a) productionPlanRoute
    demandNeedRecursive rfl production_recursive_edge_sim binding_callable_sim

/-- LEVEL 2 AT PRODUCTION (R6): two Ready supplies of the same counted arguments, formed from ANY two
    states and bound by the ONE production binder at the evaluator's own binder channels,
    correspond — with NO premise on the channels. -/
theorem production_ready_supplies_bind_correspondingly (args : List CountedResult)
    (ps : List NeedPattern) (family : Bool) (s1 s2 : EvalState) :
    RunCorr HeapCorr OptEnvCorr []
      (runEval (do let cells ← args.mapM readyNeed; bindNeedPatterns bindingChannels ps cells family) s1)
      (runEval (do let cells ← args.mapM readyNeed; bindNeedPatterns bindingChannels ps cells family) s2) :=
  ready_supplies_bind_correspondingly bindingChannels (fun a => evalSuppliedAt a) productionPlanRoute
    demandNeedRecursive rfl production_recursive_edge_sim binding_callable_sim args ps family s1 s2

/-- The same at the public channels `⟨demandNeed, projectNeedCallable⟩`. -/
theorem public_ready_supplies_bind_correspondingly (args : List CountedResult)
    (ps : List NeedPattern) (family : Bool) (s1 s2 : EvalState) :
    RunCorr HeapCorr OptEnvCorr []
      (runEval (do let cells ← args.mapM readyNeed
                   bindNeedPatterns ⟨demandNeed, projectNeedCallable⟩ ps cells family) s1)
      (runEval (do let cells ← args.mapM readyNeed
                   bindNeedPatterns ⟨demandNeed, projectNeedCallable⟩ ps cells family) s2) :=
  ready_supplies_bind_correspondingly ⟨demandNeed, projectNeedCallable⟩ (fun a => evalSuppliedAt a)
    productionPlanRoute demandNeedRecursive public_channels_value production_recursive_edge_sim
    production_callable_sim args ps family s1 s2

/-- The clause-family route at production: the dispatcher at the evaluator's binder channels, the
    activated body still an explicit continuation premise (`hact`), no premise on the channels. -/
theorem production_ready_supplies_select_correspondingly {γ : Type}
    (Q : Table → γ → γ → Prop) (activate : CondBranch → NeedEnv → EvalM γ)
    (hact : ∀ t b e1 e2, EnvCorr t e1 e2 → Sim HeapCorr Q t (activate b e1) (activate b e2))
    (callee : Algorithm) (calleeName : String) (args : List CountedResult) (s1 s2 : EvalState) :
    RunCorr HeapCorr Q []
      (runEval (do let cells ← args.mapM readyNeed
                   NeedBinder.selectFamily bindingChannels.capabilities callee cells calleeName activate) s1)
      (runEval (do let cells ← args.mapM readyNeed
                   NeedBinder.selectFamily bindingChannels.capabilities callee cells calleeName activate) s2) :=
  ready_supplies_select_correspondingly bindingChannels (fun a => evalSuppliedAt a) productionPlanRoute
    demandNeedRecursive rfl production_recursive_edge_sim binding_callable_sim Q activate hact callee
    calleeName args s1 s2

end KatLang.SupplyCorrespondence.Production
