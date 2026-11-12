import KatLangArityLaws.HeapInsertionCalls
import KatLangArityLaws.PlanRouteBridge
import KatLangArityLaws.MemberStability

open KatLang KatLang.CallPlan KatLang.EvaluatorCore

/-!
# Plan conservativity, step 1: the `.Algorithm` route as a CONDITIONAL bridge (ledger E-18, M2)

UNCONDITIONAL agreement of the `.Algorithm` route with ordinary evaluation is FALSE — the final
states differ (`PlanRouteBridgeGuards.algorithmHeapDiffers`) and so do the OUTCOMES, even up to
address renaming (`PlanRouteBridgeGuards.SelfObservation.outcomeDiffers`: 9 against 10 when the
run observes the plan's own callee record through a stored reference). This module proves the
bridge that IS true: both written forms, `R.Algorithm(args)` and `(R.Algorithm)(args)`, against
their actual ordinary production entries, UNDER the structural heap relation of
`HeapInsertion.lean` — the COMPLETE relation `HeapInsertion.Inserted`, `Frame` included — and
RELATIVE to an explicit contract that the run does not observe the plan's own callee record.
Standard axioms only.

## Status (November 2026): the review repair, and the instances that close M2

The independent review found three defects in the first version; two are repaired here in full,
the third by the instance modules.

1. **The tail premise was unsatisfiable** (`∀ v, InsertedOn P …` over EVERY receiver value and
   every `P` state; `PlanAlgorithmBridgeGuards.tailContractSelfReferenceDiffers`). REPAIRED: the
   tail contract is now asked only from the ADMISSIBLE TAIL ENTRIES of a value — `After E read v`,
   the states the production receiver read reaches from an entry state with result `v` — and at
   the ONE insertion the plan side holds there (`InsertedAt`). The self-reference is excluded by a
   proved fact, not by fiat: production's intrinsic over the plan cell's own reference RECORDS that
   cell's callee and so breaks `Frame` (`self_reference_records_callee`,
   `self_reference_breaks_frame_at_flight`, `tail_entry_not_self_reference`).
2. **The conclusion was the embedding equation only.** REPAIRED: every bridge concludes `Bridged` —
   the outcome equation AND `HeapInsertion.Inserted` at the final states. `Frame` there is proved
   (`production_frame`): two of its conjuncts follow from the heap discipline of every production
   run; the third — production records no callee for the plan cell — is the explicit PRESERVATION
   OBLIGATION `kread` / `ktail` (`KeepsOn … (Unrecorded a)`), which self-observation violates.
3. **No theorem instance existed.** REPAIRED, in three steps. `PlanAlgorithmBridgeInstances` applies
   the final theorems, every premise proved by the kernel, to reached states for a successful
   receiver read with a failing tail and for a failing receiver read, in both written forms, and
   checks the tail's two obligations for a call reference (satisfied, with production allocating
   past the insertion; violated by the self-reference). `PlanAlgorithmBridgeParameterInstances`
   proves a WHOLE-bridge instance whose receiver read returns a call reference, for both parameter
   forms, in an own-parameter supply context the kernel can evaluate. The closing pass
   (`PlanAlgorithmBridgeSourceInstances` and its companions `…SourceReceivers`, `…SourceOutcomes`,
   `…SourceEffects`, `…SourceAncestor`) applies the final theorems to GENUINE SOURCE PROGRAMS, both
   written forms each: the mandatory non-self-observing `R.Algorithm(0)` control, a structured
   failure, a captured-reference receiver, an alias receiver, an effectful receiver demanded twice
   and evaluated once, an address-bearing result, and a captured-ancestor parameter receiver. Those
   runs are beyond KERNEL evaluation (well-founded helpers behind `opaqueId`); their run equations
   are proved propositionally, by Lean's proof-producing evaluator `cbv` over the production
   definitions, from the three standard axioms.

## The contract and its domain

* **`InsertedOn P base count plan ρ mp mo`** (§ 6.2): from every production-side state satisfying
  `P` and every insertion of `count` cells at `base` with plan cell `plan`, the plan-side run from
  the plan-side state completes exactly when the production-side run does, with the production
  outcome shifted by `ρ` and the production final state under the SAME insertion. `InsertedAt D ι`
  is the same at ONE insertion `ι` from a domain `D`. `Simulates` is their general shape, of which
  `PlanConservativity.ObliviousOn` (the plan RECORD contract) is another instance
  (`simulates_of_obliviousOn`).
* **The admissible domain**: an ENTRY domain `E` holding the comparison state, and for each
  receiver VALUE `v` the tail entries `After E read v`. `After` is defined by the receiver
  computation alone — neither the plan side nor the insertion occurs in it.
* **The transfer** (`simulates_fuel`, `simulates_production`), mirroring `keeps_fuel`,
  `oblivious_fuel` and `oblivious_production`: over a call domain `Q`, a call map `κ` and a
  per-call outcome relation, if every evaluator BODY simulates whenever its recursive answer does
  (`BodySimulates`, with `BodyKeeps Q P`), then so does every completed run of the core at every
  fuel and every production operation.

## The bridges (§ 6.3)

`algorithm_core_bridge` composes the whole plan-side route — the establishment of
`NeedPlan.calleeCell` from the unrecorded state and its record in the plan cell; the receiver cell's
establishment and completion shell (`evaluating`, then the memoized outcome); the
captured-reference decoding and callee projection; the heap-read dispatch name and origin;
normalization, supply formation, dispatch, error context and result counting — against the
production core `algorithmCore`. `algorithm_bridge_dot` and `algorithm_bridge_grouped` identify that
core with the production entries (`dot_algorithm_run`, `link_call_run`);
`algorithm_bridge_grouped_settled` is the grouped form FROM ONE STATE (production's route decision
settled at the plan's flight). A PARAMETER receiver has its own theorems
(`algorithm_core_bridge_param`, `algorithm_bridge_dot_param`, `algorithm_bridge_grouped_param`): the
plan allocates the link alone (ONE inserted cell).

Three forms of each bridge, by where the contract premises come from:

* **at an entry domain** (`algorithm_bridge_*`): `InsertedAt` for the receiver read from `E` and for
  the tail from `After E read v`, with the preservation obligation and `PlanCallees`;
* **at ONE state** (`algorithm_bridge_*_at`): the singleton entry domain — every premise an equation
  between two runs or a decidable heap fact; the form a concrete state instantiates;
* **from an invariant `P`** (`algorithm_bridge_*_of_invariant`) and **from the per-body obligations**
  (`algorithm_bridge_*_of_bodies`: `BodyKeeps Q P`, `BodyInserted Q P`, and the call domain holding
  the calls production actually makes from `P` — `AlgorithmCalls`, scoped to reached probe answers
  and reached receiver results): the form the META-free programme discharges beside
  `BodyObliviousOn`, in one per-body pass under one invariant.

Corollaries: a structured failure is EQUAL on the two sides, payload and context chain
(`Bridged.failure_exact`); an address-free result is EQUAL with its count
(`Bridged.addressFree_exact`); the two sides complete together (`Bridged.completes`).

## Premises of the bridges, and which are established where

Structural and route premises (the plan cell holds the written invocation with its `.algorithm`
route recorded and its callee unrecorded; the receiver is no parameter — or, in the `_param`
theorems, a parameter bound to a cell of the comparison state that holds the read VALUE after
production's receiver read; production selects the intrinsic — explicit, because a receiver probe
may mint a runtime identity); `AddressInvariant.Inv` at the comparison state (every production run
preserves it); the contract for the two computations the sides share; the preservation obligation
(`Unrecorded`); `PlanCallees` at the tail entries (a fact of every reachable heap that no whole-run
theorem states yet); and completion of the PRODUCTION side only (the plan side's completion is
derived). No run equality and no receiver-resolution agreement is assumed.

NOT established for production in general: the contract, the preservation obligation and
`PlanCallees` — on an arbitrary reached state they are the META-free programme's per-body pass.
They ARE established, by the kernel, on the concrete states of `PlanAlgorithmBridgeInstances`, and
decided by the executable guards elsewhere.
-/

namespace KatLang.PlanAlgorithmBridge

open KatLang.HeapInsertion KatLang.PlanRouteBridge
open KatLang.PlanConservativity (Keeps BodyKeeps keeps_fuel ObliviousOn withPlan_empty)
open KatLang.WhileRoundProduction (Finite finite_const finite_call finite_bind production_eq_of_finite
  production_completes_iff_body)
open KatLang.FiniteLoop (finite_evalAttempt finite_nested finite_calleeCell ctxOutcome ctx_run ctxOutcome_fuel)

/-! ## The contract (§ 6.2) -/

/-- **The general two-run shape.** From every state `s` satisfying `P`, the plan-side run `mp` from
    `T s` completes exactly when the production-side run `mo` from `s` does, and then its outcome is
    related to production's by `R` and its final state is `T` of production's. -/
def Simulates {α β : Type} (P : EvalState → Prop) (T : EvalState → EvalState)
    (R : Except Error α → Except Error β → Prop) (mp : EvalM β) (mo : EvalM α) : Prop :=
  ∀ s, P s →
    ((mp.runState (T s)).1 = .error .fuelExhausted ↔ (mo.runState s).1 = .error .fuelExhausted) ∧
    ((mo.runState s).1 ≠ .error .fuelExhausted →
      R (mo.runState s).1 (mp.runState (T s)).1 ∧ (mp.runState (T s)).2 = T (mo.runState s).2)

/-- **THE NON-OBSERVATION CONTRACT.** From every production-side state satisfying `P` and every
    insertion of `count` cells at `base` with plan cell `plan`, whatever the inserted cells hold:
    the plan-side run `mp` completes exactly when the production-side run `mo` does, and a completed
    run has the production outcome with its value shifted by `ρ` (an error unchanged) and the
    production final state under the same insertion. A computation satisfies it exactly when it
    is insensitive to this embedding on the stated domain. This extensional property alone does not
    establish `Frame` at the final state: the bridges ask that separately (`KeepsOn … (Unrecorded a)`,
    `production_frame`). Reading or writing an unobserved record is not excluded syntactically. -/
def InsertedOn {α : Type} (P : EvalState → Prop) (base count plan : Nat) (ρ : Site → α → α)
    (mp mo : EvalM α) : Prop :=
  ∀ (ι : Insertion) (s : EvalState), ι.base = base → ι.cells.length = count → ι.plan = plan → P s →
    ((mp.runState (embed ι s)).1 = .error .fuelExhausted ↔ (mo.runState s).1 = .error .fuelExhausted) ∧
    ((mo.runState s).1 ≠ .error .fuelExhausted →
      mp.runState (embed ι s) = (shiftExcept (ρ ι.site) (mo.runState s).1, embed ι (mo.runState s).2))

/-- The contract is the general shape at the insertion's state transformation. -/
theorem insertedOn_iff_simulates {α : Type} (P : EvalState → Prop) (base count plan : Nat) (ρ : Site → α → α)
    (mp mo : EvalM α) :
    InsertedOn P base count plan ρ mp mo ↔
      ∀ ι : Insertion, ι.base = base → ι.cells.length = count → ι.plan = plan →
        Simulates P (embed ι) (fun o₁ o₂ => o₂ = shiftExcept (ρ ι.site) o₁) mp mo := by
  constructor
  · intro h ι hb hc hp s hP
    obtain ⟨h1, h2⟩ := h ι s hb hc hp hP
    refine ⟨h1, fun hne => ?_⟩
    have := h2 hne
    exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
  · intro h ι s hb hc hp hP
    obtain ⟨h1, h2⟩ := h ι hb hc hp s hP
    refine ⟨h1, fun hne => ?_⟩
    obtain ⟨ho, hs⟩ := h2 hne
    exact Prod.ext ho hs

/-- **The plan-record contract is the same shape.** `ObliviousOn P a m` — changing the plan record
    of `a` changes neither `m`'s outcome nor anything else — is, for every record `p`, the general
    shape at the state transformation `withPlan a p` with EQUAL outcomes. So ONE per-body pass can
    discharge it and the insertion contract side by side, over one call domain and one invariant. -/
theorem simulates_of_obliviousOn {α : Type} (P : EvalState → Prop) (a : Nat) (m : EvalM α)
    (h : ObliviousOn P a m) (p : NeedPlanSupply) :
    Simulates (fun s => P s ∧ a < s.needs.size) (withPlan a p) (fun o₁ o₂ => o₂ = o₁) m m := by
  intro s ⟨hP, hv⟩
  have e := h s p hP hv
  rw [e]
  exact ⟨Iff.rfl, fun _ => ⟨rfl, rfl⟩⟩

/-! ## The admissible domain

`InsertedOn P` asks its equation of EVERY insertion with the given base, count and plan cell, from
EVERY state of `P`. The bridges below do not ask that much, and must not: a premise quantified over
every receiver VALUE is false on the non-self-observing control
(`PlanAlgorithmBridgeGuards.tailContractSelfReferenceDiffers` — the value `callRef a` of the plan
cell itself makes production record that cell's callee). They ask the contract

* of the ONE insertion the plan side holds at that point (`InsertedAt`): its link and its receiver
  cell `evaluating` for the receiver read, the receiver cell completed with the read VALUE for the
  tail;
* for the receiver read, from the ENTRY domain `E` (the comparison states);
* for the tail over a VALUE `v`, from the ADMISSIBLE TAIL ENTRIES of `v` alone: the states the
  production receiver read reaches from an entry state with result `v` (`After E read v`).

`After` is defined by the receiver computation and its reachable results — not by the bridge's
conclusion: it mentions neither the plan side nor the insertion. A value the receiver read never
returns has no tail entry, so nothing is asked of it. -/

/-- **The reachable results of a computation.** `v` at `t` is a result of `m` from the domain `D`:
    some state of `D` runs `m` to the value `v` and the state `t`. -/
def After {α : Type} (D : EvalState → Prop) (m : EvalM α) (v : α) (t : EvalState) : Prop :=
  ∃ s, D s ∧ m.runState s = (.ok v, t)

theorem After.intro {α : Type} {D : EvalState → Prop} {m : EvalM α} {v : α} {s t : EvalState}
    (hD : D s) (h : m.runState s = (.ok v, t)) : After D m v t := ⟨s, hD, h⟩

/-- **THE CONTRACT AT ONE INSERTION**, from the production-side states of `D`: the plan-side run
    `mp` from the plan-side state completes exactly when the production-side run `mo` does, and a
    completed run has the production outcome with its value shifted by `ρ` (an error unchanged)
    and the production final state under the SAME insertion `ι`. `InsertedOn` is this at every
    insertion of a base, count and plan cell (`InsertedOn.at`). -/
def InsertedAt {α : Type} (D : EvalState → Prop) (ι : Insertion) (ρ : Site → α → α) (mp mo : EvalM α) : Prop :=
  ∀ s, D s →
    ((mp.runState (embed ι s)).1 = .error .fuelExhausted ↔ (mo.runState s).1 = .error .fuelExhausted) ∧
    ((mo.runState s).1 ≠ .error .fuelExhausted →
      mp.runState (embed ι s) = (shiftExcept (ρ ι.site) (mo.runState s).1, embed ι (mo.runState s).2))

theorem InsertedOn.at {α : Type} {P : EvalState → Prop} {base count plan : Nat} {ρ : Site → α → α}
    {mp mo : EvalM α} (h : InsertedOn P base count plan ρ mp mo) (ι : Insertion) (hb : ι.base = base)
    (hc : ι.cells.length = count) (hp : ι.plan = plan) : InsertedAt P ι ρ mp mo :=
  fun s hs => h ι s hb hc hp hs

/-- The contract is ANTITONE in its domain: a smaller domain asks less. -/
theorem InsertedAt.mono {α : Type} {D D' : EvalState → Prop} {ι : Insertion} {ρ : Site → α → α}
    {mp mo : EvalM α} (h : InsertedAt D ι ρ mp mo) (hsub : ∀ s, D' s → D s) : InsertedAt D' ι ρ mp mo :=
  fun s hs => h s (hsub s hs)

theorem InsertedOn.mono {α : Type} {P P' : EvalState → Prop} {base count plan : Nat} {ρ : Site → α → α}
    {mp mo : EvalM α} (h : InsertedOn P base count plan ρ mp mo) (hsub : ∀ s, P' s → P s) :
    InsertedOn P' base count plan ρ mp mo :=
  fun ι s hb hc hp hs => h ι s hb hc hp (hsub s hs)

/-- Production holds NO callee record for the plan cell: the third conjunct of
    `HeapInsertion.Frame`, the one a run can break (the other two — the plan cell below the
    insertion, the heap reaching it — follow from the heap discipline of every production run). -/
def Unrecorded (plan : Nat) (s : EvalState) : Prop := (s.needs[plan]?).bind NeedCell.callee = none

instance (plan : Nat) (s : EvalState) : Decidable (Unrecorded plan s) := by
  unfold Unrecorded; infer_instance

/-- From the states of `D`, a completed run of `m` ends in a state of `G`
    (`PlanConservativity.Keeps P` is `KeepsOn P P`). -/
def KeepsOn {α : Type} (D G : EvalState → Prop) (m : EvalM α) : Prop :=
  ∀ s, D s → (m.runState s).1 ≠ .error .fuelExhausted → G (m.runState s).2

theorem keepsOn_of_keeps {α : Type} {P : EvalState → Prop} {m : EvalM α} (h : Keeps P m) : KeepsOn P P m := h

theorem KeepsOn.mono {α : Type} {D D' G G' : EvalState → Prop} {m : EvalM α} (h : KeepsOn D G m)
    (hD : ∀ s, D' s → D s) (hG : ∀ s, G s → G' s) : KeepsOn D' G' m :=
  fun s hs hne => hG _ (h s (hD s hs) hne)

/-- A reachable result of a computation that keeps `P` is reached at a state of `P`. -/
theorem After.keeps {α : Type} {P : EvalState → Prop} {m : EvalM α} (hk : Keeps P m) {v : α} {t : EvalState}
    (h : After P m v t) : P t := by
  obtain ⟨s, hs, hr⟩ := h
  have := hk s hs (by rw [hr]; nofun)
  rw [hr] at this
  exact this

/-- The heap discipline bounds the heap's size from below. -/
theorem heapKept_size {h h' : Array NeedCell} (k : HeapKept h h') : h.size ≤ h'.size := by
  rcases Nat.eq_zero_or_pos h.size with h0 | hpos
  · omega
  · have hlt : h.size - 1 < h.size := by omega
    obtain ⟨c', hc', _⟩ := k (h.size - 1) h[h.size - 1] (Array.getElem?_eq_getElem hlt)
    have := valid_of_get hc'
    omega

/-- **THE BRIDGE'S CONCLUSION**: the plan-side outcome is production's with its value shifted past
    the inserted cells (an error unchanged), and the two final states are in THE relation
    `HeapInsertion.Inserted` — `Frame` at production's final state AND the embedding equation. -/
def Bridged (ι : Insertion) (plan prod : Except Error CountedResult × EvalState) : Prop :=
  plan.1 = shiftExcept (shiftCounted ι.site) prod.1 ∧ Inserted ι plan.2 prod.2

theorem Bridged.run_eq {ι : Insertion} {plan prod : Except Error CountedResult × EvalState}
    (h : Bridged ι plan prod) : plan = (shiftExcept (shiftCounted ι.site) prod.1, embed ι prod.2) :=
  Prod.ext h.1 h.2.2

theorem Bridged.frame {ι : Insertion} {plan prod : Except Error CountedResult × EvalState}
    (h : Bridged ι plan prod) : Frame ι.base ι.plan prod.2 := h.2.1

/-! ## The transfer (§ 6.2) -/

/-- The per-body obligation of a simulation: over the call domain `Q`, the call map `κ` (the
    plan-side call of a production-side call) and the per-call outcome relation `R`, every evaluator
    body simulates whenever its recursive answer does and keeps `P`. -/
def BodySimulates (Q : EvalCall → Prop) (P : EvalState → Prop) (T : EvalState → EvalState)
    (κ : EvalCall → EvalCall) (R : (c : EvalCall) → Except Error c.Ret → Except Error (κ c).Ret → Prop) : Prop :=
  ∀ recp reco : EvalRec, (∀ c, Q c → Keeps P (reco c)) →
    (∀ c, Q c → Simulates P T (R c) (recp (κ c)) (reco c)) →
    ∀ c, Q c → Simulates P T (R c) (evalStep recp (κ c)) (evalStep reco c)

theorem simulates_normalize {α β : Type} (P : EvalState → Prop) (T : EvalState → EvalState)
    (R : Except Error α → Except Error β → Prop) (mp : EvalM β) (mo : EvalM α)
    (h : Simulates P T R mp mo) : Simulates P T R mp.normalizeIncomplete mo.normalizeIncomplete := by
  intro s hP
  obtain ⟨hiff, hrun⟩ := h s hP
  by_cases hc : (mo.runState s).1 = .error .fuelExhausted
  · have hcp := hiff.2 hc
    rw [normalize_of_incomplete mo s hc, normalize_of_incomplete mp (T s) hcp]
    exact ⟨⟨fun _ => rfl, fun _ => rfl⟩, fun hne => absurd rfl hne⟩
  · have hcp : (mp.runState (T s)).1 ≠ .error .fuelExhausted := fun hp => hc (hiff.1 hp)
    rw [normalize_of_complete mo s hc, normalize_of_complete mp (T s) hcp]
    exact ⟨hiff, hrun⟩

/-- **The transfer, at every fuel.** The same fuel index serves both sides: the two core runs are
    incomplete together or complete together, related. -/
theorem simulates_fuel (Q : EvalCall → Prop) (P : EvalState → Prop) (T : EvalState → EvalState)
    (κ : EvalCall → EvalCall) (R : (c : EvalCall) → Except Error c.Ret → Except Error (κ c).Ret → Prop)
    (hkeep : BodyKeeps Q P) (hbody : BodySimulates Q P T κ R) :
    ∀ n c, Q c → Simulates P T (R c) (evalFuel n (κ c)) (evalFuel n c) := by
  intro n
  induction n with
  | zero =>
    intro c _ s _
    exact ⟨⟨fun _ => rfl, fun _ => rfl⟩, fun hne => absurd rfl hne⟩
  | succ n ih =>
    intro c hq
    exact simulates_normalize P T (R c) _ _ (hbody _ _ (keeps_fuel Q P hkeep n) ih c hq)

/-- **The transfer to production.** Under the per-body obligations, every production operation of
    the domain simulates: the plan-side production run of the mapped call completes exactly when
    the production-side run does — whatever administrative depth either is reached at — with
    related outcomes and final states. -/
theorem simulates_production (Q : EvalCall → Prop) (P : EvalState → Prop) (T : EvalState → EvalState)
    (κ : EvalCall → EvalCall) (R : (c : EvalCall) → Except Error c.Ret → Except Error (κ c).Ret → Prop)
    (hkeep : BodyKeeps Q P) (hbody : BodySimulates Q P T κ R) (c : EvalCall) (hq : Q c) :
    Simulates P T (R c) (evalUnbounded (κ c)) (evalUnbounded c) := by
  intro s hP
  have hfuel := fun m => simulates_fuel Q P T κ R hkeep hbody m c hq s hP
  by_cases hc : ProductionCompletes (evalUnbounded c) s
  · obtain ⟨m, hr, hm⟩ := (production_completes_iff c s _).1 ⟨rfl, hc⟩
    have hne : ((evalFuel m c).runState s).1 ≠ .error .fuelExhausted := (evalFuel_completes_iff m c s).1 hm
    obtain ⟨hiff, hrun⟩ := hfuel m
    have hnep : ((evalFuel m (κ c)).runState (T s)).1 ≠ .error .fuelExhausted := fun hp => hne (hiff.1 hp)
    have hmp : Completes (evalFuel m (κ c)) (T s) := (evalFuel_completes_iff m (κ c) (T s)).2 hnep
    obtain ⟨hprod, hpc⟩ := (production_completes_iff (κ c) (T s) _).2 ⟨m, rfl, hmp⟩
    rw [hprod, ← hr]
    exact ⟨⟨fun hp => absurd hp hnep, fun ho => absurd ho hne⟩, fun _ => hrun hne⟩
  · have hs := production_incomplete_state c s hc
    have hcp : ¬ ProductionCompletes (evalUnbounded (κ c)) (T s) := by
      intro hcp
      obtain ⟨m, _, hm⟩ := (production_completes_iff (κ c) (T s) _).1 ⟨rfl, hcp⟩
      have hnep : ((evalFuel m (κ c)).runState (T s)).1 ≠ .error .fuelExhausted :=
        (evalFuel_completes_iff m (κ c) (T s)).1 hm
      obtain ⟨hiff, _⟩ := hfuel m
      have hne : ((evalFuel m c).runState s).1 ≠ .error .fuelExhausted := fun ho => hnep (hiff.2 ho)
      exact hc ((production_completes_iff c s _).2 ⟨m, rfl, (evalFuel_completes_iff m c s).2 hne⟩).2
    rw [hs, production_incomplete_state (κ c) (T s) hcp]
    exact ⟨⟨fun _ => rfl, fun _ => rfl⟩, fun hne => absurd rfl hne⟩

/-! ## The production core of both written forms -/

/-- The fresh call of a captured callee over production operations (`algorithmOfValue` with an
    argument list, unfolded): the decoded plan, its canonical callee cell, that cell's CALLABLE, the
    plan's callee name, and the production resolved call with origin `.cell`. -/
def capturedCall (val : Result) (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) : EvalM CountedResult := do
  let plan ← decodeCallRef val
  let callee ← NeedPlan.calleeCell productionPlanRoute.classify plan
  let algorithm ← capturedCallee callee
  let name ← NeedPlan.calleeName plan
  evalResolvedCallCounted algorithm args ctx env name (.cell callee)

theorem finite_algorithmOfValue (val : Result) (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) :
    Finite (fun rec : EvalRec => EvalBody.algorithmOfValue rec val (some args) ctx env) := by
  unfold EvalBody.algorithmOfValue
  refine finite_bind (finite_const _) (fun plan => ?_)
  refine finite_bind (finite_calleeCell plan) (fun callee => ?_)
  dsimp only
  refine finite_bind (B := fun rec : EvalRec => rec (.capturedCallee callee)) (finite_call _) (fun algorithm => ?_)
  exact finite_bind (finite_const _) (fun name => finite_call _)

/-- **`algorithmOfValue` IS the captured call**, wherever either completes (the finite-use
    converse of `algorithm_of_value_run`: no completion premise on the production operation). -/
theorem algorithmOfValue_eq (val : Result) (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) (s : EvalState)
    (hc : ProductionCompletes (capturedCall val args ctx env) s) :
    (algorithmOfValue val (some args) ctx env).runState s = (capturedCall val args ctx env).runState s :=
  production_eq_of_finite (.algorithmOfValue val (some args) ctx env)
    (fun rec => EvalBody.algorithmOfValue rec val (some args) ctx env) (fun _ => rfl)
    (finite_algorithmOfValue val args ctx env) s hc

theorem algorithmOfValue_completes_iff (val : Result) (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv)
    (s : EvalState) :
    ProductionCompletes (algorithmOfValue val (some args) ctx env) s ↔
      ProductionCompletes (capturedCall val args ctx env) s :=
  production_completes_iff_body (.algorithmOfValue val (some args) ctx env)
    (fun rec => EvalBody.algorithmOfValue rec val (some args) ctx env) (fun _ => rfl)
    (finite_algorithmOfValue val args ctx env) s

/-- **The production core of an `.Algorithm` invocation**, shared by both written forms: the
    invocation receiver read (the identity probe and the intrinsic's receiver read,
    `invocationReceiverValue_eq`), then the `.Algorithm` intrinsic over that VALUE with the written
    argument list. -/
def algorithmCore (receiver : Expr) (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) : EvalM CountedResult :=
  invocationReceiverValue receiver ctx env >>= fun v => algorithmOfValue v (some args) ctx env

/-- **The dot form IS the core.** When production's own receiver probe selects the `.Algorithm`
    intrinsic, the production dot evaluation `target.Algorithm(args)` is the core under
    `CtxMsg.dotCall target Algorithm`, from the SAME state (the probe is the core's first step). -/
theorem dot_is_core (target fallback : Expr) (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv)
    (s s' : EvalState) (alg? : Option Algorithm)
    (hprobe : (resolveDotReceiver? target ctx).runState s = (.ok alg?, s'))
    (hmiss : selectDotEdge ctx target "Algorithm" alg? = .ok (.miss .algorithm))
    (hc : ProductionCompletes (evalCounted (.dotMember target "Algorithm" fallback (some args)) ctx env) s) :
    (evalCounted (.dotMember target "Algorithm" fallback (some args)) ctx env).runState s =
      ctxOutcome (CtxMsg.dotCall target "Algorithm") ((algorithmCore target args ctx env).runState s) := by
  have hcore : (algorithmCore target args ctx env).runState s =
      (algorithmReceiverValue target alg? ctx env >>= fun val =>
        algorithmOfValue val (some args) ctx env).runState s' := by
    unfold algorithmCore
    rw [invocationReceiverValue_eq, EvalM.bind_assoc, bind_run, hprobe]
  rw [dot_algorithm_run target fallback (some args) ctx env s s' alg? hprobe hmiss hc, hcore]

/-- The production callee read of a grouped call over production operations. -/
theorem algorithmCalleeOf_run (receiver : Expr) (ctx : EvalCtx) (env : ValEnv) (s : EvalState)
    (hc : ProductionCompletes (algorithmCalleeOf receiver ctx env) s) :
    (algorithmCalleeOf receiver ctx env).runState s =
      (do let value ← invocationReceiverValue receiver ctx env
          let plan ← decodeCallRef value
          let cell ← NeedPlan.calleeCell productionPlanRoute.classify plan
          let callee ← capturedCallee cell
          let name ← NeedPlan.calleeName plan
          pure (callee, name, cell)).runState s := by
  have hu := production_unfolds (.algorithmCalleeOf receiver ctx env) s hc
  change (evalUnbounded (.algorithmCalleeOf receiver ctx env)).runState s = _
  rw [← hu]
  rfl

/-- **The grouped form IS the core.** Once production's route decision answers `true` at `s₁`, the
    production call `(receiver.Algorithm)(args)` is the core under `CtxMsg.call f`, run from `s₁`. -/
theorem grouped_is_core (f receiver fallback : Expr) (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv)
    (s s₁ : EvalState) (hl : linkEdge? f = some (receiver, fallback))
    (hroute : (withCtx (CtxMsg.call f) (algorithmIntrinsicRoute receiver ctx)).runState s = (.ok true, s₁))
    (hc : ProductionCompletes (evalCallCountedExpr f args ctx env) s) :
    (evalCallCountedExpr f args ctx env).runState s =
      ctxOutcome (CtxMsg.call f) ((algorithmCore receiver args ctx env).runState s₁) := by
  have hrun := link_call_run f receiver fallback args ctx env s s₁ hl hroute hc
  rw [KatLang.DotFunnel.withCtx_bind, ctx_run] at hrun
  rw [hrun]
  congr 1
  -- the framed composite completes, because the whole call does
  have hcomp : ((algorithmCalleeOf receiver ctx env >>= fun found =>
      evalResolvedCallCounted found.1 args ctx env found.2.1 (.cell found.2.2)).runState s₁).1 ≠
      .error .fuelExhausted := by
    unfold ProductionCompletes at hc
    rw [hrun] at hc
    exact (ctxOutcome_fuel _ _).1 hc
  have hcal : ProductionCompletes (algorithmCalleeOf receiver ctx env) s₁ := by
    intro hinc
    apply hcomp
    rw [bind_run]
    rcases hr : (algorithmCalleeOf receiver ctx env).runState s₁ with ⟨o, t⟩
    rw [hr] at hinc
    simp only at hinc
    subst hinc
    rfl
  rw [bind_run, algorithmCalleeOf_run receiver ctx env s₁ hcal] at hcomp ⊢
  unfold algorithmCore
  simp only [bind_run] at hcomp ⊢
  rcases hv : (invocationReceiverValue receiver ctx env).runState s₁ with ⟨ov, s₂⟩
  rw [hv] at hcomp
  cases ov with
  | error e => rfl
  | ok value =>
    dsimp only at hcomp ⊢
    have hexp : ((capturedCall value args ctx env).runState s₂).1 ≠ .error .fuelExhausted ∧
        (match (decodeCallRef value).runState s₂ with
         | (.ok plan, t₁) =>
           (match (NeedPlan.calleeCell productionPlanRoute.classify plan).runState t₁ with
            | (.ok cell, t₂) =>
              (match (capturedCallee cell).runState t₂ with
               | (.ok callee, t₃) =>
                 (match (NeedPlan.calleeName plan).runState t₃ with
                  | (.ok name, t₄) =>
                    (evalResolvedCallCounted (callee, name, cell).1 args ctx env (callee, name, cell).2.1
                      (.cell (callee, name, cell).2.2)).runState t₄
                  | (.error e, t₄) => (.error e, t₄))
               | (.error e, t₃) => (.error e, t₃))
            | (.error e, t₂) => (.error e, t₂))
         | (.error e, t₁) => (.error e, t₁)) = (capturedCall value args ctx env).runState s₂ := by
      have heq : (match (decodeCallRef value).runState s₂ with
         | (.ok plan, t₁) =>
           (match (NeedPlan.calleeCell productionPlanRoute.classify plan).runState t₁ with
            | (.ok cell, t₂) =>
              (match (capturedCallee cell).runState t₂ with
               | (.ok callee, t₃) =>
                 (match (NeedPlan.calleeName plan).runState t₃ with
                  | (.ok name, t₄) =>
                    (evalResolvedCallCounted (callee, name, cell).1 args ctx env (callee, name, cell).2.1
                      (.cell (callee, name, cell).2.2)).runState t₄
                  | (.error e, t₄) => (.error e, t₄))
               | (.error e, t₃) => (.error e, t₃))
            | (.error e, t₂) => (.error e, t₂))
         | (.error e, t₁) => (.error e, t₁)) = (capturedCall value args ctx env).runState s₂ := by
        unfold capturedCall
        simp only [bind_run]
        rcases (decodeCallRef value).runState s₂ with ⟨_ | plan, t₁⟩
        · rfl
        · dsimp only
          rcases (NeedPlan.calleeCell productionPlanRoute.classify plan).runState t₁ with ⟨_ | cell, t₂⟩
          · rfl
          · dsimp only
            rcases (capturedCallee cell).runState t₂ with ⟨_ | callee, t₃⟩
            · rfl
            · dsimp only
              rcases (NeedPlan.calleeName plan).runState t₃ with ⟨_ | name, t₄⟩ <;> rfl
      refine ⟨?_, heq⟩
      rw [← heq]
      revert hcomp
      rcases (decodeCallRef value).runState s₂ with ⟨_ | plan, t₁⟩
      · exact id
      · dsimp only
        rcases (NeedPlan.calleeCell productionPlanRoute.classify plan).runState t₁ with ⟨_ | cell, t₂⟩
        · exact id
        · dsimp only
          rcases (capturedCallee cell).runState t₂ with ⟨_ | callee, t₃⟩
          · exact id
          · dsimp only
            rcases (NeedPlan.calleeName plan).runState t₃ with ⟨_ | name, t₄⟩
            · exact id
            · exact id
    rw [algorithmOfValue_eq value args ctx env s₂ hexp.1, ← hexp.2]
    rcases (decodeCallRef value).runState s₂ with ⟨_ | plan, t₁⟩
    · rfl
    · dsimp only
      rcases (NeedPlan.calleeCell productionPlanRoute.classify plan).runState t₁ with ⟨_ | cell, t₂⟩
      · rfl
      · dsimp only
        rcases (capturedCallee cell).runState t₂ with ⟨_ | callee, t₃⟩
        · rfl
        · dsimp only
          rcases (NeedPlan.calleeName plan).runState t₃ with ⟨_ | name, t₄⟩ <;> rfl

/-! ## The plan side: the inserted cells -/

open KatLang.AddressInvariant (Inv)
open KatLang.AlgorithmProjectionLaws

/-- **A recorded callee belongs to a plan cell.** `NeedPlan.calleeCell` records a callee only after
    reading the cell as a written invocation, and a suspension is never rewritten; it is a fact of
    every reachable heap that the bridges ask of the invariant `P` (no whole-run theorem states it
    yet). Without it the planned dispatch NAME could differ from the intrinsic's on a malformed heap:
    the intrinsic refuses a decoded cell that is no plan (`NeedPlan.calleeName`), the plan's heap
    read falls back to the written link (`NeedPlan.dispatchNameIn`). -/
def PlanCallees (s : EvalState) : Prop :=
  ∀ (b : Nat) (cell : NeedCell), s.needs[b]? = some cell → cell.callee.isSome →
    (NeedPlan.ofSuspension? cell.suspension).isSome

/-- The plan's callee link `receiver.Algorithm` once its receiver cell is recorded. -/
def linkCell (edge : Expr) (ctx : EvalCtx) (env : ValEnv) (receiver : Nat) : NeedCell :=
  { suspension := .expression edge ctx env, invocation := .link, receiver := some receiver }

/-- The link's retained receiver cell (`NeedInvocationRole.receiver`) in VALUE state `st`. -/
def receiverCellOf (edge : Expr) (ctx : EvalCtx) (env : ValEnv) (st : NeedState) : NeedCell :=
  { suspension := .expression edge ctx env, invocation := .receiver, state := st }

/-- **The insertion of a planned `.Algorithm` invocation over a non-parameter receiver**: at `base`,
    the callee link — its receiver cell recorded — and that receiver cell in VALUE state `st`; the
    plan cell `plan` records the link. -/
def planInsertion (base plan : Nat) (edge : Expr) (ctx : EvalCtx) (env : ValEnv) (st : NeedState) : Insertion :=
  ⟨base, [linkCell edge ctx env (base + 1), receiverCellOf edge ctx env st], plan⟩

theorem planInsertion_site (base plan : Nat) (edge : Expr) (ctx : EvalCtx) (env : ValEnv) (st : NeedState) :
    (planInsertion base plan edge ctx env st).site = ⟨base, 2⟩ := rfl

/-- The heap the plan side builds by establishing its link and receiver cells, as an insertion at
    the heap's end. -/
theorem plan_heap (h : Array NeedCell) (a : Nat) (ha : a < h.size) (L0 R0 : NeedCell) :
    ((((h.push L0).modify h.size (fun c => { c with invocation := NeedInvocationRole.link })).modify a
        (fun c => { c with callee := some h.size })).push R0).modify h.size
        (fun c => { c with receiver := some (h.size + 1) }) =
      ((h.toList.modify a (fun c => { c with callee := some h.size })) ++
        [{ L0 with invocation := NeedInvocationRole.link, receiver := some (h.size + 1) }, R0]).toArray := by
  apply Array.ext_getElem?
  intro i
  simp only [List.getElem?_toArray, List.getElem?_append, List.length_modify, Array.length_toList,
    List.getElem?_modify, Array.getElem?_toList, Array.getElem?_modify, Array.getElem?_push, Array.size_push,
    Array.size_modify]
  by_cases h1 : i < h.size
  · have h2 : ¬ i = h.size := by omega
    have h3 : ¬ h.size = i := by omega
    have h4 : ¬ i = h.size + 1 := by omega
    simp only [h1, h2, h3, h4, ite_true, ite_false]
    by_cases h5 : a = i
    · subst h5
      cases h[a]? <;> simp
    · simp [h5]
  · by_cases h2 : i = h.size
    · subst h2
      have h3 : ¬ a = h.size := by omega
      simp [h3]
    · by_cases h4 : i = h.size + 1
      · subst h4
        have h5 : ¬ a = h.size + 1 := by omega
        simp [h5]
      · have h5 : ¬ a = i := by omega
        have h6 : ¬ h.size = i := fun e => h2 e.symm
        have h7 : h.size ≤ i := by omega
        have h10 : ([{ L0 with invocation := NeedInvocationRole.link, receiver := some (h.size + 1) }, R0] :
            List NeedCell)[i - h.size]? = none := List.getElem?_eq_none (by simp; omega)
        simp [h1, h2, h4, h5, h6, h10]

theorem linkEdge_algorithm (receiver fallback : Expr) :
    linkEdge? (.dotMember receiver "Algorithm" fallback none) = some (receiver, fallback) := by
  simp [linkEdge?]

/-- **The plan side's establishment** (CR-13, D-3). From a valid state where the plan cell `a` holds a
    written `.Algorithm` invocation over a non-parameter receiver, its `.algorithm` route recorded and
    its callee unrecorded: the canonical callee cell is a FRESH link at the heap's end, marked and
    recorded in `a`; the link's receiver cell is ONE more fresh cell over the link's own edge, marked
    and recorded in the link. Nothing is evaluated, and the resulting state is the entry state under
    the plan's insertion at its heap size. -/
theorem establish_run (a : Nat) (x : EvalState) (ca : NeedCell) (shape : NeedPlan.CallShape)
    (receiver fallback : Expr) (hinv : Inv x) (ha : x.needs[a]? = some ca) (hnone : ca.callee = none)
    (hshape : NeedPlan.ofSuspension? ca.suspension = some shape) (hroute : ca.route = some .algorithm)
    (hedge : shape.callee = .dotMember receiver "Algorithm" fallback none) (hnp : ∀ p, receiver ≠ .param p) :
    ∃ x₁, (NeedPlan.calleeCell productionPlanRoute.classify a).runState x = (.ok x.needs.size, x₁) ∧
      (NeedLink.receiverCell x.needs.size).runState x₁ =
        (.ok (x.needs.size + 1),
          embed (planInsertion x.needs.size a shape.callee shape.caller shape.values .suspended) x) := by
  have hlt : a < x.needs.size := valid_of_get ha
  have hne : ¬ a = x.needs.size := by omega
  have hlink : linkEdge? shape.callee = some (receiver, fallback) := by rw [hedge]; exact linkEdge_algorithm _ _
  have hnparam : ∀ name, shape.callee ≠ .param name := by rw [hedge]; intro n h; cases h
  have hcal := calleeCell_establishes productionPlanRoute.classify a x ca shape .algorithm ha hnone hshape hroute
    (by decide)
  have heff : NeedPlan.effective shape .algorithm = shape := rfl
  rw [heff, supplyCallee_run, KatLang.NeedControl.Allocation.supply_nonparameter shape.callee shape.caller
    shape.values x hnparam] at hcal
  have hmark : markLink shape .algorithm x.needs.size
      { x with needs := x.needs.push { suspension := .expression shape.callee shape.caller shape.values } } =
      withInvocation x.needs.size .link
        { x with needs := x.needs.push { suspension := .expression shape.callee shape.caller shape.values } } := by
    unfold markLink
    rw [hlink]
    rfl
  dsimp only at hcal
  rw [hmark] at hcal
  refine ⟨_, hcal, ?_⟩
  -- the link cell the callee establishment leaves at the heap's end
  have hk : NeedLink.keepsInvocationReceiver NeedInvocationRole.link receiver = true := by
    cases receiver <;> first | rfl | exact absurd rfl (hnp _)
  have hcell : ({ (withInvocation x.needs.size .link
        { x with needs := x.needs.push { suspension := .expression shape.callee shape.caller shape.values } }) with
        needs := (withInvocation x.needs.size .link
          { x with needs := x.needs.push { suspension := .expression shape.callee shape.caller shape.values } }).needs.modify a
            (fun cell => { cell with callee := some x.needs.size }) } : EvalState).needs[x.needs.size]? =
      some ({ suspension := .expression shape.callee shape.caller shape.values, invocation := .link } : NeedCell) := by
    simp only [withInvocation]
    rw [Array.getElem?_modify, Array.getElem?_modify, Array.getElem?_push]
    simp only [hne, ite_false, ite_true, Option.map_some]
  rw [receiverCell_establishes_invocation x.needs.size _ _ shape.callee receiver fallback shape.caller shape.values
    hcell rfl rfl hlink hk]
  rw [embed_of_valid _ x hinv rfl]
  simp only [withInvocation, Array.size_modify, Array.size_push]
  congr 1
  exact congrArg (fun needs => ({ x with needs := needs } : EvalState))
    (plan_heap x.needs a hlt { suspension := .expression shape.callee shape.caller shape.values }
      (invocationReceiverCell shape.callee shape.caller shape.values))

/-! ## The receiver cell's completion shell -/

/-- The finite-use converse of `production_unfolds` at ONE state: a body that reaches its production
    outcome at some fuel there has, when that outcome is complete, exactly it as the operation's. -/
theorem production_eq_of_reached (c : EvalCall) (B : EvalRec → EvalM c.Ret)
    (hstep : ∀ rec, evalStep rec c = B rec) (s : EvalState) (m : Nat)
    (hm : (B (evalFuel m)).runState s = (B evalUnbounded).runState s)
    (hc : ProductionCompletes (B evalUnbounded) s) :
    (evalUnbounded c).runState s = (B evalUnbounded).runState s := by
  have hne : ((B (evalFuel m)).runState s).1 ≠ .error .fuelExhausted := by rw [hm]; exact hc
  have hfuel : (evalFuel (m + 1) c).runState s = (B evalUnbounded).runState s := by
    rw [evalFuel_succ, hstep, normalize_of_complete _ s hne, hm]
  exact ((production_completes_iff c s _).2
    ⟨m + 1, hfuel, (evalFuel_completes_iff (m + 1) c s).2 (by rw [hfuel]; exact hc)⟩).1

/-- What the VALUE completion shell makes of its computation's run: an incomplete outcome
    propagates and completes nothing; a completed outcome — success or ordinary failure — is
    returned and memoized in the cell. -/
def shellOutcome (a : Nat) (r : Except Error CountedResult × EvalState) : Except Error CountedResult × EvalState :=
  if r.1.isIncomplete then (.error .fuelExhausted, r.2) else (r.1, withState a (.completed r.1) r.2)

/-- **The shell of a suspended expression cell that is no plan**: mark `evaluating`, run the written
    expression's evaluator, memoize the outcome. -/
theorem step_expression_run (ev : Expr → EvalCtx → ValEnv → EvalM CountedResult) (route : NeedPlan.Route)
    (demand : Nat → EvalM CountedResult) (a : Nat) (s : EvalState) (cell : NeedCell) (e : Expr) (c : EvalCtx)
    (v : ValEnv) (hc : s.needs[a]? = some cell) (hs : cell.state = .suspended)
    (hsus : cell.suspension = .expression e c v) (hplan : NeedPlan.callShape? e c v = none) :
    (NeedDemand.step ev route demand a).runState s =
      shellOutcome a ((reCountValueBoundary <$> ev e c v).runState (withState a .evaluating s)) := by
  have hv : NeedDemand.suspendedValue ev route demand a cell.suspension = reCountValueBoundary <$> ev e c v := by
    rw [hsus]; exact suspended_other_is_ordinary ev route demand a e c v hplan
  rcases hr : (reCountValueBoundary <$> ev e c v).runState (withState a .evaluating s) with ⟨o, t⟩
  have hr' : (NeedDemand.suspendedValue ev route demand a cell.suspension).runState
      { s with needs := s.needs.modify a (fun c => { c with state := .evaluating }) } = (o, t) := by
    rw [hv]; exact hr
  unfold shellOutcome
  cases hinc : o.isIncomplete with
  | true =>
    rw [KatLang.NeedControl.Memo.suspended_incomplete ev route demand a s t cell o hc hs hr' hinc]
    rfl
  | false =>
    rw [KatLang.NeedControl.Memo.suspended_retains_state ev route demand a s t cell o hc hs hr' hinc]
    rfl

/-- **The production VALUE demand of such a cell**, with no completion premise on the demand itself:
    when the cell's written-expression evaluator completes from the `evaluating` state, the
    production demand is the shell over that run. -/
theorem demand_expression_run (a : Nat) (s : EvalState) (cell : NeedCell) (e : Expr) (c : EvalCtx) (v : ValEnv)
    (hc : s.needs[a]? = some cell) (hs : cell.state = .suspended)
    (hsus : cell.suspension = .expression e c v) (hplan : NeedPlan.callShape? e c v = none)
    (hcomp : ProductionCompletes (evalSuppliedAt a e c v) (withState a .evaluating s)) :
    (demandNeedRecursive a).runState s =
      shellOutcome a ((reCountValueBoundary <$> evalSuppliedAt a e c v).runState (withState a .evaluating s)) := by
  have hB : ∀ rec : EvalRec,
      (NeedDemand.step (rec.evalSuppliedAt a) rec.planRoute rec.demandNeedRecursive a).runState s =
        shellOutcome a ((reCountValueBoundary <$> rec (.evalSuppliedAt a e c v)).runState (withState a .evaluating s)) :=
    fun rec => step_expression_run _ _ _ a s cell e c v hc hs hsus hplan
  obtain ⟨m, hr, _⟩ := (production_completes_iff (.evalSuppliedAt a e c v) (withState a .evaluating s) _).1 ⟨rfl, hcomp⟩
  have hU := hB evalUnbounded
  have hm : ((fun rec : EvalRec => NeedDemand.step (rec.evalSuppliedAt a) rec.planRoute rec.demandNeedRecursive a)
      (evalFuel m)).runState s =
      ((fun rec : EvalRec => NeedDemand.step (rec.evalSuppliedAt a) rec.planRoute rec.demandNeedRecursive a)
        evalUnbounded).runState s := by
    show (NeedDemand.step ((evalFuel m).evalSuppliedAt a) (evalFuel m).planRoute (evalFuel m).demandNeedRecursive a).runState s = _
    rw [hB (evalFuel m)]
    show _ = (NeedDemand.step (EvalRec.evalSuppliedAt evalUnbounded a) (EvalRec.planRoute evalUnbounded)
      (EvalRec.demandNeedRecursive evalUnbounded) a).runState s
    rw [hU, map_run, map_run, hr]
  have hcB : ProductionCompletes ((fun rec : EvalRec =>
      NeedDemand.step (rec.evalSuppliedAt a) rec.planRoute rec.demandNeedRecursive a) evalUnbounded) s := by
    unfold ProductionCompletes
    show ((NeedDemand.step (EvalRec.evalSuppliedAt evalUnbounded a) (EvalRec.planRoute evalUnbounded)
      (EvalRec.demandNeedRecursive evalUnbounded) a).runState s).1 ≠ _
    rw [hU, map_run]
    unfold ProductionCompletes at hcomp
    have hrun : (evalUnbounded (.evalSuppliedAt a e c v)).runState (withState a .evaluating s) =
        (evalSuppliedAt a e c v).runState (withState a .evaluating s) := rfl
    rw [hrun]
    revert hcomp
    rcases (evalSuppliedAt a e c v).runState (withState a .evaluating s) with ⟨o, t⟩
    intro hcomp
    cases o with
    | ok r => unfold shellOutcome; nofun
    | error err =>
      cases err <;> first | exact absurd rfl hcomp | (unfold shellOutcome; nofun)
  exact (production_eq_of_reached (.demandNeedRecursive a)
    (fun rec => NeedDemand.step (rec.evalSuppliedAt a) rec.planRoute rec.demandNeedRecursive a)
    (fun _ => rfl) s m hm hcB).trans hU

theorem finite_invocationReceiverValue (receiver : Expr) (ctx : EvalCtx) (env : ValEnv) :
    Finite (fun rec : EvalRec => EvalBody.invocationReceiverValue rec receiver ctx env) := by
  unfold EvalBody.invocationReceiverValue
  refine finite_bind (B := fun rec : EvalRec => rec (.resolveDotReceiver? receiver ctx)) (finite_call _) (fun alg? => ?_)
  cases alg? with
  | none => exact finite_nested (B := fun rec : EvalRec => rec (.eval receiver ctx env)) (finite_call _)
  | some targetAlg => exact finite_call _

theorem finite_evalSuppliedAt (address : Nat) (e : Expr) (ctx : EvalCtx) (env : ValEnv) :
    Finite (fun rec : EvalRec => EvalBody.evalSuppliedAt rec address e ctx env) := by
  unfold EvalBody.evalSuppliedAt
  cases linkEdge? e with
  | none => exact finite_call _
  | some edge =>
    dsimp only
    refine finite_bind (finite_const _) (fun isReceiver => ?_)
    cases isReceiver with
    | true =>
      exact finite_bind (finite_invocationReceiverValue edge.1 ctx env) (fun _ => finite_const _)
    | false =>
      refine finite_bind (B := fun rec : EvalRec => rec (.algorithmIntrinsicRoute edge.1 ctx)) (finite_call _)
        (fun intrinsic => ?_)
      cases intrinsic <;> exact finite_call _

/-- **The retained receiver cell's evaluator, with no completion premise on it**: wherever the
    invocation receiver read completes, the written-expression evaluator of a cell marked
    `NeedInvocationRole.receiver` over a link edge IS that read, counted at its value boundary
    (the finite-use converse of `receiver_cell_reads_invocation_receiver`). -/
theorem receiver_cell_run (r : Nat) (source receiver fallback : Expr) (ctx : EvalCtx) (env : ValEnv)
    (s : EvalState) (cell : NeedCell) (hl : linkEdge? source = some (receiver, fallback))
    (hcell : s.needs[r]? = some cell) (hrole : cell.invocation = .receiver)
    (hc : ProductionCompletes (invocationReceiverValue receiver ctx env) s) :
    (evalSuppliedAt r source ctx env).runState s =
      (invocationReceiverValue receiver ctx env >>= fun value =>
        (pure (value, Result.valueCount value) : EvalM CountedResult)).runState s := by
  have hbody : (EvalBody.evalSuppliedAt evalUnbounded r source ctx env).runState s =
      (invocationReceiverValue receiver ctx env >>= fun value =>
        (pure (value, Result.valueCount value) : EvalM CountedResult)).runState s := by
    unfold EvalBody.evalSuppliedAt
    rw [hl]
    have hb : ((s.needs[r]?).map NeedCell.invocation == some NeedInvocationRole.receiver) = true := by
      rw [hcell, Option.map_some, hrole]; rfl
    dsimp only
    rw [EvalM.bind_runState, isInvocationReceiver_run, hb]
    rfl
  have hcb : ProductionCompletes ((fun rec : EvalRec => EvalBody.evalSuppliedAt rec r source ctx env) evalUnbounded) s := by
    unfold ProductionCompletes
    show ((EvalBody.evalSuppliedAt evalUnbounded r source ctx env).runState s).1 ≠ _
    rw [hbody, bind_run]
    unfold ProductionCompletes at hc
    revert hc
    rcases (invocationReceiverValue receiver ctx env).runState s with ⟨o, t⟩
    intro hc
    cases o with
    | ok value => nofun
    | error err => cases err <;> first | exact absurd rfl hc | nofun
  exact (production_eq_of_finite (.evalSuppliedAt r source ctx env)
    (fun rec => EvalBody.evalSuppliedAt rec r source ctx env) (fun _ => rfl)
    (finite_evalSuppliedAt r source ctx env) s hcb).trans hbody

/-! ## The plan side: the receiver VALUE -/

/-- The receiver VALUE the plan's callee read obtains from its link (the head of `plannedCallee`):
    the link's receiver cell, established or read, then the planned receiver read. -/
def plannedValue (link : Nat) : EvalM Result := do
  let cell ← NeedLink.receiverCell link
  let some linkCell := (← get).needs[link]? | throw (Error.illegalInEval "invalid need address")
  plannedReceiverValue linkCell cell

theorem plannedCallee_split (link : Nat) :
    plannedCallee link = (plannedValue link >>= fun value => decodeCallRef value >>= fun plan =>
      NeedPlan.calleeCell productionPlanRoute.classify plan >>= fun callee => capturedCallee callee) := by
  unfold plannedCallee plannedValue
  simp only [EvalM.bind_assoc]
  congr 1
  funext cell
  congr 1
  funext st
  cases st.needs[link]? with
  | none => rfl
  | some linkCell => rfl

/-- The outcome the receiver cell memoizes for the receiver read's outcome `o`, on the plan side: the
    read VALUE, shifted, counted at its value boundary; a failure as it is. -/
def receiverMemo (σ : Site) : Except Error Result → Except Error CountedResult
  | .ok v => .ok (shiftResult σ v, Result.valueCount (shiftResult σ v))
  | .error e => .error e

theorem disciplined_invocationReceiverValue (receiver : Expr) (ctx : EvalCtx) (env : ValEnv) :
    Disciplined (invocationReceiverValue receiver ctx env) := by
  rw [invocationReceiverValue_eq]
  refine Disciplined.bind (KatLang.EvaluatorDiscipline.evalUnbounded_disciplined (.resolveDotReceiver? receiver ctx))
    (fun alg? => ?_)
  cases alg? with
  | none =>
    exact Disciplined.withNestedMissingOutput
      (KatLang.EvaluatorDiscipline.evalUnbounded_disciplined (.eval receiver ctx env))
  | some targetAlg =>
    exact KatLang.EvaluatorDiscipline.evalUnbounded_disciplined (.referenceReceiverValue receiver targetAlg ctx env)

/-- **The plan side up to the receiver VALUE.** From the comparison state, the plan establishes its
    callee link and the link's receiver cell, demands that cell — the completion shell marks it
    `evaluating`, runs the invocation receiver read and memoizes the outcome — and returns the read
    VALUE. Under the contract for that read: the VALUE is production's, shifted, and the state is
    production's state after ITS receiver read, under the plan's insertion with the receiver cell
    COMPLETED with the memoized outcome. Completion is derived from production's. -/
theorem planned_value_run (E : EvalState → Prop) (a : Nat) (x : EvalState) (ca : NeedCell)
    (shape : NeedPlan.CallShape) (receiver fallback : Expr) (hinv : Inv x) (ha : x.needs[a]? = some ca)
    (hnone : ca.callee = none) (hshape : NeedPlan.ofSuspension? ca.suspension = some shape)
    (hroute : ca.route = some .algorithm)
    (hedge : shape.callee = .dotMember receiver "Algorithm" fallback none) (hnp : ∀ p, receiver ≠ .param p)
    (hE : E x)
    (cread : InsertedAt E (planInsertion x.needs.size a shape.callee shape.caller shape.values .evaluating)
      shiftResult
      (invocationReceiverValue receiver shape.caller shape.values)
      (invocationReceiverValue receiver shape.caller shape.values))
    (hcomp : ProductionCompletes (invocationReceiverValue receiver shape.caller shape.values) x) :
    (NeedPlan.calleeCell productionPlanRoute.classify a >>= plannedValue).runState x =
      (shiftExcept (shiftResult ⟨x.needs.size, 2⟩)
          ((invocationReceiverValue receiver shape.caller shape.values).runState x).1,
        embed (planInsertion x.needs.size a shape.callee shape.caller shape.values
          (.completed (receiverMemo ⟨x.needs.size, 2⟩
            ((invocationReceiverValue receiver shape.caller shape.values).runState x).1)))
          ((invocationReceiverValue receiver shape.caller shape.values).runState x).2) := by
  obtain ⟨x₁, hcal, hrcv⟩ := establish_run a x ca shape receiver fallback hinv ha hnone hshape hroute hedge hnp
  have hlink : linkEdge? shape.callee = some (receiver, fallback) := by rw [hedge]; exact linkEdge_algorithm _ _
  have hplan : NeedPlan.callShape? shape.callee shape.caller shape.values = none := by rw [hedge]; rfl
  have hle : (planInsertion x.needs.size a shape.callee shape.caller shape.values .suspended).base ≤ x.needs.size :=
    Nat.le_refl _
  -- the link and the receiver cell on the plan side
  have hgetL : (embed (planInsertion x.needs.size a shape.callee shape.caller shape.values .suspended) x).needs[x.needs.size]? =
      some (linkCell shape.callee shape.caller shape.values (x.needs.size + 1)) :=
    embedNeeds_inserted (planInsertion x.needs.size a shape.callee shape.caller shape.values .suspended) x.needs hle 0
      (Nat.zero_lt_succ 1)
  have hgetR : (embed (planInsertion x.needs.size a shape.callee shape.caller shape.values .suspended) x).needs[x.needs.size + 1]? =
      some (receiverCellOf shape.callee shape.caller shape.values .suspended) :=
    embedNeeds_inserted (planInsertion x.needs.size a shape.callee shape.caller shape.values .suspended) x.needs hle 1
      (Nat.lt_succ_self 1)
  -- the shell's `evaluating` mark is a write of the inserted receiver cell
  have hmark : withState (x.needs.size + 1) .evaluating
      (embed (planInsertion x.needs.size a shape.callee shape.caller shape.values .suspended) x) =
      embed (planInsertion x.needs.size a shape.callee shape.caller shape.values .evaluating) x :=
    embed_modify_inserted (planInsertion x.needs.size a shape.callee shape.caller shape.values .suspended) x hle 1
      (Nat.lt_succ_self 1) (fun c => { c with state := .evaluating })
  -- the shared receiver read, on the plan side
  obtain ⟨hiff, hrun⟩ := cread x hE
  have hrun := hrun hcomp
  have hcp : ProductionCompletes (invocationReceiverValue receiver shape.caller shape.values)
      (embed (planInsertion x.needs.size a shape.callee shape.caller shape.values .evaluating) x) :=
    fun h => hcomp (hiff.1 h)
  have hgetR3 : (embed (planInsertion x.needs.size a shape.callee shape.caller shape.values .evaluating) x).needs[x.needs.size + 1]? =
      some (receiverCellOf shape.callee shape.caller shape.values .evaluating) :=
    embedNeeds_inserted (planInsertion x.needs.size a shape.callee shape.caller shape.values .evaluating) x.needs hle 1
      (Nat.lt_succ_self 1)
  have hsup := receiver_cell_run (x.needs.size + 1) shape.callee receiver fallback shape.caller shape.values
    (embed (planInsertion x.needs.size a shape.callee shape.caller shape.values .evaluating) x) _ hlink hgetR3 rfl hcp
  -- production's receiver read: the heap discipline keeps the heap at least as long
  have hkeepSize : x.needs.size ≤ ((invocationReceiverValue receiver shape.caller shape.values).runState x).2.needs.size :=
    heapKept_size (disciplined_invocationReceiverValue receiver shape.caller shape.values x)
  rcases hr : (invocationReceiverValue receiver shape.caller shape.values).runState x with ⟨o₁, x₄⟩
  rw [hr] at hrun hkeepSize
  unfold ProductionCompletes at hcomp
  rw [hr] at hcomp
  simp only at hrun hcomp hkeepSize
  -- the receiver cell's evaluator from the `evaluating` state
  have hsupRun : (reCountValueBoundary <$> evalSuppliedAt (x.needs.size + 1) shape.callee shape.caller shape.values).runState
      (withState (x.needs.size + 1) .evaluating
        (embed (planInsertion x.needs.size a shape.callee shape.caller shape.values .suspended) x)) =
      (receiverMemo ⟨x.needs.size, 2⟩ o₁,
        embed (planInsertion x.needs.size a shape.callee shape.caller shape.values .evaluating) x₄) := by
    rw [hmark, map_run, hsup, bind_run, hrun]
    cases o₁ <;> rfl
  have hsupc : ProductionCompletes (evalSuppliedAt (x.needs.size + 1) shape.callee shape.caller shape.values)
      (withState (x.needs.size + 1) .evaluating
        (embed (planInsertion x.needs.size a shape.callee shape.caller shape.values .suspended) x)) := by
    unfold ProductionCompletes
    rw [hmark, hsup, bind_run, hrun]
    cases o₁ with
    | ok v => nofun
    | error e => cases e <;> first | exact absurd rfl hcomp | nofun
  have hdem := demand_expression_run (x.needs.size + 1)
    (embed (planInsertion x.needs.size a shape.callee shape.caller shape.values .suspended) x)
    (receiverCellOf shape.callee shape.caller shape.values .suspended) shape.callee shape.caller shape.values
    hgetR rfl rfl hplan hsupc
  rw [hsupRun] at hdem
  -- the memoized outcome is a write of the inserted receiver cell
  have hmemo : withState (x.needs.size + 1) (.completed (receiverMemo ⟨x.needs.size, 2⟩ o₁))
      (embed (planInsertion x.needs.size a shape.callee shape.caller shape.values .evaluating) x₄) =
      embed (planInsertion x.needs.size a shape.callee shape.caller shape.values
        (.completed (receiverMemo ⟨x.needs.size, 2⟩ o₁))) x₄ :=
    embed_modify_inserted (planInsertion x.needs.size a shape.callee shape.caller shape.values .evaluating) x₄ hkeepSize 1
      (Nat.lt_succ_self 1) (fun c => { c with state := .completed (receiverMemo ⟨x.needs.size, 2⟩ o₁) })
  have hninc : (receiverMemo ⟨x.needs.size, 2⟩ o₁).isIncomplete = false := by
    cases o₁ with
    | ok v => rfl
    | error e => cases e <;> first | exact absurd rfl hcomp | rfl
  have hshell : (demandNeedRecursive (x.needs.size + 1)).runState
      (embed (planInsertion x.needs.size a shape.callee shape.caller shape.values .suspended) x) =
      (receiverMemo ⟨x.needs.size, 2⟩ o₁,
        embed (planInsertion x.needs.size a shape.callee shape.caller shape.values
          (.completed (receiverMemo ⟨x.needs.size, 2⟩ o₁))) x₄) := by
    rw [hdem]
    unfold shellOutcome
    simp only [hninc, Bool.false_eq_true, ite_false]
    rw [hmemo]
  -- assemble
  have hprv : plannedReceiverValue (linkCell shape.callee shape.caller shape.values (x.needs.size + 1))
      (x.needs.size + 1) = Prod.fst <$> demandNeedRecursive (x.needs.size + 1) :=
    plannedReceiverValue_cell _ _ shape.callee receiver fallback shape.caller shape.values rfl hlink hnp
  rw [bind_run, hcal]
  unfold plannedValue
  simp only [bind_run, hrcv, get_run, hgetL]
  rw [hprv, map_run, hshell]
  cases o₁ <;> rfl

/-! ## The plan side: the captured callee, the heap-read name and origin, the resolved tail -/

open KatLang.MemoLinks (LinkHeapKept evalUnbounded_linkDisc linkDisc_calleeCell classify_linkDisc)

theorem classify_disciplined : ∀ shape, Disciplined (productionPlanRoute.classify shape) :=
  KatLang.EvaluatorDiscipline.productionDiscipline_holds.2.2.2.2.2.2.1

/-- A successful establishment — or read — of a plan's callee cell leaves it RECORDED in the plan
    cell (CR-13). -/
theorem calleeCell_records (p c : Nat) (s t : EvalState)
    (h : (NeedPlan.calleeCell productionPlanRoute.classify p).runState s = (.ok c, t)) :
    ∃ d, t.needs[p]? = some d ∧ d.callee = some c := by
  cases hc : s.needs[p]? with
  | none =>
    simp only [NeedPlan.calleeCell, bind_run, get_run, hc] at h
    cases h
  | some cell =>
    cases hcal : cell.callee with
    | some c0 =>
      rw [KatLang.AlgorithmProjectionLaws.calleeCell_recorded productionPlanRoute.classify p c0 s cell hc hcal] at h
      injection h with h1 h2
      injection h1 with h1
      subst h1 h2
      exact ⟨cell, hc, hcal⟩
    | none =>
      cases hshape : NeedPlan.ofSuspension? cell.suspension with
      | none =>
        simp only [NeedPlan.calleeCell, bind_run, get_run, hc, hcal, hshape] at h
        cases h
      | some shape =>
        rw [calleeCell_unrecorded productionPlanRoute.classify p s cell shape hc hcal hshape] at h
        have k1 := disciplined_routeOf productionPlanRoute.classify classify_disciplined p shape s
        generalize hro : (NeedPlan.routeOf productionPlanRoute.classify p shape).runState s = ro at h k1
        rcases ro with ⟨_ | r, t1⟩
        · cases h
        · obtain ⟨c1, hc1, _⟩ := k1 p cell hc
          dsimp only at h
          by_cases hi : r = .intrinsic
          · rw [ite_eq_left hi] at h; cases h
          · rw [ite_eq_right hi] at h
            have k2 := disciplined_supplyCallee (NeedPlan.effective shape r) r t1
            generalize hsu : (NeedPlan.supplyCallee (NeedPlan.effective shape r) r).runState t1 = su at h k2
            rcases su with ⟨_ | c2, t2⟩
            · cases h
            · obtain ⟨c3, hc3, _⟩ := k2 p c1 hc1
              cases h
              exact ⟨{ c3 with callee := some c }, by simp [Array.getElem?_modify, hc3], rfl⟩

/-- A cell whose callee cell is successfully established or read either had it recorded already or
    is a written invocation. -/
theorem calleeCell_plan (p c : Nat) (s t : EvalState)
    (h : (NeedPlan.calleeCell productionPlanRoute.classify p).runState s = (.ok c, t)) :
    ∃ cell, s.needs[p]? = some cell ∧
      (cell.callee.isSome ∨ (NeedPlan.ofSuspension? cell.suspension).isSome) := by
  cases hc : s.needs[p]? with
  | none =>
    simp only [NeedPlan.calleeCell, bind_run, get_run, hc] at h
    cases h
  | some cell =>
    refine ⟨cell, rfl, ?_⟩
    cases hcal : cell.callee with
    | some c0 => exact Or.inl rfl
    | none =>
      cases hshape : NeedPlan.ofSuspension? cell.suspension with
      | none =>
        simp only [NeedPlan.calleeCell, bind_run, get_run, hc, hcal, hshape] at h
        cases h
      | some shape => exact Or.inr rfl

/-- A written invocation has a callee name. -/
theorem calleeNameIn_of_plan (needs : Array NeedCell) (p : Nat) (cell : NeedCell) (hc : needs[p]? = some cell)
    (hplan : (NeedPlan.ofSuspension? cell.suspension).isSome) : ∃ n, NeedPlan.calleeNameIn? needs p = some n := by
  unfold NeedPlan.calleeNameIn? NeedPlan.shapeAt?
  rw [hc]
  dsimp only
  cases hs : NeedPlan.ofSuspension? cell.suspension with
  | none => rw [hs] at hplan; cases hplan
  | some shape =>
    dsimp only
    split <;> exact ⟨_, rfl⟩

/-- The plan side's route after the receiver VALUE `v`: the captured callee under the written form's
    context, the heap-read dispatch name and origin, and the production resolved call under the same
    context. -/
def planTail (a : Nat) (shape : NeedPlan.CallShape) (msg : String) (v : Result) : EvalM CountedResult := do
  let callee ← withCtx msg (decodeCallRef v >>= fun plan =>
    NeedPlan.calleeCell productionPlanRoute.classify plan >>= fun cell => capturedCallee cell)
  let name ← NeedPlan.dispatchName a shape .algorithm
  let origin ← NeedPlan.dispatchOrigin a shape .algorithm
  withCtx msg (evalResolvedCallCounted callee shape.args shape.caller shape.values name origin)

/-- The plan's `.Algorithm` ordinary call over production operations, as its head — the receiver
    VALUE — followed by its tail, re-counted. -/
theorem algorithmPlanCall_split (a : Nat) (shape : NeedPlan.CallShape) :
    algorithmPlanCall a shape =
      reCountValueBoundary <$>
        (withCtx shape.ctxMsg (NeedPlan.calleeCell productionPlanRoute.classify a >>= plannedValue) >>= fun v =>
          planTail a shape shape.ctxMsg v) := by
  have hsplit : (NeedPlan.calleeCell productionPlanRoute.classify a >>= plannedCallee) =
      ((NeedPlan.calleeCell productionPlanRoute.classify a >>= plannedValue) >>= fun value =>
        decodeCallRef value >>= fun plan =>
          NeedPlan.calleeCell productionPlanRoute.classify plan >>= fun callee => capturedCallee callee) := by
    rw [EvalM.bind_assoc]
    congr 1
    funext l
    exact plannedCallee_split l
  apply EvalM.ext
  intro s
  unfold algorithmPlanCall planTail
  rw [hsplit, ← KatLang.DotFunnel.withCtx_bind]
  simp only [bind_run, map_run, dispatchName_run, dispatchOrigin_run]
  rcases (withCtx shape.ctxMsg (NeedPlan.calleeCell productionPlanRoute.classify a >>= plannedValue)).runState s
    with ⟨o, t⟩
  cases o with
  | error e => rfl
  | ok v =>
    dsimp only
    rcases (withCtx shape.ctxMsg (decodeCallRef v >>= fun plan =>
      NeedPlan.calleeCell productionPlanRoute.classify plan >>= fun callee => capturedCallee callee)).runState t
      with ⟨oc, t'⟩
    cases oc with
    | error e => rfl
    | ok callee =>
      dsimp only
      rcases (withCtx shape.ctxMsg (evalResolvedCallCounted callee shape.args shape.caller shape.values
        (NeedPlan.dispatchNameIn t'.needs a shape .algorithm)
        (NeedPlan.dispatchOriginIn t'.needs a shape .algorithm))).runState t' with ⟨orr, t''⟩
      cases orr <;> rfl

/-- **The plan side's tail IS the captured call.** At a plan-side state where the plan cell `a`
    records its link `k`, the link records its receiver cell `rc`, and that cell is COMPLETED with
    the VALUE `v`: the plan's remaining route — decoding `v`, the decoded plan's callee cell and its
    CALLABLE under the written form's context; the heap-read dispatch name and origin
    (`algorithm_tail_name_origin`); the production resolved call under the same context — is the
    production `capturedCall v` under that context: the name is the captured plan's `calleeName`,
    the origin `.cell` of its callee cell. (A recorded callee belongs to a plan cell — `hplans`.) -/
theorem plan_tail_run (a k rc : Nat) (shape : NeedPlan.CallShape) (msg : String) (v : Result) (y : EvalState)
    (ca cl cr : NeedCell) (cnt : Nat)
    (hya : y.needs[a]? = some ca) (hcallee : ca.callee = some k)
    (hyl : y.needs[k]? = some cl) (hrcv : cl.receiver = some rc)
    (hyr : y.needs[rc]? = some cr) (hst : cr.state = .completed (.ok (v, cnt)))
    (hplans : ∀ p cell, v = .callRef p → y.needs[p]? = some cell → cell.callee.isSome →
      (NeedPlan.ofSuspension? cell.suspension).isSome) :
    (planTail a shape msg v).runState y =
      ctxOutcome msg ((capturedCall v shape.args shape.caller shape.values).runState y) := by
  unfold capturedCall planTail
  simp only [bind_run, ctx_run, dispatchName_run, dispatchOrigin_run]
  cases v with
  | callRef p =>
    have hdec : (decodeCallRef (.callRef p)).runState y = (.ok p, y) := rfl
    rw [hdec]
    dsimp only
    rcases hc : (NeedPlan.calleeCell productionPlanRoute.classify p).runState y with ⟨oc, y₁⟩
    cases oc with
    | error e => cases e <;> rfl
    | ok c =>
      dsimp only
      rcases hg : (capturedCallee c).runState y₁ with ⟨og, y₂⟩
      cases og with
      | error e => cases e <;> rfl
      | ok g =>
        -- the heap facts the name and origin read, kept from `y` to `y₂`
        have HK1 : HeapKept y.needs y₁.needs := by
          have := disciplined_calleeCell productionPlanRoute.classify classify_disciplined p y
          rw [hc] at this; exact this
        have HK2 : HeapKept y₁.needs y₂.needs := by
          have := KatLang.EvaluatorDiscipline.evalUnbounded_disciplined (.capturedCallee c) y₁
          have hrun : (evalUnbounded (.capturedCallee c)).runState y₁ = (.ok g, y₂) := hg
          rw [hrun] at this; exact this
        have LK1 : LinkHeapKept y.needs y₁.needs := by
          have := linkDisc_calleeCell productionPlanRoute.classify classify_linkDisc p y
          rw [hc] at this; exact this
        have LK2 : LinkHeapKept y₁.needs y₂.needs := by
          have := evalUnbounded_linkDisc (.capturedCallee c) y₁
          have hrun : (evalUnbounded (.capturedCallee c)).runState y₁ = (.ok g, y₂) := hg
          rw [hrun] at this; exact this
        obtain ⟨ca1, ha1, ka1⟩ := LK1 a ca hya
        obtain ⟨ca2, ha2, ka2⟩ := LK2 a ca1 ha1
        obtain ⟨cl1, hl1, kl1⟩ := LK1 k cl hyl
        obtain ⟨cl2, hl2, kl2⟩ := LK2 k cl1 hl1
        obtain ⟨cr1, hr1, kr1⟩ := HK1 rc cr hyr
        obtain ⟨cr2, hr2, kr2⟩ := HK2 rc cr1 hr1
        obtain ⟨d, hd, hdc⟩ := calleeCell_records p c y y₁ hc
        obtain ⟨d2, hd2, kd⟩ := LK2 p d hd
        obtain ⟨cell, hcell, hor⟩ := calleeCell_plan p c y y₁ hc
        have hplan : (NeedPlan.ofSuspension? cell.suspension).isSome :=
          hor.elim (fun h => hplans p cell rfl hcell h) id
        obtain ⟨c1, hc1, kc1⟩ := HK1 p cell hcell
        obtain ⟨c2, hc2, kc2⟩ := HK2 p c1 hc1
        have hplan2 : (NeedPlan.ofSuspension? c2.suspension).isSome := by
          rw [kc2.suspension, kc1.suspension]; exact hplan
        obtain ⟨n, hn⟩ := calleeNameIn_of_plan y₂.needs p c2 hc2 hplan2
        obtain ⟨hname, hcn, horigin, -⟩ := algorithm_tail_name_origin y₂ a k rc p cnt c shape ca2 cl2 cr2 d2 n
          ha2 (ka2.callee k (ka1.callee k hcallee)) hl2 (kl2.receiver _ (kl1.receiver _ hrcv)) hr2
          (kr2.completed _ (kr1.completed _ hst)) hn hd2 (kd.callee c hdc)
        have hctx : ctxOutcome msg ((Except.ok g : Except Error Algorithm), y₂) = (.ok g, y₂) := rfl
        rw [hctx]
        dsimp only
        rw [hname, horigin, hcn]
  | argView p => rfl
  | sequenceValue rs => rfl
  | listValue rs => rfl
  | atom n => rfl
  | str s => rfl
  | bool b => rfl

/-! ## The bridge (§ 6.3) -/

/-- **The production side of both written forms**: the production core under the written form's
    error context, re-counted at the value boundary. `dot_is_core` and `grouped_is_core` identify it
    with the production entries `evalCounted` of the dot expression and `evalCallCountedExpr`. -/
def algorithmProduction (msg : String) (receiver : Expr) (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) :
    EvalM CountedResult :=
  reCountValueBoundary <$> withCtx msg (algorithmCore receiver args ctx env)

/-- **The plan side's final insertion**: its callee link, and the link's receiver cell COMPLETED with
    the outcome of production's own receiver read from the comparison state (shifted, counted). -/
def finalInsertion (x : EvalState) (a : Nat) (shape : NeedPlan.CallShape) (receiver : Expr) : Insertion :=
  planInsertion x.needs.size a shape.callee shape.caller shape.values
    (.completed (receiverMemo ⟨x.needs.size, 2⟩
      ((invocationReceiverValue receiver shape.caller shape.values).runState x).1))

theorem embedCell_plan_callee (ι : Insertion) (c : NeedCell) : (embedCell ι ι.plan c).callee = some ι.base := by
  simp [embedCell]

theorem embedCell_suspension (ι : Insertion) (i : Nat) (c : NeedCell) :
    (embedCell ι i c).suspension = shiftSuspension ι.site c.suspension := by
  unfold embedCell
  split <;> rfl

theorem embedCell_callee_other (ι : Insertion) (i : Nat) (c : NeedCell) (h : ¬ ι.plan = i) :
    (embedCell ι i c).callee = c.callee.map ι.site.addr := by
  simp [embedCell, h, shiftCell]

theorem embedCell_state (ι : Insertion) (i : Nat) (c : NeedCell) :
    (embedCell ι i c).state = shiftNeedState ι.site c.state := by
  unfold embedCell
  split <;> rfl

/-- **The tail under the contract.** At a production-side state `x₄` satisfying `P` and its plan-side
    state under an insertion `ι` whose link records the receiver cell `rc`, completed with the shifted
    VALUE `v`: under the contract for `algorithmOfValue`, the plan side's tail (`planTail`) is
    production's `algorithmOfValue v` — outcome shifted, final state under the same insertion —
    framed by the written form's context. -/
theorem tail_bridge (D : EvalState → Prop) (a : Nat) (shape : NeedPlan.CallShape) (ι : Insertion) (rc : Nat)
    (x₄ : EvalState) (v : Result) (ca₄ cl cr : NeedCell) (cnt : Nat)
    (hplan : ι.plan = a) (hlt : a < ι.base) (hle : ι.base ≤ x₄.needs.size)
    (hPx : D x₄) (hplans : PlanCallees x₄)
    (hca₄ : x₄.needs[a]? = some ca₄) (hplanCell : (NeedPlan.ofSuspension? ca₄.suspension).isSome)
    (hyl : (embed ι x₄).needs[ι.base]? = some cl) (hrcv : cl.receiver = some rc)
    (hyr : (embed ι x₄).needs[rc]? = some cr)
    (hst : cr.state = .completed (.ok (shiftResult ι.site v, cnt)))
    (ctail : InsertedAt D ι shiftCounted
      (algorithmOfValue (shiftResult ι.site v) (some shape.args) shape.caller shape.values)
      (algorithmOfValue v (some shape.args) shape.caller shape.values))
    (hcomp : ProductionCompletes (algorithmOfValue v (some shape.args) shape.caller shape.values) x₄) :
    (planTail a shape shape.ctxMsg (shiftResult ι.site v)).runState (embed ι x₄) =
      ctxOutcome shape.ctxMsg
        (shiftExcept (shiftCounted ι.site)
            ((algorithmOfValue v (some shape.args) shape.caller shape.values).runState x₄).1,
          embed ι ((algorithmOfValue v (some shape.args) shape.caller shape.values).runState x₄).2) := by
  obtain ⟨hiff, hrun⟩ := ctail x₄ hPx
  have hrun := hrun hcomp
  have hya := embedNeeds_below ι x₄.needs hle a hlt ca₄ hca₄
  have hcal : (embedCell ι a ca₄).callee = some ι.base := by
    rw [← hplan]; exact embedCell_plan_callee ι ca₄
  have hplans' : ∀ p cell, shiftResult ι.site v = .callRef p →
      (embed ι x₄).needs[p]? = some cell → cell.callee.isSome →
      (NeedPlan.ofSuspension? cell.suspension).isSome := by
    intro p cell hv hcell hcal'
    obtain ⟨p₀, -, hp⟩ := shiftResult_callRef_inv _ v p hv
    subst hp
    have hsh := embedNeeds_shifted ι x₄.needs hle p₀
    have hcell' : (embedNeeds ι x₄.needs)[ι.site.addr p₀]? = some cell := hcell
    rw [hsh] at hcell'
    cases hc₀ : x₄.needs[p₀]? with
    | none => rw [hc₀] at hcell'; cases hcell'
    | some cell₀ =>
      rw [hc₀] at hcell'
      simp only [Option.map_some, Option.some.injEq] at hcell'
      subst hcell'
      rw [embedCell_suspension, ofSuspension_shift_isSome]
      by_cases hap : ι.plan = p₀
      · rw [hplan] at hap
        subst hap
        rw [hca₄] at hc₀
        injection hc₀ with hc₀
        subst hc₀
        exact hplanCell
      · have hcal₀ : cell₀.callee.isSome := by
          rw [embedCell_callee_other _ _ _ hap] at hcal'
          cases hcc : cell₀.callee with
          | none => rw [hcc] at hcal'; cases hcal'
          | some c => rfl
        exact hplans p₀ cell₀ hc₀ hcal₀
  have htail := plan_tail_run a ι.base rc shape shape.ctxMsg (shiftResult ι.site v) (embed ι x₄)
    _ cl cr cnt hya hcal hyl hrcv hyr hst hplans'
  have hcp : ProductionCompletes (algorithmOfValue (shiftResult ι.site v) (some shape.args)
      shape.caller shape.values) (embed ι x₄) := fun h => hcomp (hiff.1 h)
  have hcc := (algorithmOfValue_completes_iff _ _ _ _ _).1 hcp
  rw [← algorithmOfValue_eq _ _ _ _ _ hcc, hrun] at htail
  exact htail

theorem map_state {α β : Type} (f : α → β) (m : EvalM α) (s : EvalState) :
    ((f <$> m).runState s).2 = (m.runState s).2 := by
  rw [map_run]
  rcases m.runState s with ⟨o, t⟩
  cases o <;> rfl

theorem ctx_state {α : Type} (c : String) (m : EvalM α) (s : EvalState) :
    ((withCtx c m).runState s).2 = (m.runState s).2 := by
  rw [ctx_run]
  rcases m.runState s with ⟨o, t⟩
  cases o with
  | ok a => rfl
  | error e => cases e <;> rfl

/-- The production core completes when the framed, re-counted production side does. -/
theorem core_completes (msg : String) (receiver : Expr) (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv)
    (x : EvalState) (hcomp : ProductionCompletes (algorithmProduction msg receiver args ctx env) x) :
    ((algorithmCore receiver args ctx env).runState x).1 ≠ .error .fuelExhausted := by
  unfold ProductionCompletes algorithmProduction at hcomp
  rw [map_run, ctx_run] at hcomp
  intro h
  apply hcomp
  rcases hr : (algorithmCore receiver args ctx env).runState x with ⟨o, t⟩
  rw [hr] at h
  simp only at h
  subst h
  rfl

/-- **`Frame` AT PRODUCTION'S FINAL STATE** (the first conjunct of `HeapInsertion.Inserted`). The
    plan cell lies below the comparison state's heap size and every production run keeps the heap at
    least that long (the heap discipline); so `Frame` at the final state is exactly the PRESERVATION
    OBLIGATION that production records no callee for the plan cell — asked of the receiver read from
    the entry domain (`kread`: a failed read ends the run) and of the tail from the admissible tail
    entries (`ktail`). Self-observation breaks it (`self_reference_records_callee`). -/
theorem production_frame (E : EvalState → Prop) (a : Nat) (msg : String) (receiver : Expr) (args : OutputBundle)
    (ctx : EvalCtx) (env : ValEnv) (x : EvalState) (ca : NeedCell) (ha : x.needs[a]? = some ca) (hE : E x)
    (kread : KeepsOn E (Unrecorded a) (invocationReceiverValue receiver ctx env))
    (ktail : ∀ v, KeepsOn (After E (invocationReceiverValue receiver ctx env) v) (Unrecorded a)
      (algorithmOfValue v (some args) ctx env))
    (hcomp : ProductionCompletes (algorithmProduction msg receiver args ctx env) x) :
    Frame x.needs.size a ((algorithmProduction msg receiver args ctx env).runState x).2 := by
  have halt : a < x.needs.size := valid_of_get ha
  have hcore := core_completes msg receiver args ctx env x hcomp
  have hstate : ((algorithmProduction msg receiver args ctx env).runState x).2 =
      ((algorithmCore receiver args ctx env).runState x).2 := by
    unfold algorithmProduction
    rw [map_state, ctx_state]
  rw [hstate]
  unfold algorithmCore at hcore ⊢
  rw [bind_run] at hcore ⊢
  have hK1 : HeapKept x.needs ((invocationReceiverValue receiver ctx env).runState x).2.needs :=
    disciplined_invocationReceiverValue receiver ctx env x
  have hk1 := kread x hE
  rcases hr : (invocationReceiverValue receiver ctx env).runState x with ⟨o₁, x₄⟩
  rw [hr] at hcore hK1 hk1
  cases o₁ with
  | error e =>
    dsimp only at hcore hK1 hk1 ⊢
    have hne : e ≠ Error.fuelExhausted := fun h => hcore (by rw [h])
    exact ⟨halt, heapKept_size hK1, hk1 (fun h => hne (Except.error.inj h))⟩
  | ok v =>
    dsimp only at hcore hK1 ⊢
    have hK2 : HeapKept x₄.needs ((algorithmOfValue v (some args) ctx env).runState x₄).2.needs :=
      KatLang.EvaluatorDiscipline.evalUnbounded_disciplined (.algorithmOfValue v (some args) ctx env) x₄
    exact ⟨halt, Nat.le_trans (heapKept_size hK1) (heapKept_size hK2), ktail v x₄ ⟨x, hE, hr⟩ hcore⟩

/-- **THE `.Algorithm` BRIDGE, at the production core.** At a valid comparison state `x` where the
    plan cell `a` holds a written `.Algorithm` invocation over a non-parameter receiver, with its
    `.algorithm` route recorded and its callee unrecorded, and an entry domain `E` holding `x`:

    * `cread` — the non-observation contract for the invocation receiver read, from the entry
      domain, at the plan side's insertion with its receiver cell `evaluating`;
    * `ctail` — the contract for `algorithmOfValue v`, for each receiver VALUE `v`, from the
      ADMISSIBLE TAIL ENTRIES of `v` only (`After E read v`: the states the production receiver
      read reaches from an entry state with result `v`), at the plan side's insertion with its
      receiver cell completed with `v`;
    * `kread`, `ktail` — the preservation obligation of `Frame`: neither computation records a
      callee for the plan cell;
    * `hentry` — a recorded callee belongs to a plan cell, at every admissible tail entry.

    Then the plan's ordinary call along the `.Algorithm` route and production are `Bridged`: the
    plan's outcome is EXACTLY production's with its value shifted past the two inserted cells (an
    error unchanged: payload and context chain), and the two final states are in THE relation
    `HeapInsertion.Inserted` under `finalInsertion` — `Frame` at production's final state, and the
    plan's final state its embedding: the callee link, the receiver cell completed with the
    memoized read, the plan cell's callee record, every later address shifted, nothing else
    different. Completion is assumed of the production side only. -/
theorem algorithm_core_bridge (E : EvalState → Prop) (a : Nat) (shape : NeedPlan.CallShape)
    (receiver fallback : Expr) (x : EvalState) (ca : NeedCell)
    (hedge : shape.callee = .dotMember receiver "Algorithm" fallback none) (hnp : ∀ p, receiver ≠ .param p)
    (ha : x.needs[a]? = some ca) (hshape : NeedPlan.ofSuspension? ca.suspension = some shape)
    (hroute : ca.route = some .algorithm) (hnone : ca.callee = none)
    (hinv : Inv x) (hE : E x)
    (cread : InsertedAt E (planInsertion x.needs.size a shape.callee shape.caller shape.values .evaluating)
      shiftResult
      (invocationReceiverValue receiver shape.caller shape.values)
      (invocationReceiverValue receiver shape.caller shape.values))
    (kread : KeepsOn E (Unrecorded a) (invocationReceiverValue receiver shape.caller shape.values))
    (hentry : ∀ v t, After E (invocationReceiverValue receiver shape.caller shape.values) v t → PlanCallees t)
    (ctail : ∀ v, InsertedAt (After E (invocationReceiverValue receiver shape.caller shape.values) v)
      (planInsertion x.needs.size a shape.callee shape.caller shape.values
        (.completed (receiverMemo ⟨x.needs.size, 2⟩ (.ok v))))
      shiftCounted
      (algorithmOfValue (shiftResult ⟨x.needs.size, 2⟩ v) (some shape.args) shape.caller shape.values)
      (algorithmOfValue v (some shape.args) shape.caller shape.values))
    (ktail : ∀ v, KeepsOn (After E (invocationReceiverValue receiver shape.caller shape.values) v) (Unrecorded a)
      (algorithmOfValue v (some shape.args) shape.caller shape.values))
    (hcomp : ProductionCompletes
      (algorithmProduction shape.ctxMsg receiver shape.args shape.caller shape.values) x) :
    Bridged (finalInsertion x a shape receiver)
      ((ordinaryCall productionPlanRoute a shape .algorithm).runState x)
      ((algorithmProduction shape.ctxMsg receiver shape.args shape.caller shape.values).runState x) := by
  have hrunEq : (ordinaryCall productionPlanRoute a shape .algorithm).runState x =
      (shiftExcept (shiftCounted ⟨x.needs.size, 2⟩)
          ((algorithmProduction shape.ctxMsg receiver shape.args shape.caller shape.values).runState x).1,
        embed (finalInsertion x a shape receiver)
          ((algorithmProduction shape.ctxMsg receiver shape.args shape.caller shape.values).runState x).2) := by
    -- production's receiver read completes
    have hU1c : ProductionCompletes (invocationReceiverValue receiver shape.caller shape.values) x := by
      intro hinc
      apply hcomp
      unfold algorithmProduction algorithmCore
      rw [map_run, ctx_run, bind_run]
      rcases hr : (invocationReceiverValue receiver shape.caller shape.values).runState x with ⟨o, t⟩
      rw [hr] at hinc
      simp only at hinc
      subst hinc
      rfl
    have hhead := planned_value_run E a x ca shape receiver fallback hinv ha hnone hshape hroute hedge hnp hE
      cread hU1c
    have hK1 : HeapKept x.needs ((invocationReceiverValue receiver shape.caller shape.values).runState x).2.needs :=
      disciplined_invocationReceiverValue receiver shape.caller shape.values x
    have hplanRun : (algorithmPlanCall a shape).runState x =
        (shiftExcept (shiftCounted ⟨x.needs.size, 2⟩)
            ((algorithmProduction shape.ctxMsg receiver shape.args shape.caller shape.values).runState x).1,
          embed (finalInsertion x a shape receiver)
            ((algorithmProduction shape.ctxMsg receiver shape.args shape.caller shape.values).runState x).2) := by
      unfold finalInsertion
      unfold algorithmProduction algorithmCore at hcomp ⊢
      unfold ProductionCompletes at hcomp
      rw [map_run, ctx_run, bind_run] at hcomp ⊢
      rw [algorithmPlanCall_split, map_run, bind_run, ctx_run, hhead]
      rcases hr : (invocationReceiverValue receiver shape.caller shape.values).runState x with ⟨o₁, x₄⟩
      rw [hr] at hcomp hK1
      simp only at hK1
      cases o₁ with
      | error e =>
        simp only at hcomp
        cases e <;> first | exact absurd rfl hcomp | rfl
      | ok v =>
        dsimp only at hcomp ⊢
        have hle₄ : x.needs.size ≤ x₄.needs.size := heapKept_size hK1
        have halt : a < x.needs.size := valid_of_get ha
        -- production's tail completes
        have htc : ProductionCompletes (algorithmOfValue v (some shape.args) shape.caller shape.values) x₄ := by
          intro hinc
          apply hcomp
          rcases ht : (algorithmOfValue v (some shape.args) shape.caller shape.values).runState x₄ with ⟨o, t⟩
          rw [ht] at hinc
          simp only at hinc
          subst hinc
          rfl
        obtain ⟨ca₄, hca₄, kca⟩ := hK1 a ca ha
        have hplanCell : (NeedPlan.ofSuspension? ca₄.suspension).isSome := by
          rw [kca.suspension, hshape]; rfl
        have hyl := embedNeeds_inserted (planInsertion x.needs.size a shape.callee shape.caller shape.values
          (.completed (receiverMemo ⟨x.needs.size, 2⟩ (.ok v)))) x₄.needs hle₄ 0 (Nat.zero_lt_succ 1)
        have hyr := embedNeeds_inserted (planInsertion x.needs.size a shape.callee shape.caller shape.values
          (.completed (receiverMemo ⟨x.needs.size, 2⟩ (.ok v)))) x₄.needs hle₄ 1 (Nat.lt_succ_self 1)
        have htail := tail_bridge (After E (invocationReceiverValue receiver shape.caller shape.values) v) a shape
          (planInsertion x.needs.size a shape.callee shape.caller shape.values
            (.completed (receiverMemo ⟨x.needs.size, 2⟩ (.ok v)))) (x.needs.size + 1) x₄ v ca₄ _ _
          (Result.valueCount (shiftResult ⟨x.needs.size, 2⟩ v)) rfl halt hle₄ ⟨x, hE, hr⟩ (hentry v x₄ ⟨x, hE, hr⟩) hca₄ hplanCell
          hyl rfl hyr rfl (ctail v) htc
        simp only [planInsertion_site] at htail
        rcases ht : (algorithmOfValue v (some shape.args) shape.caller shape.values).runState x₄ with ⟨o₂, x₅⟩
        rw [ht] at hcomp htail
        simp only at htail
        have hne₂ : o₂ ≠ .error .fuelExhausted := by
          intro h
          subst h
          exact hcomp rfl
        have hctxv : ctxOutcome shape.ctxMsg
            (shiftExcept (shiftResult ⟨x.needs.size, 2⟩) (Except.ok v),
              embed (planInsertion x.needs.size a shape.callee shape.caller shape.values
                (.completed (receiverMemo ⟨x.needs.size, 2⟩ (.ok v)))) x₄) =
            (.ok (shiftResult ⟨x.needs.size, 2⟩ v),
              embed (planInsertion x.needs.size a shape.callee shape.caller shape.values
                (.completed (receiverMemo ⟨x.needs.size, 2⟩ (.ok v)))) x₄) := rfl
        rw [hctxv]
        dsimp only
        rw [htail]
        cases o₂ with
        | ok r =>
          show ((Except.ok (reCountValueBoundary (shiftCounted ⟨x.needs.size, 2⟩ r)) : Except Error CountedResult), _) = _
          rw [reCount_shift]
          rfl
        | error e => cases e <;> first | exact absurd rfl hne₂ | rfl
    have hplanc : ((algorithmPlanCall a shape).runState x).1 ≠ .error .fuelExhausted := by
      rw [hplanRun]
      unfold ProductionCompletes at hcomp
      revert hcomp
      rcases (algorithmProduction shape.ctxMsg receiver shape.args shape.caller shape.values).runState x with ⟨o, t⟩
      intro hcomp
      cases o with
      | ok r => nofun
      | error e => cases e <;> first | exact absurd rfl hcomp | nofun
    rw [ordinaryCall_algorithm_is_production a shape x hplanc, hplanRun]
  have hframe := production_frame E a shape.ctxMsg receiver shape.args shape.caller shape.values x ca ha hE kread ktail
    hcomp
  exact ⟨congrArg Prod.fst hrunEq, hframe, congrArg Prod.snd hrunEq⟩

/-! ## Both written forms against their production entries -/

/-- The plan shape of the dot form `target.Algorithm(args)` (`NeedPlan.callShape?`). -/
def dotShape (target fallback : Expr) (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) : NeedPlan.CallShape :=
  ⟨.dotMember target "Algorithm" fallback none, args, ctx, env, .dot target "Algorithm" fallback⟩

/-- The plan shape of the grouped form `(receiver.Algorithm)(args)` (`NeedPlan.callShape?`). -/
def groupedShape (receiver fallback : Expr) (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) : NeedPlan.CallShape :=
  ⟨.dotMember receiver "Algorithm" fallback none, args, ctx, env, .call⟩

theorem map_completes {α β : Type} (f : α → β) (m : EvalM α) (s : EvalState)
    (h : (m.runState s).1 ≠ .error .fuelExhausted) : ((f <$> m).runState s).1 ≠ .error .fuelExhausted := by
  rw [map_run]
  revert h
  rcases m.runState s with ⟨o, t⟩
  intro h
  cases o with
  | ok v => nofun
  | error e => cases e <;> first | exact absurd rfl h | nofun

/-- **THE `.Algorithm` BRIDGE, dot form `target.Algorithm(args)`**, when selection chooses the
    intrinsic and not a declared member. At the plan's flight `x` — the cell `a` holds the written
    invocation, its `.algorithm` route recorded, its callee unrecorded — where production's own
    receiver probe selects the `.Algorithm` intrinsic: under the heap relation of `HeapInsertion`
    and the non-observation contract for the invocation receiver read and `algorithmOfValue`
    (relative to `P`), the plan's ordinary call and the re-counted production evaluation
    `evalCounted (target.Algorithm(args))`, both from `x`, have RELATED outcomes and final states:
    the plan's outcome is production's with its value shifted past the two inserted cells, and its
    final state is production's under `finalInsertion`. Completion is assumed of production only. -/
theorem algorithm_bridge_dot (E : EvalState → Prop) (a : Nat) (target fallback : Expr) (args : OutputBundle)
    (ctx : EvalCtx) (env : ValEnv) (x x' : EvalState) (alg? : Option Algorithm) (ca : NeedCell)
    (hnp : ∀ p, target ≠ .param p)
    (ha : x.needs[a]? = some ca)
    (hsus : ca.suspension = .expression (.dotMember target "Algorithm" fallback (some args)) ctx env)
    (hroute : ca.route = some .algorithm) (hnone : ca.callee = none)
    (hprobe : (resolveDotReceiver? target ctx).runState x = (.ok alg?, x'))
    (hmiss : selectDotEdge ctx target "Algorithm" alg? = .ok (.miss .algorithm))
    (hinv : Inv x) (hE : E x)
    (cread : InsertedAt E
      (planInsertion x.needs.size a (.dotMember target "Algorithm" fallback none) ctx env .evaluating)
      shiftResult (invocationReceiverValue target ctx env) (invocationReceiverValue target ctx env))
    (kread : KeepsOn E (Unrecorded a) (invocationReceiverValue target ctx env))
    (hentry : ∀ v t, After E (invocationReceiverValue target ctx env) v t → PlanCallees t)
    (ctail : ∀ v, InsertedAt (After E (invocationReceiverValue target ctx env) v)
      (planInsertion x.needs.size a (.dotMember target "Algorithm" fallback none) ctx env
        (.completed (receiverMemo ⟨x.needs.size, 2⟩ (.ok v))))
      shiftCounted
      (algorithmOfValue (shiftResult ⟨x.needs.size, 2⟩ v) (some args) ctx env)
      (algorithmOfValue v (some args) ctx env))
    (ktail : ∀ v, KeepsOn (After E (invocationReceiverValue target ctx env) v) (Unrecorded a)
      (algorithmOfValue v (some args) ctx env))
    (hprod : ProductionCompletes (evalCounted (.dotMember target "Algorithm" fallback (some args)) ctx env) x) :
    Bridged (finalInsertion x a (dotShape target fallback args ctx env) target)
      ((ordinaryCall productionPlanRoute a (dotShape target fallback args ctx env) .algorithm).runState x)
      ((reCountValueBoundary <$> evalCounted (.dotMember target "Algorithm" fallback (some args)) ctx env).runState x) := by
  have hprodEq : (algorithmProduction (CtxMsg.dotCall target "Algorithm") target args ctx env).runState x =
      (reCountValueBoundary <$> evalCounted (.dotMember target "Algorithm" fallback (some args)) ctx env).runState x := by
    unfold algorithmProduction
    rw [map_run, map_run, ctx_run, dot_is_core target fallback args ctx env x x' alg? hprobe hmiss hprod]
  have hcomp : ProductionCompletes (algorithmProduction (CtxMsg.dotCall target "Algorithm") target args ctx env) x := by
    unfold ProductionCompletes
    rw [hprodEq]
    exact map_completes _ _ x hprod
  have h := algorithm_core_bridge E a (dotShape target fallback args ctx env) target fallback x ca rfl hnp ha
    (by rw [hsus]; rfl) hroute hnone hinv hE cread kread hentry ctail ktail hcomp
  have he : algorithmProduction (NeedPlan.CallShape.ctxMsg (dotShape target fallback args ctx env)) target
      (dotShape target fallback args ctx env).args (dotShape target fallback args ctx env).caller
      (dotShape target fallback args ctx env).values =
      algorithmProduction (CtxMsg.dotCall target "Algorithm") target args ctx env := rfl
  rw [he, hprodEq] at h
  exact h

/-- **THE `.Algorithm` BRIDGE, grouped form `(receiver.Algorithm)(args)`**, through the ordinary
    link-callee call entry. Production's call first decides the edge's route (`algorithmIntrinsicRoute`
    under the call's context); when that decision answers `true` at `x`, with the plan's flight facts,
    the invariant and the contract at `x`: the plan's ordinary call from `x` and the re-counted
    production `evalCallCountedExpr (receiver.Algorithm) args` from the decision's ENTRY state `s` have
    related outcomes and final states — as in the dot form. When the decision is settled at the
    flight (`s = x`), both run from one state. Completion is assumed of production only. -/
theorem algorithm_bridge_grouped (E : EvalState → Prop) (a : Nat) (receiver fallback : Expr) (args : OutputBundle)
    (ctx : EvalCtx) (env : ValEnv) (s x : EvalState) (ca : NeedCell)
    (hnp : ∀ p, receiver ≠ .param p)
    (hdecided : (withCtx (CtxMsg.call (.dotMember receiver "Algorithm" fallback none))
      (algorithmIntrinsicRoute receiver ctx)).runState s = (.ok true, x))
    (ha : x.needs[a]? = some ca)
    (hsus : ca.suspension = .expression (.call (.dotMember receiver "Algorithm" fallback none) args) ctx env)
    (hroute : ca.route = some .algorithm) (hnone : ca.callee = none)
    (hinv : Inv x) (hE : E x)
    (cread : InsertedAt E
      (planInsertion x.needs.size a (.dotMember receiver "Algorithm" fallback none) ctx env .evaluating)
      shiftResult (invocationReceiverValue receiver ctx env) (invocationReceiverValue receiver ctx env))
    (kread : KeepsOn E (Unrecorded a) (invocationReceiverValue receiver ctx env))
    (hentry : ∀ v t, After E (invocationReceiverValue receiver ctx env) v t → PlanCallees t)
    (ctail : ∀ v, InsertedAt (After E (invocationReceiverValue receiver ctx env) v)
      (planInsertion x.needs.size a (.dotMember receiver "Algorithm" fallback none) ctx env
        (.completed (receiverMemo ⟨x.needs.size, 2⟩ (.ok v))))
      shiftCounted
      (algorithmOfValue (shiftResult ⟨x.needs.size, 2⟩ v) (some args) ctx env)
      (algorithmOfValue v (some args) ctx env))
    (ktail : ∀ v, KeepsOn (After E (invocationReceiverValue receiver ctx env) v) (Unrecorded a)
      (algorithmOfValue v (some args) ctx env))
    (hprod : ProductionCompletes
      (evalCallCountedExpr (.dotMember receiver "Algorithm" fallback none) args ctx env) s) :
    Bridged (finalInsertion x a (groupedShape receiver fallback args ctx env) receiver)
      ((ordinaryCall productionPlanRoute a (groupedShape receiver fallback args ctx env) .algorithm).runState x)
      ((reCountValueBoundary <$>
        evalCallCountedExpr (.dotMember receiver "Algorithm" fallback none) args ctx env).runState s) := by
  have hprodEq : (algorithmProduction (CtxMsg.call (.dotMember receiver "Algorithm" fallback none)) receiver args
        ctx env).runState x =
      (reCountValueBoundary <$>
        evalCallCountedExpr (.dotMember receiver "Algorithm" fallback none) args ctx env).runState s := by
    unfold algorithmProduction
    rw [map_run, map_run, ctx_run,
      grouped_is_core (.dotMember receiver "Algorithm" fallback none) receiver fallback args ctx env s x
        (linkEdge_algorithm receiver fallback) hdecided hprod]
  have hcomp : ProductionCompletes (algorithmProduction (CtxMsg.call (.dotMember receiver "Algorithm" fallback none))
      receiver args ctx env) x := by
    unfold ProductionCompletes
    rw [hprodEq]
    exact map_completes _ _ s hprod
  have h := algorithm_core_bridge E a (groupedShape receiver fallback args ctx env) receiver fallback x ca rfl hnp ha
    (by rw [hsus]; rfl) hroute hnone hinv hE cread kread hentry ctail ktail hcomp
  have he : algorithmProduction (NeedPlan.CallShape.ctxMsg (groupedShape receiver fallback args ctx env)) receiver
      (groupedShape receiver fallback args ctx env).args (groupedShape receiver fallback args ctx env).caller
      (groupedShape receiver fallback args ctx env).values =
      algorithmProduction (CtxMsg.call (.dotMember receiver "Algorithm" fallback none)) receiver args ctx env := rfl
  rw [he, hprodEq] at h
  exact h

/-- **THE `.Algorithm` BRIDGE, grouped form, FROM ONE STATE.** `algorithm_bridge_grouped` compares the
    plan from the route decision's EXIT state with production from its ENTRY state, because
    production's call decides the edge's route before it reads the receiver. The plan's own flight is
    one state; when production's route decision is SETTLED there — it answers `true` and leaves the
    flight state as it is (`hsettled`) — the plan's ordinary call and the re-counted production
    `evalCallCountedExpr (receiver.Algorithm) args` run FROM THE SAME STATE `x`. A decision that is
    not settled at the flight (one that mints a runtime identity or allocates, as a receiver that is
    itself a dot RESULT can) is outside this statement: its plan and production runs from the one
    flight state differ by the decision's own effect. -/
theorem algorithm_bridge_grouped_settled (E : EvalState → Prop) (a : Nat) (receiver fallback : Expr)
    (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) (x : EvalState) (ca : NeedCell)
    (hnp : ∀ p, receiver ≠ .param p)
    (hsettled : (withCtx (CtxMsg.call (.dotMember receiver "Algorithm" fallback none))
      (algorithmIntrinsicRoute receiver ctx)).runState x = (.ok true, x))
    (ha : x.needs[a]? = some ca)
    (hsus : ca.suspension = .expression (.call (.dotMember receiver "Algorithm" fallback none) args) ctx env)
    (hroute : ca.route = some .algorithm) (hnone : ca.callee = none)
    (hinv : Inv x) (hE : E x)
    (cread : InsertedAt E
      (planInsertion x.needs.size a (.dotMember receiver "Algorithm" fallback none) ctx env .evaluating)
      shiftResult (invocationReceiverValue receiver ctx env) (invocationReceiverValue receiver ctx env))
    (kread : KeepsOn E (Unrecorded a) (invocationReceiverValue receiver ctx env))
    (hentry : ∀ v t, After E (invocationReceiverValue receiver ctx env) v t → PlanCallees t)
    (ctail : ∀ v, InsertedAt (After E (invocationReceiverValue receiver ctx env) v)
      (planInsertion x.needs.size a (.dotMember receiver "Algorithm" fallback none) ctx env
        (.completed (receiverMemo ⟨x.needs.size, 2⟩ (.ok v))))
      shiftCounted
      (algorithmOfValue (shiftResult ⟨x.needs.size, 2⟩ v) (some args) ctx env)
      (algorithmOfValue v (some args) ctx env))
    (ktail : ∀ v, KeepsOn (After E (invocationReceiverValue receiver ctx env) v) (Unrecorded a)
      (algorithmOfValue v (some args) ctx env))
    (hprod : ProductionCompletes
      (evalCallCountedExpr (.dotMember receiver "Algorithm" fallback none) args ctx env) x) :
    Bridged (finalInsertion x a (groupedShape receiver fallback args ctx env) receiver)
      ((ordinaryCall productionPlanRoute a (groupedShape receiver fallback args ctx env) .algorithm).runState x)
      ((reCountValueBoundary <$>
        evalCallCountedExpr (.dotMember receiver "Algorithm" fallback none) args ctx env).runState x) :=
  algorithm_bridge_grouped E a receiver fallback args ctx env x x ca hnp hsettled ha hsus hroute hnone hinv hE cread
    kread hentry ctail ktail hprod

/-! ## Corollaries: exact outcomes -/

/-- **A structured failure is EQUAL on the two sides** — payload and context chain: no `Error`
    carries a need address, so the shift leaves it alone. -/
theorem bridge_failure_exact {σ : Site} {plan prod : Except Error CountedResult × EvalState} {st : EvalState}
    (h : plan = (shiftExcept (shiftCounted σ) prod.1, st)) (e : Error) (he : prod.1 = .error e) :
    plan.1 = .error e := by
  rw [h, he]
  rfl

/-- **An address-free result is EQUAL on the two sides**, with its emitted count: a value that
    carries no call reference and no argument view is unshifted. -/
theorem bridge_addressFree_exact {σ : Site} {plan prod : Except Error CountedResult × EvalState} {st : EvalState}
    (h : plan = (shiftExcept (shiftCounted σ) prod.1, st)) (r : Result) (n : Nat) (hr : prod.1 = .ok (r, n))
    (hfree : ∀ a, ¬ KatLang.AddressInvariant.Mentions r a) : plan.1 = .ok (r, n) := by
  rw [h, hr]
  show (Except.ok (shiftCounted σ (r, n)) : Except Error CountedResult) = _
  unfold shiftCounted
  rw [shiftResult_addressFree σ r hfree]

/-- The two sides complete together: the plan's outcome is incomplete only if production's is. -/
theorem bridge_completes {σ : Site} {plan prod : Except Error CountedResult × EvalState} {st : EvalState}
    (h : plan = (shiftExcept (shiftCounted σ) prod.1, st)) (hc : prod.1 ≠ .error .fuelExhausted) :
    plan.1 ≠ .error .fuelExhausted := by
  rw [h]
  revert hc
  rcases prod with ⟨o, t⟩
  intro hc
  cases o with
  | ok r => nofun
  | error e => exact hc

/-- A structured failure of a bridged pair is EQUAL on the two sides. -/
theorem Bridged.failure_exact {ι : Insertion} {plan prod : Except Error CountedResult × EvalState}
    (h : Bridged ι plan prod) (e : Error) (he : prod.1 = .error e) : plan.1 = .error e :=
  bridge_failure_exact h.run_eq e he

/-- An address-free result of a bridged pair is EQUAL on the two sides, with its count. -/
theorem Bridged.addressFree_exact {ι : Insertion} {plan prod : Except Error CountedResult × EvalState}
    (h : Bridged ι plan prod) (r : Result) (n : Nat) (hr : prod.1 = .ok (r, n))
    (hfree : ∀ a, ¬ KatLang.AddressInvariant.Mentions r a) : plan.1 = .ok (r, n) :=
  bridge_addressFree_exact h.run_eq r n hr hfree

/-- The two sides of a bridged pair complete together. -/
theorem Bridged.completes {ι : Insertion} {plan prod : Except Error CountedResult × EvalState}
    (h : Bridged ι plan prod) (hc : prod.1 ≠ .error .fuelExhausted) : plan.1 ≠ .error .fuelExhausted :=
  bridge_completes h.run_eq hc

/-! ## Why the self-reference is not an admissible tail input

The value `callRef a` of the plan cell ITSELF is the input that refuted the old universal tail
premise. It is excluded here by a proved fact, not by fiat: from any state where the plan cell's
callee can be established, production's `algorithmOfValue (callRef a)` RECORDS that callee
(`NeedPlan.calleeCell` writes it; every later step keeps a recorded callee —
`EvaluatorMemoLinks`), so the plan cell is no longer `Unrecorded` at its final state: the run
breaks `Frame`, the very relation. The bridges ask `ktail`: the tail keeps the plan cell
`Unrecorded` from every admissible tail entry. So an admissible tail entry is never a completing
self-reference (`tail_entry_not_self_reference`); at a plan's flight the callee establishment does
succeed (`self_reference_breaks_frame_at_flight`). The M0 witness is the same fact reached through
a stored reference. -/

theorem linkDisc_calleeName (a : Nat) : KatLang.MemoLinks.LinkDisc (NeedPlan.calleeName a) :=
  KatLang.MemoLinks.linkDisc_of_needs _ (fun s => by
    show ((get >>= fun st : EvalState =>
      (match NeedPlan.calleeNameIn? st.needs a with
       | some name => pure name
       | none => throw NeedPlan.metaRefusal : EvalM String)).runState s).2.needs = s.needs
    rw [bind_run, get_run]
    dsimp only
    cases NeedPlan.calleeNameIn? s.needs a <;> rfl)

/-- **Production's intrinsic over the plan cell's own reference records that cell's callee.** If the
    callee cell of `a` is established or read at `t`, a completed `algorithmOfValue (callRef a)` from
    `t` ends with the callee RECORDED in `a`: the plan cell is not `Unrecorded` there. -/
theorem self_reference_records_callee (a : Nat) (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv)
    (t t₁ : EvalState) (c : Nat)
    (hcal : (NeedPlan.calleeCell productionPlanRoute.classify a).runState t = (.ok c, t₁))
    (hcomp : ProductionCompletes (algorithmOfValue (.callRef a) (some args) ctx env) t) :
    ¬ Unrecorded a ((algorithmOfValue (.callRef a) (some args) ctx env).runState t).2 := by
  have hcc := (algorithmOfValue_completes_iff _ _ _ _ _).1 hcomp
  rw [algorithmOfValue_eq _ _ _ _ _ hcc]
  have hrest : KatLang.MemoLinks.LinkDisc (capturedCallee c >>= fun algorithm => NeedPlan.calleeName a >>= fun name =>
      evalResolvedCallCounted algorithm args ctx env name (.cell c)) :=
    KatLang.MemoLinks.LinkDisc.bind (show KatLang.MemoLinks.LinkDisc (capturedCallee c) from evalUnbounded_linkDisc (.capturedCallee c))
      (fun algorithm => KatLang.MemoLinks.LinkDisc.bind (linkDisc_calleeName a) (fun name =>
        show KatLang.MemoLinks.LinkDisc (evalResolvedCallCounted algorithm args ctx env name (.cell c)) from
          evalUnbounded_linkDisc (.evalResolvedCallCounted algorithm args ctx env name (.cell c))))
  obtain ⟨d, hd, hdc⟩ := calleeCell_records a c t t₁ hcal
  obtain ⟨d', hd', kd⟩ := hrest t₁ a d hd
  have hrun : (capturedCall (.callRef a) args ctx env).runState t =
      (capturedCallee c >>= fun algorithm => NeedPlan.calleeName a >>= fun name =>
        evalResolvedCallCounted algorithm args ctx env name (.cell c)).runState t₁ := by
    unfold capturedCall
    rw [bind_run]
    have hdec : (decodeCallRef (.callRef a)).runState t = (.ok a, t) := rfl
    rw [hdec]
    dsimp only
    rw [bind_run, hcal]
  rw [hrun]
  intro hun
  unfold Unrecorded at hun
  rw [hd'] at hun
  have hsome : d'.callee = some c := kd.callee c hdc
  rw [Option.bind_some, hsome] at hun
  cases hun

/-- **No admissible tail entry is a completing self-reference.** Under the bridges' preservation
    obligation for the value `callRef a` (`ktail`), there is no tail entry of that value from which
    the plan cell's callee can be established and the tail completes. -/
theorem tail_entry_not_self_reference (E : EvalState → Prop) (a : Nat) (read : EvalM Result)
    (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv)
    (ktail : KeepsOn (After E read (.callRef a)) (Unrecorded a) (algorithmOfValue (.callRef a) (some args) ctx env))
    (t t₁ : EvalState) (c : Nat) (hentry : After E read (.callRef a) t)
    (hcal : (NeedPlan.calleeCell productionPlanRoute.classify a).runState t = (.ok c, t₁))
    (hcomp : ProductionCompletes (algorithmOfValue (.callRef a) (some args) ctx env) t) : False :=
  self_reference_records_callee a args ctx env t t₁ c hcal hcomp (ktail t hentry hcomp)

/-- **At a plan's flight the self-reference breaks `Frame`.** At a valid state where the cell `a`
    holds a written `.Algorithm` invocation over a non-parameter receiver with its `.algorithm` route
    recorded and its callee unrecorded, a completed production `algorithmOfValue (callRef a)` leaves
    the callee RECORDED: the state the old universal premise was instantiated at is one from which
    the tail cannot keep the relation. -/
theorem self_reference_breaks_frame_at_flight (a : Nat) (t : EvalState) (ca : NeedCell)
    (shape : NeedPlan.CallShape) (receiver fallback : Expr) (hinv : Inv t) (ha : t.needs[a]? = some ca)
    (hnone : ca.callee = none) (hshape : NeedPlan.ofSuspension? ca.suspension = some shape)
    (hroute : ca.route = some .algorithm)
    (hedge : shape.callee = .dotMember receiver "Algorithm" fallback none) (hnp : ∀ p, receiver ≠ .param p)
    (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv)
    (hcomp : ProductionCompletes (algorithmOfValue (.callRef a) (some args) ctx env) t) :
    ¬ Frame t.needs.size a ((algorithmOfValue (.callRef a) (some args) ctx env).runState t).2 := by
  obtain ⟨t₁, hcal, -⟩ := establish_run a t ca shape receiver fallback hinv ha hnone hshape hroute hedge hnp
  exact fun hf => self_reference_records_callee a args ctx env t t₁ _ hcal hcomp hf.2.2

/-! ## A parameter receiver: one inserted cell

For `r.Algorithm(args)` / `(r.Algorithm)(args)` with `r` a PARAMETER, the plan's callee link takes
the parameter's own cell as its receiver cell (D-3: nothing is allocated for it) and the plan reads
the receiver by the invocation receiver read of the written parameter at each execution — no
completion shell of its own. So ONE cell is inserted, the link. The dispatch name and origin are
read through the link's receiver cell, the parameter's cell, which must hold the read VALUE
(`hmemo`: the invocation read of a parameter bound to a supplied cell demands that cell). -/

open KatLang.MemberStability (capturedId? captured_run parameterAddressIn)

/-- **The insertion of a planned `.Algorithm` invocation over a PARAMETER receiver**: the callee
    link alone, its receiver the parameter's own cell `cell`. -/
def paramInsertion (base plan : Nat) (edge : Expr) (ctx : EvalCtx) (env : ValEnv) (cell : Nat) : Insertion :=
  ⟨base, [linkCell edge ctx env cell], plan⟩

theorem paramInsertion_site (base plan : Nat) (edge : Expr) (ctx : EvalCtx) (env : ValEnv) (cell : Nat) :
    (paramInsertion base plan edge ctx env cell).site = ⟨base, 1⟩ := rfl

theorem plan_heap_param (h : Array NeedCell) (a : Nat) (ha : a < h.size) (L0 : NeedCell) (b : Nat) :
    (((h.push L0).modify h.size (fun c => { c with invocation := NeedInvocationRole.link })).modify a
        (fun c => { c with callee := some h.size })).modify h.size (fun c => { c with receiver := some b }) =
      ((h.toList.modify a (fun c => { c with callee := some h.size })) ++
        [{ L0 with invocation := NeedInvocationRole.link, receiver := some b }]).toArray := by
  apply Array.ext_getElem?
  intro i
  simp only [List.getElem?_toArray, List.getElem?_append, List.length_modify, Array.length_toList,
    List.getElem?_modify, Array.getElem?_toList, Array.getElem?_modify, Array.getElem?_push]
  by_cases h1 : i < h.size
  · have h2 : ¬ i = h.size := by omega
    have h3 : ¬ h.size = i := by omega
    simp only [h1, h2, h3, ite_true, ite_false]
    by_cases h5 : a = i
    · subst h5
      cases h[a]? <;> simp
    · simp [h5]
  · by_cases h2 : i = h.size
    · subst h2
      have h3 : ¬ a = h.size := by omega
      simp [h3]
    · have h5 : ¬ a = i := by omega
      have h6 : ¬ h.size = i := fun e => h2 e.symm
      have h10 : ([{ L0 with invocation := NeedInvocationRole.link, receiver := some b }] :
          List NeedCell)[i - h.size]? = none := List.getElem?_eq_none (by simp; omega)
      simp [h1, h2, h5, h6, h10]

/-- The first receiver observation of a link over a parameter receiver bound to the cell `b`: the
    parameter's own cell is recorded; nothing is allocated. -/
theorem receiver_param_at (x₁ : EvalState) (k b : Nat) (link : NeedCell) (edge : Expr) (name : Ident)
    (fallback : Expr) (ctx : EvalCtx) (env : ValEnv) (hc : x₁.needs[k]? = some link)
    (hr : link.receiver = none) (hs : link.suspension = .expression edge ctx env)
    (hl : linkEdge? edge = some (.param name, fallback))
    (hsup : (supplyNeed (.param name) ctx env).runState x₁ = (.ok b, x₁)) :
    (NeedLink.receiverCell k).runState x₁ =
      (.ok b, { x₁ with needs := x₁.needs.modify k (fun cell => { cell with receiver := some b }) }) := by
  rw [receiverCell_establishes_ordinary k x₁ link edge (.param name) fallback ctx env hc hr hs hl rfl, hsup]

/-- The plan side's establishment over a parameter receiver bound to the cell `b`: the callee link is
    a fresh cell at the heap's end, marked and recorded in the plan cell, and its receiver cell IS
    `b` — nothing else is allocated and nothing is evaluated. -/
theorem establish_run_param (a : Nat) (x : EvalState) (ca : NeedCell) (shape : NeedPlan.CallShape)
    (name : Ident) (fallback : Expr) (b : Nat) (hinv : Inv x) (ha : x.needs[a]? = some ca)
    (hnone : ca.callee = none) (hshape : NeedPlan.ofSuspension? ca.suspension = some shape)
    (hroute : ca.route = some .algorithm)
    (hedge : shape.callee = .dotMember (.param name) "Algorithm" fallback none)
    (hbound : parameterAddressIn x.lexicalActivations name shape.caller = some b) :
    ∃ x₁, (NeedPlan.calleeCell productionPlanRoute.classify a).runState x = (.ok x.needs.size, x₁) ∧
      (NeedLink.receiverCell x.needs.size).runState x₁ =
        (.ok b, embed (paramInsertion x.needs.size a shape.callee shape.caller shape.values b) x) := by
  have hlt : a < x.needs.size := valid_of_get ha
  have hne : ¬ a = x.needs.size := by omega
  have hlink : linkEdge? shape.callee = some (.param name, fallback) := by rw [hedge]; exact linkEdge_algorithm _ _
  have hnparam : ∀ n, shape.callee ≠ .param n := by rw [hedge]; intro n h; cases h
  have hcal := calleeCell_establishes productionPlanRoute.classify a x ca shape .algorithm ha hnone hshape hroute
    (by decide)
  have heff : NeedPlan.effective shape .algorithm = shape := rfl
  rw [heff, supplyCallee_run, KatLang.NeedControl.Allocation.supply_nonparameter shape.callee shape.caller
    shape.values x hnparam] at hcal
  have hmark : markLink shape .algorithm x.needs.size
      { x with needs := x.needs.push { suspension := .expression shape.callee shape.caller shape.values } } =
      withInvocation x.needs.size .link
        { x with needs := x.needs.push { suspension := .expression shape.callee shape.caller shape.values } } := by
    unfold markLink
    rw [hlink]
    rfl
  dsimp only at hcal
  rw [hmark] at hcal
  refine ⟨_, hcal, ?_⟩
  have hcell : ({ (withInvocation x.needs.size .link
        { x with needs := x.needs.push { suspension := .expression shape.callee shape.caller shape.values } }) with
        needs := (withInvocation x.needs.size .link
          { x with needs := x.needs.push { suspension := .expression shape.callee shape.caller shape.values } }).needs.modify a
            (fun cell => { cell with callee := some x.needs.size }) } : EvalState).needs[x.needs.size]? =
      some ({ suspension := .expression shape.callee shape.caller shape.values, invocation := .link } : NeedCell) := by
    simp only [withInvocation]
    rw [Array.getElem?_modify, Array.getElem?_modify, Array.getElem?_push]
    simp only [hne, ite_false, ite_true, Option.map_some]
  -- the parameter's cell is found in the state the callee establishment leaves: only the heap changed
  have hsupply : ∀ s : EvalState, s.lexicalActivations = x.lexicalActivations →
      (supplyNeed (.param name) shape.caller shape.values).runState s = (.ok b, s) := by
    intro s hs
    refine KatLang.NeedControl.Allocation.supply_param_transports name shape.caller shape.values s
      ((capturedId? name shape.caller).bind (fun id => s.lexicalActivations[id]?)) b (captured_run name shape.caller s) ?_
    rw [hs]
    exact hbound
  rw [receiver_param_at _ x.needs.size b _ shape.callee name fallback shape.caller shape.values hcell rfl rfl hlink
    (hsupply _ rfl)]
  rw [embed_of_valid _ x hinv rfl]
  simp only [withInvocation]
  congr 1
  exact congrArg (fun needs => ({ x with needs := needs } : EvalState))
    (plan_heap_param x.needs a hlt { suspension := .expression shape.callee shape.caller shape.values } b)

/-- **THE `.Algorithm` BRIDGE over a PARAMETER receiver, at the production core.** As
    `algorithm_core_bridge`, with ONE inserted cell — the link, whose receiver is the parameter's own
    cell `b` — and no completion shell: the plan reads the receiver by the invocation receiver read
    of the written parameter. `hmemo`: after production's read, the parameter's cell holds the read
    VALUE (the read demands the supplied cell), which is what the heap-read dispatch name and origin
    go through. -/
theorem algorithm_core_bridge_param (E : EvalState → Prop) (a : Nat) (shape : NeedPlan.CallShape)
    (name : Ident) (fallback : Expr) (x : EvalState) (ca : NeedCell) (b : Nat)
    (hedge : shape.callee = .dotMember (.param name) "Algorithm" fallback none)
    (ha : x.needs[a]? = some ca) (hshape : NeedPlan.ofSuspension? ca.suspension = some shape)
    (hroute : ca.route = some .algorithm) (hnone : ca.callee = none)
    (hbound : parameterAddressIn x.lexicalActivations name shape.caller = some b) (hbk : b < x.needs.size)
    (hinv : Inv x) (hE : E x)
    (cread : InsertedAt E (paramInsertion x.needs.size a shape.callee shape.caller shape.values b) shiftResult
      (invocationReceiverValue (.param name) shape.caller shape.values)
      (invocationReceiverValue (.param name) shape.caller shape.values))
    (kread : KeepsOn E (Unrecorded a) (invocationReceiverValue (.param name) shape.caller shape.values))
    (hmemo : ∀ v, ((invocationReceiverValue (.param name) shape.caller shape.values).runState x).1 = .ok v →
      ∃ cell cnt, ((invocationReceiverValue (.param name) shape.caller shape.values).runState x).2.needs[b]? = some cell ∧
        cell.state = .completed (.ok (v, cnt)))
    (hentry : ∀ v t, After E (invocationReceiverValue (.param name) shape.caller shape.values) v t → PlanCallees t)
    (ctail : ∀ v, InsertedAt (After E (invocationReceiverValue (.param name) shape.caller shape.values) v)
      (paramInsertion x.needs.size a shape.callee shape.caller shape.values b) shiftCounted
      (algorithmOfValue (shiftResult ⟨x.needs.size, 1⟩ v) (some shape.args) shape.caller shape.values)
      (algorithmOfValue v (some shape.args) shape.caller shape.values))
    (ktail : ∀ v, KeepsOn (After E (invocationReceiverValue (.param name) shape.caller shape.values) v) (Unrecorded a)
      (algorithmOfValue v (some shape.args) shape.caller shape.values))
    (hcomp : ProductionCompletes
      (algorithmProduction shape.ctxMsg (.param name) shape.args shape.caller shape.values) x) :
    Bridged (paramInsertion x.needs.size a shape.callee shape.caller shape.values b)
      ((ordinaryCall productionPlanRoute a shape .algorithm).runState x)
      ((algorithmProduction shape.ctxMsg (.param name) shape.args shape.caller shape.values).runState x) := by
  have hframeFinal := production_frame E a shape.ctxMsg (.param name) shape.args shape.caller shape.values x ca ha hE
    kread ktail hcomp
  have hU1c : ProductionCompletes (invocationReceiverValue (.param name) shape.caller shape.values) x := by
    intro hinc
    apply hcomp
    unfold algorithmProduction algorithmCore
    rw [map_run, ctx_run, bind_run]
    rcases hr : (invocationReceiverValue (.param name) shape.caller shape.values).runState x with ⟨o, t⟩
    rw [hr] at hinc
    simp only at hinc
    subst hinc
    rfl
  have hlink : linkEdge? shape.callee = some (.param name, fallback) := by rw [hedge]; exact linkEdge_algorithm _ _
  obtain ⟨x₁, hcal, hrcv⟩ := establish_run_param a x ca shape name fallback b hinv ha hnone hshape hroute hedge hbound
  have hle : (paramInsertion x.needs.size a shape.callee shape.caller shape.values b).base ≤ x.needs.size :=
    Nat.le_refl _
  have hgetL : (embed (paramInsertion x.needs.size a shape.callee shape.caller shape.values b) x).needs[x.needs.size]? =
      some (linkCell shape.callee shape.caller shape.values b) :=
    embedNeeds_inserted (paramInsertion x.needs.size a shape.callee shape.caller shape.values b) x.needs hle 0
      (Nat.zero_lt_succ 0)
  have hprv : plannedReceiverValue (linkCell shape.callee shape.caller shape.values b) b =
      invocationReceiverValue (.param name) shape.caller shape.values :=
    plannedReceiverValue_param _ _ shape.callee fallback name shape.caller shape.values rfl hlink
  -- the head: the receiver VALUE
  obtain ⟨hiff, hrun⟩ := cread x hE
  have hrun := hrun hU1c
  have hhead : (NeedPlan.calleeCell productionPlanRoute.classify a >>= plannedValue).runState x =
      (shiftExcept (shiftResult ⟨x.needs.size, 1⟩)
          ((invocationReceiverValue (.param name) shape.caller shape.values).runState x).1,
        embed (paramInsertion x.needs.size a shape.callee shape.caller shape.values b)
          ((invocationReceiverValue (.param name) shape.caller shape.values).runState x).2) := by
    rw [bind_run, hcal]
    unfold plannedValue
    simp only [bind_run, hrcv, get_run, hgetL]
    rw [hprv]
    exact hrun
  have hK1 : HeapKept x.needs ((invocationReceiverValue (.param name) shape.caller shape.values).runState x).2.needs :=
    disciplined_invocationReceiverValue (.param name) shape.caller shape.values x
  have hplanRun : (algorithmPlanCall a shape).runState x =
      (shiftExcept (shiftCounted ⟨x.needs.size, 1⟩)
          ((algorithmProduction shape.ctxMsg (.param name) shape.args shape.caller shape.values).runState x).1,
        embed (paramInsertion x.needs.size a shape.callee shape.caller shape.values b)
          ((algorithmProduction shape.ctxMsg (.param name) shape.args shape.caller shape.values).runState x).2) := by
    unfold algorithmProduction algorithmCore at hcomp ⊢
    unfold ProductionCompletes at hcomp
    rw [map_run, ctx_run, bind_run] at hcomp ⊢
    rw [algorithmPlanCall_split, map_run, bind_run, ctx_run, hhead]
    rcases hr : (invocationReceiverValue (.param name) shape.caller shape.values).runState x with ⟨o₁, x₄⟩
    rw [hr] at hcomp hK1 hmemo
    simp only at hK1 hmemo
    cases o₁ with
    | error e =>
      simp only at hcomp
      cases e <;> first | exact absurd rfl hcomp | rfl
    | ok v =>
      dsimp only at hcomp ⊢
      have hle₄ : x.needs.size ≤ x₄.needs.size := heapKept_size hK1
      have halt : a < x.needs.size := valid_of_get ha
      have htc : ProductionCompletes (algorithmOfValue v (some shape.args) shape.caller shape.values) x₄ := by
        intro hinc
        apply hcomp
        rcases ht : (algorithmOfValue v (some shape.args) shape.caller shape.values).runState x₄ with ⟨o, t⟩
        rw [ht] at hinc
        simp only at hinc
        subst hinc
        rfl
      obtain ⟨ca₄, hca₄, kca⟩ := hK1 a ca ha
      have hplanCell : (NeedPlan.ofSuspension? ca₄.suspension).isSome := by
        rw [kca.suspension, hshape]; rfl
      obtain ⟨cellb, cnt, hcb, hstb⟩ := hmemo v rfl
      have hyl := embedNeeds_inserted (paramInsertion x.needs.size a shape.callee shape.caller shape.values b)
        x₄.needs hle₄ 0 (Nat.zero_lt_succ 0)
      have hyr := embedNeeds_below (paramInsertion x.needs.size a shape.callee shape.caller shape.values b)
        x₄.needs hle₄ b hbk cellb hcb
      have hst : (embedCell (paramInsertion x.needs.size a shape.callee shape.caller shape.values b) b cellb).state =
          .completed (.ok (shiftResult (paramInsertion x.needs.size a shape.callee shape.caller shape.values b).site v, cnt)) := by
        rw [embedCell_state, hstb]
        rfl
      have htail := tail_bridge (After E (invocationReceiverValue (.param name) shape.caller shape.values) v) a shape
        (paramInsertion x.needs.size a shape.callee shape.caller shape.values b) b x₄ v ca₄ _ _ cnt rfl halt hle₄
        ⟨x, hE, hr⟩ (hentry v x₄ ⟨x, hE, hr⟩) hca₄ hplanCell hyl rfl hyr hst (ctail v) htc
      simp only [paramInsertion_site] at htail
      rcases ht : (algorithmOfValue v (some shape.args) shape.caller shape.values).runState x₄ with ⟨o₂, x₅⟩
      rw [ht] at hcomp htail
      simp only at htail
      have hne₂ : o₂ ≠ .error .fuelExhausted := by
        intro h
        subst h
        exact hcomp rfl
      have hctxv : ctxOutcome shape.ctxMsg
          (shiftExcept (shiftResult ⟨x.needs.size, 1⟩) (Except.ok v),
            embed (paramInsertion x.needs.size a shape.callee shape.caller shape.values b) x₄) =
          (.ok (shiftResult ⟨x.needs.size, 1⟩ v),
            embed (paramInsertion x.needs.size a shape.callee shape.caller shape.values b) x₄) := rfl
      rw [hctxv]
      dsimp only
      rw [htail]
      cases o₂ with
      | ok r =>
        show ((Except.ok (reCountValueBoundary (shiftCounted ⟨x.needs.size, 1⟩ r)) : Except Error CountedResult), _) = _
        rw [reCount_shift]
        rfl
      | error e => cases e <;> first | exact absurd rfl hne₂ | rfl
  have hplanc : ((algorithmPlanCall a shape).runState x).1 ≠ .error .fuelExhausted := by
    rw [hplanRun]
    unfold ProductionCompletes at hcomp
    revert hcomp
    rcases (algorithmProduction shape.ctxMsg (.param name) shape.args shape.caller shape.values).runState x with ⟨o, t⟩
    intro hcomp
    cases o with
    | ok r => nofun
    | error e => cases e <;> first | exact absurd rfl hcomp | nofun
  have hrunEq : (ordinaryCall productionPlanRoute a shape .algorithm).runState x =
      (shiftExcept (shiftCounted ⟨x.needs.size, 1⟩)
          ((algorithmProduction shape.ctxMsg (.param name) shape.args shape.caller shape.values).runState x).1,
        embed (paramInsertion x.needs.size a shape.callee shape.caller shape.values b)
          ((algorithmProduction shape.ctxMsg (.param name) shape.args shape.caller shape.values).runState x).2) := by
    rw [ordinaryCall_algorithm_is_production a shape x hplanc, hplanRun]
  exact ⟨congrArg Prod.fst hrunEq, hframeFinal, congrArg Prod.snd hrunEq⟩

/-- **THE `.Algorithm` BRIDGE over a PARAMETER receiver, dot form `r.Algorithm(args)`.** As
    `algorithm_bridge_dot`, with the one-cell insertion `paramInsertion`: the parameter `r` is bound to
    the cell `b`, which holds the read VALUE after production's receiver read (`hmemo`). -/
theorem algorithm_bridge_dot_param (E : EvalState → Prop) (a : Nat) (name : Ident) (fallback : Expr)
    (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) (x x' : EvalState) (alg? : Option Algorithm)
    (ca : NeedCell) (b : Nat)
    (ha : x.needs[a]? = some ca)
    (hsus : ca.suspension = .expression (.dotMember (.param name) "Algorithm" fallback (some args)) ctx env)
    (hroute : ca.route = some .algorithm) (hnone : ca.callee = none)
    (hprobe : (resolveDotReceiver? (.param name) ctx).runState x = (.ok alg?, x'))
    (hmiss : selectDotEdge ctx (.param name) "Algorithm" alg? = .ok (.miss .algorithm))
    (hbound : parameterAddressIn x.lexicalActivations name ctx = some b) (hbk : b < x.needs.size)
    (hinv : Inv x) (hE : E x)
    (cread : InsertedAt E
      (paramInsertion x.needs.size a (.dotMember (.param name) "Algorithm" fallback none) ctx env b) shiftResult
      (invocationReceiverValue (.param name) ctx env) (invocationReceiverValue (.param name) ctx env))
    (kread : KeepsOn E (Unrecorded a) (invocationReceiverValue (.param name) ctx env))
    (hmemo : ∀ v, ((invocationReceiverValue (.param name) ctx env).runState x).1 = .ok v →
      ∃ cell cnt, ((invocationReceiverValue (.param name) ctx env).runState x).2.needs[b]? = some cell ∧
        cell.state = .completed (.ok (v, cnt)))
    (hentry : ∀ v t, After E (invocationReceiverValue (.param name) ctx env) v t → PlanCallees t)
    (ctail : ∀ v, InsertedAt (After E (invocationReceiverValue (.param name) ctx env) v)
      (paramInsertion x.needs.size a (.dotMember (.param name) "Algorithm" fallback none) ctx env b) shiftCounted
      (algorithmOfValue (shiftResult ⟨x.needs.size, 1⟩ v) (some args) ctx env)
      (algorithmOfValue v (some args) ctx env))
    (ktail : ∀ v, KeepsOn (After E (invocationReceiverValue (.param name) ctx env) v) (Unrecorded a)
      (algorithmOfValue v (some args) ctx env))
    (hprod : ProductionCompletes
      (evalCounted (.dotMember (.param name) "Algorithm" fallback (some args)) ctx env) x) :
    Bridged (paramInsertion x.needs.size a (.dotMember (.param name) "Algorithm" fallback none) ctx env b)
      ((ordinaryCall productionPlanRoute a (dotShape (.param name) fallback args ctx env) .algorithm).runState x)
      ((reCountValueBoundary <$>
        evalCounted (.dotMember (.param name) "Algorithm" fallback (some args)) ctx env).runState x) := by
  have hprodEq : (algorithmProduction (CtxMsg.dotCall (.param name) "Algorithm") (.param name) args ctx env).runState x =
      (reCountValueBoundary <$>
        evalCounted (.dotMember (.param name) "Algorithm" fallback (some args)) ctx env).runState x := by
    unfold algorithmProduction
    rw [map_run, map_run, ctx_run, dot_is_core (.param name) fallback args ctx env x x' alg? hprobe hmiss hprod]
  have hcomp : ProductionCompletes
      (algorithmProduction (CtxMsg.dotCall (.param name) "Algorithm") (.param name) args ctx env) x := by
    unfold ProductionCompletes
    rw [hprodEq]
    exact map_completes _ _ x hprod
  have h := algorithm_core_bridge_param E a (dotShape (.param name) fallback args ctx env) name fallback x ca b rfl ha
    (by rw [hsus]; rfl) hroute hnone hbound hbk hinv hE cread kread hmemo hentry ctail ktail hcomp
  have he : algorithmProduction (NeedPlan.CallShape.ctxMsg (dotShape (.param name) fallback args ctx env)) (.param name)
      (dotShape (.param name) fallback args ctx env).args (dotShape (.param name) fallback args ctx env).caller
      (dotShape (.param name) fallback args ctx env).values =
      algorithmProduction (CtxMsg.dotCall (.param name) "Algorithm") (.param name) args ctx env := rfl
  rw [he, hprodEq] at h
  exact h

/-- **THE `.Algorithm` BRIDGE over a PARAMETER receiver, grouped form `(r.Algorithm)(args)`.** As
    `algorithm_bridge_grouped`, with the one-cell insertion `paramInsertion`. -/
theorem algorithm_bridge_grouped_param (E : EvalState → Prop) (a : Nat) (name : Ident) (fallback : Expr)
    (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) (s x : EvalState) (ca : NeedCell) (b : Nat)
    (hdecided : (withCtx (CtxMsg.call (.dotMember (.param name) "Algorithm" fallback none))
      (algorithmIntrinsicRoute (.param name) ctx)).runState s = (.ok true, x))
    (ha : x.needs[a]? = some ca)
    (hsus : ca.suspension = .expression (.call (.dotMember (.param name) "Algorithm" fallback none) args) ctx env)
    (hroute : ca.route = some .algorithm) (hnone : ca.callee = none)
    (hbound : parameterAddressIn x.lexicalActivations name ctx = some b) (hbk : b < x.needs.size)
    (hinv : Inv x) (hE : E x)
    (cread : InsertedAt E
      (paramInsertion x.needs.size a (.dotMember (.param name) "Algorithm" fallback none) ctx env b) shiftResult
      (invocationReceiverValue (.param name) ctx env) (invocationReceiverValue (.param name) ctx env))
    (kread : KeepsOn E (Unrecorded a) (invocationReceiverValue (.param name) ctx env))
    (hmemo : ∀ v, ((invocationReceiverValue (.param name) ctx env).runState x).1 = .ok v →
      ∃ cell cnt, ((invocationReceiverValue (.param name) ctx env).runState x).2.needs[b]? = some cell ∧
        cell.state = .completed (.ok (v, cnt)))
    (hentry : ∀ v t, After E (invocationReceiverValue (.param name) ctx env) v t → PlanCallees t)
    (ctail : ∀ v, InsertedAt (After E (invocationReceiverValue (.param name) ctx env) v)
      (paramInsertion x.needs.size a (.dotMember (.param name) "Algorithm" fallback none) ctx env b) shiftCounted
      (algorithmOfValue (shiftResult ⟨x.needs.size, 1⟩ v) (some args) ctx env)
      (algorithmOfValue v (some args) ctx env))
    (ktail : ∀ v, KeepsOn (After E (invocationReceiverValue (.param name) ctx env) v) (Unrecorded a)
      (algorithmOfValue v (some args) ctx env))
    (hprod : ProductionCompletes
      (evalCallCountedExpr (.dotMember (.param name) "Algorithm" fallback none) args ctx env) s) :
    Bridged (paramInsertion x.needs.size a (.dotMember (.param name) "Algorithm" fallback none) ctx env b)
      ((ordinaryCall productionPlanRoute a (groupedShape (.param name) fallback args ctx env) .algorithm).runState x)
      ((reCountValueBoundary <$>
        evalCallCountedExpr (.dotMember (.param name) "Algorithm" fallback none) args ctx env).runState s) := by
  have hprodEq : (algorithmProduction (CtxMsg.call (.dotMember (.param name) "Algorithm" fallback none)) (.param name)
        args ctx env).runState x =
      (reCountValueBoundary <$>
        evalCallCountedExpr (.dotMember (.param name) "Algorithm" fallback none) args ctx env).runState s := by
    unfold algorithmProduction
    rw [map_run, map_run, ctx_run,
      grouped_is_core (.dotMember (.param name) "Algorithm" fallback none) (.param name) fallback args ctx env s x
        (linkEdge_algorithm (.param name) fallback) hdecided hprod]
  have hcomp : ProductionCompletes
      (algorithmProduction (CtxMsg.call (.dotMember (.param name) "Algorithm" fallback none)) (.param name) args
        ctx env) x := by
    unfold ProductionCompletes
    rw [hprodEq]
    exact map_completes _ _ s hprod
  have h := algorithm_core_bridge_param E a (groupedShape (.param name) fallback args ctx env) name fallback x ca b rfl
    ha (by rw [hsus]; rfl) hroute hnone hbound hbk hinv hE cread kread hmemo hentry ctail ktail hcomp
  have he : algorithmProduction (NeedPlan.CallShape.ctxMsg (groupedShape (.param name) fallback args ctx env))
      (.param name) (groupedShape (.param name) fallback args ctx env).args
      (groupedShape (.param name) fallback args ctx env).caller
      (groupedShape (.param name) fallback args ctx env).values =
      algorithmProduction (CtxMsg.call (.dotMember (.param name) "Algorithm" fallback none)) (.param name) args
        ctx env := rfl
  rw [he, hprodEq] at h
  exact h

/-! ## At ONE comparison state: the finite-domain forms

The bridges at the SINGLETON entry domain `fun s => s = x`. Then the admissible tail entries of a
value `v` are at most one state — production's state after ITS receiver read from `x`, when that
read returns `v` — and every contract premise is a plain equation between two runs: this is the
form a concrete reached state instantiates (`PlanAlgorithmBridgeInstances`), every premise a
decided fact about that state. Nothing is asked of any other state, insertion or value. -/

theorem shiftExcept_fuel_iff {α : Type} (f : α → α) (o : Except Error α) :
    shiftExcept f o = .error .fuelExhausted ↔ o = .error .fuelExhausted := by
  cases o with
  | ok v => exact ⟨nofun, nofun⟩
  | error e => exact Iff.rfl

/-- The contract at one insertion over ONE state is one equation between the two runs. -/
theorem insertedAt_singleton {α : Type} {ι : Insertion} {ρ : Site → α → α} {mp mo : EvalM α} {x t : EvalState}
    {o : Except Error α} (hmo : mo.runState x = (o, t))
    (hmp : mp.runState (embed ι x) = (shiftExcept (ρ ι.site) o, embed ι t)) :
    InsertedAt (fun s => s = x) ι ρ mp mo := by
  intro s hs
  subst hs
  rw [hmo, hmp]
  exact ⟨shiftExcept_fuel_iff _ _, fun _ => rfl⟩

/-- The reachable results of a computation from ONE state: its own result there. -/
theorem after_singleton {α : Type} {m : EvalM α} {x t : EvalState} {o : Except Error α}
    (hm : m.runState x = (o, t)) {v : α} {s : EvalState} (h : After (fun s => s = x) m v s) :
    o = .ok v ∧ s = t := by
  obtain ⟨s₀, hs₀, hr⟩ := h
  subst hs₀
  rw [hm] at hr
  exact ⟨congrArg Prod.fst hr, (congrArg Prod.snd hr).symm⟩

/-- The contract from the tail entries of `v` over ONE comparison state: one equation between the
    two tail runs, asked only when the receiver read returned `v`. -/
theorem insertedAt_after_singleton {α β : Type} {read : EvalM α} {x x₄ : EvalState} {o₁ : Except Error α}
    (hread : read.runState x = (o₁, x₄)) {v : α} {ι : Insertion} {ρ : Site → β → β} {mp mo : EvalM β}
    (h : o₁ = .ok v → ∃ o₂ x₅, mo.runState x₄ = (o₂, x₅) ∧
      mp.runState (embed ι x₄) = (shiftExcept (ρ ι.site) o₂, embed ι x₅)) :
    InsertedAt (After (fun s => s = x) read v) ι ρ mp mo := by
  intro s hs
  obtain ⟨ho, hst⟩ := after_singleton hread hs
  subst hst
  obtain ⟨o₂, x₅, hmo, hmp⟩ := h ho
  rw [hmo, hmp]
  exact ⟨shiftExcept_fuel_iff _ _, fun _ => rfl⟩

/-- **THE `.Algorithm` BRIDGE, dot form, AT ONE STATE.** `algorithm_bridge_dot` at the singleton entry
    domain: production's receiver read from `x` (`hread`) and the plan side's from the plan-side
    state with the receiver cell `evaluating` (`hreadP`); the plan cell `Unrecorded` after the read
    (`hreadU`); and, when the read returned a VALUE `v` (`htail`): `PlanCallees` there, production's
    tail (`algorithmOfValue v`) and the plan side's from the plan-side state with the receiver cell
    completed with `v`, and the plan cell `Unrecorded` after the tail. -/
theorem algorithm_bridge_dot_at (a : Nat) (target fallback : Expr) (args : OutputBundle)
    (ctx : EvalCtx) (env : ValEnv) (x x' : EvalState) (alg? : Option Algorithm) (ca : NeedCell)
    (hnp : ∀ p, target ≠ .param p)
    (ha : x.needs[a]? = some ca)
    (hsus : ca.suspension = .expression (.dotMember target "Algorithm" fallback (some args)) ctx env)
    (hroute : ca.route = some .algorithm) (hnone : ca.callee = none)
    (hprobe : (resolveDotReceiver? target ctx).runState x = (.ok alg?, x'))
    (hmiss : selectDotEdge ctx target "Algorithm" alg? = .ok (.miss .algorithm))
    (hinv : Inv x)
    (o₁ : Except Error Result) (x₄ : EvalState)
    (hread : (invocationReceiverValue target ctx env).runState x = (o₁, x₄))
    (hreadP : (invocationReceiverValue target ctx env).runState
        (embed (planInsertion x.needs.size a (.dotMember target "Algorithm" fallback none) ctx env .evaluating) x) =
      (shiftExcept (shiftResult ⟨x.needs.size, 2⟩) o₁,
        embed (planInsertion x.needs.size a (.dotMember target "Algorithm" fallback none) ctx env .evaluating) x₄))
    (hreadU : Unrecorded a x₄)
    (htail : ∀ v, o₁ = .ok v → PlanCallees x₄ ∧ ∃ o₂ x₅,
      (algorithmOfValue v (some args) ctx env).runState x₄ = (o₂, x₅) ∧
      (algorithmOfValue (shiftResult ⟨x.needs.size, 2⟩ v) (some args) ctx env).runState
          (embed (planInsertion x.needs.size a (.dotMember target "Algorithm" fallback none) ctx env
            (.completed (receiverMemo ⟨x.needs.size, 2⟩ (.ok v)))) x₄) =
        (shiftExcept (shiftCounted ⟨x.needs.size, 2⟩) o₂,
          embed (planInsertion x.needs.size a (.dotMember target "Algorithm" fallback none) ctx env
            (.completed (receiverMemo ⟨x.needs.size, 2⟩ (.ok v)))) x₅) ∧
      Unrecorded a x₅)
    (hprod : ProductionCompletes (evalCounted (.dotMember target "Algorithm" fallback (some args)) ctx env) x) :
    Bridged (finalInsertion x a (dotShape target fallback args ctx env) target)
      ((ordinaryCall productionPlanRoute a (dotShape target fallback args ctx env) .algorithm).runState x)
      ((reCountValueBoundary <$> evalCounted (.dotMember target "Algorithm" fallback (some args)) ctx env).runState x) := by
  refine algorithm_bridge_dot (fun s => s = x) a target fallback args ctx env x x' alg? ca hnp ha hsus hroute hnone
    hprobe hmiss hinv rfl (insertedAt_singleton hread hreadP) ?_ ?_ ?_ ?_ hprod
  · intro s hs _
    subst hs
    rw [hread]
    exact hreadU
  · intro v t h
    obtain ⟨ho, hst⟩ := after_singleton hread h
    subst hst
    exact (htail v ho).1
  · intro v
    refine insertedAt_after_singleton hread (fun ho => ?_)
    obtain ⟨-, o₂, x₅, hmo, hmp, -⟩ := htail v ho
    exact ⟨o₂, x₅, hmo, hmp⟩
  · intro v s hs _
    obtain ⟨ho, hst⟩ := after_singleton hread hs
    subst hst
    obtain ⟨-, o₂, x₅, hmo, -, hu⟩ := htail v ho
    rw [hmo]
    exact hu

/-- **THE `.Algorithm` BRIDGE, grouped form, AT ONE STATE** (`algorithm_bridge_grouped_settled` at
    the singleton entry domain: production's route decision is settled at the flight `x`, and both
    sides run from `x`). -/
theorem algorithm_bridge_grouped_at (a : Nat) (receiver fallback : Expr) (args : OutputBundle)
    (ctx : EvalCtx) (env : ValEnv) (x : EvalState) (ca : NeedCell)
    (hnp : ∀ p, receiver ≠ .param p)
    (hsettled : (withCtx (CtxMsg.call (.dotMember receiver "Algorithm" fallback none))
      (algorithmIntrinsicRoute receiver ctx)).runState x = (.ok true, x))
    (ha : x.needs[a]? = some ca)
    (hsus : ca.suspension = .expression (.call (.dotMember receiver "Algorithm" fallback none) args) ctx env)
    (hroute : ca.route = some .algorithm) (hnone : ca.callee = none)
    (hinv : Inv x)
    (o₁ : Except Error Result) (x₄ : EvalState)
    (hread : (invocationReceiverValue receiver ctx env).runState x = (o₁, x₄))
    (hreadP : (invocationReceiverValue receiver ctx env).runState
        (embed (planInsertion x.needs.size a (.dotMember receiver "Algorithm" fallback none) ctx env .evaluating) x) =
      (shiftExcept (shiftResult ⟨x.needs.size, 2⟩) o₁,
        embed (planInsertion x.needs.size a (.dotMember receiver "Algorithm" fallback none) ctx env .evaluating) x₄))
    (hreadU : Unrecorded a x₄)
    (htail : ∀ v, o₁ = .ok v → PlanCallees x₄ ∧ ∃ o₂ x₅,
      (algorithmOfValue v (some args) ctx env).runState x₄ = (o₂, x₅) ∧
      (algorithmOfValue (shiftResult ⟨x.needs.size, 2⟩ v) (some args) ctx env).runState
          (embed (planInsertion x.needs.size a (.dotMember receiver "Algorithm" fallback none) ctx env
            (.completed (receiverMemo ⟨x.needs.size, 2⟩ (.ok v)))) x₄) =
        (shiftExcept (shiftCounted ⟨x.needs.size, 2⟩) o₂,
          embed (planInsertion x.needs.size a (.dotMember receiver "Algorithm" fallback none) ctx env
            (.completed (receiverMemo ⟨x.needs.size, 2⟩ (.ok v)))) x₅) ∧
      Unrecorded a x₅)
    (hprod : ProductionCompletes
      (evalCallCountedExpr (.dotMember receiver "Algorithm" fallback none) args ctx env) x) :
    Bridged (finalInsertion x a (groupedShape receiver fallback args ctx env) receiver)
      ((ordinaryCall productionPlanRoute a (groupedShape receiver fallback args ctx env) .algorithm).runState x)
      ((reCountValueBoundary <$>
        evalCallCountedExpr (.dotMember receiver "Algorithm" fallback none) args ctx env).runState x) := by
  refine algorithm_bridge_grouped_settled (fun s => s = x) a receiver fallback args ctx env x ca hnp hsettled ha hsus
    hroute hnone hinv rfl (insertedAt_singleton hread hreadP) ?_ ?_ ?_ ?_ hprod
  · intro s hs _
    subst hs
    rw [hread]
    exact hreadU
  · intro v t h
    obtain ⟨ho, hst⟩ := after_singleton hread h
    subst hst
    exact (htail v ho).1
  · intro v
    refine insertedAt_after_singleton hread (fun ho => ?_)
    obtain ⟨-, o₂, x₅, hmo, hmp, -⟩ := htail v ho
    exact ⟨o₂, x₅, hmo, hmp⟩
  · intro v s hs _
    obtain ⟨ho, hst⟩ := after_singleton hread hs
    subst hst
    obtain ⟨-, o₂, x₅, hmo, -, hu⟩ := htail v ho
    rw [hmo]
    exact hu

/-- **THE `.Algorithm` BRIDGE over a PARAMETER receiver, dot form, AT ONE STATE**
    (`algorithm_bridge_dot_param` at the singleton entry domain; ONE inserted cell, the same
    insertion for the read and the tail; `hcellb`: after production's read the parameter's cell holds
    the read VALUE). -/
theorem algorithm_bridge_dot_param_at (a : Nat) (name : Ident) (fallback : Expr)
    (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) (x x' : EvalState) (alg? : Option Algorithm)
    (ca : NeedCell) (b : Nat)
    (ha : x.needs[a]? = some ca)
    (hsus : ca.suspension = .expression (.dotMember (.param name) "Algorithm" fallback (some args)) ctx env)
    (hroute : ca.route = some .algorithm) (hnone : ca.callee = none)
    (hprobe : (resolveDotReceiver? (.param name) ctx).runState x = (.ok alg?, x'))
    (hmiss : selectDotEdge ctx (.param name) "Algorithm" alg? = .ok (.miss .algorithm))
    (hbound : parameterAddressIn x.lexicalActivations name ctx = some b) (hbk : b < x.needs.size)
    (hinv : Inv x)
    (o₁ : Except Error Result) (x₄ : EvalState)
    (hread : (invocationReceiverValue (.param name) ctx env).runState x = (o₁, x₄))
    (hreadP : (invocationReceiverValue (.param name) ctx env).runState
        (embed (paramInsertion x.needs.size a (.dotMember (.param name) "Algorithm" fallback none) ctx env b) x) =
      (shiftExcept (shiftResult ⟨x.needs.size, 1⟩) o₁,
        embed (paramInsertion x.needs.size a (.dotMember (.param name) "Algorithm" fallback none) ctx env b) x₄))
    (hreadU : Unrecorded a x₄)
    (htail : ∀ v, o₁ = .ok v → PlanCallees x₄ ∧
      (∃ cell cnt, x₄.needs[b]? = some cell ∧ cell.state = .completed (.ok (v, cnt))) ∧
      ∃ o₂ x₅,
      (algorithmOfValue v (some args) ctx env).runState x₄ = (o₂, x₅) ∧
      (algorithmOfValue (shiftResult ⟨x.needs.size, 1⟩ v) (some args) ctx env).runState
          (embed (paramInsertion x.needs.size a (.dotMember (.param name) "Algorithm" fallback none) ctx env b) x₄) =
        (shiftExcept (shiftCounted ⟨x.needs.size, 1⟩) o₂,
          embed (paramInsertion x.needs.size a (.dotMember (.param name) "Algorithm" fallback none) ctx env b) x₅) ∧
      Unrecorded a x₅)
    (hprod : ProductionCompletes
      (evalCounted (.dotMember (.param name) "Algorithm" fallback (some args)) ctx env) x) :
    Bridged (paramInsertion x.needs.size a (.dotMember (.param name) "Algorithm" fallback none) ctx env b)
      ((ordinaryCall productionPlanRoute a (dotShape (.param name) fallback args ctx env) .algorithm).runState x)
      ((reCountValueBoundary <$>
        evalCounted (.dotMember (.param name) "Algorithm" fallback (some args)) ctx env).runState x) := by
  refine algorithm_bridge_dot_param (fun s => s = x) a name fallback args ctx env x x' alg? ca b ha hsus hroute hnone
    hprobe hmiss hbound hbk hinv rfl (insertedAt_singleton hread hreadP) ?_ ?_ ?_ ?_ ?_ hprod
  · intro s hs _
    subst hs
    rw [hread]
    exact hreadU
  · intro v hv
    rw [hread] at hv ⊢
    exact (htail v hv).2.1
  · intro v t h
    obtain ⟨ho, hst⟩ := after_singleton hread h
    subst hst
    exact (htail v ho).1
  · intro v
    refine insertedAt_after_singleton hread (fun ho => ?_)
    obtain ⟨-, -, o₂, x₅, hmo, hmp, -⟩ := htail v ho
    exact ⟨o₂, x₅, hmo, hmp⟩
  · intro v s hs _
    obtain ⟨ho, hst⟩ := after_singleton hread hs
    subst hst
    obtain ⟨-, -, o₂, x₅, hmo, -, hu⟩ := htail v ho
    rw [hmo]
    exact hu

/-- **THE `.Algorithm` BRIDGE over a PARAMETER receiver, grouped form, AT ONE STATE**
    (`algorithm_bridge_grouped_param` at the singleton entry domain, the route decision settled at
    the flight `x`). -/
theorem algorithm_bridge_grouped_param_at (a : Nat) (name : Ident) (fallback : Expr)
    (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) (x : EvalState) (ca : NeedCell) (b : Nat)
    (hsettled : (withCtx (CtxMsg.call (.dotMember (.param name) "Algorithm" fallback none))
      (algorithmIntrinsicRoute (.param name) ctx)).runState x = (.ok true, x))
    (ha : x.needs[a]? = some ca)
    (hsus : ca.suspension = .expression (.call (.dotMember (.param name) "Algorithm" fallback none) args) ctx env)
    (hroute : ca.route = some .algorithm) (hnone : ca.callee = none)
    (hbound : parameterAddressIn x.lexicalActivations name ctx = some b) (hbk : b < x.needs.size)
    (hinv : Inv x)
    (o₁ : Except Error Result) (x₄ : EvalState)
    (hread : (invocationReceiverValue (.param name) ctx env).runState x = (o₁, x₄))
    (hreadP : (invocationReceiverValue (.param name) ctx env).runState
        (embed (paramInsertion x.needs.size a (.dotMember (.param name) "Algorithm" fallback none) ctx env b) x) =
      (shiftExcept (shiftResult ⟨x.needs.size, 1⟩) o₁,
        embed (paramInsertion x.needs.size a (.dotMember (.param name) "Algorithm" fallback none) ctx env b) x₄))
    (hreadU : Unrecorded a x₄)
    (htail : ∀ v, o₁ = .ok v → PlanCallees x₄ ∧
      (∃ cell cnt, x₄.needs[b]? = some cell ∧ cell.state = .completed (.ok (v, cnt))) ∧
      ∃ o₂ x₅,
      (algorithmOfValue v (some args) ctx env).runState x₄ = (o₂, x₅) ∧
      (algorithmOfValue (shiftResult ⟨x.needs.size, 1⟩ v) (some args) ctx env).runState
          (embed (paramInsertion x.needs.size a (.dotMember (.param name) "Algorithm" fallback none) ctx env b) x₄) =
        (shiftExcept (shiftCounted ⟨x.needs.size, 1⟩) o₂,
          embed (paramInsertion x.needs.size a (.dotMember (.param name) "Algorithm" fallback none) ctx env b) x₅) ∧
      Unrecorded a x₅)
    (hprod : ProductionCompletes
      (evalCallCountedExpr (.dotMember (.param name) "Algorithm" fallback none) args ctx env) x) :
    Bridged (paramInsertion x.needs.size a (.dotMember (.param name) "Algorithm" fallback none) ctx env b)
      ((ordinaryCall productionPlanRoute a (groupedShape (.param name) fallback args ctx env) .algorithm).runState x)
      ((reCountValueBoundary <$>
        evalCallCountedExpr (.dotMember (.param name) "Algorithm" fallback none) args ctx env).runState x) := by
  refine algorithm_bridge_grouped_param (fun s => s = x) a name fallback args ctx env x x ca b hsettled ha hsus hroute
    hnone hbound hbk hinv rfl (insertedAt_singleton hread hreadP) ?_ ?_ ?_ ?_ ?_ hprod
  · intro s hs _
    subst hs
    rw [hread]
    exact hreadU
  · intro v hv
    rw [hread] at hv ⊢
    exact (htail v hv).2.1
  · intro v t h
    obtain ⟨ho, hst⟩ := after_singleton hread h
    subst hst
    exact (htail v ho).1
  · intro v
    refine insertedAt_after_singleton hread (fun ho => ?_)
    obtain ⟨-, -, o₂, x₅, hmo, hmp, -⟩ := htail v ho
    exact ⟨o₂, x₅, hmo, hmp⟩
  · intro v s hs _
    obtain ⟨ho, hst⟩ := after_singleton hread hs
    subst hst
    obtain ⟨-, -, o₂, x₅, hmo, -, hu⟩ := htail v ho
    rw [hmo]
    exact hu

/-! ## From an invariant and from per-body obligations to the bridges' premises (§ 6.2, § 6.3)

The bridges take the contract at the plan side's own insertions, from an entry domain and from the
admissible tail entries. This section derives those premises

* from an INVARIANT `P` (`algorithm_bridge_*_of_invariant`): `P` at the comparison state with its
  two facts (`Frame`, `PlanCallees`), `Keeps P` and the contract `InsertedOn P` for the receiver
  read, and — for each receiver VALUE `v` — `P` kept and the contract satisfied by
  `algorithmOfValue v` FROM THE ADMISSIBLE TAIL ENTRIES OF `v` (`After P read v`), never from every
  state of `P` and never for a value the receiver read does not return;
* from the PER-BODY obligations, through the transfer theorem (`algorithm_bridge_*_of_bodies`):
  `BodyInserted` is `BodySimulates` at the insertion's state transformation, the address shift of
  every call (`HeapInsertionCalls.shiftCall`) and of its result (`shiftRet`). It has the shape of
  `PlanConservativity.BodyObliviousOn` — one call domain `Q`, one invariant `P`, the shared
  `BodyKeeps Q P` — so the META-free programme can discharge the plan-RECORD obligations and these
  INSERTION obligations in one pass over the evaluator bodies under one invariant; neither is
  discharged here. The call domain is asked to hold only the calls the production side actually
  makes from `P` (`AlgorithmCalls`): the identity probe; the VALUE read the probe's REACHED answer
  selects; and `algorithmOfValue v` for the receiver read's REACHED results `v`. -/

open KatLang.PlanConservativity (keeps_production)
open KatLang.FiniteLoop (nested_run nest_ne_fuel)

/-- **The per-body insertion obligation.** For every insertion of `count` cells at `base` with plan
    cell `plan`: every evaluator body, run on the SHIFTED call from the plan-side state, simulates
    its run on the call from the production-side state — result shifted, final state under the
    same insertion — whenever its recursive answer does and keeps `P`. -/
def BodyInserted (Q : EvalCall → Prop) (P : EvalState → Prop) (base count plan : Nat) : Prop :=
  ∀ ι : Insertion, ι.base = base → ι.cells.length = count → ι.plan = plan →
    BodySimulates Q P (embed ι) (shiftCall ι.site) (fun c o₁ o₂ => o₂ = Except.map (shiftRet ι.site c) o₁)

/-- **The transfer, at the insertion.** Under the per-body obligations, every production operation
    of the domain satisfies the contract against its shifted call. -/
theorem inserted_production (Q : EvalCall → Prop) (P : EvalState → Prop) (base count plan : Nat)
    (hkeep : BodyKeeps Q P) (hbody : BodyInserted Q P base count plan) (c : EvalCall) (hq : Q c)
    (ι : Insertion) (hb : ι.base = base) (hc : ι.cells.length = count) (hp : ι.plan = plan) :
    Simulates P (embed ι) (fun o₁ o₂ => o₂ = Except.map (shiftRet ι.site c) o₁)
      (evalUnbounded (shiftCall ι.site c)) (evalUnbounded c) :=
  simulates_production Q P (embed ι) (shiftCall ι.site)
    (fun c o₁ o₂ => o₂ = Except.map (shiftRet ι.site c) o₁) hkeep (hbody ι hb hc hp) c hq

theorem shiftExcept_eq_map {α : Type} (f : α → α) (o : Except Error α) : shiftExcept f o = Except.map f o := by
  cases o <;> rfl

theorem site_of (ι : Insertion) {base count : Nat} (hb : ι.base = base) (hc : ι.cells.length = count) :
    ι.site = ⟨base, count⟩ := by
  unfold Insertion.site
  rw [hb, hc]

/-- The contract composes along `>>=`: the plan side's continuation runs on the shifted value. The
    continuation is asked ONLY from the head's reachable results (`After P mo x`), not from every
    state of `P` and not for a value the head never returns. -/
theorem InsertedOn.bindAfter {α β : Type} {P : EvalState → Prop} {base count plan : Nat}
    {ρα : Site → α → α} {ρβ : Site → β → β} {mp mo : EvalM α} {fp fo : α → EvalM β}
    (hm : InsertedOn P base count plan ρα mp mo)
    (hf : ∀ x, InsertedOn (After P mo x) base count plan ρβ (fp (ρα ⟨base, count⟩ x)) (fo x)) :
    InsertedOn P base count plan ρβ (mp >>= fp) (mo >>= fo) := by
  intro ι s hb hc hp hP
  obtain ⟨hiff, hrun⟩ := hm ι s hb hc hp hP
  have hsite := site_of ι hb hc
  rw [bind_run, bind_run]
  by_cases hinc : (mo.runState s).1 = .error .fuelExhausted
  · have hincp := hiff.2 hinc
    rcases hr : mo.runState s with ⟨o, t⟩
    rcases hrp : mp.runState (embed ι s) with ⟨op, tp⟩
    rw [hr] at hinc
    rw [hrp] at hincp
    simp only at hinc hincp
    subst hinc hincp
    exact ⟨⟨fun _ => rfl, fun _ => rfl⟩, fun hne => absurd rfl hne⟩
  · rw [hrun hinc]
    rcases hr : mo.runState s with ⟨o, t⟩
    rw [hr] at hinc
    cases o with
    | error e =>
      refine ⟨⟨fun h => ?_, fun h => ?_⟩, fun _ => rfl⟩
      · exact h
      · exact h
    | ok x =>
      have := hf x ι t hb hc hp ⟨s, hP, hr⟩
      rw [← hsite] at this
      exact this

/-- The contract composes along `>>=` when the continuation satisfies it from every state of `P`
    (the special case of `InsertedOn.bindAfter` for a head that keeps `P`). -/
theorem InsertedOn.bind {α β : Type} {P : EvalState → Prop} {base count plan : Nat}
    {ρα : Site → α → α} {ρβ : Site → β → β} {mp mo : EvalM α} {fp fo : α → EvalM β}
    (hm : InsertedOn P base count plan ρα mp mo) (hk : Keeps P mo)
    (hf : ∀ x, InsertedOn P base count plan ρβ (fp (ρα ⟨base, count⟩ x)) (fo x)) :
    InsertedOn P base count plan ρβ (mp >>= fp) (mo >>= fo) :=
  InsertedOn.bindAfter hm (fun x => (hf x).mono (fun _ h => h.keeps hk))

/-- The contract passes under `withNestedMissingOutput`: it rewrites the error, never the state. -/
theorem InsertedOn.nested {α : Type} {P : EvalState → Prop} {base count plan : Nat} {ρ : Site → α → α}
    {mp mo : EvalM α} (hm : InsertedOn P base count plan ρ mp mo) :
    InsertedOn P base count plan ρ (withNestedMissingOutput mp) (withNestedMissingOutput mo) := by
  intro ι s hb hc hp hP
  obtain ⟨hiff, hrun⟩ := hm ι s hb hc hp hP
  rw [nested_run, nested_run]
  by_cases hinc : (mo.runState s).1 = .error .fuelExhausted
  · have hincp := hiff.2 hinc
    rcases hr : mo.runState s with ⟨o, t⟩
    rcases hrp : mp.runState (embed ι s) with ⟨op, tp⟩
    rw [hr] at hinc
    rw [hrp] at hincp
    simp only at hinc hincp
    subst hinc hincp
    exact ⟨⟨fun _ => rfl, fun _ => rfl⟩, fun hne => absurd rfl hne⟩
  · rw [hrun hinc]
    rcases hr : mo.runState s with ⟨o, t⟩
    rw [hr] at hinc
    cases o with
    | ok a =>
      refine ⟨⟨fun h => ?_, fun h => ?_⟩, fun _ => rfl⟩
      · exact absurd h (by simp [shiftExcept])
      · exact absurd h (by simp)
    | error e =>
      have hne : e ≠ .fuelExhausted := fun h => hinc (by rw [h])
      have hn := nest_ne_fuel e hne
      refine ⟨⟨fun h => ?_, fun h => ?_⟩, fun _ => rfl⟩
      · injection h with h; exact absurd h hn
      · injection h with h; exact absurd h hn

theorem keeps_nested {α : Type} {P : EvalState → Prop} {m : EvalM α} (h : Keeps P m) :
    Keeps P (withNestedMissingOutput m) := by
  intro s hP hne
  rw [nested_run] at hne ⊢
  have hk := h s hP
  rcases hr : m.runState s with ⟨o, t⟩
  rw [hr] at hne hk
  cases o with
  | ok a => exact hk (by nofun)
  | error e =>
    refine hk (fun h => hne ?_)
    injection h with h
    subst h
    rfl

/-- **The operations the `.Algorithm` bridge shares between its two sides, as a call domain** —
    SCOPED to what the production side runs from `P`: the receiver's identity probe; the value read
    `eval` when a REACHED probe answers `none`, the reference read over `g` when a REACHED probe
    answers `some g`; and the intrinsic over each receiver VALUE the receiver read REACHES. Nothing
    is asked of an arbitrary expression, context, algorithm or value. -/
def AlgorithmCalls (Q : EvalCall → Prop) (P : EvalState → Prop) (receiver : Expr) (args : OutputBundle)
    (ctx : EvalCtx) (env : ValEnv) : Prop :=
  Q (.resolveDotReceiver? receiver ctx) ∧
  (∀ t, After P (resolveDotReceiver? receiver ctx) none t → Q (.eval receiver ctx env)) ∧
  (∀ g t, After P (resolveDotReceiver? receiver ctx) (some g) t → Q (.referenceReceiverValue receiver g ctx env)) ∧
  (∀ v t, After P (invocationReceiverValue receiver ctx env) v t → Q (.algorithmOfValue v (some args) ctx env))

section Bodies
variable {Q : EvalCall → Prop} {P : EvalState → Prop} {receiver : Expr} {args : OutputBundle}
  {ctx : EvalCtx} {env : ValEnv}

/-- **The receiver read keeps `P`**, from the per-body keeping obligation. -/
theorem keeps_receiver_read (hkeep : BodyKeeps Q P) (hQ : AlgorithmCalls Q P receiver args ctx env) :
    Keeps P (invocationReceiverValue receiver ctx env) := by
  rw [invocationReceiverValue_eq]
  intro s hP hne
  rw [bind_run] at hne ⊢
  have hk := keeps_production Q P hkeep _ hQ.1 s hP
  rcases hr : (resolveDotReceiver? receiver ctx).runState s with ⟨o, t⟩
  have hr' : (evalUnbounded (.resolveDotReceiver? receiver ctx)).runState s = (o, t) := hr
  rw [hr'] at hk
  rw [hr] at hne
  cases o with
  | error e =>
    dsimp only at hne hk ⊢
    have he : e ≠ Error.fuelExhausted := fun h => hne (by rw [h])
    exact hk (fun h => he (Except.error.inj h))
  | ok alg? =>
    dsimp only at hne hk ⊢
    have hPt : P t := hk (by nofun)
    cases alg? with
    | none => exact keeps_nested (keeps_production Q P hkeep _ (hQ.2.1 t ⟨s, hP, hr⟩)) t hPt hne
    | some g => exact keeps_production Q P hkeep _ (hQ.2.2.1 g t ⟨s, hP, hr⟩) t hPt hne

/-- **The tail keeps `P`**, from each admissible tail entry of its VALUE. -/
theorem keeps_tail (hkeep : BodyKeeps Q P) (hQ : AlgorithmCalls Q P receiver args ctx env) (v : Result) :
    KeepsOn (After P (invocationReceiverValue receiver ctx env) v) P (algorithmOfValue v (some args) ctx env) :=
  fun s hs hne =>
    keeps_production Q P hkeep _ (hQ.2.2.2 v s hs) s (hs.keeps (keeps_receiver_read hkeep hQ)) hne

end Bodies

/-- A production operation against its shifted call (the transfer's conclusion) IS the contract,
    once the shifted call is the plan-side computation. -/
theorem insertedOn_of_simulates {α : Type} {P : EvalState → Prop} {base count plan : Nat} {ρ : Site → α → α}
    {mp mo : EvalM α} (mp' : Site → EvalM α)
    (h : ∀ ι : Insertion, ι.base = base → ι.cells.length = count → ι.plan = plan →
      Simulates P (embed ι) (fun o₁ o₂ => o₂ = Except.map (ρ ι.site) o₁) (mp' ι.site) mo)
    (hmp : mp' ⟨base, count⟩ = mp) : InsertedOn P base count plan ρ mp mo := by
  intro ι s hb hc hp hP
  have hsim := h ι hb hc hp s hP
  rw [site_of ι hb hc, hmp] at hsim
  obtain ⟨hiff, hrun⟩ := hsim
  refine ⟨hiff, fun hne => ?_⟩
  obtain ⟨ho, hs⟩ := hrun hne
  rw [site_of ι hb hc, shiftExcept_eq_map]
  exact Prod.ext ho hs

/-- **The contract for the receiver read**, from the per-body obligations, for a caller context and
    value environment that hold no address at or above the insertion. -/
theorem inserted_receiver_read (Q : EvalCall → Prop) (P : EvalState → Prop) (base count plan : Nat)
    (hkeep : BodyKeeps Q P) (hbody : BodyInserted Q P base count plan)
    (receiver : Expr) (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv)
    (hQ : AlgorithmCalls Q P receiver args ctx env)
    (hctx : shiftCtx ⟨base, count⟩ ctx = ctx) (henv : shiftValEnv ⟨base, count⟩ env = env) :
    InsertedOn P base count plan shiftResult
      (invocationReceiverValue receiver ctx env) (invocationReceiverValue receiver ctx env) := by
  have hkprobe : Keeps P (resolveDotReceiver? receiver ctx) := keeps_production Q P hkeep _ hQ.1
  have hprobe : InsertedOn P base count plan (fun _ (x : Option Algorithm) => x)
      (resolveDotReceiver? receiver ctx) (resolveDotReceiver? receiver ctx) :=
    insertedOn_of_simulates (fun σ => resolveDotReceiver? receiver (shiftCtx σ ctx))
      (fun ι hb hc hp =>
        inserted_production Q P base count plan hkeep hbody (.resolveDotReceiver? receiver ctx) hQ.1 ι hb hc hp)
      (by simp only [hctx])
  rw [invocationReceiverValue_eq]
  refine InsertedOn.bindAfter hprobe (fun alg? => ?_)
  cases alg? with
  | none =>
    intro ι s hb hc hp hs
    have heval : InsertedOn P base count plan shiftResult (eval receiver ctx env) (eval receiver ctx env) :=
      insertedOn_of_simulates (fun σ => eval receiver (shiftCtx σ ctx) (shiftValEnv σ env))
        (fun ι hb hc hp =>
          inserted_production Q P base count plan hkeep hbody (.eval receiver ctx env) (hQ.2.1 s hs) ι hb hc hp)
        (by simp only [hctx, henv])
    exact InsertedOn.nested heval ι s hb hc hp (hs.keeps hkprobe)
  | some targetAlg =>
    intro ι s hb hc hp hs
    have href : InsertedOn P base count plan shiftResult
        (referenceReceiverValue receiver targetAlg ctx env) (referenceReceiverValue receiver targetAlg ctx env) :=
      insertedOn_of_simulates (fun σ => referenceReceiverValue receiver targetAlg (shiftCtx σ ctx) (shiftValEnv σ env))
        (fun ι hb hc hp =>
          inserted_production Q P base count plan hkeep hbody (.referenceReceiverValue receiver targetAlg ctx env)
            (hQ.2.2.1 targetAlg s hs) ι hb hc hp)
        (by simp only [hctx, henv])
    exact href ι s hb hc hp (hs.keeps hkprobe)

/-- **The contract for the tail**, from the per-body obligations: `algorithmOfValue` on the shifted
    receiver VALUE against `algorithmOfValue` on the VALUE — from the admissible tail entries of that
    VALUE, which is where the call domain holds the call. -/
theorem inserted_tail (Q : EvalCall → Prop) (P : EvalState → Prop) (base count plan : Nat)
    (hkeep : BodyKeeps Q P) (hbody : BodyInserted Q P base count plan)
    (receiver : Expr) (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv)
    (hQ : AlgorithmCalls Q P receiver args ctx env)
    (hctx : shiftCtx ⟨base, count⟩ ctx = ctx) (henv : shiftValEnv ⟨base, count⟩ env = env) (v : Result) :
    InsertedOn (After P (invocationReceiverValue receiver ctx env) v) base count plan shiftCounted
      (algorithmOfValue (shiftResult ⟨base, count⟩ v) (some args) ctx env)
      (algorithmOfValue v (some args) ctx env) := by
  intro ι s hb hc hp hs
  have h : InsertedOn P base count plan shiftCounted
      (algorithmOfValue (shiftResult ⟨base, count⟩ v) (some args) ctx env)
      (algorithmOfValue v (some args) ctx env) :=
    insertedOn_of_simulates
      (fun σ => algorithmOfValue (shiftResult σ v) (some args) (shiftCtx σ ctx) (shiftValEnv σ env))
      (fun ι hb hc hp =>
        inserted_production Q P base count plan hkeep hbody (.algorithmOfValue v (some args) ctx env)
          (hQ.2.2.2 v s hs) ι hb hc hp)
      (by simp only [hctx, henv])
  exact h ι s hb hc hp (hs.keeps (keeps_receiver_read hkeep hQ))

/-- The plan cell's captured caller context and value environment hold no address at or above the
    comparison state's heap size: the address invariant bounds them. -/
theorem plan_context_unshifted (x : EvalState) (a count : Nat) (ca : NeedCell) (e : Expr) (ctx : EvalCtx)
    (env : ValEnv) (hinv : Inv x) (ha : x.needs[a]? = some ca) (hsus : ca.suspension = .expression e ctx env) :
    shiftCtx ⟨x.needs.size, count⟩ ctx = ctx ∧ shiftValEnv ⟨x.needs.size, count⟩ env = env := by
  have hv := (hinv.cells a ca ha).susp
  rw [hsus] at hv
  exact ⟨shiftCtx_valid (σ := ⟨x.needs.size, count⟩) rfl hv.1, shiftValEnv_valid (σ := ⟨x.needs.size, count⟩) rfl hv.2⟩

/-! ### From an invariant -/

/-- **THE `.Algorithm` BRIDGE, dot form, from an INVARIANT `P`.** `algorithm_bridge_dot` at the entry
    domain `P`: `P` at the comparison state with its two facts; `Keeps P` and the contract at every
    insertion for the receiver read; and, for each receiver VALUE `v`, `P` kept and the contract
    satisfied by the tail FROM THE ADMISSIBLE TAIL ENTRIES OF `v`. `Frame` at production's final state
    follows from `P` there. -/
theorem algorithm_bridge_dot_of_invariant (P : EvalState → Prop) (a : Nat) (target fallback : Expr)
    (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) (x x' : EvalState) (alg? : Option Algorithm) (ca : NeedCell)
    (hnp : ∀ p, target ≠ .param p)
    (ha : x.needs[a]? = some ca)
    (hsus : ca.suspension = .expression (.dotMember target "Algorithm" fallback (some args)) ctx env)
    (hroute : ca.route = some .algorithm) (hnone : ca.callee = none)
    (hprobe : (resolveDotReceiver? target ctx).runState x = (.ok alg?, x'))
    (hmiss : selectDotEdge ctx target "Algorithm" alg? = .ok (.miss .algorithm))
    (hinv : Inv x) (hP : P x) (hframe : ∀ s, P s → Frame x.needs.size a s)
    (hplans : ∀ s, P s → PlanCallees s)
    (kread : Keeps P (invocationReceiverValue target ctx env))
    (cread : InsertedOn P x.needs.size 2 a shiftResult
      (invocationReceiverValue target ctx env) (invocationReceiverValue target ctx env))
    (ktail : ∀ v, KeepsOn (After P (invocationReceiverValue target ctx env) v) P
      (algorithmOfValue v (some args) ctx env))
    (ctail : ∀ v, InsertedOn (After P (invocationReceiverValue target ctx env) v) x.needs.size 2 a shiftCounted
      (algorithmOfValue (shiftResult ⟨x.needs.size, 2⟩ v) (some args) ctx env)
      (algorithmOfValue v (some args) ctx env))
    (hprod : ProductionCompletes (evalCounted (.dotMember target "Algorithm" fallback (some args)) ctx env) x) :
    Bridged (finalInsertion x a (dotShape target fallback args ctx env) target)
      ((ordinaryCall productionPlanRoute a (dotShape target fallback args ctx env) .algorithm).runState x)
      ((reCountValueBoundary <$> evalCounted (.dotMember target "Algorithm" fallback (some args)) ctx env).runState x) :=
  algorithm_bridge_dot P a target fallback args ctx env x x' alg? ca hnp ha hsus hroute hnone hprobe hmiss hinv hP
    (cread.at _ rfl rfl rfl)
    (fun s hs hne => (hframe _ (kread s hs hne)).2.2)
    (fun _ t h => hplans t (h.keeps kread))
    (fun v => (ctail v).at _ rfl rfl rfl)
    (fun v s hs hne => (hframe _ (ktail v s hs hne)).2.2)
    hprod

/-- **THE `.Algorithm` BRIDGE, grouped form, from an INVARIANT `P`** (`algorithm_bridge_grouped` at the
    entry domain `P`, as `algorithm_bridge_dot_of_invariant`). -/
theorem algorithm_bridge_grouped_of_invariant (P : EvalState → Prop) (a : Nat) (receiver fallback : Expr)
    (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) (s x : EvalState) (ca : NeedCell)
    (hnp : ∀ p, receiver ≠ .param p)
    (hdecided : (withCtx (CtxMsg.call (.dotMember receiver "Algorithm" fallback none))
      (algorithmIntrinsicRoute receiver ctx)).runState s = (.ok true, x))
    (ha : x.needs[a]? = some ca)
    (hsus : ca.suspension = .expression (.call (.dotMember receiver "Algorithm" fallback none) args) ctx env)
    (hroute : ca.route = some .algorithm) (hnone : ca.callee = none)
    (hinv : Inv x) (hP : P x) (hframe : ∀ s, P s → Frame x.needs.size a s)
    (hplans : ∀ s, P s → PlanCallees s)
    (kread : Keeps P (invocationReceiverValue receiver ctx env))
    (cread : InsertedOn P x.needs.size 2 a shiftResult
      (invocationReceiverValue receiver ctx env) (invocationReceiverValue receiver ctx env))
    (ktail : ∀ v, KeepsOn (After P (invocationReceiverValue receiver ctx env) v) P
      (algorithmOfValue v (some args) ctx env))
    (ctail : ∀ v, InsertedOn (After P (invocationReceiverValue receiver ctx env) v) x.needs.size 2 a shiftCounted
      (algorithmOfValue (shiftResult ⟨x.needs.size, 2⟩ v) (some args) ctx env)
      (algorithmOfValue v (some args) ctx env))
    (hprod : ProductionCompletes
      (evalCallCountedExpr (.dotMember receiver "Algorithm" fallback none) args ctx env) s) :
    Bridged (finalInsertion x a (groupedShape receiver fallback args ctx env) receiver)
      ((ordinaryCall productionPlanRoute a (groupedShape receiver fallback args ctx env) .algorithm).runState x)
      ((reCountValueBoundary <$>
        evalCallCountedExpr (.dotMember receiver "Algorithm" fallback none) args ctx env).runState s) :=
  algorithm_bridge_grouped P a receiver fallback args ctx env s x ca hnp hdecided ha hsus hroute hnone hinv hP
    (cread.at _ rfl rfl rfl)
    (fun s hs hne => (hframe _ (kread s hs hne)).2.2)
    (fun _ t h => hplans t (h.keeps kread))
    (fun v => (ctail v).at _ rfl rfl rfl)
    (fun v s hs hne => (hframe _ (ktail v s hs hne)).2.2)
    hprod

/-- **THE `.Algorithm` BRIDGE over a PARAMETER receiver, dot form, from an INVARIANT `P`**
    (`algorithm_bridge_dot_param` at the entry domain `P`; ONE inserted cell). -/
theorem algorithm_bridge_dot_param_of_invariant (P : EvalState → Prop) (a : Nat) (name : Ident) (fallback : Expr)
    (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) (x x' : EvalState) (alg? : Option Algorithm)
    (ca : NeedCell) (b : Nat)
    (ha : x.needs[a]? = some ca)
    (hsus : ca.suspension = .expression (.dotMember (.param name) "Algorithm" fallback (some args)) ctx env)
    (hroute : ca.route = some .algorithm) (hnone : ca.callee = none)
    (hprobe : (resolveDotReceiver? (.param name) ctx).runState x = (.ok alg?, x'))
    (hmiss : selectDotEdge ctx (.param name) "Algorithm" alg? = .ok (.miss .algorithm))
    (hbound : parameterAddressIn x.lexicalActivations name ctx = some b) (hbk : b < x.needs.size)
    (hinv : Inv x) (hP : P x) (hframe : ∀ s, P s → Frame x.needs.size a s)
    (hplans : ∀ s, P s → PlanCallees s)
    (kread : Keeps P (invocationReceiverValue (.param name) ctx env))
    (cread : InsertedOn P x.needs.size 1 a shiftResult
      (invocationReceiverValue (.param name) ctx env) (invocationReceiverValue (.param name) ctx env))
    (hmemo : ∀ v, ((invocationReceiverValue (.param name) ctx env).runState x).1 = .ok v →
      ∃ cell cnt, ((invocationReceiverValue (.param name) ctx env).runState x).2.needs[b]? = some cell ∧
        cell.state = .completed (.ok (v, cnt)))
    (ktail : ∀ v, KeepsOn (After P (invocationReceiverValue (.param name) ctx env) v) P
      (algorithmOfValue v (some args) ctx env))
    (ctail : ∀ v, InsertedOn (After P (invocationReceiverValue (.param name) ctx env) v) x.needs.size 1 a
      shiftCounted
      (algorithmOfValue (shiftResult ⟨x.needs.size, 1⟩ v) (some args) ctx env)
      (algorithmOfValue v (some args) ctx env))
    (hprod : ProductionCompletes
      (evalCounted (.dotMember (.param name) "Algorithm" fallback (some args)) ctx env) x) :
    Bridged (paramInsertion x.needs.size a (.dotMember (.param name) "Algorithm" fallback none) ctx env b)
      ((ordinaryCall productionPlanRoute a (dotShape (.param name) fallback args ctx env) .algorithm).runState x)
      ((reCountValueBoundary <$>
        evalCounted (.dotMember (.param name) "Algorithm" fallback (some args)) ctx env).runState x) :=
  algorithm_bridge_dot_param P a name fallback args ctx env x x' alg? ca b ha hsus hroute hnone hprobe hmiss hbound hbk
    hinv hP
    (cread.at _ rfl rfl rfl)
    (fun s hs hne => (hframe _ (kread s hs hne)).2.2)
    hmemo
    (fun _ t h => hplans t (h.keeps kread))
    (fun v => (ctail v).at _ rfl rfl rfl)
    (fun v s hs hne => (hframe _ (ktail v s hs hne)).2.2)
    hprod

/-- **THE `.Algorithm` BRIDGE over a PARAMETER receiver, grouped form, from an INVARIANT `P`**
    (`algorithm_bridge_grouped_param` at the entry domain `P`; ONE inserted cell). -/
theorem algorithm_bridge_grouped_param_of_invariant (P : EvalState → Prop) (a : Nat) (name : Ident)
    (fallback : Expr) (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) (s x : EvalState) (ca : NeedCell) (b : Nat)
    (hdecided : (withCtx (CtxMsg.call (.dotMember (.param name) "Algorithm" fallback none))
      (algorithmIntrinsicRoute (.param name) ctx)).runState s = (.ok true, x))
    (ha : x.needs[a]? = some ca)
    (hsus : ca.suspension = .expression (.call (.dotMember (.param name) "Algorithm" fallback none) args) ctx env)
    (hroute : ca.route = some .algorithm) (hnone : ca.callee = none)
    (hbound : parameterAddressIn x.lexicalActivations name ctx = some b) (hbk : b < x.needs.size)
    (hinv : Inv x) (hP : P x) (hframe : ∀ s, P s → Frame x.needs.size a s)
    (hplans : ∀ s, P s → PlanCallees s)
    (kread : Keeps P (invocationReceiverValue (.param name) ctx env))
    (cread : InsertedOn P x.needs.size 1 a shiftResult
      (invocationReceiverValue (.param name) ctx env) (invocationReceiverValue (.param name) ctx env))
    (hmemo : ∀ v, ((invocationReceiverValue (.param name) ctx env).runState x).1 = .ok v →
      ∃ cell cnt, ((invocationReceiverValue (.param name) ctx env).runState x).2.needs[b]? = some cell ∧
        cell.state = .completed (.ok (v, cnt)))
    (ktail : ∀ v, KeepsOn (After P (invocationReceiverValue (.param name) ctx env) v) P
      (algorithmOfValue v (some args) ctx env))
    (ctail : ∀ v, InsertedOn (After P (invocationReceiverValue (.param name) ctx env) v) x.needs.size 1 a
      shiftCounted
      (algorithmOfValue (shiftResult ⟨x.needs.size, 1⟩ v) (some args) ctx env)
      (algorithmOfValue v (some args) ctx env))
    (hprod : ProductionCompletes
      (evalCallCountedExpr (.dotMember (.param name) "Algorithm" fallback none) args ctx env) s) :
    Bridged (paramInsertion x.needs.size a (.dotMember (.param name) "Algorithm" fallback none) ctx env b)
      ((ordinaryCall productionPlanRoute a (groupedShape (.param name) fallback args ctx env) .algorithm).runState x)
      ((reCountValueBoundary <$>
        evalCallCountedExpr (.dotMember (.param name) "Algorithm" fallback none) args ctx env).runState s) :=
  algorithm_bridge_grouped_param P a name fallback args ctx env s x ca b hdecided ha hsus hroute hnone hbound hbk
    hinv hP
    (cread.at _ rfl rfl rfl)
    (fun s hs hne => (hframe _ (kread s hs hne)).2.2)
    hmemo
    (fun _ t h => hplans t (h.keeps kread))
    (fun v => (ctail v).at _ rfl rfl rfl)
    (fun v s hs hne => (hframe _ (ktail v s hs hne)).2.2)
    hprod

/-! ### From the per-body obligations -/

/-- **THE `.Algorithm` BRIDGE, dot form, from the PER-BODY obligations.** `algorithm_bridge_dot` with
    its contract and preservation premises discharged through the transfer theorem: what remains is
    the per-body keeping obligation `BodyKeeps Q P`, the per-body insertion obligation
    `BodyInserted Q P`, the call domain holding the calls the production side makes from `P`
    (`AlgorithmCalls`), and `P` at the comparison state with its two facts. The per-body obligations
    are the META-free programme's; they are NOT discharged here. -/
theorem algorithm_bridge_dot_of_bodies (Q : EvalCall → Prop) (P : EvalState → Prop) (a : Nat)
    (target fallback : Expr) (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) (x x' : EvalState)
    (alg? : Option Algorithm) (ca : NeedCell)
    (hkeep : BodyKeeps Q P) (hbody : BodyInserted Q P x.needs.size 2 a)
    (hQ : AlgorithmCalls Q P target args ctx env)
    (hnp : ∀ p, target ≠ .param p)
    (ha : x.needs[a]? = some ca)
    (hsus : ca.suspension = .expression (.dotMember target "Algorithm" fallback (some args)) ctx env)
    (hroute : ca.route = some .algorithm) (hnone : ca.callee = none)
    (hprobe : (resolveDotReceiver? target ctx).runState x = (.ok alg?, x'))
    (hmiss : selectDotEdge ctx target "Algorithm" alg? = .ok (.miss .algorithm))
    (hinv : Inv x) (hP : P x) (hframe : ∀ s, P s → Frame x.needs.size a s)
    (hplans : ∀ s, P s → PlanCallees s)
    (hprod : ProductionCompletes (evalCounted (.dotMember target "Algorithm" fallback (some args)) ctx env) x) :
    Bridged (finalInsertion x a (dotShape target fallback args ctx env) target)
      ((ordinaryCall productionPlanRoute a (dotShape target fallback args ctx env) .algorithm).runState x)
      ((reCountValueBoundary <$> evalCounted (.dotMember target "Algorithm" fallback (some args)) ctx env).runState x) := by
  obtain ⟨hctx, henv⟩ := plan_context_unshifted x a 2 ca _ ctx env hinv ha hsus
  exact algorithm_bridge_dot_of_invariant P a target fallback args ctx env x x' alg? ca hnp ha hsus hroute hnone
    hprobe hmiss hinv hP hframe hplans (keeps_receiver_read hkeep hQ)
    (inserted_receiver_read Q P x.needs.size 2 a hkeep hbody target args ctx env hQ hctx henv)
    (keeps_tail hkeep hQ)
    (inserted_tail Q P x.needs.size 2 a hkeep hbody target args ctx env hQ hctx henv) hprod

/-- **THE `.Algorithm` BRIDGE, grouped form, from the PER-BODY obligations** (`algorithm_bridge_grouped`
    with its contract and preservation premises discharged through the transfer theorem). -/
theorem algorithm_bridge_grouped_of_bodies (Q : EvalCall → Prop) (P : EvalState → Prop) (a : Nat)
    (receiver fallback : Expr) (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) (s x : EvalState)
    (ca : NeedCell)
    (hkeep : BodyKeeps Q P) (hbody : BodyInserted Q P x.needs.size 2 a)
    (hQ : AlgorithmCalls Q P receiver args ctx env)
    (hnp : ∀ p, receiver ≠ .param p)
    (hdecided : (withCtx (CtxMsg.call (.dotMember receiver "Algorithm" fallback none))
      (algorithmIntrinsicRoute receiver ctx)).runState s = (.ok true, x))
    (ha : x.needs[a]? = some ca)
    (hsus : ca.suspension = .expression (.call (.dotMember receiver "Algorithm" fallback none) args) ctx env)
    (hroute : ca.route = some .algorithm) (hnone : ca.callee = none)
    (hinv : Inv x) (hP : P x) (hframe : ∀ s, P s → Frame x.needs.size a s)
    (hplans : ∀ s, P s → PlanCallees s)
    (hprod : ProductionCompletes
      (evalCallCountedExpr (.dotMember receiver "Algorithm" fallback none) args ctx env) s) :
    Bridged (finalInsertion x a (groupedShape receiver fallback args ctx env) receiver)
      ((ordinaryCall productionPlanRoute a (groupedShape receiver fallback args ctx env) .algorithm).runState x)
      ((reCountValueBoundary <$>
        evalCallCountedExpr (.dotMember receiver "Algorithm" fallback none) args ctx env).runState s) := by
  obtain ⟨hctx, henv⟩ := plan_context_unshifted x a 2 ca _ ctx env hinv ha hsus
  exact algorithm_bridge_grouped_of_invariant P a receiver fallback args ctx env s x ca hnp hdecided ha hsus hroute
    hnone hinv hP hframe hplans (keeps_receiver_read hkeep hQ)
    (inserted_receiver_read Q P x.needs.size 2 a hkeep hbody receiver args ctx env hQ hctx henv)
    (keeps_tail hkeep hQ)
    (inserted_tail Q P x.needs.size 2 a hkeep hbody receiver args ctx env hQ hctx henv) hprod

end KatLang.PlanAlgorithmBridge
