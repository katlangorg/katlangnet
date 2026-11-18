import KatLangArityLaws.PlanConservativityAdmissible

open KatLang KatLang.PlanConservativity KatLang.PlanConservativityAdmissible

/-!
# The state-only keeping premise is unsatisfiable (ledger E-18)

`PlanConservativityAdmissible.production_fresh_plan_refFree` takes the per-body premise
`BodyKeepsGiven Q (Active a) StoredRefFree`, and the older instances take
`BodyKeeps Q (ActiveRefFree a)`. Both assume of the recursive answer `rec` only that it keeps a
STATE predicate (`PlanConservativity.Keeps`). An answer may keep every state predicate and still
RETURN a call reference, and a body stores what it is given: the VALUE demand of a cell
(`NeedDemand.step`) writes the outcome into the cell's `state`.

`badRec` is such an answer: it changes no state and answers `evalSuppliedAt` with
`Result.callRef 0`. Given distinct addresses `a` and `d`, start with `a` evaluating and `d` a
suspended expression. The body of `demandNeedRecursive d` stores the returned reference at `d`
and leaves `a` evaluating. The original two-cell example is the instance at 0 and 1:

For every call domain `Q` containing `demandNeedRecursive 1`:

* `bodyKeepsGiven_refuted : ¬ BodyKeepsGiven Q (Active 0) StoredRefFree`;
* `bodyKeeps_activeRefFree_refuted : ¬ BodyKeeps Q (ActiveRefFree 0)`.

The general refutation requires the two addresses to differ. Demanding the active cell itself
returns `demandCycle` with the original state. A contract on returned values can distinguish
`badRec` from a reference-free evaluator answer (ledger E-18).
-/

namespace KatLang.PlanConservativityKeepsGuards

/-- An answer that changes no state and returns a call reference where a supplied expression's
    value is asked for; every other question is incomplete. -/
def badRec : EvalRec := fun c =>
  match c with
  | .evalSuppliedAt _ _ _ _ => (pure (Result.callRef 0, 1) : EvalM CountedResult)
  | _ => EvalM.incomplete

/-- `badRec` keeps EVERY state predicate: it never changes the state. -/
theorem badRec_keeps (P : EvalState → Prop) : ∀ c, Keeps P (badRec c) := by
  intro c s hP hne
  cases c <;> first | exact hP | exact absurd rfl hne

/-- Any domain containing a VALUE demand at an address distinct from the active cell admits the
    counterexample. The result contract of the recursive answer is missing at the store. -/
theorem bodyKeepsGiven_distinctDemand_refuted {Q : EvalCall → Prop} {a d : Nat}
    (hne : a ≠ d) (hq : Q (.demandNeedRecursive d)) :
    ¬ BodyKeepsGiven Q (Active a) StoredRefFree := by
  let activeCell : NeedCell := { suspension := .ready (.atom 0, 1), state := .evaluating }
  let waiting : NeedCell := { suspension := .expression (.num 1) { callStack := [] } [] }
  let s : EvalState := { needs := Array.ofFn (n := max a d + 1) fun i =>
    if i.val = d then waiting else activeCell }
  have ha : s.needs[a]? = some activeCell := by simp [s, show a < max a d + 1 by omega, hne]
  have hd : s.needs[d]? = some waiting := by simp [s, show d < max a d + 1 by omega]
  have free : StoredRefFree s := by
    suffices cells : s.needs.toList.all cellRefFreeB = true by
      simpa [StoredRefFree, storedRefFreeB, s] using cells
    apply List.all_eq_true.mpr
    intro c hc
    obtain ⟨i, rfl⟩ := Array.mem_ofFn.mp (Array.mem_toList_iff.mp hc)
    split <;> rfl
  let outcome : Except Error CountedResult := .ok (.callRef 0, 1)
  let t := CallPlan.withState d (.completed outcome) (CallPlan.withState d .evaluating s)
  have run : (evalStep badRec (.demandNeedRecursive d)).runState s = (outcome, t) :=
    NeedControl.Memo.suspended_retains_state (badRec.evalSuppliedAt d) badRec.planRoute
      badRec.demandNeedRecursive d s (CallPlan.withState d .evaluating s) waiting outcome hd rfl rfl rfl
  have active : Active a t :=
    ⟨activeCell, by simp [t, CallPlan.withState, CallPlan.modify_get, Ne.symm hne, ha], rfl⟩
  have stored : t.needs[d]? = some { waiting with state := .completed outcome } := by
    simp [t, CallPlan.withState, CallPlan.modify_get, hd]
  intro keep
  have claim := keep badRec (fun c _ => badRec_keeps _ c) _ hq s ⟨activeCell, ha, rfl⟩ free
  rw [run] at claim
  have finalFree := claim (by intro h; cases h) active
  have allCells := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp finalFree).1).1
  have ok := List.all_eq_true.mp allCells _ (Array.mem_toList_iff.mpr (Array.mem_of_getElem? stored))
  contradiction

/-- The original witness, with the plan at 0 and the demand at 1. -/
theorem bodyKeepsGiven_refuted (Q : EvalCall → Prop) (hQ : Q (.demandNeedRecursive 1)) :
    ¬ BodyKeepsGiven Q (Active 0) StoredRefFree :=
  bodyKeepsGiven_distinctDemand_refuted (by decide) hQ

/-- **So is the undivided keeping premise** at `ActiveRefFree`. -/
theorem bodyKeeps_activeRefFree_refuted (Q : EvalCall → Prop) (hQ : Q (.demandNeedRecursive 1)) :
    ¬ BodyKeeps Q (ActiveRefFree 0) :=
  fun h => bodyKeepsGiven_refuted Q hQ (bodyKeeps_given_of_bodyKeeps h)

/-- A domain containing only the demand of the active cell satisfies the state-only premise. -/
theorem bodyKeepsGiven_onlyActiveDemand (a : Nat) :
    BodyKeepsGiven (fun c => c = .demandNeedRecursive a) (Active a) StoredRefFree := by
  rintro rec _ _ rfl s ⟨cell, hc, hs⟩ free _ _
  have cycle := NeedControl.Production.evaluating_cycle (rec.evalSuppliedAt a) rec.planRoute
    rec.demandNeedRecursive a s cell hc hs
  change StoredRefFree ((NeedDemand.step _ _ _ a).runState s).2
  rw [cycle]
  exact free

/-! ## Axiom audit -/

/-- info: 'KatLang.PlanConservativityKeepsGuards.bodyKeepsGiven_refuted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KatLang.PlanConservativityKeepsGuards.bodyKeepsGiven_refuted

/-- info: 'KatLang.PlanConservativityKeepsGuards.bodyKeeps_activeRefFree_refuted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KatLang.PlanConservativityKeepsGuards.bodyKeeps_activeRefFree_refuted

/-- info: 'KatLang.PlanConservativityKeepsGuards.bodyKeepsGiven_distinctDemand_refuted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KatLang.PlanConservativityKeepsGuards.bodyKeepsGiven_distinctDemand_refuted

/-- info: 'KatLang.PlanConservativityKeepsGuards.bodyKeepsGiven_onlyActiveDemand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KatLang.PlanConservativityKeepsGuards.bodyKeepsGiven_onlyActiveDemand

end KatLang.PlanConservativityKeepsGuards
