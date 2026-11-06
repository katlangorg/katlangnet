import Lean
import KatLangArityLaws.WhileRoundProduction
import KatLangArityLaws.MetaLoop
import KatLangArityLaws.CallReference
import KatLangArityLaws.NeedControl
import KatLangArityLaws.EvaluatorMemoLinks

open KatLang KatLang.EvaluatorCore KatLang.WhileRoundProduction
open Lean.Order

/-!
# FG-L1: finite-loop correspondence (November 2026)

The loop laws before this module stopped at the setup helpers (`MetaLoop.lean`) and at one round's
row control (`WhileRoundProduction.lean`). This module connects the production `repeat` and
`while` to finite composition, through their real driver, their real builtin arm and their real
call boundary. It changes no definition of `KatLang.lean`.

## Three objects, kept apart

* The STATE is an ordered list of need-cell addresses (`RepeatTrace`, `WhileTrace` index it).
* A step's ROW SUPPLY is an ordered list of `Result`s (`runNeedStepSlots`, `runNeedWhileRound`).
* The COUNTED VALUE of a finished loop is `loopResultCounted` of its materialized final slots; its
  public count is `Result.valueCount` of that value, never the slot count.

## Obligation map

| Production entry | Existing theorem | Gap closed here | Result, domain |
| --- | --- | --- | --- |
| `applyBuiltinCounted` (`.repeatBuiltin`, `.whileBuiltin`) | `metaLoopCapture_run`, `repeat_setup_order` over abstract capabilities | The arm IS the setup at the real channels: `repeat_arm`, `while_arm` (definitional), `repeat_completes_iff`, `while_completes_iff`, `repeat_setup_stages`, `while_setup_stages` | All cell-backed arguments of a captured plan; failures `repeat_capture_failure`, `repeat_count_failure`, `repeat_negative_count` |
| `repeatLoop` (local to the arm) | none | Equations and composition `repeatDriver_zero/succ/add`; finite derivation `repeat_trace_iff` | Every `n`, every step; each round an atomic production subcall |
| `EvalBody.whileLoop` | `production_unfolds` only | Finite derivation with both directions `while_trace_iff` | Every completed run; the round an atomic production subcall |
| Final boundary (LOOP-07) | `zero_state_result` | `Finished`, `finish_iff`, `repeat_after_setup_iff`, `while_after_setup_iff` | Every completed run |
| One step against an ordinary call | none | `reader_agreement`, `user_step_agreement`, `family_step_agreement`, `count_one_user`, `count_one_family`, `repeat_builtin_count_one` | `UserStep` + `UserRowsBounded`, or `FamilyRowsBounded` |
| Whole builtin | none | `repeat_builtin_iff`, `while_builtin_iff` | From a completed `RepeatSetup` / `WhileSetup` |
| Effects | `evalUnbounded_disciplined`, `evalUnbounded_linkDisc`, `cache_entries_survive` | `repeat_trace_retained`, `while_trace_retained`, `projection_reused` | Every finite run, ordinary errors included |

## Completion transfer without `FuelReached` for the binder

`production_unfolds` runs one way. `production_eq_of_finite` is its converse for a `Finite` body,
and it is what the arms and the drivers use: their bodies call the step as ONE atomic production
subcall. The loop signatures' binder uses neither channel (`repeat_binder_channel_free`).

The comparison of a loop step with an ordinary call must see INSIDE both, and `Finite` is not
proved for an arbitrary binder. It is not needed: `CompletedAt B s r` says `B` reaches `r` over
some fuel iterate, `completedAt_step` identifies a completed operation with its completed body over
the fuel chain, and `completedAt_bind_*` decompose and recompose it. The two operations run the
SAME activation at the SAME fuel, so a completed binder or dispatcher on one side is a
completed one on the other (`shared_activation_forward`, `shared_activation_backward`); what
differs is the reader, whose bodies ARE `Finite` (`reader_agreement`).

## The observation relation, and why the direct equality is narrow

`StepAgreement wrap L O`: the loop outcome `L` and the ordinary outcome `O` complete together; a
success gives `O = (ordinaryValue ys, t)` over the SAME state `t`; an error gives the same error,
nested on the ordinary side, in the same state. Both executions perform the same operations, so
the state relation is equality. The loop then appends one Ready cell per slot and completes each
(`pushReady`, `pushCompleted`, `oneRoundOutcome`): every other `EvalState` field is unchanged and
the appended cells are stated exactly, references inside `Result`s included.

The unrestricted law `Step(args).repeat(1) = Step(args)` is FALSE as a theorem, for these reasons:

* `loopStateResult` normalizes and ordinary output does not. `noncanonical_counterexample`;
  `loop_value_of_canonical` is the exact equality, on canonical slots.
* The row rule `OutputRows.items` splits a non-spread count of two or more; the ordinary reader keeps
  one slot. `RowBoundary` and `BoundedRows` state the run's own counts (guard `hostTwoCell`).
* An ordinary call checks for missing output before its binding context, and reads a value view's
  cell. `UserStep` requires written output, and no value view (`noView_of_params`,
  `noView_of_rows`). A builtin clause body is outside
  `ActivationDomain`.
* A zero-supply call of a property binding publishes (CACHE-PUB-1); a loop does not. The domain is
  `evalNeedUserSupply`, reached from `evalSuppliedCallCounted` on a non-empty supply
  (`ordinary_user_of_nonempty`).
* Row and binder failures nest at the ordinary reader; the loop's nest once at its arm. At the whole
  builtin the user error is then IDENTICAL (`repeat_builtin_count_one`). A family keeps its step frame
  around the error (`wrap`).

General iteration is NOT nesting of a one-argument value call: two rows are two cells, one grouped
row one cell, though both finish as one value.

## What stays open

* A round stays an ATOMIC production subcall in `RepeatTrace` and `WhileTrace`. Its expansion is
  `runNeedWhileRound_*` (`WhileRoundProduction.lean`), which keeps its completion premise.
  `FuelReached` for an arbitrary binder is not proved; nothing here needs it.
* Builtin and alias steps stay on the generic driver. `builtin_step_run` and `alias_step_run` give
  their dispatch; the only ordinary-call facts are `ordinary_builtin_is_step_application` and
  the reduction of an alias to its target's step.
* `UserRowsBounded` is a premise about the run. It is discharged for numeric literal rows
  (`FiniteLoopCorrespondenceGuards.lean`); that every row of a surface program satisfies it is not
  proved. Canonical slots are likewise a premise of the value equality.
* Termination: a finite count does not make a step terminate, and nothing here bounds fuel by
  it. Fuel exhaustion is the incomplete outcome, excluded from every trace; a state reached by
  it is never compared with a completed error's.
* The parser/elaborator prefix (the entries are `applyBuiltinCounted` and the operations named
  above, not a public run); C# planning, async, cancellation, budgets, Decimal128; and any
  cross-language count equivalence. Lean's count is an `Int`; C# comparison stays finite evidence.
* `projection_reused` is about a COMPLETED cell projection. Lean re-enters the capability each round
  and C# may normalize an alias target once; no context independence of alias resolution is claimed.
-/

namespace KatLang.FiniteLoop

/-! ## 1. Completed runs over the fuel chain

The relational form of a completed run: compositional in both directions for monotone
computations, and needing no finite-use proof of the prefix it passes through. -/

/-- `B` completes from `s` with `r` over some fuel iterate. -/
def CompletedAt {α : Type} (B : EvalRec → EvalM α) (s : EvalState)
    (r : Except Error α × EvalState) : Prop :=
  r.1 ≠ .error .fuelExhausted ∧ ∃ k, (B (evalFuel k)).runState s = r

theorem CompletedAt.production {α : Type} {B : EvalRec → EvalM α} {s : EvalState}
    {r : Except Error α × EvalState} (hB : monotone B) (h : CompletedAt B s r) :
    (B evalUnbounded).runState s = r := by
  obtain ⟨hr, k, hk⟩ := h
  rcases hB _ _ (evalFuel_approx_production k) s with hi | he
  · exfalso; unfold EvalM.IsIncompleteAt at hi; rw [hk] at hi; rw [hi] at hr; exact hr rfl
  · rw [← he]; exact hk

theorem CompletedAt.eventually {α : Type} {B : EvalRec → EvalM α} {s : EvalState}
    {r : Except Error α × EvalState} (hB : monotone B) (h : CompletedAt B s r) :
    ∃ k, ∀ K, k ≤ K → (B (evalFuel K)).runState s = r := by
  obtain ⟨hr, k, hk⟩ := h
  refine ⟨k, fun K hK => ?_⟩
  rw [stable_of_mono B hB hK s (by rw [hk]; exact hr), hk]

theorem completedAt_call (c : EvalCall) (s : EvalState) (r : Except Error c.Ret × EvalState) :
    CompletedAt (fun rec => rec c) s r ↔
      ((evalUnbounded c).runState s = r ∧ r.1 ≠ .error .fuelExhausted) := by
  constructor
  · rintro ⟨hr, k, hk⟩
    exact ⟨((production_completes_iff c s r).2
      ⟨k, hk, (evalFuel_completes_iff k c s).2 (by rw [hk]; exact hr)⟩).1, hr⟩
  · rintro ⟨h, hr⟩
    obtain ⟨m, hm, _⟩ := (production_completes_iff c s r).1
      ⟨h, by unfold ProductionCompletes; rw [h]; exact hr⟩
    exact ⟨hr, m, hm⟩

theorem completedAt_const {α : Type} (m : EvalM α) (s : EvalState) (r : Except Error α × EvalState) :
    CompletedAt (fun _ => m) s r ↔ (m.runState s = r ∧ r.1 ≠ .error .fuelExhausted) :=
  ⟨fun ⟨hr, _, hk⟩ => ⟨hk, hr⟩, fun ⟨h, hr⟩ => ⟨hr, 0, h⟩⟩

theorem body_of_normalized {α : Type} (m : EvalM α) (s : EvalState) (r : Except Error α × EvalState)
    (hr : r.1 ≠ .error .fuelExhausted) (h : m.normalizeIncomplete.runState s = r) :
    m.runState s = r := by
  by_cases hn : (m.runState s).1 = .error .fuelExhausted
  · exfalso
    dsimp only [EvalM.normalizeIncomplete] at h
    rcases hrun : m.runState s with ⟨o, t⟩
    rw [hrun] at hn h
    cases hn
    subst h
    exact hr rfl
  · rw [← h, normalize_of_complete _ s hn]

/-- **Completion of one evaluator operation IS completion of its body over the fuel chain**, with
    the same outcome and state. Unlike `production_eq_of_finite` it needs no `Finite` body. -/
theorem completedAt_step (c : EvalCall) (s : EvalState) (r : Except Error c.Ret × EvalState) :
    CompletedAt (fun rec => evalStep rec c) s r ↔
      ((evalUnbounded c).runState s = r ∧ r.1 ≠ .error .fuelExhausted) := by
  rw [← completedAt_call]
  constructor
  · rintro ⟨hr, k, hk⟩
    refine ⟨hr, k + 1, ?_⟩
    show (evalFuel (k + 1) c).runState s = r
    rw [evalFuel_succ, normalize_of_complete _ s (by rw [show _ = r from hk]; exact hr)]
    exact hk
  · rintro ⟨hr, m, hm⟩
    cases m with
    | zero => subst hm; exact absurd rfl hr
    | succ k =>
      change (evalFuel (k + 1) c).runState s = r at hm
      rw [evalFuel_succ] at hm
      exact ⟨hr, k, body_of_normalized _ s r hr hm⟩

theorem error_ne_fuel {α β : Type} {e : Error} (h : (Except.error e : Except Error α) ≠ .error .fuelExhausted) :
    (Except.error e : Except Error β) ≠ .error .fuelExhausted :=
  fun h' => h (by injection h' with h''; rw [h''])

theorem completedAt_bind_ok {α β : Type} {B : EvalRec → EvalM α} {K : EvalRec → α → EvalM β}
    {s t : EvalState} {a : α} {r : Except Error β × EvalState}
    (hB : monotone B) (hK : monotone (fun rec => K rec a))
    (h₁ : CompletedAt B s (.ok a, t)) (h₂ : CompletedAt (fun rec => K rec a) t r) :
    CompletedAt (fun rec => B rec >>= K rec) s r := by
  obtain ⟨k₁, hk₁⟩ := h₁.eventually hB
  obtain ⟨k₂, hk₂⟩ := h₂.eventually hK
  refine ⟨h₂.1, max k₁ k₂, ?_⟩
  rw [EvalM.bind_runState, hk₁ _ (Nat.le_max_left _ _)]
  exact hk₂ _ (Nat.le_max_right _ _)

theorem completedAt_bind_error {α β : Type} {B : EvalRec → EvalM α} {K : EvalRec → α → EvalM β}
    {s t : EvalState} {e : Error} (h : CompletedAt B s (.error e, t)) :
    CompletedAt (fun rec => B rec >>= K rec) s (.error e, t) := by
  obtain ⟨hr, k, hk⟩ := h
  exact ⟨error_ne_fuel hr, k, by rw [EvalM.bind_runState, hk]⟩

theorem completedAt_bind_inv {α β : Type} {B : EvalRec → EvalM α} {K : EvalRec → α → EvalM β}
    {s : EvalState} {r : Except Error β × EvalState}
    (h : CompletedAt (fun rec => B rec >>= K rec) s r) :
    (∃ a t, CompletedAt B s (.ok a, t) ∧ CompletedAt (fun rec => K rec a) t r) ∨
    (∃ e t, r = (.error e, t) ∧ CompletedAt B s (.error e, t)) := by
  obtain ⟨hr, k, hk⟩ := h
  rw [EvalM.bind_runState] at hk
  rcases hrun : (B (evalFuel k)).runState s with ⟨o, t⟩
  rw [hrun] at hk
  cases o with
  | ok a => exact .inl ⟨a, t, ⟨nofun, k, hrun⟩, ⟨hr, k, hk⟩⟩
  | error e =>
    simp only at hk
    subst hk
    exact .inr ⟨e, t, rfl, ⟨error_ne_fuel hr, k, hrun⟩⟩

/-! ## 2. The two readings of one activated body

`evalAlgOutputSlots` (the loop) and `evalAlgOutputCounted` (the ordinary call) both enter the body
once and run `evalCounted` on every row. They differ in the row rule and in nesting. -/

theorem nest_fuel : Error.nestMissingOutput .fuelExhausted = .fuelExhausted := rfl

theorem nest_ne_fuel (e : Error) (h : e ≠ .fuelExhausted) : e.nestMissingOutput ≠ .fuelExhausted := by
  cases e <;> first | exact absurd rfl h | (simp [Error.nestMissingOutput])

theorem nested_run {α : Type} (m : EvalM α) (s : EvalState) :
    (withNestedMissingOutput m).runState s =
      (match m.runState s with
       | (.ok a, t) => (.ok a, t)
       | (.error e, t) => (.error e.nestMissingOutput, t)) := by
  unfold withNestedMissingOutput
  rw [EvalM.bind_runState]
  rcases h : m.runState s with ⟨o, t⟩
  cases o with
  | ok a => rw [evalAttempt_runState_of_complete m s t _ h rfl]; rfl
  | error e =>
    by_cases he : e = .fuelExhausted
    · subst he; rw [evalAttempt_runState_of_incomplete m s t h]; rfl
    · have hc : (Except.error e : Except Error α).isIncomplete = false := by
        cases e <;> first | exact absurd rfl he | rfl
      rw [evalAttempt_runState_of_complete m s t _ h hc]; rfl

/-- A row a loop state and an ordinary output read alike: a spread, or a value-boundary count. -/
def RowBoundary (e : Expr) : CountedResult → Prop :=
  fun out => (∃ x, e = .sequenceSpread x) ∨ out.snd ≤ 1

/-- Every row of this run, from this state, satisfies `RowBoundary`. -/
def BoundedRows (ctx : EvalCtx) (env : ValEnv) : List Expr → EvalState → Prop
  | [], _ => True
  | e :: rest, s =>
    match (evalCounted e ctx env).runState s with
    | (.ok out, t) => RowBoundary e out ∧ BoundedRows ctx env rest t
    | _ => True

abbrev rowsCollect (ctx : EvalCtx) (env : ValEnv) (rows : List Expr) (acc : List Result) (n : Nat) :=
  EvalBody.evalOutputRowsPreparedCore.collect evalUnbounded ctx env rows acc n

theorem pure_runState {α : Type} (a : α) (s : EvalState) :
    (pure a : EvalM α).runState s = (.ok a, s) := rfl

theorem bind_pure_eq {α : Type} (m : EvalM α) : m >>= pure = m :=
  EvalM.ext fun s => by
    rw [EvalM.bind_runState]
    rcases m.runState s with ⟨_ | _, _⟩ <;> rfl

theorem items_plain (e : Expr) (out : CountedResult) (hsp : ¬ ∃ x, e = .sequenceSpread x)
    (hc : out.snd ≤ 1) : OutputRows.items e out = [out.fst] := by
  rcases out with ⟨v, n⟩
  have hi : OutputRows.items e (v, n) = if n = 0 then [v] else countedTopLevelValues (v, n) := by
    cases e <;> first | exact absurd ⟨_, rfl⟩ hsp | rfl
  rw [hi]
  rcases n with _ | _ | n
  · rfl
  · rfl
  · exact absurd hc (by simp)

theorem collect_cons_plain (ctx : EvalCtx) (env : ValEnv) (e : Expr) (rest : List Expr)
    (acc : List Result) (n : Nat) (hsp : ¬ ∃ x, e = .sequenceSpread x) :
    rowsCollect ctx env (e :: rest) acc n =
      (withNestedMissingOutput (evalCounted e ctx env) >>= fun out =>
        rowsCollect ctx env rest (out.fst :: acc) (n + if out.snd = 0 then 1 else out.snd)) := by
  cases e <;> first | exact absurd ⟨_, rfl⟩ hsp | rfl

theorem collect_cons_spread (ctx : EvalCtx) (env : ValEnv) (x : Expr) (rest : List Expr)
    (acc : List Result) (n : Nat) :
    rowsCollect ctx env (.sequenceSpread x :: rest) acc n =
      (withNestedMissingOutput (evalCounted (.sequenceSpread x) ctx env) >>= fun out =>
        rowsCollect ctx env rest ((countedTopLevelValues out).reverse ++ acc) (n + out.snd)) := rfl

theorem collect_rel (ctx : EvalCtx) (env : ValEnv) (rows : List Expr) (acc : List Result) (n : Nat)
    (s : EvalState) (h : BoundedRows ctx env rows s) :
    match (OutputRows.formLeftToRight (formOutputRow ctx env) rows).runState s with
    | (.ok ys, t) => ∃ m, (rowsCollect ctx env rows acc n).runState s =
        (.ok { counted := (combineOutputSlots (acc.reverse ++ ys), m), outputSlots := acc.reverse ++ ys }, t)
    | (.error e, t) => (rowsCollect ctx env rows acc n).runState s = (.error e.nestMissingOutput, t) := by
  induction rows generalizing acc n s with
  | nil => exact ⟨n, by rw [List.append_nil]; rfl⟩
  | cons e rest ih =>
    simp only [BoundedRows] at h
    simp only [OutputRows.formLeftToRight, EvalM.bind_runState, formOutputRow_run]
    by_cases hsp : ∃ x, e = .sequenceSpread x
    · obtain ⟨x, rfl⟩ := hsp
      rw [collect_cons_spread, EvalM.bind_runState, nested_run]
      rcases hrun : (evalCounted (.sequenceSpread x) ctx env).runState s with ⟨o, s₁⟩
      rw [hrun] at h
      cases o with
      | error err => rfl
      | ok out =>
        have hi := ih ((countedTopLevelValues out).reverse ++ acc) (n + out.snd) s₁ h.2
        have hit : OutputRows.items (.sequenceSpread x) out = countedTopLevelValues out := rfl
        dsimp only
        rw [hit]
        rcases hr : (OutputRows.formLeftToRight (formOutputRow ctx env) rest).runState s₁ with ⟨o', t⟩
        rw [hr] at hi
        cases o' with
        | error err => exact hi
        | ok ys =>
          obtain ⟨m, hm⟩ := hi
          refine ⟨m, ?_⟩
          simp only [hm, List.reverse_append, List.reverse_reverse, List.append_assoc]
    · rw [collect_cons_plain ctx env e rest acc n hsp, EvalM.bind_runState, nested_run]
      rcases hrun : (evalCounted e ctx env).runState s with ⟨o, s₁⟩
      rw [hrun] at h
      cases o with
      | error err => rfl
      | ok out =>
        have hc : out.snd ≤ 1 := h.1.resolve_left hsp
        have hi := ih (out.fst :: acc) (n + if out.snd = 0 then 1 else out.snd) s₁ h.2
        dsimp only
        rw [items_plain e out hsp hc]
        rcases hr : (OutputRows.formLeftToRight (formOutputRow ctx env) rest).runState s₁ with ⟨o', t⟩
        rw [hr] at hi
        cases o' with
        | error err => exact hi
        | ok ys =>
          obtain ⟨m, hm⟩ := hi
          refine ⟨m, ?_⟩
          simp only [hm, List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append]

theorem finite_evalAttempt {α : Type} {B : EvalRec → EvalM α} (hB : Finite B) :
    Finite (fun rec => evalAttempt (B rec)) := by
  refine ⟨monotone_evalAttempt B hB.1, ?_⟩
  intro s hc
  have run_eq : ∀ m : EvalM α, (evalAttempt m).runState s =
      (let (result, nextState) := m.runState s
       if result.isIncomplete then (.error .fuelExhausted, nextState) else (.ok result, nextState)) := fun _ => rfl
  have hc' : ProductionCompletes (B evalUnbounded) s := by
    unfold ProductionCompletes at hc ⊢
    rw [run_eq] at hc
    intro hf
    rcases hrun : (B evalUnbounded).runState s with ⟨o, t⟩
    rw [hrun] at hf hc
    cases hf
    exact hc rfl
  obtain ⟨m, hm⟩ := hB.2 s hc'
  exact ⟨m, by rw [run_eq, run_eq, hm]⟩

theorem finite_nested {α : Type} {B : EvalRec → EvalM α} (hB : Finite B) :
    Finite (fun rec => withNestedMissingOutput (B rec)) := by
  unfold withNestedMissingOutput
  refine finite_bind (finite_evalAttempt hB) (fun o => ?_)
  cases o <;> exact finite_const _

theorem finite_collect (ctx : EvalCtx) (env : ValEnv) (rows : List Expr) :
    ∀ (acc : List Result) (n : Nat),
      Finite (fun rec => EvalBody.evalOutputRowsPreparedCore.collect rec ctx env rows acc n) := by
  induction rows with
  | nil => intro acc n; exact finite_const _
  | cons e rest ih =>
    intro acc n
    have hrow := finite_nested (finite_call (.evalCounted e ctx env))
    have : (fun rec => EvalBody.evalOutputRowsPreparedCore.collect rec ctx env (e :: rest) acc n) =
        fun rec => (withNestedMissingOutput (rec (.evalCounted e ctx env)) >>= fun out =>
          match e with
          | .sequenceSpread _ => EvalBody.evalOutputRowsPreparedCore.collect rec ctx env rest ((countedTopLevelValues out).reverse ++ acc) (n + out.snd)
          | _ => EvalBody.evalOutputRowsPreparedCore.collect rec ctx env rest (out.fst :: acc) (n + if out.snd = 0 then 1 else out.snd)) := rfl
    rw [this]
    refine finite_bind hrow (fun out => ?_)
    cases e <;> exact ih _ _

theorem prepared_body (rec : EvalRec) (a : Algorithm) (ha : NotBuiltin a) (ctx : EvalCtx) (env : ValEnv) :
    EvalBody.evalAlgOutputPreparedCore rec a ctx env =
      (ActivatedBody.check a >>= fun _ => enterAlgorithmBody a ctx env >>= fun pushed =>
        rec.evalOutputRowsPreparedCore (Algorithm.output a) pushed env) := by
  have herr : ∀ {β : Type} (e : Error) (k : Unit → EvalM β), (.error e : EvalM Unit) >>= k = .error e :=
    fun e k => EvalM.ext fun s => by rw [EvalM.bind_runState]; rfl
  have hpure : ∀ {β : Type} (k : Unit → EvalM β), (pure () : EvalM Unit) >>= k = k () :=
    fun k => EvalM.ext fun s => by rw [EvalM.bind_runState]; rfl
  unfold EvalBody.evalAlgOutputPreparedCore ActivatedBody.check
  cases a with
  | builtin b => exact absurd rfl (ha b)
  | _ =>
    dsimp only
    cases Algorithm.findDuplicatePropName _ with
    | some n => dsimp only; rw [herr]
    | none =>
      dsimp only
      cases conditionalValueAccessError? "conditional" _ with
      | some err => dsimp only; simp only [herr]
      | none =>
        dsimp only
        repeat' split
        all_goals first | rfl | simp only [herr, hpure]

theorem prepared_entered_run (rec : EvalRec) (a : Algorithm) (ha : NotBuiltin a) (hp : Passes a)
    (ctx : EvalCtx) (env : ValEnv) (s : EvalState) :
    (EvalBody.evalAlgOutputPreparedCore rec a ctx env).runState s =
      (rec.evalOutputRowsPreparedCore a.output (enteredCtx a ctx s) env).runState (enteredState a ctx env s) := by
  rw [prepared_body rec a ha, EvalM.bind_runState, hp s]
  simp only
  rw [EvalM.bind_runState, enter_run]

/-- The rows core at production is the ordinary output fold over production. -/
theorem rowsCore_completes_iff (rows : List Expr) (ctx : EvalCtx) (env : ValEnv) (s : EvalState) :
    ProductionCompletes (evalOutputRowsPreparedCore rows ctx env) s ↔
      ProductionCompletes (rowsCollect ctx env rows [] 0) s :=
  production_completes_iff_body (.evalOutputRowsPreparedCore rows ctx env)
    (fun rec => EvalBody.evalOutputRowsPreparedCore.collect rec ctx env rows [] 0) (fun _ => rfl)
    (finite_collect ctx env rows [] 0) s

theorem rowsCore_eq (rows : List Expr) (ctx : EvalCtx) (env : ValEnv) (s : EvalState)
    (hc : ProductionCompletes (rowsCollect ctx env rows [] 0) s) :
    (evalOutputRowsPreparedCore rows ctx env).runState s = (rowsCollect ctx env rows [] 0).runState s :=
  production_eq_of_finite (.evalOutputRowsPreparedCore rows ctx env)
    (fun rec => EvalBody.evalOutputRowsPreparedCore.collect rec ctx env rows [] 0) (fun _ => rfl)
    (finite_collect ctx env rows [] 0) s hc

theorem finite_prepared (a : Algorithm) (ha : NotBuiltin a) (ctx : EvalCtx) (env : ValEnv) :
    Finite (fun rec => EvalBody.evalAlgOutputPreparedCore rec a ctx env) := by
  have : (fun rec => EvalBody.evalAlgOutputPreparedCore rec a ctx env) = fun rec =>
      (ActivatedBody.check a >>= fun _ => enterAlgorithmBody a ctx env >>= fun pushed =>
        rec (.evalOutputRowsPreparedCore (Algorithm.output a) pushed env)) := by
    funext rec; exact prepared_body rec a ha ctx env
  rw [this]
  exact finite_bind (finite_const _) (fun _ => finite_bind (finite_const _) (fun _ => finite_call _))

theorem counted_eq_prepared (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    evalAlgOutputCounted a ctx env = evalAlgOutputPreparedCore a ctx env >>= fun out => pure out.counted := by
  have h₁ : evalAlgOutputCounted a ctx env = evalAlgOutputCountedCore a ctx env >>= pure :=
    delegation_equation (.evalAlgOutputCounted a ctx env) (.evalAlgOutputCountedCore a ctx env) pure
      (fun rec => (bind_pure_eq _).symm) (fun _ _ => nofun)
  have h₂ : evalAlgOutputCountedCore a ctx env =
      evalAlgOutputPreparedCore a ctx env >>= fun out => pure out.counted :=
    delegation_equation (.evalAlgOutputCountedCore a ctx env) (.evalAlgOutputPreparedCore a ctx env) _
      (fun _ => rfl) (fun _ _ => nofun)
  rw [h₁, bind_pure_eq, h₂]

/-- What the ordinary reading observes of a row supply. -/
structure ReaderAgreement (L : Except Error (List Result) × EvalState)
    (O : Except Error CountedResult × EvalState) : Prop where
  completes : L.1 ≠ .error .fuelExhausted ↔ O.1 ≠ .error .fuelExhausted
  ok : ∀ ys t, L = (.ok ys, t) → ∃ m, O = (.ok (combineOutputSlots ys, m), t)
  error : ∀ e t, e ≠ .fuelExhausted → L = (.error e, t) → O = (.error e.nestMissingOutput, t)

/-- **THE TWO READINGS OF ONE ACTIVATED BODY.** On a checked non-builtin body whose rows all have
    value-boundary counts on this run, the loop reader and the ordinary output reader perform the
    same body entry and the same `evalCounted` of every row: they complete together, reach the same
    state, the ordinary value is `combineOutputSlots` of the loop's row supply, and an error is the
    same error with its missing-output kind nested (Q-36). -/
theorem reader_agreement (a : Algorithm) (ha : NotBuiltin a) (hp : Passes a) (ctx : EvalCtx)
    (env : ValEnv) (s : EvalState)
    (hb : BoundedRows (enteredCtx a ctx s) env a.output (enteredState a ctx env s)) :
    ReaderAgreement ((evalAlgOutputSlots a ctx env).runState s) ((evalAlgOutputCounted a ctx env).runState s) := by
  have hrel := collect_rel (enteredCtx a ctx s) env a.output [] 0 _ hb
  have hbody : (EvalBody.evalAlgOutputSlots evalUnbounded a ctx env).runState s =
      (OutputRows.formLeftToRight (formOutputRow (enteredCtx a ctx s) env) a.output).runState
        (enteredState a ctx env s) :=
    readRows_entered (EvalRec.formOutputRow evalUnbounded) _ _ a ha hp ctx env s
  have hL : ProductionCompletes (evalAlgOutputSlots a ctx env) s ↔
      ProductionCompletes (OutputRows.formLeftToRight (formOutputRow (enteredCtx a ctx s) env) a.output)
        (enteredState a ctx env s) := by
    refine (production_completes_iff_body (.evalAlgOutputSlots a ctx env)
      (fun rec => EvalBody.evalAlgOutputSlots rec a ctx env) (fun _ => rfl)
      (finite_evalAlgOutputSlots a ctx env) s).trans ?_
    unfold ProductionCompletes; rw [hbody]
  have hLeq : ∀ hc : ProductionCompletes (evalAlgOutputSlots a ctx env) s,
      (evalAlgOutputSlots a ctx env).runState s =
        (OutputRows.formLeftToRight (formOutputRow (enteredCtx a ctx s) env) a.output).runState
          (enteredState a ctx env s) := by
    intro hc
    exact evalAlgOutputSlots_entered a ha hp ctx env s (hL.1 hc)
  have hP₁ : ProductionCompletes (evalAlgOutputPreparedCore a ctx env) s ↔
      ProductionCompletes (evalOutputRowsPreparedCore a.output (enteredCtx a ctx s) env) (enteredState a ctx env s) := by
    refine (production_completes_iff_body (.evalAlgOutputPreparedCore a ctx env)
      (fun rec => EvalBody.evalAlgOutputPreparedCore rec a ctx env) (fun _ => rfl)
      (finite_prepared a ha ctx env) s).trans ?_
    unfold ProductionCompletes; rw [prepared_entered_run _ a ha hp]; rfl
  have hPeq : ∀ hc : ProductionCompletes (evalAlgOutputPreparedCore a ctx env) s,
      (evalAlgOutputPreparedCore a ctx env).runState s =
        (evalOutputRowsPreparedCore a.output (enteredCtx a ctx s) env).runState (enteredState a ctx env s) := by
    intro hc
    have hc' : ProductionCompletes (EvalBody.evalAlgOutputPreparedCore evalUnbounded a ctx env) s := by
      unfold ProductionCompletes; rw [prepared_entered_run _ a ha hp]; exact hP₁.1 hc
    refine (production_eq_of_finite (.evalAlgOutputPreparedCore a ctx env)
      (fun rec => EvalBody.evalAlgOutputPreparedCore rec a ctx env) (fun _ => rfl)
      (finite_prepared a ha ctx env) s hc').trans ?_
    rw [prepared_entered_run _ a ha hp]; rfl
  have hcounted : (evalAlgOutputCounted a ctx env).runState s =
      (match (evalAlgOutputPreparedCore a ctx env).runState s with
       | (.ok out, t) => (.ok out.counted, t)
       | (.error e, t) => (.error e, t)) := by
    rw [counted_eq_prepared, EvalM.bind_runState]
    rcases (evalAlgOutputPreparedCore a ctx env).runState s with ⟨_ | _, _⟩ <;> rfl
  have hOc : ProductionCompletes (evalAlgOutputCounted a ctx env) s ↔
      ProductionCompletes (evalAlgOutputPreparedCore a ctx env) s := by
    unfold ProductionCompletes
    rw [hcounted]
    rcases (evalAlgOutputPreparedCore a ctx env).runState s with ⟨_ | _, _⟩
    · exact ⟨error_ne_fuel, error_ne_fuel⟩
    · exact iff_of_true (fun h' => nomatch h') (fun h' => nomatch h')
  -- The fold side of the comparison.
  generalize hF : (OutputRows.formLeftToRight (formOutputRow (enteredCtx a ctx s) env) a.output).runState
    (enteredState a ctx env s) = F at hrel
  have hcore : ProductionCompletes (rowsCollect (enteredCtx a ctx s) env a.output [] 0)
      (enteredState a ctx env s) ↔ F.1 ≠ .error .fuelExhausted := by
    unfold ProductionCompletes
    rcases F with ⟨_ | ys, t⟩
    · rename_i e
      dsimp only at hrel
      rw [hrel]
      cases e <;> simp [Error.nestMissingOutput]
    · dsimp only at hrel
      obtain ⟨m, hm⟩ := hrel
      rw [hm]
      exact iff_of_true (fun h' => nomatch h') (fun h' => nomatch h')
  have hFL : ProductionCompletes (evalAlgOutputSlots a ctx env) s ↔ F.1 ≠ .error .fuelExhausted := by
    refine hL.trans ?_
    unfold ProductionCompletes; rw [hF]
  have hOF : ProductionCompletes (evalAlgOutputCounted a ctx env) s ↔ F.1 ≠ .error .fuelExhausted :=
    hOc.trans (hP₁.trans ((rowsCore_completes_iff _ _ _ _).trans hcore))
  have hrowsEq : F.1 ≠ .error .fuelExhausted →
      (evalOutputRowsPreparedCore a.output (enteredCtx a ctx s) env).runState (enteredState a ctx env s) =
        (rowsCollect (enteredCtx a ctx s) env a.output [] 0).runState (enteredState a ctx env s) :=
    fun hc => rowsCore_eq _ _ _ _ (hcore.2 hc)
  refine ⟨hFL.trans hOF.symm, ?_, ?_⟩
  · intro ys t hl
    have hFc : F.1 ≠ .error .fuelExhausted := hFL.1 (by unfold ProductionCompletes; rw [hl]; nofun)
    have hFv : F = (.ok ys, t) := by rw [← hF, ← hLeq (hFL.2 hFc), hl]
    subst hFv
    dsimp only at hrel
    obtain ⟨m, hm⟩ := hrel
    refine ⟨m, ?_⟩
    rw [hcounted, hPeq (hP₁.2 ((rowsCore_completes_iff _ _ _ _).2 (hcore.2 hFc))), hrowsEq hFc, hm]
    rfl
  · intro e t he hl
    have hFc : F.1 ≠ .error .fuelExhausted := hFL.1 (by
      unfold ProductionCompletes; rw [hl]; intro h'; apply he; injection h')
    have hFv : F = (.error e, t) := by rw [← hF, ← hLeq (hFL.2 hFc), hl]
    subst hFv
    dsimp only at hrel
    rw [hcounted, hPeq (hP₁.2 ((rowsCore_completes_iff _ _ _ _).2 (hcore.2 hFc))), hrowsEq hFc, hrel]

/-! ## 3. One step over a formed supply: the loop reading and the ordinary call -/

/-- A wrapper with a pointwise outcome map neither creates nor hides incompleteness. -/
theorem completedAt_transform {α : Type} {W : EvalM α → EvalM α}
    (φ : Except Error α × EvalState → Except Error α × EvalState)
    (hφ : ∀ m s, (W m).runState s = φ (m.runState s))
    (hfuel : ∀ x, (φ x).1 ≠ .error .fuelExhausted ↔ x.1 ≠ .error .fuelExhausted)
    (B : EvalRec → EvalM α) (s : EvalState) (r : Except Error α × EvalState) :
    CompletedAt (fun rec => W (B rec)) s r ↔ ∃ x, CompletedAt B s x ∧ φ x = r := by
  constructor
  · rintro ⟨hr, k, hk⟩
    rw [hφ] at hk
    exact ⟨_, ⟨(hfuel _).1 (by rw [hk]; exact hr), k, rfl⟩, hk⟩
  · rintro ⟨x, ⟨hx, k, hk⟩, rfl⟩
    exact ⟨(hfuel x).2 hx, k, by rw [hφ, hk]⟩

/-- The outcome map of `withNestedMissingOutput`. -/
def nestOutcome {α : Type} : Except Error α × EvalState → Except Error α × EvalState
  | (.ok a, t) => (.ok a, t)
  | (.error e, t) => (.error e.nestMissingOutput, t)

theorem nestOutcome_fuel {α : Type} (x : Except Error α × EvalState) :
    (nestOutcome x).1 ≠ .error .fuelExhausted ↔ x.1 ≠ .error .fuelExhausted := by
  rcases x with ⟨_ | a, t⟩
  · rename_i e
    constructor
    · intro h h'
      apply h
      injection h' with h''
      subst h''
      rfl
    · intro h h'
      apply nest_ne_fuel e (fun he => h (by rw [he]))
      injection h'
  · exact ⟨fun _ => nofun, fun _ => nofun⟩

theorem nested_transform {α : Type} (B : EvalRec → EvalM α) (s : EvalState)
    (r : Except Error α × EvalState) :
    CompletedAt (fun rec => withNestedMissingOutput (B rec)) s r ↔
      ∃ x, CompletedAt B s x ∧ nestOutcome x = r :=
  completedAt_transform nestOutcome
    (fun m s => by rw [nested_run]; rcases m.runState s with ⟨_ | _, _⟩ <;> rfl)
    nestOutcome_fuel B s r

/-- The outcome map of `withCtx`. -/
def ctxOutcome {α : Type} (c : String) : Except Error α × EvalState → Except Error α × EvalState
  | (.ok a, t) => (.ok a, t)
  | (.error .fuelExhausted, t) => (.error .fuelExhausted, t)
  | (.error e, t) => (.error (Error.withContext c e), t)

theorem ctx_run {α : Type} (c : String) (m : EvalM α) (s : EvalState) :
    (withCtx c m).runState s = ctxOutcome c (m.runState s) := by
  unfold withCtx
  rw [EvalM.bind_runState]
  rcases h : m.runState s with ⟨o, t⟩
  cases o with
  | ok a => rw [evalAttempt_runState_of_complete m s t _ h rfl]; rfl
  | error e =>
    by_cases he : e = .fuelExhausted
    · subst he; rw [evalAttempt_runState_of_incomplete m s t h]; rfl
    · have hc : (Except.error e : Except Error α).isIncomplete = false := by
        cases e <;> first | exact absurd rfl he | rfl
      rw [evalAttempt_runState_of_complete m s t _ h hc]
      cases e <;> first | exact absurd rfl he | rfl

theorem ctxOutcome_fuel {α : Type} (c : String) (x : Except Error α × EvalState) :
    (ctxOutcome c x).1 ≠ .error .fuelExhausted ↔ x.1 ≠ .error .fuelExhausted := by
  rcases x with ⟨_ | a, t⟩
  · rename_i e
    cases e <;> simp [ctxOutcome]
  · exact ⟨fun _ => nofun, fun _ => nofun⟩

theorem ctx_transform {α : Type} (c : String) (B : EvalRec → EvalM α) (s : EvalState)
    (r : Except Error α × EvalState) :
    CompletedAt (fun rec => withCtx c (B rec)) s r ↔ ∃ x, CompletedAt B s x ∧ ctxOutcome c x = r :=
  completedAt_transform (ctxOutcome c) (ctx_run c) (ctxOutcome_fuel c) B s r

/-- An activated body, its context and its values. -/
abbrev Activation := Algorithm × EvalCtx × ValEnv

/-- The ordinary-call domain of one activation: a checked non-builtin body whose rows, entered from
    `t`, all have value-boundary counts. -/
structure ActivationDomain (p : Activation) (t : EvalState) : Prop where
  notBuiltin : NotBuiltin p.1
  passes : Passes p.1
  rows : BoundedRows (enteredCtx p.1 p.2.1 t) p.2.2 p.1.output (enteredState p.1 p.2.1 p.2.2 t)

/-- The ordinary call's counted observation of a row supply: the value `combineOutputSlots`,
    re-counted at the call's value boundary. -/
def ordinaryValue (ys : List Result) : CountedResult :=
  reCountValueBoundary (combineOutputSlots ys, 0)

/-- The ordinary outcome a completed loop reading determines. -/
def ordinaryOutcome : Except Error (List Result) × EvalState → Except Error CountedResult × EvalState
  | (.ok ys, u) => (.ok (ordinaryValue ys), u)
  | (.error e, u) => (.error e.nestMissingOutput, u)

/-- The loop reading of an activation. -/
def loopRead (A : EvalRec → EvalM Activation) (rec : EvalRec) : EvalM (List Result) :=
  A rec >>= fun p => rec.evalAlgOutputSlots p.1 p.2.1 p.2.2

/-- The ordinary reading of an activation. -/
def ordinaryRead (A : EvalRec → EvalM Activation) (rec : EvalRec) : EvalM CountedResult :=
  withNestedMissingOutput (A rec) >>= fun p =>
    rec.evalAlgOutputCounted p.1 p.2.1 p.2.2 >>= fun r => pure (reCountValueBoundary r)

theorem monotone_read_slots (p : Activation) :
    monotone (fun rec : EvalRec => rec.evalAlgOutputSlots p.1 p.2.1 p.2.2) :=
  fun _ _ h => h (.evalAlgOutputSlots p.1 p.2.1 p.2.2)

theorem monotone_read_counted (p : Activation) :
    monotone (fun rec : EvalRec => rec.evalAlgOutputCounted p.1 p.2.1 p.2.2 >>= fun r =>
      pure (reCountValueBoundary r)) :=
  (finite_bind (B := fun rec => rec (.evalAlgOutputCounted p.1 p.2.1 p.2.2))
    (K := fun _ r => pure (reCountValueBoundary r))
    (finite_call (.evalAlgOutputCounted p.1 p.2.1 p.2.2)) (fun _ => finite_const _)).1

theorem completedAt_slots (p : Activation) (t : EvalState) (r : Except Error (List Result) × EvalState) :
    CompletedAt (fun rec => rec.evalAlgOutputSlots p.1 p.2.1 p.2.2) t r ↔
      ((evalAlgOutputSlots p.1 p.2.1 p.2.2).runState t = r ∧ r.1 ≠ .error .fuelExhausted) :=
  completedAt_call (.evalAlgOutputSlots p.1 p.2.1 p.2.2) t r

theorem completedAt_counted (p : Activation) (t : EvalState) (r : Except Error CountedResult × EvalState) :
    CompletedAt (fun rec => rec.evalAlgOutputCounted p.1 p.2.1 p.2.2) t r ↔
      ((evalAlgOutputCounted p.1 p.2.1 p.2.2).runState t = r ∧ r.1 ≠ .error .fuelExhausted) :=
  completedAt_call (.evalAlgOutputCounted p.1 p.2.1 p.2.2) t r

theorem completedAt_recounted (p : Activation) (t u : EvalState) (o : Except Error CountedResult)
    (h : CompletedAt (fun rec => rec.evalAlgOutputCounted p.1 p.2.1 p.2.2) t (o, u)) :
    CompletedAt (fun rec => rec.evalAlgOutputCounted p.1 p.2.1 p.2.2 >>= fun r =>
      pure (reCountValueBoundary r)) t
      (match o with | .ok c => .ok (reCountValueBoundary c) | .error e => .error e, u) := by
  obtain ⟨hr, k, hk⟩ := h
  refine ⟨?_, k, ?_⟩
  · cases o with
    | ok c => exact nofun
    | error e => exact hr
  · rw [EvalM.bind_runState, hk]
    cases o <;> rfl

theorem ordinaryValue_of_combined (ys : List Result) (m : Nat) :
    reCountValueBoundary (combineOutputSlots ys, m) = ordinaryValue ys := rfl

theorem reader_forward (p : Activation) (t : EvalState) (hd : ActivationDomain p t)
    (r : Except Error (List Result) × EvalState) (hr : r.1 ≠ .error .fuelExhausted)
    (hrun : (evalAlgOutputSlots p.1 p.2.1 p.2.2).runState t = r) :
    CompletedAt (fun rec => rec.evalAlgOutputCounted p.1 p.2.1 p.2.2 >>= fun x =>
      pure (reCountValueBoundary x)) t (ordinaryOutcome r) := by
  have hag := reader_agreement p.1 hd.notBuiltin hd.passes p.2.1 p.2.2 t hd.rows
  rcases r with ⟨_ | ys, u⟩
  · rename_i e
    have he : e ≠ .fuelExhausted := fun he => hr (by rw [he])
    have hO := hag.error e u he hrun
    exact completedAt_recounted p t u _ ((completedAt_counted p t _).2 ⟨hO, by
      intro h'; apply nest_ne_fuel e he; injection h'⟩)
  · obtain ⟨m, hO⟩ := hag.ok ys u hrun
    exact completedAt_recounted p t u _ ((completedAt_counted p t _).2 ⟨hO, nofun⟩)

/-- **A shared activation.** Two receivers of one activation complete together; a completed loop
    reading determines the ordinary reading. -/
theorem shared_activation_forward (A : EvalRec → EvalM Activation) (hA : monotone A) (s : EvalState)
    (hdom : ∀ p t, CompletedAt A s (.ok p, t) → ActivationDomain p t)
    (r : Except Error (List Result) × EvalState) (h : CompletedAt (loopRead A) s r) :
    CompletedAt (ordinaryRead A) s (ordinaryOutcome r) := by
  have hOmono : ∀ p : Activation, monotone (fun rec : EvalRec => rec.evalAlgOutputCounted p.1 p.2.1 p.2.2 >>= fun r =>
      pure (reCountValueBoundary r)) := monotone_read_counted
  rcases completedAt_bind_inv h with ⟨p, t, hp, hrest⟩ | ⟨e, t, rfl, herr⟩
  · have hrun := (completedAt_slots p t r).1 hrest
    have hn : CompletedAt (fun rec => withNestedMissingOutput (A rec)) s (.ok p, t) :=
      (nested_transform A s _).2 ⟨_, hp, rfl⟩
    exact completedAt_bind_ok (monotone_withNestedMissingOutput A hA) (hOmono p) hn
      (reader_forward p t (hdom p t hp) r hrun.2 hrun.1)
  · exact completedAt_bind_error ((nested_transform A s _).2 ⟨_, herr, rfl⟩)

/-- The converse: a completed ordinary reading comes from a completed loop reading. -/
theorem shared_activation_backward (A : EvalRec → EvalM Activation) (hA : monotone A) (s : EvalState)
    (hdom : ∀ p t, CompletedAt A s (.ok p, t) → ActivationDomain p t)
    (r : Except Error CountedResult × EvalState) (h : CompletedAt (ordinaryRead A) s r) :
    ∃ rL, CompletedAt (loopRead A) s rL := by
  rcases completedAt_bind_inv h with ⟨p, t, hp, hrest⟩ | ⟨e, t, rfl, herr⟩
  · obtain ⟨x, hx, hxe⟩ := (nested_transform A s _).1 hp
    rcases x with ⟨_ | p', t'⟩
    · cases hxe
    · cases hxe
      have hd := hdom p t hx
      have hag := reader_agreement p.1 hd.notBuiltin hd.passes p.2.1 p.2.2 t hd.rows
      have hcounted : ProductionCompletes (evalAlgOutputCounted p.1 p.2.1 p.2.2) t := by
        rcases completedAt_bind_inv hrest with ⟨c, u, hc, _⟩ | ⟨e, u, _, hc⟩
        · unfold ProductionCompletes; rw [((completedAt_counted p t _).1 hc).1]; nofun
        · have := (completedAt_counted p t _).1 hc
          unfold ProductionCompletes; rw [this.1]; exact this.2
      have hslots : ProductionCompletes (evalAlgOutputSlots p.1 p.2.1 p.2.2) t := hag.completes.2 hcounted
      have hL := (completedAt_slots p t _).2 ⟨rfl, hslots⟩
      exact ⟨_, completedAt_bind_ok hA (monotone_read_slots p) hx hL⟩
  · obtain ⟨x, hx, hxe⟩ := (nested_transform A s _).1 herr
    rcases x with ⟨_ | a, u⟩
    · cases hxe
      exact ⟨_, completedAt_bind_error hx⟩
    · cases hxe


/-- What the two receivers observe of one step over one supply. `wrap` is the loop receiver's own
    error frame (`id` for a user step, the step's call frame for a family). -/
structure StepAgreement (wrap : Error → Error) (L : Except Error (List Result) × EvalState)
    (O : Except Error CountedResult × EvalState) : Prop where
  completes : L.1 ≠ .error .fuelExhausted ↔ O.1 ≠ .error .fuelExhausted
  ok : ∀ ys t, L = (.ok ys, t) → O = (.ok (ordinaryValue ys), t)
  error : ∀ e t, e ≠ .fuelExhausted → L = (.error e, t) →
    ∃ e₀, e = wrap e₀ ∧ O = (.error e₀.nestMissingOutput, t)

theorem shared_agreement (A : EvalRec → EvalM Activation) (hA : monotone A) (s : EvalState)
    (hdom : ∀ p t, CompletedAt A s (.ok p, t) → ActivationDomain p t)
    (W : EvalM (List Result) → EvalM (List Result))
    (φ : Except Error (List Result) × EvalState → Except Error (List Result) × EvalState)
    (hφ : ∀ m s, (W m).runState s = φ (m.runState s))
    (hfuel : ∀ x, (φ x).1 ≠ .error .fuelExhausted ↔ x.1 ≠ .error .fuelExhausted)
    (wrap : Error → Error)
    (hok : ∀ ys t, φ (.ok ys, t) = (.ok ys, t))
    (herr : ∀ e t, e ≠ .fuelExhausted → φ (.error e, t) = (.error (wrap e), t))
    (L : Except Error (List Result) × EvalState) (O : Except Error CountedResult × EvalState)
    (hLrun : ∀ r, CompletedAt (fun rec => W (loopRead A rec)) s r ↔
      (L = r ∧ r.1 ≠ .error .fuelExhausted))
    (hOrun : ∀ r, CompletedAt (ordinaryRead A) s r ↔ (O = r ∧ r.1 ≠ .error .fuelExhausted)) :
    StepAgreement wrap L O := by
  have fwd : L.1 ≠ .error .fuelExhausted → ∃ x, x.1 ≠ .error .fuelExhausted ∧ φ x = L ∧
      O = ordinaryOutcome x := by
    intro hc
    obtain ⟨x, hx, hxe⟩ := (completedAt_transform φ hφ hfuel (loopRead A) s L).1 ((hLrun L).2 ⟨rfl, hc⟩)
    exact ⟨x, hx.1, hxe, ((hOrun _).1 (shared_activation_forward A hA s hdom x hx)).1⟩
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro hc
    obtain ⟨x, hx, -, hOe⟩ := fwd hc
    rw [hOe]
    rcases x with ⟨_ | ys, u⟩
    · rename_i e
      intro h'
      apply nest_ne_fuel e (fun he => hx (by rw [he]))
      injection h'
    · exact nofun
  · intro hc
    obtain ⟨rL, hrL⟩ := shared_activation_backward A hA s hdom O ((hOrun O).2 ⟨rfl, hc⟩)
    have := (hLrun _).1 ((completedAt_transform φ hφ hfuel (loopRead A) s _).2 ⟨rL, hrL, rfl⟩)
    rw [this.1]; exact this.2
  · intro ys t hl
    obtain ⟨x, hx, hxe, hOe⟩ := fwd (by rw [hl]; nofun)
    rw [hl] at hxe
    rcases x with ⟨_ | ys', u⟩
    · rename_i e; rw [herr e u (fun he => hx (by rw [he]))] at hxe; cases hxe
    · rw [hok] at hxe; cases hxe; exact hOe
  · intro e t he hl
    obtain ⟨x, hx, hxe, hOe⟩ := fwd (by rw [hl]; intro h'; apply he; injection h')
    rw [hl] at hxe
    rcases x with ⟨_ | ys', u⟩
    · rename_i e₀
      rw [herr e₀ u (fun he => hx (by rw [he]))] at hxe
      cases hxe
      exact ⟨e₀, rfl, hOe⟩
    · rw [hok] at hxe; cases hxe

/-! ### The user step -/

/-- The binder patterns of a callee. -/
abbrev calleePatterns (a : Algorithm) : List NeedPattern :=
  (Algorithm.parameterPatterns a).map NeedPattern.ofParameter

/-- A user activation over a supply: the one binder, one fresh binding context. -/
def userActivation (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) (cells : List Nat) (rec : EvalRec) :
    EvalM Activation :=
  bindNeedPatterns rec.bindingChannels (calleePatterns a) cells >>= fun o =>
    match o with
    | some bindings => needBindingContext ctx bindings >>= fun next =>
        pure (a, next, ValEnv.shadow env (Algorithm.params a))
    | none => throw Error.badArity

theorem monotone_binder (patterns : List NeedPattern) (cells : List Nat) (family : Bool) :
    monotone (fun rec : EvalRec => bindNeedPatterns rec.bindingChannels patterns cells family) := by
  mono_tac

theorem monotone_userActivation (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) (cells : List Nat) :
    monotone (userActivation a ctx env cells) := by
  unfold userActivation
  exact (monotone_bind _ _ _ (monotone_binder _ _ _) (monotone_const _))

/-- A user step with written output, passing the body checks, without a value view. -/
structure UserStep (a : Algorithm) : Prop where
  user : ∃ p pp o pr e rows d, a = .mk p pp o pr (e :: rows) d
  checks : Passes a
  noView : ∀ s, (valueViewCell? a).runState s = (.ok none, s)

/-- A parameterized body is never a value view. -/
theorem noView_of_params (p : Option ScopeCtx) (q : ParameterPattern) (qs : List ParameterPattern)
    (o : List Expr) (pr : List PropDef) (out : List Expr) (d : Option PropertyIdentity) (s : EvalState) :
    (valueViewCell? (.mk p (q :: qs) o pr out d)).runState s = (.ok none, s) := rfl

/-- A multi-row body is never a value view. -/
theorem noView_of_rows (p : Option ScopeCtx) (pp : List ParameterPattern)
    (o : List Expr) (pr : List PropDef) (e₁ e₂ : Expr) (rows : List Expr) (d : Option PropertyIdentity)
    (s : EvalState) :
    (valueViewCell? (.mk p pp o pr (e₁ :: e₂ :: rows) d)).runState s = (.ok none, s) := by
  cases pp <;> rfl

theorem user_loop_body (a : Algorithm) (h : UserStep a) (ctx : EvalCtx) (env : ValEnv)
    (cells : List Nat) (name : String) (rec : EvalRec) :
    evalStep rec (.runNeedStepSlots a ctx env cells name) = loopRead (userActivation a ctx env cells) rec := by
  obtain ⟨p, pp, o, pr, e, rows, d, rfl⟩ := h.user
  apply EvalM.ext; intro s
  show (EvalBody.runNeedStepSlots rec _ ctx env cells name).runState s = _
  simp only [EvalBody.runNeedStepSlots, EvalBody.runNeedStepWith, loopRead, userActivation,
    EvalM.bind_runState]
  rcases (bindNeedPatterns rec.bindingChannels _ cells).runState s with ⟨_ | (_ | b), t⟩
  · rfl
  · rfl
  · simp only [EvalM.bind_runState]
    rcases (needBindingContext ctx b).runState t with ⟨_ | n, u⟩
    · rfl
    · rfl

theorem user_ordinary_body (a : Algorithm) (h : UserStep a) (ctx : EvalCtx) (env : ValEnv)
    (cells : List Nat) (rec : EvalRec) :
    evalStep rec (.evalNeedUserSupply a cells ctx env) = ordinaryRead (userActivation a ctx env cells) rec := by
  have hview := h.noView
  obtain ⟨p, pp, o, pr, e, rows, d, rfl⟩ := h.user
  apply EvalM.ext; intro s
  show (EvalBody.evalNeedUserSupply rec _ cells ctx env).runState s = _
  simp only [EvalBody.evalNeedUserSupply, EvalBody.evalNeedUserSupplyOutput, ordinaryRead, userActivation,
    EvalM.bind_runState, nested_run]
  rcases (bindNeedPatterns rec.bindingChannels _ cells).runState s with ⟨_ | (_ | b), t⟩
  · rfl
  · rfl
  · dsimp only
    rw [if_neg (by simp [Algorithm.output])]
    simp only [EvalM.bind_runState, needBindingContext_run, hview, pure_runState]


/-- The rows of a user step are at value boundaries on this run: for each completed binding from
    `s`, its body, entered in that binding's context, satisfies `BoundedRows`. -/
def UserRowsBounded (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) (cells : List Nat) (s : EvalState) : Prop :=
  ∀ b t next u, (bindNeedPatterns bindingChannels (calleePatterns a) cells).runState s = (.ok (some b), t) →
    (needBindingContext ctx b).runState t = (.ok next, u) →
    BoundedRows (enteredCtx a next u) (ValEnv.shadow env (Algorithm.params a)) a.output
      (enteredState a next (ValEnv.shadow env (Algorithm.params a)) u)

theorem user_activation_domain (a : Algorithm) (h : UserStep a) (ctx : EvalCtx) (env : ValEnv)
    (cells : List Nat) (s : EvalState) (hrows : UserRowsBounded a ctx env cells s) (p : Activation)
    (t : EvalState) (hp : CompletedAt (userActivation a ctx env cells) s (.ok p, t)) :
    ActivationDomain p t := by
  have hn : NotBuiltin a := by
    obtain ⟨_, _, _, _, _, _, _, rfl⟩ := h.user
    intro b hb; cases hb
  rcases completedAt_bind_inv (B := fun rec => bindNeedPatterns rec.bindingChannels (calleePatterns a) cells)
    (K := fun _ o => match o with
      | some bindings => needBindingContext ctx bindings >>= fun next =>
          pure (a, next, ValEnv.shadow env (Algorithm.params a))
      | none => throw Error.badArity) hp with ⟨o, t₁, hb, hrest⟩ | ⟨_, _, he, _⟩
  · have hbp := hb.production (monotone_binder _ _ _)
    cases o with
    | none =>
      obtain ⟨hr, k, hk⟩ := hrest
      have : ((Except.error Error.badArity : Except Error Activation), t₁) = (.ok p, t) := hk
      cases this
    | some b =>
      obtain ⟨_, k, hk⟩ := hrest
      change (needBindingContext ctx b >>= fun next =>
        (pure (a, next, ValEnv.shadow env (Algorithm.params a)) : EvalM Activation)).runState t₁ = _ at hk
      rw [EvalM.bind_runState] at hk
      rcases hnb : (needBindingContext ctx b).runState t₁ with ⟨_ | next, u⟩
      · rw [hnb] at hk; cases hk
      · rw [hnb] at hk
        cases hk
        exact ⟨hn, h.checks, hrows b t₁ next _ hbp hnb⟩
  · cases he

/-- **THE COUNT-ONE ROUND AGAINST THE ORDINARY CALL (user step).** Over the SAME supplied cells and
    from the SAME state, the loop step `runNeedStepSlots` and the ordinary call `evalNeedUserSupply`
    run the same binder and the same body: they complete together and reach the SAME state; the
    ordinary value is `ordinaryValue` of the step's row supply; an error is the same error with
    its missing-output kind nested. Domain: `UserStep` and `UserRowsBounded`. -/
theorem user_step_agreement (a : Algorithm) (h : UserStep a) (ctx : EvalCtx) (env : ValEnv)
    (cells : List Nat) (name : String) (s : EvalState) (hrows : UserRowsBounded a ctx env cells s) :
    StepAgreement id ((runNeedStepSlots a ctx env cells name).runState s)
      ((evalNeedUserSupply a cells ctx env).runState s) := by
  refine shared_agreement (userActivation a ctx env cells) (monotone_userActivation a ctx env cells) s
    (user_activation_domain a h ctx env cells s hrows) id id (fun _ _ => rfl) (fun _ => Iff.rfl) id
    (fun _ _ => rfl) (fun _ _ _ => rfl) _ _ ?_ ?_
  · intro r
    have h1 := completedAt_step (.runNeedStepSlots a ctx env cells name) s r
    rw [show (fun rec => evalStep rec (.runNeedStepSlots a ctx env cells name)) =
      fun rec => id (loopRead (userActivation a ctx env cells) rec) from
      funext (user_loop_body a h ctx env cells name)] at h1
    exact h1
  · intro r
    have h1 := completedAt_step (.evalNeedUserSupply a cells ctx env) s r
    rw [show (fun rec => evalStep rec (.evalNeedUserSupply a cells ctx env)) =
      ordinaryRead (userActivation a ctx env cells) from
      funext (user_ordinary_body a h ctx env cells)] at h1
    exact h1

/-! ### The clause-family step -/

/-- A family activation: the ordinary dispatcher over the supply. -/
def familyActivation (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) (cells : List Nat) (name : String)
    (rec : EvalRec) : EvalM Activation :=
  selectNeedFamilyBranch rec.bindingChannels a cells ctx env name

theorem monotone_familyActivation (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) (cells : List Nat)
    (name : String) : monotone (familyActivation a ctx env cells name) := by
  unfold familyActivation; mono_tac

/-- Every activation the dispatcher completes with from `s` is in the ordinary-call domain. -/
def FamilyRowsBounded (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) (cells : List Nat) (name : String)
    (s : EvalState) : Prop :=
  ∀ p t, (selectNeedFamilyBranch bindingChannels a cells ctx env name).runState s = (.ok p, t) →
    ActivationDomain p t

theorem family_loop_body (p : Option ScopeCtx) (o : List Expr) (br : List CondBranch)
    (d : Option PropertyIdentity) (ctx : EvalCtx) (env : ValEnv) (cells : List Nat) (name : String)
    (rec : EvalRec) :
    evalStep rec (.runNeedStepSlots (.conditional p o br d) ctx env cells name) =
      withCtx s!"while evaluating call to {name}"
        (loopRead (familyActivation (.conditional p o br d) ctx env cells name) rec) := rfl

theorem family_ordinary_body (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) (cells : List Nat)
    (name : String) (rec : EvalRec) :
    evalStep rec (.evalNeedFamilySupply a cells ctx env name) =
      ordinaryRead (familyActivation a ctx env cells name) rec := rfl

/-- **THE COUNT-ONE ROUND AGAINST THE ORDINARY CALL (selected clause).** As `user_step_agreement`,
    for the one family dispatcher. The loop keeps its step call frame around the error
    (`wrap`); the ordinary call nests it instead. -/
theorem family_step_agreement (p : Option ScopeCtx) (o : List Expr) (br : List CondBranch)
    (d : Option PropertyIdentity) (ctx : EvalCtx) (env : ValEnv) (cells : List Nat) (name : String)
    (s : EvalState) (hrows : FamilyRowsBounded (.conditional p o br d) ctx env cells name s) :
    StepAgreement (Error.withContext s!"while evaluating call to {name}")
      ((runNeedStepSlots (.conditional p o br d) ctx env cells name).runState s)
      ((evalNeedFamilySupply (.conditional p o br d) cells ctx env name).runState s) := by
  have hm := monotone_familyActivation (.conditional p o br d) ctx env cells name
  let c := s!"while evaluating call to {name}"
  refine shared_agreement (familyActivation (.conditional p o br d) ctx env cells name) hm s
    (fun p' t hp => hrows p' t (hp.production hm)) (withCtx c) (ctxOutcome c) (ctx_run c) (ctxOutcome_fuel c)
    (Error.withContext c) (fun _ _ => rfl) ?_ _ _ ?_ ?_
  · intro e t he
    cases e <;> first | exact absurd rfl he | rfl
  · intro r
    have h1 := completedAt_step (.runNeedStepSlots (.conditional p o br d) ctx env cells name) s r
    rw [show (fun rec => evalStep rec (.runNeedStepSlots (.conditional p o br d) ctx env cells name)) =
      fun rec => withCtx c (loopRead (familyActivation (.conditional p o br d) ctx env cells name) rec) from
      funext (family_loop_body p o br d ctx env cells name)] at h1
    exact h1
  · intro r
    have h1 := completedAt_step (.evalNeedFamilySupply (.conditional p o br d) cells ctx env name) s r
    rw [show (fun rec => evalStep rec (.evalNeedFamilySupply (.conditional p o br d) cells ctx env name)) =
      ordinaryRead (familyActivation (.conditional p o br d) ctx env cells name) from
      funext (family_ordinary_body _ ctx env cells name)] at h1
    exact h1

/-! ### Builtin and alias steps, over the generic dispatch -/

/-- The argument list a step dispatch passes a builtin: need-backed, source-free. -/
def stepArguments (cells : List Nat) : List ResolvedArgumentAlgorithm :=
  cells.map fun address =>
    ({ algorithm := Algorithm.ofExpr (.emptySequence 0), need? := some address } : ResolvedArgumentAlgorithm)

theorem finite_withCtx {α : Type} (c : String) {B : EvalRec → EvalM α} (hB : Finite B) :
    Finite (fun rec => withCtx c (B rec)) := by
  unfold withCtx
  refine finite_bind (finite_evalAttempt hB) (fun o => ?_)
  cases o <;> exact finite_const _

/-- The outcome of a builtin step: the application's outcome, its ONE result as ONE row. -/
def builtinStepOutcome (c : String) :
    Except Error CountedResult × EvalState → Except Error (List Result) × EvalState
  | (.ok out, t) => (.ok (loopStepBuiltinRows out), t)
  | (.error .fuelExhausted, t) => (.error .fuelExhausted, t)
  | (.error e, t) => (.error (Error.withContext c e), t)

/-- A builtin step at production, with no binder premise: it completes exactly when its ordinary
    application does, and then its ONE result is ONE row under the step's own frame. -/
theorem builtin_step_run (b : Builtin) (ctx : EvalCtx) (env : ValEnv) (cells : List Nat) (name : String)
    (s : EvalState) :
    (ProductionCompletes (runNeedStepSlots (.builtin b) ctx env cells name) s ↔
      ProductionCompletes (applyBuiltinCountedResolved b (stepArguments cells) ctx env) s) ∧
    (ProductionCompletes (applyBuiltinCountedResolved b (stepArguments cells) ctx env) s →
      (runNeedStepSlots (.builtin b) ctx env cells name).runState s =
        builtinStepOutcome s!"while evaluating call to {name}"
          ((applyBuiltinCountedResolved b (stepArguments cells) ctx env).runState s)) := by
  have hb : Finite (fun rec : EvalRec => withCtx s!"while evaluating call to {name}"
      (rec (.applyBuiltinCountedResolved b (stepArguments cells) ctx env) >>= fun out =>
        pure (loopStepBuiltinRows out))) :=
    finite_withCtx _ (finite_bind (finite_call _) (fun _ => finite_const _))
  have hstep : ∀ rec, evalStep rec (.runNeedStepSlots (.builtin b) ctx env cells name) =
      withCtx s!"while evaluating call to {name}"
        (rec (.applyBuiltinCountedResolved b (stepArguments cells) ctx env) >>= fun out =>
          pure (loopStepBuiltinRows out)) := fun _ => rfl
  have hbody : (withCtx s!"while evaluating call to {name}"
      (applyBuiltinCountedResolved b (stepArguments cells) ctx env >>= fun out =>
        pure (loopStepBuiltinRows out))).runState s = builtinStepOutcome s!"while evaluating call to {name}"
        ((applyBuiltinCountedResolved b (stepArguments cells) ctx env).runState s) := by
    rw [ctx_run, EvalM.bind_runState]
    rcases (applyBuiltinCountedResolved b (stepArguments cells) ctx env).runState s with ⟨_ | _, _⟩
    · rename_i e; cases e <;> rfl
    · rfl
  have hfuel : ∀ x : Except Error CountedResult × EvalState,
      (builtinStepOutcome s!"while evaluating call to {name}" x).1 ≠ .error .fuelExhausted ↔
        x.1 ≠ .error .fuelExhausted := by
    rintro ⟨_ | _, t⟩
    · rename_i e; cases e <;> simp [builtinStepOutcome]
    · exact iff_of_true nofun nofun
  have hbc : ProductionCompletes (withCtx s!"while evaluating call to {name}"
      (applyBuiltinCountedResolved b (stepArguments cells) ctx env >>= fun out =>
        pure (loopStepBuiltinRows out))) s ↔
      ProductionCompletes (applyBuiltinCountedResolved b (stepArguments cells) ctx env) s := by
    unfold ProductionCompletes
    rw [hbody]; exact hfuel _
  refine ⟨(production_completes_iff_body _ _ hstep hb s).trans hbc, fun hc => ?_⟩
  exact (production_eq_of_finite (.runNeedStepSlots (.builtin b) ctx env cells name) _ hstep hb s
    (hbc.2 hc)).trans hbody

/-- Over a source-free supply the ordinary builtin arm IS the application the step dispatch runs. -/
theorem ordinary_builtin_is_step_application (origin : CalleeOrigin) (b : Builtin) (cells : List Nat)
    (ctx : EvalCtx) (env : ValEnv) (name : String) :
    evalSuppliedCallCounted origin (.builtin b) (cells.map fun c => (c, none)) ctx env name =
      applyBuiltinCountedResolved b (stepArguments cells) ctx env := by
  have h := delegation_equation
    (.evalSuppliedCallCounted origin (.builtin b) (cells.map fun c => (c, none)) ctx env name)
    (.applyBuiltinCountedResolved b (stepArguments cells) ctx env) pure
    (fun rec => by
      refine Eq.trans ?_ (bind_pure_eq _).symm
      show EvalBody.evalSuppliedCallCounted rec origin (.builtin b) _ ctx env name = _
      simp only [EvalBody.evalSuppliedCallCounted, List.map_map, stepArguments]
      rfl)
    (fun _ _ => nofun)
  exact h.trans (bind_pure_eq _)

/-- A non-empty supply reaches the ordinary user arm of `evalSuppliedCallCounted` directly: the
    zero-supply publication route (CACHE-PUB-1) is out of the way, whatever the origin. -/
theorem ordinary_user_of_nonempty (origin : CalleeOrigin) (p : Option ScopeCtx)
    (pp : List ParameterPattern) (o : List Expr) (pr : List PropDef) (out : List Expr)
    (d : Option PropertyIdentity) (c : NeedSupply.Sourced) (cs : List NeedSupply.Sourced)
    (ctx : EvalCtx) (env : ValEnv) (name : String) :
    evalSuppliedCallCounted origin (.mk p pp o pr out d) (c :: cs) ctx env name =
      evalNeedUserSupply (.mk p pp o pr out d) ((c :: cs).map Prod.fst) ctx env :=
  (delegation_equation
    (.evalSuppliedCallCounted origin (.mk p pp o pr out d) (c :: cs) ctx env name)
    (.evalNeedUserSupply (.mk p pp o pr out d) ((c :: cs).map Prod.fst) ctx env) pure
    (fun rec => (Eq.trans (by rfl) (bind_pure_eq _).symm)) (fun _ _ => nofun)).trans (bind_pure_eq _)

/-- An alias step resolves its target once and IS that target's step. -/
theorem alias_step_run (p : Option ScopeCtx) (o : List Expr) (pr : List PropDef) (t : Expr)
    (d : Option PropertyIdentity) (rf : Bool) (ctx : EvalCtx) (env : ValEnv)
    (cells : List Nat) (name : String) (s : EvalState)
    (hc : ProductionCompletes (resolveAliasTarget (.alias p o pr t d rf) ctx >>= fun target =>
      runNeedStepSlots target ctx env cells name) s) :
    (runNeedStepSlots (.alias p o pr t d rf) ctx env cells name).runState s =
      (resolveAliasTarget (.alias p o pr t d rf) ctx >>= fun target =>
        runNeedStepSlots target ctx env cells name).runState s :=
  production_eq_of_finite (.runNeedStepSlots (.alias p o pr t d rf) ctx env cells name)
    (fun rec => rec (.resolveAliasTarget (.alias p o pr t d rf) ctx) >>= fun target =>
      rec (.runNeedStepSlots target ctx env cells name)) (fun _ => rfl)
    (finite_bind (finite_call _) (fun _ => finite_call _)) s hc

/-! ## 4. The real state cells -/

/-- The Ready cell one emitted slot becomes. -/
def readyCell (v : Result) : NeedCell := { suspension := .ready (v, Result.valueCount v) }

/-- That cell after its VALUE was demanded. -/
def completedCell (v : Result) : NeedCell :=
  { suspension := .ready (v, Result.valueCount v), state := .completed (.ok (v, Result.valueCount v)) }

/-- The addresses of the next `slots.length` cells. -/
def readyAddrs : Nat → List Result → List Nat
  | _, [] => []
  | n, _ :: rest => n :: readyAddrs (n + 1) rest

/-- `s` with Ready cells for `slots` appended, in order; every other field unchanged. -/
def pushReady (s : EvalState) (slots : List Result) : EvalState :=
  { s with needs := s.needs ++ (slots.map readyCell).toArray }

/-- `s` with COMPLETED Ready cells for `slots` appended, in order; every other field unchanged. -/
def pushCompleted (s : EvalState) (slots : List Result) : EvalState :=
  { s with needs := s.needs ++ (slots.map completedCell).toArray }

/-- The allocation of a round's next state. -/
abbrev allocReady (slots : List Result) : EvalM (List Nat) :=
  slots.mapM (fun value => readyNeed (value, Result.valueCount value))

theorem alloc_run (slots : List Result) (s : EvalState) :
    (allocReady slots).runState s = (.ok (readyAddrs s.needs.size slots), pushReady s slots) := by
  rw [KatLang.NeedControl.Schedule.mapM_schedule]
  induction slots generalizing s with
  | nil => simp [KatLang.NeedControl.Schedule.schedule, readyAddrs, pushReady]
  | cons v rest ih =>
    simp only [KatLang.NeedControl.Schedule.schedule]
    have h : (readyNeed (v, Result.valueCount v)).runState s =
        (.ok s.needs.size, { s with needs := s.needs.push (readyCell v) }) := rfl
    rw [h]
    dsimp only
    rw [ih]
    simp [readyAddrs, pushReady]

/-- Setting the first suffix cell. -/
theorem modify_suffix (h : Array NeedCell) (c : NeedCell) (l : List NeedCell) (f : NeedCell → NeedCell) :
    (h ++ (c :: l).toArray).modify h.size f = h ++ (f c :: l).toArray := by
  apply Array.ext
  · simp
  · intro i h₁ h₂
    simp only [Array.getElem_modify, Array.getElem_append]
    by_cases hi : i < h.size
    · have hne : ¬ h.size = i := by omega
      simp [hi, hne]
    · by_cases he : h.size = i
      · subst he; simp
      · have hk : i - h.size ≠ 0 := by omega
        obtain ⟨k, hk'⟩ := Nat.exists_eq_succ_of_ne_zero hk
        simp [hi, he, hk']

/-- The heap after one completed Ready demand: the cell went `evaluating`, then `completed`. -/
def evaluatedAt (h : Array NeedCell) (a : Nat) (v : CountedResult) : Array NeedCell :=
  (h.modify a (fun c => { c with state := .evaluating })).modify a
    (fun c => { c with state := .completed (.ok v) })

theorem demand_ready (a : Nat) (s : EvalState) (c : NeedCell) (v : CountedResult)
    (hc : s.needs[a]? = some c) (hs : c.state = .suspended) (hsusp : c.suspension = .ready v) :
    (demandNeedRecursive a).runState s =
      (.ok v, { s with needs := evaluatedAt s.needs a v }) := by
  refine production_of_answer_free (.demandNeedRecursive a) s _ (fun rec => ?_) nofun
  show (NeedDemand.step (rec.evalSuppliedAt a) rec.planRoute rec.demandNeedRecursive a).runState s = _
  refine KatLang.NeedControl.Memo.suspended_retains_state _ _ _ a s
    { s with needs := s.needs.modify a (fun c => { c with state := .evaluating }) } c (.ok v) hc hs ?_ rfl
  rw [hsusp]; rfl

/-- Read a list of state cells as the loop's final slots. -/
abbrev materialize (final : List Nat) : EvalM (List Result) :=
  final.mapM (fun address => Prod.fst <$> demandNeedRecursive address)

/-- The final materialization of freshly allocated Ready cells: exactly their slots, in order; each
    cell completes, nothing else changes. -/
theorem materialize_ready (slots : List Result) (h : Array NeedCell) (s : EvalState)
    (hs : s.needs = h ++ (slots.map readyCell).toArray) :
    (materialize (readyAddrs h.size slots)).runState s =
      (.ok slots, { s with needs := h ++ (slots.map completedCell).toArray }) := by
  rw [KatLang.NeedControl.Schedule.mapM_schedule]
  induction slots generalizing h s with
  | nil =>
    simp at hs
    subst hs
    simp [readyAddrs, KatLang.NeedControl.Schedule.schedule]
  | cons v rest ih =>
    simp only [readyAddrs, KatLang.NeedControl.Schedule.schedule]
    have hget : s.needs[h.size]? = some (readyCell v) := by
      rw [hs]; simp
    have hd := demand_ready h.size s (readyCell v) (v, Result.valueCount v) hget rfl rfl
    have hneeds : evaluatedAt s.needs h.size (v, Result.valueCount v) =
        h.push (completedCell v) ++ (rest.map readyCell).toArray := by
      rw [hs, List.map_cons, evaluatedAt, modify_suffix, modify_suffix]
      simp [readyCell, completedCell]
    have hm : (Prod.fst <$> demandNeedRecursive h.size).runState s = _ :=
      KatLang.NeedControl.Collector.map_run _ _ _
    rw [hm, hd]
    dsimp only
    have hi := ih (h.push (completedCell v)) { s with needs := evaluatedAt s.needs h.size (v, Result.valueCount v) } hneeds
    rw [Array.size_push] at hi
    rw [hi]
    simp [completedCell]

/-! ## 5. Finite `repeat`: composition over the real state cells -/

section Drivers
variable (step : ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) (name : String)

/-- The evaluator's `repeat` driver, at evaluator answer `rec`. -/
abbrev repeatDriver (rec : EvalRec) (n : Nat) (cells : List Nat) : EvalM (List Nat) :=
  EvalBody.applyBuiltinCounted.repeatLoop rec ctx env step name n cells

/-- ONE `repeat` round over the state cells: project the retained step, read its row supply over
    the cells, allocate the supply as the next Ready cells. -/
def repeatRound (rec : EvalRec) (cells : List Nat) : EvalM (List Nat) :=
  rec.invokeNeed step >>= fun o =>
    projectInvokingSlot (invokingSlotRole .repeatBuiltin) o >>= fun algorithm =>
      rec.runNeedStepSlots algorithm ctx env cells name >>= fun slots => allocReady slots

theorem repeatDriver_zero (rec : EvalRec) (cells : List Nat) :
    repeatDriver step ctx env name rec 0 cells = pure cells := rfl

/-- The successor law of the driver: ONE round, then the rest over its Ready cells. -/
theorem repeatDriver_succ (rec : EvalRec) (n : Nat) (cells : List Nat) :
    repeatDriver step ctx env name rec (n + 1) cells =
      (repeatRound step ctx env name rec cells >>= repeatDriver step ctx env name rec n) := by
  apply EvalM.ext; intro s
  show (rec.invokeNeed step >>= fun o =>
    projectInvokingSlot (invokingSlotRole .repeatBuiltin) o >>= fun algorithm =>
      rec.runNeedStepSlots algorithm ctx env cells name >>= fun slots =>
        allocReady slots >>= fun next => repeatDriver step ctx env name rec n next).runState s = _
  simp only [repeatRound, EvalM.bind_runState]
  rcases (rec.invokeNeed step).runState s with ⟨_ | o, s₁⟩
  · rfl
  · cases o with
    | none => rfl
    | some a =>
      simp only [projectInvokingSlot, pure_runState]
      rcases (rec.runNeedStepSlots a ctx env cells name).runState s₁ with ⟨_ | ys, s₂⟩
      · rfl
      · dsimp only

/-- `repeat` composes: `m + n` rounds are `m` rounds, then `n` over the resulting cells. -/
theorem repeatDriver_add (rec : EvalRec) (m n : Nat) (cells : List Nat) :
    repeatDriver step ctx env name rec (m + n) cells =
      (repeatDriver step ctx env name rec m cells >>= repeatDriver step ctx env name rec n) := by
  induction m generalizing cells with
  | zero =>
    rw [Nat.zero_add]
    apply EvalM.ext; intro s
    rw [EvalM.bind_runState]; rfl
  | succ m ih =>
    rw [Nat.succ_add, repeatDriver_succ, repeatDriver_succ]
    apply EvalM.ext; intro s
    simp only [EvalM.bind_runState, ih]
    rcases (repeatRound step ctx env name rec cells).runState s with ⟨_ | _, _⟩ <;> rfl

/-- **THE FINITE `repeat` DERIVATION**: exactly the production rounds, over the real cells. Every
    premise is a production subcall; the first failure stops the composition in its retained
    state. `done` is the zero-iteration case: no projection and no invocation. -/
inductive RepeatTrace : Nat → List Nat → EvalState → Except Error (List Nat) → EvalState → Prop
  | done (cells : List Nat) (s : EvalState) : RepeatTrace 0 cells s (.ok cells) s
  | next {n : Nat} {cells : List Nat} {s s₁ s₂ t : EvalState} {alg : Algorithm} {slots : List Result}
      {r : Except Error (List Nat)} :
      (invokeNeed step).runState s = (.ok (some alg), s₁) →
      (runNeedStepSlots alg ctx env cells name).runState s₁ = (.ok slots, s₂) →
      RepeatTrace n (readyAddrs s₂.needs.size slots) (pushReady s₂ slots) r t →
      RepeatTrace (n + 1) cells s r t
  | projectError {n : Nat} {cells : List Nat} {s t : EvalState} {e : Error} :
      e ≠ .fuelExhausted → (invokeNeed step).runState s = (.error e, t) →
      RepeatTrace (n + 1) cells s (.error e) t
  | refused {n : Nat} {cells : List Nat} {s t : EvalState} :
      (invokeNeed step).runState s = (.ok none, t) →
      RepeatTrace (n + 1) cells s (.error (Error.notAnAlgorithm (invokingSlotRole .repeatBuiltin))) t
  | stepError {n : Nat} {cells : List Nat} {s s₁ t : EvalState} {alg : Algorithm} {e : Error} :
      e ≠ .fuelExhausted → (invokeNeed step).runState s = (.ok (some alg), s₁) →
      (runNeedStepSlots alg ctx env cells name).runState s₁ = (.error e, t) →
      RepeatTrace (n + 1) cells s (.error e) t

/-- The production round, as a total run. -/
theorem repeatRound_run (rec : EvalRec) (cells : List Nat) (s : EvalState) :
    (repeatRound step ctx env name rec cells).runState s =
      (match (rec.invokeNeed step).runState s with
       | (.error e, t) => (.error e, t)
       | (.ok none, t) => (.error (Error.notAnAlgorithm (invokingSlotRole .repeatBuiltin)), t)
       | (.ok (some a), s₁) =>
         match (rec.runNeedStepSlots a ctx env cells name).runState s₁ with
         | (.error e, t) => (.error e, t)
         | (.ok ys, s₂) => (.ok (readyAddrs s₂.needs.size ys), pushReady s₂ ys)) := by
  simp only [repeatRound, EvalM.bind_runState]
  rcases (rec.invokeNeed step).runState s with ⟨_ | o, s₁⟩
  · rfl
  · cases o with
    | none => rfl
    | some a =>
      simp only [projectInvokingSlot, pure_runState]
      rcases (rec.runNeedStepSlots a ctx env cells name).runState s₁ with ⟨_ | ys, s₂⟩
      · rfl
      · simp only [alloc_run]

/-- **FINITE `repeat` CORRESPONDENCE.** A finite derivation of `n` rounds IS a completed production
    driver run of `n` rounds, in both directions: outcome and state. -/
theorem repeat_trace_iff (n : Nat) (cells : List Nat) (s t : EvalState) (r : Except Error (List Nat)) :
    RepeatTrace step ctx env name n cells s r t ↔
      ((repeatDriver step ctx env name evalUnbounded n cells).runState s = (r, t) ∧
        r ≠ .error .fuelExhausted) := by
  constructor
  · intro h
    induction h with
    | done cells s => exact ⟨rfl, nofun⟩
    | @next n cells s s₁ s₂ t alg slots r hi hs _ ih =>
      refine ⟨?_, ih.2⟩
      rw [repeatDriver_succ, EvalM.bind_runState, repeatRound_run]
      simp only [EvalRec.invokeNeed, EvalRec.runNeedStepSlots]
      rw [show evalUnbounded (.invokeNeed step) = invokeNeed step from rfl, hi]
      simp only
      rw [show evalUnbounded (.runNeedStepSlots alg ctx env cells name) = runNeedStepSlots alg ctx env cells name from rfl, hs]
      exact ih.1
    | @projectError n cells s t e he hi =>
      refine ⟨?_, fun h => he (by injection h)⟩
      rw [repeatDriver_succ, EvalM.bind_runState, repeatRound_run]
      simp only [EvalRec.invokeNeed]
      rw [show evalUnbounded (.invokeNeed step) = invokeNeed step from rfl, hi]
    | @refused n cells s t hi =>
      refine ⟨?_, nofun⟩
      rw [repeatDriver_succ, EvalM.bind_runState, repeatRound_run]
      simp only [EvalRec.invokeNeed]
      rw [show evalUnbounded (.invokeNeed step) = invokeNeed step from rfl, hi]
    | @stepError n cells s s₁ t alg e he hi hs =>
      refine ⟨?_, fun h => he (by injection h)⟩
      rw [repeatDriver_succ, EvalM.bind_runState, repeatRound_run]
      simp only [EvalRec.invokeNeed, EvalRec.runNeedStepSlots]
      rw [show evalUnbounded (.invokeNeed step) = invokeNeed step from rfl, hi]
      simp only
      rw [show evalUnbounded (.runNeedStepSlots alg ctx env cells name) = runNeedStepSlots alg ctx env cells name from rfl, hs]
  · rintro ⟨h, hr⟩
    induction n generalizing cells s with
    | zero =>
      cases h
      exact .done _ _
    | succ n ih =>
      rw [repeatDriver_succ, EvalM.bind_runState, repeatRound_run] at h
      simp only [EvalRec.invokeNeed, EvalRec.runNeedStepSlots] at h
      rw [show evalUnbounded (.invokeNeed step) = invokeNeed step from rfl] at h
      rcases hi : (invokeNeed step).runState s with ⟨_ | o, s₁⟩
      · rename_i e
        rw [hi] at h
        cases h
        exact .projectError (fun he => hr (by rw [he])) hi
      · rw [hi] at h
        cases o with
        | none => cases h; exact .refused hi
        | some a =>
          simp only at h
          rw [show evalUnbounded (.runNeedStepSlots a ctx env cells name) = runNeedStepSlots a ctx env cells name from rfl] at h
          rcases hs : (runNeedStepSlots a ctx env cells name).runState s₁ with ⟨_ | ys, s₂⟩
          · rename_i e
            rw [hs] at h
            cases h
            exact .stepError (fun he => hr (by rw [he])) hi hs
          · rw [hs] at h
            exact .next hi hs (ih _ _ h)

/-! ## 6. Finite `while`: the condition-first stopping and error traces -/

/-- One `while` iteration over its state cells, written out at evaluator answer `rec`. -/
abbrev whileDriver (cells : List Nat) : EvalM (List Nat) :=
  evalUnbounded (.whileLoop step ctx env name cells)

theorem whileBody_run (rec : EvalRec) (cells : List Nat) (s : EvalState) :
    (EvalBody.whileLoop rec step ctx env name cells).runState s =
      (match (rec.invokeNeed step).runState s with
       | (.error e, t) => (.error e, t)
       | (.ok none, t) => (.error (Error.notAnAlgorithm (invokingSlotRole .whileBuiltin)), t)
       | (.ok (some a), s₁) =>
         match (rec.runNeedWhileRound a ctx env cells name).runState s₁ with
         | (.error e, t) => (.error e, t)
         | (.ok none, t) => (.ok cells, t)
         | (.ok (some ys), s₂) =>
           (rec.whileLoop step ctx env name (readyAddrs s₂.needs.size ys)).runState (pushReady s₂ ys)) := by
  simp only [EvalBody.whileLoop, WhileRound.advance, EvalM.bind_runState]
  rcases (rec.invokeNeed step).runState s with ⟨_ | o, s₁⟩
  · rfl
  · cases o with
    | none => rfl
    | some a =>
      simp only [projectInvokingSlot, pure_runState]
      rcases (rec.runNeedWhileRound a ctx env cells name).runState s₁ with ⟨_ | o', s₂⟩
      · rfl
      · cases o' with
        | none => rfl
        | some ys =>
          simp only [EvalM.bind_runState]
          rw [show (List.mapM (fun value => readyNeed (value, Result.valueCount value)) ys).runState s₂ = _ from alloc_run ys s₂]
          rfl

theorem finite_whileLoop (cells : List Nat) :
    Finite (fun rec => EvalBody.whileLoop rec step ctx env name cells) := by
  unfold EvalBody.whileLoop
  refine finite_bind (finite_call (.invokeNeed step)) (fun o => ?_)
  refine finite_bind (finite_const _) (fun alg => ?_)
  unfold WhileRound.advance
  refine finite_bind (finite_bind (finite_call _) (fun o' => ?_)) (fun x => ?_)
  · cases o' with
    | none => exact finite_const _
    | some ys => exact finite_bind (finite_const _) (fun _ => finite_const _)
  · cases x with
    | inl _ => exact finite_const _
    | inr next => exact finite_call _

/-- **THE FINITE `while` DERIVATION**, indexed by its accepted transitions. Every step is the
    production `invokeNeed` and the production condition-first round; `stop` retains the ENTERING
    cell addresses and the state the false round left (its discovery effects are not rolled back). -/
inductive WhileTrace : Nat → List Nat → EvalState → Except Error (List Nat) → EvalState → Prop
  | stop {cells : List Nat} {s s₁ t : EvalState} {alg : Algorithm} :
      (invokeNeed step).runState s = (.ok (some alg), s₁) →
      (runNeedWhileRound alg ctx env cells name).runState s₁ = (.ok none, t) →
      WhileTrace 0 cells s (.ok cells) t
  | next {n : Nat} {cells : List Nat} {s s₁ s₂ t : EvalState} {alg : Algorithm} {slots : List Result}
      {r : Except Error (List Nat)} :
      (invokeNeed step).runState s = (.ok (some alg), s₁) →
      (runNeedWhileRound alg ctx env cells name).runState s₁ = (.ok (some slots), s₂) →
      WhileTrace n (readyAddrs s₂.needs.size slots) (pushReady s₂ slots) r t →
      WhileTrace (n + 1) cells s r t
  | projectError {cells : List Nat} {s t : EvalState} {e : Error} :
      e ≠ .fuelExhausted → (invokeNeed step).runState s = (.error e, t) →
      WhileTrace 0 cells s (.error e) t
  | refused {cells : List Nat} {s t : EvalState} :
      (invokeNeed step).runState s = (.ok none, t) →
      WhileTrace 0 cells s (.error (Error.notAnAlgorithm (invokingSlotRole .whileBuiltin))) t
  | roundError {cells : List Nat} {s s₁ t : EvalState} {alg : Algorithm} {e : Error} :
      e ≠ .fuelExhausted → (invokeNeed step).runState s = (.ok (some alg), s₁) →
      (runNeedWhileRound alg ctx env cells name).runState s₁ = (.error e, t) →
      WhileTrace 0 cells s (.error e) t

theorem whileProduction_step (cells : List Nat) (s : EvalState)
    (hc : ProductionCompletes (EvalBody.whileLoop evalUnbounded step ctx env name cells) s) :
    (whileDriver step ctx env name cells).runState s =
      (EvalBody.whileLoop evalUnbounded step ctx env name cells).runState s :=
  production_eq_of_finite (.whileLoop step ctx env name cells)
    (fun rec => EvalBody.whileLoop rec step ctx env name cells) (fun _ => rfl)
    (finite_whileLoop step ctx env name cells) s hc

/-- A derivation is a completed production run. -/
theorem while_of_trace {n : Nat} {cells : List Nat} {s t : EvalState} {r : Except Error (List Nat)}
    (h : WhileTrace step ctx env name n cells s r t) :
    (whileDriver step ctx env name cells).runState s = (r, t) ∧ r ≠ .error .fuelExhausted := by
  induction h with
  | @stop cells s s₁ t alg hi hr =>
    have hb : (EvalBody.whileLoop evalUnbounded step ctx env name cells).runState s = (.ok cells, t) := by
      rw [whileBody_run]
      show (match (invokeNeed step).runState s with | (.error e, t) => _ | (.ok none, t) => _ | (.ok (some a), s₁) => _) = _
      rw [hi]
      show (match (runNeedWhileRound alg ctx env cells name).runState s₁ with | (.error e, t) => _ | (.ok none, t) => _ | (.ok (some ys), s₂) => _) = _
      rw [hr]
    exact ⟨(whileProduction_step step ctx env name cells s (by unfold ProductionCompletes; rw [hb]; nofun)).trans hb, nofun⟩
  | @next n cells s s₁ s₂ t alg slots r hi hr _ ih =>
    have hb : (EvalBody.whileLoop evalUnbounded step ctx env name cells).runState s = (r, t) := by
      rw [whileBody_run]
      show (match (invokeNeed step).runState s with | (.error e, t) => _ | (.ok none, t) => _ | (.ok (some a), s₁) => _) = _
      rw [hi]
      show (match (runNeedWhileRound alg ctx env cells name).runState s₁ with | (.error e, t) => _ | (.ok none, t) => _ | (.ok (some ys), s₂) => _) = _
      rw [hr]
      exact ih.1
    exact ⟨(whileProduction_step step ctx env name cells s (by unfold ProductionCompletes; rw [hb]; exact ih.2)).trans hb, ih.2⟩
  | @projectError cells s t e he hi =>
    have hb : (EvalBody.whileLoop evalUnbounded step ctx env name cells).runState s = (.error e, t) := by
      rw [whileBody_run]
      show (match (invokeNeed step).runState s with | (.error e, t) => _ | (.ok none, t) => _ | (.ok (some a), s₁) => _) = _
      rw [hi]
    have hne : (Except.error e : Except Error (List Nat)) ≠ .error .fuelExhausted := fun h => he (by injection h)
    exact ⟨(whileProduction_step step ctx env name cells s (by unfold ProductionCompletes; rw [hb]; exact hne)).trans hb, hne⟩
  | @refused cells s t hi =>
    have hb : (EvalBody.whileLoop evalUnbounded step ctx env name cells).runState s =
        (.error (Error.notAnAlgorithm (invokingSlotRole .whileBuiltin)), t) := by
      rw [whileBody_run]
      show (match (invokeNeed step).runState s with | (.error e, t) => _ | (.ok none, t) => _ | (.ok (some a), s₁) => _) = _
      rw [hi]
    exact ⟨(whileProduction_step step ctx env name cells s (by unfold ProductionCompletes; rw [hb]; nofun)).trans hb, nofun⟩
  | @roundError cells s s₁ t alg e he hi hr =>
    have hb : (EvalBody.whileLoop evalUnbounded step ctx env name cells).runState s = (.error e, t) := by
      rw [whileBody_run]
      show (match (invokeNeed step).runState s with | (.error e, t) => _ | (.ok none, t) => _ | (.ok (some a), s₁) => _) = _
      rw [hi]
      show (match (runNeedWhileRound alg ctx env cells name).runState s₁ with | (.error e, t) => _ | (.ok none, t) => _ | (.ok (some ys), s₂) => _) = _
      rw [hr]
    have hne : (Except.error e : Except Error (List Nat)) ≠ .error .fuelExhausted := fun h => he (by injection h)
    exact ⟨(whileProduction_step step ctx env name cells s (by unfold ProductionCompletes; rw [hb]; exact hne)).trans hb, hne⟩

theorem subcall_production (c : EvalCall) (k : Nat) (s : EvalState) (r : Except Error c.Ret × EvalState)
    (h : (evalFuel k c).runState s = r) (hr : r.1 ≠ .error .fuelExhausted) :
    (evalUnbounded c).runState s = r :=
  ((completedAt_call c s r).1 ⟨hr, k, h⟩).1

/-- A completed core run at any fuel has a finite derivation. -/
theorem trace_of_fuel (k : Nat) : ∀ (cells : List Nat) (s t : EvalState) (r : Except Error (List Nat)),
    (evalFuel k (.whileLoop step ctx env name cells)).runState s = (r, t) →
    r ≠ .error .fuelExhausted → ∃ n, WhileTrace step ctx env name n cells s r t := by
  induction k with
  | zero =>
    intro cells s t r h hr
    cases h
    exact absurd rfl hr
  | succ k ih =>
    intro cells s t r h hr
    rw [evalFuel_succ] at h
    have hb := body_of_normalized _ s (r, t) hr h
    change (EvalBody.whileLoop (evalFuel k) step ctx env name cells).runState s = (r, t) at hb
    rw [whileBody_run] at hb
    rcases hi : (EvalRec.invokeNeed (evalFuel k) step).runState s with ⟨_ | o, s₁⟩
    · rename_i e
      rw [hi] at hb
      cases hb
      have hne : e ≠ .fuelExhausted := fun he => hr (by rw [he])
      exact ⟨0, .projectError hne (subcall_production (.invokeNeed step) k s _ hi (fun h' => hne (by injection h')))⟩
    · rw [hi] at hb
      have hip := subcall_production (.invokeNeed step) k s (.ok o, s₁) hi nofun
      cases o with
      | none =>
        cases hb
        exact ⟨0, .refused hip⟩
      | some a =>
        simp only at hb
        rcases hrd : (EvalRec.runNeedWhileRound (evalFuel k) a ctx env cells name).runState s₁ with ⟨_ | o', s₂⟩
        · rename_i e
          rw [hrd] at hb
          cases hb
          have hne : e ≠ .fuelExhausted := fun he => hr (by rw [he])
          exact ⟨0, .roundError hne hip (subcall_production (.runNeedWhileRound a ctx env cells name) k s₁ _ hrd
            (fun h' => hne (by injection h')))⟩
        · rw [hrd] at hb
          have hrp := subcall_production (.runNeedWhileRound a ctx env cells name) k s₁ (.ok o', s₂) hrd nofun
          cases o' with
          | none =>
            cases hb
            exact ⟨0, .stop hip hrp⟩
          | some ys =>
            obtain ⟨n, hn⟩ := ih _ _ _ _ hb hr
            exact ⟨n + 1, .next hip hrp hn⟩

/-- **FINITE `while` CORRESPONDENCE.** A completed production driver run — a false round after finite
    accepted transitions, or an ordinary error after a finite prefix — IS a finite derivation,
    and conversely: outcome and state. Fuel exhaustion is not an outcome of either side. -/
theorem while_trace_iff (cells : List Nat) (s t : EvalState) (r : Except Error (List Nat)) :
    (∃ n, WhileTrace step ctx env name n cells s r t) ↔
      ((whileDriver step ctx env name cells).runState s = (r, t) ∧ r ≠ .error .fuelExhausted) := by
  constructor
  · rintro ⟨n, h⟩
    exact while_of_trace step ctx env name h
  · rintro ⟨h, hr⟩
    obtain ⟨hc, k, hk⟩ := (completedAt_call (.whileLoop step ctx env name cells) s (r, t)).2 ⟨h, hr⟩
    exact trace_of_fuel step ctx env name k cells s t r hk hr

end Drivers

/-! ## 7. The whole builtin arms: setup, driver, final materialization -/

theorem finite_mapM {α β : Type} (f : EvalRec → α → EvalM β) (h : ∀ a, Finite (fun rec => f rec a))
    (xs : List α) : Finite (fun rec => xs.mapM (f rec)) := by
  have key : ∀ (xs : List α) (acc : List β), Finite (fun rec => List.mapM.loop (f rec) xs acc) := by
    intro xs
    induction xs with
    | nil => intro acc; exact finite_const _
    | cons a rest ih =>
      intro acc
      exact finite_bind (h a) (fun b => ih (b :: acc))
  exact key xs []

theorem finite_classify (shape : NeedPlan.CallShape) :
    Finite (fun rec : EvalRec => rec.planRoute.classify shape) := by
  show Finite (fun rec : EvalRec => classifyPlanRouteWith rec.resolveDotReceiver? rec.algorithmIntrinsicRoute shape)
  unfold classifyPlanRouteWith
  cases shape.form with
  | call =>
    dsimp only
    cases linkEdge? shape.callee with
    | none => exact finite_const _
    | some p =>
      dsimp only
      exact finite_bind (finite_call _) (fun b => by cases b <;> exact finite_const _)
  | dot receiver name fallback =>
    dsimp only
    refine finite_bind (finite_call _) (fun o => ?_)
    exact finite_const _

theorem finite_routeOf (a : Nat) (shape : NeedPlan.CallShape) :
    Finite (fun rec : EvalRec => NeedPlan.routeOf rec.planRoute.classify a shape) := by
  unfold NeedPlan.routeOf
  refine finite_bind (finite_const _) (fun st => ?_)
  cases st.needs[a]? with
  | none => exact finite_const _
  | some cell =>
    dsimp only
    cases cell.route with
    | some r => exact finite_const _
    | none =>
      dsimp only
      exact finite_bind (finite_classify shape) (fun _ => finite_const _)

theorem finite_calleeCell (a : Nat) :
    Finite (fun rec : EvalRec => NeedPlan.calleeCell rec.planRoute.classify a) := by
  unfold NeedPlan.calleeCell
  refine finite_bind (finite_const _) (fun st => ?_)
  cases st.needs[a]? with
  | none => exact finite_const _
  | some cell =>
    dsimp only
    cases cell.callee with
    | some c => exact finite_const _
    | none =>
      dsimp only
      cases NeedPlan.ofSuspension? cell.suspension with
      | none => exact finite_const _
      | some shape =>
        dsimp only
        exact finite_bind (finite_routeOf a shape) (fun _ => finite_const _)

theorem finite_metaLoopCapture (adapter : Nat) :
    Finite (fun rec : EvalRec =>
      metaLoopCapture rec.planRoute.classify rec.demandNeedRecursive rec.argumentViewCells adapter) := by
  unfold metaLoopCapture
  refine finite_bind (finite_call (.demandNeedRecursive adapter)) (fun _ => ?_)
  refine finite_bind (finite_const _) (fun plan => ?_)
  refine finite_bind (finite_call (.argumentViewCells plan)) (fun _ => ?_)
  exact finite_bind (finite_calleeCell plan) (fun _ => finite_const _)

/-- The address of a builtin parameter in its binding. -/
def boundCell (bindings : NeedEnv) (name : Ident) : EvalM Nat :=
  match lookupAssoc name bindings with
  | some address => pure address
  | none => throw (Error.illegalInEval s!"unbound builtin parameter {name}")

/-- The cell-backed step argument the arms pass the drivers. -/
def stepArgument (stepCell : Nat) : ResolvedArgumentAlgorithm :=
  { algorithm := Algorithm.ofExpr (.emptySequence 0), need? := some stepCell }

/-- The arms' captured setup (`metaLoopCapture` at the evaluator's channels). -/
def loopCapture (rec : EvalRec) (bindings : NeedEnv) : EvalM (ResolvedArgumentAlgorithm × List Nat) := do
  let (stepCell, initialCells) <- metaLoopCapture rec.planRoute.classify rec.demandNeedRecursive
    rec.argumentViewCells (<- boundCell bindings "step")
  pure (stepArgument stepCell, initialCells)

/-- The `repeat` arm's count demand. -/
def countDemand (rec : EvalRec) (c : ResolvedArgumentAlgorithm) (bindings : NeedEnv) (ctx : EvalCtx)
    (env : ValEnv) : EvalM Int := do
  expectInt (<- rec.evalArgumentValue { c with need? := some (<- boundCell bindings "count") } ctx env)

/-- A driver, then the loop's separate final boundary (LOOP-07). -/
def finishLoop (rec : EvalRec) (driver : EvalM (List Nat)) : EvalM CountedResult := do
  let finalCells <- driver
  let finalSlots <- finalCells.mapM (fun address => Prod.fst <$> rec.demandNeedRecursive address)
  pure (loopResultCounted finalSlots)

/-- `repeat` AFTER ITS SETUP: `n` rounds from the initial cells, then final materialization. -/
def repeatAfterSetup (rec : EvalRec) (step : ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv)
    (name : String) (n : Nat) (cells : List Nat) : EvalM CountedResult :=
  finishLoop rec (repeatDriver step ctx env name rec n cells)

/-- `while` AFTER ITS SETUP: the driver from the initial cells, then final materialization. -/
def whileAfterSetup (rec : EvalRec) (step : ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv)
    (name : String) (cells : List Nat) : EvalM CountedResult :=
  finishLoop rec (rec.whileLoop step ctx env name cells)

/-- The `repeat` arm once its binding is formed. -/
def repeatTail (rec : EvalRec) (c : ResolvedArgumentAlgorithm) (bindings : NeedEnv) (ctx : EvalCtx)
    (env : ValEnv) : EvalM CountedResult := do
  let ((step, initialCells), n) <- metaRepeatSetup (loopCapture rec bindings) (countDemand rec c bindings ctx env)
  if n < 0 then
    .error (Error.illegalInEval "Repeat count must be >= 0")
  else
    let name <- loopStepName "repeat" step
    repeatAfterSetup rec step ctx env name n.toNat initialCells

/-- The `repeat` binding's outcome. -/
def repeatBinding (rec : EvalRec) (c : ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) :
    Option NeedEnv → EvalM CountedResult
  | some bindings => repeatTail rec c bindings ctx env
  | _ => throw Error.badArity

/-- The `repeat` arm: its cells, THE one binder over its signature, then its tail. -/
def repeatBody (rec : EvalRec) (a c : ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) :
    EvalM CountedResult :=
  [a, c].mapM (fun arg => rec.argumentNeed arg ctx env) >>= fun cells =>
    bindNeedPatterns rec.bindingChannels ((builtinSignature .repeatBuiltin).map NeedPattern.ofParameter) cells >>=
      repeatBinding rec c ctx env

/-- The `while` arm once its binding is formed. -/
def whileTail (rec : EvalRec) (bindings : NeedEnv) (ctx : EvalCtx) (env : ValEnv) : EvalM CountedResult := do
  let (step, initialCells) <- loopCapture rec bindings
  let name <- loopStepName "while" step
  whileAfterSetup rec step ctx env name initialCells

/-- The `while` binding's outcome. -/
def whileBinding (rec : EvalRec) (ctx : EvalCtx) (env : ValEnv) : Option NeedEnv → EvalM CountedResult
  | some bindings => whileTail rec bindings ctx env
  | _ => throw Error.badArity

/-- The `while` arm. -/
def whileBody (rec : EvalRec) (a : ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) :
    EvalM CountedResult :=
  [a].mapM (fun arg => rec.argumentNeed arg ctx env) >>= fun cells =>
    bindNeedPatterns rec.bindingChannels ((builtinSignature .whileBuiltin).map NeedPattern.ofParameter) cells >>=
      whileBinding rec ctx env

/-- **THE INSTALLATION.** The `repeat` arm of `applyBuiltinCounted` IS these stages, at every evaluator
    answer: an exact definitional equation over the real channels. -/
theorem repeat_arm (rec : EvalRec) (a c : ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) :
    EvalBody.applyBuiltinCounted rec .repeatBuiltin [a, c] ctx env =
      withNestedMissingOutput (repeatBody rec a c ctx env) := rfl

/-- **THE INSTALLATION.** The `while` arm of `applyBuiltinCounted`. -/
theorem while_arm (rec : EvalRec) (a : ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) :
    EvalBody.applyBuiltinCounted rec .whileBuiltin [a] ctx env =
      withNestedMissingOutput (whileBody rec a ctx env) := rfl

theorem repeatNames : needRepeatedNames [.metaRef "step", .bind "count"] = [] := by
  simp [needRepeatedNames, NeedPattern.names, List.eraseDups, List.eraseDupsBy, List.eraseDupsBy.loop]

theorem whileNames : needRepeatedNames [.metaRef "step"] = [] := by
  simp [needRepeatedNames, NeedPattern.names, List.eraseDups, List.eraseDupsBy, List.eraseDupsBy.loop]

/-- The loop signatures inspect nothing: their binder uses neither channel. -/
theorem repeat_binder_channel_free (ch ch' : NeedChannels) (cells : List Nat) :
    bindNeedPatterns ch ((builtinSignature .repeatBuiltin).map NeedPattern.ofParameter) cells =
      bindNeedPatterns ch' ((builtinSignature .repeatBuiltin).map NeedPattern.ofParameter) cells := by
  rw [KatLang.MetaLoopLaws.repeat_binding_patterns]
  simp only [bindNeedPatterns, NeedBinder.bindPatterns, NeedBinder.bindLevel, repeatNames]
  rfl

theorem while_binder_channel_free (ch ch' : NeedChannels) (cells : List Nat) :
    bindNeedPatterns ch ((builtinSignature .whileBuiltin).map NeedPattern.ofParameter) cells =
      bindNeedPatterns ch' ((builtinSignature .whileBuiltin).map NeedPattern.ofParameter) cells := by
  rw [KatLang.MetaLoopLaws.while_binding_patterns]
  simp only [bindNeedPatterns, NeedBinder.bindPatterns, NeedBinder.bindLevel, whileNames]
  rfl

theorem finite_loopCapture (bindings : NeedEnv) : Finite (fun rec => loopCapture rec bindings) := by
  unfold loopCapture
  refine finite_bind (finite_const _) (fun adapter => ?_)
  exact finite_bind (finite_metaLoopCapture adapter) (fun _ => finite_const _)

theorem finite_countDemand (c : ResolvedArgumentAlgorithm) (bindings : NeedEnv) (ctx : EvalCtx) (env : ValEnv) :
    Finite (fun rec => countDemand rec c bindings ctx env) := by
  unfold countDemand
  refine finite_bind (finite_const _) (fun address => ?_)
  exact finite_bind (finite_call _) (fun _ => finite_const _)

theorem finite_finishLoop (D : EvalRec → EvalM (List Nat)) (hD : Finite D) :
    Finite (fun rec => finishLoop rec (D rec)) := by
  unfold finishLoop
  refine finite_bind hD (fun cells => ?_)
  refine finite_bind (finite_mapM _ (fun a => ?_) cells) (fun _ => finite_const _)
  exact finite_bind (B := fun rec => rec (.demandNeedRecursive a)) (finite_call _) (fun _ => finite_const _)

theorem finite_repeatDriver (step : ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) (name : String) :
    ∀ (n : Nat) (cells : List Nat), Finite (fun rec => repeatDriver step ctx env name rec n cells) := by
  intro n
  induction n with
  | zero => intro cells; exact finite_const _
  | succ n ih =>
    intro cells
    refine finite_bind (B := fun rec => rec (.invokeNeed step)) (finite_call _) (fun o => ?_)
    refine finite_bind (finite_const _) (fun alg => ?_)
    refine finite_bind (B := fun rec => rec (.runNeedStepSlots alg ctx env cells name)) (finite_call _) (fun ys => ?_)
    exact finite_bind (finite_const _) (fun next => ih next)

theorem finite_repeatTail (c : ResolvedArgumentAlgorithm) (bindings : NeedEnv) (ctx : EvalCtx) (env : ValEnv) :
    Finite (fun rec => repeatTail rec c bindings ctx env) := by
  unfold repeatTail
  refine finite_bind ?_ (fun x => ?_)
  · unfold metaRepeatSetup
    exact finite_bind (finite_loopCapture bindings) (fun _ =>
      finite_bind (finite_countDemand c bindings ctx env) (fun _ => finite_const _))
  · rcases x with ⟨⟨step, cells'⟩, n⟩
    dsimp only
    split
    · exact finite_const _
    · refine finite_bind (finite_const _) (fun name => ?_)
      exact finite_finishLoop _ (finite_repeatDriver step ctx env name _ _)

theorem finite_repeatBinding (c : ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) (o : Option NeedEnv) :
    Finite (fun rec => repeatBinding rec c ctx env o) := by
  cases o with
  | none => exact finite_const _
  | some bindings => exact finite_repeatTail c bindings ctx env

theorem finite_repeatBody (a c : ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) :
    Finite (fun rec => repeatBody rec a c ctx env) := by
  unfold repeatBody
  refine finite_bind (B := fun rec : EvalRec => [a, c].mapM (fun arg => rec.argumentNeed arg ctx env))
    (finite_mapM (fun (rec : EvalRec) arg => rec.argumentNeed arg ctx env)
      (fun arg => finite_call (.argumentNeed arg ctx env)) _) (fun cells => ?_)
  have hbind : (fun rec : EvalRec => bindNeedPatterns rec.bindingChannels
      ((builtinSignature .repeatBuiltin).map NeedPattern.ofParameter) cells) =
      fun _ => bindNeedPatterns bindingChannels ((builtinSignature .repeatBuiltin).map NeedPattern.ofParameter) cells :=
    funext fun rec => repeat_binder_channel_free _ _ cells
  have hf : Finite (fun rec : EvalRec => bindNeedPatterns rec.bindingChannels
      ((builtinSignature .repeatBuiltin).map NeedPattern.ofParameter) cells) := by
    rw [hbind]; exact finite_const _
  exact finite_bind hf (finite_repeatBinding c ctx env)

theorem finite_whileTail (bindings : NeedEnv) (ctx : EvalCtx) (env : ValEnv) :
    Finite (fun rec => whileTail rec bindings ctx env) := by
  unfold whileTail
  refine finite_bind (finite_loopCapture bindings) (fun x => ?_)
  rcases x with ⟨step, cells'⟩
  dsimp only
  refine finite_bind (finite_const _) (fun name => ?_)
  exact finite_finishLoop _ (finite_call _)

theorem finite_whileBinding (ctx : EvalCtx) (env : ValEnv) (o : Option NeedEnv) :
    Finite (fun rec => whileBinding rec ctx env o) := by
  cases o with
  | none => exact finite_const _
  | some bindings => exact finite_whileTail bindings ctx env

theorem finite_whileBody (a : ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) :
    Finite (fun rec => whileBody rec a ctx env) := by
  unfold whileBody
  refine finite_bind (B := fun rec : EvalRec => [a].mapM (fun arg => rec.argumentNeed arg ctx env))
    (finite_mapM (fun (rec : EvalRec) arg => rec.argumentNeed arg ctx env)
      (fun arg => finite_call (.argumentNeed arg ctx env)) _) (fun cells => ?_)
  have hbind : (fun rec : EvalRec => bindNeedPatterns rec.bindingChannels
      ((builtinSignature .whileBuiltin).map NeedPattern.ofParameter) cells) =
      fun _ => bindNeedPatterns bindingChannels ((builtinSignature .whileBuiltin).map NeedPattern.ofParameter) cells :=
    funext fun rec => while_binder_channel_free _ _ cells
  have hf : Finite (fun rec : EvalRec => bindNeedPatterns rec.bindingChannels
      ((builtinSignature .whileBuiltin).map NeedPattern.ofParameter) cells) := by
    rw [hbind]; exact finite_const _
  exact finite_bind hf (finite_whileBinding ctx env)

/-- **PRODUCTION BRIDGE of the `repeat` arm**: production completes exactly when its stages do. -/
theorem repeat_completes_iff (a c : ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) (s : EvalState) :
    ProductionCompletes (applyBuiltinCounted .repeatBuiltin [a, c] ctx env) s ↔
      ProductionCompletes (repeatBody evalUnbounded a c ctx env) s := by
  refine (production_completes_iff_body (.applyBuiltinCounted .repeatBuiltin [a, c] ctx env)
    (fun rec => withNestedMissingOutput (repeatBody rec a c ctx env)) (fun _ => rfl)
    (finite_nested (finite_repeatBody a c ctx env)) s).trans ?_
  unfold ProductionCompletes
  rw [show (withNestedMissingOutput (repeatBody evalUnbounded a c ctx env)).runState s =
    nestOutcome ((repeatBody evalUnbounded a c ctx env).runState s) from by
      rw [nested_run]; rcases (repeatBody evalUnbounded a c ctx env).runState s with ⟨_ | _, _⟩ <;> rfl]
  exact nestOutcome_fuel _

theorem repeat_arm_production (a c : ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) (s : EvalState)
    (hc : ProductionCompletes (repeatBody evalUnbounded a c ctx env) s) :
    (applyBuiltinCounted .repeatBuiltin [a, c] ctx env).runState s =
      nestOutcome ((repeatBody evalUnbounded a c ctx env).runState s) := by
  have hrun : (withNestedMissingOutput (repeatBody evalUnbounded a c ctx env)).runState s =
      nestOutcome ((repeatBody evalUnbounded a c ctx env).runState s) := by
    rw [nested_run]; rcases (repeatBody evalUnbounded a c ctx env).runState s with ⟨_ | _, _⟩ <;> rfl
  have hc' : ProductionCompletes (withNestedMissingOutput (repeatBody evalUnbounded a c ctx env)) s := by
    unfold ProductionCompletes; rw [hrun]; exact (nestOutcome_fuel _).2 hc
  exact (production_eq_of_finite (.applyBuiltinCounted .repeatBuiltin [a, c] ctx env)
    (fun rec => withNestedMissingOutput (repeatBody rec a c ctx env)) (fun _ => rfl)
    (finite_nested (finite_repeatBody a c ctx env)) s hc').trans hrun

/-- **PRODUCTION BRIDGE of the `while` arm.** -/
theorem while_completes_iff (a : ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) (s : EvalState) :
    ProductionCompletes (applyBuiltinCounted .whileBuiltin [a] ctx env) s ↔
      ProductionCompletes (whileBody evalUnbounded a ctx env) s := by
  refine (production_completes_iff_body (.applyBuiltinCounted .whileBuiltin [a] ctx env)
    (fun rec => withNestedMissingOutput (whileBody rec a ctx env)) (fun _ => rfl)
    (finite_nested (finite_whileBody a ctx env)) s).trans ?_
  unfold ProductionCompletes
  rw [show (withNestedMissingOutput (whileBody evalUnbounded a ctx env)).runState s =
    nestOutcome ((whileBody evalUnbounded a ctx env).runState s) from by
      rw [nested_run]; rcases (whileBody evalUnbounded a ctx env).runState s with ⟨_ | _, _⟩ <;> rfl]
  exact nestOutcome_fuel _

theorem while_arm_production (a : ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) (s : EvalState)
    (hc : ProductionCompletes (whileBody evalUnbounded a ctx env) s) :
    (applyBuiltinCounted .whileBuiltin [a] ctx env).runState s =
      nestOutcome ((whileBody evalUnbounded a ctx env).runState s) := by
  have hrun : (withNestedMissingOutput (whileBody evalUnbounded a ctx env)).runState s =
      nestOutcome ((whileBody evalUnbounded a ctx env).runState s) := by
    rw [nested_run]; rcases (whileBody evalUnbounded a ctx env).runState s with ⟨_ | _, _⟩ <;> rfl
  have hc' : ProductionCompletes (withNestedMissingOutput (whileBody evalUnbounded a ctx env)) s := by
    unfold ProductionCompletes; rw [hrun]; exact (nestOutcome_fuel _).2 hc
  exact (production_eq_of_finite (.applyBuiltinCounted .whileBuiltin [a] ctx env)
    (fun rec => withNestedMissingOutput (whileBody rec a ctx env)) (fun _ => rfl)
    (finite_nested (finite_whileBody a ctx env)) s hc').trans hrun

/-! ## 8. Final materialization and the post-setup theorems -/

/-- The loop's final boundary after a completed driver: an ordinary driver failure is the loop's
    failure and nothing is materialized; otherwise the final cells are demanded in order. -/
inductive Finished : Except Error (List Nat) → EvalState → Except Error CountedResult → EvalState → Prop
  | failed {e : Error} {t : EvalState} : Finished (.error e) t (.error e) t
  | materialized {final : List Nat} {t u : EvalState} {slots : List Result} :
      (materialize final).runState t = (.ok slots, u) →
      Finished (.ok final) t (.ok (loopResultCounted slots)) u
  | materializeFailed {final : List Nat} {t u : EvalState} {e : Error} :
      e ≠ .fuelExhausted → (materialize final).runState t = (.error e, u) →
      Finished (.ok final) t (.error e) u

theorem finish_iff (driver : EvalM (List Nat)) (s u : EvalState) (r : Except Error CountedResult) :
    ((finishLoop evalUnbounded driver).runState s = (r, u) ∧ r ≠ .error .fuelExhausted) ↔
      ∃ d t, (driver.runState s = (d, t) ∧ d ≠ .error .fuelExhausted) ∧ Finished d t r u := by
  have hrun : (finishLoop evalUnbounded driver).runState s =
      (match driver.runState s with
       | (.error e, t) => (.error e, t)
       | (.ok final, t) =>
         match (materialize final).runState t with
         | (.error e, v) => (.error e, v)
         | (.ok slots, v) => (.ok (loopResultCounted slots), v)) := by
    show (driver >>= fun fc => materialize fc >>= fun ys => pure (loopResultCounted ys)).runState s = _
    rw [EvalM.bind_runState]
    rcases driver.runState s with ⟨_ | fc, t⟩
    · rfl
    · simp only [EvalM.bind_runState]
      rcases (materialize fc).runState t with ⟨_ | _, _⟩ <;> rfl
  rw [hrun]
  constructor
  · rintro ⟨h, hr⟩
    rcases hd : driver.runState s with ⟨_ | fc, t⟩
    · rename_i e
      rw [hd] at h
      cases h
      exact ⟨_, _, ⟨rfl, error_ne_fuel hr⟩, .failed⟩
    · rw [hd] at h
      simp only at h
      rcases hm : (materialize fc).runState t with ⟨_ | ys, v⟩
      · rename_i e
        rw [hm] at h
        cases h
        exact ⟨_, _, ⟨rfl, nofun⟩, .materializeFailed (fun he => hr (by rw [he])) hm⟩
      · rw [hm] at h
        cases h
        exact ⟨_, _, ⟨rfl, nofun⟩, .materialized hm⟩
  · rintro ⟨d, t, ⟨hd, hne⟩, hf⟩
    rw [hd]
    cases hf with
    | failed => exact ⟨rfl, error_ne_fuel hne⟩
    | materialized hm => simp only [hm]; exact ⟨trivial, nofun⟩
    | materializeFailed he hm => simp only [hm]; exact ⟨trivial, fun h => he (by injection h)⟩

/-- **FINITE `repeat`, post-setup.** The real rounds and the final boundary, both directions. -/
theorem repeat_after_setup_iff (step : ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv)
    (name : String) (n : Nat) (cells : List Nat) (s u : EvalState) (r : Except Error CountedResult) :
    ((repeatAfterSetup evalUnbounded step ctx env name n cells).runState s = (r, u) ∧ r ≠ .error .fuelExhausted) ↔
      ∃ d t, RepeatTrace step ctx env name n cells s d t ∧ Finished d t r u := by
  unfold repeatAfterSetup
  rw [finish_iff]
  constructor
  · rintro ⟨d, t, hd, hf⟩
    exact ⟨d, t, (repeat_trace_iff step ctx env name n cells s t d).2 hd, hf⟩
  · rintro ⟨d, t, hd, hf⟩
    exact ⟨d, t, (repeat_trace_iff step ctx env name n cells s t d).1 hd, hf⟩

/-- **FINITE `while`, post-setup.** The real rounds and the final boundary, both directions. -/
theorem while_after_setup_iff (step : ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv)
    (name : String) (cells : List Nat) (s u : EvalState) (r : Except Error CountedResult) :
    ((whileAfterSetup evalUnbounded step ctx env name cells).runState s = (r, u) ∧ r ≠ .error .fuelExhausted) ↔
      ∃ k d t, WhileTrace step ctx env name k cells s d t ∧ Finished d t r u := by
  unfold whileAfterSetup
  rw [finish_iff]
  constructor
  · rintro ⟨d, t, hd, hf⟩
    obtain ⟨k, hk⟩ := (while_trace_iff step ctx env name cells s t d).2 hd
    exact ⟨k, d, t, hk, hf⟩
  · rintro ⟨k, d, t, hk, hf⟩
    exact ⟨d, t, (while_trace_iff step ctx env name cells s t d).1 ⟨k, hk⟩, hf⟩

/-- **COUNT ZERO.** No iteration: the step is not consulted at all. What remains is the final
    materialization of the initial cells, which can still demand and fail. -/
theorem repeat_zero (step : ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) (name : String)
    (cells : List Nat) (s : EvalState) :
    (repeatAfterSetup evalUnbounded step ctx env name 0 cells).runState s =
      (materialize cells >>= fun ys => pure (loopResultCounted ys)).runState s := by
  show (pure cells >>= fun fc => materialize fc >>= fun ys => pure (loopResultCounted ys)).runState s = _
  rw [EvalM.bind_runState]; rfl

theorem repeat_trace_zero (step : ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) (name : String)
    (cells : List Nat) (s t : EvalState) (r : Except Error (List Nat)) :
    RepeatTrace step ctx env name 0 cells s r t ↔ (r = .ok cells ∧ t = s) := by
  constructor
  · intro h; cases h; exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩; exact .done _ _

/-- The observable of a one-round `repeat` over one completed step supply. -/
def oneRoundOutcome : Except Error (List Result) × EvalState → Except Error CountedResult × EvalState
  | (.ok ys, t) => (.ok (loopResultCounted ys), pushCompleted t ys)
  | (.error e, t) => (.error e, t)

/-- **COUNT ONE, THE REAL SEQUENCE.** From a retained step projected to `alg`: ONE invocation over
    the ORIGINAL cells (`runNeedStepSlots`, whatever the callable category), the emitted slots
    allocated as the next Ready cells in order, those cells materialized, and the loop's counted
    value. The final state is the step's state with one COMPLETED Ready cell per slot appended;
    every other field is unchanged. -/
theorem repeat_one_round (step : ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) (name : String)
    (cells : List Nat) (s s₁ : EvalState) (alg : Algorithm)
    (hi : (invokeNeed step).runState s = (.ok (some alg), s₁)) :
    (repeatAfterSetup evalUnbounded step ctx env name 1 cells).runState s =
      oneRoundOutcome ((runNeedStepSlots alg ctx env cells name).runState s₁) := by
  have hdriver : (repeatDriver step ctx env name evalUnbounded 1 cells).runState s =
      (match (runNeedStepSlots alg ctx env cells name).runState s₁ with
       | (.error e, t) => (.error e, t)
       | (.ok ys, s₂) => (.ok (readyAddrs s₂.needs.size ys), pushReady s₂ ys)) := by
    rw [repeatDriver_succ, EvalM.bind_runState, repeatRound_run]
    simp only [EvalRec.invokeNeed, EvalRec.runNeedStepSlots]
    rw [show evalUnbounded (.invokeNeed step) = invokeNeed step from rfl, hi]
    simp only
    rw [show evalUnbounded (.runNeedStepSlots alg ctx env cells name) = runNeedStepSlots alg ctx env cells name from rfl]
    rcases (runNeedStepSlots alg ctx env cells name).runState s₁ with ⟨_ | ys, s₂⟩ <;> rfl
  show (repeatDriver step ctx env name evalUnbounded 1 cells >>= fun fc =>
    materialize fc >>= fun ys => pure (loopResultCounted ys)).runState s = _
  rw [EvalM.bind_runState, hdriver]
  rcases (runNeedStepSlots alg ctx env cells name).runState s₁ with ⟨_ | ys, s₂⟩
  · rfl
  · simp only [EvalM.bind_runState]
    rw [materialize_ready ys s₂.needs (pushReady s₂ ys) rfl]
    rfl

/-- The two value observations agree exactly on canonical slots. -/
theorem loop_value_of_canonical (ys : List Result) (h : ∀ y ∈ ys, y.normalize = y) :
    loopResultCounted ys = ordinaryValue ys := by
  have hmap : ys.map Result.normalize = ys := by
    induction ys with
    | nil => rfl
    | cons y rest ih =>
      simp only [List.map_cons, h y (by simp), ih (fun z hz => h z (by simp [hz]))]
  have hv : loopStateResult ys = combineOutputSlots ys := by
    unfold loopStateResult
    rw [_root_.normalize_sequenceValue_eq_combineOutputSlots_map_normalize, hmap]
  simp only [loopResultCounted, ordinaryValue, reCountValueBoundary, hv]

/-- A noncanonical host-built slot: the one-iteration loop normalizes it, the ordinary call keeps it.
    The unrestricted equality `Step(args).repeat(1) = Step(args)` is therefore FALSE as a theorem
    over arbitrary `Result`s; surface programs never build this value. -/
theorem noncanonical_counterexample :
    loopResultCounted [.sequenceValue [.atom 1]] ≠ ordinaryValue [.sequenceValue [.atom 1]] := by
  simp [loopResultCounted, loopStateResult, ordinaryValue, Result.normalize, combineOutputSlots,
    reCountValueBoundary]

/-- **COUNT ONE AGAINST THE ORDINARY USER CALL.** Over the same supply and from the same state:
    the round and the call complete together and reach the same state on the step; the
    `repeat` completes with the slots' `loopResultCounted`, its final heap being the call's plus
    the completed slot cells; on canonical slots the counted values are EQUAL. -/
theorem count_one_user (step : ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) (name : String)
    (cells : List Nat) (s s₁ : EvalState) (a : Algorithm)
    (hi : (invokeNeed step).runState s = (.ok (some a), s₁)) (h : UserStep a)
    (hrows : UserRowsBounded a ctx env cells s₁) :
    StepAgreement id ((runNeedStepSlots a ctx env cells name).runState s₁)
      ((evalNeedUserSupply a cells ctx env).runState s₁) ∧
    (repeatAfterSetup evalUnbounded step ctx env name 1 cells).runState s =
      oneRoundOutcome ((runNeedStepSlots a ctx env cells name).runState s₁) :=
  ⟨user_step_agreement a h ctx env cells name s₁ hrows, repeat_one_round step ctx env name cells s s₁ a hi⟩

/-- **COUNT ONE AGAINST THE ORDINARY FAMILY CALL.** -/
theorem count_one_family (step : ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) (name : String)
    (cells : List Nat) (s s₁ : EvalState) (p : Option ScopeCtx) (o : List Expr) (br : List CondBranch)
    (d : Option PropertyIdentity)
    (hi : (invokeNeed step).runState s = (.ok (some (.conditional p o br d)), s₁))
    (hrows : FamilyRowsBounded (.conditional p o br d) ctx env cells name s₁) :
    StepAgreement (Error.withContext s!"while evaluating call to {name}")
      ((runNeedStepSlots (.conditional p o br d) ctx env cells name).runState s₁)
      ((evalNeedFamilySupply (.conditional p o br d) cells ctx env name).runState s₁) ∧
    (repeatAfterSetup evalUnbounded step ctx env name 1 cells).runState s =
      oneRoundOutcome ((runNeedStepSlots (.conditional p o br d) ctx env cells name).runState s₁) :=
  ⟨family_step_agreement p o br d ctx env cells name s₁ hrows,
    repeat_one_round step ctx env name cells s s₁ _ hi⟩

/-! ## 9. The real setup at `applyBuiltinCounted` -/

/-- The state the META binding leaves: the one Ready adapter. -/
def adapterPushed (s : EvalState) (plan : Nat) : EvalState :=
  { s with needs := s.needs.push (CallReferenceLaws.adapterCell plan) }

/-- The state after the capture read the adapter. -/
def adapterRead (s : EvalState) (plan : Nat) : EvalState :=
  { adapterPushed s plan with
    needs := evaluatedAt (adapterPushed s plan).needs s.needs.size (.callRef plan, 1) }

theorem argumentNeed_cell (arg : ResolvedArgumentAlgorithm) (p : Nat) (h : arg.need? = some p)
    (ctx : EvalCtx) (env : ValEnv) (s : EvalState) :
    (evalUnbounded (.argumentNeed arg ctx env)).runState s = (.ok p, s) := by
  refine production_of_answer_free (.argumentNeed arg ctx env) s _ (fun rec => ?_) nofun
  show (EvalBody.argumentNeed rec arg ctx env).runState s = _
  simp only [EvalBody.argumentNeed, h]
  rfl

theorem repeat_binder_run (ch : NeedChannels) (p c : Nat) (s : EvalState) (shape : NeedPlan.CallShape)
    (h : NeedPlan.shapeAt? s.needs p = some shape) :
    (bindNeedPatterns ch ((builtinSignature .repeatBuiltin).map NeedPattern.ofParameter) [p, c]).runState s =
      (.ok (some [("step", s.needs.size), ("count", c)]), adapterPushed s p) := by
  rw [KatLang.MetaLoopLaws.repeat_binding_patterns]
  have hm := CallReferenceLaws.production_meta_binding ch "step" p [] {} false s shape h rfl
  simp only [bindNeedOne] at hm
  simp only [bindNeedPatterns, NeedBinder.bindPatterns, NeedBinder.bindLevel, repeatNames,
    EvalM.bind_runState]
  have hgate : ∀ (X : EvalM (Option NeedBindState)),
      NeedBinder.cardinalityGate [NeedPattern.metaRef "step", NeedPattern.bind "count"] [p, c].length false X = X :=
    fun _ => rfl
  have hsrc : needLevelSources [NeedPattern.metaRef "step", NeedPattern.bind "count"] [p, c] =
      [.cell p, .cell c] := rfl
  rw [hgate, hsrc]
  have hrun : (NeedBinder.bindSources ch.capabilities [NeedPattern.metaRef "step", NeedPattern.bind "count"]
      [.cell p, .cell c] [] {} false).runState s =
      (.ok (some ((({} : NeedBindState).withPlain "step" s.needs.size).withPlain "count" c)), adapterPushed s p) := by
    simp only [NeedBinder.bindSources, EvalM.bind_runState]
    rw [show (NeedBinder.sourceAddress ch.capabilities.allocate _).runState s = (.ok p, s) from rfl]
    dsimp only
    rw [hm]
    rfl
  rw [hrun]
  have hbound : (((({} : NeedBindState).withPlain "step" s.needs.size).withPlain "count" c)).bound =
      [("step", s.needs.size), ("count", c)] := by
    simp [NeedBindState.withPlain, NeedEnv.rebind]
  simp only [pure_runState, Option.map, hbound]

theorem while_binder_run (ch : NeedChannels) (p : Nat) (s : EvalState) (shape : NeedPlan.CallShape)
    (h : NeedPlan.shapeAt? s.needs p = some shape) :
    (bindNeedPatterns ch ((builtinSignature .whileBuiltin).map NeedPattern.ofParameter) [p]).runState s =
      (.ok (some [("step", s.needs.size)]), adapterPushed s p) := by
  rw [KatLang.MetaLoopLaws.while_binding_patterns]
  have hm := CallReferenceLaws.production_meta_binding ch "step" p [] {} false s shape h rfl
  simp only [bindNeedOne] at hm
  simp only [bindNeedPatterns, NeedBinder.bindPatterns, NeedBinder.bindLevel, whileNames,
    EvalM.bind_runState]
  have hgate : ∀ (X : EvalM (Option NeedBindState)),
      NeedBinder.cardinalityGate [NeedPattern.metaRef "step"] [p].length false X = X :=
    fun _ => rfl
  have hsrc : needLevelSources [NeedPattern.metaRef "step"] [p] = [.cell p] := rfl
  rw [hgate, hsrc]
  have hrun : (NeedBinder.bindSources ch.capabilities [NeedPattern.metaRef "step"] [.cell p] [] {} false).runState s =
      (.ok (some (({} : NeedBindState).withPlain "step" s.needs.size)), adapterPushed s p) := by
    simp only [NeedBinder.bindSources, EvalM.bind_runState]
    rw [show (NeedBinder.sourceAddress ch.capabilities.allocate _).runState s = (.ok p, s) from rfl]
    dsimp only
    rw [hm]
    rfl
  rw [hrun]
  have hbound : (({} : NeedBindState).withPlain "step" s.needs.size).bound = [("step", s.needs.size)] := by
    simp [NeedBindState.withPlain, NeedEnv.rebind]
  simp only [pure_runState, Option.map, hbound]


theorem adapter_read (s : EvalState) (plan : Nat) :
    (demandNeedRecursive s.needs.size).runState (adapterPushed s plan) =
      (.ok (.callRef plan, 1), adapterRead s plan) :=
  demand_ready _ _ (CallReferenceLaws.adapterCell plan) _ (by simp [adapterPushed]) rfl rfl

/-- The captured supply and canonical callee, as production runs from the state after the adapter
    read. Establishing them may run the captured spreads; nothing else. -/
structure CaptureRun (plan : Nat) (s₁ s₂ s₃ : EvalState) (sourced : List NeedSupply.Sourced)
    (stepCell : Nat) : Prop where
  view : (argumentViewCells plan).runState s₁ = (.ok sourced, s₂)
  callee : (NeedPlan.calleeCell productionPlanRoute.classify plan).runState s₂ = (.ok stepCell, s₃)

theorem boundCell_run (bindings : NeedEnv) (name : Ident) (a : Nat) (s : EvalState)
    (h : lookupAssoc name bindings = some a) : (boundCell bindings name).runState s = (.ok a, s) := by
  simp only [boundCell, h]; rfl

/-- The arms' capture at production: the adapter read, then the plan's sticky supply, then the
    canonical callee cell (the installation of `metaLoopCapture`). -/
theorem capture_run (bindings : NeedEnv) (s s₂ s₃ : EvalState) (plan stepCell : Nat)
    (sourced : List NeedSupply.Sourced) (hb : lookupAssoc "step" bindings = some s.needs.size)
    (hc : CaptureRun plan (adapterRead s plan) s₂ s₃ sourced stepCell) :
    (loopCapture evalUnbounded bindings).runState (adapterPushed s plan) =
      (.ok (stepArgument stepCell, sourced.map Prod.fst), s₃) := by
  unfold loopCapture
  rw [EvalM.bind_runState, boundCell_run bindings "step" s.needs.size _ hb]
  simp only [EvalM.bind_runState]
  have hm := KatLang.MetaLoopLaws.metaLoopCapture_run (EvalRec.planRoute evalUnbounded).classify
    (EvalRec.demandNeedRecursive evalUnbounded) (EvalRec.argumentViewCells evalUnbounded) s.needs.size plan 1
    sourced (adapterPushed s plan) (adapterRead s plan) s₂ (adapter_read s plan) hc.view
  rw [hm, show (NeedPlan.calleeCell (EvalRec.planRoute evalUnbounded).classify plan).runState s₂ = _ from hc.callee]
  rfl

/-- A captured supply failure at the arms: it is the capture's failure, in its retained state. -/
theorem capture_view_fails (bindings : NeedEnv) (s t : EvalState) (plan : Nat) (e : Error)
    (hb : lookupAssoc "step" bindings = some s.needs.size)
    (hv : (argumentViewCells plan).runState (adapterRead s plan) = (.error e, t)) :
    (loopCapture evalUnbounded bindings).runState (adapterPushed s plan) = (.error e, t) := by
  unfold loopCapture
  rw [EvalM.bind_runState, boundCell_run bindings "step" s.needs.size _ hb]
  simp only [EvalM.bind_runState]
  have hm : (metaLoopCapture (EvalRec.planRoute evalUnbounded).classify (EvalRec.demandNeedRecursive evalUnbounded)
      (EvalRec.argumentViewCells evalUnbounded) s.needs.size).runState (adapterPushed s plan) = (.error e, t) := by
    simp only [metaLoopCapture, EvalM.bind_runState]
    rw [show (EvalRec.demandNeedRecursive evalUnbounded s.needs.size).runState (adapterPushed s plan) = _ from
      adapter_read s plan]
    simp only [decodeCallRef, pure_runState]
    rw [show (EvalRec.argumentViewCells evalUnbounded plan).runState (adapterRead s plan) = _ from hv]
  rw [hm]

/-- The `repeat` arm's setup prefix at production, for cell-backed arguments of a captured call. -/
structure RepeatPrefix (a c : ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) (plan cnt : Nat)
    (s : EvalState) : Prop where
  stepNeed : a.need? = some plan
  countNeed : c.need? = some cnt
  isPlan : ∃ shape, NeedPlan.shapeAt? s.needs plan = some shape

/-- The binding the `repeat` arm forms. -/
def repeatBindings (s : EvalState) (cnt : Nat) : NeedEnv := [("step", s.needs.size), ("count", cnt)]

theorem repeat_body_prefix (a c : ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) (plan cnt : Nat)
    (s : EvalState) (h : RepeatPrefix a c ctx env plan cnt s) :
    (repeatBody evalUnbounded a c ctx env).runState s =
      (repeatTail evalUnbounded c (repeatBindings s cnt) ctx env).runState (adapterPushed s plan) := by
  obtain ⟨shape, hshape⟩ := h.isPlan
  unfold repeatBody
  rw [EvalM.bind_runState, KatLang.NeedControl.Schedule.mapM_schedule]
  simp only [KatLang.NeedControl.Schedule.schedule]
  rw [show (EvalRec.argumentNeed evalUnbounded a ctx env).runState s = (.ok plan, s) from
      argumentNeed_cell a plan h.stepNeed ctx env s]
  dsimp only
  rw [show (EvalRec.argumentNeed evalUnbounded c ctx env).runState s = (.ok cnt, s) from
      argumentNeed_cell c cnt h.countNeed ctx env s]
  simp only [EvalM.bind_runState]
  rw [repeat_binder_run (EvalRec.bindingChannels evalUnbounded) plan cnt s shape hshape]
  rfl

theorem repeat_tail_capture_fails (c : ResolvedArgumentAlgorithm) (bindings : NeedEnv) (ctx : EvalCtx)
    (env : ValEnv) (s t : EvalState) (e : Error)
    (h : (loopCapture evalUnbounded bindings).runState s = (.error e, t)) :
    (repeatTail evalUnbounded c bindings ctx env).runState s = (.error e, t) := by
  unfold repeatTail
  rw [EvalM.bind_runState, KatLang.MetaLoopLaws.repeat_setup_failure_skips_count _ _ s t e h]

/-- The captured supply's failure precedes the count: nothing of the count is demanded. -/
theorem repeat_capture_failure (a c : ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) (plan cnt : Nat)
    (s t : EvalState) (e : Error) (he : e ≠ .fuelExhausted) (h : RepeatPrefix a c ctx env plan cnt s)
    (hv : (argumentViewCells plan).runState (adapterRead s plan) = (.error e, t)) :
    (applyBuiltinCounted .repeatBuiltin [a, c] ctx env).runState s = (.error e.nestMissingOutput, t) := by
  have hbody : (repeatBody evalUnbounded a c ctx env).runState s = (.error e, t) := by
    rw [repeat_body_prefix a c ctx env plan cnt s h]
    exact repeat_tail_capture_fails c _ ctx env _ t e (capture_view_fails _ s t plan e rfl hv)
  rw [repeat_arm_production a c ctx env s (by
    unfold ProductionCompletes; rw [hbody]; intro h'; apply he; injection h'), hbody]
  rfl

theorem repeat_tail_capture_ok (c : ResolvedArgumentAlgorithm) (bindings : NeedEnv) (ctx : EvalCtx)
    (env : ValEnv) (s s₃ : EvalState) (step : ResolvedArgumentAlgorithm) (cells : List Nat)
    (h : (loopCapture evalUnbounded bindings).runState s = (.ok (step, cells), s₃)) :
    (repeatTail evalUnbounded c bindings ctx env).runState s =
      (match (countDemand evalUnbounded c bindings ctx env).runState s₃ with
       | (.error e, t) => (.error e, t)
       | (.ok n, s₄) =>
         if n < 0 then (.error (Error.illegalInEval "Repeat count must be >= 0"), s₄)
         else
           (loopStepName "repeat" step >>= fun name =>
             repeatAfterSetup evalUnbounded step ctx env name n.toNat cells).runState s₄) := by
  unfold repeatTail
  rw [EvalM.bind_runState, KatLang.MetaLoopLaws.repeat_setup_order, h]
  dsimp only
  rcases (countDemand evalUnbounded c bindings ctx env).runState s₃ with ⟨_ | n, s₄⟩
  · rfl
  · dsimp only
    by_cases hn : n < 0
    · simp only [hn, if_true]; rfl
    · simp only [hn, if_false]

/-- A count failure happens after the capture, before any iteration. -/
theorem repeat_count_failure (a c : ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) (plan cnt stepCell : Nat)
    (s s₂ s₃ t : EvalState) (sourced : List NeedSupply.Sourced) (e : Error) (he : e ≠ .fuelExhausted)
    (h : RepeatPrefix a c ctx env plan cnt s) (hc : CaptureRun plan (adapterRead s plan) s₂ s₃ sourced stepCell)
    (hcount : (countDemand evalUnbounded c (repeatBindings s cnt) ctx env).runState s₃ = (.error e, t)) :
    (applyBuiltinCounted .repeatBuiltin [a, c] ctx env).runState s = (.error e.nestMissingOutput, t) := by
  have hbody : (repeatBody evalUnbounded a c ctx env).runState s = (.error e, t) := by
    rw [repeat_body_prefix a c ctx env plan cnt s h,
      repeat_tail_capture_ok c _ ctx env _ s₃ _ _ (capture_run _ s s₂ s₃ plan stepCell sourced rfl hc), hcount]
  rw [repeat_arm_production a c ctx env s (by
    unfold ProductionCompletes; rw [hbody]; intro h'; apply he; injection h'), hbody]
  rfl

/-- A negative count fails after setup and count validation: no step projection, no iteration, no
    final materialization. -/
theorem repeat_negative_count (a c : ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) (plan cnt stepCell : Nat)
    (s s₂ s₃ s₄ : EvalState) (sourced : List NeedSupply.Sourced) (n : Int) (hn : n < 0)
    (h : RepeatPrefix a c ctx env plan cnt s) (hc : CaptureRun plan (adapterRead s plan) s₂ s₃ sourced stepCell)
    (hcount : (countDemand evalUnbounded c (repeatBindings s cnt) ctx env).runState s₃ = (.ok n, s₄)) :
    (applyBuiltinCounted .repeatBuiltin [a, c] ctx env).runState s =
      (.error (Error.illegalInEval "Repeat count must be >= 0"), s₄) := by
  have hbody : (repeatBody evalUnbounded a c ctx env).runState s =
      (.error (Error.illegalInEval "Repeat count must be >= 0"), s₄) := by
    rw [repeat_body_prefix a c ctx env plan cnt s h,
      repeat_tail_capture_ok c _ ctx env _ s₃ _ _ (capture_run _ s s₂ s₃ plan stepCell sourced rfl hc), hcount]
    simp only [hn, if_true]
  rw [repeat_arm_production a c ctx env s (by unfold ProductionCompletes; rw [hbody]; nofun), hbody]
  rfl

/-- The `repeat` arm's complete successful setup. -/
structure RepeatSetup (a c : ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) (plan cnt : Nat)
    (s s₂ s₃ s₄ : EvalState) (sourced : List NeedSupply.Sourced) (stepCell : Nat) (n : Int) (name : String) : Prop
    extends RepeatPrefix a c ctx env plan cnt s where
  capture : CaptureRun plan (adapterRead s plan) s₂ s₃ sourced stepCell
  count : (countDemand evalUnbounded c (repeatBindings s cnt) ctx env).runState s₃ = (.ok n, s₄)
  nonnegative : 0 ≤ n
  stepName : (loopStepName "repeat" (stepArgument stepCell)).runState s₄ = (.ok name, s₄)

/-- **THE `repeat` SETUP IS INSTALLED.** Binding, capture, count and step name at the real builtin
    arm reach exactly the reusable post-setup theorem. -/
theorem repeat_setup_stages {a c : ResolvedArgumentAlgorithm} {ctx : EvalCtx} {env : ValEnv} {plan cnt : Nat}
    {s s₂ s₃ s₄ : EvalState} {sourced : List NeedSupply.Sourced} {stepCell : Nat} {n : Int} {name : String}
    (h : RepeatSetup a c ctx env plan cnt s s₂ s₃ s₄ sourced stepCell n name) :
    (repeatBody evalUnbounded a c ctx env).runState s =
      (repeatAfterSetup evalUnbounded (stepArgument stepCell) ctx env name n.toNat (sourced.map Prod.fst)).runState s₄ := by
  rw [repeat_body_prefix a c ctx env plan cnt s h.toRepeatPrefix,
    repeat_tail_capture_ok c _ ctx env _ s₃ _ _ (capture_run _ s s₂ s₃ plan stepCell sourced rfl h.capture), h.count]
  simp only [Int.not_lt.2 h.nonnegative, if_false, EvalM.bind_runState, h.stepName]

/-- Moving a post-setup result through the arm's outer boundary, with completion transfer. -/
theorem arm_transfer {P Body After : EvalM CountedResult} {s s₄ : EvalState}
    (hiff : ProductionCompletes P s ↔ ProductionCompletes Body s)
    (harm : ProductionCompletes Body s → P.runState s = nestOutcome (Body.runState s))
    (hst : Body.runState s = After.runState s₄) (r : Except Error CountedResult) (u : EvalState) :
    (P.runState s = (r, u) ∧ r ≠ .error .fuelExhausted) ↔
      ∃ r₀, (After.runState s₄ = (r₀, u) ∧ r₀ ≠ .error .fuelExhausted) ∧ nestOutcome (r₀, u) = (r, u) := by
  constructor
  · rintro ⟨hp, hr⟩
    have hpc : ProductionCompletes P s := by unfold ProductionCompletes; rw [hp]; exact hr
    have hbc := hiff.1 hpc
    have hn := harm hbc
    rw [hp] at hn
    unfold ProductionCompletes at hbc
    rw [hst] at hn hbc
    rcases hrun : After.runState s₄ with ⟨r₀, v⟩
    rw [hrun] at hn hbc
    cases r₀ with
    | ok x => cases hn; exact ⟨_, ⟨rfl, nofun⟩, rfl⟩
    | error e => cases hn; exact ⟨_, ⟨rfl, hbc⟩, rfl⟩
  · rintro ⟨r₀, ⟨ha, hr₀⟩, hn⟩
    have hbc : ProductionCompletes Body s := by unfold ProductionCompletes; rw [hst, ha]; exact hr₀
    rw [harm hbc, hst, ha, hn]
    refine ⟨rfl, ?_⟩
    have := (nestOutcome_fuel (r₀, u)).2 hr₀
    rw [hn] at this
    exact this

/-- **THE PUBLIC FINITE `repeat` THEOREM.** From a completed setup of the real builtin, production
    `repeat` over `n` rounds completes with `(r, u)` EXACTLY when the finite derivation over the
    real cells and the final boundary do, the outcome crossing the arm's nesting boundary. -/
theorem repeat_builtin_iff {a c : ResolvedArgumentAlgorithm} {ctx : EvalCtx} {env : ValEnv} {plan cnt : Nat}
    {s s₂ s₃ s₄ : EvalState} {sourced : List NeedSupply.Sourced} {stepCell : Nat} {n : Int} {name : String}
    (h : RepeatSetup a c ctx env plan cnt s s₂ s₃ s₄ sourced stepCell n name)
    (r : Except Error CountedResult) (u : EvalState) :
    ((applyBuiltinCounted .repeatBuiltin [a, c] ctx env).runState s = (r, u) ∧ r ≠ .error .fuelExhausted) ↔
      ∃ r₀ d t, RepeatTrace (stepArgument stepCell) ctx env name n.toNat (sourced.map Prod.fst) s₄ d t ∧
        Finished d t r₀ u ∧ nestOutcome (r₀, u) = (r, u) := by
  rw [arm_transfer (repeat_completes_iff a c ctx env s) (repeat_arm_production a c ctx env s)
    (repeat_setup_stages h) r u]
  constructor
  · rintro ⟨r₀, hrun, hn⟩
    obtain ⟨d, t, ht, hf⟩ := (repeat_after_setup_iff _ ctx env name _ _ s₄ u r₀).1 hrun
    exact ⟨r₀, d, t, ht, hf, hn⟩
  · rintro ⟨r₀, d, t, ht, hf, hn⟩
    exact ⟨r₀, (repeat_after_setup_iff _ ctx env name _ _ s₄ u r₀).2 ⟨d, t, ht, hf⟩, hn⟩

/-- **THE PUBLIC COUNT-ONE THEOREM.** `repeat(Step(args), 1)` at the real builtin, against the
    ordinary user call over the captured supply from the projected state: they complete
    together. A success is `loopResultCounted` of the row supply over the call's final state with
    the completed slot cells appended, and the call's value is `ordinaryValue` of the same
    supply; a failure is the SAME error and state on both sides. -/
theorem repeat_builtin_count_one {a c : ResolvedArgumentAlgorithm} {ctx : EvalCtx} {env : ValEnv}
    {plan cnt : Nat} {s s₂ s₃ s₄ s₅ : EvalState} {sourced : List NeedSupply.Sourced} {stepCell : Nat}
    {name : String} {alg : Algorithm}
    (h : RepeatSetup a c ctx env plan cnt s s₂ s₃ s₄ sourced stepCell 1 name)
    (hi : (invokeNeed (stepArgument stepCell)).runState s₄ = (.ok (some alg), s₅))
    (hd : UserStep alg) (hrows : UserRowsBounded alg ctx env (sourced.map Prod.fst) s₅) :
    let L := (runNeedStepSlots alg ctx env (sourced.map Prod.fst) name).runState s₅
    let O := (evalNeedUserSupply alg (sourced.map Prod.fst) ctx env).runState s₅
    (ProductionCompletes (applyBuiltinCounted .repeatBuiltin [a, c] ctx env) s ↔
      O.1 ≠ .error .fuelExhausted) ∧
    (∀ ys t, L = (.ok ys, t) →
      (applyBuiltinCounted .repeatBuiltin [a, c] ctx env).runState s =
        (.ok (loopResultCounted ys), pushCompleted t ys) ∧ O = (.ok (ordinaryValue ys), t)) ∧
    (∀ e t, e ≠ .fuelExhausted → L = (.error e, t) →
      (applyBuiltinCounted .repeatBuiltin [a, c] ctx env).runState s = (.error e.nestMissingOutput, t) ∧
        O = (.error e.nestMissingOutput, t)) := by
  intro L O
  obtain ⟨hag, hone⟩ := count_one_user (stepArgument stepCell) ctx env name _ s₄ s₅ alg hi hd hrows
  have hbody : (repeatBody evalUnbounded a c ctx env).runState s = oneRoundOutcome L := by
    rw [repeat_setup_stages h]; exact hone
  have hLone : (oneRoundOutcome L).1 ≠ .error .fuelExhausted ↔ L.1 ≠ .error .fuelExhausted := by
    rcases L with ⟨_ | _, _⟩
    · exact ⟨error_ne_fuel, error_ne_fuel⟩
    · exact iff_of_true nofun nofun
  refine ⟨?_, ?_, ?_⟩
  · refine (repeat_completes_iff a c ctx env s).trans ?_
    unfold ProductionCompletes
    rw [hbody]
    exact hLone.trans hag.completes
  · intro ys t hL
    have hc : ProductionCompletes (repeatBody evalUnbounded a c ctx env) s := by
      unfold ProductionCompletes; rw [hbody, hL]; nofun
    refine ⟨?_, hag.ok ys t hL⟩
    rw [repeat_arm_production a c ctx env s hc, hbody, hL]
    rfl
  · intro e t he hL
    have hc : ProductionCompletes (repeatBody evalUnbounded a c ctx env) s := by
      unfold ProductionCompletes; rw [hbody, hL]; intro h'; apply he; injection h'
    obtain ⟨e₀, rfl, hO⟩ := hag.error e t he hL
    refine ⟨?_, hO⟩
    rw [repeat_arm_production a c ctx env s hc, hbody, hL]
    rfl

/-- The `while` arm's complete successful setup. -/
structure WhileSetup (a : ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) (plan : Nat)
    (s s₂ s₃ : EvalState) (sourced : List NeedSupply.Sourced) (stepCell : Nat) (name : String) : Prop where
  stepNeed : a.need? = some plan
  isPlan : ∃ shape, NeedPlan.shapeAt? s.needs plan = some shape
  capture : CaptureRun plan (adapterRead s plan) s₂ s₃ sourced stepCell
  stepName : (loopStepName "while" (stepArgument stepCell)).runState s₃ = (.ok name, s₃)

/-- **THE `while` SETUP IS INSTALLED.** -/
theorem while_setup_stages {a : ResolvedArgumentAlgorithm} {ctx : EvalCtx} {env : ValEnv} {plan : Nat}
    {s s₂ s₃ : EvalState} {sourced : List NeedSupply.Sourced} {stepCell : Nat} {name : String}
    (h : WhileSetup a ctx env plan s s₂ s₃ sourced stepCell name) :
    (whileBody evalUnbounded a ctx env).runState s =
      (whileAfterSetup evalUnbounded (stepArgument stepCell) ctx env name (sourced.map Prod.fst)).runState s₃ := by
  obtain ⟨shape, hshape⟩ := h.isPlan
  unfold whileBody
  rw [EvalM.bind_runState, KatLang.NeedControl.Schedule.mapM_schedule]
  simp only [KatLang.NeedControl.Schedule.schedule]
  rw [show (EvalRec.argumentNeed evalUnbounded a ctx env).runState s = (.ok plan, s) from
      argumentNeed_cell a plan h.stepNeed ctx env s]
  simp only [EvalM.bind_runState]
  rw [while_binder_run (EvalRec.bindingChannels evalUnbounded) plan s shape hshape]
  show (whileTail evalUnbounded [("step", s.needs.size)] ctx env).runState (adapterPushed s plan) = _
  unfold whileTail
  rw [EvalM.bind_runState, capture_run _ s s₂ s₃ plan stepCell sourced rfl h.capture]
  simp only [EvalM.bind_runState, h.stepName]

/-- **THE PUBLIC FINITE `while` THEOREM.** From a completed setup of the real builtin, production
    `while` completes with `(r, u)` EXACTLY when a finite derivation — false after finite accepted
    transitions, or an ordinary error after a finite prefix — and the final boundary do. -/
theorem while_builtin_iff {a : ResolvedArgumentAlgorithm} {ctx : EvalCtx} {env : ValEnv} {plan : Nat}
    {s s₂ s₃ : EvalState} {sourced : List NeedSupply.Sourced} {stepCell : Nat} {name : String}
    (h : WhileSetup a ctx env plan s s₂ s₃ sourced stepCell name)
    (r : Except Error CountedResult) (u : EvalState) :
    ((applyBuiltinCounted .whileBuiltin [a] ctx env).runState s = (r, u) ∧ r ≠ .error .fuelExhausted) ↔
      ∃ r₀ k d t, WhileTrace (stepArgument stepCell) ctx env name k (sourced.map Prod.fst) s₃ d t ∧
        Finished d t r₀ u ∧ nestOutcome (r₀, u) = (r, u) := by
  rw [arm_transfer (while_completes_iff a ctx env s) (while_arm_production a ctx env s)
    (while_setup_stages h) r u]
  constructor
  · rintro ⟨r₀, hrun, hn⟩
    obtain ⟨k, d, t, ht, hf⟩ := (while_after_setup_iff _ ctx env name _ s₃ u r₀).1 hrun
    exact ⟨r₀, k, d, t, ht, hf, hn⟩
  · rintro ⟨r₀, k, d, t, ht, hf, hn⟩
    exact ⟨r₀, (while_after_setup_iff _ ctx env name _ s₃ u r₀).2 ⟨k, d, t, ht, hf⟩, hn⟩

/-- A stopping round retains the cells that ENTERED it: a zero-transition `while` finishes with
    its initial cells, and the state is the false round's, not the entry state. -/
theorem while_false_first (step : ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) (name : String)
    (cells : List Nat) (s s₁ t : EvalState) (alg : Algorithm)
    (hi : (invokeNeed step).runState s = (.ok (some alg), s₁))
    (hr : (runNeedWhileRound alg ctx env cells name).runState s₁ = (.ok none, t)) :
    (whileDriver step ctx env name cells).runState s = (.ok cells, t) :=
  (while_of_trace step ctx env name (.stop hi hr)).1

/-! ## 10. Retained effects -/

/-- What every step of a loop keeps: each earlier cell's suspension, completed VALUE, prepared
    supply and route (`HeapKept`), its completed CALLABLE and recorded links (`LinkHeapKept`), and
    every published property entry (`CacheKept`). -/
structure Retained (s t : EvalState) : Prop where
  heap : KatLang.CallPlan.HeapKept s.needs t.needs
  links : KatLang.MemoLinks.LinkHeapKept s.needs t.needs
  cache : KatLang.EvaluatorCacheLaws.CacheKept s t

theorem Retained.refl (s : EvalState) : Retained s s :=
  ⟨KatLang.CallPlan.HeapKept.refl _, KatLang.MemoLinks.LinkHeapKept.refl _, fun _ _ h => h⟩

theorem Retained.trans {s t u : EvalState} (h₁ : Retained s t) (h₂ : Retained t u) : Retained s u :=
  ⟨h₁.heap.trans h₂.heap, h₁.links.trans h₂.links, fun k v hl => h₂.cache k v (h₁.cache k v hl)⟩

theorem Retained.ofRun (c : EvalCall) {s t : EvalState} {o : Except Error c.Ret}
    (h : (evalUnbounded c).runState s = (o, t)) : Retained s t := by
  have hd := KatLang.EvaluatorDiscipline.evalUnbounded_disciplined c s
  have hl := KatLang.MemoLinks.evalUnbounded_linkDisc c s
  have hk := KatLang.EvaluatorCacheLaws.cache_entries_survive c s
  rw [h] at hd hl hk
  exact ⟨hd, hl, hk⟩

theorem get_append_of_get {h : Array NeedCell} (l : Array NeedCell) {a : Nat} {c : NeedCell}
    (hc : h[a]? = some c) : (h ++ l)[a]? = some c := by
  have hlt := KatLang.MemoLinks.lt_of_get hc
  rw [Array.getElem?_append_left hlt, hc]

theorem Retained.pushReady (s : EvalState) (ys : List Result) : Retained s (pushReady s ys) :=
  ⟨fun _ c hc => ⟨c, get_append_of_get _ hc, KatLang.CallPlan.CellKept.refl c⟩,
   fun _ c hc => ⟨c, get_append_of_get _ hc, KatLang.MemoLinks.LinkKept.refl c⟩,
   fun _ _ h => h⟩

/-- **NO ROLLBACK (`repeat`).** Whatever a finite run ends in, an ordinary error included, every
    earlier cell keeps its completed outcomes and links and every published entry survives. -/
theorem repeat_trace_retained {step : ResolvedArgumentAlgorithm} {ctx : EvalCtx} {env : ValEnv} {name : String}
    {n : Nat} {cells : List Nat} {s t : EvalState} {r : Except Error (List Nat)}
    (h : RepeatTrace step ctx env name n cells s r t) : Retained s t := by
  induction h with
  | done => exact .refl _
  | next hi hs _ ih => exact (Retained.ofRun _ hi).trans ((Retained.ofRun _ hs).trans ((Retained.pushReady _ _).trans ih))
  | projectError _ hi => exact .ofRun _ hi
  | refused hi => exact .ofRun _ hi
  | stepError _ hi hs => exact (Retained.ofRun _ hi).trans (.ofRun _ hs)

/-- **NO ROLLBACK (`while`).** A false round's discovery effects stay. -/
theorem while_trace_retained {step : ResolvedArgumentAlgorithm} {ctx : EvalCtx} {env : ValEnv} {name : String}
    {n : Nat} {cells : List Nat} {s t : EvalState} {r : Except Error (List Nat)}
    (h : WhileTrace step ctx env name n cells s r t) : Retained s t := by
  induction h with
  | stop hi hs => exact (Retained.ofRun _ hi).trans (.ofRun _ hs)
  | next hi hs _ ih => exact (Retained.ofRun _ hi).trans ((Retained.ofRun _ hs).trans ((Retained.pushReady _ _).trans ih))
  | projectError _ hi => exact .ofRun _ hi
  | refused hi => exact .ofRun _ hi
  | roundError _ hi hs => exact (Retained.ofRun _ hi).trans (.ofRun _ hs)

/-- **THE COMPLETED PROJECTION IS REUSED ACROSS ROUNDS.** Lean re-enters the projection capability
    each round; once the step cell holds a completed CALLABLE outcome, every later state reached
    with `Retained` re-reads that outcome and changes nothing. This is about the COMPLETED cell
    projection only: it says nothing about alias-resolution results or their context. -/
theorem projection_reused {s t : EvalState} (hr : Retained s t) (cell : Nat) (c : NeedCell)
    (outcome : Except Error (Option Algorithm)) (hc : s.needs[cell]? = some c)
    (ho : c.callable = .projected outcome) :
    (invokeNeed (stepArgument cell)).runState t = (outcome, t) := by
  obtain ⟨c', hc', hk⟩ := hr.links cell c hc
  have hdel : evalUnbounded (.invokeNeed (stepArgument cell)) =
      evalUnbounded (.projectNeedCallable cell) >>= pure :=
    delegation_equation (.invokeNeed (stepArgument cell)) (.projectNeedCallable cell) pure
      (fun rec => by
        show EvalBody.invokeNeed rec (stepArgument cell) = _
        simp only [EvalBody.invokeNeed, stepArgument]
        exact (bind_pure_eq _).symm ▸ rfl) (fun _ _ => nofun)
  show (evalUnbounded (.invokeNeed (stepArgument cell))).runState t = _
  rw [hdel, bind_pure_eq]
  exact KatLang.MemoLinks.projectNeedCallable_projected cell t c' outcome hc' (hk.callable outcome ho)

/-- The bound cells of the `repeat` arm are the binder's: the adapter and the ORIGINAL count cell. -/
theorem repeatBindings_cells (s : EvalState) (cnt : Nat) :
    lookupAssoc "step" (repeatBindings s cnt) = some s.needs.size ∧
    lookupAssoc "count" (repeatBindings s cnt) = some cnt := by
  simp [repeatBindings, lookupAssoc]

/-- The count demand reads the count's ORIGINAL bound cell through the ordinary argument VALUE. -/
theorem countDemand_run (c : ResolvedArgumentAlgorithm) (s₀ s : EvalState) (cnt : Nat) (ctx : EvalCtx)
    (env : ValEnv) :
    (countDemand evalUnbounded c (repeatBindings s₀ cnt) ctx env).runState s =
      (evalArgumentValue { c with need? := some cnt } ctx env >>= expectInt).runState s := by
  unfold countDemand
  rw [EvalM.bind_runState, boundCell_run _ "count" cnt s (repeatBindings_cells s₀ cnt).2]
  rfl

/-- Naming the step reads the heap and writes nothing; it never fails. -/
theorem loopStepName_run (loopName : String) (step : ResolvedArgumentAlgorithm) (s : EvalState) :
    ∃ name, (loopStepName loopName step).runState s = (.ok name, s) := by
  have hsrc : ∀ a, ∃ w, (needWrittenSource? a).runState s = (.ok w, s) := by
    intro a
    simp only [needWrittenSource?, EvalM.bind_runState]
    show ∃ w, (match s.needs[a]? with
      | some { suspension := .expression source _ _, .. } => (pure (some source) : EvalM (Option Expr))
      | _ => pure none).runState s = _
    cases s.needs[a]? with
    | none => exact ⟨_, rfl⟩
    | some c =>
      cases c with
      | mk sus _ _ _ _ _ _ => cases sus <;> exact ⟨_, rfl⟩
  unfold loopStepName
  dsimp only
  cases hn : step.need? with
  | none => exact ⟨_, rfl⟩
  | some a =>
    dsimp only
    obtain ⟨w, hw⟩ := hsrc a
    rw [EvalM.bind_runState, hw]
    exact ⟨_, rfl⟩

end KatLang.FiniteLoop
