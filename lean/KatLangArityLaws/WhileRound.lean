import KatLang

open KatLang

/-!
# The condition-first `while` round (LOOP-06; LOOP-CF1, October 2026)

PRODUCTION theorems about the TOTAL row-control definitions in `KatLang.lean` that the evaluator
calls: `WhileRound.conditionFirst` (the `while` reader of a step body's rows, installed by
`whileVerdictSlots` over `formOutputRow`), `OutputRows.formLeftToRight` (the supply reader,
installed by `evalAlgOutputSlots`), `WhileRound.ofSupply` / `splitContSlots` (one atomic row) and
`WhileRound.advance` (one iteration of the `.whileBuiltin` loop). Every theorem quantifies over
the row-forming capability `form` and the whole `EvalState`, so rows may have arbitrary
state-dependent effects (heap allocation, cell completion, cache publication) and failures.

This module is row CONTROL only. Its connection to the production evaluator (CF-4, S6c, October
2026) is `KatLangArityLaws/WhileRoundProduction.lean`: the shared activated-body boundary
`ActivatedBody.readRows` (one body entry, ONE `form pushedCtx env` closure for every row), the
production `formOutputRow` as one `evalCounted` plus `OutputRows.items` (an exact equation), the
finite-use converse that makes the production `whileVerdictSlots` EQUAL its activated-body run
wherever that completes, and these laws restated about the production operation
(`production_cf1_*`, `production_cf2_*`, `production_cf5_*`, …), with the separately stated
cell- and cache-sharing subclaims.

What is NOT proved here or there, and stays a source-level, executable or open fact:

* that every ordinary expression evaluation routes its property reads through the production
  property access with stable key inputs (evaluator internals), and key stability for LOCAL-only
  bindings across rows (a whole-run lexical-activation invariant; `propertyOwnerBindingContext`
  is `partial`);
* the round's dispatch (`runNeedWhileRound`) is proved only for COMPLETED runs
  (`production_unfolds`); the binder/family channels are not covered by the finite-use converse;
* anything about C# (budgets, cancellation, host effects, random draws, async suspension):
  those are covered by the C# differential tests (`LoopConditionFirstTests`);
* whole-run heap/cache refinement and the reachable-state / active-cell obligations: still open.
  (R7, October 2026: `ProductionDiscipline` is a theorem, `KatLangArityLaws/EvaluatorDiscipline.lean`;
  the whole-run property-cache laws are `KatLangArityLaws/EvaluatorCacheLaws.lean`.)

The CF-7 equivalence with the retired step-first reading holds ONLY under its stated premise:
every row succeeds with a state-INDEPENDENT result and leaves the state unchanged. It does not
cover effectful, failing or resource-limited rows — and the guards in `WhileRoundGuards.lean`
witness that, without that premise, condition-first effects are not a subset of step-first
effects and a step-first success can become a condition-first failure.
-/

namespace KatLang.WhileRoundLaws

theorem bind_run {α β : Type} (m : EvalM α) (f : α → EvalM β) (st : EvalState) :
    (m >>= f).runState st =
      (match m.runState st with
       | (.ok a, next) => (f a).runState next
       | (.error e, next) => (.error e, next)) := by
  simp only [bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont, StateT.bind]
  rcases m.runState st with ⟨out, next⟩
  cases out <;> rfl

theorem pure_run {α : Type} (a : α) (st : EvalState) :
    (pure a : EvalM α).runState st = (.ok a, st) := rfl

theorem throw_run {α : Type} (e : Error) (st : EvalState) :
    (throw e : EvalM α).runState st = (.error e, st) := rfl

theorem noFlag_run {α : Type} (st : EvalState) :
    (WhileRound.noFlag : EvalM α).runState st =
      (.error (Error.withContext whileStepWithoutFlagContext Error.badArity), st) := rfl

/-- The flag rule's outcome on a Boolean item. -/
theorem flag_bool (f : Result) (b : Bool) (hf : Result.asBool? f = some b) (st : EvalState) :
    (WhileRound.flag f).runState st = (.ok b, st) := by
  simp only [WhileRound.flag, hf]; rfl

/-- The flag rule's outcome on a non-Boolean item: the value-kind error, state unchanged. -/
theorem flag_not_bool (f : Result) (hf : Result.asBool? f = none) (st : EvalState) :
    (WhileRound.flag f).runState st =
      (.error (Error.typeMismatch
        (booleanRequiredMessage "while continuation flag (the step's last output)" f)), st) := by
  simp only [WhileRound.flag, hf]; rfl

/-! ## The supply reader is left to right (LOOP-03; `evalAlgOutputSlots`, `repeat`) -/

/-- The supply reader forms the FIRST row first, then the rest from the state it left. -/
theorem supply_reader_left_to_right (form : Expr → EvalM (List Result)) (e : Expr)
    (rest : List Expr) (st : EvalState) :
    (OutputRows.formLeftToRight form (e :: rest)).runState st =
      (match (form e).runState st with
       | (.ok xs, s₁) =>
         match (OutputRows.formLeftToRight form rest).runState s₁ with
         | (.ok ys, s₂) => (.ok (xs ++ ys), s₂)
         | (.error err, s₂) => (.error err, s₂)
       | (.error err, s₁) => (.error err, s₁)) := by
  simp only [OutputRows.formLeftToRight, bind_run]
  rcases (form e).runState st with ⟨out, s₁⟩
  cases out with
  | error err => rfl
  | ok xs =>
    simp only
    rcases (OutputRows.formLeftToRight form rest).runState s₁ with ⟨out₂, s₂⟩
    cases out₂ <;> rfl

/-! ## Flag discovery passes over effectful empty rows, right to left -/

/-- `EmptySuffix form rows s t`: forming the rows of `rows` RIGHT TO LEFT (last row first), each
    succeeds supplying NO item, threading the state from `s` to `t`. Each row may change the
    state arbitrarily (an effectful empty spread). -/
inductive EmptySuffix (form : Expr → EvalM (List Result)) : List Expr → EvalState → EvalState → Prop
  | nil (s : EvalState) : EmptySuffix form [] s s
  | snoc (rows : List Expr) (e : Expr) (s t u : EvalState) :
      (form e).runState s = (.ok [], t) → EmptySuffix form rows t u →
      EmptySuffix form (rows ++ [e]) s u

/-- Discovery over an empty suffix is exactly its right-to-left formation, then discovery of
    what lies left of it. -/
theorem discover_empty_suffix (form : Expr → EvalM (List Result)) (rows : List Expr)
    (s u : EvalState) (h : EmptySuffix form rows s u) (rest : List Expr) :
    (WhileRound.discover form (rows.reverse ++ rest)).runState s =
      (WhileRound.discover form rest).runState u := by
  induction h with
  | nil s => rfl
  | snoc rows e s t u he _ ih =>
    simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons_append]
    simp only [WhileRound.discover, bind_run, he]
    exact ih

/-- The discovered row: the first row from the right that supplies an item. -/
theorem discover_found (form : Expr → EvalM (List Result)) (e : Expr) (rest : List Expr)
    (s t : EvalState) (x : Result) (xs : List Result) (he : (form e).runState s = (.ok (x :: xs), t)) :
    (WhileRound.discover form (e :: rest)).runState s = (.ok (some (rest.reverse, x :: xs)), t) := by
  simp only [WhileRound.discover, bind_run, he]; rfl

/-- A row failing during discovery fails discovery with its own error. -/
theorem discover_failed (form : Expr → EvalM (List Result)) (e : Expr) (rest : List Expr)
    (s t : EvalState) (err : Error) (he : (form e).runState s = (.error err, t)) :
    (WhileRound.discover form (e :: rest)).runState s = (.error err, t) := by
  simp only [WhileRound.discover, bind_run, he]

/-- The reversed layout of a round whose flag row `r` has the earlier rows `pre` on its left and
    the trailing rows `trail` on its right. -/
theorem round_reverse (pre : List Expr) (r : Expr) (trail : List Expr) :
    (pre ++ r :: trail).reverse = trail.reverse ++ (r :: pre.reverse) := by
  simp [List.reverse_append]

/-! ## CF-1, CF-2, CF-5: the round, with an effectful empty trailing suffix -/

/-- CF-1 (production `WhileRound.conditionFirst`). The trailing rows `trail` are formed right to
    left supplying nothing (`EmptySuffix`, their effects included), then the flag row `r`
    supplies `items` whose last item is `false`. The round STOPS (`none`), and its final state is
    exactly the state after that discovery: no row of `pre` is formed. -/
theorem cf1_false_skips_earlier_rows (form : Expr → EvalM (List Result))
    (pre : List Expr) (r : Expr) (trail : List Expr) (s s₁ s₂ : EvalState)
    (x : Result) (xs : List Result) (f : Result)
    (htrail : EmptySuffix form trail s s₁) (hr : (form r).runState s₁ = (.ok (x :: xs), s₂))
    (hlast : (x :: xs).getLast? = some f) (hf : Result.asBool? f = some false) :
    (WhileRound.conditionFirst form (pre ++ r :: trail)).runState s = (.ok none, s₂) := by
  unfold WhileRound.conditionFirst
  rw [bind_run, round_reverse, discover_empty_suffix form trail s s₁ htrail, discover_found form r _ s₁ s₂ x xs hr]
  simp only [List.reverse_reverse, hlast, bind_run, flag_bool f false hf s₂]
  rfl

/-- CF-2 (production). As CF-1 with a `true` flag: the earlier rows `pre` are formed exactly
    once, LEFT TO RIGHT, starting from the state discovery left; a failure among them fails the
    round with that failure; otherwise the next state is the whole supply in written order (the
    earlier rows' items, then the flag row's items) without its last item (`nextSlots`). The
    empty trailing rows contribute nothing. -/
theorem cf2_true_forms_earlier_rows_once (form : Expr → EvalM (List Result))
    (pre : List Expr) (r : Expr) (trail : List Expr) (s s₁ s₂ : EvalState)
    (x : Result) (xs : List Result) (f : Result)
    (htrail : EmptySuffix form trail s s₁) (hr : (form r).runState s₁ = (.ok (x :: xs), s₂))
    (hlast : (x :: xs).getLast? = some f) (hf : Result.asBool? f = some true) :
    (WhileRound.conditionFirst form (pre ++ r :: trail)).runState s =
      (match (OutputRows.formLeftToRight form pre).runState s₂ with
       | (.ok ys, s₃) => (.ok (some (WhileRound.nextSlots (ys ++ x :: xs))), s₃)
       | (.error err, s₃) => (.error err, s₃)) := by
  unfold WhileRound.conditionFirst
  rw [bind_run, round_reverse, discover_empty_suffix form trail s s₁ htrail, discover_found form r _ s₁ s₂ x xs hr]
  simp only [List.reverse_reverse, hlast, bind_run, flag_bool f true hf s₂]
  simp only [ite_true]
  rw [bind_run]
  rcases (OutputRows.formLeftToRight form pre).runState s₂ with ⟨out, s₃⟩
  cases out <;> rfl

/-- CF-5a (production). A row failing during discovery — the flag row, or any trailing row
    formed before it — fails the round with ITS OWN error, from the state discovery reached; no
    earlier row is formed. -/
theorem cf5_discovery_failure_first (form : Expr → EvalM (List Result))
    (pre : List Expr) (r : Expr) (trail : List Expr) (s s₁ s₂ : EvalState) (err : Error)
    (htrail : EmptySuffix form trail s s₁) (hr : (form r).runState s₁ = (.error err, s₂)) :
    (WhileRound.conditionFirst form (pre ++ r :: trail)).runState s = (.error err, s₂) := by
  unfold WhileRound.conditionFirst
  rw [bind_run, round_reverse, discover_empty_suffix form trail s s₁ htrail, discover_failed form r _ s₁ s₂ err hr]

/-- CF-5b (production). A non-Boolean flag is the value-kind error, reported before any earlier
    row is formed. -/
theorem cf5_nonboolean_flag_first (form : Expr → EvalM (List Result))
    (pre : List Expr) (r : Expr) (trail : List Expr) (s s₁ s₂ : EvalState)
    (x : Result) (xs : List Result) (f : Result)
    (htrail : EmptySuffix form trail s s₁) (hr : (form r).runState s₁ = (.ok (x :: xs), s₂))
    (hlast : (x :: xs).getLast? = some f) (hf : Result.asBool? f = none) :
    (WhileRound.conditionFirst form (pre ++ r :: trail)).runState s =
      (.error (Error.typeMismatch
        (booleanRequiredMessage "while continuation flag (the step's last output)" f)), s₂) := by
  unfold WhileRound.conditionFirst
  rw [bind_run, round_reverse, discover_empty_suffix form trail s s₁ htrail, discover_found form r _ s₁ s₂ x xs hr]
  simp only [List.reverse_reverse, hlast, bind_run, flag_not_bool f hf s₂]

/-- No row supplies an item: every row is formed (right to left, effects included) and the round
    fails with the missing-flag `badArity`. -/
theorem cf_all_rows_empty_no_flag (form : Expr → EvalM (List Result)) (rows : List Expr)
    (s t : EvalState) (h : EmptySuffix form rows s t) :
    (WhileRound.conditionFirst form rows).runState s =
      (.error (Error.withContext whileStepWithoutFlagContext Error.badArity), t) := by
  unfold WhileRound.conditionFirst
  have := discover_empty_suffix form rows s t h []
  rw [List.append_nil] at this
  rw [bind_run, this]
  rfl

/-- The one-item rule: a round whose whole supply is ONE Boolean `true` item keeps that item as
    its next state. -/
theorem cf_single_item_is_state (x : Result) : WhileRound.nextSlots [x] = [x] := rfl

/-- Otherwise the next state drops exactly the last item, the flag. -/
theorem cf_next_drops_flag (x y : Result) (rest : List Result) :
    WhileRound.nextSlots (x :: y :: rest) = (x :: y :: rest).dropLast := rfl

/-! ## CF-3: the loop iteration keeps the cells that entered a stopping round -/

/-- CF-3 (production `WhileRound.advance`, one iteration of the `.whileBuiltin` loop). A round
    whose verdict is `false` FINISHES the loop with exactly the cells that entered it — on the
    first round, the original initial cells (R1: zero accepted transitions); their final VALUE
    materialization is the loop's separate LOOP-07 boundary (`demandNeedRecursive`, then
    `loopResultCounted`). Nothing is allocated for a candidate next state. -/
theorem cf3_false_round_keeps_entering_cells
    (round : List Nat → EvalM (Option (List Result))) (cells : List Nat) (s t : EvalState)
    (h : (round cells).runState s = (.ok none, t)) :
    (WhileRound.advance round cells).runState s = (.ok (.inl cells), t) := by
  simp only [WhileRound.advance, bind_run, h]; rfl

/-! ## CF-7: agreement with the retired step-first reading, ONLY for state-independent rows -/

/-- The retired step-first reading (LOOP-06 before LOOP-CF1): every row left to right, then the
    split. Defined here ONLY as the comparison point of CF-7; no production path calls it. -/
def stepFirst (form : Expr → EvalM (List Result)) (rows : List Expr) : EvalM (Option (List Result)) := do
  let supply ← OutputRows.formLeftToRight form rows
  let (next, cont) ← splitContSlots supply
  pure (if cont then some next else none)

/-- The CF-7 premise: every row (in `rows`) succeeds with a fixed item list `out e`, whatever the
    state, and leaves the state UNCHANGED. It excludes every effect, failure, cache fill, budget
    and cancellation. -/
def StateIndependent (form : Expr → EvalM (List Result)) (out : Expr → List Result)
    (rows : List Expr) : Prop :=
  ∀ e ∈ rows, ∀ st : EvalState, (form e).runState st = (.ok (out e), st)

theorem formLeftToRight_independent (form : Expr → EvalM (List Result)) (out : Expr → List Result)
    (rows : List Expr) (h : StateIndependent form out rows) (st : EvalState) :
    (OutputRows.formLeftToRight form rows).runState st = (.ok (rows.flatMap out), st) := by
  induction rows with
  | nil => rfl
  | cons e rest ih =>
    have he := h e (by simp) st
    have hrest : StateIndependent form out rest := fun e' he' st' => h e' (by simp [he']) st'
    simp only [OutputRows.formLeftToRight, bind_run, he, ih hrest, pure_run, List.flatMap_cons]

theorem discover_independent (form : Expr → EvalM (List Result)) (out : Expr → List Result)
    (rows : List Expr) (h : StateIndependent form out rows) (st : EvalState) :
    ((rows.flatMap out = [] ∧ (WhileRound.discover form rows).runState st = (.ok none, st)) ∨
     (∃ (k : List Expr) (x : Result) (xs : List Result),
        (WhileRound.discover form rows).runState st = (.ok (some (k, x :: xs)), st) ∧
        StateIndependent form out k ∧
        k.flatMap out ++ (x :: xs) = rows.reverse.flatMap out)) := by
  induction rows with
  | nil => left; exact ⟨rfl, rfl⟩
  | cons e rest ih =>
    have he := h e (by simp) st
    have hrest : StateIndependent form out rest := fun e' he' st' => h e' (by simp [he']) st'
    cases hout : out e with
    | nil =>
      rcases ih hrest with ⟨h0, hd⟩ | ⟨k, x, xs, hd, hk, hflat⟩
      · left
        refine ⟨by simp [List.flatMap_cons, hout, h0], ?_⟩
        simp only [WhileRound.discover, bind_run, he, hout]; exact hd
      · right
        refine ⟨k, x, xs, ?_, hk, ?_⟩
        · simp only [WhileRound.discover, bind_run, he, hout]; exact hd
        · simp [List.flatMap_append, hout, hflat]
    | cons y ys =>
      right
      refine ⟨rest.reverse, y, ys, ?_, ?_, ?_⟩
      · simp only [WhileRound.discover, bind_run, he, hout]; rfl
      · intro e' he' st'; exact hrest e' (by simpa using he') st'
      · simp [List.flatMap_append, hout]

theorem splitContSlots_run (supply : List Result) (st : EvalState) :
    (splitContSlots supply).runState st =
      (match supply.getLast? with
       | none => (.error (Error.withContext whileStepWithoutFlagContext Error.badArity), st)
       | some last =>
         match (WhileRound.flag last).runState st with
         | (.ok c, s₁) => (.ok (WhileRound.nextSlots supply, c), s₁)
         | (.error err, s₁) => (.error err, s₁)) := by
  unfold splitContSlots
  cases supply.getLast? with
  | none => rfl
  | some last =>
    simp only [bind_run]
    rcases (WhileRound.flag last).runState st with ⟨out, s₁⟩
    cases out <;> rfl

/-- CF-7 (production `WhileRound.conditionFirst`, against `stepFirst`). For rows that all succeed
    with STATE-INDEPENDENT results and leave the state unchanged, the condition-first round and
    the retired step-first reading agree exactly: same outcome (stop, next state, or error) and
    same state. The flag discovered first is the last item of the complete supply. Nothing is
    claimed for effectful, failing or state-dependent rows (see `WhileRoundGuards.lean`). -/
theorem cf7_agree_on_state_independent_rows (form : Expr → EvalM (List Result))
    (out : Expr → List Result) (rows : List Expr) (h : StateIndependent form out rows)
    (st : EvalState) :
    (WhileRound.conditionFirst form rows).runState st = (stepFirst form rows).runState st := by
  have hrev : StateIndependent form out rows.reverse :=
    fun e he st' => h e (List.mem_reverse.mp he) st'
  unfold WhileRound.conditionFirst stepFirst
  rw [bind_run, bind_run, formLeftToRight_independent form out rows h st]
  rcases discover_independent form out rows.reverse hrev st with ⟨h0, hd⟩ | ⟨k, x, xs, hd, hk, hflat⟩
  · have hflat : rows.flatMap out = [] := by
      simpa [List.flatMap_reverse] using h0
    rw [hd]
    simp only [bind_run, splitContSlots_run, hflat, List.getLast?_nil]
    rfl
  · rw [hd]
    simp only [List.reverse_reverse] at hflat
    rw [← hflat]
    cases hlast : (x :: xs).getLast? with
    | none => simp at hlast
    | some f =>
      have hsupply : (k.flatMap out ++ x :: xs).getLast? = some f := by
        rw [List.getLast?_append, hlast]; rfl
      cases hb : Result.asBool? f with
      | none =>
        simp only [hlast, bind_run, splitContSlots_run, hsupply, flag_not_bool f hb st]
      | some b =>
        cases b with
        | false =>
          simp only [hlast, bind_run, splitContSlots_run, hsupply, flag_bool f false hb st]
          rfl
        | true =>
          simp only [hlast, bind_run, splitContSlots_run, hsupply, flag_bool f true hb st, ↓reduceIte]
          rw [formLeftToRight_independent form out k hk st]

/-- The builtin arm: a round over ONE atomic row is the ordinary split of that row's supply. -/
theorem atomic_round_is_split (supply : List Result) (st : EvalState) :
    (WhileRound.ofSupply supply).runState st =
      (match (splitContSlots supply).runState st with
       | (.ok (next, cont), s₁) => (.ok (if cont then some next else none), s₁)
       | (.error err, s₁) => (.error err, s₁)) := by
  simp only [WhileRound.ofSupply, bind_run]
  rcases (splitContSlots supply).runState st with ⟨out, s₁⟩
  cases out with
  | error err => rfl
  | ok p => rcases p with ⟨next, cont⟩; rfl

end KatLang.WhileRoundLaws
