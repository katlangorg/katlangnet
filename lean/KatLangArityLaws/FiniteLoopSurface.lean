import KatLangArityLaws.FiniteLoopCorrespondence

open KatLang KatLang.EvaluatorCore KatLang.WhileRoundProduction KatLang.FiniteLoop

/-!
# E-15 widening: the surface domain of the finite-loop comparison (November 2026)

`FiniteLoopCorrespondence.lean` (FG-L1) compared one loop step with the ordinary call under three
run premises — `UserRowsBounded`, `FamilyRowsBounded` and canonical slots — that its guards
discharged for numeric literal rows only, and it gave builtin and alias steps their dispatch only.
This module discharges those premises for whole syntactic classes of steps, and proves value
theorems for builtin and alias steps. It changes no definition of `KatLang.lean` and no theorem
of `FiniteLoopCorrespondence.lean`.

## The domain

The classes are syntactic and stated on a row's OWN constructor, so they hold from every state,
in every context, for every supply: the evaluator arm of such a row fixes the count itself.

* `scalarRow` — a literal (`7`, `'a'`, `true`), `()`, an interpolated string, and every unary,
  binary and comparison operator WHATEVER ITS OPERANDS: `x + 1`, `-x`, `not b`, `x < n`,
  `F(x) * 2`, `xs[0] + y`. Such a row completes with one canonical scalar (or `()`) at a
  value-boundary count (`scalarRow_canonical`).
* `valueRow` — a scalar row, a capture `(b, a)`, a name `K`, an inline block, a selection
  `xs[i]`, a list `[x, x]`, an internal join, or an explicit spread `v*`. A non-spread value row
  completes at a value-boundary count (`valueRow_bounded`); a spread is admitted by `RowBoundary`
  as it is.

Discharges:

| Premise | Discharged for | Theorem |
| --- | --- | --- |
| `BoundedRows` | every list of value rows, every state | `boundedRows_of_valueRows` |
| `UserRowsBounded` | every user step whose rows are value rows (`RowsBy valueRow`) | `userRowsBounded_of_valueRows` |
| `FamilyRowsBounded` | every family whose clause bodies are user bodies with value rows (`ClauseBy valueRow`) | `familyRowsBounded_of_clauses` (via `select_ok`: every dispatched body is a clause body wired under the family) |
| canonical slots | every user step / family whose rows are scalar rows | `user_slots_canonical`, `family_slots_canonical` |

Examples IN the domain: `Inc(x) = x + 1`; `Next(x) = x + 1, x < 3`; `Twice(x) = x + 1, x * 2`;
`Use(x) = Inc(x) * 2`; `Fam(0) = 100; Fam(n) = n * 2`; `Flip(a, b) = (b, a)` (rows bounded,
value equality NOT claimed: a capture is not a scalar row); `Sel(xs) = xs[0]`; `Lst(x) = [x, x]`.

Examples OUTSIDE it: `Swap(a, b) = b, a` and `Echo(x) = x` (a bare parameter row reads the
supplied cell's count: a host-built Ready cell of count two splits, guard `hostTwoCell` of
FG-L1); `Wrap(x) = F(x)` (a bare call row's count is the callee's: a builtin callee's own
count is not proved bounded here); `Dot(x) = x.F` (dot member).

## The value theorems

* `count_one_user_value`, `count_one_family_value`: for scalar-row steps, `repeat` of count one
  completes with `v` IFF the ordinary call over the same cells completes with the SAME `v`; the
  loop's final state is the call's plus one completed slot cell per slot. Premise: the step
  projection only.
* `builtin_step_value`, `count_one_builtin`, `count_one_builtin_ok`: a builtin step round IS its
  ordinary application's completed outcome (its one result as one slot, an error under the
  step frame), and `repeat(1)` is determined by the ordinary call `F(args)`; on a canonical
  result it IS `reCountValueBoundary` of the call's result (`scalar_canonical` discharges this
  for numbers, Booleans and strings). No Lean `Builtin` is excluded from this application-relative
  statement. Additionally `count_application_value` / `count_one_count_value` prove the top-level
  length formula for ordinary prepared collections (excluding views and retained collectors), and
  `if_application_value` / `count_one_if_value` prove the chosen-branch formula for both Boolean
  conditions, without evaluating the other branch. These use argument-operation premises rather
  than assuming the builtin application's result. Other builtins have no closed-form result law
  here. Math functions and host operations in the C# corpus are outside Lean's `Builtin` type.
* `alias_loop_forwards`, `alias_call_forwards`, `StepAgreement.forward`: once an alias resolves
  to `target`, both receivers ARE the target's from the resolved state.
  `alias_user_step_agreement`, `count_one_alias_value`, `count_one_alias_builtin` follow.

## Not claimed

Bare parameter, bare call and dot-member rows (above); canonical values of non-scalar value
rows (a capture, list, name or selection value is not proved canonical); canonicity of a
builtin list result beyond the premise; the alias resolution premise (resolution is not shown to
succeed); arbitrary-binder `FuelReached` (E-7);
C#, which stays finite evidence (E-16).
-/

namespace KatLang.FiniteLoopSurface

/-! ## 1. Completed outcomes that satisfy a predicate -/

/-- Every completed (`.ok`) outcome of `m`, from every state, satisfies `P`. -/
def OkSat {α : Type} (P : α → Prop) (m : EvalM α) : Prop :=
  ∀ s a t, m.runState s = (.ok a, t) → P a

theorem okSat_pure {α : Type} {P : α → Prop} {a : α} (h : P a) : OkSat P (pure a) := by
  intro s a' t hrun
  cases hrun
  exact h

theorem okSat_error {α : Type} {P : α → Prop} (e : Error) : OkSat P (EvalM.error e : EvalM α) := by
  intro s a t hrun
  cases hrun

theorem okSat_throw {α : Type} {P : α → Prop} (e : Error) : OkSat P (throw e : EvalM α) := by
  intro s a t hrun
  cases hrun

theorem okSat_bind {α β : Type} {P : α → Prop} {m : EvalM β} {k : β → EvalM α}
    (h : ∀ b, OkSat P (k b)) : OkSat P (m >>= k) := by
  intro s a t hrun
  rw [EvalM.bind_runState] at hrun
  rcases hm : m.runState s with ⟨_ | b, u⟩
  · rw [hm] at hrun; cases hrun
  · rw [hm] at hrun; exact h b u a t hrun

theorem okSat_bind_of {α β : Type} {P : α → Prop} {Q : β → Prop} {m : EvalM β} {k : β → EvalM α}
    (hm : OkSat Q m) (h : ∀ b, Q b → OkSat P (k b)) : OkSat P (m >>= k) := by
  intro s a t hrun
  rw [EvalM.bind_runState] at hrun
  rcases hr : m.runState s with ⟨_ | b, u⟩
  · rw [hr] at hrun; cases hrun
  · rw [hr] at hrun; exact h b (hm s b u hr) u a t hrun

theorem okSat_nested {α : Type} {P : α → Prop} {m : EvalM α} (h : OkSat P m) :
    OkSat P (withNestedMissingOutput m) := by
  intro s a t hrun
  rw [nested_run] at hrun
  rcases hm : m.runState s with ⟨_ | b, u⟩
  · rw [hm] at hrun; cases hrun
  · rw [hm] at hrun; cases hrun; exact h s _ _ hm

theorem okSat_withCtx {α : Type} {P : α → Prop} {m : EvalM α} (c : String) (h : OkSat P m) :
    OkSat P (withCtx c m) := by
  intro s a t hrun
  rw [ctx_run] at hrun
  rcases hm : m.runState s with ⟨_ | b, u⟩
  · rw [hm] at hrun; rename_i e; cases e <;> cases hrun
  · rw [hm] at hrun; cases hrun; exact h s _ _ hm

theorem okSat_missingCtx {α : Type} {P : α → Prop} {m : EvalM α} (c : String) (h : OkSat P m) :
    OkSat P (withMissingOutputCtx c m) := by
  intro s a t hrun
  unfold withMissingOutputCtx at hrun
  rw [EvalM.bind_runState] at hrun
  rcases hm : m.runState s with ⟨o, u⟩
  cases o with
  | ok b =>
    rw [evalAttempt_runState_of_complete m s u _ hm rfl] at hrun
    cases hrun; exact h s _ _ hm
  | error e =>
    by_cases he : e = .fuelExhausted
    · subst he; rw [evalAttempt_runState_of_incomplete m s u hm] at hrun; cases hrun
    · have hc : (Except.error e : Except Error α).isIncomplete = false := by
        cases e <;> first | exact absurd rfl he | rfl
      rw [evalAttempt_runState_of_complete m s u _ hm hc] at hrun
      dsimp only at hrun
      split at hrun <;> first | (cases hrun; done) | (rename_i heq; cases heq; done) | simp_all

/-- A production operation's completed outcomes are its body's at production. -/
theorem okSat_call (c : EvalCall) (P : c.Ret → Prop) (h : OkSat P (evalStep evalUnbounded c)) :
    OkSat P (evalUnbounded c) := by
  intro s a t hrun
  have hc : ProductionCompletes (evalUnbounded c) s := by
    unfold ProductionCompletes; rw [hrun]; nofun
  exact h s a t ((production_unfolds c s hc).trans hrun)

theorem valueCount_le (r : Result) : r.valueCount ≤ 1 := by
  unfold Result.valueCount; split <;> omega

theorem okSat_mono {α : Type} {P Q : α → Prop} {m : EvalM α} (h : ∀ a, P a → Q a) (hm : OkSat P m) :
    OkSat Q m :=
  fun s a t hrun => h a (hm s a t hrun)

/-- A value-boundary count: what `RowBoundary` asks of a non-spread row. -/
def Bounded (out : CountedResult) : Prop := out.snd ≤ 1

/-- A value-boundary count AND a canonical value: what the value equality asks of a slot. -/
def Canonical (out : CountedResult) : Prop := out.snd ≤ 1 ∧ out.fst.normalize = out.fst

theorem Canonical.bounded {out : CountedResult} (h : Canonical out) : Bounded out := h.1

theorem canon_atom (n : Int) : Canonical (.atom n, 1) := ⟨Nat.le_refl _, by simp [Result.normalize]⟩
theorem canon_bool (b : Bool) : Canonical (.bool b, 1) := ⟨Nat.le_refl _, by simp [Result.normalize]⟩
theorem canon_str (x : String) : Canonical (.str x, 1) := ⟨Nat.le_refl _, by simp [Result.normalize]⟩

/-- One structural step of an `OkSat` goal. -/
syntax "oksat_step" : tactic
macro_rules
  | `(tactic| oksat_step) => `(tactic| first
      | exact okSat_error _
      | exact okSat_throw _
      | (apply okSat_pure)
      | (apply okSat_nested)
      | (apply okSat_withCtx)
      | (apply okSat_missingCtx)
      | (apply okSat_bind; intro _)
      | split)

/-! ## 2. The operator arms: one canonical scalar, whatever the operands -/

theorem negativeIntPow_atom (x y : Int) :
    OkSat (fun r => ∃ n, r = Result.atom n) (negativeIntPow x y) := by
  unfold negativeIntPow
  split
  · exact okSat_error _
  split
  · exact okSat_pure ⟨_, rfl⟩
  split
  · exact okSat_pure ⟨_, rfl⟩
  · exact okSat_error _

theorem unary_canonical (op : UnaryOp) (operand : Expr) (ctx : EvalCtx) (env : ValEnv) :
    OkSat Canonical (evalUnbounded (.evalUnaryCounted op operand ctx env)) := by
  refine okSat_call (.evalUnaryCounted op operand ctx env) Canonical ?_
  show OkSat _ (EvalBody.evalUnaryCounted evalUnbounded op operand ctx env)
  unfold EvalBody.evalUnaryCounted
  refine okSat_bind fun r => ?_
  cases op
  all_goals (dsimp only; split)
  all_goals first | exact okSat_error _ | first | exact okSat_pure (canon_atom _) | exact okSat_pure (canon_bool _)

theorem binary_canonical (op : BinaryOp) (a b : Expr) (ctx : EvalCtx) (env : ValEnv) :
    OkSat Canonical (evalUnbounded (.evalBinaryCounted op a b ctx env)) := by
  refine okSat_call (.evalBinaryCounted op a b ctx env) Canonical ?_
  show OkSat _ (EvalBody.evalBinaryCounted evalUnbounded op a b ctx env)
  unfold EvalBody.evalBinaryCounted
  refine okSat_bind fun lr => okSat_bind fun rr => ?_
  split
  all_goals first | exact okSat_bind fun x => okSat_bind fun y => okSat_pure (canon_bool _) | skip
  split
  all_goals first | exact okSat_error _ | skip
  refine okSat_bind fun x => okSat_bind fun y => ?_
  split
  · exact okSat_error _
  split
  · refine okSat_bind_of (negativeIntPow_atom x y) fun v hv => ?_
    obtain ⟨n, rfl⟩ := hv
    exact okSat_pure (canon_atom n)
  · apply okSat_pure
    split <;> first | exact canon_atom _ | exact canon_bool _

theorem links_canonical (pe : Expr) (prev : Result) (holds : Bool) (links : List ComparisonLink)
    (ctx : EvalCtx) (env : ValEnv) :
    OkSat Canonical (evalUnbounded (.evalComparisonLinksCounted pe prev holds links ctx env)) := by
  induction links generalizing pe prev holds with
  | nil =>
    refine okSat_call (.evalComparisonLinksCounted pe prev holds [] ctx env) Canonical ?_
    exact okSat_pure (canon_bool _)
  | cons l rest ih =>
    refine okSat_call (.evalComparisonLinksCounted pe prev holds (l :: rest) ctx env) Canonical ?_
    show OkSat _ (EvalBody.evalComparisonLinksCounted evalUnbounded pe prev holds (l :: rest) ctx env)
    unfold EvalBody.evalComparisonLinksCounted
    exact okSat_bind fun _ => okSat_bind fun _ => ih _ _ _

theorem comparison_canonical (first : Expr) (links : List ComparisonLink) (ctx : EvalCtx) (env : ValEnv) :
    OkSat Canonical (evalUnbounded (.evalComparisonCounted first links ctx env)) := by
  refine okSat_call (.evalComparisonCounted first links ctx env) Canonical ?_
  show OkSat _ (EvalBody.evalComparisonCounted evalUnbounded first links ctx env)
  unfold EvalBody.evalComparisonCounted
  exact okSat_bind fun _ => links_canonical _ _ _ _ _ _

theorem listLiteral_bounded (elements : List Expr) (ctx : EvalCtx) (env : ValEnv) :
    OkSat Bounded (evalUnbounded (.evalListLiteralCounted elements ctx env)) := by
  refine okSat_call (.evalListLiteralCounted elements ctx env) Bounded ?_
  show OkSat _ (EvalBody.evalListLiteralCounted evalUnbounded elements ctx env)
  unfold EvalBody.evalListLiteralCounted
  exact okSat_bind fun _ => okSat_pure (Nat.le_refl _)

theorem construct_loop_bounded (ctx : EvalCtx) (env : ValEnv) :
    ∀ (leaves : List Expr) (items : List Result),
      OkSat Bounded (EvalBody.evalSequenceConstructCounted.loop evalUnbounded ctx env leaves items) := by
  intro leaves
  induction leaves with
  | nil => intro items; exact okSat_pure (valueCount_le _)
  | cons leaf rest ih =>
    intro items
    unfold EvalBody.evalSequenceConstructCounted.loop
    split
    · exact okSat_bind fun _ => ih _
    · refine okSat_bind fun _ => ?_
      split
      · exact ih _
      · exact ih _

theorem construct_bounded (e : Expr) (ctx : EvalCtx) (env : ValEnv) :
    OkSat Bounded (evalUnbounded (.evalSequenceConstructCounted e ctx env)) := by
  refine okSat_call (.evalSequenceConstructCounted e ctx env) Bounded ?_
  show OkSat _ (EvalBody.evalSequenceConstructCounted evalUnbounded e ctx env)
  unfold EvalBody.evalSequenceConstructCounted
  exact construct_loop_bounded ctx env _ _

/-! ## 3. The surface row classes -/

/-- SCALAR ROWS: a row whose OWN evaluator arm forms one canonical scalar value (or `()`),
    whatever its operands are: literals, `()`, interpolated strings, and the unary, binary and
    comparison operators. Operands are unrestricted: `x + 1`, `F(x) * 2`, `x < n` are scalar rows
    for parameters `x`, `n` and any call `F(x)`. -/
def scalarRow : Expr → Bool
  | .num _ | .stringLiteral _ | .boolLiteral _ | .emptySequence _ | .interpolatedString _ _
  | .unary _ _ | .binary _ _ _ | .comparison _ _ => true
  | _ => false

/-- VALUE-BOUNDARY ROWS: a scalar row, or a row whose own arm re-counts its value at a value
    boundary (a capture `(…)`, a name `A`, an inline block, a selection `v[i]`, a list `[…]`, an
    internal join), or an explicit spread `v*` (which `RowBoundary` admits as it is). Not here:
    a bare parameter `x`, a bare call `F(…)` and a dot member `R.F`, whose count is the supplied
    cell's or the callee's (see the module notes). -/
def valueRow : Expr → Bool
  | .capture _ | .resolve _ | .algorithmExpr _ | .index _ _ | .listLiteral _ | .sequenceConstruct _ _
  | .sequenceSpread _ => true
  | e => scalarRow e

theorem valueRow_of_scalarRow {e : Expr} (h : scalarRow e = true) : valueRow e = true := by
  cases e <;> first | rfl | exact h

theorem canon_empty (depth : Nat) :
    Canonical (buildEmptySequenceValue depth, Result.valueCount (buildEmptySequenceValue depth)) :=
  ⟨valueCount_le (buildEmptySequenceValue depth), by simp [buildEmptySequenceValue, Result.normalize]⟩

/-- **A scalar row completes with a canonical value at a value-boundary count**, from every state,
    in every context. -/
theorem scalarRow_canonical (e : Expr) (h : scalarRow e = true) (ctx : EvalCtx) (env : ValEnv) :
    OkSat Canonical (evalCounted e ctx env) := by
  refine okSat_call (.evalCounted e ctx env) Canonical ?_
  show OkSat _ (EvalBody.evalCounted evalUnbounded e ctx env)
  cases e <;> simp [scalarRow] at h <;> dsimp only [EvalBody.evalCounted]
  · exact okSat_pure (canon_atom _)
  · exact okSat_pure (canon_str _)
  · exact okSat_nested (okSat_bind fun _ => okSat_pure (canon_str _))
  · exact okSat_pure (canon_bool _)
  · exact okSat_nested (unary_canonical _ _ _ _)
  · exact okSat_nested (binary_canonical _ _ _ _ _)
  · exact okSat_nested (comparison_canonical _ _ _ _)
  · exact okSat_pure (canon_empty _)

/-- **A non-spread value-boundary row completes at a value-boundary count**, from every state, in
    every context. -/
theorem valueRow_bounded (e : Expr) (h : valueRow e = true) (hsp : ¬ ∃ x, e = .sequenceSpread x)
    (ctx : EvalCtx) (env : ValEnv) : OkSat Bounded (evalCounted e ctx env) := by
  cases hs : scalarRow e
  · refine okSat_call (.evalCounted e ctx env) Bounded ?_
    show OkSat _ (EvalBody.evalCounted evalUnbounded e ctx env)
    cases e <;> simp [valueRow, scalarRow] at h hs <;> dsimp only [EvalBody.evalCounted]
    · refine okSat_nested (okSat_bind fun o => ?_)
      split
      · exact okSat_bind fun _ => okSat_bind fun _ => okSat_pure (valueCount_le _)
      · refine okSat_bind fun _ => okSat_bind fun _ => ?_
        split <;> exact okSat_bind fun _ => okSat_pure (valueCount_le _)
    · exact okSat_nested (construct_bounded _ _ _)
    · exact absurd ⟨_, rfl⟩ hsp
    · exact okSat_nested (listLiteral_bounded _ _ _)
    · split
      · refine okSat_bind fun _ => ?_
        split
        · exact okSat_error _
        · exact okSat_missingCtx _ (okSat_bind fun _ => okSat_pure (valueCount_le _))
      · exact okSat_error _
    · refine okSat_bind fun _ => ?_
      split
      · exact okSat_error _
      · exact okSat_bind fun _ => okSat_pure (valueCount_le _)
    · exact okSat_bind fun r => okSat_pure (valueCount_le r)
  · exact okSat_mono (fun _ h => Canonical.bounded h) (scalarRow_canonical e hs ctx env)

/-! ## 4. Discharging the row premises -/

theorem rowBoundary_of_valueRow (e : Expr) (h : valueRow e = true) (ctx : EvalCtx) (env : ValEnv)
    (s : EvalState) (out : CountedResult) (t : EvalState)
    (hrun : (evalCounted e ctx env).runState s = (.ok out, t)) : RowBoundary e out := by
  by_cases hsp : ∃ x, e = .sequenceSpread x
  · exact .inl hsp
  · exact .inr (valueRow_bounded e h hsp ctx env s out t hrun)

/-- **Value-boundary rows are bounded on every run**: from every state, in every context. -/
theorem boundedRows_of_valueRows (ctx : EvalCtx) (env : ValEnv) :
    ∀ (rows : List Expr) (s : EvalState), (∀ e ∈ rows, valueRow e = true) → BoundedRows ctx env rows s := by
  intro rows
  induction rows with
  | nil => intro _ _; trivial
  | cons e rest ih =>
    intro s h
    unfold BoundedRows
    split
    · rename_i out t hrun
      exact ⟨rowBoundary_of_valueRow e (h e (by simp)) ctx env s out t hrun,
        ih t (fun x hx => h x (by simp [hx]))⟩
    · trivial

/-- A body whose written rows all satisfy `row`. -/
def RowsBy (row : Expr → Bool) (a : Algorithm) : Prop := ∀ e ∈ a.output, row e = true

theorem RowsBy.value_of_scalar {a : Algorithm} (h : RowsBy scalarRow a) : RowsBy valueRow a :=
  fun e he => valueRow_of_scalarRow (h e he)

/-- **`UserRowsBounded` IS DISCHARGED for every user step whose rows are value-boundary rows**, for
    every context, value environment, supply and state. -/
theorem userRowsBounded_of_valueRows (a : Algorithm) (h : RowsBy valueRow a) (ctx : EvalCtx)
    (env : ValEnv) (cells : List Nat) (s : EvalState) : UserRowsBounded a ctx env cells s :=
  fun _ _ _ _ _ _ => boundedRows_of_valueRows _ _ _ _ h

/-- A clause body in the ordinary-call domain: a user body with written output and no duplicate
    property, whose rows satisfy `row`. -/
structure ClauseBy (row : Expr → Bool) (b : Algorithm) : Prop where
  user : ∃ p pp o pr e rows d, b = .mk p pp o pr (e :: rows) d
  props : b.findDuplicatePropName = none
  rows : RowsBy row b

theorem ClauseBy.withParent {row : Expr → Bool} {b : Algorithm} (h : ClauseBy row b)
    (q : Option ScopeCtx) : ClauseBy row (b.withParent q) := by
  obtain ⟨p, pp, o, pr, e, rows, d, rfl⟩ := h.user
  have hp := h.props
  have hr := h.rows
  unfold Algorithm.withParent
  split <;> (rename_i heq; cases heq) <;>
    exact ⟨⟨_, _, _, _, _, _, _, rfl⟩, hp, hr⟩

theorem ClauseBy.passes {row : Expr → Bool} {b : Algorithm} (h : ClauseBy row b) : Passes b := by
  obtain ⟨p, pp, o, pr, e, rows, d, rfl⟩ := h.user
  exact check_user_passes _ _ _ _ _ _ _ h.props rfl

theorem ClauseBy.notBuiltin {row : Expr → Bool} {b : Algorithm} (h : ClauseBy row b) : NotBuiltin b := by
  obtain ⟨p, pp, o, pr, e, rows, d, rfl⟩ := h.user
  intro b' hb; cases hb

/-- A successful clause search ends in ONE activation of one of the searched clauses. -/
theorem choose_ok {β : Type} (k : NeedCapabilities EvalM) (cells : List Nat) (name : String)
    (activate : CondBranch → NeedEnv → EvalM β) :
    ∀ (branches : List CondBranch) (s : EvalState) (p : β) (t : EvalState),
      (NeedBinder.chooseBranch k cells name activate branches).runState s = (.ok p, t) →
      ∃ branch ∈ branches, ∃ bindings u, (activate branch bindings).runState u = (.ok p, t) := by
  intro branches
  induction branches with
  | nil => intro s p t h; cases h
  | cons br rest ih =>
    intro s p t h
    unfold NeedBinder.chooseBranch at h
    rw [EvalM.bind_runState] at h
    rcases hb : (NeedBinder.bindPatterns k (needClauseHead br.pattern) cells true).runState s with
      ⟨_ | (_ | bindings), u⟩
    · rw [hb] at h; cases h
    · rw [hb] at h
      obtain ⟨b', hb', rest'⟩ := ih u p t h
      exact ⟨b', by simp [hb'], rest'⟩
    · rw [hb] at h
      exact ⟨br, by simp, bindings, u, h⟩

theorem activate_ok (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) (br : CondBranch) (bindings : NeedEnv) :
    OkSat (fun p : Activation => ∃ q, p.1 = br.body.withParent q) (needActivateBranch a ctx env br bindings) := by
  unfold needActivateBranch
  refine okSat_bind fun next => ?_
  refine okSat_bind_of (Q := fun body => ∃ q, body = br.body.withParent q) ?_ fun body hb => okSat_pure hb
  unfold wireSelectedBranchBody
  exact okSat_bind fun _ => okSat_pure ⟨_, rfl⟩

/-- Every activation the production dispatcher completes with is a searched clause's body, wired
    under the family. -/
theorem select_ok (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) (cells : List Nat) (name : String)
    (s : EvalState) (p : Activation) (t : EvalState)
    (h : (selectNeedFamilyBranch bindingChannels a cells ctx env name).runState s = (.ok p, t)) :
    ∃ br ∈ a.branches, ∃ q, p.1 = br.body.withParent q := by
  change (NeedBinder.selectFamily bindingChannels.capabilities a cells name
    (needActivateBranch a ctx env)).runState s = _ at h
  unfold NeedBinder.selectFamily at h
  split at h
  · first | cases h | (rw [EvalM.bind_runState] at h; cases h)
  · simp only [] at h
    split at h
    · first | cases h | (rw [EvalM.bind_runState] at h; cases h)
    · obtain ⟨br, hbr, bindings, u, hact⟩ := choose_ok _ cells name _ _ s p t h
      exact ⟨br, hbr, activate_ok a ctx env br bindings u p t hact⟩

/-- **`FamilyRowsBounded` IS DISCHARGED for every clause family whose clause bodies are user bodies
    with value-boundary rows**, for every context, value environment, supply, name and state. -/
theorem familyRowsBounded_of_clauses (a : Algorithm) (h : ∀ br ∈ a.branches, ClauseBy valueRow br.body)
    (ctx : EvalCtx) (env : ValEnv) (cells : List Nat) (name : String) (s : EvalState) :
    FamilyRowsBounded a ctx env cells name s := by
  intro p t hp
  obtain ⟨br, hbr, q, hq⟩ := select_ok a ctx env cells name s p t hp
  have hc := (h br hbr).withParent q
  rw [← hq] at hc
  exact ⟨hc.notBuiltin, hc.passes, boundedRows_of_valueRows _ _ _ _ hc.rows⟩

/-! ## 5. Canonical slots -/

/-- Every slot of a row supply is canonical. -/
def CanonSlots (ys : List Result) : Prop := ∀ y ∈ ys, y.normalize = y

theorem scalarRow_not_spread {e : Expr} (h : scalarRow e = true) : ¬ ∃ x, e = .sequenceSpread x := by
  rintro ⟨x, rfl⟩; simp [scalarRow] at h

/-- Scalar rows supply canonical slots, one per row, on every completed run. -/
theorem formRows_canonical (ctx : EvalCtx) (env : ValEnv) :
    ∀ (rows : List Expr), (∀ e ∈ rows, scalarRow e = true) →
      OkSat CanonSlots (OutputRows.formLeftToRight (formOutputRow ctx env) rows) := by
  intro rows
  induction rows with
  | nil => intro _ s ys t h; cases h; intro y hy; cases hy
  | cons e rest ih =>
    intro hr s ys t h
    unfold OutputRows.formLeftToRight at h
    rw [EvalM.bind_runState, formOutputRow_run] at h
    rcases hrun : (evalCounted e ctx env).runState s with ⟨_ | out, u⟩
    · rw [hrun] at h; cases h
    · rw [hrun] at h
      dsimp only at h
      have hse := hr e (by simp)
      have hc := scalarRow_canonical e hse ctx env s out u hrun
      rw [items_plain e out (scalarRow_not_spread hse) hc.1, EvalM.bind_runState] at h
      rcases hrest : (OutputRows.formLeftToRight (formOutputRow ctx env) rest).runState u with ⟨_ | ys', v⟩
      · rw [hrest] at h; cases h
      · rw [hrest] at h
        cases h
        intro y hy
        simp only [List.singleton_append, List.mem_cons] at hy
        rcases hy with rfl | hy
        · exact hc.2
        · exact ih (fun x hx => hr x (by simp [hx])) u ys' _ hrest y hy

/-- A checked non-builtin body with scalar rows reads canonical slots. -/
theorem slots_canonical_of_body (b : Algorithm) (hn : NotBuiltin b) (hp : Passes b)
    (hr : RowsBy scalarRow b) (ctx : EvalCtx) (env : ValEnv) :
    OkSat CanonSlots (evalAlgOutputSlots b ctx env) := by
  intro s ys t h
  have hbody : (EvalBody.evalAlgOutputSlots evalUnbounded b ctx env).runState s =
      (OutputRows.formLeftToRight (formOutputRow (enteredCtx b ctx s) env) b.output).runState
        (enteredState b ctx env s) :=
    readRows_entered (EvalRec.formOutputRow evalUnbounded) _ _ b hn hp ctx env s
  have hc : ProductionCompletes (evalUnbounded (.evalAlgOutputSlots b ctx env)) s := by
    unfold ProductionCompletes
    show ((evalAlgOutputSlots b ctx env).runState s).1 ≠ _
    rw [h]; nofun
  have hu := production_unfolds _ s hc
  have h' : (OutputRows.formLeftToRight (formOutputRow (enteredCtx b ctx s) env) b.output).runState
      (enteredState b ctx env s) = (.ok ys, t) := by
    rw [← hbody]; exact hu.trans h
  exact formRows_canonical _ _ _ hr _ _ _ h'

theorem userActivation_fst (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) (cells : List Nat) :
    OkSat (fun p : Activation => p.1 = a) (userActivation a ctx env cells evalUnbounded) := by
  unfold userActivation
  refine okSat_bind fun o => ?_
  split
  · exact okSat_bind fun _ => okSat_pure rfl
  · exact okSat_throw _

/-- **The canonical-slot premise IS DISCHARGED for a user step with scalar rows.** -/
theorem user_slots_canonical (a : Algorithm) (h : UserStep a) (hr : RowsBy scalarRow a) (ctx : EvalCtx)
    (env : ValEnv) (cells : List Nat) (name : String) :
    OkSat CanonSlots (runNeedStepSlots a ctx env cells name) := by
  refine okSat_call (.runNeedStepSlots a ctx env cells name) CanonSlots ?_
  rw [user_loop_body a h ctx env cells name evalUnbounded]
  unfold loopRead
  refine okSat_bind_of (userActivation_fst a ctx env cells) fun p hp => ?_
  obtain ⟨b, c', e'⟩ := p
  dsimp only at hp
  subst hp
  have hn : NotBuiltin b := by
    obtain ⟨_, _, _, _, _, _, _, rfl⟩ := h.user
    intro b' hb; cases hb
  exact slots_canonical_of_body b hn h.checks hr c' e'

/-- **The canonical-slot premise IS DISCHARGED for a clause family whose clause bodies have scalar
    rows.** -/
theorem family_slots_canonical (p : Option ScopeCtx) (o : List Expr) (br : List CondBranch)
    (d : Option PropertyIdentity) (h : ∀ b ∈ br, ClauseBy scalarRow b.body) (ctx : EvalCtx) (env : ValEnv)
    (cells : List Nat) (name : String) :
    OkSat CanonSlots (runNeedStepSlots (.conditional p o br d) ctx env cells name) := by
  refine okSat_call (.runNeedStepSlots (.conditional p o br d) ctx env cells name) CanonSlots ?_
  rw [family_loop_body p o br d ctx env cells name evalUnbounded]
  refine okSat_withCtx _ ?_
  unfold loopRead
  refine okSat_bind_of (Q := fun q : Activation => ∃ b ∈ br, ∃ w, q.1 = b.body.withParent w)
    (fun s q t hq => select_ok _ ctx env cells name s q t hq) fun q hq => ?_
  obtain ⟨b, hb, w, hw⟩ := hq
  obtain ⟨body, c', e'⟩ := q
  dsimp only at hw
  subst hw
  have hc := (h b hb).withParent w
  exact slots_canonical_of_body _ hc.notBuiltin hc.passes hc.rows c' e'

/-! ## 6. `Step(args).repeat(1) = Step(args)` on the widened domain -/

/-- A successful ordinary call determines the loop's value AND its whole final state. The reverse
    direction uses completion agreement to recover the successful slot run; it assumes no loop
    success. -/
theorem value_state_of_agreement {wrap : Error → Error} {L : Except Error (List Result) × EvalState}
    {O : Except Error CountedResult × EvalState} (hag : StepAgreement wrap L O)
    (hcan : ∀ ys t, L = (.ok ys, t) → CanonSlots ys) (v : CountedResult) (t : EvalState)
    (ho : O = (.ok v, t)) :
    ∃ ys, L = (.ok ys, t) ∧ oneRoundOutcome L = (.ok v, pushCompleted t ys) := by
  have hc : L.1 ≠ .error .fuelExhausted := hag.completes.2 (by rw [ho]; nofun)
  rcases hl : L with ⟨_ | ys, u⟩
  · rename_i e
    have he : e ≠ .fuelExhausted := by intro he; apply hc; rw [hl, he]
    obtain ⟨e₀, _, he₀⟩ := hag.error e u he hl
    rw [ho] at he₀
    cases he₀
  · have hv := hag.ok ys u hl
    rw [ho] at hv
    cases hv
    refine ⟨ys, rfl, ?_⟩
    simp only [oneRoundOutcome, loop_value_of_canonical ys (hcan ys t hl)]

/-- A one-round loop completes with `v` iff the ordinary call completes with `v`. In particular,
    the right side contains only the ordinary call, with no loop-success premise. -/
theorem value_iff_of_agreement {wrap : Error → Error} {L : Except Error (List Result) × EvalState}
    {O : Except Error CountedResult × EvalState} (hag : StepAgreement wrap L O)
    (hcan : ∀ ys t, L = (.ok ys, t) → CanonSlots ys) (v : CountedResult) :
    (∃ u, oneRoundOutcome L = (.ok v, u)) ↔ (∃ t, O = (.ok v, t)) := by
  constructor
  · rintro ⟨u, hu⟩
    rcases L with ⟨_ | ys, t⟩
    · cases hu
    · simp only [oneRoundOutcome] at hu
      cases hu
      refine ⟨t, ?_⟩
      rw [hag.ok ys t rfl, loop_value_of_canonical ys (hcan ys t rfl)]
  · rintro ⟨t, ho⟩
    obtain ⟨ys, _, hR⟩ := value_state_of_agreement hag hcan v t ho
    exact ⟨_, hR⟩

/-- **COUNT ONE, BY VALUE (user step with scalar rows).** For every user step whose written rows
    are scalar rows, from the projected step: `repeat` of count one completes with `v` iff the
    ordinary call over the same cells completes with the SAME `v`; the loop state is the call
    state plus the completed slot cells. The only premise left is the step projection. -/
theorem count_one_user_value (step : ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv)
    (name : String) (cells : List Nat) (s s₁ : EvalState) (a : Algorithm)
    (hi : (invokeNeed step).runState s = (.ok (some a), s₁)) (h : UserStep a) (hr : RowsBy scalarRow a)
    (v : CountedResult) :
    (∃ u, (repeatAfterSetup evalUnbounded step ctx env name 1 cells).runState s = (.ok v, u)) ↔
      (∃ t, (evalNeedUserSupply a cells ctx env).runState s₁ = (.ok v, t)) := by
  obtain ⟨hag, heq⟩ := count_one_user step ctx env name cells s s₁ a hi h
    (userRowsBounded_of_valueRows a hr.value_of_scalar ctx env cells s₁)
  rw [heq]
  exact value_iff_of_agreement hag (fun ys t hL => user_slots_canonical a h hr ctx env cells name s₁ ys t hL) v

/-- **COUNT ONE, BY VALUE (clause family with scalar-row clause bodies).** -/
theorem count_one_family_value (step : ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv)
    (name : String) (cells : List Nat) (s s₁ : EvalState) (p : Option ScopeCtx) (o : List Expr)
    (br : List CondBranch) (d : Option PropertyIdentity)
    (hi : (invokeNeed step).runState s = (.ok (some (.conditional p o br d)), s₁))
    (h : ∀ b ∈ br, ClauseBy scalarRow b.body) (v : CountedResult) :
    (∃ u, (repeatAfterSetup evalUnbounded step ctx env name 1 cells).runState s = (.ok v, u)) ↔
      (∃ t, (evalNeedFamilySupply (.conditional p o br d) cells ctx env name).runState s₁ = (.ok v, t)) := by
  have hv : ∀ b ∈ br, ClauseBy valueRow b.body := fun b hb =>
    ⟨(h b hb).user, (h b hb).props, (h b hb).rows.value_of_scalar⟩
  obtain ⟨hag, heq⟩ := count_one_family step ctx env name cells s s₁ p o br d hi
    (familyRowsBounded_of_clauses (.conditional p o br d) hv ctx env cells name s₁)
  rw [heq]
  exact value_iff_of_agreement hag
    (fun ys t hL => family_slots_canonical p o br d h ctx env cells name s₁ ys t hL) v

/-! ## 7. Builtin steps: the value -/

/-- The one-slot loop value of a canonical slot is that slot re-counted at the value boundary. -/
theorem loop_value_one_slot (out : CountedResult) (h : out.fst.normalize = out.fst) :
    loopResultCounted [out.fst] = reCountValueBoundary out := by
  have hv : loopStateResult [out.fst] = out.fst := by
    unfold loopStateResult
    rw [show Result.normalize (.sequenceValue [out.fst]) = out.fst.normalize by simp [Result.normalize], h]
  simp only [loopResultCounted, reCountValueBoundary, hv]

/-- **A BUILTIN STEP ROUND, BY VALUE.** Wherever the builtin application over the step arguments
    completes, the step round is that application outcome: its ONE result as ONE slot, in the
    SAME state; an ordinary error is the same error under the step call frame. -/
theorem builtin_step_value (b : Builtin) (ctx : EvalCtx) (env : ValEnv) (cells : List Nat) (name : String)
    (s : EvalState) (x : Except Error CountedResult) (t : EvalState)
    (hx : x ≠ .error .fuelExhausted)
    (h : (applyBuiltinCountedResolved b (stepArguments cells) ctx env).runState s = (x, t)) :
    (runNeedStepSlots (.builtin b) ctx env cells name).runState s =
      builtinStepOutcome s!"while evaluating call to {name}" (x, t) := by
  have hc : ProductionCompletes (applyBuiltinCountedResolved b (stepArguments cells) ctx env) s := by
    unfold ProductionCompletes; rw [h]; exact hx
  rw [(builtin_step_run b ctx env cells name s).2 hc, h]

/-- **COUNT ONE, BY VALUE (builtin step).** From the projected builtin step: whatever completed
    outcome the ordinary call `F(args)` over the same cells has (any callee origin), the one-round
    `repeat` is determined by it. A result `out` gives `loopResultCounted [out.fst]` over the call
    state plus one completed slot cell; an ordinary error is the same error under the step call
    frame, in the same state. No builtin is excluded. -/
theorem count_one_builtin (step : ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) (name : String)
    (cells : List Nat) (s s₁ : EvalState) (b : Builtin) (origin : CalleeOrigin)
    (hi : (invokeNeed step).runState s = (.ok (some (.builtin b)), s₁))
    (x : Except Error CountedResult) (t : EvalState) (hx : x ≠ .error .fuelExhausted)
    (hcall : (evalSuppliedCallCounted origin (.builtin b) (cells.map fun c => (c, none)) ctx env name).runState s₁ = (x, t)) :
    (repeatAfterSetup evalUnbounded step ctx env name 1 cells).runState s =
      oneRoundOutcome (builtinStepOutcome s!"while evaluating call to {name}" (x, t)) := by
  rw [ordinary_builtin_is_step_application] at hcall
  rw [repeat_one_round step ctx env name cells s s₁ _ hi, builtin_step_value b ctx env cells name s₁ x t hx hcall]

/-- The success case of `count_one_builtin`: on a canonical result, `repeat(1)` IS the call value
    at its value boundary. -/
theorem count_one_builtin_ok (step : ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) (name : String)
    (cells : List Nat) (s s₁ : EvalState) (b : Builtin) (origin : CalleeOrigin)
    (hi : (invokeNeed step).runState s = (.ok (some (.builtin b)), s₁))
    (out : CountedResult) (t : EvalState) (hcan : out.fst.normalize = out.fst)
    (hcall : (evalSuppliedCallCounted origin (.builtin b) (cells.map fun c => (c, none)) ctx env name).runState s₁ = (.ok out, t)) :
    (repeatAfterSetup evalUnbounded step ctx env name 1 cells).runState s =
      (.ok (reCountValueBoundary out), pushCompleted t [out.fst]) := by
  rw [count_one_builtin step ctx env name cells s s₁ b origin hi (.ok out) t nofun hcall]
  show (Except.ok (loopResultCounted [out.fst]), _) = _
  rw [loop_value_one_slot out hcan]
  rfl

/-- Scalar results are canonical: every numeric, Boolean and string result of a builtin. -/
theorem scalar_canonical (r : Result) (h : (∃ n, r = .atom n) ∨ (∃ b, r = .bool b) ∨ (∃ x, r = .str x)) :
    r.normalize = r := by
  rcases h with ⟨n, rfl⟩ | ⟨b, rfl⟩ | ⟨x, rfl⟩ <;> simp [Result.normalize]

/-! ### Specified results, rather than assuming the builtin application's result

These laws expand the installed production arms. `count` covers an ordinary prepared collection
(not an argument view or retained collector); `if` covers either Boolean condition and demands
only the chosen branch. Their premises are the lower-level argument operations, not the result
of the builtin call. Other builtins retain the general application-relative theorem above.
-/

theorem production_ok_of_body (c : EvalCall) (B : EvalRec → EvalM c.Ret)
    (hstep : ∀ rec, evalStep rec c = B rec) (hB : Finite B) (s t : EvalState) (v : c.Ret)
    (h : (B evalUnbounded).runState s = (.ok v, t)) :
    (evalUnbounded c).runState s = (.ok v, t) :=
  (production_eq_of_finite c B hstep hB s (by unfold ProductionCompletes; rw [h]; nofun)).trans h

theorem resolved_builtin_eq (b : Builtin) (args : List ResolvedArgumentAlgorithm)
    (ctx : EvalCtx) (env : ValEnv) :
    applyBuiltinCountedResolved b args ctx env = applyBuiltinCounted b args ctx env :=
  (delegation_equation (.applyBuiltinCountedResolved b args ctx env)
    (.applyBuiltinCounted b args ctx env) pure
    (fun _ => (Eq.trans (by rfl) (bind_pure_eq _).symm)) (fun _ _ => nofun)).trans (bind_pure_eq _)

/-- `count` of a prepared ordinary collection is its top-level length, with no additional work
    after argument binding. Views and retained collectors have separate selective routes. -/
theorem count_application_value (args : List ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv)
    (s t : EvalState) (bound : BoundSequenceBuiltinArguments)
    (hb : (evalUnbounded (.bindSequenceBuiltinArguments .countBuiltin {} args ctx env)).runState s =
      (.ok bound, t)) (hv : bound.view? = none) (hs : bound.slice? = none) :
    (applyBuiltinCountedResolved .countBuiltin args ctx env).runState s =
      (.ok (.atom (Int.ofNat bound.preparedInput.items.length), 1), t) := by
  let B := fun rec : EvalRec => EvalBody.applyBuiltinCountedSequence rec .countBuiltin {} args ctx env
  have hf : Finite B := by
    unfold B EvalBody.applyBuiltinCountedSequence
    refine finite_bind (finite_call _) fun b => ?_
    split
    · exact finite_call _
    · split
      · unfold retainedCollectorBuiltin
        dsimp only
        unfold argumentViewBuiltin
        exact finite_bind (finite_const _) (fun _ => finite_const _)
      · exact finite_const _
  have hseq := production_ok_of_body (.applyBuiltinCountedSequence .countBuiltin {} args ctx env) B
    (fun _ => rfl) hf s t (.atom (Int.ofNat bound.preparedInput.items.length), 1) (by
      unfold B EvalBody.applyBuiltinCountedSequence
      simp only [EvalRec.bindSequenceBuiltinArguments]
      rw [EvalM.bind_runState, hb]
      simp only [hv, hs]
      rfl)
  rw [resolved_builtin_eq]
  exact production_ok_of_body (.applyBuiltinCounted .countBuiltin args ctx env)
    (fun rec => withNestedMissingOutput (rec (.applyBuiltinCountedSequence .countBuiltin {} args ctx env)))
    (fun _ => rfl) (finite_nested (finite_call _)) s t _ (by rw [nested_run, hseq])

/-- The count step's specified result: the collection's length, with one completed numeric slot
    appended to the state left by collection argument binding. -/
theorem count_one_count_value (step : ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv)
    (name : String) (cells : List Nat) (s s₁ t : EvalState) (bound : BoundSequenceBuiltinArguments)
    (hi : (invokeNeed step).runState s = (.ok (some (.builtin .countBuiltin)), s₁))
    (hb : (evalUnbounded (.bindSequenceBuiltinArguments .countBuiltin {} (stepArguments cells) ctx env)).runState s₁ =
      (.ok bound, t)) (hv : bound.view? = none) (hs : bound.slice? = none) :
    (repeatAfterSetup evalUnbounded step ctx env name 1 cells).runState s =
      (.ok (.atom (Int.ofNat bound.preparedInput.items.length), 1),
        pushCompleted t [.atom (Int.ofNat bound.preparedInput.items.length)]) := by
  have hcall := count_application_value (stepArguments cells) ctx env s₁ t bound hb hv hs
  rw [repeat_one_round step ctx env name cells s s₁ _ hi,
    builtin_step_value .countBuiltin ctx env cells name s₁ (.ok _) t nofun hcall]
  simp [oneRoundOutcome, builtinStepOutcome, loopStepBuiltinRows, Result.normalize,
    loopResultCounted, loopStateResult, reCountValueBoundary, Result.valueCount]

/-- The installed `if` arm returns the chosen branch's value and re-counts it. Nothing is assumed
    about the unselected branch; it is never evaluated by this equation. -/
theorem if_application_value (cond yes no : ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv)
    (s s₁ t : EvalState) (flag : Bool) (out : CountedResult)
    (hc : (evalUnbounded (.evalArgumentValue cond ctx env)).runState s = (.ok (.bool flag), s₁))
    (hb : (evalUnbounded (.evalArgumentValueCounted (if flag then yes else no) ctx env)).runState s₁ = (.ok out, t)) :
    (applyBuiltinCountedResolved .ifBuiltin [cond, yes, no] ctx env).runState s =
      (.ok (reCountValueBoundary out), t) := by
  let B := fun rec : EvalRec => withNestedMissingOutput (rec (.evalArgumentValue cond ctx env) >>= fun r =>
    match r.asBool? with
    | some false => rec (.evalArgumentValueCounted no ctx env) >>= fun out => pure (reCountValueBoundary out)
    | some true => rec (.evalArgumentValueCounted yes ctx env) >>= fun out => pure (reCountValueBoundary out)
    | none => EvalM.error (.typeMismatch (booleanRequiredMessage "if condition" r)))
  have hf : Finite B := by
    refine finite_nested (finite_bind (finite_call _) fun r => ?_)
    cases r.asBool? with
    | none => exact finite_const _
    | some b => cases b <;> exact finite_bind (finite_call _) (fun _ => finite_const _)
  rw [resolved_builtin_eq]
  exact production_ok_of_body (.applyBuiltinCounted .ifBuiltin [cond, yes, no] ctx env) B
    (fun _ => rfl) hf s t _ (by
      change (withNestedMissingOutput _).runState s = _
      rw [nested_run, EvalM.bind_runState, hc]
      cases flag with
      | false =>
        have hno : (evalUnbounded (.evalArgumentValueCounted no ctx env)).runState s₁ = (.ok out, t) := by
          simpa using hb
        dsimp only [Result.asBool?]
        rw [EvalM.bind_runState, hno]
        rfl
      | true =>
        have hyes : (evalUnbounded (.evalArgumentValueCounted yes ctx env)).runState s₁ = (.ok out, t) := by
          simpa using hb
        dsimp only [Result.asBool?]
        rw [EvalM.bind_runState, hyes]
        rfl)

/-- One source-free argument backed by an already supplied cell, as in `stepArguments`. -/
def stepCellArgument (c : Nat) : ResolvedArgumentAlgorithm :=
  { algorithm := Algorithm.ofExpr (.emptySequence 0), need? := some c }

/-- The lazy `if` step has the selected branch's value. Canonical selected values include all
    scalar results; the unselected branch may fail or diverge. -/
theorem count_one_if_value (step : ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv)
    (name : String) (c y n : Nat) (s s₁ s₂ t : EvalState) (flag : Bool) (out : CountedResult)
    (hi : (invokeNeed step).runState s = (.ok (some (.builtin .ifBuiltin)), s₁))
    (hc : (evalUnbounded (.evalArgumentValue (stepCellArgument c) ctx env)).runState s₁ = (.ok (.bool flag), s₂))
    (hb : (evalUnbounded (.evalArgumentValueCounted (stepCellArgument (if flag then y else n)) ctx env)).runState s₂ = (.ok out, t))
    (hcan : out.fst.normalize = out.fst) :
    (repeatAfterSetup evalUnbounded step ctx env name 1 [c, y, n]).runState s =
      (.ok (reCountValueBoundary out), pushCompleted t [out.fst]) := by
  have hcall := if_application_value (stepCellArgument c) (stepCellArgument y)
    (stepCellArgument n) ctx env s₁ s₂ t flag out hc (by cases flag <;> exact hb)
  have hargs : [stepCellArgument c, stepCellArgument y, stepCellArgument n] =
      stepArguments [c, y, n] := rfl
  rw [hargs] at hcall
  rw [repeat_one_round step ctx env name [c, y, n] s s₁ _ hi,
    builtin_step_value .ifBuiltin ctx env [c, y, n] name s₁ (.ok _) t nofun hcall]
  show (Except.ok (loopResultCounted [out.fst]), _) = _
  rw [loop_value_one_slot out hcan]
  rfl

/-! ## 8. Alias steps: the value, through the target -/

/-- Two production runs related by a resolved prefix: they complete together and, when they
    complete, are equal. -/
structure Forwards {α : Type} (L L' : Except Error α × EvalState) : Prop where
  completes : L.1 ≠ .error .fuelExhausted ↔ L'.1 ≠ .error .fuelExhausted
  eq : L'.1 ≠ .error .fuelExhausted → L = L'

/-- A step agreement transported along forwarding runs on both sides. -/
theorem StepAgreement.forward {wrap : Error → Error} {L L' : Except Error (List Result) × EvalState}
    {O O' : Except Error CountedResult × EvalState} (hag : StepAgreement wrap L' O')
    (hL : Forwards L L') (hO : Forwards O O') : StepAgreement wrap L O := by
  refine ⟨hL.completes.trans (hag.completes.trans hO.completes.symm), ?_, ?_⟩
  · intro ys t hl
    have hc' : L'.1 ≠ .error .fuelExhausted := hL.completes.1 (by rw [hl]; nofun)
    have hl' : L' = (.ok ys, t) := by rw [← hL.eq hc', hl]
    have ho' := hag.ok ys t hl'
    rw [hO.eq (hag.completes.1 hc'), ho']
  · intro e t he hl
    have hc' : L'.1 ≠ .error .fuelExhausted := hL.completes.1 (by rw [hl]; intro h'; apply he; injection h')
    have hl' : L' = (.error e, t) := by rw [← hL.eq hc', hl]
    obtain ⟨e₀, he₀, ho'⟩ := hag.error e t he hl'
    refine ⟨e₀, he₀, ?_⟩
    rw [hO.eq (hag.completes.1 hc'), ho']

/-- **THE LOOP RECEIVER FORWARDS AN ALIAS STEP TO ITS TARGET.** Once the alias resolves to `target`,
    the alias step round and the target step round, from the resolved state, complete together
    and are then equal. -/
theorem alias_loop_forwards (p : Option ScopeCtx) (o : List Expr) (pr : List PropDef) (tg : Expr)
    (d : Option PropertyIdentity) (rf : Bool) (ctx : EvalCtx) (env : ValEnv) (cells : List Nat)
    (name : String) (s : EvalState) (target : Algorithm) (s' : EvalState)
    (hres : (resolveAliasTarget (.alias p o pr tg d rf) ctx).runState s = (.ok target, s')) :
    Forwards ((runNeedStepSlots (.alias p o pr tg d rf) ctx env cells name).runState s)
      ((runNeedStepSlots target ctx env cells name).runState s') := by
  have hstep : ∀ rec, evalStep rec (.runNeedStepSlots (.alias p o pr tg d rf) ctx env cells name) =
      (fun rec => rec (.resolveAliasTarget (.alias p o pr tg d rf) ctx) >>= fun target =>
        rec (.runNeedStepSlots target ctx env cells name)) rec := fun _ => rfl
  have hfin : Finite (fun rec => rec (.resolveAliasTarget (.alias p o pr tg d rf) ctx) >>= fun target =>
      rec (.runNeedStepSlots target ctx env cells name)) :=
    finite_bind (finite_call _) (fun _ => finite_call _)
  have hbody : (resolveAliasTarget (.alias p o pr tg d rf) ctx >>= fun target =>
      runNeedStepSlots target ctx env cells name).runState s =
      (runNeedStepSlots target ctx env cells name).runState s' := by
    rw [EvalM.bind_runState, hres]
  refine ⟨?_, fun hc => ?_⟩
  · have := production_completes_iff_body _ _ hstep hfin s
    unfold ProductionCompletes at this
    exact this.trans (Iff.of_eq (congrArg (fun x => x.1 ≠ _) hbody))
  · exact (production_eq_of_finite _ _ hstep hfin s
      (by unfold ProductionCompletes; exact (congrArg (fun x => x.1 ≠ _) hbody).mpr hc)).trans hbody

/-- **THE ORDINARY CALL FORWARDS AN ALIAS CALLEE TO ITS TARGET** over the same supply. -/
theorem alias_call_forwards (origin : CalleeOrigin) (p : Option ScopeCtx) (o : List Expr) (pr : List PropDef)
    (tg : Expr) (d : Option PropertyIdentity) (rf : Bool) (cells : List NeedSupply.Sourced) (ctx : EvalCtx)
    (env : ValEnv) (name : String) (s : EvalState) (target : Algorithm) (s' : EvalState)
    (hres : (resolveAliasTarget (.alias p o pr tg d rf) ctx).runState s = (.ok target, s')) :
    Forwards ((evalSuppliedCallCounted origin (.alias p o pr tg d rf) cells ctx env name).runState s)
      ((evalSuppliedCallCounted origin target cells ctx env name).runState s') := by
  have hstep : ∀ rec, evalStep rec (.evalSuppliedCallCounted origin (.alias p o pr tg d rf) cells ctx env name) =
      (fun rec => rec (.resolveAliasTarget (.alias p o pr tg d rf) ctx) >>= fun target =>
        rec (.evalSuppliedCallCounted origin target cells ctx env name)) rec := fun _ => rfl
  have hfin : Finite (fun rec => rec (.resolveAliasTarget (.alias p o pr tg d rf) ctx) >>= fun target =>
      rec (.evalSuppliedCallCounted origin target cells ctx env name)) :=
    finite_bind (finite_call _) (fun _ => finite_call _)
  have hbody : (resolveAliasTarget (.alias p o pr tg d rf) ctx >>= fun target =>
      evalSuppliedCallCounted origin target cells ctx env name).runState s =
      (evalSuppliedCallCounted origin target cells ctx env name).runState s' := by
    rw [EvalM.bind_runState, hres]
  refine ⟨?_, fun hc => ?_⟩
  · have := production_completes_iff_body _ _ hstep hfin s
    unfold ProductionCompletes at this
    exact this.trans (Iff.of_eq (congrArg (fun x => x.1 ≠ _) hbody))
  · exact (production_eq_of_finite _ _ hstep hfin s
      (by unfold ProductionCompletes; exact (congrArg (fun x => x.1 ≠ _) hbody).mpr hc)).trans hbody

/-- **AN ALIAS STEP AGAINST THE ORDINARY CALL OF THE ALIAS (user target).** Over the same non-empty
    supply and from the same state: once the alias resolves to a user step, the loop step and the
    ordinary call of the ALIAS satisfy the user step agreement. -/
theorem alias_user_step_agreement (p : Option ScopeCtx) (o : List Expr) (pr : List PropDef) (tg : Expr)
    (d : Option PropertyIdentity) (rf : Bool) (origin : CalleeOrigin) (c : NeedSupply.Sourced)
    (cs : List NeedSupply.Sourced) (ctx : EvalCtx) (env : ValEnv) (name : String) (s : EvalState)
    (target : Algorithm) (s' : EvalState)
    (hres : (resolveAliasTarget (.alias p o pr tg d rf) ctx).runState s = (.ok target, s'))
    (h : UserStep target) (hrows : UserRowsBounded target ctx env ((c :: cs).map Prod.fst) s') :
    StepAgreement id ((runNeedStepSlots (.alias p o pr tg d rf) ctx env ((c :: cs).map Prod.fst) name).runState s)
      ((evalSuppliedCallCounted origin (.alias p o pr tg d rf) (c :: cs) ctx env name).runState s) := by
  have hag := user_step_agreement target h ctx env _ name s' hrows
  have hO := alias_call_forwards origin p o pr tg d rf (c :: cs) ctx env name s target s' hres
  obtain ⟨p', pp, o', pr', e, rows, d', rfl⟩ := h.user
  rw [ordinary_user_of_nonempty] at hO
  exact StepAgreement.forward hag (alias_loop_forwards p o pr tg d rf ctx env _ name s _ s' hres) hO

/-- **COUNT ONE, BY VALUE (alias of a scalar-row user step).** From the projected alias step and
    its resolution: `repeat` of count one completes with `v` iff the ordinary call of the ALIAS over
    the same cells completes with the SAME `v`. -/
theorem count_one_alias_value (step : ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv)
    (name : String) (c : NeedSupply.Sourced) (cs : List NeedSupply.Sourced) (s s₁ : EvalState)
    (p : Option ScopeCtx) (o : List Expr) (pr : List PropDef) (tg : Expr) (d : Option PropertyIdentity)
    (rf : Bool) (origin : CalleeOrigin) (target : Algorithm) (s' : EvalState)
    (hi : (invokeNeed step).runState s = (.ok (some (.alias p o pr tg d rf)), s₁))
    (hres : (resolveAliasTarget (.alias p o pr tg d rf) ctx).runState s₁ = (.ok target, s'))
    (h : UserStep target) (hr : RowsBy scalarRow target) (v : CountedResult) :
    (∃ u, (repeatAfterSetup evalUnbounded step ctx env name 1 ((c :: cs).map Prod.fst)).runState s = (.ok v, u)) ↔
      (∃ t, (evalSuppliedCallCounted origin (.alias p o pr tg d rf) (c :: cs) ctx env name).runState s₁ = (.ok v, t)) := by
  have hag := alias_user_step_agreement p o pr tg d rf origin c cs ctx env name s₁ target s' hres h
    (userRowsBounded_of_valueRows target hr.value_of_scalar ctx env _ s')
  have hL := alias_loop_forwards p o pr tg d rf ctx env ((c :: cs).map Prod.fst) name s₁ target s' hres
  rw [repeat_one_round step ctx env name _ s s₁ _ hi]
  refine value_iff_of_agreement hag (fun ys t hl => ?_) v
  have hc' := hL.completes.1 (by rw [hl]; nofun)
  rw [hL.eq hc'] at hl
  exact user_slots_canonical target h hr ctx env _ name s' ys t hl

/-- **COUNT ONE, BY VALUE (alias of a builtin).** From the projected alias step and its resolution to
    a builtin: whatever completed outcome the ordinary call of the ALIAS over the same cells has,
    the one-round `repeat` is the builtin step outcome of it, exactly as for the builtin itself. -/
theorem count_one_alias_builtin (step : ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv)
    (name : String) (cells : List Nat) (s s₁ : EvalState) (p : Option ScopeCtx) (o : List Expr)
    (pr : List PropDef) (tg : Expr) (d : Option PropertyIdentity) (rf : Bool) (origin : CalleeOrigin)
    (b : Builtin) (s' : EvalState)
    (hi : (invokeNeed step).runState s = (.ok (some (.alias p o pr tg d rf)), s₁))
    (hres : (resolveAliasTarget (.alias p o pr tg d rf) ctx).runState s₁ = (.ok (.builtin b), s'))
    (x : Except Error CountedResult) (t : EvalState) (hx : x ≠ .error .fuelExhausted)
    (hcall : (evalSuppliedCallCounted origin (.alias p o pr tg d rf) (cells.map fun c => (c, none)) ctx env name).runState s₁ = (x, t)) :
    (repeatAfterSetup evalUnbounded step ctx env name 1 cells).runState s =
      oneRoundOutcome (builtinStepOutcome s!"while evaluating call to {name}" (x, t)) := by
  have hO := alias_call_forwards origin p o pr tg d rf (cells.map fun c => (c, none)) ctx env name s₁ _ s' hres
  have hOc : ((evalSuppliedCallCounted origin (.alias p o pr tg d rf) (cells.map fun c => (c, none)) ctx env name).runState s₁).1 ≠
      .error .fuelExhausted := by rw [hcall]; exact hx
  have hcall' := (hO.eq (hO.completes.1 hOc)).symm.trans hcall
  rw [ordinary_builtin_is_step_application] at hcall'
  have hstep := builtin_step_value b ctx env cells name s' x t hx hcall'
  have hL := alias_loop_forwards p o pr tg d rf ctx env cells name s₁ _ s' hres
  have hLc : ((runNeedStepSlots (.builtin b) ctx env cells name).runState s').1 ≠ .error .fuelExhausted := by
    rw [hstep]
    rcases x with e | out
    · cases e <;> first | exact absurd rfl hx | simp [builtinStepOutcome]
    · exact nofun
  rw [repeat_one_round step ctx env name cells s s₁ _ hi, hL.eq hLc, hstep]

end KatLang.FiniteLoopSurface
