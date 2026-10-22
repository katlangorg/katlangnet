import Lean
import KatLangArityLaws.EvaluatorCore
import KatLangArityLaws.EvaluatorCacheLaws
import KatLangArityLaws.EvaluatorDiscipline
import KatLangArityLaws.WhileRound
import KatLangArityLaws.NeedControl

open KatLang KatLang.EvaluatorCore KatLang.WhileRoundLaws
open Lean.Order

/-!
# CF-4: the condition-first round at the production evaluator (S6c, October 2026)

`KatLangArityLaws/WhileRound.lean` proves the row CONTROL of a `while` round
(`WhileRound.conditionFirst`) for every row-forming capability `form`. This module connects that
control to the production evaluator: the activated-body boundary the evaluator installs, the
ordinary row formation it passes, and the production operations themselves.

* **The activated-body boundary** (`ActivatedBody.readRows`, the one TOTAL setup shared by
  `evalAlgOutputSlots` and `whileVerdictSlots`). The body checks are state-free and fail before
  anything else (`readRows_check_fails`: no entry, no row); a builtin body is one atomic counted
  value (`readRows_builtin`); otherwise the body is ENTERED ONCE and the rest of the run IS the
  reader over the ONE closure `form pushed env` from the entered state (`readRows_entered`), so
  the run depends on `form` only at that one context and environment
  (`readRows_uses_one_context`). `enterAlgorithmBody` never fails, allocates no cell, keeps the
  parameter cells (`needEnv`), binding context and property cache, and records at most one
  lexical activation (`enter_run`, `entered_*`).
* **Ordinary row formation** (`formOutputRow_is_counted_row`): the production `formOutputRow` IS
  one production `evalCounted` followed by the existing row rule `OutputRows.items` — an exact
  equation, no completion premise (the R7 delegation equation). Its outcome/state are those of
  `evalCounted`, errors unchanged (`formOutputRow_run`).
* **Finite use** (`Finite`, `FuelReached`, `production_eq_of_finite`): the R7 bridge proved only that
  a completed production outcome is its body over production (`production_unfolds`). For a body
  built by sequencing finitely many recursive calls — the row readers and the activated-body
  boundary — the CONVERSE holds too: wherever the body over production completes, production
  completes with the same outcome AND state. Hence `whileVerdictSlots_production` /
  `evalAlgOutputSlots_production`: production completes iff its activated-body run over the
  production row formation does, and then they are EQUAL.
* **Production CF laws** (`production_cf1_false_skips_earlier_rows`, `…cf2…`, `…cf5…`,
  `production_cf_all_rows_empty_no_flag`, `production_check_failure_reaches_no_row`,
  `production_builtin_body_atomic`): the existing row-control theorems composed with the boundary,
  stated about the production `whileVerdictSlots`, with the rows formed by the production
  `formOutputRow` in the ONE entered context.
* **The round's dispatch** (`runNeedWhileRound_user`, `…_family`, `…_builtin`, `…_alias`): a
  completed production round is the ONE dispatcher `runNeedStepWith` — binder or family dispatch,
  then exactly ONE production `whileVerdictSlots` of the bound/selected body (no second dispatch,
  no second body for the transitions) — or the atomic builtin route, or one alias resolution. These
  are `production_unfolds` instances and keep its completion premise (the binder's recursive
  channels are not covered by `FuelReached` here).
* **Shared cells** (`needBindingContext_run`, `completed_cell_reused_after`): the entered context's
  parameter cells are the binder's addresses; a cell completed during discovery stays completed
  with the same outcome through every later production run (`ProductionDiscipline`), and its
  production demand then returns that outcome without evaluating anything.
* **Shared caches, separately** (`cacheKey_exported_context_free`,
  `cacheKey_retained_owner_context`, `cacheKey_same_inputs`, `property_cache_hit_production`,
  `published_entry_survives`, `exported_publication_reused`): exported keys are run-scoped; a
  local-only key with a retained declaring-owner context ignores the access context; equal
  explicit inputs give equal keys; the production property access returns a published entry
  without evaluating; Q-37 published entries survive every later production run; so an EXPORTED
  binding published during discovery is reused by every later read in the round.

NOT claimed here (open): that every ordinary expression evaluation routes its property reads
through `evalZeroArgPropertyAccessCounted` with the same key inputs (evaluator internals); key
stability for LOCAL-only bindings across rows (needs the declaring owner's lexical activation to
be unchanged between the reads — a whole-run lexical-activation invariant — and the `partial`
`propertyOwnerBindingContext`); key injectivity; `FuelReached` for the binder/family channels
(the round's dispatch equations keep a completion premise); the `.whileBuiltin` loop driver beyond
`WhileRound.advance` (`EvalBody.whileLoop` is a `production_unfolds` instance); whole-run
heap/cache refinement, reachable-state / active-cell discipline, termination and R7; anything
about C# (budgets, cancellation, host effects, random draws, async suspension, planning).
-/

namespace KatLang.WhileRoundProduction

/-! ## 1. The activated-body boundary -/

/-- The body checks pass (state-free). -/
def Passes (a : Algorithm) : Prop := ∀ s, (ActivatedBody.check a).runState s = (.ok (), s)

/-- The body checks fail with `e` (state-free). -/
def Fails (a : Algorithm) (e : Error) : Prop := ∀ s, (ActivatedBody.check a).runState s = (.error e, s)

theorem check_duplicate (a : Algorithm) (n : Ident) (h : a.findDuplicatePropName = some n) :
    Fails a (Error.duplicateProperty n) := by
  intro s; simp only [ActivatedBody.check, h]; rfl

theorem check_conditional (a : Algorithm) (err : Error) (hd : a.findDuplicatePropName = none)
    (hc : conditionalValueAccessError? "conditional" a = some err) : Fails a err := by
  intro s; simp only [ActivatedBody.check, hd, hc, EvalM.bind_runState]; rfl

theorem check_missing_output (p : Option ScopeCtx) (pp : List ParameterPattern) (o : List Expr)
    (pr : List PropDef) (d : Option PropertyIdentity)
    (hd : (Algorithm.mk p pp o pr [] d).findDuplicatePropName = none)
    (hc : conditionalValueAccessError? "conditional" (Algorithm.mk p pp o pr [] d) = none) :
    Fails (Algorithm.mk p pp o pr [] d) Error.missingOutput := by
  intro s; simp only [ActivatedBody.check, hd, hc]; rfl

/-- A user body with written output and no duplicate property passes the checks. -/
theorem check_user_passes (p : Option ScopeCtx) (pp : List ParameterPattern) (o : List Expr)
    (pr : List PropDef) (e : Expr) (rows : List Expr) (d : Option PropertyIdentity)
    (hd : (Algorithm.mk p pp o pr (e :: rows) d).findDuplicatePropName = none)
    (hc : conditionalValueAccessError? "conditional" (Algorithm.mk p pp o pr (e :: rows) d) = none) :
    Passes (Algorithm.mk p pp o pr (e :: rows) d) := by
  intro s; simp only [ActivatedBody.check, hd, hc]; rfl

/-- The checks are state-free: they pass or fail with one error, whatever the state. -/
theorem check_dichotomy (a : Algorithm) : Passes a ∨ ∃ e, Fails a e := by
  cases hd : a.findDuplicatePropName with
  | some n => exact .inr ⟨_, check_duplicate a n hd⟩
  | none =>
    cases hc : conditionalValueAccessError? "conditional" a with
    | some err => exact .inr ⟨_, check_conditional a err hd hc⟩
    | none =>
      cases a with
      | mk p pp o pr out d =>
        cases out with
        | nil => exact .inr ⟨_, check_missing_output p pp o pr d hd hc⟩
        | cons e rows => exact .inl (check_user_passes p pp o pr e rows d hd hc)
      | _ => left; intro s; simp only [ActivatedBody.check, hd, hc]; rfl

/-- Whether ONE body entry records a lexical activation (`enterAlgorithmBody`): a body with
    parameters or a local-only property does; a parameterless body of exported members does not. -/
def recordsActivation (a : Algorithm) : Bool :=
  !(a.params.isEmpty && a.props.all (fun p => p.exposure.isExported))

/-- The activation record ONE body entry appends: the parameters' values and CELLS from the
    entry context (no cell is copied or allocated) and its binding context. -/
def enteredActivation (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) : ParameterActivation :=
  { values := env.filter (fun b => a.params.contains b.fst)
    needs := ctx.needEnv.filter (fun b => a.params.contains b.fst)
    bindingContext := ctx.bindingContext }

/-- The context ONE body entry returns. -/
def enteredCtx (a : Algorithm) (ctx : EvalCtx) (s : EvalState) : EvalCtx :=
  if recordsActivation a then
    { ctx.push a with headScope := some (a.asScopeCtx.withActivation s.lexicalActivations.size) }
  else ctx.push a

/-- The state ONE body entry leaves. -/
def enteredState (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) (s : EvalState) : EvalState :=
  if recordsActivation a then
    { s with lexicalActivations := s.lexicalActivations.push (enteredActivation a ctx env) }
  else s

/-- **Body entry** (`enterAlgorithmBody`): it never fails; it returns `enteredCtx` and leaves
    `enteredState`. -/
theorem enter_run (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) (s : EvalState) :
    (enterAlgorithmBody a ctx env).runState s = (.ok (enteredCtx a ctx s), enteredState a ctx env s) := by
  unfold enterAlgorithmBody enteredCtx enteredState recordsActivation
  cases h : (a.params.isEmpty && a.props.all (fun p => p.exposure.isExported)) with
  | true => simp only [ite_true, Bool.not_true]; rfl
  | false =>
    simp only [Bool.not_false, ite_true]
    simp only [recordParameterActivation]
    rfl

/-- The entered context keeps the parameter cells and the binding context of the entry context:
    rows read the cells the binder bound, never fresh copies. -/
theorem entered_needEnv (a : Algorithm) (ctx : EvalCtx) (s : EvalState) :
    (enteredCtx a ctx s).needEnv = ctx.needEnv ∧
    (enteredCtx a ctx s).bindingContext = ctx.bindingContext ∧
    (enteredCtx a ctx s).callStack = a :: ctx.callStack := by
  unfold enteredCtx; split <;> exact ⟨rfl, rfl, rfl⟩

/-- Body entry allocates no cell and touches no cell, no property-cache entry and no owner mark;
    it appends at most ONE lexical activation, keeping every earlier one. -/
theorem entered_state (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) (s : EvalState) :
    (enteredState a ctx env s).needs = s.needs ∧
    (enteredState a ctx env s).zeroArgPropertyCache = s.zeroArgPropertyCache ∧
    (enteredState a ctx env s).activeZeroArgProperties = s.activeZeroArgProperties ∧
    (enteredState a ctx env s).nextBindingContext = s.nextBindingContext ∧
    (enteredState a ctx env s).lexicalActivations =
      (if recordsActivation a then s.lexicalActivations.push (enteredActivation a ctx env)
       else s.lexicalActivations) := by
  unfold enteredState; split <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- A builtin body: its ONE counted value, read by the receiver's atomic route; no check, no
    entry, no row. -/
theorem readRows_builtin {α : Type} (form : EvalCtx → ValEnv → Expr → EvalM (List Result))
    (read : (Expr → EvalM (List Result)) → List Expr → EvalM α) (atomic : CountedResult → EvalM α)
    (b : Builtin) (ctx : EvalCtx) (env : ValEnv) :
    ActivatedBody.readRows form read atomic (.builtin b) ctx env =
      (evalBuiltinValueCounted b >>= atomic) := rfl

/-- Not a builtin. -/
def NotBuiltin (a : Algorithm) : Prop := ∀ b, a ≠ .builtin b

theorem readRows_nonbuiltin {α : Type} (form : EvalCtx → ValEnv → Expr → EvalM (List Result))
    (read : (Expr → EvalM (List Result)) → List Expr → EvalM α) (atomic : CountedResult → EvalM α)
    (a : Algorithm) (ha : NotBuiltin a) (ctx : EvalCtx) (env : ValEnv) :
    ActivatedBody.readRows form read atomic a ctx env =
      (do ActivatedBody.check a
          let pushedCtx ← enterAlgorithmBody a ctx env
          read (form pushedCtx env) (Algorithm.output a)) := by
  cases a with
  | builtin b => exact absurd rfl (ha b)
  | _ => rfl

/-- **A failed check reaches nothing**: the check's error, from the entry state — no body entry,
    no row. -/
theorem readRows_check_fails {α : Type} (form : EvalCtx → ValEnv → Expr → EvalM (List Result))
    (read : (Expr → EvalM (List Result)) → List Expr → EvalM α) (atomic : CountedResult → EvalM α)
    (a : Algorithm) (ha : NotBuiltin a) (e : Error) (hf : Fails a e) (ctx : EvalCtx) (env : ValEnv)
    (s : EvalState) :
    (ActivatedBody.readRows form read atomic a ctx env).runState s = (.error e, s) := by
  rw [readRows_nonbuiltin form read atomic a ha, EvalM.bind_runState, hf s]

/-- **ONE body entry, ONE context for every row** (CF-4): after passing checks the body is entered
    exactly once, and the rest of the run IS the reader over the ONE closure
    `form (enteredCtx a ctx s) env`, from the entered state. Every row the reader requests —
    discovery and transitions alike — is formed by that closure, from the state the previous
    row left: no second entry, no rebinding, no restored state. -/
theorem readRows_entered {α : Type} (form : EvalCtx → ValEnv → Expr → EvalM (List Result))
    (read : (Expr → EvalM (List Result)) → List Expr → EvalM α) (atomic : CountedResult → EvalM α)
    (a : Algorithm) (ha : NotBuiltin a) (hp : Passes a) (ctx : EvalCtx) (env : ValEnv) (s : EvalState) :
    (ActivatedBody.readRows form read atomic a ctx env).runState s =
      (read (form (enteredCtx a ctx s) env) a.output).runState (enteredState a ctx env s) := by
  rw [readRows_nonbuiltin form read atomic a ha, EvalM.bind_runState, hp s]
  simp only
  rw [EvalM.bind_runState, enter_run]

/-- **The run uses `form` at ONE context only**: two row-forming capabilities that agree at the
    entered context and environment give the same run (outcome and state). A reader that
    re-entered the body or rebound its parameters between discovery and the transitions would
    form rows at another context, which this excludes. -/
theorem readRows_uses_one_context {α : Type} (form form' : EvalCtx → ValEnv → Expr → EvalM (List Result))
    (read : (Expr → EvalM (List Result)) → List Expr → EvalM α) (atomic : CountedResult → EvalM α)
    (a : Algorithm) (ha : NotBuiltin a) (ctx : EvalCtx) (env : ValEnv) (s : EvalState)
    (hagree : form (enteredCtx a ctx s) env = form' (enteredCtx a ctx s) env) :
    (ActivatedBody.readRows form read atomic a ctx env).runState s =
      (ActivatedBody.readRows form' read atomic a ctx env).runState s := by
  rcases check_dichotomy a with hp | ⟨e, hf⟩
  · rw [readRows_entered form read atomic a ha hp, readRows_entered form' read atomic a ha hp, hagree]
  · rw [readRows_check_fails form read atomic a ha e hf, readRows_check_fails form' read atomic a ha e hf]

/-! ## 2. Ordinary row formation at the production evaluator -/

/-- **One ordinary counted evaluation, then the row rule** — an exact production equation (no
    completion premise): `formOutputRow` is the production `evalCounted` of the row's expression in
    the given context and environment, contributing `OutputRows.items` without restricting its
    counted result: a zero-count non-spread row keeps one visible value (`()` included); all
    other cases use `countedTopLevelValues`, preserving the actual count and value boundaries.
    A host-built Ready cell with count greater than one need not supply just one item. -/
theorem formOutputRow_is_counted_row (ctx : EvalCtx) (env : ValEnv) (e : Expr) :
    formOutputRow ctx env e = (evalCounted e ctx env >>= fun out => pure (OutputRows.items e out)) :=
  delegation_equation (.formOutputRow ctx env e) (.evalCounted e ctx env) _ (fun _ => rfl) (fun _ _ => nofun)

/-- The production row formation's outcome and state: those `evalCounted` reaches, a success
    mapped by `OutputRows.items`, an error unchanged. -/
theorem formOutputRow_run (ctx : EvalCtx) (env : ValEnv) (e : Expr) (s : EvalState) :
    (formOutputRow ctx env e).runState s =
      (match (evalCounted e ctx env).runState s with
       | (.ok out, t) => (.ok (OutputRows.items e out), t)
       | (.error err, t) => (.error err, t)) := by
  rw [formOutputRow_is_counted_row, EvalM.bind_runState]
  rcases (evalCounted e ctx env).runState s with ⟨o, t⟩
  cases o <;> rfl

/-- The evaluator core's row formation is the production one at the production answer. -/
theorem core_formOutputRow_is_production (ctx : EvalCtx) (env : ValEnv) :
    EvalRec.formOutputRow evalUnbounded ctx env = formOutputRow ctx env := rfl

/-! ## 3. Finite use: the converse of `production_unfolds` for sequenced bodies

`production_unfolds` (R7) says a COMPLETED production outcome is its body run over production. The
converse needs that the body uses only finitely many recursive answers. `Finite B` packages the
two properties a computation over an evaluator answer needs for it: it is monotone in the answer,
and wherever it completes over production it has the same outcome and state over some fuel
iterate. It holds for every recursive call, every answer-independent computation and every bind
of finite computations — hence for the row readers and the activated-body boundary. -/

/-- `B` is reached at finite fuel wherever it completes over production. -/
def FuelReached {α : Type} (B : EvalRec → EvalM α) : Prop :=
  ∀ s, ProductionCompletes (B evalUnbounded) s →
    ∃ m, (B (evalFuel m)).runState s = (B evalUnbounded).runState s

/-- Monotone in the evaluator answer and reached at finite fuel. -/
def Finite {α : Type} (B : EvalRec → EvalM α) : Prop := monotone B ∧ FuelReached B

theorem stable_of_mono {α : Type} (B : EvalRec → EvalM α) (hB : monotone B) {m m' : Nat}
    (h : m ≤ m') (s : EvalState) (hne : ((B (evalFuel m)).runState s).1 ≠ .error .fuelExhausted) :
    (B (evalFuel m')).runState s = (B (evalFuel m)).runState s := by
  rcases hB _ _ (evalFuel_mono h) s with hi | he
  · exfalso; apply hne; unfold EvalM.IsIncompleteAt at hi; rw [hi]
  · exact he.symm

theorem finite_const {α : Type} (m : EvalM α) : Finite (fun _ => m) :=
  ⟨fun _ _ _ => PartialOrder.rel_refl, fun _ _ => ⟨0, rfl⟩⟩

theorem finite_call (c : EvalCall) : Finite (fun rec => rec c) := by
  refine ⟨fun _ _ h => h c, ?_⟩
  intro s hc
  obtain ⟨m, hr, _⟩ := (production_completes_iff c s _).1 ⟨rfl, hc⟩
  exact ⟨m, hr⟩

theorem finite_bind {α β : Type} {B : EvalRec → EvalM α} {K : EvalRec → α → EvalM β}
    (hB : Finite B) (hK : ∀ a, Finite (fun rec => K rec a)) :
    Finite (fun rec => B rec >>= K rec) := by
  refine ⟨monotone_bind _ B K hB.1 (monotone_of_monotone_apply K (fun a => (hK a).1)), ?_⟩
  intro s hc
  unfold ProductionCompletes at hc
  rw [EvalM.bind_runState] at hc
  show ∃ m, (B (evalFuel m) >>= K (evalFuel m)).runState s = (B evalUnbounded >>= K evalUnbounded).runState s
  simp only [EvalM.bind_runState]
  rcases hrun : (B evalUnbounded).runState s with ⟨o, t⟩
  rw [hrun] at hc
  cases o with
  | error e =>
    obtain ⟨m, hm⟩ := hB.2 s (by unfold ProductionCompletes; rw [hrun]; simp only at hc ⊢; intro h; apply hc; injection h with h; rw [h])
    exact ⟨m, by rw [hm, hrun]⟩
  | ok a =>
    obtain ⟨m₁, hm₁⟩ := hB.2 s (by unfold ProductionCompletes; rw [hrun]; nofun)
    obtain ⟨m₂, hm₂⟩ := (hK a).2 t hc
    refine ⟨max m₁ m₂, ?_⟩
    have h1 : (B (evalFuel (max m₁ m₂))).runState s = (.ok a, t) := by
      rw [stable_of_mono B hB.1 (Nat.le_max_left _ _) s (by rw [hm₁, hrun]; nofun), hm₁, hrun]
    have hne : ((K (evalFuel m₂) a).runState t).1 ≠ .error .fuelExhausted := by
      have : (K (evalFuel m₂) a).runState t = (K evalUnbounded a).runState t := hm₂
      rw [this]; exact hc
    have h2 := stable_of_mono (fun rec => K rec a) (hK a).1 (Nat.le_max_right m₁ m₂) t hne
    simp only [h1]
    exact h2.trans hm₂

/-- A row-forming capability over the evaluator answer whose every row is finite. -/
def FiniteForm (form : EvalRec → Expr → EvalM (List Result)) : Prop := ∀ e, Finite (fun rec => form rec e)

theorem finite_formLeftToRight (form : EvalRec → Expr → EvalM (List Result)) (hf : FiniteForm form) :
    ∀ rows, Finite (fun rec => OutputRows.formLeftToRight (form rec) rows)
  | [] => by simp only [OutputRows.formLeftToRight]; exact finite_const _
  | e :: rest => by
      simp only [OutputRows.formLeftToRight]
      exact finite_bind (hf e) (fun xs => finite_bind (finite_formLeftToRight form hf rest)
        (fun ys => finite_const _))

theorem finite_discover (form : EvalRec → Expr → EvalM (List Result)) (hf : FiniteForm form) :
    ∀ rows, Finite (fun rec => WhileRound.discover (form rec) rows)
  | [] => by simp only [WhileRound.discover]; exact finite_const _
  | e :: rest => by
      simp only [WhileRound.discover]
      refine finite_bind (hf e) (fun xs => ?_)
      cases xs with
      | nil => exact finite_discover form hf rest
      | cons x xs => exact finite_const _

theorem finite_conditionFirst (form : EvalRec → Expr → EvalM (List Result)) (hf : FiniteForm form)
    (rows : List Expr) : Finite (fun rec => WhileRound.conditionFirst (form rec) rows) := by
  unfold WhileRound.conditionFirst
  refine finite_bind (finite_discover form hf rows.reverse) (fun r => ?_)
  rcases r with _ | ⟨earlier, flagItems⟩
  · exact finite_const _
  · dsimp only
    cases flagItems.getLast? with
    | none => exact finite_const _
    | some f =>
      refine finite_bind (finite_const _) (fun b => ?_)
      cases b
      · exact finite_const _
      · exact finite_bind (finite_formLeftToRight form hf earlier) (fun _ => finite_const _)

/-- The production row formation, as a row-forming capability over the evaluator answer. -/
theorem finiteForm_formOutputRow (ctx : EvalCtx) (env : ValEnv) :
    FiniteForm (fun rec => EvalRec.formOutputRow rec ctx env) :=
  fun e => finite_call (.formOutputRow ctx env e)

/-- The activated-body boundary over the evaluator's row formation is finite for every finite
    reader. -/
theorem finite_readRows {α : Type}
    (read : (Expr → EvalM (List Result)) → List Expr → EvalM α)
    (hread : ∀ form : EvalRec → Expr → EvalM (List Result), FiniteForm form →
      ∀ rows, Finite (fun rec => read (form rec) rows))
    (atomic : CountedResult → EvalM α) (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    Finite (fun rec => ActivatedBody.readRows (EvalRec.formOutputRow rec) read atomic a ctx env) := by
  unfold ActivatedBody.readRows
  cases a with
  | builtin b => exact finite_bind (finite_const _) (fun _ => finite_const _)
  | _ =>
    exact finite_bind (finite_const _) (fun _ => finite_bind (finite_const _)
      (fun pushed => hread _ (finiteForm_formOutputRow pushed env) _))

/-- **THE FINITE-USE CONVERSE.** An operation whose body is a finite computation `B` has, from
    every state where `B` completes over production, EXACTLY `B`'s production outcome and state. -/
theorem production_eq_of_finite (c : EvalCall) (B : EvalRec → EvalM c.Ret)
    (hstep : ∀ rec, evalStep rec c = B rec) (hB : Finite B) (s : EvalState)
    (hc : ProductionCompletes (B evalUnbounded) s) :
    (evalUnbounded c).runState s = (B evalUnbounded).runState s := by
  obtain ⟨m, hm⟩ := hB.2 s hc
  have hne : ((B (evalFuel m)).runState s).1 ≠ .error .fuelExhausted := by rw [hm]; exact hc
  have hfuel : (evalFuel (m + 1) c).runState s = (B evalUnbounded).runState s := by
    rw [evalFuel_succ, hstep, normalize_of_complete _ s hne, hm]
  exact ((production_completes_iff c s _).2
    ⟨m + 1, hfuel, (evalFuel_completes_iff (m + 1) c s).2 (by rw [hfuel]; exact hc)⟩).1

/-- Production completes exactly when its finite body does over production. -/
theorem production_completes_iff_body (c : EvalCall) (B : EvalRec → EvalM c.Ret)
    (hstep : ∀ rec, evalStep rec c = B rec) (hB : Finite B) (s : EvalState) :
    ProductionCompletes (evalUnbounded c) s ↔ ProductionCompletes (B evalUnbounded) s := by
  constructor
  · intro hc
    have h := production_unfolds c s hc
    rw [hstep] at h
    unfold ProductionCompletes at hc ⊢; rw [h]; exact hc
  · intro hc
    unfold ProductionCompletes at hc ⊢
    rw [production_eq_of_finite c B hstep hB s hc]; exact hc

/-- A body run that never consults the evaluator answer at `s` is production's outcome there. -/
theorem production_of_answer_free (c : EvalCall) (s : EvalState) (r : Except Error c.Ret × EvalState)
    (h : ∀ rec, (evalStep rec c).runState s = r) (hr : r.1 ≠ .error .fuelExhausted) :
    (evalUnbounded c).runState s = r := by
  have hfuel : (evalFuel 1 c).runState s = r := by
    rw [evalFuel_succ, normalize_of_complete _ s (by rw [h]; exact hr), h]
  exact ((production_completes_iff c s r).2
    ⟨1, hfuel, (evalFuel_completes_iff 1 c s).2 (by rw [hfuel]; exact hr)⟩).1

/-! ### The production row readers -/

theorem finite_whileVerdictSlots (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    Finite (fun rec => EvalBody.whileVerdictSlots rec a ctx env) :=
  finite_readRows WhileRound.conditionFirst (fun form hf rows => finite_conditionFirst form hf rows) _ a ctx env

theorem finite_evalAlgOutputSlots (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    Finite (fun rec => EvalBody.evalAlgOutputSlots rec a ctx env) :=
  finite_readRows OutputRows.formLeftToRight (fun form hf rows => finite_formLeftToRight form hf rows) _ a ctx env

/-- **The production `while` reader IS its activated-body run** wherever that completes: the
    same outcome and state (`whileVerdictSlots_completes_iff` is the completion equivalence). -/
theorem whileVerdictSlots_production (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) (s : EvalState)
    (hc : ProductionCompletes (EvalBody.whileVerdictSlots evalUnbounded a ctx env) s) :
    (whileVerdictSlots a ctx env).runState s = (EvalBody.whileVerdictSlots evalUnbounded a ctx env).runState s :=
  production_eq_of_finite (.whileVerdictSlots a ctx env) _ (fun _ => rfl) (finite_whileVerdictSlots a ctx env) s hc

theorem whileVerdictSlots_completes_iff (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) (s : EvalState) :
    ProductionCompletes (whileVerdictSlots a ctx env) s ↔
      ProductionCompletes (EvalBody.whileVerdictSlots evalUnbounded a ctx env) s :=
  production_completes_iff_body (.whileVerdictSlots a ctx env) _ (fun _ => rfl) (finite_whileVerdictSlots a ctx env) s

/-- The same for the supply reader (`repeat`, the left-to-right reading). -/
theorem evalAlgOutputSlots_production (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) (s : EvalState)
    (hc : ProductionCompletes (EvalBody.evalAlgOutputSlots evalUnbounded a ctx env) s) :
    (evalAlgOutputSlots a ctx env).runState s = (EvalBody.evalAlgOutputSlots evalUnbounded a ctx env).runState s :=
  production_eq_of_finite (.evalAlgOutputSlots a ctx env) _ (fun _ => rfl) (finite_evalAlgOutputSlots a ctx env) s hc

/-- **CF-4 at the production `while` reader.** For a checked, non-builtin step body, the production
    `whileVerdictSlots` IS `WhileRound.conditionFirst` over the production `formOutputRow` in the ONE
    entered context, from the entered state — wherever that run completes. -/
theorem whileVerdictSlots_entered (a : Algorithm) (ha : NotBuiltin a) (hp : Passes a)
    (ctx : EvalCtx) (env : ValEnv) (s : EvalState)
    (hc : ((WhileRound.conditionFirst (formOutputRow (enteredCtx a ctx s) env) a.output).runState
      (enteredState a ctx env s)).1 ≠ .error .fuelExhausted) :
    (whileVerdictSlots a ctx env).runState s =
      (WhileRound.conditionFirst (formOutputRow (enteredCtx a ctx s) env) a.output).runState
        (enteredState a ctx env s) := by
  have hbody : (EvalBody.whileVerdictSlots evalUnbounded a ctx env).runState s =
      (WhileRound.conditionFirst (formOutputRow (enteredCtx a ctx s) env) a.output).runState
        (enteredState a ctx env s) :=
    readRows_entered (EvalRec.formOutputRow evalUnbounded) _ _ a ha hp ctx env s
  rw [whileVerdictSlots_production a ctx env s (by unfold ProductionCompletes; rw [hbody]; exact hc), hbody]

/-- **CF-4 at the production supply reader** (`repeat`): every row formed once, left to right, in
    the ONE entered context. -/
theorem evalAlgOutputSlots_entered (a : Algorithm) (ha : NotBuiltin a) (hp : Passes a)
    (ctx : EvalCtx) (env : ValEnv) (s : EvalState)
    (hc : ((OutputRows.formLeftToRight (formOutputRow (enteredCtx a ctx s) env) a.output).runState
      (enteredState a ctx env s)).1 ≠ .error .fuelExhausted) :
    (evalAlgOutputSlots a ctx env).runState s =
      (OutputRows.formLeftToRight (formOutputRow (enteredCtx a ctx s) env) a.output).runState
        (enteredState a ctx env s) := by
  have hbody : (EvalBody.evalAlgOutputSlots evalUnbounded a ctx env).runState s =
      (OutputRows.formLeftToRight (formOutputRow (enteredCtx a ctx s) env) a.output).runState
        (enteredState a ctx env s) :=
    readRows_entered (EvalRec.formOutputRow evalUnbounded) _ _ a ha hp ctx env s
  rw [evalAlgOutputSlots_production a ctx env s (by unfold ProductionCompletes; rw [hbody]; exact hc), hbody]

/-! ## 4. The condition-first laws at the production `while` reader

The row-control theorems of `WhileRound.lean`, composed with the boundary: every row is formed by
the production `formOutputRow` in the ONE entered context `pushed := enteredCtx a ctx s` and
environment `env`, threading the state from the entered state `s₀ := enteredState a ctx env s`.
Each statement is about the production operation `whileVerdictSlots`; no premise says that
production behaves like a callback. The only premises beyond the row facts are the body checks,
and — where the result is an arbitrary row error — that the error is a completed outcome. -/

section ProductionLaws
variable (a : Algorithm) (ha : NotBuiltin a) (hp : Passes a) (ctx : EvalCtx) (env : ValEnv) (s : EvalState)
include ha hp

/-- CF-1 at production: a `false` flag found after an effectful empty trailing suffix STOPS the
    round in the state discovery reached; no earlier row is formed. -/
theorem production_cf1_false_skips_earlier_rows
    (pre : List Expr) (r : Expr) (trail : List Expr) (hrows : a.output = pre ++ r :: trail)
    (s₁ s₂ : EvalState) (x : Result) (xs : List Result) (f : Result)
    (htrail : EmptySuffix (formOutputRow (enteredCtx a ctx s) env) trail (enteredState a ctx env s) s₁)
    (hr : (formOutputRow (enteredCtx a ctx s) env r).runState s₁ = (.ok (x :: xs), s₂))
    (hlast : (x :: xs).getLast? = some f) (hf : Result.asBool? f = some false) :
    (whileVerdictSlots a ctx env).runState s = (.ok none, s₂) := by
  have h := cf1_false_skips_earlier_rows _ pre r trail _ s₁ s₂ x xs f htrail hr hlast hf
  rw [← hrows] at h
  rw [whileVerdictSlots_entered a ha hp ctx env s (by rw [h]; nofun), h]

/-- CF-2 at production, accepted transitions: after a `true` flag the earlier rows are formed
    left to right from discovery's final state, in the SAME entered context; the next state is
    the supply without its last item. -/
theorem production_cf2_true_forms_earlier_rows
    (pre : List Expr) (r : Expr) (trail : List Expr) (hrows : a.output = pre ++ r :: trail)
    (s₁ s₂ s₃ : EvalState) (x : Result) (xs : List Result) (f : Result) (ys : List Result)
    (htrail : EmptySuffix (formOutputRow (enteredCtx a ctx s) env) trail (enteredState a ctx env s) s₁)
    (hr : (formOutputRow (enteredCtx a ctx s) env r).runState s₁ = (.ok (x :: xs), s₂))
    (hlast : (x :: xs).getLast? = some f) (hf : Result.asBool? f = some true)
    (hpre : (OutputRows.formLeftToRight (formOutputRow (enteredCtx a ctx s) env) pre).runState s₂ = (.ok ys, s₃)) :
    (whileVerdictSlots a ctx env).runState s = (.ok (some (WhileRound.nextSlots (ys ++ x :: xs))), s₃) := by
  have h := cf2_true_forms_earlier_rows_once _ pre r trail _ s₁ s₂ x xs f htrail hr hlast hf
  rw [hpre, ← hrows] at h
  simp only at h
  rw [whileVerdictSlots_entered a ha hp ctx env s (by rw [h]; nofun), h]

/-- CF-2 at production, first transition failure: after a `true` flag the round fails with the
    FIRST failing earlier row's error, in the state that row left (no rollback of discovery). -/
theorem production_cf2_transition_failure
    (pre : List Expr) (r : Expr) (trail : List Expr) (hrows : a.output = pre ++ r :: trail)
    (s₁ s₂ s₃ : EvalState) (x : Result) (xs : List Result) (f : Result) (err : Error)
    (herr : err ≠ .fuelExhausted)
    (htrail : EmptySuffix (formOutputRow (enteredCtx a ctx s) env) trail (enteredState a ctx env s) s₁)
    (hr : (formOutputRow (enteredCtx a ctx s) env r).runState s₁ = (.ok (x :: xs), s₂))
    (hlast : (x :: xs).getLast? = some f) (hf : Result.asBool? f = some true)
    (hpre : (OutputRows.formLeftToRight (formOutputRow (enteredCtx a ctx s) env) pre).runState s₂ = (.error err, s₃)) :
    (whileVerdictSlots a ctx env).runState s = (.error err, s₃) := by
  have h := cf2_true_forms_earlier_rows_once _ pre r trail _ s₁ s₂ x xs f htrail hr hlast hf
  rw [hpre, ← hrows] at h
  simp only at h
  rw [whileVerdictSlots_entered a ha hp ctx env s (by rw [h]; intro h'; apply herr; injection h'), h]

/-- CF-5a at production: a row failing during discovery fails the round with its own error, in
    the state it left; no earlier row is formed and the visited suffix is not rolled back. -/
theorem production_cf5_discovery_failure
    (pre : List Expr) (r : Expr) (trail : List Expr) (hrows : a.output = pre ++ r :: trail)
    (s₁ s₂ : EvalState) (err : Error) (herr : err ≠ .fuelExhausted)
    (htrail : EmptySuffix (formOutputRow (enteredCtx a ctx s) env) trail (enteredState a ctx env s) s₁)
    (hr : (formOutputRow (enteredCtx a ctx s) env r).runState s₁ = (.error err, s₂)) :
    (whileVerdictSlots a ctx env).runState s = (.error err, s₂) := by
  have h := cf5_discovery_failure_first _ pre r trail _ s₁ s₂ err htrail hr
  rw [← hrows] at h
  rw [whileVerdictSlots_entered a ha hp ctx env s (by rw [h]; intro h'; apply herr; injection h'), h]

/-- CF-5b at production: a non-Boolean flag is the value-kind error, before any earlier row. -/
theorem production_cf5_nonboolean_flag
    (pre : List Expr) (r : Expr) (trail : List Expr) (hrows : a.output = pre ++ r :: trail)
    (s₁ s₂ : EvalState) (x : Result) (xs : List Result) (f : Result)
    (htrail : EmptySuffix (formOutputRow (enteredCtx a ctx s) env) trail (enteredState a ctx env s) s₁)
    (hr : (formOutputRow (enteredCtx a ctx s) env r).runState s₁ = (.ok (x :: xs), s₂))
    (hlast : (x :: xs).getLast? = some f) (hf : Result.asBool? f = none) :
    (whileVerdictSlots a ctx env).runState s =
      (.error (Error.typeMismatch
        (booleanRequiredMessage "while continuation flag (the step's last output)" f)), s₂) := by
  have h := cf5_nonboolean_flag_first _ pre r trail _ s₁ s₂ x xs f htrail hr hlast hf
  rw [← hrows] at h
  rw [whileVerdictSlots_entered a ha hp ctx env s (by rw [h]; nofun), h]

/-- No row supplies an item: every row is formed right to left (effects kept) and the round is
    the missing-flag `badArity`. -/
theorem production_cf_all_rows_empty_no_flag (t : EvalState)
    (h : EmptySuffix (formOutputRow (enteredCtx a ctx s) env) a.output (enteredState a ctx env s) t) :
    (whileVerdictSlots a ctx env).runState s =
      (.error (Error.withContext whileStepWithoutFlagContext Error.badArity), t) := by
  have h' := cf_all_rows_empty_no_flag _ _ _ t h
  rw [whileVerdictSlots_entered a ha hp ctx env s (by rw [h']; nofun), h']

end ProductionLaws

/-- A failed body check reaches NOTHING at production: the check's error from the entry state —
    no body entry, no row, no activation recorded. -/
theorem production_check_failure_reaches_no_row (a : Algorithm) (ha : NotBuiltin a) (e : Error)
    (hf : Fails a e) (he : e ≠ .fuelExhausted) (ctx : EvalCtx) (env : ValEnv) (s : EvalState) :
    (whileVerdictSlots a ctx env).runState s = (.error e, s) ∧
    (evalAlgOutputSlots a ctx env).runState s = (.error e, s) := by
  constructor
  · exact production_of_answer_free (.whileVerdictSlots a ctx env) s _
      (fun rec => readRows_check_fails _ _ _ a ha e hf ctx env s) (by intro h; apply he; injection h)
  · exact production_of_answer_free (.evalAlgOutputSlots a ctx env) s _
      (fun rec => readRows_check_fails _ _ _ a ha e hf ctx env s) (by intro h; apply he; injection h)

/-- A builtin body (a host-built clause body) is ONE atomic row at production: its counted value,
    split as one supply (`WhileRound.ofSupply`) — no check, no entry, no row. -/
theorem production_builtin_body_atomic (b : Builtin) (ctx : EvalCtx) (env : ValEnv) (s : EvalState)
    (hc : ((evalBuiltinValueCounted b >>= fun out => WhileRound.ofSupply [out.fst]).runState s).1 ≠
      .error .fuelExhausted) :
    (whileVerdictSlots (.builtin b) ctx env).runState s =
      (evalBuiltinValueCounted b >>= fun out => WhileRound.ofSupply [out.fst]).runState s :=
  production_of_answer_free (.whileVerdictSlots (.builtin b) ctx env) s _ (fun _ => rfl) hc

/-! ## 5. The round's dispatch: one invocation, then ONE body reader

A completed production `while` round (`runNeedWhileRound`) is the ONE dispatcher `runNeedStepWith`
over production (`production_unfolds`), with the production `whileVerdictSlots` as the row reader:
a user step binds through the one binder and reads its body ONCE; a clause family dispatches ONCE
and reads the ONE selected (already activated) body; a builtin is one atomic row; an alias resolves
its target once and is that target's round. The family's selection, binder activation
(`needActivateBranch` / `wireSelectedBranchBody`) and body entry are separate operations: the
body entry is `readRows`'s, performed once inside that one `whileVerdictSlots` call. These keep
`production_unfolds`' completion premise — the binder channels are not proved `Finite` here. -/

theorem runNeedWhileRound_unfolds (step : Algorithm) (ctx : EvalCtx) (env : ValEnv) (cells : List Nat)
    (stepName : String) (s : EvalState)
    (hc : ProductionCompletes (runNeedWhileRound step ctx env cells stepName) s) :
    (runNeedWhileRound step ctx env cells stepName).runState s =
      (EvalBody.runNeedStepWith evalUnbounded whileVerdictSlots
        (fun out => WhileRound.ofSupply (loopStepBuiltinRows out))
        (fun target => runNeedWhileRound target ctx env cells stepName) step ctx env cells stepName).runState s :=
  (production_unfolds (.runNeedWhileRound step ctx env cells stepName) s hc).symm

/-- A user step: the one binder over the state cells, ONE fresh binding context, then exactly ONE
    production `whileVerdictSlots` of the step body with the bound context. -/
theorem runNeedWhileRound_user (p : Option ScopeCtx) (pp : List ParameterPattern) (o : List Expr)
    (pr : List PropDef) (out : List Expr) (d : Option PropertyIdentity)
    (ctx : EvalCtx) (env : ValEnv) (cells : List Nat) (stepName : String) (s : EvalState)
    (hc : ProductionCompletes (runNeedWhileRound (.mk p pp o pr out d) ctx env cells stepName) s) :
    (runNeedWhileRound (.mk p pp o pr out d) ctx env cells stepName).runState s =
      (do
        let some bindings ← bindNeedPatterns bindingChannels
            ((Algorithm.parameterPatterns (.mk p pp o pr out d)).map NeedPattern.ofParameter) cells
          | throw Error.badArity
        let next ← needBindingContext ctx bindings
        whileVerdictSlots (.mk p pp o pr out d) next
          (ValEnv.shadow env (Algorithm.params (.mk p pp o pr out d))) : EvalM _).runState s := by
  rw [runNeedWhileRound_unfolds _ ctx env cells stepName s hc]; rfl

/-- A clause family: the ordinary family dispatcher ONCE, then exactly ONE production
    `whileVerdictSlots` of the selected, activated body — no second dispatch, no second body. -/
theorem runNeedWhileRound_family (p : Option ScopeCtx) (o : List Expr) (br : List CondBranch)
    (d : Option PropertyIdentity) (ctx : EvalCtx) (env : ValEnv) (cells : List Nat) (stepName : String)
    (s : EvalState)
    (hc : ProductionCompletes (runNeedWhileRound (.conditional p o br d) ctx env cells stepName) s) :
    (runNeedWhileRound (.conditional p o br d) ctx env cells stepName).runState s =
      (withCtx s!"while evaluating call to {stepName}" do
        let (body, next, values) ← selectNeedFamilyBranch bindingChannels (.conditional p o br d) cells ctx env stepName
        whileVerdictSlots body next values).runState s := by
  rw [runNeedWhileRound_unfolds _ ctx env cells stepName s hc]; rfl

/-- A builtin step: its ordinary argument roles over the state cells; its ONE result is ONE
    atomic row read by `WhileRound.ofSupply`. -/
theorem runNeedWhileRound_builtin (b : Builtin) (ctx : EvalCtx) (env : ValEnv) (cells : List Nat)
    (stepName : String) (s : EvalState)
    (hc : ProductionCompletes (runNeedWhileRound (.builtin b) ctx env cells stepName) s) :
    (runNeedWhileRound (.builtin b) ctx env cells stepName).runState s =
      (withCtx s!"while evaluating call to {stepName}" do
        let out ← applyBuiltinCountedResolved b (cells.map fun address =>
          ({ algorithm := Algorithm.ofExpr (.emptySequence 0), need? := some address } : ResolvedArgumentAlgorithm)) ctx env
        WhileRound.ofSupply (loopStepBuiltinRows out)).runState s := by
  rw [runNeedWhileRound_unfolds _ ctx env cells stepName s hc]; rfl

/-- An alias step: its target resolved once by the existing alias route; the round is the
    target's round over the same cells. -/
theorem runNeedWhileRound_alias (p : Option ScopeCtx) (o : List Expr) (pr : List PropDef) (t : Expr)
    (d : Option PropertyIdentity) (ctx : EvalCtx) (env : ValEnv) (cells : List Nat) (stepName : String) (s : EvalState)
    (hc : ProductionCompletes (runNeedWhileRound (.alias p o pr t d) ctx env cells stepName) s) :
    (runNeedWhileRound (.alias p o pr t d) ctx env cells stepName).runState s =
      (do
        let target ← resolveAliasTarget (.alias p o pr t d) ctx
        runNeedWhileRound target ctx env cells stepName).runState s := by
  rw [runNeedWhileRound_unfolds _ ctx env cells stepName s hc]; rfl

/-! ## 6. Shared parameter cells -/

/-- The callee-side context of a completed binding: ONE fresh binding context; the bound names map
    to the binder's own addresses (prepended); no cell is allocated or touched. -/
theorem needBindingContext_run (ctx : EvalCtx) (bindings : NeedEnv) (s : EvalState) :
    (needBindingContext ctx bindings).runState s =
      (.ok { ctx with bindingContext := s.nextBindingContext,
                      needEnv := bindings ++ ctx.needEnv.filter
                        (fun entry => !(bindings.map Prod.fst).contains entry.fst) },
       { s with nextBindingContext := s.nextBindingContext + 1 }) := rfl

theorem lookupAssoc_append_left {A : Type} (x : Ident) (l r : Assoc Ident A) (v : A)
    (h : lookupAssoc x l = some v) : lookupAssoc x (l ++ r) = some v := by
  induction l with
  | nil => simp [lookupAssoc] at h
  | cons kv rest ih =>
    obtain ⟨k, w⟩ := kv
    simp only [lookupAssoc, List.cons_append] at h ⊢
    split
    · rename_i hk; rw [if_pos hk] at h; exact h
    · rename_i hk; rw [if_neg hk] at h; exact ih h

/-- **The rows read the binder's cells.** A name the binder bound to address `addr` is found at
    `addr` in the context every row of the round is formed in (`enteredCtx` over the binding's
    context): the SAME supplied or structurally allocated cell, never a fresh Ready copy. -/
theorem round_parameter_cell (a : Algorithm) (ctx : EvalCtx) (bindings : NeedEnv) (s t : EvalState)
    (x : Ident) (addr : Nat) (hx : lookupAssoc x bindings = some addr)
    (hnext : (needBindingContext ctx bindings).runState s = (.ok next, t)) :
    lookupAssoc x (enteredCtx a next t).needEnv = some addr := by
  rw [needBindingContext_run] at hnext
  injection hnext with hctx _
  injection hctx with hctx
  rw [(entered_needEnv a next t).1, ← hctx]
  exact lookupAssoc_append_left x _ _ addr hx

/-- A cell completed with a completed outcome is reused by the production demand: its outcome,
    the state unchanged — nothing is evaluated or formed again. -/
theorem completed_cell_reused (addr : Nat) (s : EvalState) (cell : NeedCell)
    (o : Except Error CountedResult) (hc : s.needs[addr]? = some cell) (hs : cell.state = .completed o)
    (ho : o ≠ .error .fuelExhausted) :
    (demandNeedRecursive addr).runState s = (o, s) :=
  production_of_answer_free (.demandNeedRecursive addr) s (o, s)
    (fun _ => KatLang.NeedControl.Memo.completed_sticky _ _ _ addr s cell o hc hs) ho

/-- **A cell completed during discovery is the cell the transitions read.** After ANY disciplined
    computation — every production operation is (`evalUnbounded_disciplined`), so every later row
    of the round — the cell still holds the same completed outcome, and its production demand
    returns it without evaluating. -/
theorem completed_cell_reused_after {α : Type} (m : EvalM α) (hm : KatLang.CallPlan.Disciplined m)
    (addr : Nat) (s : EvalState) (cell : NeedCell) (o : Except Error CountedResult)
    (hc : s.needs[addr]? = some cell) (hs : cell.state = .completed o) (ho : o ≠ .error .fuelExhausted) :
    (demandNeedRecursive addr).runState (m.runState s).2 = (o, (m.runState s).2) := by
  obtain ⟨cell', hc', hk⟩ := hm s addr cell hc
  exact completed_cell_reused addr _ cell' o hc' (hk.completed o hs) ho

/-- The transition reader over the production row formation is disciplined. -/
theorem transitions_disciplined (ctx : EvalCtx) (env : ValEnv) (rows : List Expr) :
    KatLang.CallPlan.Disciplined (OutputRows.formLeftToRight (formOutputRow ctx env) rows) :=
  KatLang.EvaluatorDiscipline.disc_formLeftToRight _
    (fun e => KatLang.EvaluatorDiscipline.evalUnbounded_disciplined (.formOutputRow ctx env e)) rows

/-! ## 7. Shared property caches — what is proved, separately

Context sharing and state threading (§ 1, § 4) are necessary for cache sharing but do not by
themselves prove that a property is evaluated once. The cache claims proved here are about the
production property access (`evalZeroArgPropertyAccessCounted`) and its key. -/

/-- An EXPORTED binding's key is run-scoped: it ignores the access kind, context, environment and
    retained owner context. -/
theorem cacheKey_exported_context_free (k k' : ZeroArgPropertyAccessKind) (owner : Algorithm)
    (binding : PropDef) (hexp : binding.exposure.isExported = true) (ctx ctx' : EvalCtx)
    (env env' : ValEnv) (oc oc' : Option Nat) :
    zeroArgPropertyCacheKey k owner binding ctx env oc = zeroArgPropertyCacheKey k' owner binding ctx' env' oc' := by
  simp [zeroArgPropertyCacheKey, hexp]

/-- A LOCAL-only binding with a retained declaring-owner context `n` keys on `n`: it ignores the
    access kind, context and environment. -/
theorem cacheKey_retained_owner_context (k k' : ZeroArgPropertyAccessKind) (owner : Algorithm)
    (binding : PropDef) (ctx ctx' : EvalCtx) (env env' : ValEnv) (n : Nat) :
    zeroArgPropertyCacheKey k owner binding ctx env (some n) =
      zeroArgPropertyCacheKey k' owner binding ctx' env' (some n) := by
  simp [zeroArgPropertyCacheKey]

/-- Without a retained owner context, equal explicit inputs — the binding context and the value
    environment — give the same key (the relevant equality direction; no injectivity is claimed). -/
theorem cacheKey_same_inputs (k k' : ZeroArgPropertyAccessKind) (owner : Algorithm) (binding : PropDef)
    (ctx ctx' : EvalCtx) (env : ValEnv) (hb : ctx.bindingContext = ctx'.bindingContext) :
    zeroArgPropertyCacheKey k owner binding ctx env none = zeroArgPropertyCacheKey k' owner binding ctx' env none := by
  simp [zeroArgPropertyCacheKey, hb]

/-- **A published entry is reused by the production access**: a cacheable property-style read whose
    key (at the read's state) holds `v` returns `v` and leaves the state unchanged — no evaluation,
    no owner mark, no publication. -/
theorem property_cache_hit_production (k : ZeroArgPropertyAccessKind) (owner : Algorithm)
    (binding : PropDef) (resolved : Algorithm) (ctx : EvalCtx) (env : ValEnv) (s : EvalState)
    (v : CountedResult) (hcache : isCacheableZeroArgPropertyAlgorithm resolved = true)
    (hhit : ZeroArgPropertyCache.lookup s.zeroArgPropertyCache
      (zeroArgPropertyCacheKey k owner binding ctx env (propertyOwnerBindingContext resolved.parent s)) = some v) :
    (evalZeroArgPropertyAccessCounted k owner binding resolved ctx env).runState s = (.ok v, s) := by
  refine production_of_answer_free (.evalZeroArgPropertyAccessCounted k owner binding resolved ctx env .read) s _
    (fun rec => ?_) nofun
  show (EvalBody.evalZeroArgPropertyAccessCounted rec k owner binding resolved ctx env .read).runState s = _
  simp only [EvalBody.evalZeroArgPropertyAccessCounted, hcache, if_true, EvalM.bind_runState]
  show (match ZeroArgPropertyCache.lookup s.zeroArgPropertyCache _ with
    | some cached => (pure cached : EvalM CountedResult)
    | none => _).runState s = _
  rw [hhit]; rfl

/-- Q-37: an entry published before a production computation survives it with its value — e.g.
    an entry published during discovery survives the round's transitions. -/
theorem published_entry_survives (c : EvalCall) (s : EvalState) (key : ZeroArgPropertyCacheKey)
    (v : CountedResult) (h : ZeroArgPropertyCache.lookup s.zeroArgPropertyCache key = some v) :
    ZeroArgPropertyCache.lookup ((evalUnbounded c).runState s).2.zeroArgPropertyCache key = some v :=
  KatLang.EvaluatorCacheLaws.cache_entries_survive c s key v h

/-- The transition reader over the production row formation keeps every published entry. -/
theorem transitions_keep_cache (ctx : EvalCtx) (env : ValEnv) (rows : List Expr) :
    Preserves KatLang.EvaluatorCacheLaws.CacheKept (OutputRows.formLeftToRight (formOutputRow ctx env) rows) :=
  KatLang.EvaluatorCacheLaws.pres_formLeftToRight _
    (fun e => KatLang.EvaluatorCacheLaws.cache_entries_survive (.formOutputRow ctx env e)) rows

/-- **An EXPORTED property published during discovery is reused by every later read of the
    round.** If the cache holds the exported binding's entry at `s₂` and `t` keeps the entries of
    `s₂` (every production computation does), then a property-style read of that binding through
    the production access — in ANY context and environment — returns the published value at `t`
    without evaluating. -/
theorem exported_publication_reused (k k' : ZeroArgPropertyAccessKind) (owner : Algorithm)
    (binding : PropDef) (hexp : binding.exposure.isExported = true) (resolved : Algorithm)
    (hcache : isCacheableZeroArgPropertyAlgorithm resolved = true)
    (ctx₀ : EvalCtx) (env₀ : ValEnv) (oc : Option Nat) (s₂ t : EvalState) (v : CountedResult)
    (hpub : ZeroArgPropertyCache.lookup s₂.zeroArgPropertyCache (zeroArgPropertyCacheKey k owner binding ctx₀ env₀ oc) = some v)
    (hkept : KatLang.EvaluatorCacheLaws.CacheKept s₂ t) (ctx : EvalCtx) (env : ValEnv) :
    (evalZeroArgPropertyAccessCounted k' owner binding resolved ctx env).runState t = (.ok v, t) := by
  apply property_cache_hit_production k' owner binding resolved ctx env t v hcache
  rw [cacheKey_exported_context_free k' k owner binding hexp ctx ctx₀ env env₀ _ oc]
  exact hkept _ v hpub

/-- The LOCAL-only counterpart, with its residual premise explicit: the read's declaring-owner
    context must still be the retained `n` the entry was published under (the whole-run stability
    of lexical activations is NOT proved here). -/
theorem local_publication_reused (k k' : ZeroArgPropertyAccessKind) (owner : Algorithm)
    (binding : PropDef) (resolved : Algorithm) (hcache : isCacheableZeroArgPropertyAlgorithm resolved = true)
    (ctx₀ : EvalCtx) (env₀ : ValEnv) (n : Nat) (s₂ t : EvalState) (v : CountedResult)
    (hpub : ZeroArgPropertyCache.lookup s₂.zeroArgPropertyCache (zeroArgPropertyCacheKey k owner binding ctx₀ env₀ (some n)) = some v)
    (hkept : KatLang.EvaluatorCacheLaws.CacheKept s₂ t) (ctx : EvalCtx) (env : ValEnv)
    (hstable : propertyOwnerBindingContext resolved.parent t = some n) :
    (evalZeroArgPropertyAccessCounted k' owner binding resolved ctx env).runState t = (.ok v, t) := by
  apply property_cache_hit_production k' owner binding resolved ctx env t v hcache
  rw [hstable, cacheKey_retained_owner_context k' k owner binding ctx ctx₀ env env₀ n]
  exact hkept _ v hpub

end KatLang.WhileRoundProduction
