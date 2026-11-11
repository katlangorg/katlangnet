import KatLangArityLaws.ValidationFrame

open KatLang KatLang.EvaluatorCore KatLang.ValidationFrame

/-!
# E-6 Tier 3: the admitted set of the pre-evaluation validation

E-6 Tier 2 (`ValidationFrame`) proved WHAT the validation does to a run — it returns its entry
state, fails only with a `ValidatorError`, never yields the incomplete outcome, and its outcome does
not depend on the entry state. This module states WHICH trees it accepts.

* **The admitted set** (§ 2): `AdmittedAlgorithm` / `AdmittedScope` / `AdmittedExpr`, a
  declarative, monad-free and state-free predicate over the WHOLE tree the validator walks:
  every algorithm node satisfies its node conditions (no singleton sequence pattern, at most one
  collecting capture per level, no repeated name over a collector, no invalid `meta` parameter,
  explicit parameters only with output, uniform clause-family arities, a static-path alias target
  whose static chase meets no alias twice), with the static chain and alias count the validator
  uses at that node, and every child the validator visits — opens, properties, output rows,
  branch bodies, alias targets, host-built parent scopes and their members, every
  subexpression — is admitted in turn. `Admitted e` adds the HOST-LEAN-O6 provenance check.
* **The characterization** (§ 3): `validate_ok_iff` — the validation of `e` returns `ok` (from
  ANY entry state) exactly when `Admitted e`; `validate_error_iff` — it fails, with a validator
  error and the state unchanged, exactly when `¬ Admitted e`. The tree-level forms are
  `validateAlgorithmTree_passes`, `validateScopeTree_passes`, `validateExprTree_passes`; the
  algorithm-level entry `validateAlgorithm_ok_iff`.
* **The public run** (§ 4): `runResultM e` validates the IDENTIFIED tree
  `(identifyPropertyExpr e).run' 0`. If it is not admitted the public run refuses at once with a
  validator error and its entry state (`public_refused`); if it is, the public run IS the root
  step (`public_admitted`). The outcome-form incompletion corollary: the public outcome is
  incomplete exactly when the identified tree is admitted and the root step is incomplete
  (`public_incomplete_iff_root`), from `EvalState.empty` in fuel form
  (`public_incomplete_from_empty`). This relates outcomes only, through
  `PublicRunBridge.Incomplete`; it does not say whether a public incomplete outcome may or should
  occur (Constitution Q-82, open).

What is NOT re-expressed: the node conditions are the validator's own total executable checks
(`Algorithm.hasSingletonSequencePattern`, `staticAliasCycle`, `hostProvenanceViolation?`, …), named
as such, not restated in a second vocabulary; and the admitted set is a set of IDENTIFIED trees —
how identification moves a source tree into or out of it is not characterized here.
-/

namespace KatLang.AdmittedSet

/-! ## 1. Passing validation steps -/

/-- A validation step PASSES: it returns `ok` from every entry state. For a `Frame` it is the same
    as returning `ok` from one state (`passes_iff_at`). -/
def Passes (m : EvalM PUnit) : Prop := ∀ s, (m.runState s).1 = .ok ()

theorem passes_iff_at {m : EvalM PUnit} (hm : Frame m) (s : EvalState) :
    Passes m ↔ (m.runState s).1 = .ok () :=
  ⟨fun h => h s, fun h s' => by rw [hm.indep s' s]; exact h⟩

theorem passes_pure : Passes (pure PUnit.unit) ↔ True := ⟨fun _ => trivial, fun _ _ => rfl⟩

theorem passes_error {e : Error} : Passes (EvalM.error e : EvalM PUnit) ↔ False :=
  ⟨fun h => (by have := h EvalState.empty; cases this), False.elim⟩

/-- A failed check fails its whole continuation, unvisited (used top-down, `↓`). -/
theorem passes_error_bind {α : Type} {e : Error} {k : α → EvalM PUnit} :
    Passes (EvalM.error e >>= k) ↔ False :=
  ⟨fun h => (by have := h EvalState.empty; cases this), False.elim⟩

theorem passes_ite {c : Prop} [Decidable c] {m m' : EvalM PUnit} :
    Passes (if c then m else m') ↔ (c → Passes m) ∧ (¬ c → Passes m') := by
  by_cases hc : c <;> simp [hc]

/-- A frame followed by a continuation passes exactly when both pass. -/
theorem passes_bind {m : EvalM PUnit} {k : PUnit → EvalM PUnit} (hm : Frame m) :
    Passes (m >>= k) ↔ Passes m ∧ Passes (k ()) := by
  constructor
  · intro h
    have hm' : Passes m := by
      intro s
      have hs := h s
      rw [EvalM.bind_runState] at hs
      rcases hr : m.runState s with ⟨o, t⟩
      rw [hr] at hs
      cases o with
      | ok u => rfl
      | error e => cases hs
    refine ⟨hm', fun s => ?_⟩
    have hs := h s
    rw [EvalM.bind_runState] at hs
    have h1 := hm' s
    have h2 := hm.state s
    rcases hr : m.runState s with ⟨o, t⟩
    rw [hr] at hs h1 h2
    simp only at h1 h2; subst h1 h2
    exact hs
  · rintro ⟨h1, h2⟩ s
    rw [EvalM.bind_runState]
    have h3 := h1 s
    have h4 := hm.state s
    rcases hr : m.runState s with ⟨o, t⟩
    rw [hr] at h3 h4
    simp only at h3 h4; subst h3 h4
    exact h2 _

/-- A `for` loop over frames passes exactly when every iteration passes. -/
theorem passes_forIn {α : Type} (l : List α) (g : α → EvalM PUnit) (hg : ∀ x ∈ l, Frame (g x)) :
    Passes (forIn l PUnit.unit fun x (_ : PUnit) => do g x; pure (ForInStep.yield PUnit.unit)) ↔
      ∀ x ∈ l, Passes (g x) := by
  induction l with
  | nil => simp only [List.forIn_nil, List.not_mem_nil, false_implies, implies_true, iff_true]; exact fun _ => rfl
  | cons x xs ih =>
    have hx := hg x (by simp)
    have ihx := ih (fun y hy => hg y (by simp [hy]))
    simp only [List.forIn_cons, List.mem_cons, forall_eq_or_imp]
    rw [← ihx]
    constructor
    · intro h
      have hgx : Passes (g x) := by
        intro s; have hs := h s
        rw [EvalM.bind_runState, EvalM.bind_runState] at hs
        rcases hr : (g x).runState s with ⟨o, t⟩
        rw [hr] at hs; cases o with | ok u => rfl | error e => cases hs
      refine ⟨hgx, fun s => ?_⟩
      have hs := h s
      rw [EvalM.bind_runState, EvalM.bind_runState] at hs
      have h1 := hgx s; have h2 := hx.state s
      rcases hr : (g x).runState s with ⟨o, t⟩
      rw [hr] at hs h1 h2; simp only at h1 h2; subst h1 h2
      exact hs
    · rintro ⟨h1, h2⟩ s
      rw [EvalM.bind_runState, EvalM.bind_runState]
      have h3 := h1 s; have h4 := hx.state s
      rcases hr : (g x).runState s with ⟨o, t⟩
      rw [hr] at h3 h4; simp only at h3 h4; subst h3 h4
      exact h2 _

/-- An `attach`ed `forM` over frames passes exactly when every element passes. -/
theorem passes_forM_attach {α : Type} (l : List α) (f : {x // x ∈ l} → EvalM PUnit)
    (hf : ∀ x (hx : x ∈ l), Frame (f ⟨x, hx⟩)) :
    Passes (l.attach.forM f) ↔ ∀ x (hx : x ∈ l), Passes (f ⟨x, hx⟩) := by
  suffices h : ∀ (l' : List {x // x ∈ l}), (Passes (l'.forM f) ↔ ∀ y ∈ l', Passes (f y)) by
    rw [h]; exact ⟨fun h x hx => h ⟨x, hx⟩ (List.mem_attach _ _), fun h y _ => h y.1 y.2⟩
  intro l'
  induction l' with
  | nil => exact ⟨fun _ _ h => (by cases h), fun _ _ => rfl⟩
  | cons y ys ih =>
    rw [List.forM_eq_forM, List.forM_cons, passes_bind (hf y.1 y.2), ← List.forM_eq_forM, ih]
    simp only [List.mem_cons, forall_eq_or_imp]

/-- The clause-family arity check passes exactly when both arity scans find no mismatch. -/
theorem passes_branchArities (name : Ident) (a : Algorithm) :
    Passes (validateConditionalBranchArities name a) ↔
      a.validateBranchArities = none ∧ a.validateBranchOutputArities = none := by
  unfold validateConditionalBranchArities
  split
  · next h => simp only [passes_error, h, reduceCtorEq, false_and]
  · next h =>
    split
    · next h2 => simp only [passes_error, h2, reduceCtorEq, and_false]
    · next h2 => simp only [passes_pure, h, h2, and_self]

/-! ## 2. The admitted set -/

mutual
/-- **AN ADMITTED ALGORITHM TREE** `a`, labelled `name` (the nearest enclosing property name, for
    clause-family diagnostics), in the static scope chain `chain` (outermost first), against the
    whole tree's alias count `aliases`. A loaded module root restarts the chain (Q-31 H-P). -/
def AdmittedAlgorithm (a : Algorithm) (name : Ident) (chain : List Algorithm) (aliases : Nat) : Prop :=
  let chain := if a.isModuleRoot then [] else chain
  let inner := chain ++ [a]
  a.hasSingletonSequencePattern = false ∧ a.hasMultipleCollectingCaptures = false ∧
  match a with
  | .mk parent? parameters op pr out _ =>
      ParameterPattern.signatureViolation? parameters ≠ some .repeatedNameIncludesCollecting ∧
      ParameterPattern.metaViolation? parameters = none ∧
      (parameters = [] ∨ out ≠ []) ∧
      (∀ e ∈ op, AdmittedExpr e inner aliases) ∧
      (∀ p ∈ pr, AdmittedAlgorithm p.alg p.name inner aliases) ∧
      (∀ e ∈ out, AdmittedExpr e inner aliases) ∧
      (match parent? with | none => True | some s => AdmittedScope s aliases)
  | .builtin _ => True
  | .conditional parent? op branches _ =>
      a.validateBranchArities = none ∧ a.validateBranchOutputArities = none ∧
      (∀ e ∈ op, AdmittedExpr e inner aliases) ∧
      (∀ b ∈ branches, AdmittedAlgorithm b.body name inner aliases) ∧
      (match parent? with | none => True | some s => AdmittedScope s aliases)
  | .alias parent? op pr target _ _ =>
      (target.isStaticAliasPath || target.isRuntimeAliasRow) = true ∧
      staticAliasCycle aliases chain a = false ∧
      (∀ e ∈ op, AdmittedExpr e inner aliases) ∧
      (∀ p ∈ pr, AdmittedAlgorithm p.alg p.name inner aliases) ∧
      AdmittedExpr target inner aliases ∧
      (match parent? with | none => True | some s => AdmittedScope s aliases)
termination_by sizeOf a
decreasing_by validation_decreasing

/-- **AN ADMITTED HOST-BUILT PARENT SCOPE**: its opens and property algorithms, in the scope's
    own static chain (`ScopeCtx.staticChain`), and its own parent. Its `output` and `branches` are
    identity data the validator does not walk, so they are unconstrained. -/
def AdmittedScope (s : ScopeCtx) (aliases : Nat) : Prop :=
  match s with
  | .mk parent? _ op pr _ _ _ _ =>
      (∀ e ∈ op, AdmittedExpr e s.staticChain aliases) ∧
      (∀ p ∈ pr, AdmittedAlgorithm p.alg p.name s.staticChain aliases) ∧
      (match parent? with | none => True | some outer => AdmittedScope outer aliases)
termination_by sizeOf s
decreasing_by validation_decreasing

/-- **AN ADMITTED EXPRESSION**: every block in it is admitted (labelled `conditional`), every
    subexpression is admitted — dot-call fallbacks and arguments included. -/
def AdmittedExpr (e : Expr) (chain : List Algorithm) (aliases : Nat) : Prop :=
  match e with
  | .interpolatedString _ links => ∀ link ∈ links, AdmittedExpr link.hole chain aliases
  | .unary _ operand | .sequenceSpread operand => AdmittedExpr operand chain aliases
  | .binary _ left right | .sequenceConstruct left right =>
      AdmittedExpr left chain aliases ∧ AdmittedExpr right chain aliases
  | .comparison first links =>
      AdmittedExpr first chain aliases ∧ ∀ link ∈ links, AdmittedExpr link.operand chain aliases
  | .index target items | .call target items =>
      AdmittedExpr target chain aliases ∧ ∀ item ∈ items, AdmittedExpr item chain aliases
  | .listLiteral items | .capture items => ∀ item ∈ items, AdmittedExpr item chain aliases
  | .algorithmExpr alg => AdmittedAlgorithm alg "conditional" chain aliases
  | .dotMember target _ fallback args? =>
      AdmittedExpr target chain aliases ∧ AdmittedExpr fallback chain aliases ∧
      (match args? with | none => True | some args => ∀ arg ∈ args, AdmittedExpr arg chain aliases)
  | _ => True
termination_by sizeOf e
decreasing_by validation_decreasing
end

/-- **THE ADMITTED SET** of the pre-evaluation validation: a program tree whose host provenance is
    coherent (HOST-LEAN-O6, `hostProvenanceViolation?`) and that is admitted at the root, with the
    empty static chain and the tree's own alias count. -/
def Admitted (e : Expr) : Prop :=
  hostProvenanceViolation? e = none ∧ AdmittedExpr e [] e.aliasCount

/-- The admitted set of one algorithm tree (`validateExplicitParamOutputInvariant`). -/
def AdmittedRoot (a : Algorithm) (name : Ident) : Prop :=
  hostProvenanceViolation? (.algorithmExpr a) = none ∧ AdmittedAlgorithm a name [] a.aliasCount

/-! ## 3. The characterization -/

/-- Discharge a side condition of the admitted-set rewriting: a member, a size bound, a frame. -/
macro "adm_disch" : tactic => `(tactic| first
  | assumption
  | (validation_decreasing; done)
  | (intro _ _; first | exact validateExprTree_frame _ _ _ | exact validateAlgorithmTree_frame _ _ _ _)
  | (intro _ _; frame_tac 400; done)
  | (frame_tac 400; done))

/- The proofs below rewrite the validator's `do` block into Prop, top-down: a check that fails
   closes its continuation unvisited (`↓passes_error_bind`; the `do` elaboration duplicates each
   continuation per `if`), a frame step splits off (`passes_bind`, its `Frame` side condition by
   `frame_tac`), a loop becomes a membership quantifier (`passes_forIn`, `passes_forM_attach`),
   and a recursive call on a proper subterm is the induction hypothesis, guarded by its size
   (`ihE`/`ihA`/`ihS`). What remains is propositional over the node checks (`grind`). -/
mutual
theorem validateScopeTree_passes (s : ScopeCtx) (aliases : Nat) :
    Passes (validateScopeTree s aliases) ↔ AdmittedScope s aliases := by
  have ihE := fun (x : Expr) (_ : sizeOf x < sizeOf s) c a => validateExprTree_passes x c a
  have ihA := fun (x : Algorithm) (_ : sizeOf x < sizeOf s) n c a => validateAlgorithmTree_passes x n c a
  have ihS := fun (x : ScopeCtx) (_ : sizeOf x < sizeOf s) a => validateScopeTree_passes x a
  rw [validateScopeTree.eq_def, AdmittedScope.eq_def]
  cases s with
  | mk parent? ps op pr out bs act id =>
  cases parent? <;> dsimp only <;>
  simp (config := { contextual := true }) (disch := adm_disch) only [passes_bind, passes_forIn,
    passes_pure, ihE, ihA, ihS]
termination_by sizeOf s
decreasing_by all_goals (simp_wf; assumption)

theorem validateAlgorithmTree_passes (a : Algorithm) (name : Ident) (chain : List Algorithm) (aliases : Nat) :
    Passes (validateAlgorithmTree a name chain aliases) ↔ AdmittedAlgorithm a name chain aliases := by
  have ihE := fun (x : Expr) (_ : sizeOf x < sizeOf a) c a => validateExprTree_passes x c a
  have ihA := fun (x : Algorithm) (_ : sizeOf x < sizeOf a) n c a => validateAlgorithmTree_passes x n c a
  have ihS := fun (x : ScopeCtx) (_ : sizeOf x < sizeOf a) a => validateScopeTree_passes x a
  rw [validateAlgorithmTree.eq_def, AdmittedAlgorithm.eq_def]
  dsimp only
  generalize (if a.isModuleRoot = true then ([] : List Algorithm) else chain) = ch
  cases a with
  | builtin b =>
    dsimp only; simp only [↓passes_ite, ↓passes_error_bind, passes_pure]
    grind
  | mk p ps op pr out id =>
    cases p <;> dsimp only <;> simp only [↓passes_ite, ↓passes_error_bind] <;> split
    all_goals simp (config := { contextual := true }) (disch := adm_disch) only [↓passes_ite,
      ↓passes_error_bind, passes_bind, passes_forIn, passes_pure, ihE, ihA, ihS]
    all_goals (cases hsv : ParameterPattern.signatureViolation? ps <;> simp_all <;> grind)
  | conditional p op bs id =>
    cases p <;> dsimp only <;> simp only [↓passes_ite, ↓passes_error_bind]
    all_goals simp (config := { contextual := true }) (disch := adm_disch) only [
      passes_bind, passes_forIn, passes_pure, passes_branchArities, ihE, ihA, ihS]
    all_goals (simp_all <;> grind)
  | alias p op pr t id r =>
    cases p <;> dsimp only <;> simp only [↓passes_ite, ↓passes_error_bind]
    all_goals simp (config := { contextual := true }) (disch := adm_disch) only [
      passes_bind, passes_forIn, passes_pure, ihE, ihA, ihS]
    all_goals (simp_all <;> grind)
termination_by sizeOf a
decreasing_by all_goals (simp_wf; assumption)

theorem validateExprTree_passes (e : Expr) (chain : List Algorithm) (aliases : Nat) :
    Passes (validateExprTree e chain aliases) ↔ AdmittedExpr e chain aliases := by
  have ihE := fun (x : Expr) (_ : sizeOf x < sizeOf e) c a => validateExprTree_passes x c a
  have ihA := fun (x : Algorithm) (_ : sizeOf x < sizeOf e) n c a => validateAlgorithmTree_passes x n c a
  rw [validateExprTree.eq_def, AdmittedExpr.eq_def]
  cases e
  all_goals (try cases ‹Option (List Expr)›)
  all_goals dsimp only
  all_goals simp (config := { contextual := true }) (disch := adm_disch) only [passes_bind, passes_forM_attach,
      passes_pure, ihE, ihA]
termination_by sizeOf e
decreasing_by all_goals (simp_wf; assumption)
end

/-- The program-level validation passes exactly on the admitted set. -/
theorem validate_passes (e : Expr) :
    Passes (validateExplicitParamOutputInvariantExpr e) ↔ Admitted e := by
  unfold validateExplicitParamOutputInvariantExpr Admitted
  split
  · next message heq =>
    simp only [passes_error_bind, heq, reduceCtorEq, false_and]
  · next heq =>
    dsimp only; rw [validateExprTree_passes]
    exact ⟨fun h => ⟨by cases h' : hostProvenanceViolation? e <;> simp_all, h⟩, fun h => h.2⟩

/-- **THE ADMITTED-SET THEOREM.** From any entry state, the pre-evaluation validation of `e`
    returns `ok` exactly when `e` is in the admitted set. -/
theorem validate_ok_iff (e : Expr) (s : EvalState) :
    ((validateExplicitParamOutputInvariantExpr e).runState s).1 = .ok () ↔ Admitted e := by
  rw [← validate_passes, passes_iff_at (validateExpr_isFrame e) s]

/-- Its complement: the validation fails — with a validator error, leaving the state unchanged —
    exactly outside the admitted set. -/
theorem validate_error_iff (e : Expr) (s : EvalState) :
    (∃ err, (validateExplicitParamOutputInvariantExpr e).runState s = (.error err, s) ∧ ValidatorError err) ↔
      ¬ Admitted e := by
  rw [← validate_ok_iff e s]
  have hst := (validate_frame e s).1
  constructor
  · rintro ⟨err, h, -⟩ hok
    rw [h] at hok; cases hok
  · intro hno
    rcases hr : (validateExplicitParamOutputInvariantExpr e).runState s with ⟨o, t⟩
    have ht : t = s := by have h0 := hst; rw [hr] at h0; exact h0
    rw [hr] at hno; simp only at hno
    cases o with
    | ok u => exact absurd rfl hno
    | error err => exact ⟨err, by rw [ht], (validate_frame e s).2 err (by rw [hr])⟩

/-- The algorithm-level validation (`validateExplicitParamOutputInvariant`) passes exactly on
    `AdmittedRoot`. -/
theorem validateAlgorithm_ok_iff (a : Algorithm) (name : Ident) (s : EvalState) :
    ((validateExplicitParamOutputInvariant a name).runState s).1 = .ok () ↔ AdmittedRoot a name := by
  rw [← passes_iff_at (validateAlgorithm_isFrame a name) s]
  unfold validateExplicitParamOutputInvariant AdmittedRoot
  split
  · next message heq =>
    simp only [passes_error_bind, heq, reduceCtorEq, false_and]
  · next heq =>
    dsimp only; rw [validateAlgorithmTree_passes]
    exact ⟨fun h => ⟨by cases h' : hostProvenanceViolation? (.algorithmExpr a) <;> simp_all, h⟩,
      fun h => h.2⟩

/-! ## 4. The public run over the admitted set -/

open KatLang.PublicRunBridge

/-- The tree the public run validates and evaluates. -/
abbrev identified (e : Expr) : Expr := (identifyPropertyExpr e).run' 0

/-- The public run OVER the validation: an admitted identified tree runs the root step from the
    entry state; any other one is refused at once. -/
theorem public_split (e : Expr) (s : EvalState) :
    (runResultM e).runState s =
      match (validateExplicitParamOutputInvariantExpr (identified e)).runState s with
      | (.ok _, t) => (rootRun evalUnbounded (identified e)).runState t
      | (.error err, t) => (.error err, t) := by
  unfold identified
  rw [runResultM_is_production, runResultWith_split, EvalM.bind_runState]
  rcases (validateExplicitParamOutputInvariantExpr ((identifyPropertyExpr e).run' 0)).runState s with ⟨o, t⟩
  cases o <;> rfl

/-- **A REFUSED PUBLIC RUN.** Outside the admitted set the public run fails with a validator
    error and returns its entry state: nothing is evaluated. -/
theorem public_refused (e : Expr) (s : EvalState) (h : ¬ Admitted (identified e)) :
    ∃ err, (runResultM e).runState s = (.error err, s) ∧ ValidatorError err := by
  obtain ⟨err, hv, herr⟩ := (validate_error_iff _ s).2 h
  exact ⟨err, by rw [public_split, hv], herr⟩

/-- **AN ADMITTED PUBLIC RUN** is its root step — wiring, the zero-supply gate and ONE root
    production call — from the entry state. -/
theorem public_admitted (e : Expr) (s : EvalState) (h : Admitted (identified e)) :
    (runResultM e).runState s = (rootRun evalUnbounded (identified e)).runState s := by
  have hok := (validate_ok_iff _ s).2 h
  have hst := (validate_frame (identified e) s).1
  rw [public_split]
  rcases hr : (validateExplicitParamOutputInvariantExpr (identified e)).runState s with ⟨o, t⟩
  rw [hr] at hok hst; simp only at hok hst; subst hok hst; rfl

/-- **PUBLIC INCOMPLETION, OUTCOME FORM.** From any entry state, the public outcome is the
    incomplete one exactly when the identified tree is admitted and the root step's outcome is
    incomplete: validation contributes no incompletion (`validate_never_incomplete`) and hands the
    root step the entry state itself. A statement about outcomes only (`Incomplete`); it neither
    excludes nor endorses a public incomplete outcome (Q-82, open). -/
theorem public_incomplete_iff_root (e : Expr) (s : EvalState) :
    Incomplete ((runResultM e).runState s).1 ↔
      Admitted (identified e) ∧ Incomplete ((rootRun evalUnbounded (identified e)).runState s).1 := by
  by_cases h : Admitted (identified e)
  · rw [public_admitted e s h]; exact ⟨fun hi => ⟨h, hi⟩, fun hi => hi.2⟩
  · obtain ⟨err, hr, herr⟩ := public_refused e s h
    rw [hr]
    exact ⟨fun hi => absurd hi (by unfold Incomplete; intro he; cases he; exact herr.ne_fuelExhausted rfl),
      fun hi => absurd hi.1 h⟩

/-- **PUBLIC INCOMPLETION FROM `EvalState.empty`.** The public run from the empty state is
    incomplete exactly when the identified tree is admitted and the root step over the total core
    is incomplete at EVERY fuel from the empty state. -/
theorem public_incomplete_from_empty (e : Expr) :
    Incomplete ((runResultM e).runState EvalState.empty).1 ↔
      Admitted (identified e) ∧
        ∀ n, Incomplete ((rootRun (evalFuel n) (identified e)).runState EvalState.empty).1 := by
  rw [public_incomplete_iff]
  by_cases h : Admitted (identified e)
  · have hok := (validate_ok_iff _ EvalState.empty).2 h
    have hst := (validate_frame (identified e) EvalState.empty).1
    have hsplit : ∀ n, (runResultWith (evalFuel n) e).runState EvalState.empty =
        (rootRun (evalFuel n) (identified e)).runState EvalState.empty := fun n => by
      rw [runResultWith_split, EvalM.bind_runState]
      rcases hr : (validateExplicitParamOutputInvariantExpr (identified e)).runState EvalState.empty with ⟨o, t⟩
      rw [hr] at hok hst; simp only at hok hst; subst hok hst; rfl
    simp only [hsplit]
    exact ⟨fun hi => ⟨h, hi⟩, fun hi => hi.2⟩
  · obtain ⟨err, hv, herr⟩ := (validate_error_iff _ EvalState.empty).2 h
    have hsplit : ∀ n, (runResultWith (evalFuel n) e).runState EvalState.empty =
        (.error err, EvalState.empty) := fun n => by
      rw [runResultWith_split, EvalM.bind_runState, hv]
    simp only [hsplit]
    exact ⟨fun hi => absurd (hi 0) (by unfold Incomplete; intro he; cases he; exact herr.ne_fuelExhausted rfl),
      fun hi => absurd hi.1 h⟩

end KatLang.AdmittedSet
