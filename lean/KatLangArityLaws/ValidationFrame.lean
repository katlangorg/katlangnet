import Lean
import KatLangArityLaws.PublicRunBridge
import KatLangArityLaws.AddressInvariantProduction

open KatLang KatLang.EvaluatorCore

/-!
# E-6 Tier 2: the total pre-evaluation validation and the public-run frame

`runResultM` (`lean/KatLang.lean`) runs identification, then the pre-evaluation validation
`validateExplicitParamOutputInvariantExpr`, then root wiring and ONE root production call. Since
FG-I1 identification and wiring are total; since this module's task the validation is total too:
`Algorithm.aliasCount`/`ScopeCtx.parentAliasCount`/`Expr.aliasCount`, `ScopeCtx.staticChain`,
`validateAlgorithmTree`/`validateScopeTree`/`validateExprTree` and the HOST-LEAN-O6 scan
`scanHostProvenance*` are well-founded definitions (formerly `partial`, kernel-opaque).

* **Former bodies** (§ 1): each former `partial` body, verbatim, is an equation of the total
  definition (`*_equation`). Where the total body differs in form (an `attach`ed `forM`, an
  explicit `match` on an optional child), the equation is proved, otherwise it is the unfolding.
* **The validator frame** (§ 2–3): `validate_frame` — the validation leaves the state unchanged and
  fails only with a `ValidatorError`; `validate_never_incomplete` — it never yields the incomplete
  outcome (`PublicRunBridge.Incomplete`); `validate_state_independent` — its outcome does not depend
  on the entry state.
* **Identification keeps the root shape** (§ 4): `identify_root_shape`.
* **The public address invariant** (§ 5, E-5's `runResultM`-level instance): `public_inv` — from
  every `AddressInvariant.Inv` entry state the public run ends in an `Inv` state, and a completed
  value is address-valid there; `public_inv_from_empty`.

What stays parametric: the prefix reaches `reprStr` in `HostProvenanceScan.level` during
validation and in `sameDeclaringScope`'s fallback on the root wiring's scope-comparison path. The
`Repr` printers it calls are total since E-6 Tier 3 (written out, `lean/KatLang.lean` § Total
`Repr` printers); the core layout `Std.Format.pretty` inside `reprStr` stays kernel-opaque. The
validator frame proofs never compute it: they read only `hostProvenanceViolation?`'s three outcome
shapes. Which trees the validation accepts is `AdmittedSet` (E-6 Tier 3). Nothing here claims the public run
never returns the incomplete outcome (Constitution Q-82, open): incomplete runs are related by
outcome only, through `PublicRunBridge.Incomplete`.
-/

namespace KatLang.ValidationFrame

/-! ## 1. The former bodies -/

/-- An `attach`ed `forM` whose body ignores the membership proof is the plain `forM`. -/
theorem forM_attachWith_eq {m : Type → Type} [Monad m] {α : Type} (l : List α) (P : α → Prop)
    (H : ∀ x ∈ l, P x) (g : {x // P x} → m PUnit) (f : α → m PUnit) (h : ∀ x hx, g ⟨x, hx⟩ = f x) :
    (l.attachWith P H).forM g = l.forM f := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.attachWith_cons, List.forM_eq_forM, List.forM_cons, h]
    rw [← List.forM_eq_forM, ← List.forM_eq_forM, ih]

theorem forM_attach_eq {m : Type → Type} [Monad m] {α : Type} (l : List α)
    (g : {x // x ∈ l} → m PUnit) (f : α → m PUnit) (h : ∀ x hx, g ⟨x, hx⟩ = f x) :
    l.attach.forM g = l.forM f :=
  forM_attachWith_eq l _ _ g f h

/-- `forM_attach_eq` in the shape a simplified `attach`ed body takes (`fun x => f x.val`). -/
theorem forM_attach_val {m : Type → Type} [Monad m] {α : Type} (l : List α) (f : α → m PUnit) :
    (l.attach.forM fun x => f x.val) = l.forM f :=
  forM_attach_eq l _ f (fun _ _ => rfl)

/-- `forM_attach_val` through a field: `fun x => f (g x.val)`. -/
theorem forM_attach_comp {m : Type → Type} [Monad m] {α β : Type} (l : List α) (f : β → m PUnit)
    (g : α → β) : (l.attach.forM fun x => f (g x.val)) = l.forM (fun y => f (g y)) :=
  forM_attach_eq l _ _ (fun _ _ => rfl)

/-- The former body of `Algorithm.aliasCount` (unchanged). -/
theorem Algorithm.aliasCount_equation (a : Algorithm) :
    a.aliasCount = match a with
      | .mk p _ op pr out _ =>
          ScopeCtx.parentAliasCount p + (op.map Expr.aliasCount).sum
            + (pr.map (fun prop => prop.alg.aliasCount)).sum + (out.map Expr.aliasCount).sum
      | .builtin _ => 0
      | .conditional p op branches _ =>
          ScopeCtx.parentAliasCount p + (op.map Expr.aliasCount).sum
            + (branches.map (fun branch => branch.body.aliasCount)).sum
      | .alias p op pr target _ _ =>
          1 + ScopeCtx.parentAliasCount p + (op.map Expr.aliasCount).sum
            + (pr.map (fun prop => prop.alg.aliasCount)).sum + target.aliasCount := by
  cases a <;> rw [Algorithm.aliasCount]

/-- The former body of `ScopeCtx.parentAliasCount` (unchanged). -/
theorem ScopeCtx.parentAliasCount_equation (p : Option ScopeCtx) :
    ScopeCtx.parentAliasCount p = match p with
      | none => 0
      | some (.mk parent? _ op pr _ _ _ _) =>
          ScopeCtx.parentAliasCount parent? + (op.map Expr.aliasCount).sum
            + (pr.map (fun prop => prop.alg.aliasCount)).sum := by
  rw [ScopeCtx.parentAliasCount.eq_def]
  rcases p with _ | ⟨_⟩ <;> rfl

/-- The former body of `Expr.aliasCount`: its `dotMember` row read `args?.getD []`. -/
theorem Expr.aliasCount_equation (e : Expr) :
    e.aliasCount = match e with
      | .algorithmExpr alg => alg.aliasCount
      | .unary _ operand => operand.aliasCount
      | .binary _ left right => left.aliasCount + right.aliasCount
      | .comparison first links => first.aliasCount + (links.map (fun link => link.operand.aliasCount)).sum
      | .index target selectors => target.aliasCount + (selectors.map Expr.aliasCount).sum
      | .sequenceConstruct left right => left.aliasCount + right.aliasCount
      | .sequenceSpread operand => operand.aliasCount
      | .listLiteral items => (items.map Expr.aliasCount).sum
      | .capture rows => (rows.map Expr.aliasCount).sum
      | .call fn args => fn.aliasCount + (args.map Expr.aliasCount).sum
      | .dotMember target _ fallback args? =>
          target.aliasCount + fallback.aliasCount + ((args?.getD []).map Expr.aliasCount).sum
      | _ => 0 := by
  rw [Expr.aliasCount.eq_def]
  cases e
  case dotMember t n f args => cases args <;> rfl
  all_goals rfl

/-- The former body of `ScopeCtx.staticChain`: it read `(parent?.map ScopeCtx.staticChain).getD []`. -/
theorem ScopeCtx.staticChain_equation (s : ScopeCtx) :
    s.staticChain = match s with
      | .mk parent? _ op pr _ _ _ _ =>
          ((parent?.map ScopeCtx.staticChain).getD []) ++ [Algorithm.mk none [] op pr [] none] := by
  rcases s with ⟨_ | _⟩ <;> rfl

/-- The former body of `validateAlgorithmTree` (unchanged). -/
theorem validateAlgorithmTree_equation (a : Algorithm) (name : Ident) (chain : List Algorithm)
    (aliases : Nat) :
    validateAlgorithmTree a name chain aliases = (do
      let chain := if a.isModuleRoot then [] else chain
      if a.hasSingletonSequencePattern then
        .error (Error.illegalInEval singletonSequencePatternMessage)
      if a.hasMultipleCollectingCaptures then
        .error (Error.illegalInEval multipleCollectingBindingsPerLevelMessage)
      let inner := chain ++ [a]
      match a with
      | .mk parent? parameters op pr out _ =>
          if let some .repeatedNameIncludesCollecting := ParameterPattern.signatureViolation? parameters then
            .error (Error.illegalInEval repeatedNameIncludesCollectingMessage)
          if (ParameterPattern.metaViolation? parameters).isSome then
            .error (Error.illegalInEval invalidMetaParameterMessage)
          if !parameters.isEmpty && out.isEmpty then
            .error Error.explicitParamsRequireOutput
          for openExpr in op do
            validateExprTree openExpr inner aliases
          for prop in pr do
            validateAlgorithmTree prop.alg prop.name inner aliases
          for expr in out do
            validateExprTree expr inner aliases
          if let some scope := parent? then
            validateScopeTree scope aliases
      | .builtin _ => pure ()
      | .conditional parent? op branches _ =>
          validateConditionalBranchArities name a
          for openExpr in op do
            validateExprTree openExpr inner aliases
          for branch in branches do
            validateAlgorithmTree branch.body name inner aliases
          if let some scope := parent? then
            validateScopeTree scope aliases
      | .alias parent? op pr target _ _ =>
          if !(target.isStaticAliasPath || target.isRuntimeAliasRow) then
            .error (Error.illegalInEval (aliasTargetNotStaticPathMessage (openExprName target)))
          if staticAliasCycle aliases chain a then
            .error (Error.illegalInEval aliasCycleMessage)
          for openExpr in op do
            validateExprTree openExpr inner aliases
          for prop in pr do
            validateAlgorithmTree prop.alg prop.name inner aliases
          validateExprTree target inner aliases
          if let some scope := parent? then
            validateScopeTree scope aliases : EvalM Unit) := by
  rw [validateAlgorithmTree.eq_def]; rfl

/-- The former body of `validateScopeTree` (unchanged). -/
theorem validateScopeTree_equation (s : ScopeCtx) (aliases : Nat) :
    validateScopeTree s aliases = (do
      let chain := s.staticChain
      match s with
      | .mk parent? _ op pr _ _ _ _ =>
          for openExpr in op do
            validateExprTree openExpr chain aliases
          for prop in pr do
            validateAlgorithmTree prop.alg prop.name chain aliases
          if let some outer := parent? then
            validateScopeTree outer aliases : EvalM Unit) := by
  rw [validateScopeTree.eq_def]; rfl

/-- Close a former-body goal whose `forM` walked the list itself where the total body walks its
    `attach`ment: through the binds, then `forM_attach_eq`. -/
macro "attach_equation" : tactic => `(tactic| repeat (first
  | rfl
  | exact forM_attach_eq _ _ _ (fun _ _ => rfl)
  | (congr 1; funext _)))

/-- The former body of `validateExprTree`: its `forM`s walked the lists themselves. -/
theorem validateExprTree_equation (e : Expr) (chain : List Algorithm) (aliases : Nat) :
    validateExprTree e chain aliases = (match e with
      | .param _ => pure ()
      | .num _ => pure ()
      | .stringLiteral _ => pure ()
      | .boolLiteral _ => pure ()
      | .resolve _ => pure ()
      | .unary _ operand =>
          validateExprTree operand chain aliases
      | .binary _ left right => do
          validateExprTree left chain aliases
          validateExprTree right chain aliases
      | .comparison first links => do
          validateExprTree first chain aliases
          links.forM (fun link => validateExprTree link.operand chain aliases)
      | .index target selectors => do
          validateExprTree target chain aliases
          selectors.forM (fun selector => validateExprTree selector chain aliases)
      | .sequenceConstruct left right => do
        validateExprTree left chain aliases
        validateExprTree right chain aliases
      | .emptySequence _ => pure ()
      | .sequenceSpread operand => do
          validateExprTree operand chain aliases
      | .listLiteral items =>
          items.forM (fun item => validateExprTree item chain aliases)
      | .algorithmExpr alg =>
          validateAlgorithmTree alg "conditional" chain aliases
      | .capture rows =>
          rows.forM (fun row => validateExprTree row chain aliases)
      | .call fn args => do
          validateExprTree fn chain aliases
          args.forM (fun arg => validateExprTree arg chain aliases)
      | .dotMember target _ fallback args? => do
          validateExprTree target chain aliases
          validateExprTree fallback chain aliases
          match args? with
          | some args => args.forM (fun arg => validateExprTree arg chain aliases)
          | none => pure () : EvalM Unit) := by
  rw [validateExprTree.eq_def]
  cases e
  case dotMember t n f args => cases args <;> dsimp only <;> attach_equation
  all_goals dsimp only
  all_goals attach_equation

/-- The former body of `scanHostProvenanceExpr`. -/
theorem scanHostProvenanceExpr_equation (e : Expr) :
    scanHostProvenanceExpr e = (match e with
      | .algorithmExpr a => scanHostProvenanceAlgorithm a
      | .unary _ operand => scanHostProvenanceExpr operand
      | .binary _ left right => do scanHostProvenanceExpr left; scanHostProvenanceExpr right
      | .comparison first links => do
          scanHostProvenanceExpr first
          links.forM (scanHostProvenanceExpr ·.operand)
      | .index target selectors => do
          scanHostProvenanceExpr target
          selectors.forM scanHostProvenanceExpr
      | .sequenceConstruct left right => do scanHostProvenanceExpr left; scanHostProvenanceExpr right
      | .sequenceSpread operand => scanHostProvenanceExpr operand
      | .listLiteral items => items.forM scanHostProvenanceExpr
      | .capture rows => rows.forM scanHostProvenanceExpr
      | .call fn args => do scanHostProvenanceExpr fn; args.forM scanHostProvenanceExpr
      | .dotMember target _ fallback args? => do
          scanHostProvenanceExpr target
          scanHostProvenanceExpr fallback
          (args?.getD []).forM scanHostProvenanceExpr
      | _ => pure () : StateM HostProvenanceScan Unit) := by
  rw [scanHostProvenanceExpr.eq_def]
  cases e
  all_goals (try cases ‹Option (List Expr)›)
  all_goals simp only [Option.getD, List.forM, forM_attach_val, forM_attach_comp]

/-- The former body of `scanHostProvenanceAlgorithm`: it read each optional parent with
    `Option.forM`. -/
theorem scanHostProvenanceAlgorithm_equation (a : Algorithm) :
    scanHostProvenanceAlgorithm a = (do
      if (PropertyIdentity.hostToken? a.declarationId).isSome then
        modify fun scan => { scan with misplaced := true }
      match a with
      | .builtin _ => pure ()
      | .mk parent _ opens props output _ => do
          parent.forM scanHostProvenanceScope
          opens.forM scanHostProvenanceExpr
          props.forM scanHostProvenanceProperty
          output.forM scanHostProvenanceExpr
      | .conditional parent opens branches _ => do
          parent.forM scanHostProvenanceScope
          opens.forM scanHostProvenanceExpr
          branches.forM (scanHostProvenanceAlgorithm ·.body)
      | .alias parent opens props target _ _ => do
          parent.forM scanHostProvenanceScope
          opens.forM scanHostProvenanceExpr
          props.forM scanHostProvenanceProperty
          scanHostProvenanceExpr target : StateM HostProvenanceScan Unit) := by
  rw [scanHostProvenanceAlgorithm.eq_def]
  cases a
  all_goals (try cases ‹Option ScopeCtx›)
  all_goals simp only [Option.forM, pure_bind, forM_attach_val, forM_attach_comp]

/-- The former body of `scanHostProvenanceScope`. -/
theorem scanHostProvenanceScope_equation (scope : ScopeCtx) :
    scanHostProvenanceScope scope = (do
      match scope with
      | .mk parent _ opens props output branches _ id => do
          if let some token := PropertyIdentity.hostToken? id then
            modify (HostProvenanceScan.level scope token)
          parent.forM scanHostProvenanceScope
          opens.forM scanHostProvenanceExpr
          props.forM scanHostProvenanceProperty
          output.forM scanHostProvenanceExpr
          branches.forM (scanHostProvenanceAlgorithm ·.body) : StateM HostProvenanceScan Unit) := by
  rw [scanHostProvenanceScope.eq_def]
  cases scope
  all_goals (try cases ‹Option ScopeCtx›)
  all_goals simp only [Option.forM, pure_bind, forM_attach_val, forM_attach_comp]
  all_goals rfl

/-- The former body of `scanHostProvenanceProperty` (unchanged). -/
theorem scanHostProvenanceProperty_equation (p : PropDef) :
    scanHostProvenanceProperty p = (do
      if (PropertyIdentity.hostToken? p.identity).isSome then
        modify fun scan => { scan with misplaced := true }
      scanHostProvenanceAlgorithm p.alg : StateM HostProvenanceScan Unit) := by
  rw [scanHostProvenanceProperty.eq_def]

/-! ## 2. The error set and the frame of one validation step -/

/-- THE VALIDATOR'S ERROR SET: every error the pre-evaluation validation can raise — the
    host-provenance check's two messages (HOST-LEAN-O6), the five fixed pattern/alias messages,
    a non-static alias target, explicit parameters without output, and the two conditional
    arity mismatches. -/
inductive ValidatorError : Error → Prop
  | hostMisplaced : ValidatorError (.illegalInEval hostIdentityMisplacedMessage)
  | hostIncoherent (t : Nat) : ValidatorError (.illegalInEval (hostProvenanceIncoherentMessage t))
  | illegal (m : String) : m ∈ [singletonSequencePatternMessage, multipleCollectingBindingsPerLevelMessage,
      repeatedNameIncludesCollectingMessage, invalidMetaParameterMessage, aliasCycleMessage] →
      ValidatorError (.illegalInEval m)
  | aliasTarget (n : String) : ValidatorError (.illegalInEval (aliasTargetNotStaticPathMessage n))
  | explicitParams : ValidatorError .explicitParamsRequireOutput
  | branchArity (n : String) (a b : Nat) : ValidatorError (.branchArityMismatch n a b)
  | branchOutputArity (n : String) (a b : Nat) : ValidatorError (.branchOutputArityMismatch n a b)

namespace ValidatorError
theorem singleton : ValidatorError (.illegalInEval singletonSequencePatternMessage) :=
  .illegal _ (List.mem_cons_self ..)
theorem multipleCollecting : ValidatorError (.illegalInEval multipleCollectingBindingsPerLevelMessage) :=
  .illegal _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
theorem repeatedName : ValidatorError (.illegalInEval repeatedNameIncludesCollectingMessage) :=
  .illegal _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
theorem invalidMeta : ValidatorError (.illegalInEval invalidMetaParameterMessage) :=
  .illegal _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
theorem aliasCycle : ValidatorError (.illegalInEval aliasCycleMessage) :=
  .illegal _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))

/-- No validator error is the incomplete outcome. -/
theorem ne_fuelExhausted {e : Error} (h : ValidatorError e) : e ≠ .fuelExhausted := by
  cases h <;> intro h' <;> cases h'
end ValidatorError

/-- A VALIDATION STEP: it never changes the state, its outcome does not depend on the state, and it
    fails only with a validator error. -/
structure Frame {α : Type} (m : EvalM α) : Prop where
  state : ∀ s, (m.runState s).2 = s
  indep : ∀ s s', (m.runState s).1 = (m.runState s').1
  errors : ∀ s err, (m.runState s).1 = .error err → ValidatorError err

namespace Frame

theorem pure' {α : Type} (a : α) : Frame (pure a : EvalM α) :=
  ⟨fun _ => rfl, fun _ _ => rfl, fun _ _ h => by cases h⟩

theorem error' {α : Type} {e : Error} (h : ValidatorError e) : Frame (EvalM.error e : EvalM α) :=
  ⟨fun _ => rfl, fun _ _ => rfl, fun _ _ he => by cases he; exact h⟩

/-- A step that fails at once frames whatever follows it. -/
theorem error_bind {α β : Type} {e : Error} {k : α → EvalM β} (h : ValidatorError e) :
    Frame (EvalM.error e >>= k) :=
  ⟨fun _ => rfl, fun _ _ => rfl, fun _ _ he => by cases he; exact h⟩

theorem bind' {α β : Type} {m : EvalM α} {k : α → EvalM β} (hm : Frame m) (hk : ∀ a, Frame (k a)) :
    Frame (m >>= k) := by
  refine ⟨fun s => ?_, fun s s' => ?_, fun s err he => ?_⟩
  · rw [EvalM.bind_runState]
    have h2 := hm.state s
    rcases hr : m.runState s with ⟨o, t⟩
    rw [hr] at h2; subst h2
    cases o with
    | ok a => exact (hk a).state _
    | error e => rfl
  · rw [EvalM.bind_runState, EvalM.bind_runState]
    have h1 := hm.indep s s'
    have h2 := hm.state s
    have h3 := hm.state s'
    rcases hr : m.runState s with ⟨o, t⟩
    rcases hr' : m.runState s' with ⟨o', t'⟩
    rw [hr, hr'] at h1; rw [hr] at h2; rw [hr'] at h3
    simp only at h1 h2 h3; subst h1 h2 h3
    cases o with
    | ok a => exact (hk a).indep _ _
    | error e => rfl
  · rw [EvalM.bind_runState] at he
    rcases hr : m.runState s with ⟨o, t⟩
    rw [hr] at he
    cases o with
    | ok a => exact (hk a).errors _ _ he
    | error e =>
      have hee : e = err := by simpa using he
      subst hee; exact hm.errors s e (by rw [hr])

theorem ite' {α : Type} {c : Prop} [Decidable c] {m m' : EvalM α} (h : Frame m) (h' : Frame m') :
    Frame (if c then m else m') := by
  by_cases hc : c <;> simp [hc, h, h']

theorem forIn' {α β : Type} (l : List α) (b : β) (f : α → β → EvalM (ForInStep β))
    (h : ∀ x ∈ l, ∀ b, Frame (f x b)) : Frame (forIn l b f) := by
  induction l generalizing b with
  | nil => exact pure' b
  | cons x xs ih =>
    rw [List.forIn_cons]
    refine bind' (h x (by simp) b) (fun r => ?_)
    cases r with
    | done b => exact pure' b
    | yield b => exact ih b (fun y hy => h y (by simp [hy]))

theorem forM' {α : Type} (l : List α) (f : α → EvalM PUnit) (h : ∀ x ∈ l, Frame (f x)) :
    Frame (l.forM f) := by
  induction l with
  | nil => exact pure' _
  | cons x xs ih =>
    rw [List.forM_eq_forM, List.forM_cons]
    exact bind' (h x (by simp)) (fun _ => by rw [← List.forM_eq_forM]; exact ih (fun y hy => h y (by simp [hy])))

theorem forM_attach {α : Type} (l : List α) (f : {x // x ∈ l} → EvalM PUnit)
    (h : ∀ x (hx : x ∈ l), Frame (f ⟨x, hx⟩)) : Frame (l.attach.forM f) :=
  forM' _ _ (fun ⟨x, hx⟩ _ => h x hx)

end Frame

theorem branchArities_frame (name : Ident) (a : Algorithm) :
    Frame (validateConditionalBranchArities name a) := by
  unfold validateConditionalBranchArities
  split
  · exact Frame.error' (.branchArity _ _ _)
  · split
    · exact Frame.error' (.branchOutputArity _ _ _)
    · exact Frame.pure' _

/-! ### A syntax-directed frame tactic

The validators' `do` blocks elaborate to binds, `if`s, `for` loops, `attach`ed `forM`s, matches and
recursive calls. `frame_tac` applies the matching `Frame` lemma by the HEAD of the monadic term (a
plain `apply` would unify against the well-founded definitions and the message strings), a thrown
error closes by its message's `ValidatorError` lemma, and a failed check closes its continuation
(`Frame.error_bind`) without re-proving it. -/

open Lean Elab Tactic Meta in
/-- The monadic term under `Frame` in the main goal. -/
def frameTerm : TacticM Lean.Expr := do
  let tgt ← whnfR (← getMainTarget)
  let some m := tgt.getAppArgs.back? | throwError "frame: no term"
  return m

open Lean Meta in
/-- The `ValidatorError` lemma for a thrown error term. -/
def frameErrorLemma (err : Lean.Expr) : MetaM Name := do
  let eh := err.getAppFn.constName?.getD .anonymous
  if eh == ``Error.explicitParamsRequireOutput then return ``ValidatorError.explicitParams
  if eh == ``Error.branchArityMismatch then return ``ValidatorError.branchArity
  if eh == ``Error.branchOutputArityMismatch then return ``ValidatorError.branchOutputArity
  unless eh == ``Error.illegalInEval do throwError "frame: unknown error {eh}"
  let some msg := err.getAppArgs.back? | throwError "frame: no message"
  let mh := msg.getAppFn.constName?.getD .anonymous
  if mh == ``singletonSequencePatternMessage then return ``ValidatorError.singleton
  if mh == ``multipleCollectingBindingsPerLevelMessage then return ``ValidatorError.multipleCollecting
  if mh == ``repeatedNameIncludesCollectingMessage then return ``ValidatorError.repeatedName
  if mh == ``invalidMetaParameterMessage then return ``ValidatorError.invalidMeta
  if mh == ``aliasCycleMessage then return ``ValidatorError.aliasCycle
  if mh == ``aliasTargetNotStaticPathMessage then return ``ValidatorError.aliasTarget
  if mh == ``hostIdentityMisplacedMessage then return ``ValidatorError.hostMisplaced
  if mh == ``hostProvenanceIncoherentMessage then return ``ValidatorError.hostIncoherent
  throwError "frame: unknown message {mh}"

open Lean Elab Tactic Meta in
/-- Close `ValidatorError err` for a thrown `err`. -/
def frameErrorTac (err : Lean.Expr) : TacticM Unit := do
  let l := mkIdent (← frameErrorLemma err)
  evalTactic (← `(tactic| first | exact $l | exact $l _ | exact $l _ _ _))

open Lean Elab Tactic Meta in
/-- One syntax-directed step of a frame proof, chosen by the head of the monadic term. -/
def frameStep : TacticM Unit := do
  let m ← frameTerm
  let h := m.getAppFn.constName?.getD .anonymous
  if h == ``ite then evalTactic (← `(tactic| apply Frame.ite'))
  else if h == ``Bind.bind then
    let x := m.getAppArgs[4]!
    if x.getAppFn.constName? == some ``EvalM.error then
      let some err := x.getAppArgs.back? | throwError "frame: no error"
      evalTactic (← `(tactic| apply Frame.error_bind))
      frameErrorTac err
    else evalTactic (← `(tactic| refine Frame.bind' ?_ (fun _ => ?_)))
  else if h == ``ForIn.forIn then evalTactic (← `(tactic| (apply Frame.forIn'; intro _ _ _)))
  else if h == ``List.forM then evalTactic (← `(tactic| (apply Frame.forM_attach; intro _ _; dsimp only)))
  else if h == ``Pure.pure then evalTactic (← `(tactic| exact Frame.pure' _))
  else if h == ``validateConditionalBranchArities then
    evalTactic (← `(tactic| exact branchArities_frame _ _))
  else if h == ``EvalM.error then
    let some err := m.getAppArgs.back? | throwError "frame: no error"
    evalTactic (← `(tactic| apply Frame.error'))
    frameErrorTac err
  else if h == ``validateExprTree then
    evalTactic (← `(tactic| exact $(mkIdent `validateExprTree_frame) _ _ _))
  else if h == ``validateAlgorithmTree then
    evalTactic (← `(tactic| exact $(mkIdent `validateAlgorithmTree_frame) _ _ _ _))
  else if h == ``validateScopeTree then
    evalTactic (← `(tactic| exact $(mkIdent `validateScopeTree_frame) _ _))
  else evalTactic (← `(tactic| split))

open Lean Elab Tactic Meta in
/-- Run `frameStep` on every open goal until none makes progress (at most `n` rounds). -/
elab "frame_tac" n:num : tactic => do
  for _ in [0:n.getNat] do
    let gs ← getGoals
    if gs.isEmpty then return
    let mut progress := false
    let mut next : List MVarId := []
    for g in gs do
      setGoals [g]
      try
        frameStep
        progress := true
        next := next ++ (← getGoals)
      catch _ =>
        next := next ++ [g]
    setGoals next
    if !progress then return

/-! ## 3. The validators are validation steps -/

mutual
/-- `validateAlgorithmTree` is a validation step, for every tree, label, chain and alias count. -/
theorem validateAlgorithmTree_frame (a : Algorithm) (name : Ident) (chain : List Algorithm)
    (aliases : Nat) : Frame (validateAlgorithmTree a name chain aliases) := by
  rw [validateAlgorithmTree.eq_def]
  cases a
  all_goals (try cases ‹Option ScopeCtx›)
  all_goals dsimp only
  all_goals frame_tac 400
termination_by sizeOf a
decreasing_by validation_decreasing

theorem validateScopeTree_frame (s : ScopeCtx) (aliases : Nat) :
    Frame (validateScopeTree s aliases) := by
  rw [validateScopeTree.eq_def]
  cases s
  all_goals (try cases ‹Option ScopeCtx›)
  all_goals dsimp only
  all_goals frame_tac 400
termination_by sizeOf s
decreasing_by validation_decreasing

theorem validateExprTree_frame (e : Expr) (chain : List Algorithm) (aliases : Nat) :
    Frame (validateExprTree e chain aliases) := by
  rw [validateExprTree.eq_def]
  cases e
  all_goals (try cases ‹Option (List Expr)›)
  all_goals dsimp only
  all_goals frame_tac 400
termination_by sizeOf e
decreasing_by validation_decreasing
end

/-- The host-provenance check refuses only with its two messages. -/
theorem hostProvenanceViolation_error (e : Expr) (m : String) (h : hostProvenanceViolation? e = some m) :
    ValidatorError (.illegalInEval m) := by
  unfold hostProvenanceViolation? at h
  generalize (StateT.run (scanHostProvenanceExpr e) {}).snd = scan at h
  dsimp only at h
  split at h
  · cases h; exact .hostMisplaced
  · rcases Option.map_eq_some_iff.1 h with ⟨t, -, rfl⟩
    exact .hostIncoherent t

/-- The whole pre-evaluation validation of a program is a validation step. -/
theorem validateExpr_isFrame (e : Expr) : Frame (validateExplicitParamOutputInvariantExpr e) := by
  unfold validateExplicitParamOutputInvariantExpr
  split
  · next message heq => exact Frame.error_bind (hostProvenanceViolation_error e message heq)
  · exact Frame.bind' (Frame.pure' _) (fun _ => validateExprTree_frame _ _ _)

/-- The pre-evaluation validation of one algorithm tree is a validation step. -/
theorem validateAlgorithm_isFrame (a : Algorithm) (name : Ident) :
    Frame (validateExplicitParamOutputInvariant a name) := by
  unfold validateExplicitParamOutputInvariant
  split
  · next message heq => exact Frame.error_bind (hostProvenanceViolation_error _ message heq)
  · exact Frame.bind' (Frame.pure' _) (fun _ => validateAlgorithmTree_frame _ _ _ _)

/-- **THE VALIDATOR FRAME.** The validation leaves the state unchanged and fails only with a
    validator error. -/
theorem validate_frame (e : Expr) (s : EvalState) :
    ((validateExplicitParamOutputInvariantExpr e).runState s).2 = s ∧
    ∀ err, ((validateExplicitParamOutputInvariantExpr e).runState s).1 = .error err → ValidatorError err :=
  ⟨(validateExpr_isFrame e).state s, (validateExpr_isFrame e).errors s⟩

/-- The validation never yields the incomplete outcome. -/
theorem validate_never_incomplete (e : Expr) (s : EvalState) :
    ¬ PublicRunBridge.Incomplete ((validateExplicitParamOutputInvariantExpr e).runState s).1 := by
  intro h
  exact ((validate_frame e s).2 _ h).ne_fuelExhausted rfl

/-- The validation's outcome does not depend on the entry state. -/
theorem validate_state_independent (e : Expr) (s s' : EvalState) :
    ((validateExplicitParamOutputInvariantExpr e).runState s).1 =
      ((validateExplicitParamOutputInvariantExpr e).runState s').1 :=
  (validateExpr_isFrame e).indep s s'

/-! ## 4. Identification keeps the root shape -/

/-- Whether an expression is a block root. -/
def isBlock : Expr → Bool
  | .algorithmExpr _ => true
  | _ => false

/-- Identification keeps whether an expression is a block root. -/
theorem identify_isBlock (e : Expr) : isBlock ((identifyPropertyExpr e).run' 0) = isBlock e := by
  cases e
  case dotMember t n f args => rw [identifyPropertyExpr]; cases args <;> rfl
  all_goals (rw [identifyPropertyExpr]; rfl)

/-- Identification maps a block root to a block root and anything else to a non-block. -/
theorem identify_root_shape (e : Expr) :
    (∃ a, e = .algorithmExpr a) ↔ ∃ a', (identifyPropertyExpr e).run' 0 = .algorithmExpr a' := by
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨_, by rw [identifyPropertyExpr]; rfl⟩
  · rintro ⟨a', h⟩
    have hb := identify_isBlock e
    rw [h] at hb
    cases e
    case algorithmExpr a => exact ⟨a, rfl⟩
    all_goals cases hb

/-! ## 5. The public address invariant (E-5's `runResultM`-level instance) -/

open KatLang.AddressInvariant

/-- The run-result boundary keeps the state and returns its value unchanged when it accepts it. -/
theorem exportRunValue_runState (v : Result) (t : EvalState) :
    (exportRunValue v).runState t =
      (if v.containsCallRef then .error (Error.typeMismatch callReferenceLeavesRunMessage) else .ok v, t) := by
  unfold exportRunValue requireCallRefFree
  by_cases h : v.containsCallRef <;> simp [h] <;> rfl

/-- One production root call followed by the run-result boundary keeps `Inv` and returns a valid
    value. -/
theorem export_after_sound (m : EvalM Result) (hm : SoundOver Inv (fun _ => True) m (fun r h => RV h r))
    (s : EvalState) (hs : Inv s) :
    Inv ((m >>= exportRunValue).runState s).2 ∧
    ∀ r, ((m >>= exportRunValue).runState s).1 = .ok r → RV ((m >>= exportRunValue).runState s).2.needs r := by
  obtain ⟨hv, -, hr⟩ := hm s hs trivial
  rw [EvalM.bind_runState]
  rcases hrun : m.runState s with ⟨o, t⟩
  rw [hrun] at hv hr
  cases o with
  | error err => exact ⟨hv, fun r h => by cases h⟩
  | ok v =>
    simp only
    rw [exportRunValue_runState]
    refine ⟨hv, fun r h => ?_⟩
    by_cases hc : v.containsCallRef
    · simp [hc] at h
    · simp [hc] at h; subst h; exact hr v rfl

/-- **THE PUBLIC ADDRESS INVARIANT.** From every `Inv` entry state, the public run ends in an `Inv`
    state, and a completed value mentions only addresses of that final heap. -/
theorem public_inv (e : Expr) (s : EvalState) (hs : AddressInvariant.Inv s) :
    AddressInvariant.Inv ((runResultM e).runState s).2 ∧
    ∀ r, ((runResultM e).runState s).1 = .ok r →
      AddressInvariant.RV ((runResultM e).runState s).2.needs r := by
  rw [PublicRunBridge.runResultM_is_production, PublicRunBridge.runResultWith_split, EvalM.bind_runState]
  generalize (identifyPropertyExpr e).run' 0 = e'
  have hst := (validate_frame e' s).1
  rcases hv : (validateExplicitParamOutputInvariantExpr e').runState s with ⟨o, t⟩
  rw [hv] at hst; simp only at hst; subst hst
  cases o with
  | error err => exact ⟨hs, fun r h => by cases h⟩
  | ok u =>
    simp only
    unfold PublicRunBridge.rootRun
    cases e' with
    | algorithmExpr a =>
      dsimp only
      split
      · exact export_after_sound _ (production_entry_program _) _ hs
      · exact ⟨hs, fun r h => by cases h⟩
    | _ => exact export_after_sound _ (production_entry_eval _) _ hs

/-- The public address invariant from the empty state. -/
theorem public_inv_from_empty (e : Expr) :
    AddressInvariant.Inv ((runResultM e).runState EvalState.empty).2 ∧
    ∀ r, ((runResultM e).runState EvalState.empty).1 = .ok r →
      AddressInvariant.RV ((runResultM e).runState EvalState.empty).2.needs r :=
  public_inv e EvalState.empty empty_inv

end KatLang.ValidationFrame
