import Lean
import KatLangArityLaws.EvaluatorCore

open KatLang KatLang.EvaluatorCore

/-!
# R7: whole-run property-cache discipline (Q-37)

A FIELD-FRAMED relation depends on a state only through its property cache and its active owner
set. Every evaluator body except the one that writes those fields
(`EvalBody.evalZeroArgPropertyAccessCounted`) preserves every such relation whenever its recursive
answer does (`evalStep_preserves_other`, one theorem per body, `EvalBody.*_pres`; syntax-directed
`pres_tac`, the field-generic counterpart of `EvaluatorDiscipline`'s procedure). For two relations
the property-access body is then proved by hand:

* `CacheKept` — published entries survive with their values: `cache_entries_survive_core` (every
  completed core run, every fuel, every state) and `cache_entries_survive` (every production run).
  Publication never replaces (`lookup_insert_keep`); an owner failure publishes nothing; nested
  publications of other keys are never undone.
* `ActiveKept` — the active owner set at exit is the one at entry, on COMPLETED runs (success and
  ordinary failure): `owner_set_restored_core`, `owner_set_restored`, `owner_set_empty_after`. An
  incomplete inner run may leave its owner mark, so this uses `invariant_transfer_completed`.

Q-37's local route laws (an inactive miss owns the evaluation; a reentrant miss evaluates but does
not publish; only the owner's success publishes; explicit `P()` is a fresh ordinary invocation —
which, since CACHE-PUB-1, is the body's `invoke` request: never a cache hit, and the owner of an
empty, inactive key) are the body itself, now a kernel term of the total core; their one-step
statements over that body are `KatLangArityLaws/PropertyInvocationLaws.lean`. Both whole-run
theorems below cover invocations unchanged in statement: the writer body is still the ONE
`evalZeroArgPropertyAccessCounted`, now with a `read` / `invoke` request. Not claimed: that a reentrant run can
never publish its own key (needs `LawfulBEq` of the cache key), property-cache key injectivity, or
any C# cache/accounting behaviour.
-/

namespace KatLang.EvaluatorCacheLaws

-- The relation-generic sections carry `[StateRel R] [FieldFrame R]` for every lemma; a lemma
-- that needs only one of them is still stated in the shared section.
set_option linter.unusedSectionVars false

/-- A reflexive, transitive relation between a computation's entry and exit states. -/
class StateRel (R : EvalState → EvalState → Prop) : Prop where
  refl : ∀ s, R s s
  trans : ∀ {s t u}, R s t → R t u → R s u

/-- `R` depends on a state only through its property cache and its active owner set: any write
    that keeps both is related. -/
class FieldFrame (R : EvalState → EvalState → Prop) : Prop where
  frame : ∀ s t, t.zeroArgPropertyCache = s.zeroArgPropertyCache →
    t.activeZeroArgProperties = s.activeZeroArgProperties → R s t

/-- `m` relates the one entry state `st` (read by a preceding `get`) to its exit state. -/
def PresAt {α : Type} (R : EvalState → EvalState → Prop) (st : EvalState) (m : EvalM α) : Prop :=
  R st (m.runState st).2

section Framework
variable {R : EvalState → EvalState → Prop} [StateRel R]

theorem pres_bind {α β : Type} {m : EvalM α} {f : α → EvalM β}
    (hm : Preserves R m) (hf : ∀ x, Preserves R (f x)) : Preserves R (m >>= f) := by
  intro s
  rw [EvalM.bind_runState]
  have k := hm s
  cases hr : m.runState s with
  | mk out t =>
    rw [hr] at k
    cases out with
    | error e => exact k
    | ok x => exact StateRel.trans k (hf x t)

theorem pres_pure {α : Type} (a : α) : Preserves R (pure a : EvalM α) := fun s => StateRel.refl s
theorem pres_get : Preserves R (get : EvalM EvalState) := fun s => StateRel.refl s
theorem pres_throw {α : Type} (e : Error) : Preserves R (throw e : EvalM α) := fun s => StateRel.refl s
theorem pres_evalError {α : Type} (e : Error) : Preserves R (EvalM.error e : EvalM α) :=
  fun s => StateRel.refl s
theorem pres_throwOf {α : Type} (e : Error) : Preserves R (MonadExceptOf.throw e : EvalM α) :=
  fun s => StateRel.refl s
theorem pres_raw_throw {α : Type} (e : Error) : Preserves R (⟨throw e⟩ : EvalM α) :=
  fun s => StateRel.refl s
theorem pres_raw_pure {α : Type} (a : α) : Preserves R (⟨pure a⟩ : EvalM α) :=
  fun s => StateRel.refl s
theorem pres_lift {α : Type} (o : Except Error α) : Preserves R (monadLift o : EvalM α) := by
  intro s; cases o <;> exact StateRel.refl s

theorem pres_map {α β : Type} (f : α → β) {m : EvalM α} (hm : Preserves R m) :
    Preserves R (f <$> m) :=
  pres_bind (f := Function.comp pure f) hm (fun x => pres_pure (f x))

theorem pres_attempt {α : Type} {m : EvalM α} (hm : Preserves R m) : Preserves R (evalAttempt m) := by
  intro s
  have k := hm s
  show R s ((match m.runState s with
    | (result, nextState) =>
      if result.isIncomplete then ((Except.error Error.fuelExhausted : Except Error (Except Error α)), nextState)
      else (Except.ok result, nextState)) : Except Error (Except Error α) × EvalState).2
  revert k
  rcases m.runState s with ⟨r, t⟩
  intro k
  dsimp only
  split <;> exact k

theorem pres_withCtx {α : Type} (c : String) {m : EvalM α} (hm : Preserves R m) :
    Preserves R (withCtx c m) := by
  unfold withCtx
  refine pres_bind (pres_attempt hm) (fun r => ?_)
  cases r with
  | ok x => exact pres_pure x
  | error e => exact pres_evalError _

/-- META-DIAG-1: a META capture is disciplined when its capture is (refusal naming writes nothing). -/
theorem pres_captureMeta (name : Ident) {m : EvalM Nat} (hm : Preserves R m) :
    Preserves R (NeedBinder.captureMeta name m) := by
  intro s
  have k := hm s
  show R s ((NeedBinder.captureMeta name m).runState s).2
  rw [NeedBinder.captureMeta_runState]
  revert k
  rcases m.runState s with ⟨r, t⟩
  intro k
  cases r <;> exact k

theorem pres_get_bind {β : Type} (f : EvalState → EvalM β) (h : ∀ st, PresAt R st (f st)) :
    Preserves R (get >>= f) := by
  intro s
  rw [EvalM.bind_runState]
  exact h s

theorem PresAt.of_pres {α : Type} {st : EvalState} {m : EvalM α} (h : Preserves R m) : PresAt R st m :=
  h st

theorem PresAt.bind {α β : Type} {st : EvalState} {m : EvalM α} {f : α → EvalM β}
    (hm : PresAt R st m) (hf : ∀ x, Preserves R (f x)) : PresAt R st (m >>= f) := by
  unfold PresAt at *
  rw [EvalM.bind_runState]
  cases hr : m.runState st with
  | mk out t =>
    rw [hr] at hm
    cases out with
    | error e => exact hm
    | ok x => exact StateRel.trans hm (hf x t)

theorem PresAt.set {st t : EvalState} (h : R st t) : PresAt R st (set t : EvalM PUnit) := h

/-- A `get` under a read-state goal reads that very state. -/
theorem PresAt.get_bind {β : Type} {st : EvalState} (f : EvalState → EvalM β) (h : PresAt R st (f st)) :
    PresAt R st (get >>= f) := by
  unfold PresAt at *
  rw [EvalM.bind_runState]
  exact h

theorem pres_modify (f : EvalState → EvalState) (h : ∀ s, R s (f s)) :
    Preserves R (modify f : EvalM Unit) := fun s => h s

theorem pres_mapM {α β : Type} (f : α → EvalM β) (h : ∀ x, Preserves R (f x)) (xs : List α) :
    Preserves R (xs.mapM f) := by
  suffices ∀ acc, Preserves R (List.mapM.loop f xs acc) by exact this []
  induction xs with
  | nil => intro acc; exact pres_pure _
  | cons x xs ih => intro acc; exact pres_bind (h x) (fun y => ih _)

theorem pres_forIn'_loop {α β : Type} (as : List α) (f : (a : α) → a ∈ as → β → EvalM (ForInStep β))
    (hf : ∀ a h b, Preserves R (f a h b)) :
    ∀ (as' : List α) (b : β) (h : ∃ bs, bs ++ as' = as), Preserves R (List.forIn'.loop as f as' b h)
  | [], b, h => by unfold List.forIn'.loop; exact pres_pure _
  | a :: as', b, h => by
    unfold List.forIn'.loop
    apply pres_bind (hf _ _ _)
    intro r
    cases r with
    | done b => exact pres_pure _
    | yield b => exact pres_forIn'_loop as f hf as' b _

theorem pres_forIn {α β : Type} (xs : List α) (init : β) (f : α → β → EvalM (ForInStep β))
    (h : ∀ a b, Preserves R (f a b)) : Preserves R (forIn xs init f) :=
  pres_forIn'_loop xs (fun a _ b => f a b) (fun a _ b => h a b) xs init ⟨[], rfl⟩

theorem pres_forM {α : Type} (xs : List α) (f : α → EvalM PUnit)
    (h : ∀ a, Preserves R (f a)) : Preserves R (xs.forM f) := by
  induction xs with
  | nil => exact pres_pure _
  | cons x xs ih => unfold List.forM; exact pres_bind (h x) (fun _ => ih)

theorem pres_foldlM {α β : Type} (f : β → α → EvalM β) (h : ∀ b a, Preserves R (f b a))
    (init : β) (xs : List α) : Preserves R (xs.foldlM f init) := by
  induction xs generalizing init with
  | nil => exact pres_pure _
  | cons x xs ih => unfold List.foldlM; exact pres_bind (h _ _) (fun b => ih b)

end Framework

open Lean Meta Elab Tactic in
/-- Is the goal a `Preserves`/`PresAt` statement; its computation (the last argument). -/
def presComputation? (ty : Lean.Expr) : Option Lean.Expr :=
  if ty.isAppOf ``KatLang.EvaluatorCore.Preserves || ty.isAppOf ``KatLang.EvaluatorCacheLaws.PresAt then
    some ty.appArg!
  else none

open Lean Meta Elab Tactic in
elab "pres_unfold_head" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let ty ← instantiateMVars (← goal.getType)
    let some m := presComputation? ty | throwError "pres_unfold_head: not a preservation goal"
    let m := m.headBeta
    let some c := m.getAppFn.constName? | throwError "pres_unfold_head: no head constant"
    if c ∈ [``Bind.bind, ``Pure.pure, ``Functor.map, ``KatLang.evalAttempt, ``ForIn.forIn,
        ``MonadState.get, ``MonadStateOf.get, ``MonadState.set, ``MonadStateOf.set,
        ``MonadState.modifyGet, ``modify, ``get, ``set, ``List.forM, ``List.mapM, ``List.foldlM,
        ``KatLang.withCtx, ``throw, ``MonadExcept.throw, ``MonadExceptOf.throw, ``throwThe,
        ``KatLang.EvalM.error] then
      throwError "pres_unfold_head: combinator"
    let g' ← Lean.Meta.unfoldTarget goal c
    let ty' ← instantiateMVars (← g'.getType)
    if (ty'.find? (fun e => e.isConstOf c)).isSome then
      throwError "pres_unfold_head: recursive definition"
    replaceMainGoal [g']

open Lean Meta Elab Tactic in
/-- Closes `Preserves R (rec c)` from a hypothesis `∀ c, Preserves R (rec c)`. -/
elab "pres_rec" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let ty ← instantiateMVars (← goal.getType)
    unless ty.isAppOf ``KatLang.EvaluatorCore.Preserves do throwError "pres_rec: not a Preserves goal"
    let m := ty.appArg!.headBeta
    unless m.isApp && m.appFn!.isFVar do throwError "pres_rec: not a recursive call"
    let f := m.appFn!
    for d in (← getLCtx) do
      unless d.isImplementationDetail do
        let t ← instantiateMVars d.type
        if t.isForall then
          let body := t.bindingBody!
          if body.isAppOf ``KatLang.EvaluatorCore.Preserves then
            let m' := body.appArg!
            if m'.isApp && m'.appFn! == f && m'.appArg! == .bvar 0 then
              goal.assign (mkApp d.toExpr m.appArg!)
              return
    throwError "pres_rec: no hypothesis"

open Lean Meta Elab Tactic in
elab "pres_hyp" : tactic => do
  let goal ← getMainGoal
  let ok ← goal.withContext do
    let gty ← instantiateMVars (← goal.getType)
    for d in (← getLCtx) do
      unless d.isImplementationDetail do
        let s ← saveState
        let (ms, _, hty) ← withReducible (forallMetaTelescopeReducing (← instantiateMVars d.type))
        if (← withReducible (isDefEq gty hty)) &&
            (← ms.allM (fun m => return !(← instantiateMVars m).hasMVar)) then
          goal.assign (mkAppN d.toExpr ms)
          return true
        restoreState s
    return false
  unless ok do throwError "pres_hyp: no hypothesis"

open Lean Meta Elab Tactic in
elab "pres_absurd" : tactic => do
  let goal ← getMainGoal
  let ok ← goal.withContext do
    let gty ← goal.getType
    for d in (← getLCtx) do
      unless d.isImplementationDetail do
        let s ← saveState
        let (ms, _, hty) ← withReducible (forallMetaTelescopeReducing (← instantiateMVars d.type))
        if hty.isConstOf ``False && ms.size ≥ 1 then
          let eqTy ← instantiateMVars (← inferType ms.back!)
          if let some (_, l, r) := eqTy.eq? then
            if ← withReducible (isDefEq l r) then
              let rflPf ← mkEqRefl l
              if ← isDefEq ms.back! rflPf then
                if ← ms.allM (fun m => return !(← instantiateMVars m).hasMVar) then
                  goal.assign (← mkFalseElim gty (mkAppN d.toExpr ms))
                  return true
        restoreState s
    return false
  unless ok do throwError "pres_absurd: no contradiction"

open Lean Meta Elab Tactic in
elab "pres_zeta" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let ty ← instantiateMVars (← goal.getType)
    let some m := presComputation? ty | throwError "pres_zeta: not a preservation goal"
    let mut e := m
    let mut n := 0
    for _ in [0:10000] do
      match e with
      | Lean.Expr.letE _ _ v b _ => e := b.instantiate1 v; n := n + 1
      | Lean.Expr.mdata _ e' => e := e'
      | _ => break
    if n == 0 then throwError "pres_zeta: no local definition"
    replaceMainGoal [← goal.replaceTargetDefEq (ty.updateApp! ty.appFn! e)]

open Lean Meta Elab Tactic in
elab "pres_whnf_core" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let ty ← instantiateMVars (← goal.getType)
    let some m := presComputation? ty | throwError "pres_whnf_core: not a preservation goal"
    let m' ← whnfCore m
    if m' == m then throwError "pres_whnf_core: no progress"
    replaceMainGoal [← goal.replaceTargetDefEq (ty.updateApp! ty.appFn! m')]

open Lean Meta Elab Tactic in
elab "pres_intro" : tactic => do
  let goal ← getMainGoal
  unless (← instantiateMVars (← goal.getType)).isForall do throwError "pres_intro: no binder"
  let (_, g) ← goal.intro1
  replaceMainGoal [g]

/-- The evaluator helpers `rec.f args` are `rec (.f args)`. -/
macro "pres_unfold_rec" : tactic => `(tactic| dsimp (config := { proj := false }) only [EvalRec.whileLoop, EvalRec.aliasStepIsRuntime, EvalRec.aliasValue, EvalRec.resolveAliasChase, EvalRec.resolveAliasTarget, EvalRec.resolveAliasValueTarget, EvalRec.lookupLexicalProperty, EvalRec.lookupLexicalValueProperty, EvalRec.lookupLexical, EvalRec.needPlanNormalizeCallee, EvalRec.resolveAlg, EvalRec.projectNeedCallable, EvalRec.projectNeedWrittenAt, EvalRec.linkCallable, EvalRec.projectParameterCallable, EvalRec.projectNeedWritten, EvalRec.projectNeedStructuralMember, EvalRec.resolveCalleeAlg, EvalRec.expectPreparedSequenceBuiltinAlgorithmSuffixArg, EvalRec.resolveDotReceiver?, EvalRec.resolveDotReceiver, EvalRec.algorithmIntrinsicRoute, EvalRec.demandNeedRecursive, EvalRec.evalSuppliedAt, EvalRec.linkValue, EvalRec.algorithmOfValue, EvalRec.capturedCallee, EvalRec.referenceReceiverValue, EvalRec.algorithmCalleeOf, EvalRec.evalSuppliedCallCounted, EvalRec.evalNeedUserSupply, EvalRec.evalNeedFamilySupply, EvalRec.invokeNeed, EvalRec.argumentNeed, EvalRec.runNeedStepSlots, EvalRec.runNeedWhileRound, EvalRec.evalAlgOutputCore, EvalRec.evalAlgOutput, EvalRec.evalProgramOutput, EvalRec.evalAlgOutputSlots, EvalRec.formOutputRow, EvalRec.whileVerdictSlots, EvalRec.evalSequenceCallbackCall, EvalRec.evalSequenceCallbackCallCounted, EvalRec.evalAlgOutputPreparedCore, EvalRec.evalOutputRowsPreparedCore, EvalRec.evalCapturePreparedCore, EvalRec.evalCaptureCountedCore, EvalRec.evalCaptureValue, EvalRec.evalAlgOutputCountedCore, EvalRec.evalAlgOutputCounted, EvalRec.evalZeroArgumentDemandOutputCounted, EvalRec.evalZeroArgumentDemandOutput, EvalRec.evalArgumentValueCounted, EvalRec.evalArgumentValue, EvalRec.evalZeroArgPropertyAccessCounted, EvalRec.evalZeroArgPropertyAccess, EvalRec.evalConditionalCallbackCallCounted, EvalRec.evalUserCallbackCallCounted, EvalRec.evalResolvedCallbackCallCounted, EvalRec.evalResolvedCallbackCall, EvalRec.evalSequenceReduceStepCounted, EvalRec.demandSequenceBuiltinCallItemValue, EvalRec.bindSequenceBuiltinArguments, EvalRec.evalReduceCounted, EvalRec.evalFilterCounted, EvalRec.evalMapCounted, EvalRec.applyBuiltinCountedSequence, EvalRec.applyBuiltinCounted, EvalRec.applyBuiltin, EvalRec.applyBuiltinCountedResolved, EvalRec.evalExplicitSequenceValueItems, EvalRec.evalExplicitSequenceValueRowSlots, EvalRec.evalExplicitSequenceValueExprSlots, EvalRec.evalUserCallCounted, EvalRec.evalConditionalCallCounted, EvalRec.evalResolvedCall, EvalRec.evalResolvedCallCounted, EvalRec.evalCallCountedExpr, EvalRec.callLexicalWithReceiverCounted, EvalRec.rejectDotStringIntrinsicArguments, EvalRec.evalDotStringReceiverValue, EvalRec.evalDotCallCounted, EvalRec.rejectInvokeIntrinsicArguments, EvalRec.invokeCallReferenceValue, EvalRec.argumentViewCells, EvalRec.evalArgumentViewBuiltin, EvalRec.evalSequenceSpreadOperandValue, EvalRec.evalSequenceSpreadCounted, EvalRec.evalSupplySpread, EvalRec.evalListLiteralCounted, EvalRec.evalSequenceConstructCounted, EvalRec.evalUnaryCounted, EvalRec.evalBinaryCounted, EvalRec.evalComparisonCounted, EvalRec.evalComparisonLinksCounted, EvalRec.evalCounted, EvalRec.evalUserCall, EvalRec.evalConditionalCall, EvalRec.evalCallExpr, EvalRec.evalDotCall, EvalRec.eval, EvalRec.planRoute,
  EvalRec.bindingChannels, NeedChannels.shell, NeedChannels.capabilities] at *)

/-- A relation-specific closer for a write the field frame does not cover (extended per relation
    by `macro_rules`; fails by default). -/
syntax "pres_rel_close" : tactic
macro_rules | `(tactic| pres_rel_close) => `(tactic| fail "no relation-specific closer")

/-- A field-framed write: a goal `R s t` whose `t` keeps the cache and the owner set. -/
macro "pres_frame" : tactic => `(tactic| (apply FieldFrame.frame <;> rfl))

set_option hygiene false in
/-- Syntax-directed preservation of a field-framed relation, base form (framework lemmas only). -/
macro "pres_tac_base" : tactic => `(tactic| ((try pres_unfold_rec) <;> repeat' (first
  | pres_rec
  | pres_hyp
  | pres_absurd
  | (with_reducible apply pres_get_bind)
  | (with_reducible apply PresAt.get_bind)
  | (with_reducible apply PresAt.bind)
  | ((with_reducible apply PresAt.set); first | pres_frame | pres_rel_close)
  | (with_reducible apply pres_withCtx)
  | (with_reducible apply pres_captureMeta)
  | (with_reducible apply pres_attempt)
  | (with_reducible apply pres_map)
  | (with_reducible apply pres_bind)
  | (with_reducible apply pres_pure)
  | (with_reducible apply pres_get)
  | (with_reducible apply pres_throw)
  | (with_reducible apply pres_throwOf)
  | (with_reducible apply pres_raw_throw)
  | (with_reducible apply pres_raw_pure)
  | (with_reducible apply pres_evalError)
  | (with_reducible apply pres_lift)
  | (with_reducible apply pres_mapM)
  | ((with_reducible apply pres_modify); intro s; first | pres_frame | pres_rel_close)
  | (with_reducible apply pres_forIn)
  | (with_reducible apply pres_forM)
  | (with_reducible apply pres_foldlM)
  | split
  | pres_intro
  | pres_zeta
  | pres_whnf_core
  | pres_unfold_head
  | (with_reducible apply PresAt.of_pres))))

section Helpers
variable {R : EvalState → EvalState → Prop} [StateRel R] [FieldFrame R]


theorem pres_allocate (sus : NeedSuspension) : Preserves R (allocateNeed sus) := by
  unfold allocateNeed; pres_tac_base
theorem pres_bindParameters (names : List Ident) (ctx : EvalCtx) :
    Preserves R (EvalCtx.bindParameters names ctx) := by
  unfold EvalCtx.bindParameters; pres_tac_base
theorem pres_recordActivation (names : List Ident) (ctx : EvalCtx) (env : ValEnv) :
    Preserves R (recordParameterActivation names ctx env) := by
  unfold recordParameterActivation; pres_tac_base
theorem pres_identifyRuntime (a : Algorithm) : Preserves R (identifyRuntimeAlgorithm a) := by
  unfold identifyRuntimeAlgorithm; pres_tac_base
theorem pres_valueViewCell (a : Algorithm) : Preserves R (valueViewCell? a) := by
  unfold valueViewCell?; pres_tac_base
end Helpers

set_option hygiene false in
/-- Syntax-directed preservation of a field-framed relation, with the state-writing helpers. -/
macro "pres_tac_mid" : tactic => `(tactic| ((try pres_unfold_rec) <;> repeat' (first
  | pres_rec
  | pres_hyp
  | pres_absurd
  | (with_reducible apply pres_get_bind)
  | (with_reducible apply PresAt.get_bind)
  | (with_reducible apply PresAt.bind)
  | ((with_reducible apply PresAt.set); first | pres_frame | pres_rel_close)
  | (with_reducible apply pres_withCtx)
  | (with_reducible apply pres_captureMeta)
  | (with_reducible apply pres_attempt)
  | (with_reducible apply pres_map)
  | (with_reducible apply pres_bind)
  | (with_reducible apply pres_pure)
  | (with_reducible apply pres_get)
  | (with_reducible apply pres_throw)
  | (with_reducible apply pres_throwOf)
  | (with_reducible apply pres_raw_throw)
  | (with_reducible apply pres_raw_pure)
  | (with_reducible apply pres_allocate)
  | (with_reducible apply pres_bindParameters)
  | (with_reducible apply pres_recordActivation)
  | (with_reducible apply pres_identifyRuntime)
  | (with_reducible apply pres_valueViewCell)
  | (with_reducible apply pres_evalError)
  | (with_reducible apply pres_lift)
  | (with_reducible apply pres_mapM)
  | ((with_reducible apply pres_modify); intro s; first | pres_frame | pres_rel_close)
  | (with_reducible apply pres_forIn)
  | (with_reducible apply pres_forM)
  | (with_reducible apply pres_foldlM)
  | split
  | pres_intro
  | pres_zeta
  | pres_whnf_core
  | pres_unfold_head
  | (with_reducible apply PresAt.of_pres))))


section Helpers2
variable {R : EvalState → EvalState → Prop} [StateRel R] [FieldFrame R]

theorem pres_openNavigateWith (structureOf : Algorithm → EvalM Algorithm)
    (h : ∀ a, Preserves R (structureOf a)) (ctx : EvalCtx) (notStatic : Error)
    (value : Algorithm) (receiverName : String) (steps : List Ident) :
    Preserves R (openNavigateWith structureOf ctx notStatic value receiverName steps) := by
  induction steps generalizing value receiverName with
  | nil => unfold openNavigateWith; pres_tac_mid
  | cons member rest ih => unfold openNavigateWith; pres_tac_mid

theorem pres_openStructure (fuel : Nat) (ctx : EvalCtx) (a : Algorithm) :
    Preserves R (openStructure fuel ctx a) := by
  induction fuel generalizing a with
  | zero => simp only [openStructure]; pres_tac_mid
  | succ n ih =>
    have := pres_openNavigateWith (R := R) (fun value => openStructure n ctx value) ih
    simp only [openStructure]; pres_tac_mid

theorem pres_form (spread : NeedSupply.SpreadEval) (h : ∀ e c v, Preserves R (spread e c v))
    (ctx : EvalCtx) (env : ValEnv) (args : OutputBundle) :
    Preserves R (NeedSupply.form spread ctx env args) := by
  induction args with
  | nil => unfold NeedSupply.form; pres_tac_mid
  | cons e rest ih => unfold NeedSupply.form; pres_tac_mid

/-! ## The recursive total helpers -/

theorem pres_formLeftToRight (form : Expr → EvalM (List Result)) (h : ∀ e, Preserves R (form e))
    (rows : List Expr) : Preserves R (OutputRows.formLeftToRight form rows) := by
  induction rows with
  | nil => unfold OutputRows.formLeftToRight; pres_tac_mid
  | cons e rest ih => unfold OutputRows.formLeftToRight; pres_tac_mid

theorem pres_discover (form : Expr → EvalM (List Result)) (h : ∀ e, Preserves R (form e))
    (rows : List Expr) : Preserves R (WhileRound.discover form rows) := by
  induction rows with
  | nil => unfold WhileRound.discover; pres_tac_mid
  | cons e rest ih => unfold WhileRound.discover; pres_tac_mid

theorem pres_selectWith {α : Type} (demand : α → EvalM Result) (h : ∀ a, Preserves R (demand a))
    (receiver : Result) (cells : List α) : Preserves R (selectWith demand receiver cells) := by
  induction cells with
  | nil => unfold selectWith; pres_tac_mid
  | cons c rest ih => unfold selectWith; pres_tac_mid

theorem pres_selectViewWith {α : Type} (demand : α → EvalM Result) (hd : ∀ a, Preserves R (demand a))
    (cellsOf : EvalM (List NeedSupply.Sourced)) (hc : Preserves R cellsOf)
    (demandCell : Nat → EvalM Result) (hdc : ∀ a, Preserves R (demandCell a)) (selectors : List α) :
    Preserves R (selectViewWith demand cellsOf demandCell selectors) := by
  induction selectors with
  | nil => unfold selectViewWith; pres_tac_mid
  | cons c rest ih => unfold selectViewWith; pres_tac_mid

theorem pres_interpolateWith (value : Expr → EvalM Result) (h : ∀ e, Preserves R (value e))
    (acc : String) (links : List InterpolationLink) :
    Preserves R (interpolateWith value acc links) := by
  induction links generalizing acc with
  | nil => unfold interpolateWith; pres_tac_mid
  | cons l rest ih => unfold interpolateWith; pres_tac_mid

/-- Capabilities whose every field is disciplined. -/
structure CapsPres (R : EvalState → EvalState → Prop) (caps : NeedCapabilities EvalM) : Prop where
  value : ∀ a, Preserves R (caps.value a)
  callable : ∀ a, Preserves R (caps.callable a)
  allocate : ∀ s, Preserves R (caps.allocate s)
  reference : ∀ a, Preserves R (caps.reference a)

/-- NEED-04's data-anchor check demands only through the VALUE capability. -/
theorem pres_checkAnchor (caps : NeedCapabilities EvalM) (hc : CapsPres R caps) (name : Ident)
    (anchor : CountedResult) (family : Bool) (cells : List Nat) :
    Preserves R (NeedBinder.checkAnchor caps name anchor family cells) := by
  have hv := hc.value
  induction cells with
  | nil => unfold NeedBinder.checkAnchor; pres_tac_mid
  | cons c rest ih => unfold NeedBinder.checkAnchor; pres_tac_mid

theorem pres_binder (caps : NeedCapabilities EvalM) (hc : CapsPres R caps) (repeated : List Ident)
    (family : Bool) :
    (∀ pattern address bound,
      Preserves R (NeedBinder.bindOne caps pattern address repeated bound family)) ∧
    (∀ patterns sources current,
      Preserves R (NeedBinder.bindSources caps patterns sources repeated current family)) := by
  have hv := hc.value; have hcl := hc.callable; have hal := hc.allocate; have hre := hc.reference
  have hck := pres_checkAnchor caps hc
  refine NeedBinder.bindOne.mutual_induct
    (motive_1 := fun pattern address bound =>
      Preserves R (NeedBinder.bindOne caps pattern address repeated bound family))
    (motive_2 := fun patterns sources current =>
      Preserves R (NeedBinder.bindSources caps patterns sources repeated current family))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals intros
  all_goals first
    | (simp only [NeedBinder.bindOne]; pres_tac_mid)
    | (simp only [NeedBinder.bindSources]; pres_tac_mid)

theorem pres_bindPatterns (caps : NeedCapabilities EvalM) (hc : CapsPres R caps)
    (patterns : List NeedPattern) (cells : List Nat) (family : Bool) :
    Preserves R (NeedBinder.bindPatterns caps patterns cells family) := by
  unfold NeedBinder.bindPatterns NeedBinder.bindLevel NeedBinder.cardinalityGate
  have := (pres_binder caps hc (needRepeatedNames patterns) family).2
  pres_tac_mid

theorem pres_chooseBranch {β : Type} (caps : NeedCapabilities EvalM) (hc : CapsPres R caps)
    (cells : List Nat) (calleeName : String) (activate : CondBranch → NeedEnv → EvalM β)
    (ha : ∀ b e, Preserves R (activate b e)) (branches : List CondBranch) :
    Preserves R (NeedBinder.chooseBranch caps cells calleeName activate branches) := by
  induction branches with
  | nil => unfold NeedBinder.chooseBranch; pres_tac_mid
  | cons b rest ih =>
    unfold NeedBinder.chooseBranch
    have := fun ps fam => pres_bindPatterns caps hc ps cells fam
    pres_tac_mid

theorem pres_selectFamily {β : Type} (caps : NeedCapabilities EvalM) (hc : CapsPres R caps)
    (callee : Algorithm) (cells : List Nat) (calleeName : String)
    (activate : CondBranch → NeedEnv → EvalM β) (ha : ∀ b e, Preserves R (activate b e)) :
    Preserves R (NeedBinder.selectFamily caps callee cells calleeName activate) := by
  unfold NeedBinder.selectFamily
  have := pres_chooseBranch caps hc cells calleeName activate ha
  pres_tac_mid


theorem pres_collectSingleAtomicNumbers (b : Builtin) (index : Nat) (items : List Result) :
    Preserves R (collectSingleAtomicNumbers b index items) := by
  induction items generalizing index with
  | nil => unfold collectSingleAtomicNumbers; pres_tac_mid
  | cons i rest ih => unfold collectSingleAtomicNumbers; pres_tac_mid

theorem pres_minLoop (numbers : List Int) (current : Int) :
    Preserves R (evalMinCounted.minLoop numbers current) := by
  induction numbers generalizing current with
  | nil => unfold evalMinCounted.minLoop; pres_tac_mid
  | cons n rest ih => unfold evalMinCounted.minLoop; pres_tac_mid

theorem pres_maxLoop (numbers : List Int) (current : Int) :
    Preserves R (evalMaxCounted.maxLoop numbers current) := by
  induction numbers generalizing current with
  | nil => unfold evalMaxCounted.maxLoop; pres_tac_mid
  | cons n rest ih => unfold evalMaxCounted.maxLoop; pres_tac_mid

theorem pres_resolveAlgForOpen (ctx : EvalCtx) (e : Expr) : Preserves R (resolveAlgForOpen e ctx) := by
  have := pres_openStructure (R := R)
  induction e using resolveAlgForOpen.induct ctx with
  | case7 o n a ih => unfold resolveAlgForOpen; pres_tac_mid
  | _ => unfold resolveAlgForOpen; pres_tac_mid

theorem pres_lookupOpenProperties (a : Algorithm) (name : Ident) (ctx : EvalCtx) :
    Preserves R (lookupOpenProperties a name ctx) := by
  have := pres_resolveAlgForOpen (R := R)
  have := pres_openStructure (R := R)
  unfold lookupOpenProperties; pres_tac_mid

theorem pres_lookupOpenPropertiesInParentChain (name : Ident) (ctx : EvalCtx) (sc : ScopeCtx) :
    Preserves R (lookupOpenPropertiesInParentChain sc name ctx) := by
  induction sc using lookupOpenPropertiesInParentChain.induct with
  | _ t ih =>
    have := pres_lookupOpenProperties (R := R)
    unfold lookupOpenPropertiesInParentChain
    cases t with
    | mk parent _ _ _ _ _ _ _ => cases parent <;> pres_tac_mid

theorem pres_aliasStepNavigateWith (structureOf : Algorithm → EvalCtx → EvalM (Option Algorithm))
    (h : ∀ a c, Preserves R (structureOf a c)) (stepCtx : EvalCtx) (notStatic : Error)
    (value : Algorithm) (last : Option ResolvedProperty) (receiverName : String) (steps : List Ident) :
    Preserves R (aliasStepNavigateWith structureOf stepCtx notStatic value last receiverName steps) := by
  induction steps generalizing value last receiverName with
  | nil => unfold aliasStepNavigateWith; pres_tac_mid
  | cons member rest ih => unfold aliasStepNavigateWith; pres_tac_mid

theorem pres_resolveAliasStepWith (structureOf : Algorithm → EvalCtx → EvalM (Option Algorithm))
    (h : ∀ a c, Preserves R (structureOf a c)) (step : Algorithm) (target : Expr) (ctx : EvalCtx) :
    Preserves R (resolveAliasStepWith structureOf step target ctx) := by
  have := pres_aliasStepNavigateWith (R := R) structureOf h
  have := pres_lookupOpenProperties (R := R)
  have := pres_lookupOpenPropertiesInParentChain (R := R)
  unfold resolveAliasStepWith; pres_tac_mid

theorem pres_aliasRouteIsIntrinsicWith (structureOf : Algorithm → EvalCtx → EvalM (Option Algorithm))
    (h : ∀ a c, Preserves R (structureOf a c)) (receiver : Expr) (ctx : EvalCtx) :
    Preserves R (aliasRouteIsIntrinsicWith structureOf receiver ctx) := by
  have := pres_aliasStepNavigateWith (R := R) structureOf h
  have := pres_lookupOpenProperties (R := R)
  have := pres_lookupOpenPropertiesInParentChain (R := R)
  unfold aliasRouteIsIntrinsicWith; pres_tac_mid

section LocalLoops
variable (rec : EvalRec) (hrec : ∀ c, Preserves R (rec c))
include hrec

theorem pres_outputRowsCollect (rowCtx : EvalCtx) (env : ValEnv) (rows : List Expr)
    (acc : List Result) (emitted : Nat) :
    Preserves R (EvalBody.evalOutputRowsPreparedCore.collect rec rowCtx env rows acc emitted) := by
  induction rows generalizing acc emitted with
  | nil => unfold EvalBody.evalOutputRowsPreparedCore.collect; pres_tac_mid
  | cons e rest ih => unfold EvalBody.evalOutputRowsPreparedCore.collect; pres_tac_mid

theorem pres_explicitRowsCollect (rowCtx : EvalCtx) (env : ValEnv) (rows : List Expr) (acc : List Result) :
    Preserves R (EvalBody.evalExplicitSequenceValueRowSlots.collect rec rowCtx env rows acc) := by
  induction rows generalizing acc with
  | nil => unfold EvalBody.evalExplicitSequenceValueRowSlots.collect; pres_tac_mid
  | cons e rest ih => unfold EvalBody.evalExplicitSequenceValueRowSlots.collect; pres_tac_mid

theorem pres_listLiteralCollect (ctx : EvalCtx) (env : ValEnv) (elements : List Expr) (acc : List Result) :
    Preserves R (EvalBody.evalListLiteralCounted.collect rec ctx env elements acc) := by
  induction elements generalizing acc with
  | nil => unfold EvalBody.evalListLiteralCounted.collect; pres_tac_mid
  | cons e rest ih => unfold EvalBody.evalListLiteralCounted.collect; pres_tac_mid

theorem pres_sequenceConstructLoop (ctx : EvalCtx) (env : ValEnv) (leaves : List Expr) (items : List Result) :
    Preserves R (EvalBody.evalSequenceConstructCounted.loop rec ctx env leaves items) := by
  induction leaves generalizing items with
  | nil => unfold EvalBody.evalSequenceConstructCounted.loop; pres_tac_mid
  | cons e rest ih => unfold EvalBody.evalSequenceConstructCounted.loop; pres_tac_mid

theorem pres_prepareControls (b : Builtin) (ctx : EvalCtx) (env : ValEnv)
    (descriptors : List SequenceBuiltinSuffixArgDescriptor) (items : List CallableCallItem) :
    Preserves R (EvalBody.bindSequenceBuiltinArguments.prepareControls rec b ctx env descriptors items) := by
  induction descriptors generalizing items with
  | nil => cases items <;> (unfold EvalBody.bindSequenceBuiltinArguments.prepareControls; pres_tac_mid)
  | cons d rest ih => cases items <;> (unfold EvalBody.bindSequenceBuiltinArguments.prepareControls; pres_tac_mid)

theorem pres_reduceLoop (stepAlg : Algorithm) (ctx : EvalCtx) (env : ValEnv)
    (items : List CountedResult) (acc : CountedResult) :
    Preserves R (EvalBody.evalReduceCounted.reduceLoop rec stepAlg ctx env items acc) := by
  induction items generalizing acc with
  | nil => unfold EvalBody.evalReduceCounted.reduceLoop; pres_tac_mid
  | cons i rest ih => unfold EvalBody.evalReduceCounted.reduceLoop; pres_tac_mid

theorem pres_filterLoop (predicateAlg : Algorithm) (ctx : EvalCtx) (env : ValEnv)
    (index : Nat) (items : List CountedResult) :
    Preserves R (EvalBody.evalFilterCounted.filterLoop rec predicateAlg ctx env index items) := by
  induction items generalizing index with
  | nil => unfold EvalBody.evalFilterCounted.filterLoop; pres_tac_mid
  | cons i rest ih => unfold EvalBody.evalFilterCounted.filterLoop; pres_tac_mid

theorem pres_mapLoop (transformAlg : Algorithm) (ctx : EvalCtx) (env : ValEnv) (items : List CountedResult) :
    Preserves R (EvalBody.evalMapCounted.mapLoop rec transformAlg ctx env items) := by
  induction items with
  | nil => unfold EvalBody.evalMapCounted.mapLoop; pres_tac_mid
  | cons i rest ih => unfold EvalBody.evalMapCounted.mapLoop; pres_tac_mid

theorem pres_repeatLoop (ctx : EvalCtx) (env : ValEnv) (step : ResolvedArgumentAlgorithm)
    (stepName : String) (remaining : Nat) (cells : List Nat) :
    Preserves R (EvalBody.applyBuiltinCounted.repeatLoop rec ctx env step stepName remaining cells) := by
  induction remaining generalizing cells with
  | zero => unfold EvalBody.applyBuiltinCounted.repeatLoop; pres_tac_mid
  | succ k ih => unfold EvalBody.applyBuiltinCounted.repeatLoop; pres_tac_mid

end LocalLoops

end Helpers2

set_option hygiene false in
/-- Syntax-directed preservation of a field-framed relation by an evaluator body, given that its
    recursive answer `hrec` preserves it. -/
macro "pres_tac" : tactic => `(tactic| ((try pres_unfold_rec) <;> repeat' (first
  | pres_rec
  | pres_hyp
  | pres_absurd
  | (with_reducible apply pres_get_bind)
  | (with_reducible apply PresAt.get_bind)
  | (with_reducible apply PresAt.bind)
  | ((with_reducible apply PresAt.set); first | pres_frame | pres_rel_close)
  | (with_reducible apply pres_withCtx)
  | (with_reducible apply pres_captureMeta)
  | (with_reducible apply pres_attempt)
  | (with_reducible apply pres_map)
  | (with_reducible apply pres_bind)
  | (with_reducible apply pres_pure)
  | (with_reducible apply pres_get)
  | (with_reducible apply pres_throw)
  | (with_reducible apply pres_throwOf)
  | (with_reducible apply pres_raw_throw)
  | (with_reducible apply pres_raw_pure)
  | (with_reducible apply pres_allocate)
  | (with_reducible apply pres_bindParameters)
  | (with_reducible apply pres_recordActivation)
  | (with_reducible apply pres_identifyRuntime)
  | (with_reducible apply pres_valueViewCell)
  | (with_reducible apply pres_evalError)
  | (with_reducible apply pres_lift)
  | (with_reducible apply pres_mapM)
  | ((with_reducible apply pres_modify); intro s; first | pres_frame | pres_rel_close)
  | (with_reducible apply pres_forIn)
  | (with_reducible apply pres_forM)
  | (with_reducible apply pres_foldlM)
  | (with_reducible apply pres_form)
  | (with_reducible apply pres_formLeftToRight)
  | (with_reducible apply pres_discover)
  | (with_reducible apply pres_selectWith)
  | (with_reducible apply pres_selectViewWith)
  | (with_reducible apply pres_interpolateWith)
  | (with_reducible apply pres_bindPatterns)
  | (with_reducible apply pres_selectFamily)
  | (with_reducible apply pres_collectSingleAtomicNumbers)
  | (with_reducible apply pres_minLoop)
  | (with_reducible apply pres_maxLoop)
  | (with_reducible apply pres_resolveAlgForOpen)
  | (with_reducible apply pres_openStructure)
  | (with_reducible apply pres_resolveAliasStepWith)
  | (with_reducible apply pres_aliasRouteIsIntrinsicWith)
  | (with_reducible apply pres_lookupOpenProperties)
  | (with_reducible apply pres_lookupOpenPropertiesInParentChain)
  | (with_reducible apply EvalBody.terminalAccess_pres rec hrec)
  | (with_reducible apply pres_outputRowsCollect rec hrec)
  | (with_reducible apply pres_explicitRowsCollect rec hrec)
  | (with_reducible apply pres_listLiteralCollect rec hrec)
  | (with_reducible apply pres_sequenceConstructLoop rec hrec)
  | (with_reducible apply pres_prepareControls rec hrec)
  | (with_reducible apply pres_reduceLoop rec hrec)
  | (with_reducible apply pres_filterLoop rec hrec)
  | (with_reducible apply pres_mapLoop rec hrec)
  | (with_reducible apply pres_repeatLoop rec hrec)
  | (with_reducible apply CapsPres.mk)
  | split
  | pres_intro
  | pres_zeta
  | pres_whnf_core
  | pres_unfold_head
  | (with_reducible apply PresAt.of_pres))))


section Bodies
variable {R : EvalState → EvalState → Prop} [StateRel R] [FieldFrame R]

theorem EvalBody.whileLoop_pres (rec : EvalRec) (hrec : ∀ c, Preserves R (rec c)) (step : ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) (stepName : String) (cells : List Nat) :
    Preserves R (EvalBody.whileLoop rec step ctx env stepName cells) := by
  unfold EvalBody.whileLoop; pres_tac

theorem EvalBody.aliasStepIsRuntime_pres (rec : EvalRec) (hrec : ∀ c, Preserves R (rec c)) (step : Algorithm) (target : Expr) (ctx : EvalCtx) (visited : List String) :
    Preserves R (EvalBody.aliasStepIsRuntime rec step target ctx visited) := by
  unfold EvalBody.aliasStepIsRuntime; pres_tac

theorem EvalBody.aliasValue_pres (rec : EvalRec) (hrec : ∀ c, Preserves R (rec c)) (wired : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    Preserves R (EvalBody.aliasValue rec wired ctx env) := by
  unfold EvalBody.aliasValue; pres_tac

theorem EvalBody.resolveAliasChase_pres (rec : EvalRec) (hrec : ∀ c, Preserves R (rec c)) (followCarriers projectRuntime : Bool) (a : Algorithm) (ctx : EvalCtx) (visited : List String) (last : Option (Algorithm × PropDef)) :
    Preserves R (EvalBody.resolveAliasChase rec followCarriers projectRuntime a ctx visited last) := by
  unfold EvalBody.resolveAliasChase; pres_tac

theorem EvalBody.resolveAliasTarget_pres (rec : EvalRec) (hrec : ∀ c, Preserves R (rec c)) (a : Algorithm) (ctx : EvalCtx) :
    Preserves R (EvalBody.resolveAliasTarget rec a ctx) := by
  unfold EvalBody.resolveAliasTarget; pres_tac

theorem EvalBody.resolveAliasStructure_pres (rec : EvalRec) (hrec : ∀ c, Preserves R (rec c)) (a : Algorithm) (ctx : EvalCtx) :
    Preserves R (EvalBody.resolveAliasStructure rec a ctx) := by
  unfold EvalBody.resolveAliasStructure; pres_tac

theorem EvalBody.aliasOriginBinding?_pres (rec : EvalRec) (hrec : ∀ c, Preserves R (rec c)) (a : Algorithm) (ctx : EvalCtx) :
    Preserves R (EvalBody.aliasOriginBinding? rec a ctx) := by
  unfold EvalBody.aliasOriginBinding?; pres_tac

theorem EvalBody.resolveAliasValueTarget_pres (rec : EvalRec) (hrec : ∀ c, Preserves R (rec c)) (a : Algorithm) (ctx : EvalCtx) :
    Preserves R (EvalBody.resolveAliasValueTarget rec a ctx) := by
  unfold EvalBody.resolveAliasValueTarget; pres_tac

theorem EvalBody.lookupLexicalProperty_pres (rec : EvalRec) (hrec : ∀ c, Preserves R (rec c)) (a : Algorithm) (name : Ident) (ctx : EvalCtx) :
    Preserves R (EvalBody.lookupLexicalProperty rec a name ctx) := by
  unfold EvalBody.lookupLexicalProperty; pres_tac

theorem EvalBody.lookupLexicalValueProperty_pres (rec : EvalRec) (hrec : ∀ c, Preserves R (rec c)) (a : Algorithm) (name : Ident) (ctx : EvalCtx) :
    Preserves R (EvalBody.lookupLexicalValueProperty rec a name ctx) := by
  unfold EvalBody.lookupLexicalValueProperty; pres_tac

theorem EvalBody.lookupLexical_pres (rec : EvalRec) (hrec : ∀ c, Preserves R (rec c)) (a : Algorithm) (name : Ident) (ctx : EvalCtx) :
    Preserves R (EvalBody.lookupLexical rec a name ctx) := by
  unfold EvalBody.lookupLexical; pres_tac

theorem EvalBody.needPlanNormalizeCallee_pres (rec : EvalRec) (hrec : ∀ c, Preserves R (rec c)) (callee : Algorithm) (ctx : EvalCtx) :
    Preserves R (EvalBody.needPlanNormalizeCallee rec callee ctx) := by
  unfold EvalBody.needPlanNormalizeCallee; pres_tac

theorem EvalBody.resolveAlg_pres (rec : EvalRec) (hrec : ∀ c, Preserves R (rec c)) (e : Expr) (ctx : EvalCtx) :
    Preserves R (EvalBody.resolveAlg rec e ctx) := by
  unfold EvalBody.resolveAlg; pres_tac

theorem EvalBody.projectNeedCallable_pres (rec : EvalRec) (hrec : ∀ c, Preserves R (rec c)) (address : Nat) :
    Preserves R (EvalBody.projectNeedCallable rec address) := by
  unfold EvalBody.projectNeedCallable; pres_tac

theorem EvalBody.projectNeedWrittenAt_pres (rec : EvalRec) (hrec : ∀ c, Preserves R (rec c)) (address : Nat) (source : Expr) (caller : EvalCtx) :
    Preserves R (EvalBody.projectNeedWrittenAt rec address source caller) := by
  unfold EvalBody.projectNeedWrittenAt; pres_tac

theorem EvalBody.linkCallable_pres (rec : EvalRec) (hrec : ∀ c, Preserves R (rec c)) (address : Nat) :
    Preserves R (EvalBody.linkCallable rec address) := by
  unfold EvalBody.linkCallable; pres_tac

theorem EvalBody.projectParameterCallable_pres (rec : EvalRec) (hrec : ∀ c, Preserves R (rec c)) (x : Ident) (ctx : EvalCtx) :
    Preserves R (EvalBody.projectParameterCallable rec x ctx) := by
  unfold EvalBody.projectParameterCallable; pres_tac

theorem EvalBody.projectNeedWritten_pres (rec : EvalRec) (hrec : ∀ c, Preserves R (rec c)) (source : Expr) (caller : EvalCtx) :
    Preserves R (EvalBody.projectNeedWritten rec source caller) := by
  unfold EvalBody.projectNeedWritten; pres_tac

theorem EvalBody.projectNeedStructuralMember_pres (rec : EvalRec) (hrec : ∀ c, Preserves R (rec c)) (source : Expr) (ctx : EvalCtx) :
    Preserves R (EvalBody.projectNeedStructuralMember rec source ctx) := by
  unfold EvalBody.projectNeedStructuralMember; pres_tac

theorem EvalBody.resolveCalleeAlg_pres (rec : EvalRec) (hrec : ∀ c, Preserves R (rec c)) (f : Expr) (ctx : EvalCtx) :
    Preserves R (EvalBody.resolveCalleeAlg rec f ctx) := by
  unfold EvalBody.resolveCalleeAlg; pres_tac

theorem EvalBody.expectPreparedSequenceBuiltinAlgorithmSuffixArg_pres (rec : EvalRec) (hrec : ∀ c, Preserves R (rec c)) (b : Builtin) (descriptors : List SequenceBuiltinSuffixArgDescriptor) (args : List PreparedSequenceBuiltinSuffixArg) (index : Nat) :
    Preserves R (EvalBody.expectPreparedSequenceBuiltinAlgorithmSuffixArg rec b descriptors args index) := by
  unfold EvalBody.expectPreparedSequenceBuiltinAlgorithmSuffixArg; pres_tac

theorem EvalBody.resolveDotReceiver?_pres (rec : EvalRec) (hrec : ∀ c, Preserves R (rec c)) (e : Expr) (ctx : EvalCtx) :
    Preserves R (EvalBody.resolveDotReceiver? rec e ctx) := by
  unfold EvalBody.resolveDotReceiver?; pres_tac

theorem EvalBody.resolveDotReceiver_pres (rec : EvalRec) (hrec : ∀ c, Preserves R (rec c)) (e : Expr) (ctx : EvalCtx) :
    Preserves R (EvalBody.resolveDotReceiver rec e ctx) := by
  unfold EvalBody.resolveDotReceiver; pres_tac

theorem EvalBody.algorithmIntrinsicRoute_pres (rec : EvalRec) (hrec : ∀ c, Preserves R (rec c)) (receiver : Expr) (ctx : EvalCtx) :
    Preserves R (EvalBody.algorithmIntrinsicRoute rec receiver ctx) := by
  unfold EvalBody.algorithmIntrinsicRoute; pres_tac

theorem EvalBody.demandNeedRecursive_pres (rec : EvalRec) (hrec : ∀ c, Preserves R (rec c)) (address : Nat) :
    Preserves R (EvalBody.demandNeedRecursive rec address) := by
  unfold EvalBody.demandNeedRecursive; pres_tac

theorem EvalBody.evalSuppliedAt_pres (rec : EvalRec) (hrec : ∀ c, Preserves R (rec c)) (address : Nat) (e : Expr) (ctx : EvalCtx) (env : ValEnv) :
    Preserves R (EvalBody.evalSuppliedAt rec address e ctx env) := by
  unfold EvalBody.evalSuppliedAt; pres_tac

theorem EvalBody.linkValue_pres (rec : EvalRec) (hrec : ∀ c, Preserves R (rec c)) (address : Nat) :
    Preserves R (EvalBody.linkValue rec address) := by
  unfold EvalBody.linkValue; pres_tac

theorem EvalBody.algorithmOfValue_pres (rec : EvalRec) (hrec : ∀ c, Preserves R (rec c)) (val : Result) (argsOpt : Option OutputBundle) (ctx : EvalCtx) (env : ValEnv) :
    Preserves R (EvalBody.algorithmOfValue rec val argsOpt ctx env) := by
  unfold EvalBody.algorithmOfValue; pres_tac

theorem EvalBody.capturedCallee_pres (rec : EvalRec) (hrec : ∀ c, Preserves R (rec c)) (callee : Nat) :
    Preserves R (EvalBody.capturedCallee rec callee) := by
  unfold EvalBody.capturedCallee; pres_tac

theorem EvalBody.referenceReceiverValue_pres (rec : EvalRec) (hrec : ∀ c, Preserves R (rec c)) (target : Expr) (targetAlg : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    Preserves R (EvalBody.referenceReceiverValue rec target targetAlg ctx env) := by
  unfold EvalBody.referenceReceiverValue; pres_tac

theorem EvalBody.algorithmCalleeOf_pres (rec : EvalRec) (hrec : ∀ c, Preserves R (rec c)) (receiver : Expr) (ctx : EvalCtx) (env : ValEnv) :
    Preserves R (EvalBody.algorithmCalleeOf rec receiver ctx env) := by
  unfold EvalBody.algorithmCalleeOf; pres_tac

theorem EvalBody.evalSuppliedCallCounted_pres (rec : EvalRec) (hrec : ∀ c, Preserves R (rec c)) (origin : CalleeOrigin) (callee : Algorithm) (cells : List NeedSupply.Sourced) (ctx : EvalCtx) (env : ValEnv) (calleeName : String) :
    Preserves R (EvalBody.evalSuppliedCallCounted rec origin callee cells ctx env calleeName) := by
  unfold EvalBody.evalSuppliedCallCounted; pres_tac

theorem EvalBody.evalNeedUserSupply_pres (rec : EvalRec) (hrec : ∀ c, Preserves R (rec c)) (callee : Algorithm) (cells : List Nat) (ctx : EvalCtx) (env : ValEnv) :
    Preserves R (EvalBody.evalNeedUserSupply rec callee cells ctx env) := by
  unfold EvalBody.evalNeedUserSupply; pres_tac

theorem EvalBody.evalNeedFamilySupply_pres (rec : EvalRec) (hrec : ∀ c, Preserves R (rec c)) (callee : Algorithm) (cells : List Nat) (ctx : EvalCtx) (env : ValEnv) (calleeName : String) :
    Preserves R (EvalBody.evalNeedFamilySupply rec callee cells ctx env calleeName) := by
  unfold EvalBody.evalNeedFamilySupply; pres_tac

theorem EvalBody.invokeNeed_pres (rec : EvalRec) (hrec : ∀ c, Preserves R (rec c)) (arg : ResolvedArgumentAlgorithm) :
    Preserves R (EvalBody.invokeNeed rec arg) := by
  unfold EvalBody.invokeNeed; pres_tac

theorem EvalBody.argumentNeed_pres (rec : EvalRec) (hrec : ∀ c, Preserves R (rec c)) (arg : ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) :
    Preserves R (EvalBody.argumentNeed rec arg ctx env) := by
  unfold EvalBody.argumentNeed; pres_tac

theorem EvalBody.runNeedStepSlots_pres (rec : EvalRec) (hrec : ∀ c, Preserves R (rec c)) (step : Algorithm) (ctx : EvalCtx) (env : ValEnv) (cells : List Nat) (stepName : String) :
    Preserves R (EvalBody.runNeedStepSlots rec step ctx env cells stepName) := by
  unfold EvalBody.runNeedStepSlots EvalBody.runNeedStepWith; pres_tac

theorem EvalBody.runNeedWhileRound_pres (rec : EvalRec) (hrec : ∀ c, Preserves R (rec c)) (step : Algorithm) (ctx : EvalCtx) (env : ValEnv) (cells : List Nat) (stepName : String) :
    Preserves R (EvalBody.runNeedWhileRound rec step ctx env cells stepName) := by
  unfold EvalBody.runNeedWhileRound EvalBody.runNeedStepWith; pres_tac

theorem EvalBody.evalAlgOutputCore_pres (rec : EvalRec) (hrec : ∀ c, Preserves R (rec c)) (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    Preserves R (EvalBody.evalAlgOutputCore rec a ctx env) := by
  unfold EvalBody.evalAlgOutputCore; pres_tac

theorem EvalBody.evalAlgOutput_pres (rec : EvalRec) (hrec : ∀ c, Preserves R (rec c)) (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    Preserves R (EvalBody.evalAlgOutput rec a ctx env) := by
  unfold EvalBody.evalAlgOutput; pres_tac

theorem EvalBody.evalProgramOutput_pres (rec : EvalRec) (hrec : ∀ c, Preserves R (rec c)) (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    Preserves R (EvalBody.evalProgramOutput rec a ctx env) := by
  unfold EvalBody.evalProgramOutput; pres_tac

theorem EvalBody.evalAlgOutputSlots_pres (rec : EvalRec) (hrec : ∀ c, Preserves R (rec c)) (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    Preserves R (EvalBody.evalAlgOutputSlots rec a ctx env) := by
  unfold EvalBody.evalAlgOutputSlots ActivatedBody.readRows; pres_tac

theorem EvalBody.formOutputRow_pres (rec : EvalRec) (hrec : ∀ c, Preserves R (rec c)) (ctx : EvalCtx) (env : ValEnv) (e : Expr) :
    Preserves R (EvalBody.formOutputRow rec ctx env e) := by
  unfold EvalBody.formOutputRow; pres_tac

theorem EvalBody.whileVerdictSlots_pres (rec : EvalRec) (hrec : ∀ c, Preserves R (rec c)) (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    Preserves R (EvalBody.whileVerdictSlots rec a ctx env) := by
  unfold EvalBody.whileVerdictSlots ActivatedBody.readRows; pres_tac

theorem EvalBody.evalSequenceCallbackCall_pres (rec : EvalRec) (hrec : ∀ c, Preserves R (rec c)) (callee : Algorithm) (item : CountedResult) (ctx : EvalCtx) (env : ValEnv) (calleeName : String) :
    Preserves R (EvalBody.evalSequenceCallbackCall rec callee item ctx env calleeName) := by
  unfold EvalBody.evalSequenceCallbackCall; pres_tac

theorem EvalBody.evalSequenceCallbackCallCounted_pres (rec : EvalRec) (hrec : ∀ c, Preserves R (rec c)) (callee : Algorithm) (item : CountedResult) (ctx : EvalCtx) (env : ValEnv) (calleeName : String) :
    Preserves R (EvalBody.evalSequenceCallbackCallCounted rec callee item ctx env calleeName) := by
  unfold EvalBody.evalSequenceCallbackCallCounted; pres_tac

theorem EvalBody.evalAlgOutputPreparedCore_pres (rec : EvalRec) (hrec : ∀ c, Preserves R (rec c)) (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    Preserves R (EvalBody.evalAlgOutputPreparedCore rec a ctx env) := by
  unfold EvalBody.evalAlgOutputPreparedCore; pres_tac

theorem EvalBody.evalOutputRowsPreparedCore_pres (rec : EvalRec) (hrec : ∀ c, Preserves R (rec c)) (rows : OutputBundle) (rowCtx : EvalCtx) (env : ValEnv) :
    Preserves R (EvalBody.evalOutputRowsPreparedCore rec rows rowCtx env) := by
  unfold EvalBody.evalOutputRowsPreparedCore; pres_tac

theorem EvalBody.evalCapturePreparedCore_pres (rec : EvalRec) (hrec : ∀ c, Preserves R (rec c)) (rows : OutputBundle) (ctx : EvalCtx) (env : ValEnv) :
    Preserves R (EvalBody.evalCapturePreparedCore rec rows ctx env) := by
  unfold EvalBody.evalCapturePreparedCore; pres_tac

theorem EvalBody.evalCaptureCountedCore_pres (rec : EvalRec) (hrec : ∀ c, Preserves R (rec c)) (rows : OutputBundle) (ctx : EvalCtx) (env : ValEnv) :
    Preserves R (EvalBody.evalCaptureCountedCore rec rows ctx env) := by
  unfold EvalBody.evalCaptureCountedCore; pres_tac

theorem EvalBody.evalCaptureValue_pres (rec : EvalRec) (hrec : ∀ c, Preserves R (rec c)) (rows : OutputBundle) (ctx : EvalCtx) (env : ValEnv) :
    Preserves R (EvalBody.evalCaptureValue rec rows ctx env) := by
  unfold EvalBody.evalCaptureValue; pres_tac

theorem EvalBody.evalAlgOutputCountedCore_pres (rec : EvalRec) (hrec : ∀ c, Preserves R (rec c)) (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    Preserves R (EvalBody.evalAlgOutputCountedCore rec a ctx env) := by
  unfold EvalBody.evalAlgOutputCountedCore; pres_tac

theorem EvalBody.evalAlgOutputCounted_pres (rec : EvalRec) (hrec : ∀ c, Preserves R (rec c)) (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    Preserves R (EvalBody.evalAlgOutputCounted rec a ctx env) := by
  unfold EvalBody.evalAlgOutputCounted; pres_tac

/-- A VALUE terminal's read (`EvalBody.terminalAccess`), proved once and used by every body that
    reads one, so those bodies never unfold it inline (M4★). -/
theorem EvalBody.terminalAccess_pres (rec : EvalRec) (hrec : ∀ c, Preserves R (rec c)) (t : AliasTerminal) (ctx : EvalCtx) (env : ValEnv) :
    Preserves R (EvalBody.terminalAccess rec t ctx env) := by
  unfold EvalBody.terminalAccess; pres_tac

theorem EvalBody.evalZeroArgumentDemandOutputCounted_pres (rec : EvalRec) (hrec : ∀ c, Preserves R (rec c)) (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    Preserves R (EvalBody.evalZeroArgumentDemandOutputCounted rec a ctx env) := by
  unfold EvalBody.evalZeroArgumentDemandOutputCounted; pres_tac

theorem EvalBody.evalZeroArgumentDemandOutput_pres (rec : EvalRec) (hrec : ∀ c, Preserves R (rec c)) (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    Preserves R (EvalBody.evalZeroArgumentDemandOutput rec a ctx env) := by
  unfold EvalBody.evalZeroArgumentDemandOutput; pres_tac

theorem EvalBody.evalArgumentValueCounted_pres (rec : EvalRec) (hrec : ∀ c, Preserves R (rec c)) (arg : ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) :
    Preserves R (EvalBody.evalArgumentValueCounted rec arg ctx env) := by
  unfold EvalBody.evalArgumentValueCounted; pres_tac

theorem EvalBody.evalArgumentValue_pres (rec : EvalRec) (hrec : ∀ c, Preserves R (rec c)) (arg : ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) :
    Preserves R (EvalBody.evalArgumentValue rec arg ctx env) := by
  unfold EvalBody.evalArgumentValue; pres_tac

/-- CACHE-PUB-1: a property request's calculation — a read's demand or an invocation's fresh
    zero-supply call — preserves every field-framed relation its recursive answer does. -/
theorem EvalBody.zeroArgPropertyCalculation_pres (rec : EvalRec) (hrec : ∀ c, Preserves R (rec c)) (request : ZeroArgPropertyRequest) (resolvedAlgorithm : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    Preserves R (EvalBody.zeroArgPropertyCalculation rec request resolvedAlgorithm ctx env) := by
  unfold EvalBody.zeroArgPropertyCalculation; pres_tac

theorem EvalBody.evalZeroArgPropertyAccess_pres (rec : EvalRec) (hrec : ∀ c, Preserves R (rec c)) (accessKind : ZeroArgPropertyAccessKind) (owner : Algorithm) (binding : PropDef) (resolvedAlgorithm : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    Preserves R (EvalBody.evalZeroArgPropertyAccess rec accessKind owner binding resolvedAlgorithm ctx env) := by
  unfold EvalBody.evalZeroArgPropertyAccess; pres_tac

theorem EvalBody.evalConditionalCallbackCallCounted_pres (rec : EvalRec) (hrec : ∀ c, Preserves R (rec c)) (callee : Algorithm) (args : List CountedResult) (ctx : EvalCtx) (env : ValEnv) (calleeName : String) :
    Preserves R (EvalBody.evalConditionalCallbackCallCounted rec callee args ctx env calleeName) := by
  unfold EvalBody.evalConditionalCallbackCallCounted; pres_tac

theorem EvalBody.evalUserCallbackCallCounted_pres (rec : EvalRec) (hrec : ∀ c, Preserves R (rec c)) (callee : Algorithm) (args : List CountedResult) (ctx : EvalCtx) (env : ValEnv) :
    Preserves R (EvalBody.evalUserCallbackCallCounted rec callee args ctx env) := by
  unfold EvalBody.evalUserCallbackCallCounted; pres_tac

theorem EvalBody.evalResolvedCallbackCallCounted_pres (rec : EvalRec) (hrec : ∀ c, Preserves R (rec c)) (callee : Algorithm) (args : List CountedResult) (ctx : EvalCtx) (env : ValEnv) (calleeName : String) :
    Preserves R (EvalBody.evalResolvedCallbackCallCounted rec callee args ctx env calleeName) := by
  unfold EvalBody.evalResolvedCallbackCallCounted; pres_tac

theorem EvalBody.evalResolvedCallbackCall_pres (rec : EvalRec) (hrec : ∀ c, Preserves R (rec c)) (callee : Algorithm) (args : List CountedResult) (ctx : EvalCtx) (env : ValEnv) (calleeName : String) :
    Preserves R (EvalBody.evalResolvedCallbackCall rec callee args ctx env calleeName) := by
  unfold EvalBody.evalResolvedCallbackCall; pres_tac

theorem EvalBody.evalSequenceReduceStepCounted_pres (rec : EvalRec) (hrec : ∀ c, Preserves R (rec c)) (callee : Algorithm) (element : CountedResult) (accumulator : Result) (ctx : EvalCtx) (env : ValEnv) (calleeName : String) :
    Preserves R (EvalBody.evalSequenceReduceStepCounted rec callee element accumulator ctx env calleeName) := by
  unfold EvalBody.evalSequenceReduceStepCounted; pres_tac

theorem EvalBody.demandSequenceBuiltinCallItemValue_pres (rec : EvalRec) (hrec : ∀ c, Preserves R (rec c)) (item : CallableCallItem) (ctx : EvalCtx) (env : ValEnv) :
    Preserves R (EvalBody.demandSequenceBuiltinCallItemValue rec item ctx env) := by
  unfold EvalBody.demandSequenceBuiltinCallItemValue; pres_tac

theorem EvalBody.bindSequenceBuiltinArguments_pres (rec : EvalRec) (hrec : ∀ c, Preserves R (rec c)) (b : Builtin) (metadata : SequenceBuiltinMetadata) (args : List ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) :
    Preserves R (EvalBody.bindSequenceBuiltinArguments rec b metadata args ctx env) := by
  unfold EvalBody.bindSequenceBuiltinArguments; pres_tac

theorem EvalBody.evalReduceCounted_pres (rec : EvalRec) (hrec : ∀ c, Preserves R (rec c)) (collection : List CountedResult) (stepAlg : Algorithm) (initial : Result) (ctx : EvalCtx) (env : ValEnv) :
    Preserves R (EvalBody.evalReduceCounted rec collection stepAlg initial ctx env) := by
  unfold EvalBody.evalReduceCounted; pres_tac

theorem EvalBody.evalFilterCounted_pres (rec : EvalRec) (hrec : ∀ c, Preserves R (rec c)) (items : List CountedResult) (predicateAlg : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    Preserves R (EvalBody.evalFilterCounted rec items predicateAlg ctx env) := by
  unfold EvalBody.evalFilterCounted; pres_tac

theorem EvalBody.evalMapCounted_pres (rec : EvalRec) (hrec : ∀ c, Preserves R (rec c)) (collection : List CountedResult) (transformAlg : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    Preserves R (EvalBody.evalMapCounted rec collection transformAlg ctx env) := by
  unfold EvalBody.evalMapCounted; pres_tac

theorem EvalBody.applyBuiltinCountedSequence_pres (rec : EvalRec) (hrec : ∀ c, Preserves R (rec c)) (b : Builtin) (metadata : SequenceBuiltinMetadata) (args : List ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) :
    Preserves R (EvalBody.applyBuiltinCountedSequence rec b metadata args ctx env) := by
  unfold EvalBody.applyBuiltinCountedSequence; pres_tac

-- META-S3-3 enlarged this body (the builtin META binding branch); the same tactic needs more time.
set_option maxHeartbeats 1600000 in
theorem EvalBody.applyBuiltinCounted_pres (rec : EvalRec) (hrec : ∀ c, Preserves R (rec c)) (b : Builtin) (args : List ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) :
    Preserves R (EvalBody.applyBuiltinCounted rec b args ctx env) := by
  unfold EvalBody.applyBuiltinCounted; pres_tac

theorem EvalBody.applyBuiltin_pres (rec : EvalRec) (hrec : ∀ c, Preserves R (rec c)) (b : Builtin) (args : List ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) :
    Preserves R (EvalBody.applyBuiltin rec b args ctx env) := by
  unfold EvalBody.applyBuiltin; pres_tac

theorem EvalBody.applyBuiltinCountedResolved_pres (rec : EvalRec) (hrec : ∀ c, Preserves R (rec c)) (b : Builtin) (args : List ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) :
    Preserves R (EvalBody.applyBuiltinCountedResolved rec b args ctx env) := by
  unfold EvalBody.applyBuiltinCountedResolved; pres_tac

theorem EvalBody.evalExplicitSequenceValueItems_pres (rec : EvalRec) (hrec : ∀ c, Preserves R (rec c)) (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    Preserves R (EvalBody.evalExplicitSequenceValueItems rec a ctx env) := by
  unfold EvalBody.evalExplicitSequenceValueItems; pres_tac

theorem EvalBody.evalExplicitSequenceValueRowSlots_pres (rec : EvalRec) (hrec : ∀ c, Preserves R (rec c)) (rows : OutputBundle) (rowCtx : EvalCtx) (env : ValEnv) :
    Preserves R (EvalBody.evalExplicitSequenceValueRowSlots rec rows rowCtx env) := by
  unfold EvalBody.evalExplicitSequenceValueRowSlots; pres_tac

theorem EvalBody.evalExplicitSequenceValueExprSlots_pres (rec : EvalRec) (hrec : ∀ c, Preserves R (rec c)) (expr : Expr) (ctx : EvalCtx) (env : ValEnv) :
    Preserves R (EvalBody.evalExplicitSequenceValueExprSlots rec expr ctx env) := by
  unfold EvalBody.evalExplicitSequenceValueExprSlots; pres_tac

theorem EvalBody.evalUserCallCounted_pres (rec : EvalRec) (hrec : ∀ c, Preserves R (rec c)) (callee : Algorithm) (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) :
    Preserves R (EvalBody.evalUserCallCounted rec callee args ctx env) := by
  unfold EvalBody.evalUserCallCounted; pres_tac

theorem EvalBody.evalConditionalCallCounted_pres (rec : EvalRec) (hrec : ∀ c, Preserves R (rec c)) (callee : Algorithm) (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) (calleeName : String) :
    Preserves R (EvalBody.evalConditionalCallCounted rec callee args ctx env calleeName) := by
  unfold EvalBody.evalConditionalCallCounted; pres_tac

theorem EvalBody.evalResolvedCall_pres (rec : EvalRec) (hrec : ∀ c, Preserves R (rec c)) (callee : Algorithm) (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) (calleeName : String) :
    Preserves R (EvalBody.evalResolvedCall rec callee args ctx env calleeName) := by
  unfold EvalBody.evalResolvedCall; pres_tac

theorem EvalBody.evalResolvedCallCounted_pres (rec : EvalRec) (hrec : ∀ c, Preserves R (rec c)) (callee : Algorithm) (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) (calleeName : String) (origin : CalleeOrigin) :
    Preserves R (EvalBody.evalResolvedCallCounted rec callee args ctx env calleeName origin) := by
  unfold EvalBody.evalResolvedCallCounted; pres_tac

theorem EvalBody.evalCallCountedExpr_pres (rec : EvalRec) (hrec : ∀ c, Preserves R (rec c)) (f : Expr) (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) :
    Preserves R (EvalBody.evalCallCountedExpr rec f args ctx env) := by
  unfold EvalBody.evalCallCountedExpr; pres_tac

theorem EvalBody.callLexicalWithReceiverCounted_pres (rec : EvalRec) (hrec : ∀ c, Preserves R (rec c)) (name : Ident) (receiver : Expr) (fallback : Expr) (extraArgs : Option OutputBundle) (ctx : EvalCtx) (env : ValEnv) :
    Preserves R (EvalBody.callLexicalWithReceiverCounted rec name receiver fallback extraArgs ctx env) := by
  unfold EvalBody.callLexicalWithReceiverCounted; pres_tac

theorem EvalBody.rejectDotStringIntrinsicArguments_pres (rec : EvalRec) (hrec : ∀ c, Preserves R (rec c)) (argsOpt : Option OutputBundle) (ctx : EvalCtx) (env : ValEnv) :
    Preserves R (EvalBody.rejectDotStringIntrinsicArguments rec argsOpt ctx env) := by
  unfold EvalBody.rejectDotStringIntrinsicArguments; pres_tac

theorem EvalBody.evalDotStringReceiverValue_pres (rec : EvalRec) (hrec : ∀ c, Preserves R (rec c)) (target : Expr) (targetAlg : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    Preserves R (EvalBody.evalDotStringReceiverValue rec target targetAlg ctx env) := by
  unfold EvalBody.evalDotStringReceiverValue; pres_tac

set_option maxHeartbeats 4000000 in
theorem EvalBody.evalDotCallCounted_pres (rec : EvalRec) (hrec : ∀ c, Preserves R (rec c)) (target : Expr) (name : Ident) (fallback : Expr) (argsOpt : Option OutputBundle) (ctx : EvalCtx) (env : ValEnv) :
    Preserves R (EvalBody.evalDotCallCounted rec target name fallback argsOpt ctx env) := by
  unfold EvalBody.evalDotCallCounted; pres_tac

theorem EvalBody.rejectInvokeIntrinsicArguments_pres (rec : EvalRec) (hrec : ∀ c, Preserves R (rec c)) (argsOpt : Option OutputBundle) (ctx : EvalCtx) (env : ValEnv) :
    Preserves R (EvalBody.rejectInvokeIntrinsicArguments rec argsOpt ctx env) := by
  unfold EvalBody.rejectInvokeIntrinsicArguments; pres_tac

theorem EvalBody.invokeCallReferenceValue_pres (rec : EvalRec) (hrec : ∀ c, Preserves R (rec c)) (val : Result) :
    Preserves R (EvalBody.invokeCallReferenceValue rec val) := by
  unfold EvalBody.invokeCallReferenceValue; pres_tac

theorem EvalBody.argumentViewCells_pres (rec : EvalRec) (hrec : ∀ c, Preserves R (rec c)) (a : Nat) :
    Preserves R (EvalBody.argumentViewCells rec a) := by
  unfold EvalBody.argumentViewCells; pres_tac

theorem EvalBody.evalArgumentViewBuiltin_pres (rec : EvalRec) (hrec : ∀ c, Preserves R (rec c)) (b : Builtin) (a : Nat) :
    Preserves R (EvalBody.evalArgumentViewBuiltin rec b a) := by
  unfold EvalBody.evalArgumentViewBuiltin; pres_tac

theorem EvalBody.evalSequenceSpreadOperandValue_pres (rec : EvalRec) (hrec : ∀ c, Preserves R (rec c)) (e : Expr) (ctx : EvalCtx) (env : ValEnv) :
    Preserves R (EvalBody.evalSequenceSpreadOperandValue rec e ctx env) := by
  unfold EvalBody.evalSequenceSpreadOperandValue; pres_tac

theorem EvalBody.evalSequenceSpreadCounted_pres (rec : EvalRec) (hrec : ∀ c, Preserves R (rec c)) (e : Expr) (ctx : EvalCtx) (env : ValEnv) :
    Preserves R (EvalBody.evalSequenceSpreadCounted rec e ctx env) := by
  unfold EvalBody.evalSequenceSpreadCounted; pres_tac

theorem EvalBody.evalSupplySpread_pres (rec : EvalRec) (hrec : ∀ c, Preserves R (rec c)) (e : Expr) (ctx : EvalCtx) (env : ValEnv) :
    Preserves R (EvalBody.evalSupplySpread rec e ctx env) := by
  unfold EvalBody.evalSupplySpread; pres_tac

theorem EvalBody.evalListLiteralCounted_pres (rec : EvalRec) (hrec : ∀ c, Preserves R (rec c)) (elements : List Expr) (ctx : EvalCtx) (env : ValEnv) :
    Preserves R (EvalBody.evalListLiteralCounted rec elements ctx env) := by
  unfold EvalBody.evalListLiteralCounted; pres_tac

theorem EvalBody.evalSequenceConstructCounted_pres (rec : EvalRec) (hrec : ∀ c, Preserves R (rec c)) (e : Expr) (ctx : EvalCtx) (env : ValEnv) :
    Preserves R (EvalBody.evalSequenceConstructCounted rec e ctx env) := by
  unfold EvalBody.evalSequenceConstructCounted; pres_tac

theorem EvalBody.evalUnaryCounted_pres (rec : EvalRec) (hrec : ∀ c, Preserves R (rec c)) (op : UnaryOp) (operand : Expr) (ctx : EvalCtx) (env : ValEnv) :
    Preserves R (EvalBody.evalUnaryCounted rec op operand ctx env) := by
  unfold EvalBody.evalUnaryCounted; pres_tac

theorem EvalBody.evalBinaryCounted_pres (rec : EvalRec) (hrec : ∀ c, Preserves R (rec c)) (op : BinaryOp) (a b : Expr) (ctx : EvalCtx) (env : ValEnv) :
    Preserves R (EvalBody.evalBinaryCounted rec op a b ctx env) := by
  unfold EvalBody.evalBinaryCounted; pres_tac

theorem EvalBody.evalComparisonCounted_pres (rec : EvalRec) (hrec : ∀ c, Preserves R (rec c)) (first : Expr) (links : List ComparisonLink) (ctx : EvalCtx) (env : ValEnv) :
    Preserves R (EvalBody.evalComparisonCounted rec first links ctx env) := by
  unfold EvalBody.evalComparisonCounted; pres_tac

theorem EvalBody.evalComparisonLinksCounted_pres (rec : EvalRec) (hrec : ∀ c, Preserves R (rec c)) (previousExpr : Expr) (previous : Result) (holds : Bool) (links : List ComparisonLink) (ctx : EvalCtx) (env : ValEnv) :
    Preserves R (EvalBody.evalComparisonLinksCounted rec previousExpr previous holds links ctx env) := by
  unfold EvalBody.evalComparisonLinksCounted; pres_tac

theorem EvalBody.evalCounted_pres (rec : EvalRec) (hrec : ∀ c, Preserves R (rec c)) (e : Expr) (ctx : EvalCtx) (env : ValEnv) :
    Preserves R (EvalBody.evalCounted rec e ctx env) := by
  unfold EvalBody.evalCounted; pres_tac

theorem EvalBody.evalUserCall_pres (rec : EvalRec) (hrec : ∀ c, Preserves R (rec c)) (callee : Algorithm) (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) :
    Preserves R (EvalBody.evalUserCall rec callee args ctx env) := by
  unfold EvalBody.evalUserCall; pres_tac

theorem EvalBody.evalConditionalCall_pres (rec : EvalRec) (hrec : ∀ c, Preserves R (rec c)) (callee : Algorithm) (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) (calleeName : String) :
    Preserves R (EvalBody.evalConditionalCall rec callee args ctx env calleeName) := by
  unfold EvalBody.evalConditionalCall; pres_tac

theorem EvalBody.evalCallExpr_pres (rec : EvalRec) (hrec : ∀ c, Preserves R (rec c)) (f : Expr) (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) :
    Preserves R (EvalBody.evalCallExpr rec f args ctx env) := by
  unfold EvalBody.evalCallExpr; pres_tac

theorem EvalBody.evalDotCall_pres (rec : EvalRec) (hrec : ∀ c, Preserves R (rec c)) (target : Expr) (name : Ident) (fallback : Expr) (argsOpt : Option OutputBundle) (ctx : EvalCtx) (env : ValEnv) :
    Preserves R (EvalBody.evalDotCall rec target name fallback argsOpt ctx env) := by
  unfold EvalBody.evalDotCall; pres_tac

theorem EvalBody.eval_pres (rec : EvalRec) (hrec : ∀ c, Preserves R (rec c)) (e : Expr) (ctx : EvalCtx) (env : ValEnv) :
    Preserves R (EvalBody.eval rec e ctx env) := by
  unfold EvalBody.eval; pres_tac

/-- The per-body step of every field-framed whole-run invariant, given its step for the one
    body that writes the property cache and its owner set. -/
theorem evalStep_preserves
    (hprop : ∀ rec : EvalRec, (∀ c, Preserves R (rec c)) → ∀ accessKind owner binding resolvedAlgorithm ctx env request,
      Preserves R (EvalBody.evalZeroArgPropertyAccessCounted rec accessKind owner binding resolvedAlgorithm ctx env request))
    (rec : EvalRec) (hrec : ∀ c, Preserves R (rec c)) : ∀ c, Preserves R (evalStep rec c) := by
  intro c
  cases c with
  | whileLoop step ctx env stepName cells => exact EvalBody.whileLoop_pres rec hrec step ctx env stepName cells
  | aliasStepIsRuntime step target ctx visited => exact EvalBody.aliasStepIsRuntime_pres rec hrec step target ctx visited
  | aliasValue wired ctx env => exact EvalBody.aliasValue_pres rec hrec wired ctx env
  | resolveAliasChase followCarriers projectRuntime a ctx visited last => exact EvalBody.resolveAliasChase_pres rec hrec followCarriers projectRuntime a ctx visited last
  | resolveAliasTarget a ctx => exact EvalBody.resolveAliasTarget_pres rec hrec a ctx
  | resolveAliasStructure a ctx => exact EvalBody.resolveAliasStructure_pres rec hrec a ctx
  | resolveAliasValueTarget a ctx => exact EvalBody.resolveAliasValueTarget_pres rec hrec a ctx
  | aliasOriginBinding? a ctx => exact EvalBody.aliasOriginBinding?_pres rec hrec a ctx
  | lookupLexicalProperty a name ctx => exact EvalBody.lookupLexicalProperty_pres rec hrec a name ctx
  | lookupLexicalValueProperty a name ctx => exact EvalBody.lookupLexicalValueProperty_pres rec hrec a name ctx
  | lookupLexical a name ctx => exact EvalBody.lookupLexical_pres rec hrec a name ctx
  | needPlanNormalizeCallee callee ctx => exact EvalBody.needPlanNormalizeCallee_pres rec hrec callee ctx
  | resolveAlg e ctx => exact EvalBody.resolveAlg_pres rec hrec e ctx
  | projectNeedCallable address => exact EvalBody.projectNeedCallable_pres rec hrec address
  | projectNeedWrittenAt address source caller => exact EvalBody.projectNeedWrittenAt_pres rec hrec address source caller
  | linkCallable address => exact EvalBody.linkCallable_pres rec hrec address
  | projectParameterCallable x ctx => exact EvalBody.projectParameterCallable_pres rec hrec x ctx
  | projectNeedWritten source caller => exact EvalBody.projectNeedWritten_pres rec hrec source caller
  | projectNeedStructuralMember source ctx => exact EvalBody.projectNeedStructuralMember_pres rec hrec source ctx
  | resolveCalleeAlg f ctx => exact EvalBody.resolveCalleeAlg_pres rec hrec f ctx
  | expectPreparedSequenceBuiltinAlgorithmSuffixArg b descriptors args index => exact EvalBody.expectPreparedSequenceBuiltinAlgorithmSuffixArg_pres rec hrec b descriptors args index
  | resolveDotReceiver? e ctx => exact EvalBody.resolveDotReceiver?_pres rec hrec e ctx
  | resolveDotReceiver e ctx => exact EvalBody.resolveDotReceiver_pres rec hrec e ctx
  | algorithmIntrinsicRoute receiver ctx => exact EvalBody.algorithmIntrinsicRoute_pres rec hrec receiver ctx
  | demandNeedRecursive address => exact EvalBody.demandNeedRecursive_pres rec hrec address
  | evalSuppliedAt address e ctx env => exact EvalBody.evalSuppliedAt_pres rec hrec address e ctx env
  | linkValue address => exact EvalBody.linkValue_pres rec hrec address
  | algorithmOfValue val argsOpt ctx env => exact EvalBody.algorithmOfValue_pres rec hrec val argsOpt ctx env
  | capturedCallee callee => exact EvalBody.capturedCallee_pres rec hrec callee
  | referenceReceiverValue target targetAlg ctx env => exact EvalBody.referenceReceiverValue_pres rec hrec target targetAlg ctx env
  | algorithmCalleeOf receiver ctx env => exact EvalBody.algorithmCalleeOf_pres rec hrec receiver ctx env
  | evalSuppliedCallCounted origin callee cells ctx env calleeName => exact EvalBody.evalSuppliedCallCounted_pres rec hrec origin callee cells ctx env calleeName
  | evalNeedUserSupply callee cells ctx env => exact EvalBody.evalNeedUserSupply_pres rec hrec callee cells ctx env
  | evalNeedFamilySupply callee cells ctx env calleeName => exact EvalBody.evalNeedFamilySupply_pres rec hrec callee cells ctx env calleeName
  | invokeNeed arg => exact EvalBody.invokeNeed_pres rec hrec arg
  | argumentNeed arg ctx env => exact EvalBody.argumentNeed_pres rec hrec arg ctx env
  | runNeedStepSlots step ctx env cells stepName => exact EvalBody.runNeedStepSlots_pres rec hrec step ctx env cells stepName
  | runNeedWhileRound step ctx env cells stepName => exact EvalBody.runNeedWhileRound_pres rec hrec step ctx env cells stepName
  | evalAlgOutputCore a ctx env => exact EvalBody.evalAlgOutputCore_pres rec hrec a ctx env
  | evalAlgOutput a ctx env => exact EvalBody.evalAlgOutput_pres rec hrec a ctx env
  | evalProgramOutput a ctx env => exact EvalBody.evalProgramOutput_pres rec hrec a ctx env
  | evalAlgOutputSlots a ctx env => exact EvalBody.evalAlgOutputSlots_pres rec hrec a ctx env
  | formOutputRow ctx env e => exact EvalBody.formOutputRow_pres rec hrec ctx env e
  | whileVerdictSlots a ctx env => exact EvalBody.whileVerdictSlots_pres rec hrec a ctx env
  | evalSequenceCallbackCall callee item ctx env calleeName => exact EvalBody.evalSequenceCallbackCall_pres rec hrec callee item ctx env calleeName
  | evalSequenceCallbackCallCounted callee item ctx env calleeName => exact EvalBody.evalSequenceCallbackCallCounted_pres rec hrec callee item ctx env calleeName
  | evalAlgOutputPreparedCore a ctx env => exact EvalBody.evalAlgOutputPreparedCore_pres rec hrec a ctx env
  | evalOutputRowsPreparedCore rows rowCtx env => exact EvalBody.evalOutputRowsPreparedCore_pres rec hrec rows rowCtx env
  | evalCapturePreparedCore rows ctx env => exact EvalBody.evalCapturePreparedCore_pres rec hrec rows ctx env
  | evalCaptureCountedCore rows ctx env => exact EvalBody.evalCaptureCountedCore_pres rec hrec rows ctx env
  | evalCaptureValue rows ctx env => exact EvalBody.evalCaptureValue_pres rec hrec rows ctx env
  | evalAlgOutputCountedCore a ctx env => exact EvalBody.evalAlgOutputCountedCore_pres rec hrec a ctx env
  | evalAlgOutputCounted a ctx env => exact EvalBody.evalAlgOutputCounted_pres rec hrec a ctx env
  | evalZeroArgumentDemandOutputCounted a ctx env => exact EvalBody.evalZeroArgumentDemandOutputCounted_pres rec hrec a ctx env
  | evalZeroArgumentDemandOutput a ctx env => exact EvalBody.evalZeroArgumentDemandOutput_pres rec hrec a ctx env
  | evalArgumentValueCounted arg ctx env => exact EvalBody.evalArgumentValueCounted_pres rec hrec arg ctx env
  | evalArgumentValue arg ctx env => exact EvalBody.evalArgumentValue_pres rec hrec arg ctx env
  | evalZeroArgPropertyAccessCounted accessKind owner binding resolvedAlgorithm ctx env request => exact hprop rec hrec accessKind owner binding resolvedAlgorithm ctx env request
  | evalZeroArgPropertyAccess accessKind owner binding resolvedAlgorithm ctx env => exact EvalBody.evalZeroArgPropertyAccess_pres rec hrec accessKind owner binding resolvedAlgorithm ctx env
  | evalConditionalCallbackCallCounted callee args ctx env calleeName => exact EvalBody.evalConditionalCallbackCallCounted_pres rec hrec callee args ctx env calleeName
  | evalUserCallbackCallCounted callee args ctx env => exact EvalBody.evalUserCallbackCallCounted_pres rec hrec callee args ctx env
  | evalResolvedCallbackCallCounted callee args ctx env calleeName => exact EvalBody.evalResolvedCallbackCallCounted_pres rec hrec callee args ctx env calleeName
  | evalResolvedCallbackCall callee args ctx env calleeName => exact EvalBody.evalResolvedCallbackCall_pres rec hrec callee args ctx env calleeName
  | evalSequenceReduceStepCounted callee element accumulator ctx env calleeName => exact EvalBody.evalSequenceReduceStepCounted_pres rec hrec callee element accumulator ctx env calleeName
  | demandSequenceBuiltinCallItemValue item ctx env => exact EvalBody.demandSequenceBuiltinCallItemValue_pres rec hrec item ctx env
  | bindSequenceBuiltinArguments b metadata args ctx env => exact EvalBody.bindSequenceBuiltinArguments_pres rec hrec b metadata args ctx env
  | evalReduceCounted collection stepAlg initial ctx env => exact EvalBody.evalReduceCounted_pres rec hrec collection stepAlg initial ctx env
  | evalFilterCounted items predicateAlg ctx env => exact EvalBody.evalFilterCounted_pres rec hrec items predicateAlg ctx env
  | evalMapCounted collection transformAlg ctx env => exact EvalBody.evalMapCounted_pres rec hrec collection transformAlg ctx env
  | applyBuiltinCountedSequence b metadata args ctx env => exact EvalBody.applyBuiltinCountedSequence_pres rec hrec b metadata args ctx env
  | applyBuiltinCounted b args ctx env => exact EvalBody.applyBuiltinCounted_pres rec hrec b args ctx env
  | applyBuiltin b args ctx env => exact EvalBody.applyBuiltin_pres rec hrec b args ctx env
  | applyBuiltinCountedResolved b args ctx env => exact EvalBody.applyBuiltinCountedResolved_pres rec hrec b args ctx env
  | evalExplicitSequenceValueItems a ctx env => exact EvalBody.evalExplicitSequenceValueItems_pres rec hrec a ctx env
  | evalExplicitSequenceValueRowSlots rows rowCtx env => exact EvalBody.evalExplicitSequenceValueRowSlots_pres rec hrec rows rowCtx env
  | evalExplicitSequenceValueExprSlots expr ctx env => exact EvalBody.evalExplicitSequenceValueExprSlots_pres rec hrec expr ctx env
  | evalUserCallCounted callee args ctx env => exact EvalBody.evalUserCallCounted_pres rec hrec callee args ctx env
  | evalConditionalCallCounted callee args ctx env calleeName => exact EvalBody.evalConditionalCallCounted_pres rec hrec callee args ctx env calleeName
  | evalResolvedCall callee args ctx env calleeName => exact EvalBody.evalResolvedCall_pres rec hrec callee args ctx env calleeName
  | evalResolvedCallCounted callee args ctx env calleeName origin => exact EvalBody.evalResolvedCallCounted_pres rec hrec callee args ctx env calleeName origin
  | evalCallCountedExpr f args ctx env => exact EvalBody.evalCallCountedExpr_pres rec hrec f args ctx env
  | callLexicalWithReceiverCounted name receiver fallback extraArgs ctx env => exact EvalBody.callLexicalWithReceiverCounted_pres rec hrec name receiver fallback extraArgs ctx env
  | rejectDotStringIntrinsicArguments argsOpt ctx env => exact EvalBody.rejectDotStringIntrinsicArguments_pres rec hrec argsOpt ctx env
  | evalDotStringReceiverValue target targetAlg ctx env => exact EvalBody.evalDotStringReceiverValue_pres rec hrec target targetAlg ctx env
  | evalDotCallCounted target name fallback argsOpt ctx env => exact EvalBody.evalDotCallCounted_pres rec hrec target name fallback argsOpt ctx env
  | rejectInvokeIntrinsicArguments argsOpt ctx env => exact EvalBody.rejectInvokeIntrinsicArguments_pres rec hrec argsOpt ctx env
  | invokeCallReferenceValue val => exact EvalBody.invokeCallReferenceValue_pres rec hrec val
  | argumentViewCells a => exact EvalBody.argumentViewCells_pres rec hrec a
  | evalArgumentViewBuiltin b a => exact EvalBody.evalArgumentViewBuiltin_pres rec hrec b a
  | evalSequenceSpreadOperandValue e ctx env => exact EvalBody.evalSequenceSpreadOperandValue_pres rec hrec e ctx env
  | evalSequenceSpreadCounted e ctx env => exact EvalBody.evalSequenceSpreadCounted_pres rec hrec e ctx env
  | evalSupplySpread e ctx env => exact EvalBody.evalSupplySpread_pres rec hrec e ctx env
  | evalListLiteralCounted elements ctx env => exact EvalBody.evalListLiteralCounted_pres rec hrec elements ctx env
  | evalSequenceConstructCounted e ctx env => exact EvalBody.evalSequenceConstructCounted_pres rec hrec e ctx env
  | evalUnaryCounted op operand ctx env => exact EvalBody.evalUnaryCounted_pres rec hrec op operand ctx env
  | evalBinaryCounted op a b ctx env => exact EvalBody.evalBinaryCounted_pres rec hrec op a b ctx env
  | evalComparisonCounted first links ctx env => exact EvalBody.evalComparisonCounted_pres rec hrec first links ctx env
  | evalComparisonLinksCounted previousExpr previous holds links ctx env => exact EvalBody.evalComparisonLinksCounted_pres rec hrec previousExpr previous holds links ctx env
  | evalCounted e ctx env => exact EvalBody.evalCounted_pres rec hrec e ctx env
  | evalUserCall callee args ctx env => exact EvalBody.evalUserCall_pres rec hrec callee args ctx env
  | evalConditionalCall callee args ctx env calleeName => exact EvalBody.evalConditionalCall_pres rec hrec callee args ctx env calleeName
  | evalCallExpr f args ctx env => exact EvalBody.evalCallExpr_pres rec hrec f args ctx env
  | evalDotCall target name fallback argsOpt ctx env => exact EvalBody.evalDotCall_pres rec hrec target name fallback argsOpt ctx env
  | eval e ctx env => exact EvalBody.eval_pres rec hrec e ctx env

/-- The one body that writes the property cache and its owner set. -/
def isPropertyAccessCall : EvalCall → Bool
  | .evalZeroArgPropertyAccessCounted .. => true
  | _ => false

/-- Every other body preserves every field-framed relation. -/
theorem evalStep_preserves_other (rec : EvalRec) (hrec : ∀ c, Preserves R (rec c)) (c : EvalCall)
    (hc : isPropertyAccessCall c = false) : Preserves R (evalStep rec c) := by
  cases c with
  | whileLoop step ctx env stepName cells => exact EvalBody.whileLoop_pres rec hrec step ctx env stepName cells
  | aliasStepIsRuntime step target ctx visited => exact EvalBody.aliasStepIsRuntime_pres rec hrec step target ctx visited
  | aliasValue wired ctx env => exact EvalBody.aliasValue_pres rec hrec wired ctx env
  | resolveAliasChase followCarriers projectRuntime a ctx visited last => exact EvalBody.resolveAliasChase_pres rec hrec followCarriers projectRuntime a ctx visited last
  | resolveAliasTarget a ctx => exact EvalBody.resolveAliasTarget_pres rec hrec a ctx
  | resolveAliasStructure a ctx => exact EvalBody.resolveAliasStructure_pres rec hrec a ctx
  | resolveAliasValueTarget a ctx => exact EvalBody.resolveAliasValueTarget_pres rec hrec a ctx
  | aliasOriginBinding? a ctx => exact EvalBody.aliasOriginBinding?_pres rec hrec a ctx
  | lookupLexicalProperty a name ctx => exact EvalBody.lookupLexicalProperty_pres rec hrec a name ctx
  | lookupLexicalValueProperty a name ctx => exact EvalBody.lookupLexicalValueProperty_pres rec hrec a name ctx
  | lookupLexical a name ctx => exact EvalBody.lookupLexical_pres rec hrec a name ctx
  | needPlanNormalizeCallee callee ctx => exact EvalBody.needPlanNormalizeCallee_pres rec hrec callee ctx
  | resolveAlg e ctx => exact EvalBody.resolveAlg_pres rec hrec e ctx
  | projectNeedCallable address => exact EvalBody.projectNeedCallable_pres rec hrec address
  | projectNeedWrittenAt address source caller => exact EvalBody.projectNeedWrittenAt_pres rec hrec address source caller
  | linkCallable address => exact EvalBody.linkCallable_pres rec hrec address
  | projectParameterCallable x ctx => exact EvalBody.projectParameterCallable_pres rec hrec x ctx
  | projectNeedWritten source caller => exact EvalBody.projectNeedWritten_pres rec hrec source caller
  | projectNeedStructuralMember source ctx => exact EvalBody.projectNeedStructuralMember_pres rec hrec source ctx
  | resolveCalleeAlg f ctx => exact EvalBody.resolveCalleeAlg_pres rec hrec f ctx
  | expectPreparedSequenceBuiltinAlgorithmSuffixArg b descriptors args index => exact EvalBody.expectPreparedSequenceBuiltinAlgorithmSuffixArg_pres rec hrec b descriptors args index
  | resolveDotReceiver? e ctx => exact EvalBody.resolveDotReceiver?_pres rec hrec e ctx
  | resolveDotReceiver e ctx => exact EvalBody.resolveDotReceiver_pres rec hrec e ctx
  | algorithmIntrinsicRoute receiver ctx => exact EvalBody.algorithmIntrinsicRoute_pres rec hrec receiver ctx
  | demandNeedRecursive address => exact EvalBody.demandNeedRecursive_pres rec hrec address
  | evalSuppliedAt address e ctx env => exact EvalBody.evalSuppliedAt_pres rec hrec address e ctx env
  | linkValue address => exact EvalBody.linkValue_pres rec hrec address
  | algorithmOfValue val argsOpt ctx env => exact EvalBody.algorithmOfValue_pres rec hrec val argsOpt ctx env
  | capturedCallee callee => exact EvalBody.capturedCallee_pres rec hrec callee
  | referenceReceiverValue target targetAlg ctx env => exact EvalBody.referenceReceiverValue_pres rec hrec target targetAlg ctx env
  | algorithmCalleeOf receiver ctx env => exact EvalBody.algorithmCalleeOf_pres rec hrec receiver ctx env
  | evalSuppliedCallCounted origin callee cells ctx env calleeName => exact EvalBody.evalSuppliedCallCounted_pres rec hrec origin callee cells ctx env calleeName
  | evalNeedUserSupply callee cells ctx env => exact EvalBody.evalNeedUserSupply_pres rec hrec callee cells ctx env
  | evalNeedFamilySupply callee cells ctx env calleeName => exact EvalBody.evalNeedFamilySupply_pres rec hrec callee cells ctx env calleeName
  | invokeNeed arg => exact EvalBody.invokeNeed_pres rec hrec arg
  | argumentNeed arg ctx env => exact EvalBody.argumentNeed_pres rec hrec arg ctx env
  | runNeedStepSlots step ctx env cells stepName => exact EvalBody.runNeedStepSlots_pres rec hrec step ctx env cells stepName
  | runNeedWhileRound step ctx env cells stepName => exact EvalBody.runNeedWhileRound_pres rec hrec step ctx env cells stepName
  | evalAlgOutputCore a ctx env => exact EvalBody.evalAlgOutputCore_pres rec hrec a ctx env
  | evalAlgOutput a ctx env => exact EvalBody.evalAlgOutput_pres rec hrec a ctx env
  | evalProgramOutput a ctx env => exact EvalBody.evalProgramOutput_pres rec hrec a ctx env
  | evalAlgOutputSlots a ctx env => exact EvalBody.evalAlgOutputSlots_pres rec hrec a ctx env
  | formOutputRow ctx env e => exact EvalBody.formOutputRow_pres rec hrec ctx env e
  | whileVerdictSlots a ctx env => exact EvalBody.whileVerdictSlots_pres rec hrec a ctx env
  | evalSequenceCallbackCall callee item ctx env calleeName => exact EvalBody.evalSequenceCallbackCall_pres rec hrec callee item ctx env calleeName
  | evalSequenceCallbackCallCounted callee item ctx env calleeName => exact EvalBody.evalSequenceCallbackCallCounted_pres rec hrec callee item ctx env calleeName
  | evalAlgOutputPreparedCore a ctx env => exact EvalBody.evalAlgOutputPreparedCore_pres rec hrec a ctx env
  | evalOutputRowsPreparedCore rows rowCtx env => exact EvalBody.evalOutputRowsPreparedCore_pres rec hrec rows rowCtx env
  | evalCapturePreparedCore rows ctx env => exact EvalBody.evalCapturePreparedCore_pres rec hrec rows ctx env
  | evalCaptureCountedCore rows ctx env => exact EvalBody.evalCaptureCountedCore_pres rec hrec rows ctx env
  | evalCaptureValue rows ctx env => exact EvalBody.evalCaptureValue_pres rec hrec rows ctx env
  | evalAlgOutputCountedCore a ctx env => exact EvalBody.evalAlgOutputCountedCore_pres rec hrec a ctx env
  | evalAlgOutputCounted a ctx env => exact EvalBody.evalAlgOutputCounted_pres rec hrec a ctx env
  | evalZeroArgumentDemandOutputCounted a ctx env => exact EvalBody.evalZeroArgumentDemandOutputCounted_pres rec hrec a ctx env
  | evalZeroArgumentDemandOutput a ctx env => exact EvalBody.evalZeroArgumentDemandOutput_pres rec hrec a ctx env
  | evalArgumentValueCounted arg ctx env => exact EvalBody.evalArgumentValueCounted_pres rec hrec arg ctx env
  | evalArgumentValue arg ctx env => exact EvalBody.evalArgumentValue_pres rec hrec arg ctx env
  | evalZeroArgPropertyAccessCounted accessKind owner binding resolvedAlgorithm ctx env request => cases hc
  | evalZeroArgPropertyAccess accessKind owner binding resolvedAlgorithm ctx env => exact EvalBody.evalZeroArgPropertyAccess_pres rec hrec accessKind owner binding resolvedAlgorithm ctx env
  | evalConditionalCallbackCallCounted callee args ctx env calleeName => exact EvalBody.evalConditionalCallbackCallCounted_pres rec hrec callee args ctx env calleeName
  | evalUserCallbackCallCounted callee args ctx env => exact EvalBody.evalUserCallbackCallCounted_pres rec hrec callee args ctx env
  | evalResolvedCallbackCallCounted callee args ctx env calleeName => exact EvalBody.evalResolvedCallbackCallCounted_pres rec hrec callee args ctx env calleeName
  | evalResolvedCallbackCall callee args ctx env calleeName => exact EvalBody.evalResolvedCallbackCall_pres rec hrec callee args ctx env calleeName
  | evalSequenceReduceStepCounted callee element accumulator ctx env calleeName => exact EvalBody.evalSequenceReduceStepCounted_pres rec hrec callee element accumulator ctx env calleeName
  | demandSequenceBuiltinCallItemValue item ctx env => exact EvalBody.demandSequenceBuiltinCallItemValue_pres rec hrec item ctx env
  | bindSequenceBuiltinArguments b metadata args ctx env => exact EvalBody.bindSequenceBuiltinArguments_pres rec hrec b metadata args ctx env
  | evalReduceCounted collection stepAlg initial ctx env => exact EvalBody.evalReduceCounted_pres rec hrec collection stepAlg initial ctx env
  | evalFilterCounted items predicateAlg ctx env => exact EvalBody.evalFilterCounted_pres rec hrec items predicateAlg ctx env
  | evalMapCounted collection transformAlg ctx env => exact EvalBody.evalMapCounted_pres rec hrec collection transformAlg ctx env
  | applyBuiltinCountedSequence b metadata args ctx env => exact EvalBody.applyBuiltinCountedSequence_pres rec hrec b metadata args ctx env
  | applyBuiltinCounted b args ctx env => exact EvalBody.applyBuiltinCounted_pres rec hrec b args ctx env
  | applyBuiltin b args ctx env => exact EvalBody.applyBuiltin_pres rec hrec b args ctx env
  | applyBuiltinCountedResolved b args ctx env => exact EvalBody.applyBuiltinCountedResolved_pres rec hrec b args ctx env
  | evalExplicitSequenceValueItems a ctx env => exact EvalBody.evalExplicitSequenceValueItems_pres rec hrec a ctx env
  | evalExplicitSequenceValueRowSlots rows rowCtx env => exact EvalBody.evalExplicitSequenceValueRowSlots_pres rec hrec rows rowCtx env
  | evalExplicitSequenceValueExprSlots expr ctx env => exact EvalBody.evalExplicitSequenceValueExprSlots_pres rec hrec expr ctx env
  | evalUserCallCounted callee args ctx env => exact EvalBody.evalUserCallCounted_pres rec hrec callee args ctx env
  | evalConditionalCallCounted callee args ctx env calleeName => exact EvalBody.evalConditionalCallCounted_pres rec hrec callee args ctx env calleeName
  | evalResolvedCall callee args ctx env calleeName => exact EvalBody.evalResolvedCall_pres rec hrec callee args ctx env calleeName
  | evalResolvedCallCounted callee args ctx env calleeName origin => exact EvalBody.evalResolvedCallCounted_pres rec hrec callee args ctx env calleeName origin
  | evalCallCountedExpr f args ctx env => exact EvalBody.evalCallCountedExpr_pres rec hrec f args ctx env
  | callLexicalWithReceiverCounted name receiver fallback extraArgs ctx env => exact EvalBody.callLexicalWithReceiverCounted_pres rec hrec name receiver fallback extraArgs ctx env
  | rejectDotStringIntrinsicArguments argsOpt ctx env => exact EvalBody.rejectDotStringIntrinsicArguments_pres rec hrec argsOpt ctx env
  | evalDotStringReceiverValue target targetAlg ctx env => exact EvalBody.evalDotStringReceiverValue_pres rec hrec target targetAlg ctx env
  | evalDotCallCounted target name fallback argsOpt ctx env => exact EvalBody.evalDotCallCounted_pres rec hrec target name fallback argsOpt ctx env
  | rejectInvokeIntrinsicArguments argsOpt ctx env => exact EvalBody.rejectInvokeIntrinsicArguments_pres rec hrec argsOpt ctx env
  | invokeCallReferenceValue val => exact EvalBody.invokeCallReferenceValue_pres rec hrec val
  | argumentViewCells a => exact EvalBody.argumentViewCells_pres rec hrec a
  | evalArgumentViewBuiltin b a => exact EvalBody.evalArgumentViewBuiltin_pres rec hrec b a
  | evalSequenceSpreadOperandValue e ctx env => exact EvalBody.evalSequenceSpreadOperandValue_pres rec hrec e ctx env
  | evalSequenceSpreadCounted e ctx env => exact EvalBody.evalSequenceSpreadCounted_pres rec hrec e ctx env
  | evalSupplySpread e ctx env => exact EvalBody.evalSupplySpread_pres rec hrec e ctx env
  | evalListLiteralCounted elements ctx env => exact EvalBody.evalListLiteralCounted_pres rec hrec elements ctx env
  | evalSequenceConstructCounted e ctx env => exact EvalBody.evalSequenceConstructCounted_pres rec hrec e ctx env
  | evalUnaryCounted op operand ctx env => exact EvalBody.evalUnaryCounted_pres rec hrec op operand ctx env
  | evalBinaryCounted op a b ctx env => exact EvalBody.evalBinaryCounted_pres rec hrec op a b ctx env
  | evalComparisonCounted first links ctx env => exact EvalBody.evalComparisonCounted_pres rec hrec first links ctx env
  | evalComparisonLinksCounted previousExpr previous holds links ctx env => exact EvalBody.evalComparisonLinksCounted_pres rec hrec previousExpr previous holds links ctx env
  | evalCounted e ctx env => exact EvalBody.evalCounted_pres rec hrec e ctx env
  | evalUserCall callee args ctx env => exact EvalBody.evalUserCall_pres rec hrec callee args ctx env
  | evalConditionalCall callee args ctx env calleeName => exact EvalBody.evalConditionalCall_pres rec hrec callee args ctx env calleeName
  | evalCallExpr f args ctx env => exact EvalBody.evalCallExpr_pres rec hrec f args ctx env
  | evalDotCall target name fallback argsOpt ctx env => exact EvalBody.evalDotCall_pres rec hrec target name fallback argsOpt ctx env
  | eval e ctx env => exact EvalBody.eval_pres rec hrec e ctx env

end Bodies

/-! ## Q-37: published entries are never replaced or removed -/

/-- Every entry the property cache holds at the entry state is held, with the same value, at the
    exit state. -/
def CacheKept (s t : EvalState) : Prop :=
  ∀ k v, ZeroArgPropertyCache.lookup s.zeroArgPropertyCache k = some v →
    ZeroArgPropertyCache.lookup t.zeroArgPropertyCache k = some v

instance : StateRel CacheKept := ⟨fun _ _ _ h => h, fun h1 h2 k v h => h2 k v (h1 k v h)⟩
instance : FieldFrame CacheKept := ⟨fun s t hc _ k v h => by rw [hc]; exact h⟩

/-- Publication never replaces an entry: `insert` keeps an existing equal key's value and only
    appends otherwise, so every earlier lookup is unchanged. -/
theorem lookup_insert_keep (c : ZeroArgPropertyCache) (key : ZeroArgPropertyCacheKey) (val : CountedResult)
    (k : ZeroArgPropertyCacheKey) (v : CountedResult) (h : ZeroArgPropertyCache.lookup c k = some v) :
    ZeroArgPropertyCache.lookup (ZeroArgPropertyCache.insert c key val) k = some v := by
  induction c with
  | nil => simp [ZeroArgPropertyCache.lookup] at h
  | cons e rest ih =>
    obtain ⟨ek, ev⟩ := e
    simp only [ZeroArgPropertyCache.insert]
    split
    · exact h
    · simp only [ZeroArgPropertyCache.lookup] at h ⊢
      split
      · rename_i hk; rw [if_pos hk] at h; exact h
      · rename_i hk; rw [if_neg hk] at h; exact ih h

macro_rules | `(tactic| pres_rel_close) => `(tactic| (first | (exact fun _ _ h => h) | (exact fun _ _ h => lookup_insert_keep _ _ _ _ _ h)))

theorem get_runState (s : EvalState) : (get : EvalM EvalState).runState s = (.ok s, s) := rfl
theorem set_runState (t s : EvalState) : (set t : EvalM PUnit).runState s = (.ok (), t) := rfl
theorem pure_runState {α : Type} (a : α) (s : EvalState) : (pure a : EvalM α).runState s = (.ok a, s) := rfl
theorem throw_runState {α : Type} (e : Error) (s : EvalState) : (throw e : EvalM α).runState s = (.error e, s) := rfl

/-- The two outcomes of a probe: the incomplete outcome propagates, every completed outcome is
    captured; the state is the probe's own exit state either way. -/
theorem evalAttempt_cases {α : Type} (m : EvalM α) (t : EvalState) :
    ∃ o t', m.runState t = (o, t') ∧
      (((evalAttempt m).runState t = (.error .fuelExhausted, t') ∧ o.isIncomplete = true) ∨
       ((evalAttempt m).runState t = (.ok o, t') ∧ o.isIncomplete = false)) := by
  rcases hm : m.runState t with ⟨o, t'⟩
  refine ⟨o, t', rfl, ?_⟩
  cases hi : o.isIncomplete
  · exact .inr ⟨evalAttempt_runState_of_complete m t t' o hm hi, rfl⟩
  · exact .inl ⟨by rw [Except.isIncomplete_eq_true hi] at hm; exact evalAttempt_runState_of_incomplete m t t' hm, rfl⟩

theorem cache_property_step (rec : EvalRec) (hrec : ∀ c, Preserves CacheKept (rec c))
    (accessKind : ZeroArgPropertyAccessKind) (owner : Algorithm) (binding : PropDef)
    (resolvedAlgorithm : Algorithm) (ctx : EvalCtx) (env : ValEnv) (request : ZeroArgPropertyRequest) :
    Preserves CacheKept (EvalBody.evalZeroArgPropertyAccessCounted rec accessKind owner binding resolvedAlgorithm ctx env request) := by
  -- Both requests' calculations keep every entry (`zeroArgPropertyCalculation_pres`): a read
  -- returns an established entry, an invocation executes freshly beside it, and the owner's
  -- publication never replaces one (`lookup_insert_keep`).
  have hcalc := EvalBody.zeroArgPropertyCalculation_pres (R := CacheKept) rec hrec request resolvedAlgorithm ctx env
  intro s
  unfold EvalBody.evalZeroArgPropertyAccessCounted
  split
  · simp only [EvalM.bind_runState, get_runState]
    split
    · cases request with
      | read => exact StateRel.refl s
      | invoke _ => exact hcalc s
    · split
      · exact hcalc s
      · simp only [EvalM.bind_runState, set_runState]
        obtain ⟨o, t2, hm, hc⟩ := evalAttempt_cases (EvalBody.zeroArgPropertyCalculation rec request resolvedAlgorithm ctx env)
          { s with activeZeroArgProperties := (zeroArgPropertyCacheKey accessKind owner binding ctx env (propertyOwnerBindingContext resolvedAlgorithm.parent s)) :: s.activeZeroArgProperties }
        have hk := hcalc { s with activeZeroArgProperties := (zeroArgPropertyCacheKey accessKind owner binding ctx env (propertyOwnerBindingContext resolvedAlgorithm.parent s)) :: s.activeZeroArgProperties }
        rw [hm] at hk
        rcases hc with ⟨hrun, _⟩ | ⟨hrun, _⟩
        · rw [hrun]; exact fun k v h => hk k v h
        · rw [hrun]
          simp only [get_runState]
          cases o with
          | ok counted =>
            simp only [EvalM.bind_runState, set_runState, pure_runState]
            exact fun k v h => lookup_insert_keep _ _ _ _ _ (hk k v h)
          | error err =>
            simp only [EvalM.bind_runState, set_runState, throw_runState]
            exact fun k v h => hk k v h
  · exact hcalc s

/-- **Q-37, whole run (core):** every completed run of the total core, at every fuel and from
    every state, keeps every property-cache entry it found, with its value — success and ordinary
    failure alike (an owner failure publishes nothing, and nested publications are never undone). -/
theorem cache_entries_survive_core (n : Nat) (c : EvalCall) (s : EvalState)
    (hc : Completes (evalFuel n c) s) : CacheKept s ((evalFuel n c).runState s).2 :=
  invariant_transfer CacheKept StateRel.refl
    (fun rec hrec => evalStep_preserves cache_property_step rec hrec) n c s hc

/-- **Q-37, whole run (production):** every production evaluator operation keeps every
    property-cache entry it found, with its value. -/
theorem cache_entries_survive (c : EvalCall) : Preserves CacheKept (evalUnbounded c) :=
  production_preserves CacheKept StateRel.refl
    (fun rec hrec => evalStep_preserves cache_property_step rec hrec) c


/-! ## Q-37: the owner set's entry/exit discipline on completed runs

An owning property-style evaluation marks its key active, runs, and on BOTH success and ordinary
failure restores the owner set it found. An INCOMPLETE inner run legitimately leaves the mark (the
outer run is incomplete too), so this invariant is stated for completed runs: the transfer below
needs the per-body step only on completed outcomes. -/

/-- Invariant transfer from a per-body step required only on COMPLETED outcomes. -/
theorem invariant_transfer_completed (R : EvalState → EvalState → Prop) (hrefl : ∀ s, R s s)
    (hbody : ∀ rec : EvalRec, (∀ c, Preserves R (rec c)) → ∀ c s,
      ((evalStep rec c).runState s).1 ≠ .error .fuelExhausted → R s ((evalStep rec c).runState s).2) :
    ∀ n c s, Completes (evalFuel n c) s → R s ((evalFuel n c).runState s).2 := by
  intro n
  induction n with
  | zero => intro c s hc; exact absurd rfl hc
  | succ n ih =>
    intro c s hc
    have hpart : ∀ c, Preserves R (completedPart n c) := by
      intro c' s'
      by_cases hc' : Completes (evalFuel n c') s'
      · simp only [completedPart, if_pos hc']; exact ih c' s' hc'
      · simp only [completedPart, if_neg hc']; exact hrefl s'
    have hstep := evalStep_monotone _ _ (evalFuel_approx_completedPart n) c s
    have hne := (evalFuel_completes_iff (n + 1) c s).1 hc
    rw [evalFuel_succ] at hne ⊢
    by_cases hraw : ((evalStep (evalFuel n) c).runState s).1 = .error .fuelExhausted
    · rw [normalize_of_incomplete _ s hraw] at hne; exact absurd rfl hne
    · rw [normalize_of_complete _ s hraw]
      rcases hstep with hi | he
      · exfalso; apply hraw; unfold EvalM.IsIncompleteAt at hi; rw [hi]
      · rw [he]; rw [he] at hraw; exact hbody _ hpart c s hraw

/-- The owner set (`activeZeroArgProperties`) at exit is the one at entry. -/
def ActiveKept (s t : EvalState) : Prop := t.activeZeroArgProperties = s.activeZeroArgProperties

instance : StateRel ActiveKept := ⟨fun _ => rfl, fun h1 h2 => h2.trans h1⟩
instance : FieldFrame ActiveKept := ⟨fun _ _ _ ha => ha⟩


theorem active_property_step (rec : EvalRec) (hrec : ∀ c, Preserves ActiveKept (rec c))
    (accessKind : ZeroArgPropertyAccessKind) (owner : Algorithm) (binding : PropDef)
    (resolvedAlgorithm : Algorithm) (ctx : EvalCtx) (env : ValEnv) (request : ZeroArgPropertyRequest) (s : EvalState)
    (hne : ((EvalBody.evalZeroArgPropertyAccessCounted rec accessKind owner binding resolvedAlgorithm ctx env request).runState s).1
      ≠ .error .fuelExhausted) :
    ActiveKept s ((EvalBody.evalZeroArgPropertyAccessCounted rec accessKind owner binding resolvedAlgorithm ctx env request).runState s).2 := by
  -- Both requests share the one owner discipline: their calculation (a read's demand or an
  -- invocation's fresh call) keeps the owner set, and an owner restores the set it found.
  have hcalc := EvalBody.zeroArgPropertyCalculation_pres (R := ActiveKept) rec hrec request resolvedAlgorithm ctx env
  revert hne
  unfold EvalBody.evalZeroArgPropertyAccessCounted
  split
  · simp only [EvalM.bind_runState, get_runState]
    split
    · cases request with
      | read => intro _; rfl
      | invoke _ => intro _; exact hcalc s
    · split
      · intro _; exact hcalc s
      · simp only [EvalM.bind_runState, set_runState]
        generalize hz : (evalAttempt (EvalBody.zeroArgPropertyCalculation rec request resolvedAlgorithm ctx env)).runState _ = r
        obtain ⟨o, t2, hm, hc⟩ := evalAttempt_cases (EvalBody.zeroArgPropertyCalculation rec request resolvedAlgorithm ctx env)
          { s with activeZeroArgProperties := (zeroArgPropertyCacheKey accessKind owner binding ctx env (propertyOwnerBindingContext resolvedAlgorithm.parent s)) :: s.activeZeroArgProperties }
        have ha := hcalc { s with activeZeroArgProperties := (zeroArgPropertyCacheKey accessKind owner binding ctx env (propertyOwnerBindingContext resolvedAlgorithm.parent s)) :: s.activeZeroArgProperties }
        rw [hm] at ha
        rcases hc with ⟨hrun, _⟩ | ⟨hrun, _⟩
        · rw [hrun] at hz; subst hz
          intro h; exact absurd rfl h
        · rw [hrun] at hz; subst hz
          simp only [get_runState]
          cases o with
          | ok counted =>
            simp only [EvalM.bind_runState, set_runState, pure_runState]
            intro _; rfl
          | error err =>
            simp only [EvalM.bind_runState, set_runState, throw_runState]
            intro _; rfl
  · intro _; exact hcalc s


theorem active_body_step (rec : EvalRec) (hrec : ∀ c, Preserves ActiveKept (rec c)) (c : EvalCall)
    (s : EvalState) (hne : ((evalStep rec c).runState s).1 ≠ .error .fuelExhausted) :
    ActiveKept s ((evalStep rec c).runState s).2 := by
  cases h : isPropertyAccessCall c
  · exact evalStep_preserves_other rec hrec c h s
  · cases c <;> first
      | (exact active_property_step rec hrec _ _ _ _ _ _ _ s hne)
      | (simp [isPropertyAccessCall] at h)

/-- **Q-37 owner discipline, whole run (core):** every completed run of the total core — success or
    ordinary failure — leaves the active owner set exactly as it found it: an owning evaluation
    releases its key on both exits, and a reentrant read never adds one. -/
theorem owner_set_restored_core (n : Nat) (c : EvalCall) (s : EvalState)
    (hc : Completes (evalFuel n c) s) :
    ((evalFuel n c).runState s).2.activeZeroArgProperties = s.activeZeroArgProperties :=
  invariant_transfer_completed ActiveKept (fun _ => rfl) active_body_step n c s hc

/-- **Q-37 owner discipline, whole run (production):** every COMPLETED production operation leaves
    the active owner set as it found it. -/
theorem owner_set_restored (c : EvalCall) (s : EvalState)
    (hc : ProductionCompletes (evalUnbounded c) s) :
    ((evalUnbounded c).runState s).2.activeZeroArgProperties = s.activeZeroArgProperties := by
  obtain ⟨m, hr, hm⟩ := (production_completes_iff c s _).1 ⟨rfl, hc⟩
  rw [← hr]
  exact owner_set_restored_core m c s hm

/-- A public run starts with no owner, so every completed production operation from an
    ownerless state ends ownerless (the C# run's empty `activeZeroArgProperties` invariant). -/
theorem owner_set_empty_after (c : EvalCall) (s : EvalState) (hs : s.activeZeroArgProperties = [])
    (hc : ProductionCompletes (evalUnbounded c) s) :
    ((evalUnbounded c).runState s).2.activeZeroArgProperties = [] := by
  rw [owner_set_restored c s hc, hs]

end KatLang.EvaluatorCacheLaws
