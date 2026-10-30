import Lean
import KatLangArityLaws.EvaluatorCore
import KatLangArityLaws.ArgumentView

open KatLang KatLang.CallPlan KatLang.EvaluatorCore KatLang.CallReferenceLaws KatLang.ArgumentViewLaws

/-!
# R7: whole-run heap discipline of the production evaluator

`Disciplined m` (`KatLangArityLaws/InvocationPlan.lean`): `m` keeps every existing cell's
suspension, completed VALUE and prepared plan supply, over EVERY entry state. This module proves
that EVERY evaluator body is disciplined whenever its recursive answer is
(`evalStep_disciplined`, one theorem per body, `EvalBody.*_disciplined`), and transfers it through
`invariant_transfer` / `production_preserves`:

* `evalFuel_disciplined` — every completed run of the total core, at every fuel, from every state;
* `evalUnbounded_disciplined` — every production operation, unconditionally;
* `productionDiscipline_holds` — the M1.5 named obligation `ProductionDiscipline` IS A THEOREM in
  its original general form (all entry states, not only reachable ones), so `production_*'`
  restate the M1.5 production specializations without the hypothesis.

The per-body proofs are syntax-directed (`disc_tac`): the existing compositional lemmas of
`InvocationPlan` (shells, preparation, execution, invocation, reification, formation), framework
lemmas for reads followed by writes (`DiscAt`, `disc_get_bind`), loops (`forIn`/`forM`/`foldlM`),
and the recursive total helpers (by their own induction). Head-unfolding never unfolds a recursive
definition, and macro hygiene is off so the tactic reaches lemmas defined after it. (The D4 bare-cell
write and its hand proof were retired with D4 by M4★, ALIAS-UNIFY-1.)

Not claimed here: other heap invariants (address validity of environments, allocation order of
collector slices, acyclicity). Address validity and collector order for allocation, parameter
transport, supply formation and the binder are proved in `HeapAddressValidity.lean` (FG-H1) under
named evaluator premises (false over `StateValid`); their whole-run replacement is FG-H1-FU-01's
invariant `Inv` (`AddressInvariant*.lean`: every production operation keeps it, by the same
transfer shape over a per-body obligation `evalStep_sound`); acyclicity remains open. `CellKept` does
not constrain a cell's CALLABLE state, recorded callee or recorded receiver; their entry-state
preservation is the
companion relation `LinkKept` of `EvaluatorMemoLinks.lean` (FG-M1), proved by the same procedure
over `LinkDisc`.
-/

namespace KatLang.EvaluatorDiscipline

open Lean Meta Elab Tactic in
/-- Unfolds the head constant of the computation in a `Disciplined` goal (a total helper with
    no lemma of its own), so the syntax-directed procedure can continue inside it. -/
elab "disc_unfold_head" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let ty ← instantiateMVars (← goal.getType)
    let_expr KatLang.CallPlan.Disciplined _ m := ty | throwError "disc_unfold_head: not a discipline goal"
    let m := m.headBeta
    let some c := m.getAppFn.constName? | throwError "disc_unfold_head: no head constant"
    if c ∈ [``Bind.bind, ``Pure.pure, ``Functor.map, ``KatLang.evalAttempt, ``ForIn.forIn,
        ``MonadState.get, ``MonadStateOf.get, ``MonadState.set, ``MonadStateOf.set,
        ``MonadState.modifyGet, ``modify, ``get, ``set, ``List.forM, ``List.mapM, ``List.foldlM] then
      throwError "disc_unfold_head: combinator"
    let g' ← Lean.Meta.unfoldTarget goal c
    let ty' ← instantiateMVars (← g'.getType)
    if (ty'.find? (fun e => e.isConstOf c)).isSome then
      throwError "disc_unfold_head: recursive definition"
    replaceMainGoal [g']

open Lean Meta Elab Tactic in
/-- Closes `Disciplined (rec c)` from a hypothesis `∀ c, Disciplined (rec c)`. -/
elab "disc_rec" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let ty ← instantiateMVars (← goal.getType)
    let_expr KatLang.CallPlan.Disciplined _ m := ty | throwError "disc_rec: not a discipline goal"
    let m := m.headBeta
    unless m.isApp && m.appFn!.isFVar do throwError "disc_rec: not a recursive call"
    let f := m.appFn!
    for d in (← getLCtx) do
      unless d.isImplementationDetail do
        let t ← instantiateMVars d.type
        if t.isForall then
          let body := t.bindingBody!
          if let some (_, m') := body.app2? ``KatLang.CallPlan.Disciplined then
            if m'.isApp && m'.appFn! == f && m'.appArg! == .bvar 0 then
              goal.assign (mkApp d.toExpr m.appArg!)
              return
    throwError "disc_rec: no hypothesis"

open Lean Meta Elab Tactic in
/-- Closes a goal from a local hypothesis, instantiating its leading universal binders, at
    reducible transparency (cheap: never evaluates a computation). -/
elab "disc_hyp" : tactic => do
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
  unless ok do throwError "disc_hyp: no hypothesis"

open Lean Meta Elab Tactic in
/-- Zeta-reduces the top-level local definitions (`let`/`have`) of the computation in a
    `Disciplined`/`DiscAt` goal, and nothing else. -/
elab "disc_zeta" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let ty ← instantiateMVars (← goal.getType)
    let m := ty.appArg!
    let mut e := m
    let mut n := 0
    for _ in [0:10000] do
      match e with
      | Lean.Expr.letE _ _ v b _ => e := b.instantiate1 v; n := n + 1
      | Lean.Expr.mdata _ e' => e := e'
      | _ => break
    let m' := e
    if n == 0 then throwError "disc_zeta: no local definition"
    replaceMainGoal [← goal.replaceTargetDefEq (ty.updateApp! ty.appFn! m')]

open Lean Meta Elab Tactic in
/-- `intro` on a goal that is syntactically a binder (never unfolding a definition to find one). -/
elab "intro_syntactic" : tactic => do
  let goal ← getMainGoal
  unless (← instantiateMVars (← goal.getType)).isForall do throwError "intro_syntactic: no binder"
  let (_, g) ← goal.intro1
  replaceMainGoal [g]

open Lean Meta Elab Tactic in
/-- Closes an impossible branch: a hypothesis `∀ xs, a = b → False` whose equation holds by `rfl`
    for some instantiation. -/
elab "disc_absurd" : tactic => do
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
  unless ok do throwError "disc_absurd: no contradiction"

open Lean Meta Elab Tactic in
/-- Beta/projection/constructor-iota normal form (`whnfCore`, no definition unfolding) of the
    computation in a `Disciplined` goal. -/
elab "disc_whnf_core" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let ty ← instantiateMVars (← goal.getType)
    let_expr KatLang.CallPlan.Disciplined _ m := ty | throwError "disc_whnf_core: not a discipline goal"
    let m' ← whnfCore m
    if m' == m then throwError "disc_whnf_core: no progress"
    replaceMainGoal [← goal.replaceTargetDefEq (ty.updateApp! ty.appFn! m')]

/-- The evaluator helpers `rec.f args` are `rec (.f args)`. -/
macro "disc_unfold_rec" : tactic => `(tactic| dsimp (config := { proj := false }) only [EvalRec.whileLoop, EvalRec.aliasStepIsRuntime, EvalRec.aliasValue, EvalRec.resolveAliasChase, EvalRec.resolveAliasTarget, EvalRec.resolveAliasValueTarget, EvalRec.lookupLexicalProperty, EvalRec.lookupLexicalValueProperty, EvalRec.lookupLexical, EvalRec.needPlanNormalizeCallee, EvalRec.resolveAlg, EvalRec.projectNeedCallable, EvalRec.projectNeedWrittenAt, EvalRec.linkCallable, EvalRec.projectParameterCallable, EvalRec.projectNeedWritten, EvalRec.projectNeedStructuralMember, EvalRec.resolveCalleeAlg, EvalRec.expectPreparedSequenceBuiltinAlgorithmSuffixArg, EvalRec.resolveDotReceiver?, EvalRec.resolveDotReceiver, EvalRec.algorithmIntrinsicRoute, EvalRec.demandNeedRecursive, EvalRec.evalSuppliedAt, EvalRec.linkValue, EvalRec.algorithmOfValue, EvalRec.capturedCallee, EvalRec.referenceReceiverValue, EvalRec.algorithmCalleeOf, EvalRec.evalSuppliedCallCounted, EvalRec.evalNeedUserSupply, EvalRec.evalNeedFamilySupply, EvalRec.invokeNeed, EvalRec.argumentNeed, EvalRec.runNeedStepSlots, EvalRec.runNeedWhileRound, EvalRec.evalAlgOutputCore, EvalRec.evalAlgOutput, EvalRec.evalProgramOutput, EvalRec.evalAlgOutputSlots, EvalRec.formOutputRow, EvalRec.whileVerdictSlots, EvalRec.evalSequenceCallbackCall, EvalRec.evalSequenceCallbackCallCounted, EvalRec.evalAlgOutputPreparedCore, EvalRec.evalOutputRowsPreparedCore, EvalRec.evalCapturePreparedCore, EvalRec.evalCaptureCountedCore, EvalRec.evalCaptureValue, EvalRec.evalAlgOutputCountedCore, EvalRec.evalAlgOutputCounted, EvalRec.evalZeroArgumentDemandOutputCounted, EvalRec.evalZeroArgumentDemandOutput, EvalRec.evalArgumentValueCounted, EvalRec.evalArgumentValue, EvalRec.evalZeroArgPropertyAccessCounted, EvalRec.evalZeroArgPropertyAccess, EvalRec.evalConditionalCallbackCallCounted, EvalRec.evalUserCallbackCallCounted, EvalRec.evalResolvedCallbackCallCounted, EvalRec.evalResolvedCallbackCall, EvalRec.evalSequenceReduceStepCounted, EvalRec.demandSequenceBuiltinCallItemValue, EvalRec.bindSequenceBuiltinArguments, EvalRec.evalReduceCounted, EvalRec.evalFilterCounted, EvalRec.evalMapCounted, EvalRec.applyBuiltinCountedSequence, EvalRec.applyBuiltinCounted, EvalRec.applyBuiltin, EvalRec.applyBuiltinCountedResolved, EvalRec.evalExplicitSequenceValueItems, EvalRec.evalExplicitSequenceValueRowSlots, EvalRec.evalExplicitSequenceValueExprSlots, EvalRec.evalUserCallCounted, EvalRec.evalConditionalCallCounted, EvalRec.evalResolvedCall, EvalRec.evalResolvedCallCounted, EvalRec.evalCallCountedExpr, EvalRec.callLexicalWithReceiverCounted, EvalRec.rejectDotStringIntrinsicArguments, EvalRec.evalDotStringReceiverValue, EvalRec.evalDotCallCounted, EvalRec.rejectInvokeIntrinsicArguments, EvalRec.invokeCallReferenceValue, EvalRec.argumentViewCells, EvalRec.evalArgumentViewBuiltin, EvalRec.evalSequenceSpreadOperandValue, EvalRec.evalSequenceSpreadCounted, EvalRec.evalSupplySpread, EvalRec.evalListLiteralCounted, EvalRec.evalSequenceConstructCounted, EvalRec.evalUnaryCounted, EvalRec.evalBinaryCounted, EvalRec.evalComparisonCounted, EvalRec.evalComparisonLinksCounted, EvalRec.evalCounted, EvalRec.evalUserCall, EvalRec.evalConditionalCall, EvalRec.evalCallExpr, EvalRec.evalDotCall, EvalRec.eval, EvalRec.planRoute,
  EvalRec.bindingChannels, NeedChannels.shell, NeedChannels.capabilities] at *)

/-- A state write that keeps the heap is disciplined. -/
theorem disc_modify (f : EvalState → EvalState) (h : ∀ s, HeapKept s.needs (f s).needs) :
    Disciplined (modify f : EvalM Unit) := fun s => h s

theorem cellKept_of_same (c c' : NeedCell) (hs : c'.suspension = c.suspension)
    (hst : c'.state = c.state) (hp : c'.plan = c.plan) (hr : c'.route = c.route) : CellKept c c' :=
  ⟨hs, fun _ h => hst ▸ h, fun _ h => hp ▸ h, fun _ h => hr ▸ h⟩

/-! ## Reads, writes and loops -/

/-- `m` keeps the heap when run from the one state `st` (the state a preceding `get` read). -/
def DiscAt {α : Type} (st : EvalState) (m : EvalM α) : Prop := HeapKept st.needs (m.runState st).2.needs

theorem disc_get_bind {β : Type} (f : EvalState → EvalM β) (h : ∀ st, DiscAt st (f st)) :
    Disciplined (get >>= f) := by
  intro s
  rw [bind_run, get_run]
  exact h s

theorem DiscAt.of_disc {α : Type} {st : EvalState} {m : EvalM α} (h : Disciplined m) : DiscAt st m := h st

theorem DiscAt.bind {α β : Type} {st : EvalState} {m : EvalM α} {f : α → EvalM β}
    (hm : DiscAt st m) (hf : ∀ x, Disciplined (f x)) : DiscAt st (m >>= f) := by
  unfold DiscAt at *
  rw [bind_run]
  cases hr : m.runState st with
  | mk out t =>
    rw [hr] at hm
    cases out with
    | error e => exact hm
    | ok x => exact hm.trans (hf x t)

theorem DiscAt.set {st t : EvalState} (h : HeapKept st.needs t.needs) : DiscAt st (set t : EvalM PUnit) := h

theorem HeapKept.set_bang (h : Array NeedCell) (a : Nat) (c c' : NeedCell) (hc : h[a]? = some c)
    (hk : CellKept c c') : HeapKept h (h.set! a c') := by
  intro b d hd
  have ha : a < h.size := by
    rcases Nat.lt_or_ge a h.size with hl | hl
    · exact hl
    · rw [Array.getElem?_eq_none hl] at hc; cases hc
  by_cases hab : a = b
  · subst hab
    rw [hc] at hd; cases hd
    exact ⟨c', by simp [Array.set!, ha], hk⟩
  · exact ⟨d, by simp [Array.set!, hab, hd], CellKept.refl d⟩

theorem disc_forIn'_loop {α β : Type} (as : List α) (f : (a : α) → a ∈ as → β → EvalM (ForInStep β))
    (hf : ∀ a h b, Disciplined (f a h b)) :
    ∀ (as' : List α) (b : β) (h : ∃ bs, bs ++ as' = as), Disciplined (List.forIn'.loop as f as' b h)
  | [], b, h => by unfold List.forIn'.loop; exact disciplined_pure _
  | a :: as', b, h => by
    unfold List.forIn'.loop
    apply Disciplined.bind (hf _ _ _)
    intro r
    cases r with
    | done b => exact disciplined_pure _
    | yield b => exact disc_forIn'_loop as f hf as' b _

theorem disc_forIn {α β : Type} (xs : List α) (init : β) (f : α → β → EvalM (ForInStep β))
    (h : ∀ a b, Disciplined (f a b)) : Disciplined (forIn xs init f) :=
  disc_forIn'_loop xs (fun a _ b => f a b) (fun a _ b => h a b) xs init ⟨[], rfl⟩

theorem disc_forM {α : Type} (xs : List α) (f : α → EvalM PUnit)
    (h : ∀ a, Disciplined (f a)) : Disciplined (xs.forM f) := by
  induction xs with
  | nil => exact disciplined_pure _
  | cons x xs ih => unfold List.forM; exact Disciplined.bind (h x) (fun _ => ih)

theorem disc_foldlM {α β : Type} (f : β → α → EvalM β) (h : ∀ b a, Disciplined (f b a))
    (init : β) (xs : List α) : Disciplined (xs.foldlM f init) := by
  induction xs generalizing init with
  | nil => exact disciplined_pure _
  | cons x xs ih => unfold List.foldlM; exact Disciplined.bind (h _ _) (fun b => ih b)



set_option hygiene false in
/-- Syntax-directed heap discipline of an evaluator body, given that its recursive answer `hrec`
    is disciplined. -/
macro "disc_tac_base" : tactic => `(tactic| ((try disc_unfold_rec) <;> repeat' (first
  | disc_rec
  | disc_hyp
  | disc_absurd
  | (with_reducible apply disc_get_bind)
  | (with_reducible apply DiscAt.bind)
  | (with_reducible apply DiscAt.set; first
      | exact HeapKept.refl _
      | (apply HeapKept.set_bang <;> first | disc_hyp | (exact cellKept_of_same _ _ rfl rfl rfl rfl)))
  | (with_reducible apply Disciplined.withCtx)
  | (with_reducible apply Disciplined.captureMeta)
  | (with_reducible apply Disciplined.attempt)
  | (with_reducible apply Disciplined.map)
  | (with_reducible apply Disciplined.bind)
  | (with_reducible apply disciplined_pure)
  | (with_reducible apply disciplined_get)
  | (with_reducible apply disciplined_throw)
  | (with_reducible apply disciplined_evalError)
  | (with_reducible apply disciplined_lift)
  | (with_reducible apply disciplined_allocate)
  | (with_reducible apply disciplined_supply)
  | (with_reducible apply disciplined_mapM)
  | (with_reducible apply disciplined_form)
  | (with_reducible apply disciplined_slot)
  | (with_reducible apply disciplined_prepare)
  | (with_reducible apply disciplined_routeOf)
  | (with_reducible apply disciplined_calleeCell)
  | (with_reducible apply disciplined_execute)
  | (with_reducible apply disciplined_step)
  | (with_reducible apply disciplined_reify)
  | (with_reducible apply disciplined_invoke)
  | (with_reducible apply disciplined_reference)
  | (with_reducible apply disciplined_viewCells)
  | (with_reducible apply disc_modify; intro s; first
      | exact HeapKept.refl _
      | (apply HeapKept.modify; intro c _; exact cellKept_of_same _ _ rfl rfl rfl rfl))
  | (with_reducible apply disc_forIn)
  | (with_reducible apply disc_forM)
  | (with_reducible apply disc_foldlM)
  | (with_reducible apply CapsDisc.mk)

  | split
  | intro_syntactic
  | disc_zeta
  | disc_whnf_core
  | disc_unfold_head
  | (with_reducible apply DiscAt.of_disc))))

/-! ## Heap discipline of the recursive total helpers -/

theorem disc_formLeftToRight (form : Expr → EvalM (List Result)) (h : ∀ e, Disciplined (form e))
    (rows : List Expr) : Disciplined (OutputRows.formLeftToRight form rows) := by
  induction rows with
  | nil => unfold OutputRows.formLeftToRight; disc_tac_base
  | cons e rest ih => unfold OutputRows.formLeftToRight; disc_tac_base

theorem disc_discover (form : Expr → EvalM (List Result)) (h : ∀ e, Disciplined (form e))
    (rows : List Expr) : Disciplined (WhileRound.discover form rows) := by
  induction rows with
  | nil => unfold WhileRound.discover; disc_tac_base
  | cons e rest ih => unfold WhileRound.discover; disc_tac_base

theorem disc_selectWith {α : Type} (demand : α → EvalM Result) (h : ∀ a, Disciplined (demand a))
    (receiver : Result) (cells : List α) : Disciplined (selectWith demand receiver cells) := by
  induction cells with
  | nil => unfold selectWith; disc_tac_base
  | cons c rest ih => unfold selectWith; disc_tac_base

theorem disc_selectViewWith {α : Type} (demand : α → EvalM Result) (hd : ∀ a, Disciplined (demand a))
    (cellsOf : EvalM (List NeedSupply.Sourced)) (hc : Disciplined cellsOf)
    (demandCell : Nat → EvalM Result) (hdc : ∀ a, Disciplined (demandCell a)) (selectors : List α) :
    Disciplined (selectViewWith demand cellsOf demandCell selectors) := by
  induction selectors with
  | nil => unfold selectViewWith; disc_tac_base
  | cons c rest ih => unfold selectViewWith; disc_tac_base

theorem disc_interpolateWith (value : Expr → EvalM Result) (h : ∀ e, Disciplined (value e))
    (acc : String) (links : List InterpolationLink) :
    Disciplined (interpolateWith value acc links) := by
  induction links generalizing acc with
  | nil => unfold interpolateWith; disc_tac_base
  | cons l rest ih => unfold interpolateWith; disc_tac_base

/-- Capabilities whose every field is disciplined. -/
structure CapsDisc (caps : NeedCapabilities EvalM) : Prop where
  value : ∀ a, Disciplined (caps.value a)
  callable : ∀ a, Disciplined (caps.callable a)
  allocate : ∀ s, Disciplined (caps.allocate s)
  reference : ∀ a, Disciplined (caps.reference a)

/-- NEED-04's data-anchor check demands only through the VALUE capability. -/
theorem disc_checkAnchor (caps : NeedCapabilities EvalM) (hc : CapsDisc caps) (name : Ident)
    (anchor : CountedResult) (family : Bool) (cells : List Nat) :
    Disciplined (NeedBinder.checkAnchor caps name anchor family cells) := by
  have hv := hc.value
  induction cells with
  | nil => unfold NeedBinder.checkAnchor; disc_tac_base
  | cons c rest ih => unfold NeedBinder.checkAnchor; disc_tac_base

theorem disc_binder (caps : NeedCapabilities EvalM) (hc : CapsDisc caps) (repeated : List Ident)
    (family : Bool) :
    (∀ pattern address bound,
      Disciplined (NeedBinder.bindOne caps pattern address repeated bound family)) ∧
    (∀ patterns sources current,
      Disciplined (NeedBinder.bindSources caps patterns sources repeated current family)) := by
  have hv := hc.value; have hcl := hc.callable; have hal := hc.allocate; have hre := hc.reference
  have hck := disc_checkAnchor caps hc
  refine NeedBinder.bindOne.mutual_induct
    (motive_1 := fun pattern address bound =>
      Disciplined (NeedBinder.bindOne caps pattern address repeated bound family))
    (motive_2 := fun patterns sources current =>
      Disciplined (NeedBinder.bindSources caps patterns sources repeated current family))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals intros
  all_goals first
    | (simp only [NeedBinder.bindOne]; disc_tac_base)
    | (simp only [NeedBinder.bindSources]; disc_tac_base)

theorem disc_bindPatterns (caps : NeedCapabilities EvalM) (hc : CapsDisc caps)
    (patterns : List NeedPattern) (cells : List Nat) (family : Bool) :
    Disciplined (NeedBinder.bindPatterns caps patterns cells family) := by
  unfold NeedBinder.bindPatterns NeedBinder.bindLevel NeedBinder.cardinalityGate
  have := (disc_binder caps hc (needRepeatedNames patterns) family).2
  disc_tac_base

theorem disc_chooseBranch {β : Type} (caps : NeedCapabilities EvalM) (hc : CapsDisc caps)
    (cells : List Nat) (calleeName : String) (activate : CondBranch → NeedEnv → EvalM β)
    (ha : ∀ b e, Disciplined (activate b e)) (branches : List CondBranch) :
    Disciplined (NeedBinder.chooseBranch caps cells calleeName activate branches) := by
  induction branches with
  | nil => unfold NeedBinder.chooseBranch; disc_tac_base
  | cons b rest ih =>
    unfold NeedBinder.chooseBranch
    have := fun ps fam => disc_bindPatterns caps hc ps cells fam
    disc_tac_base

theorem disc_selectFamily {β : Type} (caps : NeedCapabilities EvalM) (hc : CapsDisc caps)
    (callee : Algorithm) (cells : List Nat) (calleeName : String)
    (activate : CondBranch → NeedEnv → EvalM β) (ha : ∀ b e, Disciplined (activate b e)) :
    Disciplined (NeedBinder.selectFamily caps callee cells calleeName activate) := by
  unfold NeedBinder.selectFamily
  have := disc_chooseBranch caps hc cells calleeName activate ha
  disc_tac_base


theorem disc_collectSingleAtomicNumbers (b : Builtin) (index : Nat) (items : List Result) :
    Disciplined (collectSingleAtomicNumbers b index items) := by
  induction items generalizing index with
  | nil => unfold collectSingleAtomicNumbers; disc_tac_base
  | cons i rest ih => unfold collectSingleAtomicNumbers; disc_tac_base

theorem disc_minLoop (numbers : List Int) (current : Int) :
    Disciplined (evalMinCounted.minLoop numbers current) := by
  induction numbers generalizing current with
  | nil => unfold evalMinCounted.minLoop; disc_tac_base
  | cons n rest ih => unfold evalMinCounted.minLoop; disc_tac_base

theorem disc_maxLoop (numbers : List Int) (current : Int) :
    Disciplined (evalMaxCounted.maxLoop numbers current) := by
  induction numbers generalizing current with
  | nil => unfold evalMaxCounted.maxLoop; disc_tac_base
  | cons n rest ih => unfold evalMaxCounted.maxLoop; disc_tac_base

theorem disc_openNavigateWith (structureOf : Algorithm → EvalM Algorithm)
    (h : ∀ a, Disciplined (structureOf a)) (ctx : EvalCtx) (notStatic : Error)
    (value : Algorithm) (receiverName : String) (steps : List Ident) :
    Disciplined (openNavigateWith structureOf ctx notStatic value receiverName steps) := by
  induction steps generalizing value receiverName with
  | nil => unfold openNavigateWith; disc_tac_base
  | cons member rest ih => unfold openNavigateWith; disc_tac_base

theorem disc_openStructure (fuel : Nat) (ctx : EvalCtx) (a : Algorithm) :
    Disciplined (openStructure fuel ctx a) := by
  induction fuel generalizing a with
  | zero => simp only [openStructure]; disc_tac_base
  | succ n ih =>
    have := disc_openNavigateWith (fun value => openStructure n ctx value) ih
    simp only [openStructure]; disc_tac_base

theorem disc_resolveAlgForOpen (ctx : EvalCtx) (e : Expr) : Disciplined (resolveAlgForOpen e ctx) := by
  have := disc_openStructure
  induction e using resolveAlgForOpen.induct ctx with
  | case7 o n a ih => unfold resolveAlgForOpen; disc_tac_base
  | _ => unfold resolveAlgForOpen; disc_tac_base

theorem disc_lookupOpenProperties (a : Algorithm) (name : Ident) (ctx : EvalCtx) :
    Disciplined (lookupOpenProperties a name ctx) := by
  have := disc_resolveAlgForOpen
  have := disc_openStructure
  unfold lookupOpenProperties; disc_tac_base

theorem disc_lookupOpenPropertiesInParentChain (name : Ident) (ctx : EvalCtx) (sc : ScopeCtx) :
    Disciplined (lookupOpenPropertiesInParentChain sc name ctx) := by
  induction sc using lookupOpenPropertiesInParentChain.induct with
  | _ t ih =>
    have := disc_lookupOpenProperties
    unfold lookupOpenPropertiesInParentChain
    cases t with
    | mk parent _ _ _ _ _ _ _ => cases parent <;> disc_tac_base

theorem disc_aliasStepNavigateWith (structureOf : Algorithm → EvalCtx → EvalM (Option Algorithm))
    (h : ∀ a c, Disciplined (structureOf a c)) (stepCtx : EvalCtx) (notStatic : Error)
    (value : Algorithm) (last : Option ResolvedProperty) (receiverName : String) (steps : List Ident) :
    Disciplined (aliasStepNavigateWith structureOf stepCtx notStatic value last receiverName steps) := by
  induction steps generalizing value last receiverName with
  | nil => unfold aliasStepNavigateWith; disc_tac_base
  | cons member rest ih => unfold aliasStepNavigateWith; disc_tac_base

theorem disc_resolveAliasStepWith (structureOf : Algorithm → EvalCtx → EvalM (Option Algorithm))
    (h : ∀ a c, Disciplined (structureOf a c)) (step : Algorithm) (target : Expr) (ctx : EvalCtx) :
    Disciplined (resolveAliasStepWith structureOf step target ctx) := by
  have := disc_aliasStepNavigateWith structureOf h
  have := disc_lookupOpenProperties
  have := disc_lookupOpenPropertiesInParentChain
  unfold resolveAliasStepWith; disc_tac_base

theorem disc_aliasRouteIsIntrinsicWith (structureOf : Algorithm → EvalCtx → EvalM (Option Algorithm))
    (h : ∀ a c, Disciplined (structureOf a c)) (receiver : Expr) (ctx : EvalCtx) :
    Disciplined (aliasRouteIsIntrinsicWith structureOf receiver ctx) := by
  have := disc_aliasStepNavigateWith structureOf h
  have := disc_lookupOpenProperties
  have := disc_lookupOpenPropertiesInParentChain
  unfold aliasRouteIsIntrinsicWith; disc_tac_base

section LocalLoops
variable (rec : EvalRec) (hrec : ∀ c, Disciplined (rec c))
include hrec

theorem disc_outputRowsCollect (rowCtx : EvalCtx) (env : ValEnv) (rows : List Expr)
    (acc : List Result) (emitted : Nat) :
    Disciplined (EvalBody.evalOutputRowsPreparedCore.collect rec rowCtx env rows acc emitted) := by
  induction rows generalizing acc emitted with
  | nil => unfold EvalBody.evalOutputRowsPreparedCore.collect; disc_tac_base
  | cons e rest ih => unfold EvalBody.evalOutputRowsPreparedCore.collect; disc_tac_base

theorem disc_explicitRowsCollect (rowCtx : EvalCtx) (env : ValEnv) (rows : List Expr) (acc : List Result) :
    Disciplined (EvalBody.evalExplicitSequenceValueRowSlots.collect rec rowCtx env rows acc) := by
  induction rows generalizing acc with
  | nil => unfold EvalBody.evalExplicitSequenceValueRowSlots.collect; disc_tac_base
  | cons e rest ih => unfold EvalBody.evalExplicitSequenceValueRowSlots.collect; disc_tac_base

theorem disc_listLiteralCollect (ctx : EvalCtx) (env : ValEnv) (elements : List Expr) (acc : List Result) :
    Disciplined (EvalBody.evalListLiteralCounted.collect rec ctx env elements acc) := by
  induction elements generalizing acc with
  | nil => unfold EvalBody.evalListLiteralCounted.collect; disc_tac_base
  | cons e rest ih => unfold EvalBody.evalListLiteralCounted.collect; disc_tac_base

theorem disc_sequenceConstructLoop (ctx : EvalCtx) (env : ValEnv) (leaves : List Expr) (items : List Result) :
    Disciplined (EvalBody.evalSequenceConstructCounted.loop rec ctx env leaves items) := by
  induction leaves generalizing items with
  | nil => unfold EvalBody.evalSequenceConstructCounted.loop; disc_tac_base
  | cons e rest ih => unfold EvalBody.evalSequenceConstructCounted.loop; disc_tac_base

theorem disc_prepareControls (b : Builtin) (ctx : EvalCtx) (env : ValEnv)
    (descriptors : List SequenceBuiltinSuffixArgDescriptor) (items : List CallableCallItem) :
    Disciplined (EvalBody.bindSequenceBuiltinArguments.prepareControls rec b ctx env descriptors items) := by
  induction descriptors generalizing items with
  | nil => cases items <;> (unfold EvalBody.bindSequenceBuiltinArguments.prepareControls; disc_tac_base)
  | cons d rest ih => cases items <;> (unfold EvalBody.bindSequenceBuiltinArguments.prepareControls; disc_tac_base)

theorem disc_reduceLoop (stepAlg : Algorithm) (ctx : EvalCtx) (env : ValEnv)
    (items : List CountedResult) (acc : CountedResult) :
    Disciplined (EvalBody.evalReduceCounted.reduceLoop rec stepAlg ctx env items acc) := by
  induction items generalizing acc with
  | nil => unfold EvalBody.evalReduceCounted.reduceLoop; disc_tac_base
  | cons i rest ih => unfold EvalBody.evalReduceCounted.reduceLoop; disc_tac_base

theorem disc_filterLoop (predicateAlg : Algorithm) (ctx : EvalCtx) (env : ValEnv)
    (index : Nat) (items : List CountedResult) :
    Disciplined (EvalBody.evalFilterCounted.filterLoop rec predicateAlg ctx env index items) := by
  induction items generalizing index with
  | nil => unfold EvalBody.evalFilterCounted.filterLoop; disc_tac_base
  | cons i rest ih => unfold EvalBody.evalFilterCounted.filterLoop; disc_tac_base

theorem disc_mapLoop (transformAlg : Algorithm) (ctx : EvalCtx) (env : ValEnv) (items : List CountedResult) :
    Disciplined (EvalBody.evalMapCounted.mapLoop rec transformAlg ctx env items) := by
  induction items with
  | nil => unfold EvalBody.evalMapCounted.mapLoop; disc_tac_base
  | cons i rest ih => unfold EvalBody.evalMapCounted.mapLoop; disc_tac_base

theorem disc_repeatLoop (ctx : EvalCtx) (env : ValEnv) (step : ResolvedArgumentAlgorithm)
    (stepName : String) (remaining : Nat) (cells : List Nat) :
    Disciplined (EvalBody.applyBuiltinCounted.repeatLoop rec ctx env step stepName remaining cells) := by
  induction remaining generalizing cells with
  | zero => unfold EvalBody.applyBuiltinCounted.repeatLoop; disc_tac_base
  | succ k ih => unfold EvalBody.applyBuiltinCounted.repeatLoop; disc_tac_base

end LocalLoops


/-! ### Pushing writers keep every existing cell

`bindParameters`, `recordParameterActivation`, `enterAlgorithmBody` and the supplier never change an
existing cell (they only push one). -/

theorem needs_bindParameters (names : List Ident) (ctx : EvalCtx) (s : EvalState) :
    ((EvalCtx.bindParameters names ctx).runState s).2.needs = s.needs := rfl

theorem needs_recordParameterActivation (names : List Ident) (ctx : EvalCtx) (env : ValEnv)
    (s : EvalState) : ((recordParameterActivation names ctx env).runState s).2.needs = s.needs := rfl

theorem needs_enterAlgorithmBody (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) (s : EvalState) :
    ((enterAlgorithmBody a ctx env).runState s).2.needs = s.needs := by
  unfold enterAlgorithmBody
  split
  · rfl
  · rw [bind_run]; rfl

/-- The supplier only ever pushes: every existing cell is kept exactly. -/
theorem supply_keeps_cells (source : Expr) (caller : EvalCtx) (values : ValEnv) (s : EvalState)
    (a : Nat) (c : NeedCell) (h : s.needs[a]? = some c) :
    ((supplyNeed source caller values).runState s).2.needs[a]? = some c := by
  rcases supply_cases source caller values s with e | e
  · rw [e]; exact h
  · rw [e]
    have ha : a < s.needs.size := by
      rcases Nat.lt_or_ge a s.needs.size with hl | hl
      · exact hl
      · rw [Array.getElem?_eq_none hl] at h; cases h
    show (s.needs.push _)[a]? = some c
    rw [Array.getElem?_push]; simp [Nat.ne_of_lt ha, h]

set_option hygiene false in
/-- Syntax-directed heap discipline of an evaluator body, given that its recursive answer `hrec`
    is disciplined. -/
macro "disc_tac" : tactic => `(tactic| ((try disc_unfold_rec) <;> repeat' (first
  | disc_rec
  | disc_hyp
  | disc_absurd
  | (with_reducible apply disc_get_bind)
  | (with_reducible apply DiscAt.bind)
  | (with_reducible apply DiscAt.set; first
      | exact HeapKept.refl _
      | (apply HeapKept.set_bang <;> first | disc_hyp | (exact cellKept_of_same _ _ rfl rfl rfl rfl)))
  | (with_reducible apply Disciplined.withCtx)
  | (with_reducible apply Disciplined.captureMeta)
  | (with_reducible apply Disciplined.attempt)
  | (with_reducible apply Disciplined.map)
  | (with_reducible apply Disciplined.bind)
  | (with_reducible apply disciplined_pure)
  | (with_reducible apply disciplined_get)
  | (with_reducible apply disciplined_throw)
  | (with_reducible apply disciplined_evalError)
  | (with_reducible apply disciplined_lift)
  | (with_reducible apply disciplined_allocate)
  | (with_reducible apply disciplined_supply)
  | (with_reducible apply disciplined_mapM)
  | (with_reducible apply disciplined_form)
  | (with_reducible apply disciplined_slot)
  | (with_reducible apply disciplined_prepare)
  | (with_reducible apply disciplined_routeOf)
  | (with_reducible apply disciplined_calleeCell)
  | (with_reducible apply disciplined_execute)
  | (with_reducible apply disciplined_step)
  | (with_reducible apply disciplined_reify)
  | (with_reducible apply disciplined_invoke)
  | (with_reducible apply disciplined_reference)
  | (with_reducible apply disciplined_viewCells)
  | (with_reducible apply disc_modify; intro s; first
      | exact HeapKept.refl _
      | (apply HeapKept.modify; intro c _; exact cellKept_of_same _ _ rfl rfl rfl rfl))
  | (with_reducible apply disc_forIn)
  | (with_reducible apply disc_forM)
  | (with_reducible apply disc_foldlM)
  | (with_reducible apply disc_formLeftToRight)
  | (with_reducible apply disc_discover)
  | (with_reducible apply disc_selectWith)
  | (with_reducible apply disc_selectViewWith)
  | (with_reducible apply disc_interpolateWith)
  | (with_reducible apply disc_bindPatterns)
  | (with_reducible apply disc_selectFamily)
  | (with_reducible apply disc_collectSingleAtomicNumbers)
  | (with_reducible apply disc_minLoop)
  | (with_reducible apply disc_maxLoop)
  | (with_reducible apply disc_resolveAlgForOpen)
  | (with_reducible apply disc_openStructure)
  | (with_reducible apply disc_resolveAliasStepWith)
  | (with_reducible apply disc_aliasRouteIsIntrinsicWith)
  | (with_reducible apply disc_lookupOpenProperties)
  | (with_reducible apply disc_lookupOpenPropertiesInParentChain)
  | (with_reducible apply EvalBody.terminalAccess_disciplined rec hrec)
  | (with_reducible apply disc_outputRowsCollect rec hrec)
  | (with_reducible apply disc_explicitRowsCollect rec hrec)
  | (with_reducible apply disc_listLiteralCollect rec hrec)
  | (with_reducible apply disc_sequenceConstructLoop rec hrec)
  | (with_reducible apply disc_prepareControls rec hrec)
  | (with_reducible apply disc_reduceLoop rec hrec)
  | (with_reducible apply disc_filterLoop rec hrec)
  | (with_reducible apply disc_mapLoop rec hrec)
  | (with_reducible apply disc_repeatLoop rec hrec)
  | (with_reducible apply CapsDisc.mk)

  | split
  | intro_syntactic
  | disc_zeta
  | disc_whnf_core
  | disc_unfold_head
  | (with_reducible apply DiscAt.of_disc))))

theorem EvalBody.whileLoop_disciplined (rec : EvalRec) (hrec : ∀ c, Disciplined (rec c)) (step : ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) (stepName : String) (cells : List Nat) :
    Disciplined (EvalBody.whileLoop rec step ctx env stepName cells) := by
  unfold EvalBody.whileLoop; disc_tac

theorem EvalBody.aliasStepIsRuntime_disciplined (rec : EvalRec) (hrec : ∀ c, Disciplined (rec c)) (step : Algorithm) (target : Expr) (ctx : EvalCtx) (visited : List String) :
    Disciplined (EvalBody.aliasStepIsRuntime rec step target ctx visited) := by
  unfold EvalBody.aliasStepIsRuntime; disc_tac

theorem EvalBody.aliasValue_disciplined (rec : EvalRec) (hrec : ∀ c, Disciplined (rec c)) (wired : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    Disciplined (EvalBody.aliasValue rec wired ctx env) := by
  unfold EvalBody.aliasValue; disc_tac

theorem EvalBody.resolveAliasChase_disciplined (rec : EvalRec) (hrec : ∀ c, Disciplined (rec c)) (followCarriers projectRuntime : Bool) (a : Algorithm) (ctx : EvalCtx) (visited : List String) (last : Option (Algorithm × PropDef)) :
    Disciplined (EvalBody.resolveAliasChase rec followCarriers projectRuntime a ctx visited last) := by
  unfold EvalBody.resolveAliasChase; disc_tac

theorem EvalBody.resolveAliasTarget_disciplined (rec : EvalRec) (hrec : ∀ c, Disciplined (rec c)) (a : Algorithm) (ctx : EvalCtx) :
    Disciplined (EvalBody.resolveAliasTarget rec a ctx) := by
  unfold EvalBody.resolveAliasTarget; disc_tac

theorem EvalBody.resolveAliasStructure_disciplined (rec : EvalRec) (hrec : ∀ c, Disciplined (rec c)) (a : Algorithm) (ctx : EvalCtx) :
    Disciplined (EvalBody.resolveAliasStructure rec a ctx) := by
  unfold EvalBody.resolveAliasStructure; disc_tac

theorem EvalBody.aliasOriginBinding?_disciplined (rec : EvalRec) (hrec : ∀ c, Disciplined (rec c)) (a : Algorithm) (ctx : EvalCtx) :
    Disciplined (EvalBody.aliasOriginBinding? rec a ctx) := by
  unfold EvalBody.aliasOriginBinding?; disc_tac

theorem EvalBody.resolveAliasValueTarget_disciplined (rec : EvalRec) (hrec : ∀ c, Disciplined (rec c)) (a : Algorithm) (ctx : EvalCtx) :
    Disciplined (EvalBody.resolveAliasValueTarget rec a ctx) := by
  unfold EvalBody.resolveAliasValueTarget; disc_tac

theorem EvalBody.lookupLexicalProperty_disciplined (rec : EvalRec) (hrec : ∀ c, Disciplined (rec c)) (a : Algorithm) (name : Ident) (ctx : EvalCtx) :
    Disciplined (EvalBody.lookupLexicalProperty rec a name ctx) := by
  unfold EvalBody.lookupLexicalProperty; disc_tac

theorem EvalBody.lookupLexicalValueProperty_disciplined (rec : EvalRec) (hrec : ∀ c, Disciplined (rec c)) (a : Algorithm) (name : Ident) (ctx : EvalCtx) :
    Disciplined (EvalBody.lookupLexicalValueProperty rec a name ctx) := by
  unfold EvalBody.lookupLexicalValueProperty; disc_tac

theorem EvalBody.lookupLexical_disciplined (rec : EvalRec) (hrec : ∀ c, Disciplined (rec c)) (a : Algorithm) (name : Ident) (ctx : EvalCtx) :
    Disciplined (EvalBody.lookupLexical rec a name ctx) := by
  unfold EvalBody.lookupLexical; disc_tac

theorem EvalBody.needPlanNormalizeCallee_disciplined (rec : EvalRec) (hrec : ∀ c, Disciplined (rec c)) (callee : Algorithm) (ctx : EvalCtx) :
    Disciplined (EvalBody.needPlanNormalizeCallee rec callee ctx) := by
  unfold EvalBody.needPlanNormalizeCallee; disc_tac

theorem EvalBody.resolveAlg_disciplined (rec : EvalRec) (hrec : ∀ c, Disciplined (rec c)) (e : Expr) (ctx : EvalCtx) :
    Disciplined (EvalBody.resolveAlg rec e ctx) := by
  unfold EvalBody.resolveAlg; disc_tac

theorem EvalBody.projectNeedCallable_disciplined (rec : EvalRec) (hrec : ∀ c, Disciplined (rec c)) (address : Nat) :
    Disciplined (EvalBody.projectNeedCallable rec address) := by
  unfold EvalBody.projectNeedCallable; disc_tac

theorem EvalBody.projectNeedWrittenAt_disciplined (rec : EvalRec) (hrec : ∀ c, Disciplined (rec c)) (address : Nat) (source : Expr) (caller : EvalCtx) :
    Disciplined (EvalBody.projectNeedWrittenAt rec address source caller) := by
  unfold EvalBody.projectNeedWrittenAt; disc_tac

theorem EvalBody.linkCallable_disciplined (rec : EvalRec) (hrec : ∀ c, Disciplined (rec c)) (address : Nat) :
    Disciplined (EvalBody.linkCallable rec address) := by
  unfold EvalBody.linkCallable; disc_tac

theorem EvalBody.projectParameterCallable_disciplined (rec : EvalRec) (hrec : ∀ c, Disciplined (rec c)) (x : Ident) (ctx : EvalCtx) :
    Disciplined (EvalBody.projectParameterCallable rec x ctx) := by
  unfold EvalBody.projectParameterCallable; disc_tac

theorem EvalBody.projectNeedWritten_disciplined (rec : EvalRec) (hrec : ∀ c, Disciplined (rec c)) (source : Expr) (caller : EvalCtx) :
    Disciplined (EvalBody.projectNeedWritten rec source caller) := by
  unfold EvalBody.projectNeedWritten; disc_tac

theorem EvalBody.projectNeedStructuralMember_disciplined (rec : EvalRec) (hrec : ∀ c, Disciplined (rec c)) (source : Expr) (ctx : EvalCtx) :
    Disciplined (EvalBody.projectNeedStructuralMember rec source ctx) := by
  unfold EvalBody.projectNeedStructuralMember; disc_tac

theorem EvalBody.resolveCalleeAlg_disciplined (rec : EvalRec) (hrec : ∀ c, Disciplined (rec c)) (f : Expr) (ctx : EvalCtx) :
    Disciplined (EvalBody.resolveCalleeAlg rec f ctx) := by
  unfold EvalBody.resolveCalleeAlg; disc_tac

theorem EvalBody.expectPreparedSequenceBuiltinAlgorithmSuffixArg_disciplined (rec : EvalRec) (hrec : ∀ c, Disciplined (rec c)) (b : Builtin) (descriptors : List SequenceBuiltinSuffixArgDescriptor) (args : List PreparedSequenceBuiltinSuffixArg) (index : Nat) :
    Disciplined (EvalBody.expectPreparedSequenceBuiltinAlgorithmSuffixArg rec b descriptors args index) := by
  unfold EvalBody.expectPreparedSequenceBuiltinAlgorithmSuffixArg; disc_tac

theorem EvalBody.resolveDotReceiver?_disciplined (rec : EvalRec) (hrec : ∀ c, Disciplined (rec c)) (e : Expr) (ctx : EvalCtx) :
    Disciplined (EvalBody.resolveDotReceiver? rec e ctx) := by
  unfold EvalBody.resolveDotReceiver?; disc_tac

theorem EvalBody.resolveDotReceiver_disciplined (rec : EvalRec) (hrec : ∀ c, Disciplined (rec c)) (e : Expr) (ctx : EvalCtx) :
    Disciplined (EvalBody.resolveDotReceiver rec e ctx) := by
  unfold EvalBody.resolveDotReceiver; disc_tac

theorem EvalBody.algorithmIntrinsicRoute_disciplined (rec : EvalRec) (hrec : ∀ c, Disciplined (rec c)) (receiver : Expr) (ctx : EvalCtx) :
    Disciplined (EvalBody.algorithmIntrinsicRoute rec receiver ctx) := by
  unfold EvalBody.algorithmIntrinsicRoute; disc_tac

theorem EvalBody.demandNeedRecursive_disciplined (rec : EvalRec) (hrec : ∀ c, Disciplined (rec c)) (address : Nat) :
    Disciplined (EvalBody.demandNeedRecursive rec address) := by
  unfold EvalBody.demandNeedRecursive; disc_tac

theorem EvalBody.evalSuppliedAt_disciplined (rec : EvalRec) (hrec : ∀ c, Disciplined (rec c)) (address : Nat) (e : Expr) (ctx : EvalCtx) (env : ValEnv) :
    Disciplined (EvalBody.evalSuppliedAt rec address e ctx env) := by
  unfold EvalBody.evalSuppliedAt; disc_tac

theorem EvalBody.linkValue_disciplined (rec : EvalRec) (hrec : ∀ c, Disciplined (rec c)) (address : Nat) :
    Disciplined (EvalBody.linkValue rec address) := by
  unfold EvalBody.linkValue; disc_tac

theorem EvalBody.algorithmOfValue_disciplined (rec : EvalRec) (hrec : ∀ c, Disciplined (rec c)) (val : Result) (argsOpt : Option OutputBundle) (ctx : EvalCtx) (env : ValEnv) :
    Disciplined (EvalBody.algorithmOfValue rec val argsOpt ctx env) := by
  unfold EvalBody.algorithmOfValue; disc_tac

theorem EvalBody.capturedCallee_disciplined (rec : EvalRec) (hrec : ∀ c, Disciplined (rec c)) (callee : Nat) :
    Disciplined (EvalBody.capturedCallee rec callee) := by
  unfold EvalBody.capturedCallee; disc_tac

theorem EvalBody.referenceReceiverValue_disciplined (rec : EvalRec) (hrec : ∀ c, Disciplined (rec c)) (target : Expr) (targetAlg : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    Disciplined (EvalBody.referenceReceiverValue rec target targetAlg ctx env) := by
  unfold EvalBody.referenceReceiverValue; disc_tac

theorem EvalBody.algorithmCalleeOf_disciplined (rec : EvalRec) (hrec : ∀ c, Disciplined (rec c)) (receiver : Expr) (ctx : EvalCtx) (env : ValEnv) :
    Disciplined (EvalBody.algorithmCalleeOf rec receiver ctx env) := by
  unfold EvalBody.algorithmCalleeOf; disc_tac

theorem EvalBody.evalSuppliedCallCounted_disciplined (rec : EvalRec) (hrec : ∀ c, Disciplined (rec c)) (origin : CalleeOrigin) (callee : Algorithm) (cells : List NeedSupply.Sourced) (ctx : EvalCtx) (env : ValEnv) (calleeName : String) :
    Disciplined (EvalBody.evalSuppliedCallCounted rec origin callee cells ctx env calleeName) := by
  unfold EvalBody.evalSuppliedCallCounted; disc_tac

theorem EvalBody.evalNeedUserSupply_disciplined (rec : EvalRec) (hrec : ∀ c, Disciplined (rec c)) (callee : Algorithm) (cells : List Nat) (ctx : EvalCtx) (env : ValEnv) :
    Disciplined (EvalBody.evalNeedUserSupply rec callee cells ctx env) := by
  unfold EvalBody.evalNeedUserSupply; disc_tac

theorem EvalBody.evalNeedFamilySupply_disciplined (rec : EvalRec) (hrec : ∀ c, Disciplined (rec c)) (callee : Algorithm) (cells : List Nat) (ctx : EvalCtx) (env : ValEnv) (calleeName : String) :
    Disciplined (EvalBody.evalNeedFamilySupply rec callee cells ctx env calleeName) := by
  unfold EvalBody.evalNeedFamilySupply; disc_tac

theorem EvalBody.invokeNeed_disciplined (rec : EvalRec) (hrec : ∀ c, Disciplined (rec c)) (arg : ResolvedArgumentAlgorithm) :
    Disciplined (EvalBody.invokeNeed rec arg) := by
  unfold EvalBody.invokeNeed; disc_tac

theorem EvalBody.argumentNeed_disciplined (rec : EvalRec) (hrec : ∀ c, Disciplined (rec c)) (arg : ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) :
    Disciplined (EvalBody.argumentNeed rec arg ctx env) := by
  unfold EvalBody.argumentNeed; disc_tac

theorem EvalBody.runNeedStepSlots_disciplined (rec : EvalRec) (hrec : ∀ c, Disciplined (rec c)) (step : Algorithm) (ctx : EvalCtx) (env : ValEnv) (cells : List Nat) (stepName : String) :
    Disciplined (EvalBody.runNeedStepSlots rec step ctx env cells stepName) := by
  unfold EvalBody.runNeedStepSlots EvalBody.runNeedStepWith; disc_tac

theorem EvalBody.runNeedWhileRound_disciplined (rec : EvalRec) (hrec : ∀ c, Disciplined (rec c)) (step : Algorithm) (ctx : EvalCtx) (env : ValEnv) (cells : List Nat) (stepName : String) :
    Disciplined (EvalBody.runNeedWhileRound rec step ctx env cells stepName) := by
  unfold EvalBody.runNeedWhileRound EvalBody.runNeedStepWith; disc_tac

theorem EvalBody.evalAlgOutputCore_disciplined (rec : EvalRec) (hrec : ∀ c, Disciplined (rec c)) (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    Disciplined (EvalBody.evalAlgOutputCore rec a ctx env) := by
  unfold EvalBody.evalAlgOutputCore; disc_tac

theorem EvalBody.evalAlgOutput_disciplined (rec : EvalRec) (hrec : ∀ c, Disciplined (rec c)) (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    Disciplined (EvalBody.evalAlgOutput rec a ctx env) := by
  unfold EvalBody.evalAlgOutput; disc_tac

theorem EvalBody.evalProgramOutput_disciplined (rec : EvalRec) (hrec : ∀ c, Disciplined (rec c)) (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    Disciplined (EvalBody.evalProgramOutput rec a ctx env) := by
  unfold EvalBody.evalProgramOutput; disc_tac

theorem EvalBody.evalAlgOutputSlots_disciplined (rec : EvalRec) (hrec : ∀ c, Disciplined (rec c)) (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    Disciplined (EvalBody.evalAlgOutputSlots rec a ctx env) := by
  unfold EvalBody.evalAlgOutputSlots ActivatedBody.readRows; disc_tac

theorem EvalBody.formOutputRow_disciplined (rec : EvalRec) (hrec : ∀ c, Disciplined (rec c)) (ctx : EvalCtx) (env : ValEnv) (e : Expr) :
    Disciplined (EvalBody.formOutputRow rec ctx env e) := by
  unfold EvalBody.formOutputRow; disc_tac

theorem EvalBody.whileVerdictSlots_disciplined (rec : EvalRec) (hrec : ∀ c, Disciplined (rec c)) (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    Disciplined (EvalBody.whileVerdictSlots rec a ctx env) := by
  unfold EvalBody.whileVerdictSlots ActivatedBody.readRows; disc_tac

theorem EvalBody.evalSequenceCallbackCall_disciplined (rec : EvalRec) (hrec : ∀ c, Disciplined (rec c)) (callee : Algorithm) (item : CountedResult) (ctx : EvalCtx) (env : ValEnv) (calleeName : String) :
    Disciplined (EvalBody.evalSequenceCallbackCall rec callee item ctx env calleeName) := by
  unfold EvalBody.evalSequenceCallbackCall; disc_tac

theorem EvalBody.evalSequenceCallbackCallCounted_disciplined (rec : EvalRec) (hrec : ∀ c, Disciplined (rec c)) (callee : Algorithm) (item : CountedResult) (ctx : EvalCtx) (env : ValEnv) (calleeName : String) :
    Disciplined (EvalBody.evalSequenceCallbackCallCounted rec callee item ctx env calleeName) := by
  unfold EvalBody.evalSequenceCallbackCallCounted; disc_tac

theorem EvalBody.evalAlgOutputPreparedCore_disciplined (rec : EvalRec) (hrec : ∀ c, Disciplined (rec c)) (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    Disciplined (EvalBody.evalAlgOutputPreparedCore rec a ctx env) := by
  unfold EvalBody.evalAlgOutputPreparedCore; disc_tac

theorem EvalBody.evalOutputRowsPreparedCore_disciplined (rec : EvalRec) (hrec : ∀ c, Disciplined (rec c)) (rows : OutputBundle) (rowCtx : EvalCtx) (env : ValEnv) :
    Disciplined (EvalBody.evalOutputRowsPreparedCore rec rows rowCtx env) := by
  unfold EvalBody.evalOutputRowsPreparedCore; disc_tac

theorem EvalBody.evalCapturePreparedCore_disciplined (rec : EvalRec) (hrec : ∀ c, Disciplined (rec c)) (rows : OutputBundle) (ctx : EvalCtx) (env : ValEnv) :
    Disciplined (EvalBody.evalCapturePreparedCore rec rows ctx env) := by
  unfold EvalBody.evalCapturePreparedCore; disc_tac

theorem EvalBody.evalCaptureCountedCore_disciplined (rec : EvalRec) (hrec : ∀ c, Disciplined (rec c)) (rows : OutputBundle) (ctx : EvalCtx) (env : ValEnv) :
    Disciplined (EvalBody.evalCaptureCountedCore rec rows ctx env) := by
  unfold EvalBody.evalCaptureCountedCore; disc_tac

theorem EvalBody.evalCaptureValue_disciplined (rec : EvalRec) (hrec : ∀ c, Disciplined (rec c)) (rows : OutputBundle) (ctx : EvalCtx) (env : ValEnv) :
    Disciplined (EvalBody.evalCaptureValue rec rows ctx env) := by
  unfold EvalBody.evalCaptureValue; disc_tac

theorem EvalBody.evalAlgOutputCountedCore_disciplined (rec : EvalRec) (hrec : ∀ c, Disciplined (rec c)) (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    Disciplined (EvalBody.evalAlgOutputCountedCore rec a ctx env) := by
  unfold EvalBody.evalAlgOutputCountedCore; disc_tac

theorem EvalBody.evalAlgOutputCounted_disciplined (rec : EvalRec) (hrec : ∀ c, Disciplined (rec c)) (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    Disciplined (EvalBody.evalAlgOutputCounted rec a ctx env) := by
  unfold EvalBody.evalAlgOutputCounted; disc_tac

/-- A VALUE terminal's read (`EvalBody.terminalAccess`), proved once and used by every body that
    reads one, so those bodies never unfold it inline (M4★). -/
theorem EvalBody.terminalAccess_disciplined (rec : EvalRec) (hrec : ∀ c, Disciplined (rec c)) (t : AliasTerminal) (ctx : EvalCtx) (env : ValEnv) :
    Disciplined (EvalBody.terminalAccess rec t ctx env) := by
  unfold EvalBody.terminalAccess; disc_tac

theorem EvalBody.evalZeroArgumentDemandOutputCounted_disciplined (rec : EvalRec) (hrec : ∀ c, Disciplined (rec c)) (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    Disciplined (EvalBody.evalZeroArgumentDemandOutputCounted rec a ctx env) := by
  unfold EvalBody.evalZeroArgumentDemandOutputCounted; disc_tac

theorem EvalBody.evalZeroArgumentDemandOutput_disciplined (rec : EvalRec) (hrec : ∀ c, Disciplined (rec c)) (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    Disciplined (EvalBody.evalZeroArgumentDemandOutput rec a ctx env) := by
  unfold EvalBody.evalZeroArgumentDemandOutput; disc_tac

theorem EvalBody.evalArgumentValueCounted_disciplined (rec : EvalRec) (hrec : ∀ c, Disciplined (rec c)) (arg : ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) :
    Disciplined (EvalBody.evalArgumentValueCounted rec arg ctx env) := by
  unfold EvalBody.evalArgumentValueCounted; disc_tac

theorem EvalBody.evalArgumentValue_disciplined (rec : EvalRec) (hrec : ∀ c, Disciplined (rec c)) (arg : ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) :
    Disciplined (EvalBody.evalArgumentValue rec arg ctx env) := by
  unfold EvalBody.evalArgumentValue; disc_tac

/-- CACHE-PUB-1: a property request's calculation (a read's demand, an invocation's fresh call) is
    disciplined whenever its recursive answer is. -/
theorem EvalBody.zeroArgPropertyCalculation_disciplined (rec : EvalRec) (hrec : ∀ c, Disciplined (rec c)) (request : ZeroArgPropertyRequest) (resolvedAlgorithm : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    Disciplined (EvalBody.zeroArgPropertyCalculation rec request resolvedAlgorithm ctx env) := by
  unfold EvalBody.zeroArgPropertyCalculation; disc_tac

theorem EvalBody.evalZeroArgPropertyAccessCounted_disciplined (rec : EvalRec) (hrec : ∀ c, Disciplined (rec c)) (accessKind : ZeroArgPropertyAccessKind) (owner : Algorithm) (binding : PropDef) (resolvedAlgorithm : Algorithm) (ctx : EvalCtx) (env : ValEnv) (request : ZeroArgPropertyRequest) :
    Disciplined (EvalBody.evalZeroArgPropertyAccessCounted rec accessKind owner binding resolvedAlgorithm ctx env request) := by
  have hcalc : ∀ q, Disciplined (EvalBody.zeroArgPropertyCalculation rec q resolvedAlgorithm ctx env) :=
    fun q => EvalBody.zeroArgPropertyCalculation_disciplined rec hrec q resolvedAlgorithm ctx env
  unfold EvalBody.evalZeroArgPropertyAccessCounted; disc_tac

theorem EvalBody.evalZeroArgPropertyAccess_disciplined (rec : EvalRec) (hrec : ∀ c, Disciplined (rec c)) (accessKind : ZeroArgPropertyAccessKind) (owner : Algorithm) (binding : PropDef) (resolvedAlgorithm : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    Disciplined (EvalBody.evalZeroArgPropertyAccess rec accessKind owner binding resolvedAlgorithm ctx env) := by
  unfold EvalBody.evalZeroArgPropertyAccess; disc_tac

theorem EvalBody.evalConditionalCallbackCallCounted_disciplined (rec : EvalRec) (hrec : ∀ c, Disciplined (rec c)) (callee : Algorithm) (args : List CountedResult) (ctx : EvalCtx) (env : ValEnv) (calleeName : String) :
    Disciplined (EvalBody.evalConditionalCallbackCallCounted rec callee args ctx env calleeName) := by
  unfold EvalBody.evalConditionalCallbackCallCounted; disc_tac

theorem EvalBody.evalUserCallbackCallCounted_disciplined (rec : EvalRec) (hrec : ∀ c, Disciplined (rec c)) (callee : Algorithm) (args : List CountedResult) (ctx : EvalCtx) (env : ValEnv) :
    Disciplined (EvalBody.evalUserCallbackCallCounted rec callee args ctx env) := by
  unfold EvalBody.evalUserCallbackCallCounted; disc_tac

theorem EvalBody.evalResolvedCallbackCallCounted_disciplined (rec : EvalRec) (hrec : ∀ c, Disciplined (rec c)) (callee : Algorithm) (args : List CountedResult) (ctx : EvalCtx) (env : ValEnv) (calleeName : String) :
    Disciplined (EvalBody.evalResolvedCallbackCallCounted rec callee args ctx env calleeName) := by
  unfold EvalBody.evalResolvedCallbackCallCounted; disc_tac

theorem EvalBody.evalResolvedCallbackCall_disciplined (rec : EvalRec) (hrec : ∀ c, Disciplined (rec c)) (callee : Algorithm) (args : List CountedResult) (ctx : EvalCtx) (env : ValEnv) (calleeName : String) :
    Disciplined (EvalBody.evalResolvedCallbackCall rec callee args ctx env calleeName) := by
  unfold EvalBody.evalResolvedCallbackCall; disc_tac

theorem EvalBody.evalSequenceReduceStepCounted_disciplined (rec : EvalRec) (hrec : ∀ c, Disciplined (rec c)) (callee : Algorithm) (element : CountedResult) (accumulator : Result) (ctx : EvalCtx) (env : ValEnv) (calleeName : String) :
    Disciplined (EvalBody.evalSequenceReduceStepCounted rec callee element accumulator ctx env calleeName) := by
  unfold EvalBody.evalSequenceReduceStepCounted; disc_tac

theorem EvalBody.demandSequenceBuiltinCallItemValue_disciplined (rec : EvalRec) (hrec : ∀ c, Disciplined (rec c)) (item : CallableCallItem) (ctx : EvalCtx) (env : ValEnv) :
    Disciplined (EvalBody.demandSequenceBuiltinCallItemValue rec item ctx env) := by
  unfold EvalBody.demandSequenceBuiltinCallItemValue; disc_tac

theorem EvalBody.bindSequenceBuiltinArguments_disciplined (rec : EvalRec) (hrec : ∀ c, Disciplined (rec c)) (b : Builtin) (metadata : SequenceBuiltinMetadata) (args : List ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) :
    Disciplined (EvalBody.bindSequenceBuiltinArguments rec b metadata args ctx env) := by
  unfold EvalBody.bindSequenceBuiltinArguments; disc_tac

theorem EvalBody.evalReduceCounted_disciplined (rec : EvalRec) (hrec : ∀ c, Disciplined (rec c)) (collection : List CountedResult) (stepAlg : Algorithm) (initial : Result) (ctx : EvalCtx) (env : ValEnv) :
    Disciplined (EvalBody.evalReduceCounted rec collection stepAlg initial ctx env) := by
  unfold EvalBody.evalReduceCounted; disc_tac

theorem EvalBody.evalFilterCounted_disciplined (rec : EvalRec) (hrec : ∀ c, Disciplined (rec c)) (items : List CountedResult) (predicateAlg : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    Disciplined (EvalBody.evalFilterCounted rec items predicateAlg ctx env) := by
  unfold EvalBody.evalFilterCounted; disc_tac

theorem EvalBody.evalMapCounted_disciplined (rec : EvalRec) (hrec : ∀ c, Disciplined (rec c)) (collection : List CountedResult) (transformAlg : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    Disciplined (EvalBody.evalMapCounted rec collection transformAlg ctx env) := by
  unfold EvalBody.evalMapCounted; disc_tac

theorem EvalBody.applyBuiltinCountedSequence_disciplined (rec : EvalRec) (hrec : ∀ c, Disciplined (rec c)) (b : Builtin) (metadata : SequenceBuiltinMetadata) (args : List ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) :
    Disciplined (EvalBody.applyBuiltinCountedSequence rec b metadata args ctx env) := by
  unfold EvalBody.applyBuiltinCountedSequence; disc_tac

-- META-S3-3 enlarged this body (the builtin META binding branch); the same tactic needs more time.
set_option maxHeartbeats 1600000 in
theorem EvalBody.applyBuiltinCounted_disciplined (rec : EvalRec) (hrec : ∀ c, Disciplined (rec c)) (b : Builtin) (args : List ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) :
    Disciplined (EvalBody.applyBuiltinCounted rec b args ctx env) := by
  unfold EvalBody.applyBuiltinCounted; disc_tac

theorem EvalBody.applyBuiltin_disciplined (rec : EvalRec) (hrec : ∀ c, Disciplined (rec c)) (b : Builtin) (args : List ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) :
    Disciplined (EvalBody.applyBuiltin rec b args ctx env) := by
  unfold EvalBody.applyBuiltin; disc_tac

theorem EvalBody.applyBuiltinCountedResolved_disciplined (rec : EvalRec) (hrec : ∀ c, Disciplined (rec c)) (b : Builtin) (args : List ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) :
    Disciplined (EvalBody.applyBuiltinCountedResolved rec b args ctx env) := by
  unfold EvalBody.applyBuiltinCountedResolved; disc_tac

theorem EvalBody.evalExplicitSequenceValueItems_disciplined (rec : EvalRec) (hrec : ∀ c, Disciplined (rec c)) (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    Disciplined (EvalBody.evalExplicitSequenceValueItems rec a ctx env) := by
  unfold EvalBody.evalExplicitSequenceValueItems; disc_tac

theorem EvalBody.evalExplicitSequenceValueRowSlots_disciplined (rec : EvalRec) (hrec : ∀ c, Disciplined (rec c)) (rows : OutputBundle) (rowCtx : EvalCtx) (env : ValEnv) :
    Disciplined (EvalBody.evalExplicitSequenceValueRowSlots rec rows rowCtx env) := by
  unfold EvalBody.evalExplicitSequenceValueRowSlots; disc_tac

theorem EvalBody.evalExplicitSequenceValueExprSlots_disciplined (rec : EvalRec) (hrec : ∀ c, Disciplined (rec c)) (expr : Expr) (ctx : EvalCtx) (env : ValEnv) :
    Disciplined (EvalBody.evalExplicitSequenceValueExprSlots rec expr ctx env) := by
  unfold EvalBody.evalExplicitSequenceValueExprSlots; disc_tac

theorem EvalBody.evalUserCallCounted_disciplined (rec : EvalRec) (hrec : ∀ c, Disciplined (rec c)) (callee : Algorithm) (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) :
    Disciplined (EvalBody.evalUserCallCounted rec callee args ctx env) := by
  unfold EvalBody.evalUserCallCounted; disc_tac

theorem EvalBody.evalConditionalCallCounted_disciplined (rec : EvalRec) (hrec : ∀ c, Disciplined (rec c)) (callee : Algorithm) (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) (calleeName : String) :
    Disciplined (EvalBody.evalConditionalCallCounted rec callee args ctx env calleeName) := by
  unfold EvalBody.evalConditionalCallCounted; disc_tac

theorem EvalBody.evalResolvedCall_disciplined (rec : EvalRec) (hrec : ∀ c, Disciplined (rec c)) (callee : Algorithm) (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) (calleeName : String) :
    Disciplined (EvalBody.evalResolvedCall rec callee args ctx env calleeName) := by
  unfold EvalBody.evalResolvedCall; disc_tac

theorem EvalBody.evalResolvedCallCounted_disciplined (rec : EvalRec) (hrec : ∀ c, Disciplined (rec c)) (callee : Algorithm) (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) (calleeName : String) (origin : CalleeOrigin) :
    Disciplined (EvalBody.evalResolvedCallCounted rec callee args ctx env calleeName origin) := by
  unfold EvalBody.evalResolvedCallCounted; disc_tac

theorem EvalBody.evalCallCountedExpr_disciplined (rec : EvalRec) (hrec : ∀ c, Disciplined (rec c)) (f : Expr) (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) :
    Disciplined (EvalBody.evalCallCountedExpr rec f args ctx env) := by
  unfold EvalBody.evalCallCountedExpr; disc_tac

theorem EvalBody.callLexicalWithReceiverCounted_disciplined (rec : EvalRec) (hrec : ∀ c, Disciplined (rec c)) (name : Ident) (receiver : Expr) (fallback : Expr) (extraArgs : Option OutputBundle) (ctx : EvalCtx) (env : ValEnv) :
    Disciplined (EvalBody.callLexicalWithReceiverCounted rec name receiver fallback extraArgs ctx env) := by
  unfold EvalBody.callLexicalWithReceiverCounted; disc_tac

theorem EvalBody.rejectDotStringIntrinsicArguments_disciplined (rec : EvalRec) (hrec : ∀ c, Disciplined (rec c)) (argsOpt : Option OutputBundle) (ctx : EvalCtx) (env : ValEnv) :
    Disciplined (EvalBody.rejectDotStringIntrinsicArguments rec argsOpt ctx env) := by
  unfold EvalBody.rejectDotStringIntrinsicArguments; disc_tac

theorem EvalBody.evalDotStringReceiverValue_disciplined (rec : EvalRec) (hrec : ∀ c, Disciplined (rec c)) (target : Expr) (targetAlg : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    Disciplined (EvalBody.evalDotStringReceiverValue rec target targetAlg ctx env) := by
  unfold EvalBody.evalDotStringReceiverValue; disc_tac

set_option maxHeartbeats 4000000 in
theorem EvalBody.evalDotCallCounted_disciplined (rec : EvalRec) (hrec : ∀ c, Disciplined (rec c)) (target : Expr) (name : Ident) (fallback : Expr) (argsOpt : Option OutputBundle) (ctx : EvalCtx) (env : ValEnv) :
    Disciplined (EvalBody.evalDotCallCounted rec target name fallback argsOpt ctx env) := by
  unfold EvalBody.evalDotCallCounted; disc_tac

theorem EvalBody.rejectInvokeIntrinsicArguments_disciplined (rec : EvalRec) (hrec : ∀ c, Disciplined (rec c)) (argsOpt : Option OutputBundle) (ctx : EvalCtx) (env : ValEnv) :
    Disciplined (EvalBody.rejectInvokeIntrinsicArguments rec argsOpt ctx env) := by
  unfold EvalBody.rejectInvokeIntrinsicArguments; disc_tac

theorem EvalBody.invokeCallReferenceValue_disciplined (rec : EvalRec) (hrec : ∀ c, Disciplined (rec c)) (val : Result) :
    Disciplined (EvalBody.invokeCallReferenceValue rec val) := by
  unfold EvalBody.invokeCallReferenceValue; disc_tac

theorem EvalBody.argumentViewCells_disciplined (rec : EvalRec) (hrec : ∀ c, Disciplined (rec c)) (a : Nat) :
    Disciplined (EvalBody.argumentViewCells rec a) := by
  unfold EvalBody.argumentViewCells; disc_tac

theorem EvalBody.evalArgumentViewBuiltin_disciplined (rec : EvalRec) (hrec : ∀ c, Disciplined (rec c)) (b : Builtin) (a : Nat) :
    Disciplined (EvalBody.evalArgumentViewBuiltin rec b a) := by
  unfold EvalBody.evalArgumentViewBuiltin; disc_tac

theorem EvalBody.evalSequenceSpreadOperandValue_disciplined (rec : EvalRec) (hrec : ∀ c, Disciplined (rec c)) (e : Expr) (ctx : EvalCtx) (env : ValEnv) :
    Disciplined (EvalBody.evalSequenceSpreadOperandValue rec e ctx env) := by
  unfold EvalBody.evalSequenceSpreadOperandValue; disc_tac

theorem EvalBody.evalSequenceSpreadCounted_disciplined (rec : EvalRec) (hrec : ∀ c, Disciplined (rec c)) (e : Expr) (ctx : EvalCtx) (env : ValEnv) :
    Disciplined (EvalBody.evalSequenceSpreadCounted rec e ctx env) := by
  unfold EvalBody.evalSequenceSpreadCounted; disc_tac

theorem EvalBody.evalSupplySpread_disciplined (rec : EvalRec) (hrec : ∀ c, Disciplined (rec c)) (e : Expr) (ctx : EvalCtx) (env : ValEnv) :
    Disciplined (EvalBody.evalSupplySpread rec e ctx env) := by
  unfold EvalBody.evalSupplySpread; disc_tac

theorem EvalBody.evalListLiteralCounted_disciplined (rec : EvalRec) (hrec : ∀ c, Disciplined (rec c)) (elements : List Expr) (ctx : EvalCtx) (env : ValEnv) :
    Disciplined (EvalBody.evalListLiteralCounted rec elements ctx env) := by
  unfold EvalBody.evalListLiteralCounted; disc_tac

theorem EvalBody.evalSequenceConstructCounted_disciplined (rec : EvalRec) (hrec : ∀ c, Disciplined (rec c)) (e : Expr) (ctx : EvalCtx) (env : ValEnv) :
    Disciplined (EvalBody.evalSequenceConstructCounted rec e ctx env) := by
  unfold EvalBody.evalSequenceConstructCounted; disc_tac

theorem EvalBody.evalUnaryCounted_disciplined (rec : EvalRec) (hrec : ∀ c, Disciplined (rec c)) (op : UnaryOp) (operand : Expr) (ctx : EvalCtx) (env : ValEnv) :
    Disciplined (EvalBody.evalUnaryCounted rec op operand ctx env) := by
  unfold EvalBody.evalUnaryCounted; disc_tac

theorem EvalBody.evalBinaryCounted_disciplined (rec : EvalRec) (hrec : ∀ c, Disciplined (rec c)) (op : BinaryOp) (a b : Expr) (ctx : EvalCtx) (env : ValEnv) :
    Disciplined (EvalBody.evalBinaryCounted rec op a b ctx env) := by
  unfold EvalBody.evalBinaryCounted; disc_tac

theorem EvalBody.evalComparisonCounted_disciplined (rec : EvalRec) (hrec : ∀ c, Disciplined (rec c)) (first : Expr) (links : List ComparisonLink) (ctx : EvalCtx) (env : ValEnv) :
    Disciplined (EvalBody.evalComparisonCounted rec first links ctx env) := by
  unfold EvalBody.evalComparisonCounted; disc_tac

theorem EvalBody.evalComparisonLinksCounted_disciplined (rec : EvalRec) (hrec : ∀ c, Disciplined (rec c)) (previousExpr : Expr) (previous : Result) (holds : Bool) (links : List ComparisonLink) (ctx : EvalCtx) (env : ValEnv) :
    Disciplined (EvalBody.evalComparisonLinksCounted rec previousExpr previous holds links ctx env) := by
  unfold EvalBody.evalComparisonLinksCounted; disc_tac

theorem EvalBody.evalCounted_disciplined (rec : EvalRec) (hrec : ∀ c, Disciplined (rec c)) (e : Expr) (ctx : EvalCtx) (env : ValEnv) :
    Disciplined (EvalBody.evalCounted rec e ctx env) := by
  unfold EvalBody.evalCounted; disc_tac

theorem EvalBody.evalUserCall_disciplined (rec : EvalRec) (hrec : ∀ c, Disciplined (rec c)) (callee : Algorithm) (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) :
    Disciplined (EvalBody.evalUserCall rec callee args ctx env) := by
  unfold EvalBody.evalUserCall; disc_tac

theorem EvalBody.evalConditionalCall_disciplined (rec : EvalRec) (hrec : ∀ c, Disciplined (rec c)) (callee : Algorithm) (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) (calleeName : String) :
    Disciplined (EvalBody.evalConditionalCall rec callee args ctx env calleeName) := by
  unfold EvalBody.evalConditionalCall; disc_tac

theorem EvalBody.evalCallExpr_disciplined (rec : EvalRec) (hrec : ∀ c, Disciplined (rec c)) (f : Expr) (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) :
    Disciplined (EvalBody.evalCallExpr rec f args ctx env) := by
  unfold EvalBody.evalCallExpr; disc_tac

theorem EvalBody.evalDotCall_disciplined (rec : EvalRec) (hrec : ∀ c, Disciplined (rec c)) (target : Expr) (name : Ident) (fallback : Expr) (argsOpt : Option OutputBundle) (ctx : EvalCtx) (env : ValEnv) :
    Disciplined (EvalBody.evalDotCall rec target name fallback argsOpt ctx env) := by
  unfold EvalBody.evalDotCall; disc_tac

theorem EvalBody.eval_disciplined (rec : EvalRec) (hrec : ∀ c, Disciplined (rec c)) (e : Expr) (ctx : EvalCtx) (env : ValEnv) :
    Disciplined (EvalBody.eval rec e ctx env) := by
  unfold EvalBody.eval; disc_tac

theorem evalStep_disciplined (rec : EvalRec) (hrec : ∀ c, Disciplined (rec c)) :
    ∀ c, Disciplined (evalStep rec c) := by
  intro c
  cases c with
  | whileLoop step ctx env stepName cells => exact EvalBody.whileLoop_disciplined rec hrec step ctx env stepName cells
  | aliasStepIsRuntime step target ctx visited => exact EvalBody.aliasStepIsRuntime_disciplined rec hrec step target ctx visited
  | aliasValue wired ctx env => exact EvalBody.aliasValue_disciplined rec hrec wired ctx env
  | resolveAliasChase followCarriers projectRuntime a ctx visited last => exact EvalBody.resolveAliasChase_disciplined rec hrec followCarriers projectRuntime a ctx visited last
  | resolveAliasStructure a ctx => exact EvalBody.resolveAliasStructure_disciplined rec hrec a ctx
  | aliasOriginBinding? a ctx => exact EvalBody.aliasOriginBinding?_disciplined rec hrec a ctx
  | resolveAliasTarget a ctx => exact EvalBody.resolveAliasTarget_disciplined rec hrec a ctx
  | resolveAliasValueTarget a ctx => exact EvalBody.resolveAliasValueTarget_disciplined rec hrec a ctx
  | lookupLexicalProperty a name ctx => exact EvalBody.lookupLexicalProperty_disciplined rec hrec a name ctx
  | lookupLexicalValueProperty a name ctx => exact EvalBody.lookupLexicalValueProperty_disciplined rec hrec a name ctx
  | lookupLexical a name ctx => exact EvalBody.lookupLexical_disciplined rec hrec a name ctx
  | needPlanNormalizeCallee callee ctx => exact EvalBody.needPlanNormalizeCallee_disciplined rec hrec callee ctx
  | resolveAlg e ctx => exact EvalBody.resolveAlg_disciplined rec hrec e ctx
  | projectNeedCallable address => exact EvalBody.projectNeedCallable_disciplined rec hrec address
  | projectNeedWrittenAt address source caller => exact EvalBody.projectNeedWrittenAt_disciplined rec hrec address source caller
  | linkCallable address => exact EvalBody.linkCallable_disciplined rec hrec address
  | projectParameterCallable x ctx => exact EvalBody.projectParameterCallable_disciplined rec hrec x ctx
  | projectNeedWritten source caller => exact EvalBody.projectNeedWritten_disciplined rec hrec source caller
  | projectNeedStructuralMember source ctx => exact EvalBody.projectNeedStructuralMember_disciplined rec hrec source ctx
  | resolveCalleeAlg f ctx => exact EvalBody.resolveCalleeAlg_disciplined rec hrec f ctx
  | expectPreparedSequenceBuiltinAlgorithmSuffixArg b descriptors args index => exact EvalBody.expectPreparedSequenceBuiltinAlgorithmSuffixArg_disciplined rec hrec b descriptors args index
  | resolveDotReceiver? e ctx => exact EvalBody.resolveDotReceiver?_disciplined rec hrec e ctx
  | resolveDotReceiver e ctx => exact EvalBody.resolveDotReceiver_disciplined rec hrec e ctx
  | algorithmIntrinsicRoute receiver ctx => exact EvalBody.algorithmIntrinsicRoute_disciplined rec hrec receiver ctx
  | demandNeedRecursive address => exact EvalBody.demandNeedRecursive_disciplined rec hrec address
  | evalSuppliedAt address e ctx env => exact EvalBody.evalSuppliedAt_disciplined rec hrec address e ctx env
  | linkValue address => exact EvalBody.linkValue_disciplined rec hrec address
  | algorithmOfValue val argsOpt ctx env => exact EvalBody.algorithmOfValue_disciplined rec hrec val argsOpt ctx env
  | capturedCallee callee => exact EvalBody.capturedCallee_disciplined rec hrec callee
  | referenceReceiverValue target targetAlg ctx env => exact EvalBody.referenceReceiverValue_disciplined rec hrec target targetAlg ctx env
  | algorithmCalleeOf receiver ctx env => exact EvalBody.algorithmCalleeOf_disciplined rec hrec receiver ctx env
  | evalSuppliedCallCounted origin callee cells ctx env calleeName => exact EvalBody.evalSuppliedCallCounted_disciplined rec hrec origin callee cells ctx env calleeName
  | evalNeedUserSupply callee cells ctx env => exact EvalBody.evalNeedUserSupply_disciplined rec hrec callee cells ctx env
  | evalNeedFamilySupply callee cells ctx env calleeName => exact EvalBody.evalNeedFamilySupply_disciplined rec hrec callee cells ctx env calleeName
  | invokeNeed arg => exact EvalBody.invokeNeed_disciplined rec hrec arg
  | argumentNeed arg ctx env => exact EvalBody.argumentNeed_disciplined rec hrec arg ctx env
  | runNeedStepSlots step ctx env cells stepName => exact EvalBody.runNeedStepSlots_disciplined rec hrec step ctx env cells stepName
  | runNeedWhileRound step ctx env cells stepName => exact EvalBody.runNeedWhileRound_disciplined rec hrec step ctx env cells stepName
  | evalAlgOutputCore a ctx env => exact EvalBody.evalAlgOutputCore_disciplined rec hrec a ctx env
  | evalAlgOutput a ctx env => exact EvalBody.evalAlgOutput_disciplined rec hrec a ctx env
  | evalProgramOutput a ctx env => exact EvalBody.evalProgramOutput_disciplined rec hrec a ctx env
  | evalAlgOutputSlots a ctx env => exact EvalBody.evalAlgOutputSlots_disciplined rec hrec a ctx env
  | formOutputRow ctx env e => exact EvalBody.formOutputRow_disciplined rec hrec ctx env e
  | whileVerdictSlots a ctx env => exact EvalBody.whileVerdictSlots_disciplined rec hrec a ctx env
  | evalSequenceCallbackCall callee item ctx env calleeName => exact EvalBody.evalSequenceCallbackCall_disciplined rec hrec callee item ctx env calleeName
  | evalSequenceCallbackCallCounted callee item ctx env calleeName => exact EvalBody.evalSequenceCallbackCallCounted_disciplined rec hrec callee item ctx env calleeName
  | evalAlgOutputPreparedCore a ctx env => exact EvalBody.evalAlgOutputPreparedCore_disciplined rec hrec a ctx env
  | evalOutputRowsPreparedCore rows rowCtx env => exact EvalBody.evalOutputRowsPreparedCore_disciplined rec hrec rows rowCtx env
  | evalCapturePreparedCore rows ctx env => exact EvalBody.evalCapturePreparedCore_disciplined rec hrec rows ctx env
  | evalCaptureCountedCore rows ctx env => exact EvalBody.evalCaptureCountedCore_disciplined rec hrec rows ctx env
  | evalCaptureValue rows ctx env => exact EvalBody.evalCaptureValue_disciplined rec hrec rows ctx env
  | evalAlgOutputCountedCore a ctx env => exact EvalBody.evalAlgOutputCountedCore_disciplined rec hrec a ctx env
  | evalAlgOutputCounted a ctx env => exact EvalBody.evalAlgOutputCounted_disciplined rec hrec a ctx env
  | evalZeroArgumentDemandOutputCounted a ctx env => exact EvalBody.evalZeroArgumentDemandOutputCounted_disciplined rec hrec a ctx env
  | evalZeroArgumentDemandOutput a ctx env => exact EvalBody.evalZeroArgumentDemandOutput_disciplined rec hrec a ctx env
  | evalArgumentValueCounted arg ctx env => exact EvalBody.evalArgumentValueCounted_disciplined rec hrec arg ctx env
  | evalArgumentValue arg ctx env => exact EvalBody.evalArgumentValue_disciplined rec hrec arg ctx env
  | evalZeroArgPropertyAccessCounted accessKind owner binding resolvedAlgorithm ctx env request => exact EvalBody.evalZeroArgPropertyAccessCounted_disciplined rec hrec accessKind owner binding resolvedAlgorithm ctx env request
  | evalZeroArgPropertyAccess accessKind owner binding resolvedAlgorithm ctx env => exact EvalBody.evalZeroArgPropertyAccess_disciplined rec hrec accessKind owner binding resolvedAlgorithm ctx env
  | evalConditionalCallbackCallCounted callee args ctx env calleeName => exact EvalBody.evalConditionalCallbackCallCounted_disciplined rec hrec callee args ctx env calleeName
  | evalUserCallbackCallCounted callee args ctx env => exact EvalBody.evalUserCallbackCallCounted_disciplined rec hrec callee args ctx env
  | evalResolvedCallbackCallCounted callee args ctx env calleeName => exact EvalBody.evalResolvedCallbackCallCounted_disciplined rec hrec callee args ctx env calleeName
  | evalResolvedCallbackCall callee args ctx env calleeName => exact EvalBody.evalResolvedCallbackCall_disciplined rec hrec callee args ctx env calleeName
  | evalSequenceReduceStepCounted callee element accumulator ctx env calleeName => exact EvalBody.evalSequenceReduceStepCounted_disciplined rec hrec callee element accumulator ctx env calleeName
  | demandSequenceBuiltinCallItemValue item ctx env => exact EvalBody.demandSequenceBuiltinCallItemValue_disciplined rec hrec item ctx env
  | bindSequenceBuiltinArguments b metadata args ctx env => exact EvalBody.bindSequenceBuiltinArguments_disciplined rec hrec b metadata args ctx env
  | evalReduceCounted collection stepAlg initial ctx env => exact EvalBody.evalReduceCounted_disciplined rec hrec collection stepAlg initial ctx env
  | evalFilterCounted items predicateAlg ctx env => exact EvalBody.evalFilterCounted_disciplined rec hrec items predicateAlg ctx env
  | evalMapCounted collection transformAlg ctx env => exact EvalBody.evalMapCounted_disciplined rec hrec collection transformAlg ctx env
  | applyBuiltinCountedSequence b metadata args ctx env => exact EvalBody.applyBuiltinCountedSequence_disciplined rec hrec b metadata args ctx env
  | applyBuiltinCounted b args ctx env => exact EvalBody.applyBuiltinCounted_disciplined rec hrec b args ctx env
  | applyBuiltin b args ctx env => exact EvalBody.applyBuiltin_disciplined rec hrec b args ctx env
  | applyBuiltinCountedResolved b args ctx env => exact EvalBody.applyBuiltinCountedResolved_disciplined rec hrec b args ctx env
  | evalExplicitSequenceValueItems a ctx env => exact EvalBody.evalExplicitSequenceValueItems_disciplined rec hrec a ctx env
  | evalExplicitSequenceValueRowSlots rows rowCtx env => exact EvalBody.evalExplicitSequenceValueRowSlots_disciplined rec hrec rows rowCtx env
  | evalExplicitSequenceValueExprSlots expr ctx env => exact EvalBody.evalExplicitSequenceValueExprSlots_disciplined rec hrec expr ctx env
  | evalUserCallCounted callee args ctx env => exact EvalBody.evalUserCallCounted_disciplined rec hrec callee args ctx env
  | evalConditionalCallCounted callee args ctx env calleeName => exact EvalBody.evalConditionalCallCounted_disciplined rec hrec callee args ctx env calleeName
  | evalResolvedCall callee args ctx env calleeName => exact EvalBody.evalResolvedCall_disciplined rec hrec callee args ctx env calleeName
  | evalResolvedCallCounted callee args ctx env calleeName origin => exact EvalBody.evalResolvedCallCounted_disciplined rec hrec callee args ctx env calleeName origin
  | evalCallCountedExpr f args ctx env => exact EvalBody.evalCallCountedExpr_disciplined rec hrec f args ctx env
  | callLexicalWithReceiverCounted name receiver fallback extraArgs ctx env => exact EvalBody.callLexicalWithReceiverCounted_disciplined rec hrec name receiver fallback extraArgs ctx env
  | rejectDotStringIntrinsicArguments argsOpt ctx env => exact EvalBody.rejectDotStringIntrinsicArguments_disciplined rec hrec argsOpt ctx env
  | evalDotStringReceiverValue target targetAlg ctx env => exact EvalBody.evalDotStringReceiverValue_disciplined rec hrec target targetAlg ctx env
  | evalDotCallCounted target name fallback argsOpt ctx env => exact EvalBody.evalDotCallCounted_disciplined rec hrec target name fallback argsOpt ctx env
  | rejectInvokeIntrinsicArguments argsOpt ctx env => exact EvalBody.rejectInvokeIntrinsicArguments_disciplined rec hrec argsOpt ctx env
  | invokeCallReferenceValue val => exact EvalBody.invokeCallReferenceValue_disciplined rec hrec val
  | argumentViewCells a => exact EvalBody.argumentViewCells_disciplined rec hrec a
  | evalArgumentViewBuiltin b a => exact EvalBody.evalArgumentViewBuiltin_disciplined rec hrec b a
  | evalSequenceSpreadOperandValue e ctx env => exact EvalBody.evalSequenceSpreadOperandValue_disciplined rec hrec e ctx env
  | evalSequenceSpreadCounted e ctx env => exact EvalBody.evalSequenceSpreadCounted_disciplined rec hrec e ctx env
  | evalSupplySpread e ctx env => exact EvalBody.evalSupplySpread_disciplined rec hrec e ctx env
  | evalListLiteralCounted elements ctx env => exact EvalBody.evalListLiteralCounted_disciplined rec hrec elements ctx env
  | evalSequenceConstructCounted e ctx env => exact EvalBody.evalSequenceConstructCounted_disciplined rec hrec e ctx env
  | evalUnaryCounted op operand ctx env => exact EvalBody.evalUnaryCounted_disciplined rec hrec op operand ctx env
  | evalBinaryCounted op a b ctx env => exact EvalBody.evalBinaryCounted_disciplined rec hrec op a b ctx env
  | evalComparisonCounted first links ctx env => exact EvalBody.evalComparisonCounted_disciplined rec hrec first links ctx env
  | evalComparisonLinksCounted previousExpr previous holds links ctx env => exact EvalBody.evalComparisonLinksCounted_disciplined rec hrec previousExpr previous holds links ctx env
  | evalCounted e ctx env => exact EvalBody.evalCounted_disciplined rec hrec e ctx env
  | evalUserCall callee args ctx env => exact EvalBody.evalUserCall_disciplined rec hrec callee args ctx env
  | evalConditionalCall callee args ctx env calleeName => exact EvalBody.evalConditionalCall_disciplined rec hrec callee args ctx env calleeName
  | evalCallExpr f args ctx env => exact EvalBody.evalCallExpr_disciplined rec hrec f args ctx env
  | evalDotCall target name fallback argsOpt ctx env => exact EvalBody.evalDotCall_disciplined rec hrec target name fallback argsOpt ctx env
  | eval e ctx env => exact EvalBody.eval_disciplined rec hrec e ctx env

/-! ## Whole-run heap discipline and the discharge of `ProductionDiscipline` -/

/-- Every evaluator body is disciplined whenever its recursive answer is: the per-body step of
    the whole-run heap invariant. -/
theorem body_step_disciplined : ∀ rec : EvalRec,
    (∀ c, Preserves (fun s t => HeapKept s.needs t.needs) (rec c)) →
    ∀ c, Preserves (fun s t => HeapKept s.needs t.needs) (evalStep rec c) :=
  fun rec hrec c => evalStep_disciplined rec hrec c

/-- **Every completed run of the total core, at every fuel, keeps every existing cell's
    suspension, completed VALUE and prepared plan supply.** -/
theorem evalFuel_disciplined (n : Nat) (c : EvalCall) (s : EvalState)
    (hc : Completes (evalFuel n c) s) :
    HeapKept s.needs ((evalFuel n c).runState s).2.needs :=
  invariant_transfer (fun s t => HeapKept s.needs t.needs) (fun _ => HeapKept.refl _)
    body_step_disciplined n c s hc

/-- **Every production evaluator operation is disciplined** (unconditionally: a divergent run's
    kernel-level fallback keeps its entry state). -/
theorem evalUnbounded_disciplined (c : EvalCall) : Disciplined (evalUnbounded c) :=
  production_preserves (fun s t => HeapKept s.needs t.needs) (fun _ => HeapKept.refl _)
    body_step_disciplined c

/-- META-S3-4: the production plan-route classifier is disciplined — identity resolution through
    the production receiver resolver and the `.Algorithm` route fact, then a pure selection. -/
theorem classify_disciplined (shape : NeedPlan.CallShape) :
    Disciplined (classifyPlanRouteWith resolveDotReceiver? algorithmIntrinsicRoute shape) := by
  unfold classifyPlanRouteWith
  split
  · split
    · exact Disciplined.bind (evalUnbounded_disciplined (.algorithmIntrinsicRoute _ _))
        (fun b => by split <;> exact disciplined_pure _)
    · exact disciplined_pure _
  · exact Disciplined.bind (evalUnbounded_disciplined (.resolveDotReceiver? _ _))
      (fun t => by split <;> first | exact disciplined_throw _ | exact disciplined_pure _)

/-- **`ProductionDiscipline` IS A THEOREM (R7).** The named opaque obligation of the M1.5
    invocation-plan laws — that the production callbacks keep every existing cell's suspension,
    completed VALUE and prepared plan — holds for the actual production operations, over ALL
    entry states (its original, general statement). -/
theorem productionDiscipline_holds : ProductionDiscipline :=
  ⟨fun a e c v => evalUnbounded_disciplined (.evalSuppliedAt a e c v),
   fun f c => evalUnbounded_disciplined (.resolveCalleeAlg f c),
   fun g c => evalUnbounded_disciplined (.needPlanNormalizeCallee g c),
   fun o g cells c v n => evalUnbounded_disciplined (.evalSuppliedCallCounted o g cells c v n),
   fun b => evalUnbounded_disciplined (.demandNeedRecursive b),
   fun e c v => evalUnbounded_disciplined (.evalSupplySpread e c v),
   classify_disciplined,
   fun b => evalUnbounded_disciplined (.projectNeedCallable b)⟩

/-- The production VALUE demand is disciplined, now without any hypothesis. -/
theorem production_value_disciplined' (a : Nat) : Disciplined (demandNeed a) :=
  production_value_disciplined productionDiscipline_holds a

/-- Production: any number of explicit invocations never change a completed original VALUE —
    now an unconditional kernel theorem. -/
theorem production_invocations_keep_value' (a : Nat) (s : EvalState)
    (cell : NeedCell) (outcome : Except Error CountedResult) (hc : s.needs[a]? = some cell)
    (hs : cell.state = .completed outcome) (refs : List NeedPlan.CallReference) :
    (demandNeed a).runState ((refs.mapM invokeNeedCall).runState s).2 =
      (outcome, ((refs.mapM invokeNeedCall).runState s).2) :=
  production_invocations_keep_value productionDiscipline_holds a s cell outcome hc hs refs

/-- Production: META → VALUE and VALUE → META agree — unconditionally. -/
theorem production_meta_value_orders' (a : Nat) (s : EvalState)
    (shape : NeedPlan.CallShape) (hshape : NeedPlan.shapeAt? s.needs a = some shape) :
    (let metaFirst := (reifyNeedCall a).runState s
     let value := (demandNeed a).runState metaFirst.2
     (metaFirst.1, value.1, value.2)) =
    (let value := (demandNeed a).runState s
     let metaAfter := (reifyNeedCall a).runState value.2
     (metaAfter.1, value.1, metaAfter.2)) :=
  production_meta_value_orders productionDiscipline_holds a s shape hshape



end KatLang.EvaluatorDiscipline
