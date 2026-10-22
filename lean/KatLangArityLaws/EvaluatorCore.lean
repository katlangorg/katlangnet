import Lean
import KatLang

open KatLang
open Lean.Order

/-!
# R7: the fuel-indexed evaluator core — monotonicity, fuel laws and the production bridge

`lean/KatLang.lean` § The fuel-indexed evaluator core defines the recursive evaluator as the
functional `evalStep : EvalRec → EvalRec` over the call universe `EvalCall` (one constructor per
evaluator operation plus the `while` round, 102 in all), iterated by `evalFuel n`, and runs production as the fuel search
`evalUnbounded` over the same core. This module proves, with standard axioms only:

* **Monotonicity** `evalStep_monotone` (in `EvalM.Approx`: the incomplete outcome below every
  answer, a completed answer only below itself), from one lemma per body (`EvalBody.*_mono`) and per
  total helper that takes an evaluator callback (§ Monotonicity of the total helpers).
* **Fuel laws.** Law 1 `completed_stable` (outcome AND final state, for every larger fuel);
  law 3 `completed_deterministic`; law 4 `completed_failure_stable`; the incomplete outcome is
  THE canonical one (`evalFuel_incomplete_normal`). Law 2 is `derives_iff_fuel`: the relational
  semantics `Derives n` (one step over an answer whose completed answers are derivable at height
  `n`) coincides with fuel `n`. Law 5 (divergence stays possible; a bound is not divergence) is
  executable evidence (`EvaluatorCoreGuards`), not a kernel theorem.
* **The production bridge** `production_completes_iff`: a production operation completes with
  `r` exactly when the core completes with `r` at some fuel (through `searchFuel`'s kernel
  fixpoint induction and unfolding equation). Consequences: `evalFuel_approx_production`, and
  `production_unfolds` — a completed production outcome is its body over the production
  operations (the converse is not claimed: it needs finite use of recursive answers).
* **Whole-run invariants** `invariant_transfer` / `production_preserves`: a reflexive state
  relation every body preserves (given its recursive answer does) holds for every completed core
  run at every fuel and for every production run. `EvaluatorDiscipline` instantiates it for the heap
  (discharging `ProductionDiscipline`), `EvaluatorCacheLaws` for the property cache (Q-37).
* **Delegation equations** `delegation_equation`: an operation whose body is one recursive call
  and a non-recursive continuation EQUALS its delegate under production, with no completion
  premise — every plain operation is its counted twin's value (`*_is_counted_projection`, FORMAL-05).

Not claimed: anything about C# (concurrency, cancellation, budgets, Decimal128, host effects); the
converse unfolding of production in general; a kernel proof that a specific program diverges.
-/

namespace KatLang.EvaluatorCore

open Lean Meta Elab Tactic in
/-- Closes `monotone (fun x => core x a₁ … aₖ)` from a local hypothesis — possibly universally
    quantified — whose statement is `monotone (fun x => core x a₁ … aᵢ)` for some `i ≤ k`
    (`monotone_apply` strips the remaining constant arguments). Fails fast when none matches. -/
elab "mono_hyp" : tactic => do
  let goal ← getMainGoal
  let solved ← goal.withContext do
    let ty ← instantiateMVars (← goal.getType)
    let_expr Lean.Order.monotone _ _ _ _ f := ty | return false
    let f := f.headBeta
    unless f.isLambda do return false
    let body := f.bindingBody!.headBeta
    unless body.hasLooseBVars do return false
    let args := body.getAppArgs
    let mut k := 0
    for i in [0:args.size] do
      let a := args[args.size - 1 - i]!
      if a.hasLooseBVars then break
      k := k + 1
    let hyps := (← getLCtx).foldl (init := #[]) fun acc d =>
      if d.isImplementationDetail then acc else acc.push d
    let mut found := false
    for j' in [0:k+1] do
      if found then break
      let j := k - j'
      let saved ← saveState
      let mut g := goal
      let mut ok := true
      for _ in [0:j] do
        if ok then
          match ← observing? (g.apply (← mkConstWithFreshMVarLevels ``Lean.Order.monotone_apply)) with
          | some [g'] => g := g'
          | _ => ok := false
      if ok then
        let gty ← instantiateMVars (← g.getType)
        for d in hyps do
          if found then break
          let s2 ← saveState
          let (ms, _, hty) ← withReducible (forallMetaTelescopeReducing (← instantiateMVars d.type))
          if (← isDefEq gty hty) && (← ms.allM (fun m => return !(← instantiateMVars m).hasMVar)) then
            g.assign (mkAppN d.toExpr ms)
            found := true
          else
            restoreState s2
      unless found do restoreState saved
    return found
  if solved then replaceMainGoal [] else throwError "mono_hyp: no hypothesis matches"

/-- Syntax-directed monotonicity in callbacks and evaluator answers. -/
macro "mono_cb_tac" : tactic =>
  `(tactic| repeat' (first | assumption | monotonicity | mono_hyp | (apply Lean.Order.monotone_of_monotone_apply; intro)))

/-- The body tactic: zeta-reduce local definitions first, then the same procedure. -/
macro "mono_tac" : tactic => `(tactic| (try dsimp only) <;> mono_cb_tac)

/-! ## Monotonicity of the total helpers the bodies call with evaluator callbacks

Each lemma states that a total helper is monotone in the callbacks it is given (`γ` is any
order; in use, the evaluator answer `EvalRec`). They are what lets the syntax-directed
`monotonicity` tactic cross a helper call inside a body. -/

section Helpers
variable {γ : Type} [PartialOrder γ]

@[partial_fixpoint_monotone] theorem monotone_map_evalM {α β : Type} (f : α → β)
    (m : γ → EvalM α) (h : monotone m) : monotone (fun x => f <$> m x) := by
  show monotone (fun x => bind (m x) (Function.comp pure f))
  mono_cb_tac

@[partial_fixpoint_monotone] theorem monotone_withCtx {α : Type} (c : String)
    (m : γ → EvalM α) (h : monotone m) : monotone (fun x => withCtx c (m x)) := by
  unfold withCtx; mono_cb_tac

@[partial_fixpoint_monotone] theorem monotone_withMissingOutputCtx {α : Type} (c : String)
    (m : γ → EvalM α) (h : monotone m) : monotone (fun x => withMissingOutputCtx c (m x)) := by
  unfold withMissingOutputCtx; mono_cb_tac

@[partial_fixpoint_monotone] theorem monotone_formLeftToRight
    (form : γ → Expr → EvalM (List Result)) (h : monotone form) (rows : List Expr) :
    monotone (fun x => OutputRows.formLeftToRight (form x) rows) := by
  induction rows with
  | nil => unfold OutputRows.formLeftToRight; mono_cb_tac
  | cons e rest ih => unfold OutputRows.formLeftToRight; mono_cb_tac

@[partial_fixpoint_monotone] theorem monotone_discover
    (form : γ → Expr → EvalM (List Result)) (h : monotone form) (rows : List Expr) :
    monotone (fun x => WhileRound.discover (form x) rows) := by
  induction rows with
  | nil => unfold WhileRound.discover; mono_cb_tac
  | cons e rest ih => unfold WhileRound.discover; mono_cb_tac

@[partial_fixpoint_monotone] theorem monotone_conditionFirst
    (form : γ → Expr → EvalM (List Result)) (h : monotone form) (rows : List Expr) :
    monotone (fun x => WhileRound.conditionFirst (form x) rows) := by
  unfold WhileRound.conditionFirst; mono_cb_tac

@[partial_fixpoint_monotone] theorem monotone_whileAdvance
    (round : γ → List Nat → EvalM (Option (List Result))) (h : monotone round) (cells : List Nat) :
    monotone (fun x => WhileRound.advance (round x) cells) := by
  unfold WhileRound.advance; mono_cb_tac

@[partial_fixpoint_monotone] theorem monotone_planRouteOf
    (classify : γ → NeedPlan.CallShape → EvalM PlanRoute) (h : monotone classify) (a : Nat)
    (shape : NeedPlan.CallShape) :
    monotone (fun x => NeedPlan.routeOf (classify x) a shape) := by
  unfold NeedPlan.routeOf; mono_cb_tac

@[partial_fixpoint_monotone] theorem monotone_planCalleeCell
    (classify : γ → NeedPlan.CallShape → EvalM PlanRoute) (h : monotone classify) (a : Nat) :
    monotone (fun x => NeedPlan.calleeCell (classify x) a) := by
  unfold NeedPlan.calleeCell; mono_cb_tac

@[partial_fixpoint_monotone] theorem monotone_metaLoopCapture
    (classify : γ → NeedPlan.CallShape → EvalM PlanRoute) (hc : monotone classify)
    (read : γ → Nat → EvalM CountedResult) (hr : monotone read)
    (view : γ → Nat → EvalM (List NeedSupply.Sourced)) (hv : monotone view) (adapter : Nat) :
    monotone (fun x => metaLoopCapture (classify x) (read x) (view x) adapter) := by
  unfold metaLoopCapture; mono_cb_tac

@[partial_fixpoint_monotone] theorem monotone_metaRepeatSetup {α : Type}
    (setup : γ → EvalM α) (hs : monotone setup) (count : γ → EvalM Int) (hc : monotone count) :
    monotone (fun x => metaRepeatSetup (setup x) (count x)) := by
  unfold metaRepeatSetup; mono_cb_tac

@[partial_fixpoint_monotone] theorem monotone_runtimeAliasStepWith
    (project : γ → Nat → EvalM (Option Algorithm)) (h : monotone project)
    (owner : Algorithm) (target : Expr) (ctx : EvalCtx) :
    monotone (fun x => runtimeAliasStepWith (project x) owner target ctx) := by
  unfold runtimeAliasStepWith; mono_cb_tac

@[partial_fixpoint_monotone] theorem monotone_projectParameterWith
    (project : γ → Nat → EvalM (Option Algorithm)) (h : monotone project) (name : Ident) (ctx : EvalCtx) :
    monotone (fun x => projectParameterWith (project x) name ctx) := by
  unfold projectParameterWith; mono_cb_tac

@[partial_fixpoint_monotone] theorem monotone_resolveCalleeAlgWith
    (project : γ → Expr → EvalCtx → EvalM (Option Algorithm)) (hp : monotone project)
    (normalize : γ → Algorithm → EvalCtx → EvalM Algorithm) (hn : monotone normalize)
    (resolve : γ → Expr → EvalCtx → EvalM Algorithm) (hr : monotone resolve) (f : Expr) (ctx : EvalCtx) :
    monotone (fun x => resolveCalleeAlgWith (project x) (normalize x) (resolve x) f ctx) := by
  unfold resolveCalleeAlgWith; mono_cb_tac

@[partial_fixpoint_monotone] theorem monotone_selectWith {α : Type}
    (demand : γ → α → EvalM Result) (h : monotone demand) (receiver : Result) (cells : List α) :
    monotone (fun x => selectWith (demand x) receiver cells) := by
  induction cells with
  | nil => unfold selectWith; mono_cb_tac
  | cons c rest ih => unfold selectWith; mono_cb_tac

@[partial_fixpoint_monotone] theorem monotone_interpolateWith
    (value : γ → Expr → EvalM Result) (h : monotone value) (acc : String)
    (links : List InterpolationLink) :
    monotone (fun x => interpolateWith (value x) acc links) := by
  induction links generalizing acc with
  | nil => unfold interpolateWith; mono_cb_tac
  | cons l rest ih => unfold interpolateWith; mono_cb_tac

@[partial_fixpoint_monotone] theorem monotone_selectViewWith {α : Type}
    (demand : γ → α → EvalM Result) (hd : monotone demand)
    (cellsOf : γ → EvalM (List NeedSupply.Sourced)) (hc : monotone cellsOf)
    (demandCell : γ → Nat → EvalM Result) (hdc : monotone demandCell) (selectors : List α) :
    monotone (fun x => selectViewWith (demand x) (cellsOf x) (demandCell x) selectors) := by
  induction selectors with
  | nil => unfold selectViewWith; mono_cb_tac
  | cons c rest ih => unfold selectViewWith; mono_cb_tac

@[partial_fixpoint_monotone] theorem monotone_expectPreparedSuffixArgAt {α : Type} (b : Builtin)
    (descriptors : List SequenceBuiltinSuffixArgDescriptor) (args : List PreparedSequenceBuiltinSuffixArg)
    (index : Nat) (expectedKind : SequenceBuiltinSuffixArgKind)
    (projector : γ → SequenceBuiltinSuffixArgDescriptor → PreparedSequenceBuiltinSuffixArg → EvalM α)
    (h : monotone projector) :
    monotone (fun x => expectPreparedSequenceBuiltinSuffixArgAt b descriptors args index expectedKind (projector x)) := by
  unfold expectPreparedSequenceBuiltinSuffixArgAt; mono_cb_tac

@[partial_fixpoint_monotone] theorem monotone_argumentViewBuiltin
    (cellsOf : γ → EvalM (List NeedSupply.Sourced)) (hc : monotone cellsOf)
    (demandCell : γ → Nat → EvalM Result) (hdc : monotone demandCell) (b : Builtin) :
    monotone (fun x => argumentViewBuiltin (cellsOf x) (demandCell x) b) := by
  unfold argumentViewBuiltin; mono_cb_tac

/-! ### Need cells: projection, demand, supply, plans and links -/

@[partial_fixpoint_monotone] theorem monotone_projectionSuspended
    (written : γ → Expr → EvalCtx → EvalM (Option Algorithm)) (h : monotone written) :
    monotone (fun x => NeedProjection.suspended (written x)) := by
  intro x y hxy s
  cases s with
  | ready _ => exact Lean.Order.PartialOrder.rel_refl
  | collector _ => exact Lean.Order.PartialOrder.rel_refl
  | expression source caller values =>
    show NeedProjection.suspended (written x) (.expression source caller values) ⊑
      NeedProjection.suspended (written y) (.expression source caller values)
    simp only [NeedProjection.suspended]
    split
    · exact Lean.Order.PartialOrder.rel_refl
    · exact h x y hxy source caller

@[partial_fixpoint_monotone] theorem monotone_projectionStep
    (project : γ → NeedSuspension → EvalM (Option Algorithm)) (h : monotone project) (a : Nat) :
    monotone (fun x => NeedProjection.step (project x) a) := by
  unfold NeedProjection.step; mono_cb_tac

@[partial_fixpoint_monotone] theorem monotone_supplySlot
    (spread : γ → NeedSupply.SpreadEval) (h : monotone spread) (ctx : EvalCtx) (env : ValEnv) (e : Expr) :
    monotone (fun x => NeedSupply.slot (spread x) ctx env e) := by
  unfold NeedSupply.slot; mono_cb_tac

@[partial_fixpoint_monotone] theorem monotone_supplyForm
    (spread : γ → NeedSupply.SpreadEval) (h : monotone spread) (ctx : EvalCtx) (env : ValEnv)
    (args : OutputBundle) :
    monotone (fun x => NeedSupply.form (spread x) ctx env args) := by
  induction args with
  | nil => unfold NeedSupply.form; mono_cb_tac
  | cons e rest ih => unfold NeedSupply.form; mono_cb_tac

@[partial_fixpoint_monotone] theorem monotone_supplyAddresses
    (spread : γ → NeedSupply.SpreadEval) (h : monotone spread) (ctx : EvalCtx) (env : ValEnv)
    (args : OutputBundle) :
    monotone (fun x => NeedSupply.addresses (spread x) ctx env args) := by
  unfold NeedSupply.addresses; mono_cb_tac

@[partial_fixpoint_monotone] theorem monotone_planPrepare
    (spread : γ → NeedSupply.SpreadEval) (h : monotone spread) (a : Nat) (shape : NeedPlan.CallShape) :
    monotone (fun x => NeedPlan.prepare (spread x) a shape) := by
  unfold NeedPlan.prepare; mono_cb_tac

/-- A plan route given by monotone fields. -/
structure RouteMono (route : γ → NeedPlan.Route) : Prop where
  target : monotone (fun x => (route x).target)
  normalize : monotone (fun x => (route x).normalize)
  dispatch : monotone (fun x => (route x).dispatch)
  spread : monotone (fun x => (route x).spread)
  classify : monotone (fun x => (route x).classify)
  project : monotone (fun x => (route x).project)

theorem monotone_planCalleeAlong (route : γ → NeedPlan.Route) (h : RouteMono route) (a : Nat)
    (eff : NeedPlan.CallShape) (r : PlanRoute) :
    monotone (fun x => NeedPlan.calleeAlong (route x) a eff r) := by
  have ht := h.target; have hp := h.project
  have := monotone_planCalleeCell (fun x => (route x).classify) h.classify a
  cases r <;> (simp only [NeedPlan.calleeAlong]; mono_cb_tac)

theorem monotone_planExecuteAlong (route : γ → NeedPlan.Route) (h : RouteMono route) (a : Nat)
    (shape : NeedPlan.CallShape) (r : PlanRoute) :
    monotone (fun x => NeedPlan.executeAlong (route x) a shape r) := by
  have hn := h.normalize; have hd := h.dispatch; have hs := h.spread
  have := monotone_planCalleeAlong route h a (NeedPlan.effective shape r) r
  unfold NeedPlan.executeAlong; dsimp only; mono_cb_tac

theorem monotone_planExecute (route : γ → NeedPlan.Route) (h : RouteMono route) (a : Nat)
    (shape : NeedPlan.CallShape) :
    monotone (fun x => NeedPlan.execute (route x) a shape) := by
  have := monotone_planRouteOf (fun x => (route x).classify) h.classify a shape
  have := monotone_planExecuteAlong route h a shape
  unfold NeedPlan.execute; mono_cb_tac

theorem monotone_planInvoke (route : γ → NeedPlan.Route) (h : RouteMono route)
    (r : NeedPlan.CallReference) :
    monotone (fun x => NeedPlan.invoke (route x) r) := by
  unfold NeedPlan.invoke
  have := monotone_planExecute route h
  mono_cb_tac

@[partial_fixpoint_monotone] theorem monotone_planViewCells
    (spread : γ → NeedSupply.SpreadEval) (h : monotone spread)
    (classify : γ → NeedPlan.CallShape → EvalM PlanRoute) (hc : monotone classify) (a : Nat) :
    monotone (fun x => NeedPlan.viewCells (spread x) (classify x) a) := by
  unfold NeedPlan.viewCells; mono_cb_tac

@[partial_fixpoint_monotone] theorem monotone_planViewSupply
    (spread : γ → NeedSupply.SpreadEval) (h : monotone spread)
    (classify : γ → NeedPlan.CallShape → EvalM PlanRoute) (hc : monotone classify) (a : Nat) :
    monotone (fun x => NeedPlan.viewSupply (spread x) (classify x) a) := by
  unfold NeedPlan.viewSupply; mono_cb_tac

@[partial_fixpoint_monotone] theorem monotone_demandMaterialize
    (demand : γ → Nat → EvalM CountedResult) (h : monotone demand) (slice : List Nat) :
    monotone (fun x => NeedDemand.materialize (demand x) slice) := by
  unfold NeedDemand.materialize; mono_cb_tac

theorem monotone_suspendedValue
    (ev : γ → Expr → EvalCtx → ValEnv → EvalM CountedResult) (hev : monotone ev)
    (route : γ → NeedPlan.Route) (hroute : RouteMono route)
    (demand : γ → Nat → EvalM CountedResult) (hd : monotone demand) (a : Nat) (sus : NeedSuspension) :
    monotone (fun x => NeedDemand.suspendedValue (ev x) (route x) (demand x) a sus) := by
  cases sus with
  | ready v => exact monotone_const _
  | collector slice => exact monotone_demandMaterialize demand hd slice
  | expression e c v =>
    simp only [NeedDemand.suspendedValue]
    cases NeedPlan.callShape? e c v with
    | none => exact monotone_map_evalM _ _ (monotone_apply _ _ (monotone_apply _ _ (monotone_apply _ _ hev)))
    | some shape =>
      have := monotone_planExecuteAlong route hroute a shape
      have := monotone_planRouteOf (fun x => (route x).classify) hroute.classify a shape
      have hm : monotone (fun x => reCountValueBoundary <$> ev x e c v) :=
        monotone_map_evalM _ _ (monotone_apply _ _ (monotone_apply _ _ (monotone_apply _ _ hev)))
      mono_cb_tac

theorem monotone_demandStep
    (ev : γ → Expr → EvalCtx → ValEnv → EvalM CountedResult) (hev : monotone ev)
    (route : γ → NeedPlan.Route) (hroute : RouteMono route)
    (demand : γ → Nat → EvalM CountedResult) (hd : monotone demand) (a : Nat) :
    monotone (fun x => NeedDemand.step (ev x) (route x) (demand x) a) := by
  have hsv := monotone_suspendedValue ev hev route hroute demand hd a
  unfold NeedDemand.step; mono_cb_tac

@[partial_fixpoint_monotone] theorem monotone_linkDecodeCallee
    (classify : γ → NeedPlan.CallShape → EvalM PlanRoute) (hc : monotone classify)
    (demand : γ → Nat → EvalM CountedResult) (h : monotone demand) (a : Nat) :
    monotone (fun x => NeedLink.decodeCallee (classify x) (demand x) a) := by
  unfold NeedLink.decodeCallee; mono_cb_tac

@[partial_fixpoint_monotone] theorem monotone_linkValue
    (classify : γ → NeedPlan.CallShape → EvalM PlanRoute) (hc : monotone classify)
    (demand : γ → Nat → EvalM CountedResult) (h : monotone demand) (a : Nat) :
    monotone (fun x => NeedLink.value (classify x) (demand x) a) := by
  unfold NeedLink.value; mono_cb_tac

@[partial_fixpoint_monotone] theorem monotone_linkCallable
    (classify : γ → NeedPlan.CallShape → EvalM PlanRoute) (hc : monotone classify)
    (demand : γ → Nat → EvalM CountedResult) (h : monotone demand)
    (project : γ → Nat → EvalM (Option Algorithm)) (hp : monotone project) (a : Nat) :
    monotone (fun x => NeedLink.callable (classify x) (demand x) (project x) a) := by
  unfold NeedLink.callable; mono_cb_tac

@[partial_fixpoint_monotone] theorem monotone_classifyPlanRouteWith
    (resolve : γ → Expr → EvalCtx → EvalM (Option Algorithm)) (hr : monotone resolve)
    (route : γ → Expr → EvalCtx → EvalM Bool) (hg : monotone route) :
    monotone (fun x => classifyPlanRouteWith (resolve x) (route x)) := by
  apply Lean.Order.monotone_of_monotone_apply; intro shape
  unfold classifyPlanRouteWith; mono_cb_tac

/-! ### The generic binder and the family dispatcher -/

/-- Capabilities given by monotone fields. -/
structure CapsMono (caps : γ → NeedCapabilities EvalM) : Prop where
  value : monotone (fun x => (caps x).value)
  callable : monotone (fun x => (caps x).callable)
  allocate : monotone (fun x => (caps x).allocate)
  reference : monotone (fun x => (caps x).reference)

@[partial_fixpoint_monotone] theorem monotone_cardinalityGate (patterns : List NeedPattern) (count : Nat) (family : Bool)
    (accepted : γ → EvalM (Option NeedEnv)) (h : monotone accepted) :
    monotone (fun x => NeedBinder.cardinalityGate patterns count family (accepted x)) := by
  unfold NeedBinder.cardinalityGate; mono_cb_tac

@[partial_fixpoint_monotone] theorem monotone_sourceAddress (allocate : γ → NeedSuspension → EvalM Nat) (h : monotone allocate)
    (source : NeedSource Nat) :
    monotone (fun x => NeedBinder.sourceAddress (allocate x) source) := by
  unfold NeedBinder.sourceAddress; mono_cb_tac

/-- META-DIAG-1: the META capture combinator is monotone in its capture (its handler is fixed). -/
@[partial_fixpoint_monotone] theorem monotone_captureMeta (name : Ident) (capture : γ → EvalM Nat)
    (h : monotone capture) : monotone (fun x => NeedBinder.captureMeta name (capture x)) := by
  intro a b hab s
  show EvalM.IsIncompleteAt _ s ∨ _
  unfold EvalM.IsIncompleteAt
  rw [NeedBinder.captureMeta_runState, NeedBinder.captureMeta_runState]
  rcases h a b hab s with hs | hs
  · left; unfold EvalM.IsIncompleteAt at hs; rw [hs]; rfl
  · right; rw [hs]

theorem monotone_bindName (caps : γ → NeedCapabilities EvalM) (hc : CapsMono caps)
    (name : Ident) (address : Nat) (repeated : List Ident) (bound : NeedEnv) (family : Bool) :
    monotone (fun x => NeedBinder.bindName (caps x) name address repeated bound family) := by
  have hv := hc.value; have hcl := hc.callable
  unfold NeedBinder.bindName; mono_tac

theorem monotone_binder (caps : γ → NeedCapabilities EvalM) (hc : CapsMono caps)
    (repeated : List Ident) (family : Bool) :
    (∀ pattern address bound,
      monotone (fun x => NeedBinder.bindOne (caps x) pattern address repeated bound family)) ∧
    (∀ patterns sources current,
      monotone (fun x => NeedBinder.bindSources (caps x) patterns sources repeated current family)) := by
  have hv := hc.value; have hcl := hc.callable; have hal := hc.allocate; have hre := hc.reference
  have hname := monotone_bindName caps hc
  have hsrc := monotone_sourceAddress (fun x => (caps x).allocate) hal
  refine NeedBinder.bindOne.mutual_induct
    (motive_1 := fun pattern address bound =>
      monotone (fun x => NeedBinder.bindOne (caps x) pattern address repeated bound family))
    (motive_2 := fun patterns sources current =>
      monotone (fun x => NeedBinder.bindSources (caps x) patterns sources repeated current family))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro address bound name collecting
    simp only [NeedBinder.bindOne]
    exact hname name address repeated bound family
  · intro address bound name
    simp only [NeedBinder.bindOne]
    mono_tac
  · intro address bound literal
    simp only [NeedBinder.bindOne]
    mono_tac
  · intro address bound ps ih
    simp only [NeedBinder.bindOne]
    have hg := monotone_cardinalityGate (γ := γ) ps
    mono_tac
  · intro address bound ps ih
    simp only [NeedBinder.bindOne]
    have hg := monotone_cardinalityGate (γ := γ) ps
    mono_tac
  · intro address bound ps ih
    simp only [NeedBinder.bindOne]
    have hg := monotone_cardinalityGate (γ := γ) ps
    mono_tac
  · intro sources current
    simp only [NeedBinder.bindSources]
    mono_tac
  · intro sources current pattern rest ih1 ih2
    simp only [NeedBinder.bindSources]
    mono_tac

theorem monotone_bindPatterns (caps : γ → NeedCapabilities EvalM) (hc : CapsMono caps)
    (patterns : List NeedPattern) (cells : List Nat) (family : Bool) :
    monotone (fun x => NeedBinder.bindPatterns (caps x) patterns cells family) := by
  unfold NeedBinder.bindPatterns NeedBinder.bindLevel
  exact monotone_cardinalityGate _ _ _ _
    ((monotone_binder caps hc (needRepeatedNames patterns) family).2 _ _ _)

theorem monotone_chooseBranch {β : Type} (caps : γ → NeedCapabilities EvalM) (hc : CapsMono caps)
    (cells : List Nat) (calleeName : String) (activate : CondBranch → NeedEnv → EvalM β)
    (branches : List CondBranch) :
    monotone (fun x => NeedBinder.chooseBranch (caps x) cells calleeName activate branches) := by
  induction branches with
  | nil => unfold NeedBinder.chooseBranch; mono_cb_tac
  | cons b rest ih =>
    unfold NeedBinder.chooseBranch
    have := fun ps fam => monotone_bindPatterns caps hc ps cells fam
    mono_tac

theorem monotone_selectFamily {β : Type} (caps : γ → NeedCapabilities EvalM) (hc : CapsMono caps)
    (callee : Algorithm) (cells : List Nat) (calleeName : String)
    (activate : CondBranch → NeedEnv → EvalM β) :
    monotone (fun x => NeedBinder.selectFamily (caps x) callee cells calleeName activate) := by
  unfold NeedBinder.selectFamily
  have := monotone_chooseBranch caps hc cells calleeName activate
  mono_tac

end Helpers

/-! ### The production records over an evaluator answer -/

theorem planRoute_mono {γ : Type} [PartialOrder γ] (recOf : γ → EvalRec) (h : monotone recOf) :
    RouteMono (fun x => (recOf x).planRoute) :=
  ⟨fun _ _ hxy _ _ => h _ _ hxy _, fun _ _ hxy _ _ => h _ _ hxy _,
   fun _ _ hxy _ _ _ _ _ _ => h _ _ hxy _, fun _ _ hxy _ _ _ => h _ _ hxy _,
   monotone_classifyPlanRouteWith _ (fun _ _ hxy _ _ => h _ _ hxy _) _ (fun _ _ hxy _ _ => h _ _ hxy _),
   fun _ _ hxy _ => h _ _ hxy _⟩

theorem planRoute_classify_mono : monotone (fun rec : EvalRec => rec.planRoute.classify) :=
  (planRoute_mono (fun rec : EvalRec => rec) (fun _ _ h => h)).classify

theorem bindingCaps_mono {γ : Type} [PartialOrder γ] (recOf : γ → EvalRec) (h : monotone recOf) :
    CapsMono (fun x => (recOf x).bindingChannels.capabilities) := by
  refine ⟨?_, ?_, monotone_const _, monotone_const _⟩
  · intro x y hxy a
    exact monotone_demandStep (fun x => (recOf x).evalSuppliedAt a) (fun _ _ hxy _ _ _ => h _ _ hxy _)
      _ (planRoute_mono recOf h) (fun x => (recOf x).demandNeedRecursive) (fun _ _ hxy _ => h _ _ hxy _)
      a x y hxy
  · intro x y hxy a
    exact monotone_projectionStep _ (monotone_projectionSuspended
      (fun x => (recOf x).projectNeedWrittenAt a) (fun _ _ hxy _ _ => h _ _ hxy _)) a x y hxy

@[partial_fixpoint_monotone] theorem monotone_bindNeedPatterns {γ : Type} [PartialOrder γ]
    (recOf : γ → EvalRec) (h : monotone recOf) (patterns : List NeedPattern) (cells : List Nat)
    (family : Bool) :
    monotone (fun x => bindNeedPatterns (recOf x).bindingChannels patterns cells family) :=
  monotone_bindPatterns _ (bindingCaps_mono recOf h) patterns cells family

@[partial_fixpoint_monotone] theorem monotone_selectNeedFamilyBranch {γ : Type} [PartialOrder γ]
    (recOf : γ → EvalRec) (h : monotone recOf) (callee : Algorithm) (cells : List Nat)
    (ctx : EvalCtx) (env : ValEnv) (calleeName : String) :
    monotone (fun x => selectNeedFamilyBranch (recOf x).bindingChannels callee cells ctx env calleeName) :=
  monotone_selectFamily _ (bindingCaps_mono recOf h) callee cells calleeName _

@[partial_fixpoint_monotone] theorem monotone_planInvoke_rec {γ : Type} [PartialOrder γ]
    (recOf : γ → EvalRec) (h : monotone recOf) (r : NeedPlan.CallReference) :
    monotone (fun x => NeedPlan.invoke (recOf x).planRoute r) :=
  monotone_planInvoke _ (planRoute_mono recOf h) r

@[partial_fixpoint_monotone] theorem monotone_demandStep_rec {γ : Type} [PartialOrder γ]
    (recOf : γ → EvalRec) (h : monotone recOf) (ev : γ → Expr → EvalCtx → ValEnv → EvalM CountedResult)
    (hev : monotone ev) (a : Nat) :
    monotone (fun x => NeedDemand.step (ev x) (recOf x).planRoute (recOf x).demandNeedRecursive a) :=
  monotone_demandStep ev hev _ (planRoute_mono recOf h) _ (fun _ _ hxy _ => h _ _ hxy _) a


/-! ### The bodies' local loops (structural `let rec` helpers over lists) -/

section LocalLoops
variable {γ : Type} [PartialOrder γ] (recOf : γ → EvalRec) (h : monotone recOf)
include h

@[partial_fixpoint_monotone] theorem monotone_outputRowsCollect (rowCtx : EvalCtx) (env : ValEnv)
    (rows : List Expr) (acc : List Result) (emitted : Nat) :
    monotone (fun ρ => EvalBody.evalOutputRowsPreparedCore.collect (recOf ρ) rowCtx env rows acc emitted) := by
  induction rows generalizing acc emitted with
  | nil => unfold EvalBody.evalOutputRowsPreparedCore.collect; mono_tac
  | cons e rest ih => unfold EvalBody.evalOutputRowsPreparedCore.collect; mono_tac

@[partial_fixpoint_monotone] theorem monotone_explicitRowsCollect (rowCtx : EvalCtx) (env : ValEnv)
    (rows : List Expr) (acc : List Result) :
    monotone (fun ρ => EvalBody.evalExplicitSequenceValueRowSlots.collect (recOf ρ) rowCtx env rows acc) := by
  induction rows generalizing acc with
  | nil => unfold EvalBody.evalExplicitSequenceValueRowSlots.collect; mono_tac
  | cons e rest ih => unfold EvalBody.evalExplicitSequenceValueRowSlots.collect; mono_tac

@[partial_fixpoint_monotone] theorem monotone_listLiteralCollect (ctx : EvalCtx) (env : ValEnv)
    (elements : List Expr) (acc : List Result) :
    monotone (fun ρ => EvalBody.evalListLiteralCounted.collect (recOf ρ) ctx env elements acc) := by
  induction elements generalizing acc with
  | nil => unfold EvalBody.evalListLiteralCounted.collect; mono_tac
  | cons e rest ih => unfold EvalBody.evalListLiteralCounted.collect; mono_tac

@[partial_fixpoint_monotone] theorem monotone_sequenceConstructLoop (ctx : EvalCtx) (env : ValEnv)
    (leaves : List Expr) (items : List Result) :
    monotone (fun ρ => EvalBody.evalSequenceConstructCounted.loop (recOf ρ) ctx env leaves items) := by
  induction leaves generalizing items with
  | nil => unfold EvalBody.evalSequenceConstructCounted.loop; mono_tac
  | cons e rest ih => unfold EvalBody.evalSequenceConstructCounted.loop; mono_tac

@[partial_fixpoint_monotone] theorem monotone_prepareControls (b : Builtin) (ctx : EvalCtx) (env : ValEnv)
    (descriptors : List SequenceBuiltinSuffixArgDescriptor) (items : List CallableCallItem) :
    monotone (fun ρ => EvalBody.bindSequenceBuiltinArguments.prepareControls (recOf ρ) b ctx env descriptors items) := by
  induction descriptors generalizing items with
  | nil => cases items <;> (unfold EvalBody.bindSequenceBuiltinArguments.prepareControls; mono_tac)
  | cons d rest ih => cases items <;> (unfold EvalBody.bindSequenceBuiltinArguments.prepareControls; mono_tac)

@[partial_fixpoint_monotone] theorem monotone_reduceLoop (stepAlg : Algorithm) (ctx : EvalCtx) (env : ValEnv)
    (items : List CountedResult) (acc : CountedResult) :
    monotone (fun ρ => EvalBody.evalReduceCounted.reduceLoop (recOf ρ) stepAlg ctx env items acc) := by
  induction items generalizing acc with
  | nil => unfold EvalBody.evalReduceCounted.reduceLoop; mono_tac
  | cons i rest ih => unfold EvalBody.evalReduceCounted.reduceLoop; mono_tac

@[partial_fixpoint_monotone] theorem monotone_filterLoop (predicateAlg : Algorithm) (ctx : EvalCtx) (env : ValEnv)
    (index : Nat) (items : List CountedResult) :
    monotone (fun ρ => EvalBody.evalFilterCounted.filterLoop (recOf ρ) predicateAlg ctx env index items) := by
  induction items generalizing index with
  | nil => unfold EvalBody.evalFilterCounted.filterLoop; mono_tac
  | cons i rest ih => unfold EvalBody.evalFilterCounted.filterLoop; mono_tac

@[partial_fixpoint_monotone] theorem monotone_mapLoop (transformAlg : Algorithm) (ctx : EvalCtx) (env : ValEnv)
    (items : List CountedResult) :
    monotone (fun ρ => EvalBody.evalMapCounted.mapLoop (recOf ρ) transformAlg ctx env items) := by
  induction items with
  | nil => unfold EvalBody.evalMapCounted.mapLoop; mono_tac
  | cons i rest ih => unfold EvalBody.evalMapCounted.mapLoop; mono_tac

@[partial_fixpoint_monotone] theorem monotone_repeatLoop (ctx : EvalCtx) (env : ValEnv)
    (step : ResolvedArgumentAlgorithm) (stepName : String) (remaining : Nat) (cells : List Nat) :
    monotone (fun ρ => EvalBody.applyBuiltinCounted.repeatLoop (recOf ρ) ctx env step stepName remaining cells) := by
  induction remaining generalizing cells with
  | zero => unfold EvalBody.applyBuiltinCounted.repeatLoop; mono_tac
  | succ k ih => unfold EvalBody.applyBuiltinCounted.repeatLoop; mono_tac

end LocalLoops

theorem EvalBody.whileLoop_mono (step : ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) (stepName : String) (cells : List Nat) :
    monotone (fun rec : EvalRec => EvalBody.whileLoop rec step ctx env stepName cells) := by
  unfold EvalBody.whileLoop; mono_tac

theorem EvalBody.aliasStepIsRuntime_mono (step : Algorithm) (target : Expr) (ctx : EvalCtx) :
    monotone (fun rec : EvalRec => EvalBody.aliasStepIsRuntime rec step target ctx) := by
  unfold EvalBody.aliasStepIsRuntime; mono_tac

theorem EvalBody.aliasValue_mono (wired : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    monotone (fun rec : EvalRec => EvalBody.aliasValue rec wired ctx env) := by
  unfold EvalBody.aliasValue; mono_tac

theorem EvalBody.resolveAliasChase_mono (callable : Bool) (a : Algorithm) (ctx : EvalCtx) (visited : List String) (projectedFrom : Option Algorithm) :
    monotone (fun rec : EvalRec => EvalBody.resolveAliasChase rec callable a ctx visited projectedFrom) := by
  unfold EvalBody.resolveAliasChase; mono_tac

theorem EvalBody.resolveAliasTarget_mono (a : Algorithm) (ctx : EvalCtx) :
    monotone (fun rec : EvalRec => EvalBody.resolveAliasTarget rec a ctx) := by
  unfold EvalBody.resolveAliasTarget; mono_tac

theorem EvalBody.resolveAliasValueTarget_mono (a : Algorithm) (ctx : EvalCtx) :
    monotone (fun rec : EvalRec => EvalBody.resolveAliasValueTarget rec a ctx) := by
  unfold EvalBody.resolveAliasValueTarget; mono_tac

theorem EvalBody.lookupLexicalProperty_mono (a : Algorithm) (name : Ident) (ctx : EvalCtx) :
    monotone (fun rec : EvalRec => EvalBody.lookupLexicalProperty rec a name ctx) := by
  unfold EvalBody.lookupLexicalProperty; mono_tac

theorem EvalBody.lookupLexicalValueProperty_mono (a : Algorithm) (name : Ident) (ctx : EvalCtx) :
    monotone (fun rec : EvalRec => EvalBody.lookupLexicalValueProperty rec a name ctx) := by
  unfold EvalBody.lookupLexicalValueProperty; mono_tac

theorem EvalBody.lookupLexical_mono (a : Algorithm) (name : Ident) (ctx : EvalCtx) :
    monotone (fun rec : EvalRec => EvalBody.lookupLexical rec a name ctx) := by
  unfold EvalBody.lookupLexical; mono_tac

theorem EvalBody.needPlanNormalizeCallee_mono (callee : Algorithm) (ctx : EvalCtx) :
    monotone (fun rec : EvalRec => EvalBody.needPlanNormalizeCallee rec callee ctx) := by
  unfold EvalBody.needPlanNormalizeCallee; mono_tac

theorem EvalBody.resolveAlg_mono (e : Expr) (ctx : EvalCtx) :
    monotone (fun rec : EvalRec => EvalBody.resolveAlg rec e ctx) := by
  unfold EvalBody.resolveAlg; mono_tac

theorem EvalBody.projectNeedCallable_mono (address : Nat) :
    monotone (fun rec : EvalRec => EvalBody.projectNeedCallable rec address) := by
  unfold EvalBody.projectNeedCallable; mono_tac

theorem EvalBody.projectNeedWrittenAt_mono (address : Nat) (source : Expr) (caller : EvalCtx) :
    monotone (fun rec : EvalRec => EvalBody.projectNeedWrittenAt rec address source caller) := by
  unfold EvalBody.projectNeedWrittenAt; mono_tac

theorem EvalBody.linkCallable_mono (address : Nat) :
    monotone (fun rec : EvalRec => EvalBody.linkCallable rec address) := by
  have := planRoute_classify_mono; unfold EvalBody.linkCallable; mono_tac

theorem EvalBody.projectParameterCallable_mono (x : Ident) (ctx : EvalCtx) :
    monotone (fun rec : EvalRec => EvalBody.projectParameterCallable rec x ctx) := by
  unfold EvalBody.projectParameterCallable; mono_tac

theorem EvalBody.projectNeedWritten_mono (source : Expr) (caller : EvalCtx) :
    monotone (fun rec : EvalRec => EvalBody.projectNeedWritten rec source caller) := by
  unfold EvalBody.projectNeedWritten; mono_tac

theorem EvalBody.projectNeedStructuralMember_mono (source : Expr) (ctx : EvalCtx) :
    monotone (fun rec : EvalRec => EvalBody.projectNeedStructuralMember rec source ctx) := by
  unfold EvalBody.projectNeedStructuralMember; mono_tac

theorem EvalBody.resolveCalleeAlg_mono (f : Expr) (ctx : EvalCtx) :
    monotone (fun rec : EvalRec => EvalBody.resolveCalleeAlg rec f ctx) := by
  unfold EvalBody.resolveCalleeAlg; mono_tac

theorem EvalBody.expectPreparedSequenceBuiltinAlgorithmSuffixArg_mono (b : Builtin) (descriptors : List SequenceBuiltinSuffixArgDescriptor) (args : List PreparedSequenceBuiltinSuffixArg) (index : Nat) :
    monotone (fun rec : EvalRec => EvalBody.expectPreparedSequenceBuiltinAlgorithmSuffixArg rec b descriptors args index) := by
  unfold EvalBody.expectPreparedSequenceBuiltinAlgorithmSuffixArg; mono_tac

theorem EvalBody.resolveDotReceiver?_mono (e : Expr) (ctx : EvalCtx) :
    monotone (fun rec : EvalRec => EvalBody.resolveDotReceiver? rec e ctx) := by
  unfold EvalBody.resolveDotReceiver?; mono_tac

theorem EvalBody.resolveDotReceiver_mono (e : Expr) (ctx : EvalCtx) :
    monotone (fun rec : EvalRec => EvalBody.resolveDotReceiver rec e ctx) := by
  unfold EvalBody.resolveDotReceiver; mono_tac

theorem EvalBody.algorithmIntrinsicRoute_mono (receiver : Expr) (ctx : EvalCtx) :
    monotone (fun rec : EvalRec => EvalBody.algorithmIntrinsicRoute rec receiver ctx) := by
  unfold EvalBody.algorithmIntrinsicRoute; mono_tac

theorem EvalBody.demandNeedRecursive_mono (address : Nat) :
    monotone (fun rec : EvalRec => EvalBody.demandNeedRecursive rec address) := by
  unfold EvalBody.demandNeedRecursive; mono_tac

theorem EvalBody.evalSuppliedAt_mono (address : Nat) (e : Expr) (ctx : EvalCtx) (env : ValEnv) :
    monotone (fun rec : EvalRec => EvalBody.evalSuppliedAt rec address e ctx env) := by
  unfold EvalBody.evalSuppliedAt; mono_tac

theorem EvalBody.linkValue_mono (address : Nat) :
    monotone (fun rec : EvalRec => EvalBody.linkValue rec address) := by
  have := planRoute_classify_mono; unfold EvalBody.linkValue; mono_tac

theorem EvalBody.algorithmOfValue_mono (val : Result) (argsOpt : Option OutputBundle) (ctx : EvalCtx) (env : ValEnv) :
    monotone (fun rec : EvalRec => EvalBody.algorithmOfValue rec val argsOpt ctx env) := by
  have := planRoute_classify_mono; unfold EvalBody.algorithmOfValue; mono_tac

theorem EvalBody.capturedCallee_mono (callee : Nat) :
    monotone (fun rec : EvalRec => EvalBody.capturedCallee rec callee) := by
  unfold EvalBody.capturedCallee; mono_tac

theorem EvalBody.referenceReceiverValue_mono (target : Expr) (targetAlg : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    monotone (fun rec : EvalRec => EvalBody.referenceReceiverValue rec target targetAlg ctx env) := by
  unfold EvalBody.referenceReceiverValue; mono_tac

theorem EvalBody.algorithmCalleeOf_mono (receiver : Expr) (ctx : EvalCtx) (env : ValEnv) :
    monotone (fun rec : EvalRec => EvalBody.algorithmCalleeOf rec receiver ctx env) := by
  have := planRoute_classify_mono; unfold EvalBody.algorithmCalleeOf; mono_tac

-- CACHE-PUB-1: the origin-binding helpers the dispatch calls with the evaluator answer.
theorem EvalBody.publicationBinding?_mono (owner : Algorithm) (binding : PropDef) (wired : Algorithm) (ctx : EvalCtx) (invoked : Algorithm) :
    monotone (fun rec : EvalRec => EvalBody.publicationBinding? rec owner binding wired ctx invoked) := by
  unfold EvalBody.publicationBinding?; mono_tac

theorem EvalBody.writtenCalleeBinding?_mono (callee : Expr) (caller : EvalCtx) (invoked : Algorithm) :
    monotone (fun rec : EvalRec => EvalBody.writtenCalleeBinding? rec callee caller invoked) := by
  have := EvalBody.publicationBinding?_mono
  unfold EvalBody.writtenCalleeBinding?; mono_tac

theorem EvalBody.cellCalleeBinding?_mono (address : Nat) (invoked : Algorithm) :
    monotone (fun rec : EvalRec => EvalBody.cellCalleeBinding? rec address invoked) := by
  have := EvalBody.writtenCalleeBinding?_mono
  unfold EvalBody.cellCalleeBinding?; mono_tac

theorem EvalBody.originBinding?_mono (origin : CalleeOrigin) (ctx : EvalCtx) (invoked : Algorithm) :
    monotone (fun rec : EvalRec => EvalBody.originBinding? rec origin ctx invoked) := by
  have := EvalBody.publicationBinding?_mono
  have := EvalBody.writtenCalleeBinding?_mono
  have := EvalBody.cellCalleeBinding?_mono
  unfold EvalBody.originBinding?; mono_tac

theorem EvalBody.evalSuppliedCallCounted_mono (origin : CalleeOrigin) (callee : Algorithm) (cells : List NeedSupply.Sourced) (ctx : EvalCtx) (env : ValEnv) (calleeName : String) :
    monotone (fun rec : EvalRec => EvalBody.evalSuppliedCallCounted rec origin callee cells ctx env calleeName) := by
  have := EvalBody.originBinding?_mono origin ctx callee
  unfold EvalBody.evalSuppliedCallCounted; mono_tac

theorem EvalBody.evalNeedUserSupplyOutput_mono (callee : Algorithm) (cells : List Nat) (ctx : EvalCtx) (env : ValEnv) :
    monotone (fun rec : EvalRec => EvalBody.evalNeedUserSupplyOutput rec callee cells ctx env) := by
  unfold EvalBody.evalNeedUserSupplyOutput; mono_tac

theorem EvalBody.evalNeedUserSupply_mono (callee : Algorithm) (cells : List Nat) (ctx : EvalCtx) (env : ValEnv) :
    monotone (fun rec : EvalRec => EvalBody.evalNeedUserSupply rec callee cells ctx env) := by
  have := EvalBody.evalNeedUserSupplyOutput_mono callee cells ctx env
  unfold EvalBody.evalNeedUserSupply; mono_tac

theorem EvalBody.evalNeedFamilySupply_mono (callee : Algorithm) (cells : List Nat) (ctx : EvalCtx) (env : ValEnv) (calleeName : String) :
    monotone (fun rec : EvalRec => EvalBody.evalNeedFamilySupply rec callee cells ctx env calleeName) := by
  unfold EvalBody.evalNeedFamilySupply; mono_tac

theorem EvalBody.invokeNeed_mono (arg : ResolvedArgumentAlgorithm) :
    monotone (fun rec : EvalRec => EvalBody.invokeNeed rec arg) := by
  unfold EvalBody.invokeNeed; mono_tac

theorem EvalBody.argumentNeed_mono (arg : ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) :
    monotone (fun rec : EvalRec => EvalBody.argumentNeed rec arg ctx env) := by
  unfold EvalBody.argumentNeed; mono_tac

theorem EvalBody.runNeedStepSlots_mono (step : Algorithm) (ctx : EvalCtx) (env : ValEnv) (cells : List Nat) (stepName : String) :
    monotone (fun rec : EvalRec => EvalBody.runNeedStepSlots rec step ctx env cells stepName) := by
  unfold EvalBody.runNeedStepSlots EvalBody.runNeedStepWith; mono_tac

theorem EvalBody.runNeedWhileRound_mono (step : Algorithm) (ctx : EvalCtx) (env : ValEnv) (cells : List Nat) (stepName : String) :
    monotone (fun rec : EvalRec => EvalBody.runNeedWhileRound rec step ctx env cells stepName) := by
  unfold EvalBody.runNeedWhileRound EvalBody.runNeedStepWith; mono_tac

theorem EvalBody.evalAlgOutputCore_mono (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    monotone (fun rec : EvalRec => EvalBody.evalAlgOutputCore rec a ctx env) := by
  unfold EvalBody.evalAlgOutputCore; mono_tac

theorem EvalBody.evalAlgOutput_mono (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    monotone (fun rec : EvalRec => EvalBody.evalAlgOutput rec a ctx env) := by
  unfold EvalBody.evalAlgOutput; mono_tac

theorem EvalBody.evalProgramOutput_mono (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    monotone (fun rec : EvalRec => EvalBody.evalProgramOutput rec a ctx env) := by
  unfold EvalBody.evalProgramOutput; mono_tac

theorem EvalBody.evalAlgOutputSlots_mono (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    monotone (fun rec : EvalRec => EvalBody.evalAlgOutputSlots rec a ctx env) := by
  unfold EvalBody.evalAlgOutputSlots ActivatedBody.readRows; mono_tac

theorem EvalBody.formOutputRow_mono (ctx : EvalCtx) (env : ValEnv) (e : Expr) :
    monotone (fun rec : EvalRec => EvalBody.formOutputRow rec ctx env e) := by
  unfold EvalBody.formOutputRow; mono_tac

theorem EvalBody.whileVerdictSlots_mono (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    monotone (fun rec : EvalRec => EvalBody.whileVerdictSlots rec a ctx env) := by
  unfold EvalBody.whileVerdictSlots ActivatedBody.readRows; mono_tac

theorem EvalBody.evalSequenceCallbackCall_mono (callee : Algorithm) (item : CountedResult) (ctx : EvalCtx) (env : ValEnv) (calleeName : String) :
    monotone (fun rec : EvalRec => EvalBody.evalSequenceCallbackCall rec callee item ctx env calleeName) := by
  unfold EvalBody.evalSequenceCallbackCall; mono_tac

theorem EvalBody.evalSequenceCallbackCallCounted_mono (callee : Algorithm) (item : CountedResult) (ctx : EvalCtx) (env : ValEnv) (calleeName : String) :
    monotone (fun rec : EvalRec => EvalBody.evalSequenceCallbackCallCounted rec callee item ctx env calleeName) := by
  unfold EvalBody.evalSequenceCallbackCallCounted; mono_tac

theorem EvalBody.evalAlgOutputPreparedCore_mono (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    monotone (fun rec : EvalRec => EvalBody.evalAlgOutputPreparedCore rec a ctx env) := by
  unfold EvalBody.evalAlgOutputPreparedCore; mono_tac

theorem EvalBody.evalOutputRowsPreparedCore_mono (rows : OutputBundle) (rowCtx : EvalCtx) (env : ValEnv) :
    monotone (fun rec : EvalRec => EvalBody.evalOutputRowsPreparedCore rec rows rowCtx env) := by
  unfold EvalBody.evalOutputRowsPreparedCore; mono_tac

theorem EvalBody.evalCapturePreparedCore_mono (rows : OutputBundle) (ctx : EvalCtx) (env : ValEnv) :
    monotone (fun rec : EvalRec => EvalBody.evalCapturePreparedCore rec rows ctx env) := by
  unfold EvalBody.evalCapturePreparedCore; mono_tac

theorem EvalBody.evalCaptureCountedCore_mono (rows : OutputBundle) (ctx : EvalCtx) (env : ValEnv) :
    monotone (fun rec : EvalRec => EvalBody.evalCaptureCountedCore rec rows ctx env) := by
  unfold EvalBody.evalCaptureCountedCore; mono_tac

theorem EvalBody.evalCaptureValue_mono (rows : OutputBundle) (ctx : EvalCtx) (env : ValEnv) :
    monotone (fun rec : EvalRec => EvalBody.evalCaptureValue rec rows ctx env) := by
  unfold EvalBody.evalCaptureValue; mono_tac

theorem EvalBody.evalAlgOutputCountedCore_mono (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    monotone (fun rec : EvalRec => EvalBody.evalAlgOutputCountedCore rec a ctx env) := by
  unfold EvalBody.evalAlgOutputCountedCore; mono_tac

theorem EvalBody.evalAlgOutputCounted_mono (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    monotone (fun rec : EvalRec => EvalBody.evalAlgOutputCounted rec a ctx env) := by
  unfold EvalBody.evalAlgOutputCounted; mono_tac

theorem EvalBody.evalZeroArgumentDemandOutputCounted_mono (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    monotone (fun rec : EvalRec => EvalBody.evalZeroArgumentDemandOutputCounted rec a ctx env) := by
  unfold EvalBody.evalZeroArgumentDemandOutputCounted; mono_tac

theorem EvalBody.evalZeroArgumentDemandOutput_mono (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    monotone (fun rec : EvalRec => EvalBody.evalZeroArgumentDemandOutput rec a ctx env) := by
  unfold EvalBody.evalZeroArgumentDemandOutput; mono_tac

theorem EvalBody.evalArgumentValueCounted_mono (arg : ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) :
    monotone (fun rec : EvalRec => EvalBody.evalArgumentValueCounted rec arg ctx env) := by
  unfold EvalBody.evalArgumentValueCounted; mono_tac

theorem EvalBody.evalArgumentValue_mono (arg : ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) :
    monotone (fun rec : EvalRec => EvalBody.evalArgumentValue rec arg ctx env) := by
  unfold EvalBody.evalArgumentValue; mono_tac

theorem EvalBody.zeroArgPropertyCalculation_mono (request : ZeroArgPropertyRequest) (resolvedAlgorithm : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    monotone (fun rec : EvalRec => EvalBody.zeroArgPropertyCalculation rec request resolvedAlgorithm ctx env) := by
  have := EvalBody.evalNeedUserSupplyOutput_mono resolvedAlgorithm [] ctx env
  unfold EvalBody.zeroArgPropertyCalculation; mono_tac

theorem EvalBody.evalZeroArgPropertyAccessCounted_mono (accessKind : ZeroArgPropertyAccessKind) (owner : Algorithm) (binding : PropDef) (resolvedAlgorithm : Algorithm) (ctx : EvalCtx) (env : ValEnv) (request : ZeroArgPropertyRequest) :
    monotone (fun rec : EvalRec => EvalBody.evalZeroArgPropertyAccessCounted rec accessKind owner binding resolvedAlgorithm ctx env request) := by
  have := EvalBody.zeroArgPropertyCalculation_mono request resolvedAlgorithm ctx env
  unfold EvalBody.evalZeroArgPropertyAccessCounted; mono_tac

theorem EvalBody.evalZeroArgPropertyAccess_mono (accessKind : ZeroArgPropertyAccessKind) (owner : Algorithm) (binding : PropDef) (resolvedAlgorithm : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    monotone (fun rec : EvalRec => EvalBody.evalZeroArgPropertyAccess rec accessKind owner binding resolvedAlgorithm ctx env) := by
  unfold EvalBody.evalZeroArgPropertyAccess; mono_tac

theorem EvalBody.evalConditionalCallbackCallCounted_mono (callee : Algorithm) (args : List CountedResult) (ctx : EvalCtx) (env : ValEnv) (calleeName : String) :
    monotone (fun rec : EvalRec => EvalBody.evalConditionalCallbackCallCounted rec callee args ctx env calleeName) := by
  unfold EvalBody.evalConditionalCallbackCallCounted; mono_tac

theorem EvalBody.evalUserCallbackCallCounted_mono (callee : Algorithm) (args : List CountedResult) (ctx : EvalCtx) (env : ValEnv) :
    monotone (fun rec : EvalRec => EvalBody.evalUserCallbackCallCounted rec callee args ctx env) := by
  unfold EvalBody.evalUserCallbackCallCounted; mono_tac

theorem EvalBody.evalResolvedCallbackCallCounted_mono (callee : Algorithm) (args : List CountedResult) (ctx : EvalCtx) (env : ValEnv) (calleeName : String) :
    monotone (fun rec : EvalRec => EvalBody.evalResolvedCallbackCallCounted rec callee args ctx env calleeName) := by
  unfold EvalBody.evalResolvedCallbackCallCounted; mono_tac

theorem EvalBody.evalResolvedCallbackCall_mono (callee : Algorithm) (args : List CountedResult) (ctx : EvalCtx) (env : ValEnv) (calleeName : String) :
    monotone (fun rec : EvalRec => EvalBody.evalResolvedCallbackCall rec callee args ctx env calleeName) := by
  unfold EvalBody.evalResolvedCallbackCall; mono_tac

theorem EvalBody.evalSequenceReduceStepCounted_mono (callee : Algorithm) (element : CountedResult) (accumulator : Result) (ctx : EvalCtx) (env : ValEnv) (calleeName : String) :
    monotone (fun rec : EvalRec => EvalBody.evalSequenceReduceStepCounted rec callee element accumulator ctx env calleeName) := by
  unfold EvalBody.evalSequenceReduceStepCounted; mono_tac

theorem EvalBody.demandSequenceBuiltinCallItemValue_mono (item : CallableCallItem) (ctx : EvalCtx) (env : ValEnv) :
    monotone (fun rec : EvalRec => EvalBody.demandSequenceBuiltinCallItemValue rec item ctx env) := by
  unfold EvalBody.demandSequenceBuiltinCallItemValue; mono_tac

theorem EvalBody.bindSequenceBuiltinArguments_mono (b : Builtin) (metadata : SequenceBuiltinMetadata) (args : List ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) :
    monotone (fun rec : EvalRec => EvalBody.bindSequenceBuiltinArguments rec b metadata args ctx env) := by
  unfold EvalBody.bindSequenceBuiltinArguments; mono_tac

theorem EvalBody.evalReduceCounted_mono (collection : List CountedResult) (stepAlg : Algorithm) (initial : Result) (ctx : EvalCtx) (env : ValEnv) :
    monotone (fun rec : EvalRec => EvalBody.evalReduceCounted rec collection stepAlg initial ctx env) := by
  unfold EvalBody.evalReduceCounted; mono_tac

theorem EvalBody.evalFilterCounted_mono (items : List CountedResult) (predicateAlg : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    monotone (fun rec : EvalRec => EvalBody.evalFilterCounted rec items predicateAlg ctx env) := by
  unfold EvalBody.evalFilterCounted; mono_tac

theorem EvalBody.evalMapCounted_mono (collection : List CountedResult) (transformAlg : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    monotone (fun rec : EvalRec => EvalBody.evalMapCounted rec collection transformAlg ctx env) := by
  unfold EvalBody.evalMapCounted; mono_tac

theorem EvalBody.applyBuiltinCountedSequence_mono (b : Builtin) (metadata : SequenceBuiltinMetadata) (args : List ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) :
    monotone (fun rec : EvalRec => EvalBody.applyBuiltinCountedSequence rec b metadata args ctx env) := by
  unfold EvalBody.applyBuiltinCountedSequence; mono_tac

theorem EvalBody.applyBuiltinCounted_mono (b : Builtin) (args : List ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) :
    monotone (fun rec : EvalRec => EvalBody.applyBuiltinCounted rec b args ctx env) := by
  have := planRoute_classify_mono; unfold EvalBody.applyBuiltinCounted; mono_tac

theorem EvalBody.applyBuiltin_mono (b : Builtin) (args : List ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) :
    monotone (fun rec : EvalRec => EvalBody.applyBuiltin rec b args ctx env) := by
  unfold EvalBody.applyBuiltin; mono_tac

theorem EvalBody.applyBuiltinCountedResolved_mono (b : Builtin) (args : List ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) :
    monotone (fun rec : EvalRec => EvalBody.applyBuiltinCountedResolved rec b args ctx env) := by
  unfold EvalBody.applyBuiltinCountedResolved; mono_tac

theorem EvalBody.evalExplicitSequenceValueItems_mono (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    monotone (fun rec : EvalRec => EvalBody.evalExplicitSequenceValueItems rec a ctx env) := by
  unfold EvalBody.evalExplicitSequenceValueItems; mono_tac

theorem EvalBody.evalExplicitSequenceValueRowSlots_mono (rows : OutputBundle) (rowCtx : EvalCtx) (env : ValEnv) :
    monotone (fun rec : EvalRec => EvalBody.evalExplicitSequenceValueRowSlots rec rows rowCtx env) := by
  unfold EvalBody.evalExplicitSequenceValueRowSlots; mono_tac

theorem EvalBody.evalExplicitSequenceValueExprSlots_mono (expr : Expr) (ctx : EvalCtx) (env : ValEnv) :
    monotone (fun rec : EvalRec => EvalBody.evalExplicitSequenceValueExprSlots rec expr ctx env) := by
  unfold EvalBody.evalExplicitSequenceValueExprSlots; mono_tac

theorem EvalBody.evalUserCallCounted_mono (callee : Algorithm) (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) :
    monotone (fun rec : EvalRec => EvalBody.evalUserCallCounted rec callee args ctx env) := by
  unfold EvalBody.evalUserCallCounted; mono_tac

theorem EvalBody.evalConditionalCallCounted_mono (callee : Algorithm) (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) (calleeName : String) :
    monotone (fun rec : EvalRec => EvalBody.evalConditionalCallCounted rec callee args ctx env calleeName) := by
  unfold EvalBody.evalConditionalCallCounted; mono_tac

theorem EvalBody.evalResolvedCall_mono (callee : Algorithm) (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) (calleeName : String) :
    monotone (fun rec : EvalRec => EvalBody.evalResolvedCall rec callee args ctx env calleeName) := by
  unfold EvalBody.evalResolvedCall; mono_tac

theorem EvalBody.evalResolvedCallCounted_mono (callee : Algorithm) (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) (calleeName : String) (origin : CalleeOrigin) :
    monotone (fun rec : EvalRec => EvalBody.evalResolvedCallCounted rec callee args ctx env calleeName origin) := by
  unfold EvalBody.evalResolvedCallCounted; mono_tac

theorem EvalBody.evalCallCountedExpr_mono (f : Expr) (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) :
    monotone (fun rec : EvalRec => EvalBody.evalCallCountedExpr rec f args ctx env) := by
  unfold EvalBody.evalCallCountedExpr; mono_tac

theorem EvalBody.callLexicalWithReceiverCounted_mono (name : Ident) (receiver : Expr) (fallback : Expr) (extraArgs : Option OutputBundle) (ctx : EvalCtx) (env : ValEnv) :
    monotone (fun rec : EvalRec => EvalBody.callLexicalWithReceiverCounted rec name receiver fallback extraArgs ctx env) := by
  unfold EvalBody.callLexicalWithReceiverCounted; mono_tac

theorem EvalBody.rejectDotStringIntrinsicArguments_mono (argsOpt : Option OutputBundle) (ctx : EvalCtx) (env : ValEnv) :
    monotone (fun rec : EvalRec => EvalBody.rejectDotStringIntrinsicArguments rec argsOpt ctx env) := by
  unfold EvalBody.rejectDotStringIntrinsicArguments; mono_tac

theorem EvalBody.evalDotStringReceiverValue_mono (target : Expr) (targetAlg : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    monotone (fun rec : EvalRec => EvalBody.evalDotStringReceiverValue rec target targetAlg ctx env) := by
  unfold EvalBody.evalDotStringReceiverValue; mono_tac

theorem EvalBody.evalDotCallCounted_mono (target : Expr) (name : Ident) (fallback : Expr) (argsOpt : Option OutputBundle) (ctx : EvalCtx) (env : ValEnv) :
    monotone (fun rec : EvalRec => EvalBody.evalDotCallCounted rec target name fallback argsOpt ctx env) := by
  unfold EvalBody.evalDotCallCounted; mono_tac

theorem EvalBody.rejectInvokeIntrinsicArguments_mono (argsOpt : Option OutputBundle) (ctx : EvalCtx) (env : ValEnv) :
    monotone (fun rec : EvalRec => EvalBody.rejectInvokeIntrinsicArguments rec argsOpt ctx env) := by
  unfold EvalBody.rejectInvokeIntrinsicArguments; mono_tac

theorem EvalBody.invokeCallReferenceValue_mono (val : Result) :
    monotone (fun rec : EvalRec => EvalBody.invokeCallReferenceValue rec val) := by
  unfold EvalBody.invokeCallReferenceValue; mono_tac

theorem EvalBody.argumentViewCells_mono (a : Nat) :
    monotone (fun rec : EvalRec => EvalBody.argumentViewCells rec a) := by
  have := planRoute_classify_mono; unfold EvalBody.argumentViewCells; mono_tac

theorem EvalBody.evalArgumentViewBuiltin_mono (b : Builtin) (a : Nat) :
    monotone (fun rec : EvalRec => EvalBody.evalArgumentViewBuiltin rec b a) := by
  unfold EvalBody.evalArgumentViewBuiltin; mono_tac

theorem EvalBody.evalSequenceSpreadOperandValue_mono (e : Expr) (ctx : EvalCtx) (env : ValEnv) :
    monotone (fun rec : EvalRec => EvalBody.evalSequenceSpreadOperandValue rec e ctx env) := by
  unfold EvalBody.evalSequenceSpreadOperandValue; mono_tac

theorem EvalBody.evalSequenceSpreadCounted_mono (e : Expr) (ctx : EvalCtx) (env : ValEnv) :
    monotone (fun rec : EvalRec => EvalBody.evalSequenceSpreadCounted rec e ctx env) := by
  unfold EvalBody.evalSequenceSpreadCounted; mono_tac

theorem EvalBody.evalSupplySpread_mono (e : Expr) (ctx : EvalCtx) (env : ValEnv) :
    monotone (fun rec : EvalRec => EvalBody.evalSupplySpread rec e ctx env) := by
  have := planRoute_classify_mono; unfold EvalBody.evalSupplySpread; mono_tac

theorem EvalBody.evalListLiteralCounted_mono (elements : List Expr) (ctx : EvalCtx) (env : ValEnv) :
    monotone (fun rec : EvalRec => EvalBody.evalListLiteralCounted rec elements ctx env) := by
  unfold EvalBody.evalListLiteralCounted; mono_tac

theorem EvalBody.evalSequenceConstructCounted_mono (e : Expr) (ctx : EvalCtx) (env : ValEnv) :
    monotone (fun rec : EvalRec => EvalBody.evalSequenceConstructCounted rec e ctx env) := by
  unfold EvalBody.evalSequenceConstructCounted; mono_tac

theorem EvalBody.evalUnaryCounted_mono (op : UnaryOp) (operand : Expr) (ctx : EvalCtx) (env : ValEnv) :
    monotone (fun rec : EvalRec => EvalBody.evalUnaryCounted rec op operand ctx env) := by
  unfold EvalBody.evalUnaryCounted; mono_tac

theorem EvalBody.evalBinaryCounted_mono (op : BinaryOp) (a b : Expr) (ctx : EvalCtx) (env : ValEnv) :
    monotone (fun rec : EvalRec => EvalBody.evalBinaryCounted rec op a b ctx env) := by
  unfold EvalBody.evalBinaryCounted; mono_tac

theorem EvalBody.evalComparisonCounted_mono (first : Expr) (links : List ComparisonLink) (ctx : EvalCtx) (env : ValEnv) :
    monotone (fun rec : EvalRec => EvalBody.evalComparisonCounted rec first links ctx env) := by
  unfold EvalBody.evalComparisonCounted; mono_tac

theorem EvalBody.evalComparisonLinksCounted_mono (previousExpr : Expr) (previous : Result) (holds : Bool) (links : List ComparisonLink) (ctx : EvalCtx) (env : ValEnv) :
    monotone (fun rec : EvalRec => EvalBody.evalComparisonLinksCounted rec previousExpr previous holds links ctx env) := by
  unfold EvalBody.evalComparisonLinksCounted; mono_tac

theorem EvalBody.evalCounted_mono (e : Expr) (ctx : EvalCtx) (env : ValEnv) :
    monotone (fun rec : EvalRec => EvalBody.evalCounted rec e ctx env) := by
  unfold EvalBody.evalCounted; mono_tac

theorem EvalBody.evalUserCall_mono (callee : Algorithm) (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) :
    monotone (fun rec : EvalRec => EvalBody.evalUserCall rec callee args ctx env) := by
  unfold EvalBody.evalUserCall; mono_tac

theorem EvalBody.evalConditionalCall_mono (callee : Algorithm) (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) (calleeName : String) :
    monotone (fun rec : EvalRec => EvalBody.evalConditionalCall rec callee args ctx env calleeName) := by
  unfold EvalBody.evalConditionalCall; mono_tac

theorem EvalBody.evalCallExpr_mono (f : Expr) (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) :
    monotone (fun rec : EvalRec => EvalBody.evalCallExpr rec f args ctx env) := by
  unfold EvalBody.evalCallExpr; mono_tac

theorem EvalBody.evalDotCall_mono (target : Expr) (name : Ident) (fallback : Expr) (argsOpt : Option OutputBundle) (ctx : EvalCtx) (env : ValEnv) :
    monotone (fun rec : EvalRec => EvalBody.evalDotCall rec target name fallback argsOpt ctx env) := by
  unfold EvalBody.evalDotCall; mono_tac

theorem EvalBody.eval_mono (e : Expr) (ctx : EvalCtx) (env : ValEnv) :
    monotone (fun rec : EvalRec => EvalBody.eval rec e ctx env) := by
  unfold EvalBody.eval; mono_tac

theorem evalStep_monotone : monotone evalStep := by
  intro r₁ r₂ h c
  cases c with
  | whileLoop step ctx env stepName cells => exact EvalBody.whileLoop_mono step ctx env stepName cells _ _ h
  | aliasStepIsRuntime step target ctx => exact EvalBody.aliasStepIsRuntime_mono step target ctx _ _ h
  | aliasValue wired ctx env => exact EvalBody.aliasValue_mono wired ctx env _ _ h
  | resolveAliasChase callable a ctx visited projectedFrom => exact EvalBody.resolveAliasChase_mono callable a ctx visited projectedFrom _ _ h
  | resolveAliasTarget a ctx => exact EvalBody.resolveAliasTarget_mono a ctx _ _ h
  | resolveAliasValueTarget a ctx => exact EvalBody.resolveAliasValueTarget_mono a ctx _ _ h
  | lookupLexicalProperty a name ctx => exact EvalBody.lookupLexicalProperty_mono a name ctx _ _ h
  | lookupLexicalValueProperty a name ctx => exact EvalBody.lookupLexicalValueProperty_mono a name ctx _ _ h
  | lookupLexical a name ctx => exact EvalBody.lookupLexical_mono a name ctx _ _ h
  | needPlanNormalizeCallee callee ctx => exact EvalBody.needPlanNormalizeCallee_mono callee ctx _ _ h
  | resolveAlg e ctx => exact EvalBody.resolveAlg_mono e ctx _ _ h
  | projectNeedCallable address => exact EvalBody.projectNeedCallable_mono address _ _ h
  | projectNeedWrittenAt address source caller => exact EvalBody.projectNeedWrittenAt_mono address source caller _ _ h
  | linkCallable address => exact EvalBody.linkCallable_mono address _ _ h
  | projectParameterCallable x ctx => exact EvalBody.projectParameterCallable_mono x ctx _ _ h
  | projectNeedWritten source caller => exact EvalBody.projectNeedWritten_mono source caller _ _ h
  | projectNeedStructuralMember source ctx => exact EvalBody.projectNeedStructuralMember_mono source ctx _ _ h
  | resolveCalleeAlg f ctx => exact EvalBody.resolveCalleeAlg_mono f ctx _ _ h
  | expectPreparedSequenceBuiltinAlgorithmSuffixArg b descriptors args index => exact EvalBody.expectPreparedSequenceBuiltinAlgorithmSuffixArg_mono b descriptors args index _ _ h
  | resolveDotReceiver? e ctx => exact EvalBody.resolveDotReceiver?_mono e ctx _ _ h
  | resolveDotReceiver e ctx => exact EvalBody.resolveDotReceiver_mono e ctx _ _ h
  | algorithmIntrinsicRoute receiver ctx => exact EvalBody.algorithmIntrinsicRoute_mono receiver ctx _ _ h
  | demandNeedRecursive address => exact EvalBody.demandNeedRecursive_mono address _ _ h
  | evalSuppliedAt address e ctx env => exact EvalBody.evalSuppliedAt_mono address e ctx env _ _ h
  | linkValue address => exact EvalBody.linkValue_mono address _ _ h
  | algorithmOfValue val argsOpt ctx env => exact EvalBody.algorithmOfValue_mono val argsOpt ctx env _ _ h
  | capturedCallee callee => exact EvalBody.capturedCallee_mono callee _ _ h
  | referenceReceiverValue target targetAlg ctx env => exact EvalBody.referenceReceiverValue_mono target targetAlg ctx env _ _ h
  | algorithmCalleeOf receiver ctx env => exact EvalBody.algorithmCalleeOf_mono receiver ctx env _ _ h
  | evalSuppliedCallCounted origin callee cells ctx env calleeName => exact EvalBody.evalSuppliedCallCounted_mono origin callee cells ctx env calleeName _ _ h
  | evalNeedUserSupply callee cells ctx env => exact EvalBody.evalNeedUserSupply_mono callee cells ctx env _ _ h
  | evalNeedFamilySupply callee cells ctx env calleeName => exact EvalBody.evalNeedFamilySupply_mono callee cells ctx env calleeName _ _ h
  | invokeNeed arg => exact EvalBody.invokeNeed_mono arg _ _ h
  | argumentNeed arg ctx env => exact EvalBody.argumentNeed_mono arg ctx env _ _ h
  | runNeedStepSlots step ctx env cells stepName => exact EvalBody.runNeedStepSlots_mono step ctx env cells stepName _ _ h
  | runNeedWhileRound step ctx env cells stepName => exact EvalBody.runNeedWhileRound_mono step ctx env cells stepName _ _ h
  | evalAlgOutputCore a ctx env => exact EvalBody.evalAlgOutputCore_mono a ctx env _ _ h
  | evalAlgOutput a ctx env => exact EvalBody.evalAlgOutput_mono a ctx env _ _ h
  | evalProgramOutput a ctx env => exact EvalBody.evalProgramOutput_mono a ctx env _ _ h
  | evalAlgOutputSlots a ctx env => exact EvalBody.evalAlgOutputSlots_mono a ctx env _ _ h
  | formOutputRow ctx env e => exact EvalBody.formOutputRow_mono ctx env e _ _ h
  | whileVerdictSlots a ctx env => exact EvalBody.whileVerdictSlots_mono a ctx env _ _ h
  | evalSequenceCallbackCall callee item ctx env calleeName => exact EvalBody.evalSequenceCallbackCall_mono callee item ctx env calleeName _ _ h
  | evalSequenceCallbackCallCounted callee item ctx env calleeName => exact EvalBody.evalSequenceCallbackCallCounted_mono callee item ctx env calleeName _ _ h
  | evalAlgOutputPreparedCore a ctx env => exact EvalBody.evalAlgOutputPreparedCore_mono a ctx env _ _ h
  | evalOutputRowsPreparedCore rows rowCtx env => exact EvalBody.evalOutputRowsPreparedCore_mono rows rowCtx env _ _ h
  | evalCapturePreparedCore rows ctx env => exact EvalBody.evalCapturePreparedCore_mono rows ctx env _ _ h
  | evalCaptureCountedCore rows ctx env => exact EvalBody.evalCaptureCountedCore_mono rows ctx env _ _ h
  | evalCaptureValue rows ctx env => exact EvalBody.evalCaptureValue_mono rows ctx env _ _ h
  | evalAlgOutputCountedCore a ctx env => exact EvalBody.evalAlgOutputCountedCore_mono a ctx env _ _ h
  | evalAlgOutputCounted a ctx env => exact EvalBody.evalAlgOutputCounted_mono a ctx env _ _ h
  | evalZeroArgumentDemandOutputCounted a ctx env => exact EvalBody.evalZeroArgumentDemandOutputCounted_mono a ctx env _ _ h
  | evalZeroArgumentDemandOutput a ctx env => exact EvalBody.evalZeroArgumentDemandOutput_mono a ctx env _ _ h
  | evalArgumentValueCounted arg ctx env => exact EvalBody.evalArgumentValueCounted_mono arg ctx env _ _ h
  | evalArgumentValue arg ctx env => exact EvalBody.evalArgumentValue_mono arg ctx env _ _ h
  | evalZeroArgPropertyAccessCounted accessKind owner binding resolvedAlgorithm ctx env request => exact EvalBody.evalZeroArgPropertyAccessCounted_mono accessKind owner binding resolvedAlgorithm ctx env request _ _ h
  | evalZeroArgPropertyAccess accessKind owner binding resolvedAlgorithm ctx env => exact EvalBody.evalZeroArgPropertyAccess_mono accessKind owner binding resolvedAlgorithm ctx env _ _ h
  | evalConditionalCallbackCallCounted callee args ctx env calleeName => exact EvalBody.evalConditionalCallbackCallCounted_mono callee args ctx env calleeName _ _ h
  | evalUserCallbackCallCounted callee args ctx env => exact EvalBody.evalUserCallbackCallCounted_mono callee args ctx env _ _ h
  | evalResolvedCallbackCallCounted callee args ctx env calleeName => exact EvalBody.evalResolvedCallbackCallCounted_mono callee args ctx env calleeName _ _ h
  | evalResolvedCallbackCall callee args ctx env calleeName => exact EvalBody.evalResolvedCallbackCall_mono callee args ctx env calleeName _ _ h
  | evalSequenceReduceStepCounted callee element accumulator ctx env calleeName => exact EvalBody.evalSequenceReduceStepCounted_mono callee element accumulator ctx env calleeName _ _ h
  | demandSequenceBuiltinCallItemValue item ctx env => exact EvalBody.demandSequenceBuiltinCallItemValue_mono item ctx env _ _ h
  | bindSequenceBuiltinArguments b metadata args ctx env => exact EvalBody.bindSequenceBuiltinArguments_mono b metadata args ctx env _ _ h
  | evalReduceCounted collection stepAlg initial ctx env => exact EvalBody.evalReduceCounted_mono collection stepAlg initial ctx env _ _ h
  | evalFilterCounted items predicateAlg ctx env => exact EvalBody.evalFilterCounted_mono items predicateAlg ctx env _ _ h
  | evalMapCounted collection transformAlg ctx env => exact EvalBody.evalMapCounted_mono collection transformAlg ctx env _ _ h
  | applyBuiltinCountedSequence b metadata args ctx env => exact EvalBody.applyBuiltinCountedSequence_mono b metadata args ctx env _ _ h
  | applyBuiltinCounted b args ctx env => exact EvalBody.applyBuiltinCounted_mono b args ctx env _ _ h
  | applyBuiltin b args ctx env => exact EvalBody.applyBuiltin_mono b args ctx env _ _ h
  | applyBuiltinCountedResolved b args ctx env => exact EvalBody.applyBuiltinCountedResolved_mono b args ctx env _ _ h
  | evalExplicitSequenceValueItems a ctx env => exact EvalBody.evalExplicitSequenceValueItems_mono a ctx env _ _ h
  | evalExplicitSequenceValueRowSlots rows rowCtx env => exact EvalBody.evalExplicitSequenceValueRowSlots_mono rows rowCtx env _ _ h
  | evalExplicitSequenceValueExprSlots expr ctx env => exact EvalBody.evalExplicitSequenceValueExprSlots_mono expr ctx env _ _ h
  | evalUserCallCounted callee args ctx env => exact EvalBody.evalUserCallCounted_mono callee args ctx env _ _ h
  | evalConditionalCallCounted callee args ctx env calleeName => exact EvalBody.evalConditionalCallCounted_mono callee args ctx env calleeName _ _ h
  | evalResolvedCall callee args ctx env calleeName => exact EvalBody.evalResolvedCall_mono callee args ctx env calleeName _ _ h
  | evalResolvedCallCounted callee args ctx env calleeName origin => exact EvalBody.evalResolvedCallCounted_mono callee args ctx env calleeName origin _ _ h
  | evalCallCountedExpr f args ctx env => exact EvalBody.evalCallCountedExpr_mono f args ctx env _ _ h
  | callLexicalWithReceiverCounted name receiver fallback extraArgs ctx env => exact EvalBody.callLexicalWithReceiverCounted_mono name receiver fallback extraArgs ctx env _ _ h
  | rejectDotStringIntrinsicArguments argsOpt ctx env => exact EvalBody.rejectDotStringIntrinsicArguments_mono argsOpt ctx env _ _ h
  | evalDotStringReceiverValue target targetAlg ctx env => exact EvalBody.evalDotStringReceiverValue_mono target targetAlg ctx env _ _ h
  | evalDotCallCounted target name fallback argsOpt ctx env => exact EvalBody.evalDotCallCounted_mono target name fallback argsOpt ctx env _ _ h
  | rejectInvokeIntrinsicArguments argsOpt ctx env => exact EvalBody.rejectInvokeIntrinsicArguments_mono argsOpt ctx env _ _ h
  | invokeCallReferenceValue val => exact EvalBody.invokeCallReferenceValue_mono val _ _ h
  | argumentViewCells a => exact EvalBody.argumentViewCells_mono a _ _ h
  | evalArgumentViewBuiltin b a => exact EvalBody.evalArgumentViewBuiltin_mono b a _ _ h
  | evalSequenceSpreadOperandValue e ctx env => exact EvalBody.evalSequenceSpreadOperandValue_mono e ctx env _ _ h
  | evalSequenceSpreadCounted e ctx env => exact EvalBody.evalSequenceSpreadCounted_mono e ctx env _ _ h
  | evalSupplySpread e ctx env => exact EvalBody.evalSupplySpread_mono e ctx env _ _ h
  | evalListLiteralCounted elements ctx env => exact EvalBody.evalListLiteralCounted_mono elements ctx env _ _ h
  | evalSequenceConstructCounted e ctx env => exact EvalBody.evalSequenceConstructCounted_mono e ctx env _ _ h
  | evalUnaryCounted op operand ctx env => exact EvalBody.evalUnaryCounted_mono op operand ctx env _ _ h
  | evalBinaryCounted op a b ctx env => exact EvalBody.evalBinaryCounted_mono op a b ctx env _ _ h
  | evalComparisonCounted first links ctx env => exact EvalBody.evalComparisonCounted_mono first links ctx env _ _ h
  | evalComparisonLinksCounted previousExpr previous holds links ctx env => exact EvalBody.evalComparisonLinksCounted_mono previousExpr previous holds links ctx env _ _ h
  | evalCounted e ctx env => exact EvalBody.evalCounted_mono e ctx env _ _ h
  | evalUserCall callee args ctx env => exact EvalBody.evalUserCall_mono callee args ctx env _ _ h
  | evalConditionalCall callee args ctx env calleeName => exact EvalBody.evalConditionalCall_mono callee args ctx env calleeName _ _ h
  | evalCallExpr f args ctx env => exact EvalBody.evalCallExpr_mono f args ctx env _ _ h
  | evalDotCall target name fallback argsOpt ctx env => exact EvalBody.evalDotCall_mono target name fallback argsOpt ctx env _ _ h
  | eval e ctx env => exact EvalBody.eval_mono e ctx env _ _ h
/-! ## Fuel laws

`evalFuel n` is `n` iterations of `evalStep` from the everywhere-incomplete answer; `evalStep` is
monotone (`evalStep_monotone`), so the iterates form a chain in `EvalM.Approx`. -/

/-- A run of `m` from `s` COMPLETES: its outcome is not the incomplete outcome. -/
def Completes {α : Type} (m : EvalM α) (s : EvalState) : Prop := ¬ m.IsIncompleteAt s

theorem normalize_mono {α : Type} {a b : EvalM α} (h : a ⊑ b) :
    a.normalizeIncomplete ⊑ b.normalizeIncomplete :=
  monotone_normalizeIncomplete (fun x : EvalM α => x) (fun _ _ h => h) a b h

theorem normalize_of_complete {α : Type} (m : EvalM α) (s : EvalState)
    (h : (m.runState s).1 ≠ .error .fuelExhausted) :
    m.normalizeIncomplete.runState s = m.runState s := by
  dsimp only [EvalM.normalizeIncomplete]
  revert h
  generalize m.runState s = r
  rcases r with ⟨o, t⟩
  intro h
  cases o with
  | ok _ => rfl
  | error e => cases e <;> first | rfl | exact absurd rfl h

theorem normalize_of_incomplete {α : Type} (m : EvalM α) (s : EvalState)
    (h : (m.runState s).1 = .error .fuelExhausted) :
    m.normalizeIncomplete.runState s = (.error .fuelExhausted, {}) := by
  dsimp only [EvalM.normalizeIncomplete]
  revert h
  generalize m.runState s = r
  rcases r with ⟨o, t⟩
  intro h
  simp only at h
  subst h
  rfl

theorem evalFuel_succ (n : Nat) (c : EvalCall) :
    evalFuel (n + 1) c = (evalStep (evalFuel n) c).normalizeIncomplete := rfl

/-- One more unit of fuel never loses a completed outcome. -/
theorem evalFuel_mono_succ : ∀ n, evalFuel n ⊑ evalFuel (n + 1)
  | 0 => fun _ => EvalM.incomplete_approx _
  | Nat.succ n => fun c => normalize_mono (evalStep_monotone _ _ (evalFuel_mono_succ n) c)

/-- **Fuel monotonicity.** -/
theorem evalFuel_mono {n m : Nat} (h : n ≤ m) : evalFuel n ⊑ evalFuel m := by
  induction h with
  | refl => exact PartialOrder.rel_refl
  | step _ ih => exact PartialOrder.rel_trans ih (evalFuel_mono_succ _)

/-- Every incomplete outcome of the core is THE incomplete outcome (no retained state). -/
theorem evalFuel_incomplete_normal (n : Nat) (c : EvalCall) (s : EvalState) :
    ((evalFuel n c).runState s).1 = .error .fuelExhausted → (evalFuel n c).IsIncompleteAt s := by
  intro h
  cases n with
  | zero => rfl
  | succ n =>
    unfold EvalM.IsIncompleteAt
    rw [evalFuel_succ] at h ⊢
    by_cases hc : ((evalStep (evalFuel n) c).runState s).1 = .error .fuelExhausted
    · exact normalize_of_incomplete _ s hc
    · rw [normalize_of_complete _ s hc] at h; exact absurd h hc

/-- A run of the core completes exactly when its outcome is not `fuelExhausted`. -/
theorem evalFuel_completes_iff (n : Nat) (c : EvalCall) (s : EvalState) :
    Completes (evalFuel n c) s ↔ ((evalFuel n c).runState s).1 ≠ .error .fuelExhausted := by
  constructor
  · intro h he; exact h (evalFuel_incomplete_normal n c s he)
  · intro h hi; exact h (by unfold EvalM.IsIncompleteAt at hi; rw [hi])

/-- **LAW 1 — completion is stable under more fuel**: the same outcome, emitted count, error
    payload and final state (the whole `(outcome, EvalState)` pair; the core carries no proof
    instrumentation to erase). -/
theorem completed_stable {n m : Nat} (h : n ≤ m) (c : EvalCall) (s : EvalState)
    (hc : Completes (evalFuel n c) s) :
    (evalFuel m c).runState s = (evalFuel n c).runState s := by
  rcases evalFuel_mono h c s with hi | he
  · exact absurd hi hc
  · exact he.symm

/-- **LAW 4 — a completed ordinary failure keeps its state and stays that failure**: more fuel
    never turns it into a success, another error or an incomplete run. -/
theorem completed_failure_stable {n m : Nat} (h : n ≤ m) (c : EvalCall) (s t : EvalState)
    (e : Error) (he : e ≠ .fuelExhausted) (hr : (evalFuel n c).runState s = (.error e, t)) :
    (evalFuel m c).runState s = (.error e, t) := by
  rw [completed_stable h c s (fun hi => he (by unfold EvalM.IsIncompleteAt at hi; rw [hi] at hr; cases hr; rfl)), hr]

/-- **LAW 3 — determinism**: two completed runs of the same call from the same state, at any
    two fuels, have the same outcome and final state. -/
theorem completed_deterministic {n m : Nat} (c : EvalCall) (s : EvalState)
    (hn : Completes (evalFuel n c) s) (hm : Completes (evalFuel m c) s) :
    (evalFuel n c).runState s = (evalFuel m c).runState s := by
  rcases Nat.le_total n m with h | h
  · exact (completed_stable h c s hn).symm
  · exact completed_stable h c s hm

/-! ## Derivations of finite height (LAW 2)

`Derives n c s r`: call `c` from state `s` has the completed outcome `r` by ONE evaluator step
(`evalStep`, normalized) over an answer `rec` all of whose completed answers are themselves
derivable at height `n`. It is a relational semantics over the SAME bodies, independent of the
fuel function; its finite heights correspond exactly to fuel. -/
inductive Derives : Nat → (c : EvalCall) → EvalState → Except Error c.Ret × EvalState → Prop where
  | step (n : Nat) (rec : EvalRec)
      (hrec : ∀ (c' : EvalCall) (s' : EvalState), Completes (rec c') s' →
        Derives n c' s' ((rec c').runState s'))
      (c : EvalCall) (s : EvalState)
      (hc : Completes (evalStep rec c).normalizeIncomplete s) :
      Derives (n + 1) c s (((evalStep rec c).normalizeIncomplete).runState s)

theorem derives_complete {n : Nat} {c : EvalCall} {s : EvalState} {r : Except Error c.Ret × EvalState}
    (h : Derives n c s r) : (evalFuel n c).runState s = r ∧ Completes (evalFuel n c) s := by
  induction h with
  | step n rec hrec c s hc ih =>
    have hle : rec ⊑ evalFuel n := by
      intro c' s'
      by_cases hcomp : Completes (rec c') s'
      · exact .inr (ih c' s' hcomp).1.symm
      · exact .inl (Classical.not_not.mp hcomp)
    have hstep := normalize_mono (evalStep_monotone _ _ hle c) s
    rcases hstep with hi | he
    · exact absurd hi hc
    · refine ⟨he.symm, ?_⟩
      intro hi
      apply hc
      unfold EvalM.IsIncompleteAt at hi ⊢
      rw [he]; exact hi

/-- **LAW 2 — finite derivations and sufficient fuel correspond in both directions.** -/
theorem derives_iff_fuel (n : Nat) (c : EvalCall) (s : EvalState) (r : Except Error c.Ret × EvalState) :
    Derives n c s r ↔ ((evalFuel n c).runState s = r ∧ Completes (evalFuel n c) s) := by
  constructor
  · exact derives_complete
  · rintro ⟨hr, hc⟩
    induction n generalizing c s r with
    | zero => exact absurd rfl hc
    | succ n ih =>
      subst hr
      exact Derives.step n (evalFuel n) (fun c' s' hc' => ih c' s' _ rfl hc') c s hc

/-! ## The production bridge

`evalUnbounded` — every production operation — is the fuel search `searchFuel` over the SAME core.
-/

theorem searchFuel_sound (c : EvalCall) (s : EvalState) :
    ∀ fuel r, searchFuel c s fuel = some r → ∃ m, (evalFuel m c).runState s = r ∧ Completes (evalFuel m c) s := by
  have adm : admissible (fun f : Nat → Option (Except Error c.Ret × EvalState) =>
      ∀ fuel, (fun (_ : Nat) (o : Option (Except Error c.Ret × EvalState)) =>
        ∀ r, o = some r → ∃ m, (evalFuel m c).runState s = r ∧ Completes (evalFuel m c) s) fuel (f fuel)) := by
    apply admissible_pi_apply (P := fun (_ : Nat) (o : Option (Except Error c.Ret × EvalState)) =>
      ∀ r, o = some r → ∃ m, (evalFuel m c).runState s = r ∧ Completes (evalFuel m c) s)
    intro fuel
    apply admissible_flatOrder
    intro r h; cases h
  have key := searchFuel.fixpoint_induct c s _ adm
  intro fuel r h
  refine key ?_ fuel r h
  · intro f ih fuel r h
    simp only at h
    revert h
    cases hrun : (evalFuel fuel c).runState s with
    | mk o t =>
      cases o with
      | ok v =>
        intro h; cases h
        exact ⟨fuel, hrun, fun hi => by unfold EvalM.IsIncompleteAt at hi; rw [hi] at hrun; cases hrun⟩
      | error e =>
        cases e
        all_goals first
          | (intro h; exact ih _ _ h)
          | (intro h; cases h
             exact ⟨fuel, hrun, fun hi => by unfold EvalM.IsIncompleteAt at hi; rw [hi] at hrun; cases hrun⟩)

theorem searchFuel_complete (c : EvalCall) (s : EvalState) (m : Nat)
    (hm : Completes (evalFuel m c) s) (fuel : Nat) :
    searchFuel c s fuel = some ((evalFuel m c).runState s) := by
  rw [searchFuel.eq_1]
  by_cases hf : Completes (evalFuel fuel c) s
  · rw [completed_deterministic c s hf hm]
    have hne := (evalFuel_completes_iff m c s).1 hm
    revert hne
    generalize (evalFuel m c).runState s = r
    rcases r with ⟨o, t⟩
    intro hne
    cases o with
    | ok v => rfl
    | error e => cases e <;> first | (exact absurd rfl hne) | rfl
  · have hlt : fuel < m := by
      rcases Nat.lt_or_ge fuel m with hl | hl
      · exact hl
      · exact absurd (fun hi => hm (by
          unfold EvalM.IsIncompleteAt at hi ⊢; rw [← completed_stable hl c s hm]; exact hi)) hf
    have hinc : (evalFuel fuel c).runState s = (.error .fuelExhausted, {}) := Classical.not_not.mp hf
    rw [hinc]
    exact searchFuel_complete c s m hm (2 * fuel + 1)
termination_by m - fuel

/-- A production outcome that is not `fuelExhausted` is COMPLETE. -/
def ProductionCompletes {α : Type} (m : EvalM α) (s : EvalState) : Prop :=
  (m.runState s).1 ≠ .error .fuelExhausted

/-- **THE PRODUCTION BRIDGE.** A production evaluator operation completes from `s` with outcome
    `r` exactly when the total core completes with `r` at some fuel. -/
theorem production_completes_iff (c : EvalCall) (s : EvalState) (r : Except Error c.Ret × EvalState) :
    ((evalUnbounded c).runState s = r ∧ ProductionCompletes (evalUnbounded c) s) ↔
    ∃ m, (evalFuel m c).runState s = r ∧ Completes (evalFuel m c) s := by
  constructor
  · rintro ⟨hr, hc⟩
    unfold ProductionCompletes at hc
    revert hr hc
    show (searchFuel c s initialFuel).getD (.error .fuelExhausted, s) = r →
      ((searchFuel c s initialFuel).getD (.error .fuelExhausted, s)).1 ≠ .error .fuelExhausted → _
    cases hs : searchFuel c s initialFuel with
    | none => intro _ hc; exact absurd rfl hc
    | some r' => intro hr _; simp only [Option.getD_some] at hr; subst hr; exact searchFuel_sound c s _ _ hs
  · rintro ⟨m, hr, hc⟩
    have hsearch := searchFuel_complete c s m hc initialFuel
    have hrun : (evalUnbounded c).runState s = (evalFuel m c).runState s := by
      show (searchFuel c s initialFuel).getD (.error .fuelExhausted, s) = _
      rw [hsearch]; rfl
    refine ⟨hrun.trans hr, ?_⟩
    unfold ProductionCompletes
    rw [hrun]
    exact (evalFuel_completes_iff m c s).1 hc

/-- Every fuel iterate approximates production: where the core completes, production agrees. -/
theorem evalFuel_approx_production (n : Nat) : ∀ c, evalFuel n c ⊑ evalUnbounded c := by
  intro c s
  by_cases hc : Completes (evalFuel n c) s
  · exact .inr ((production_completes_iff c s _).2 ⟨n, rfl, hc⟩).1.symm
  · exact .inl (Classical.not_not.mp hc)

/-- **Production unfolds through its own bodies.** A completed production outcome is ONE
    evaluator step over production itself: for every operation, its completed production outcome
    is its body (`EvalBody.*`) run with the production operations as its recursive calls — e.g.
    a completed `demandNeedRecursive a` is `NeedDemand.step (evalSuppliedAt a) productionPlanRoute
    demandNeedRecursive a` (`production_demand_unfolds`). The converse (a completed body run over
    production is production's outcome) is NOT claimed: it needs finite use of the recursive
    answers, which is not proved here. -/
theorem production_unfolds (c : EvalCall) (s : EvalState)
    (hc : ProductionCompletes (evalUnbounded c) s) :
    (evalStep evalUnbounded c).runState s = (evalUnbounded c).runState s := by
  obtain ⟨m, hr, hm⟩ := (production_completes_iff c s _).1 ⟨rfl, hc⟩
  cases m with
  | zero => exact absurd rfl hm
  | succ k =>
    have happrox : evalFuel k ⊑ evalUnbounded := evalFuel_approx_production k
    have hstep := evalStep_monotone _ _ happrox c s
    have hne := (evalFuel_completes_iff (k + 1) c s).1 hm
    -- the normalization is the identity on a completed outcome
    have hnorm : (evalStep (evalFuel k) c).runState s = (evalFuel (k + 1) c).runState s := by
      rw [evalFuel_succ] at hne ⊢
      by_cases hc : ((evalStep (evalFuel k) c).runState s).1 = .error .fuelExhausted
      · rw [normalize_of_incomplete _ s hc] at hne; exact absurd rfl hne
      · exact (normalize_of_complete _ s hc).symm
    rcases hstep with hi | he
    · exfalso; apply hm
      unfold EvalM.IsIncompleteAt at hi ⊢
      rw [← hnorm]; exact hi
    · rw [← he, hnorm, hr]

/-! ### Production operations are the core at their call -/

theorem production_demand_unfolds (a : Nat) (s : EvalState)
    (hc : ProductionCompletes (demandNeedRecursive a) s) :
    (NeedDemand.step (evalSuppliedAt a) productionPlanRoute demandNeedRecursive a).runState s =
      (demandNeedRecursive a).runState s :=
  production_unfolds (.demandNeedRecursive a) s hc

theorem productionPlanRoute_is_core : productionPlanRoute = EvalRec.planRoute evalUnbounded := rfl
theorem bindingChannels_is_core : bindingChannels = EvalRec.bindingChannels evalUnbounded := rfl


/-! ## Whole-run state invariants

A relation `R` between a computation's entry and exit states that every evaluator BODY preserves
whenever its recursive calls do holds for every completed run of the core at every fuel, and for
every production run. This is the induction principle the whole-run heap and cache invariants
use: each instance proves only the per-body step (`EvaluatorDiscipline`). -/

/-- `m` relates every entry state to its exit state by `R`. -/
def Preserves {α : Type} (R : EvalState → EvalState → Prop) (m : EvalM α) : Prop :=
  ∀ s, R s (m.runState s).2

/-- The completed part of an answer, made total with the entry state: where `evalFuel n`
    completes it agrees with it, elsewhere it stops at once without touching the state. -/
noncomputable def completedPart (n : Nat) : EvalRec := fun c =>
  ⟨fun s => @ite _ (Completes (evalFuel n c) s) (Classical.propDecidable _)
    ((evalFuel n c).runState s) (.error .fuelExhausted, s)⟩

theorem evalFuel_approx_completedPart (n : Nat) : evalFuel n ⊑ completedPart n := by
  intro c s
  by_cases hc : Completes (evalFuel n c) s
  · right; simp only [completedPart, if_pos hc]
  · left; exact Classical.not_not.mp hc

/-- **INVARIANT TRANSFER.** -/
theorem invariant_transfer (R : EvalState → EvalState → Prop) (hrefl : ∀ s, R s s)
    (hbody : ∀ rec : EvalRec, (∀ c, Preserves R (rec c)) → ∀ c, Preserves R (evalStep rec c)) :
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
      · rw [he]; exact hbody _ hpart c s

/-- Production preserves every such invariant, unconditionally (its kernel-level fallback for a
    divergent run keeps the entry state). -/
theorem production_preserves (R : EvalState → EvalState → Prop) (hrefl : ∀ s, R s s)
    (hbody : ∀ rec : EvalRec, (∀ c, Preserves R (rec c)) → ∀ c, Preserves R (evalStep rec c))
    (c : EvalCall) : Preserves R (evalUnbounded c) := by
  intro s
  by_cases hc : ProductionCompletes (evalUnbounded c) s
  · obtain ⟨m, hr, hm⟩ := (production_completes_iff c s _).1 ⟨rfl, hc⟩
    rw [← hr]
    exact invariant_transfer R hrefl hbody m c s hm
  · have hs : (evalUnbounded c).runState s = (.error .fuelExhausted, s) := by
      unfold ProductionCompletes at hc
      have hdef : (evalUnbounded c).runState s = (searchFuel c s initialFuel).getD (.error .fuelExhausted, s) := rfl
      rw [hdef] at hc ⊢
      cases hsearch : searchFuel c s initialFuel with
      | none => rfl
      | some r =>
        exfalso
        obtain ⟨m, hr, hm⟩ := searchFuel_sound c s _ _ hsearch
        rw [hsearch] at hc
        apply hc
        simp only [Option.getD_some]
        rw [← hr]; exact (evalFuel_completes_iff m c s).1 hm
    rw [hs]; exact hrefl s

/-! ## Production equations for delegating operations

A body that runs exactly ONE recursive call and then a non-recursive, never-incomplete
continuation gives an exact production EQUATION (no completion premise: a divergent callee makes
both sides the same non-completing outcome). This turns every plain/counted projection of the
evaluator (FORMAL-05) into a kernel theorem about the production operations. -/

theorem production_incomplete_state (c : EvalCall) (s : EvalState)
    (hc : ¬ ProductionCompletes (evalUnbounded c) s) :
    (evalUnbounded c).runState s = (.error .fuelExhausted, s) := by
  unfold ProductionCompletes at hc
  have hdef : (evalUnbounded c).runState s = (searchFuel c s initialFuel).getD (.error .fuelExhausted, s) := rfl
  rw [hdef] at hc ⊢
  cases hsearch : searchFuel c s initialFuel with
  | none => rfl
  | some r =>
    exfalso
    obtain ⟨m, hr, hm⟩ := searchFuel_sound c s _ _ hsearch
    rw [hsearch] at hc
    apply hc
    simp only [Option.getD_some]
    rw [← hr]; exact (evalFuel_completes_iff m c s).1 hm

theorem EvalM.bind_pure' {α : Type} (m : EvalM α) : m >>= (fun x => pure x) = m := by
  apply EvalM.ext; intro s
  rw [EvalM.bind_runState]
  rcases m.runState s with ⟨o, t⟩
  cases o <;> rfl

/-- **THE DELEGATION EQUATION.** -/
theorem delegation_equation (c c' : EvalCall) (k : c'.Ret → EvalM c.Ret)
    (hstep : ∀ rec : EvalRec, evalStep rec c = rec c' >>= k)
    (hk : ∀ v t, ((k v).runState t).1 ≠ .error .fuelExhausted) :
    evalUnbounded c = evalUnbounded c' >>= k := by
  apply EvalM.ext; intro s
  rw [EvalM.bind_runState]
  by_cases hc' : ProductionCompletes (evalUnbounded c') s
  · obtain ⟨m, hr, hm⟩ := (production_completes_iff c' s _).1 ⟨rfl, hc'⟩
    have hne := (evalFuel_completes_iff m c' s).1 hm
    rw [← hr]
    rcases hrun : (evalFuel m c').runState s with ⟨o, t⟩
    rw [hrun] at hne
    -- the core at fuel m+1 runs the continuation over the completed callee outcome
    -- the core at fuel m+1 runs the continuation over the completed callee outcome; the
    -- production outcome of `c` is that run
    have key : ∀ r : Except Error c.Ret × EvalState,
        (evalStep (evalFuel m) c).runState s = r → r.1 ≠ .error .fuelExhausted →
        (evalUnbounded c).runState s = r := by
      intro r hr' hne'
      have hfuel : (evalFuel (m + 1) c).runState s = r := by
        rw [evalFuel_succ, normalize_of_complete _ s (by rw [hr']; exact hne'), hr']
      exact ((production_completes_iff c s r).2
        ⟨m + 1, hfuel, (evalFuel_completes_iff (m + 1) c s).2 (by rw [hfuel]; exact hne')⟩).1
    cases o with
    | ok a =>
      apply key
      · rw [hstep, EvalM.bind_runState, hrun]
      · exact hk a t
    | error e =>
      apply key
      · rw [hstep, EvalM.bind_runState, hrun]
      · intro h; apply hne; simp only at h ⊢; injection h with h; rw [h]
  · rw [production_incomplete_state c' s hc']
    apply production_incomplete_state c s
    intro hc
    obtain ⟨m, hr, hm⟩ := (production_completes_iff c s _).1 ⟨rfl, hc⟩
    cases m with
    | zero => exact hm rfl
    | succ j =>
      apply hc'
      by_cases hj : Completes (evalFuel j c') s
      · exact ((production_completes_iff c' s _).2 ⟨j, rfl, hj⟩).2
      · exfalso; apply hm
        have hinc : (evalFuel j c').runState s = (.error .fuelExhausted, {}) := Classical.not_not.mp hj
        unfold EvalM.IsIncompleteAt
        rw [evalFuel_succ, hstep]
        apply normalize_of_incomplete
        rw [EvalM.bind_runState, hinc]

theorem pure_never_incomplete {α : Type} (a : α) (t : EvalState) :
    ((pure a : EvalM α).runState t).1 ≠ .error .fuelExhausted := nofun

/-- **Forwarding equation**: a body that IS one recursive call. -/
theorem forwarding_equation (c c' : EvalCall) (hty : c'.Ret = c.Ret)
    (hstep : ∀ rec : EvalRec, evalStep rec c = rec c' >>= (fun x => pure (cast hty x))) :
    evalUnbounded c = evalUnbounded c' >>= (fun x => pure (cast hty x)) :=
  delegation_equation c c' _ hstep (fun _ _ => nofun)

/-! ### FORMAL-05 at the evaluator level: every plain operation is its counted twin's VALUE -/

theorem eval_is_counted_projection (e : Expr) (ctx : EvalCtx) (env : ValEnv) :
    eval e ctx env = evalCounted e ctx env >>= fun out => pure out.fst :=
  delegation_equation (.eval e ctx env) (.evalCounted e ctx env) _ (fun _ => rfl) (fun _ _ => nofun)

theorem evalCallExpr_is_counted_projection (f : Expr) (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) :
    evalCallExpr f args ctx env = evalCallCountedExpr f args ctx env >>= fun out => pure out.fst :=
  delegation_equation (.evalCallExpr f args ctx env) (.evalCallCountedExpr f args ctx env) _
    (fun _ => rfl) (fun _ _ => nofun)

theorem evalDotCall_is_counted_projection (target : Expr) (name : Ident) (fallback : Expr)
    (argsOpt : Option OutputBundle) (ctx : EvalCtx) (env : ValEnv) :
    evalDotCall target name fallback argsOpt ctx env =
      evalDotCallCounted target name fallback argsOpt ctx env >>= fun out => pure out.fst :=
  delegation_equation (.evalDotCall target name fallback argsOpt ctx env)
    (.evalDotCallCounted target name fallback argsOpt ctx env) _ (fun _ => rfl) (fun _ _ => nofun)

theorem evalUserCall_is_counted_projection (callee : Algorithm) (args : OutputBundle) (ctx : EvalCtx)
    (env : ValEnv) :
    evalUserCall callee args ctx env = evalUserCallCounted callee args ctx env >>= fun out => pure out.fst :=
  delegation_equation (.evalUserCall callee args ctx env) (.evalUserCallCounted callee args ctx env) _
    (fun _ => rfl) (fun _ _ => nofun)

theorem evalConditionalCall_is_counted_projection (callee : Algorithm) (args : OutputBundle)
    (ctx : EvalCtx) (env : ValEnv) (calleeName : String) :
    evalConditionalCall callee args ctx env calleeName =
      evalConditionalCallCounted callee args ctx env calleeName >>= fun out => pure out.fst :=
  delegation_equation (.evalConditionalCall callee args ctx env calleeName)
    (.evalConditionalCallCounted callee args ctx env calleeName) _ (fun _ => rfl) (fun _ _ => nofun)

theorem evalResolvedCall_is_counted_projection (callee : Algorithm) (args : OutputBundle)
    (ctx : EvalCtx) (env : ValEnv) (calleeName : String) :
    evalResolvedCall callee args ctx env calleeName =
      evalResolvedCallCounted callee args ctx env calleeName >>= fun out => pure out.fst :=
  delegation_equation (.evalResolvedCall callee args ctx env calleeName)
    (.evalResolvedCallCounted callee args ctx env calleeName .none) _ (fun _ => rfl) (fun _ _ => nofun)

theorem evalResolvedCallbackCall_is_counted_projection (callee : Algorithm) (args : List CountedResult)
    (ctx : EvalCtx) (env : ValEnv) (calleeName : String) :
    evalResolvedCallbackCall callee args ctx env calleeName =
      evalResolvedCallbackCallCounted callee args ctx env calleeName >>= fun out => pure out.fst :=
  delegation_equation (.evalResolvedCallbackCall callee args ctx env calleeName)
    (.evalResolvedCallbackCallCounted callee args ctx env calleeName) _ (fun _ => rfl) (fun _ _ => nofun)

theorem applyBuiltin_is_counted_projection (b : Builtin) (args : List ResolvedArgumentAlgorithm)
    (ctx : EvalCtx) (env : ValEnv) :
    applyBuiltin b args ctx env = applyBuiltinCounted b args ctx env >>= fun out => pure out.fst :=
  delegation_equation (.applyBuiltin b args ctx env) (.applyBuiltinCounted b args ctx env) _
    (fun _ => rfl) (fun _ _ => nofun)

theorem evalAlgOutputCore_is_counted_projection (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    evalAlgOutputCore a ctx env = evalAlgOutputCountedCore a ctx env >>= fun out => pure out.fst :=
  delegation_equation (.evalAlgOutputCore a ctx env) (.evalAlgOutputCountedCore a ctx env) _
    (fun _ => rfl) (fun _ _ => nofun)

theorem evalZeroArgPropertyAccess_is_counted_projection (accessKind : ZeroArgPropertyAccessKind)
    (owner : Algorithm) (binding : PropDef) (resolvedAlgorithm : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    evalZeroArgPropertyAccess accessKind owner binding resolvedAlgorithm ctx env =
      evalZeroArgPropertyAccessCounted accessKind owner binding resolvedAlgorithm ctx env >>=
        fun out => pure out.fst :=
  delegation_equation (.evalZeroArgPropertyAccess accessKind owner binding resolvedAlgorithm ctx env)
    (.evalZeroArgPropertyAccessCounted accessKind owner binding resolvedAlgorithm ctx env .read) _
    (fun _ => rfl) (fun _ _ => nofun)

theorem evalZeroArgumentDemandOutput_is_counted_projection (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    evalZeroArgumentDemandOutput a ctx env =
      evalZeroArgumentDemandOutputCounted a ctx env >>= fun out => pure out.fst :=
  delegation_equation (.evalZeroArgumentDemandOutput a ctx env)
    (.evalZeroArgumentDemandOutputCounted a ctx env) _ (fun _ => rfl) (fun _ _ => nofun)

theorem evalArgumentValue_is_counted_projection (arg : ResolvedArgumentAlgorithm) (ctx : EvalCtx)
    (env : ValEnv) :
    evalArgumentValue arg ctx env = evalArgumentValueCounted arg ctx env >>= fun out => pure out.fst :=
  delegation_equation (.evalArgumentValue arg ctx env) (.evalArgumentValueCounted arg ctx env) _
    (fun _ => rfl) (fun _ _ => nofun)

theorem evalCaptureValue_is_counted_projection (rows : OutputBundle) (ctx : EvalCtx) (env : ValEnv) :
    evalCaptureValue rows ctx env = evalCaptureCountedCore rows ctx env >>= fun out => pure out.fst :=
  delegation_equation (.evalCaptureValue rows ctx env) (.evalCaptureCountedCore rows ctx env) _
    (fun _ => rfl) (fun _ _ => nofun)



end KatLang.EvaluatorCore
