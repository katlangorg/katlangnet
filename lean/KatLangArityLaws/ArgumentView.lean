import KatLangArityLaws.CallReference

open KatLang KatLang.CallPlan

/-!
# CallReference S2: the lazy argument view `R.Arguments` (October 2026)

S2 adds ONE value and three operations on top of the S1 reference:

* `R.Arguments` (the dot intrinsic on a structural miss, `evalDotCallCounted`) reads R's VALUE and,
  for `callRef a`, returns `Result.argView a` — the view of plan `a`'s ORIGINAL effective argument
  supply (`argumentsOfValue`);
* `count` / `first` / `last` over a view bound as their whole collection
  (`argumentViewBuiltin`), and postfix selection over a view receiver (`selectViewWith`), both
  parametrized by the view's cells (`cellsOf`, production `NeedPlan.viewCells evalSupplySpread a`)
  and by cell VALUE demand (production `demandNeedRecursive`);
* the ARGUMENT SPREAD `F(V*)`: supply formation asks its spread capability for the slot's
  contribution (`NeedSupply.SpreadEval`), and for a view the production capability returns
  `NeedPlan.viewSupply` — the plan's original cells, transported (`SpreadSupply.cells`).

Every theorem below is about those authoritative definitions. Proved here:

* obtaining a view is INERT — no state change at all — and is refused for anything but a call
  reference; a view is a different value from its reference; an argument list is refused
  (`arguments_*`, `view_*`);
* the view's supply IS the plan's one sticky preparation: a prepared plan answers from its record
  and runs nothing, an unprepared plan forms its supply exactly once through `NeedSupply.form`
  over the plan's own written arguments, and every later read — after any disciplined
  computation: VALUE, `Invoke()`, more view operations — returns that same outcome
  (`viewCells_*`); the view and every invocation read the SAME cells (`view_and_invoke_share_cells`);
* `count` demands NO cell — its outcome does not depend on cell demand at all — and reads only the
  supply (`count_*`); `first`/`last` and selection demand only the selected cells (demand
  extensionality: their outcome depends on cell demand only at the selected cells,
  `first_demands_only_first`, `last_demands_only_last`, `select_demands_only_selected`);
* selection keeps the ordinary formation precedence: an empty selection reads nothing, a selector
  that fails `selectorIndex` (a non-number, a negative number) fails before the supply is read
  (`select_*`); `selectPosition` itself factors through `selectorIndex`
  (`selectPosition_eq_selectorIndex`);
* the argument spread contributes EXACTLY the plan's recorded cell addresses — the production
  supply representation, not equal values — allocating, copying and demanding nothing
  (`viewSupply_prepared`, `view_spread_slot`, with `NeedControl.Formation.computed_spread_transports`);
* the VALUE openers refuse to open a view, and agree with the pre-S2 opening wherever no view is
  opened (`openSpreadItems_eq_reopen`, `openSupplySpread_eq_items`) — the conservative extension
  for META-free programs, whose values never contain a view;
* the run boundary refuses a value containing a view (`export_refuses_view`).

NOT claimed (source facts, executable guards in `ArgumentViewGuards.lean`): that the `partial`
evaluator's `Arguments` arm, `.index` arm, sequence-builtin binding and `evalSupplySpread` call
these definitions; the reachable-state refinement (still open, M1.5 §8) and `ProductionDiscipline`
(which now also names `evalSupplySpread`; open until R7, now the theorem `productionDiscipline_holds`,
`EvaluatorDiscipline.lean`); run identity and the ended-run, foreign-run and terminal
refusals (C#-only obligations: Lean has one run per state); C# concurrency, cancellation and
resource accounting.
-/

namespace KatLang.ArgumentViewLaws

/-! ## Obtaining the view: `R.Arguments` -/

/-- **Inertia.** Obtaining the view of a call reference changes NOTHING: no target, no supply
    preparation, no argument VALUE, no allocation — the whole state is returned unchanged. -/
theorem arguments_inert (a : Nat) (s : EvalState) :
    (argumentsOfValue (.callRef a)).runState s = (.ok (.argView a, 1), s) := rfl

/-- Any other receiver VALUE — an argument view included — is the intrinsic's kind rejection,
    again without any effect. -/
theorem arguments_refuses (v : Result) (s : EvalState) (h : ∀ a, v ≠ .callRef a) :
    (argumentsOfValue v).runState s =
      (.error (.typeMismatch (argumentsRequiresCallReferenceMessage v)), s) := by
  cases v with
  | callRef a => exact absurd rfl (h a)
  | _ => rfl

theorem arguments_of_view_refused (a : Nat) (s : EvalState) :
    (argumentsOfValue (.argView a)).runState s =
      (.error (.typeMismatch (argumentsRequiresCallReferenceMessage (.argView a))), s) := rfl

/-- `R.Arguments(…)` — any written list, the empty one included — is refused before anything is
    formed or demanded. -/
theorem arguments_route_refuses_list (args : OutputBundle) (s : EvalState) :
    (rejectArgumentsIntrinsicArguments (some args)).runState s =
      (.error (.illegalInEval argumentsIsPropertyMessage), s) := rfl

theorem arguments_route_accepts_read (s : EvalState) :
    (rejectArgumentsIntrinsicArguments none).runState s = (.ok (), s) := rfl

/-- A view and a reference are different values, whatever their plans. -/
theorem view_is_not_reference (a b : Nat) : Result.argView a ≠ Result.callRef b := by
  intro h
  cases h

/-- Views are equal iff they view the same plan; equality never inspects a cell. -/
theorem view_identity (a b : Nat) : Result.argView a = Result.argView b ↔ a = b :=
  ⟨fun h => by injection h, fun h => h ▸ rfl⟩

/-- A view is no number, Boolean, text or openable structure. -/
theorem view_is_opaque (a : Nat) :
    (Result.argView a).asInt? = none ∧ (Result.argView a).asBool? = none ∧
    (Result.argView a).structureItems? = none ∧ (Result.argView a).languageAtoms = [] := by
  refine ⟨rfl, rfl, rfl, by simp [Result.languageAtoms]⟩

/-! ## The view's supply: the plan's ONE sticky preparation (actual `NeedPlan.viewCells`) -/

/-- The view's supply reads the plan's route first (META-S3-4, D-4: recorded, or classified now),
    then — on a callable route — the plan's ONE sticky preparation over the route's effective
    bundle; an intrinsic route is the refusal (D-1A). -/
theorem viewCells_routes (sp : NeedSupply.SpreadEval) (classify : NeedPlan.CallShape → EvalM PlanRoute)
    (a : Nat) (s : EvalState)
    (shape : NeedPlan.CallShape) (h : NeedPlan.shapeAt? s.needs a = some shape) :
    (NeedPlan.viewCells sp classify a).runState s =
      (match (NeedPlan.routeOf classify a shape).runState s with
       | (.error e, t) => (.error e, t)
       | (.ok r, t) =>
         if r = .intrinsic then (.error NeedPlan.invocationRefusal, t)
         else (NeedPlan.prepare sp a (NeedPlan.effective shape r)).runState t) := by
  simp only [NeedPlan.viewCells, bind_run, get_run, h]
  rcases (NeedPlan.routeOf classify a shape).runState s with ⟨_ | r, t⟩
  · rfl
  · by_cases hi : r = .intrinsic
    · subst hi; rfl
    · have hb : (r == PlanRoute.intrinsic) = false := by
        cases r <;> first | rfl | exact absurd rfl hi
      simp only [hb, Bool.false_eq_true, ↓reduceIte, if_neg hi]

/-- With the plan's callable route recorded, the view's supply IS the plan's preparation over the
    route's effective bundle. -/
theorem viewCells_run (sp : NeedSupply.SpreadEval) (classify : NeedPlan.CallShape → EvalM PlanRoute)
    (a : Nat) (s : EvalState) (shape : NeedPlan.CallShape) (cell : NeedCell) (r : PlanRoute)
    (h : NeedPlan.shapeAt? s.needs a = some shape) (hc : s.needs[a]? = some cell)
    (hr : cell.route = some r) (hi : r ≠ .intrinsic) :
    (NeedPlan.viewCells sp classify a).runState s =
      (NeedPlan.prepare sp a (NeedPlan.effective shape r)).runState s := by
  rw [viewCells_routes sp classify a s shape h, routeOf_recorded classify a shape s cell r hc hr]
  exact if_neg hi

/-- D-1A: the view of an intrinsic-routed capture has no supply — the refusal, with no effect. -/
theorem viewCells_intrinsic (sp : NeedSupply.SpreadEval) (classify : NeedPlan.CallShape → EvalM PlanRoute)
    (a : Nat) (s : EvalState) (shape : NeedPlan.CallShape) (cell : NeedCell)
    (h : NeedPlan.shapeAt? s.needs a = some shape) (hc : s.needs[a]? = some cell)
    (hr : cell.route = some .intrinsic) :
    (NeedPlan.viewCells sp classify a).runState s = (.error NeedPlan.invocationRefusal, s) := by
  rw [viewCells_routes sp classify a s shape h, routeOf_recorded classify a shape s cell .intrinsic hc hr]
  rfl

theorem viewCells_refuses (sp : NeedSupply.SpreadEval) (classify : NeedPlan.CallShape → EvalM PlanRoute)
    (a : Nat) (s : EvalState)
    (h : NeedPlan.shapeAt? s.needs a = none) :
    (NeedPlan.viewCells sp classify a).runState s = (.error NeedPlan.metaRefusal, s) := by
  simp only [NeedPlan.viewCells, bind_run, get_run, h]
  rfl

/-- **A prepared plan answers from its record**: the view's supply is the recorded outcome —
    cells or an ordinary failure — and nothing runs or changes. -/
theorem viewCells_prepared (sp : NeedSupply.SpreadEval) (classify : NeedPlan.CallShape → EvalM PlanRoute)
    (a : Nat) (s : EvalState)
    (shape : NeedPlan.CallShape) (cell : NeedCell) (r : PlanRoute) (outcome : Except Error (List NeedSupply.Sourced))
    (hs : NeedPlan.shapeAt? s.needs a = some shape) (hc : s.needs[a]? = some cell)
    (hr : cell.route = some r) (hi : r ≠ .intrinsic)
    (hp : cell.plan = .prepared outcome) :
    (NeedPlan.viewCells sp classify a).runState s = (outcome, s) := by
  rw [viewCells_run sp classify a s shape cell r hs hc hr hi, prepare_prepared sp a _ s cell outcome hc hp]

/-- **An unprepared plan forms its supply exactly once**, through the ONE former over the route's
    effective bundle (META-S3-4: an extension's receiver first) in the plan's caller context — the
    formation VALUE and `Invoke()` run — and records the outcome. The target is never resolved and
    no argument VALUE is demanded by the view itself (formation demands nothing; only an arbitrary
    spread's own evaluation runs). -/
theorem viewCells_unprepared (sp : NeedSupply.SpreadEval) (classify : NeedPlan.CallShape → EvalM PlanRoute)
    (a : Nat) (s : EvalState)
    (shape : NeedPlan.CallShape) (cell : NeedCell) (r : PlanRoute)
    (hs : NeedPlan.shapeAt? s.needs a = some shape) (hc : s.needs[a]? = some cell)
    (hr : cell.route = some r) (hi : r ≠ .intrinsic)
    (hp : cell.plan = .unprepared)
    (hcomplete : ((NeedSupply.form sp shape.caller shape.values (NeedPlan.effective shape r).args).runState
      (withPlan a .preparing s)).1.isIncomplete = false) :
    (NeedPlan.viewCells sp classify a).runState s =
      (let res := (NeedSupply.form sp shape.caller shape.values (NeedPlan.effective shape r).args).runState
          (withPlan a .preparing s)
       (res.1, withPlan a (.prepared res.1) res.2)) := by
  rw [viewCells_run sp classify a s shape cell r hs hc hr hi]
  have := prepare_unprepared sp a (NeedPlan.effective shape r) s cell hc hp
    (by simp only [effective_caller, effective_values]; exact hcomplete)
  simp only [effective_caller, effective_values] at this
  exact this

theorem disciplined_viewCells (sp : NeedSupply.SpreadEval) (hsp : ∀ e c v, Disciplined (sp e c v))
    (classify : NeedPlan.CallShape → EvalM PlanRoute) (hclassify : ∀ shape, Disciplined (classify shape))
    (a : Nat) : Disciplined (NeedPlan.viewCells sp classify a) := by
  intro s
  cases h : NeedPlan.shapeAt? s.needs a with
  | none => rw [viewCells_refuses sp classify a s h]; exact HeapKept.refl _
  | some shape =>
    rw [viewCells_routes sp classify a s shape h]
    have k := disciplined_routeOf classify hclassify a shape s
    rcases hro : (NeedPlan.routeOf classify a shape).runState s with ⟨_ | r, t⟩ <;> rw [hro] at k
    · exact k
    · dsimp only
      by_cases hi : r = .intrinsic
      · rw [if_pos hi]; exact k
      · rw [if_neg hi]; exact k.trans (disciplined_prepare sp hsp a _ t)

/-- **Supply formation happens once.** After a first view read of an unprepared plan with a recorded
    route (and then any disciplined computation — the original VALUE, `Invoke()`, other view
    operations, forwarding), the next view read returns EXACTLY the first outcome and changes
    nothing: an arbitrary spread among the arguments is never evaluated again, and a sticky failure
    stays. -/
theorem viewCells_forms_once (sp : NeedSupply.SpreadEval) (hsp : ∀ e c v, Disciplined (sp e c v))
    (classify : NeedPlan.CallShape → EvalM PlanRoute)
    (a : Nat) (s : EvalState) (shape : NeedPlan.CallShape) (cell : NeedCell) (r : PlanRoute)
    (hs : NeedPlan.shapeAt? s.needs a = some shape) (hc : s.needs[a]? = some cell)
    (hr : cell.route = some r) (hi : r ≠ .intrinsic)
    (hp : cell.plan = .unprepared) {α : Type} (m : EvalM α) (hm : Disciplined m)
    (hcomplete : ((NeedSupply.form sp shape.caller shape.values (NeedPlan.effective shape r).args).runState
      (withPlan a .preparing s)).1.isIncomplete = false) :
    (NeedPlan.viewCells sp classify a).runState (m.runState ((NeedPlan.viewCells sp classify a).runState s).2).2 =
      (((NeedPlan.viewCells sp classify a).runState s).1,
        (m.runState ((NeedPlan.viewCells sp classify a).runState s).2).2) := by
  obtain ⟨c', hc', hplan, _⟩ := prepare_records sp hsp a (NeedPlan.effective shape r) s cell hc hp
    (by simp only [effective_caller, effective_values]; exact hcomplete)
  rw [viewCells_run sp classify a s shape cell r hs hc hr hi]
  have kprep := disciplined_prepare sp hsp a (NeedPlan.effective shape r) s
  have hs2 := shapeAt_kept (hm _) a shape (shapeAt_kept kprep a shape hs)
  -- The route record is sticky: preparation and `m` keep it (`CellKept.routed`).
  obtain ⟨c1, hc1, k1⟩ := kprep a cell hc
  rw [hc'] at hc1
  cases hc1
  obtain ⟨c2, hc2, k2⟩ := hm _ a c' hc'
  rw [viewCells_run sp classify a _ shape c2 r hs2 hc2 (k2.routed r (k1.routed r hr)) hi]
  exact prepared_survives m hm sp a (NeedPlan.effective shape r) _ c' _ hc' hplan

/-- **The view and every invocation read the same cells.** With plan `a`'s callable route recorded
    and its supply prepared — by its VALUE, an `Invoke()` or an earlier view operation — the view's
    supply is exactly the recorded cells and an explicit invocation is `callOver` those same cells. -/
theorem view_and_invoke_share_cells (route : NeedPlan.Route)
    (htarget : ∀ f c, Disciplined (route.target f c))
    (hnormal : ∀ g c, Disciplined (route.normalize g c))
    (hclassify : ∀ shape, Disciplined (route.classify shape))
    (hproject : ∀ c, Disciplined (route.project c))
    (a : Nat) (s : EvalState) (cell : NeedCell) (shape : NeedPlan.CallShape) (r : PlanRoute)
    (cells : List NeedSupply.Sourced)
    (hc : s.needs[a]? = some cell) (hshape : NeedPlan.ofSuspension? cell.suspension = some shape)
    (hr : cell.route = some r) (hi : r ≠ .intrinsic)
    (hp : cell.plan = .prepared (.ok cells)) :
    (NeedPlan.viewCells route.spread route.classify a).runState s = (.ok cells, s) ∧
    (NeedPlan.invoke route ⟨a⟩).runState s = (callOver route a shape r cells).runState s := by
  have hsa : NeedPlan.shapeAt? s.needs a = some shape := by simp [NeedPlan.shapeAt?, hc, hshape]
  refine ⟨viewCells_prepared route.spread route.classify a s shape cell r _ hsa hc hr hi hp, ?_⟩
  rw [invoke_run route a s shape hsa]
  exact execute_prepared route htarget hnormal hclassify hproject a shape s cell r cells hc hr hi hp

/-! ## The argument spread transports the ORIGINAL cells (actual `NeedPlan.viewSupply`) -/

/-- Reading written sources leaves the state unchanged, so mapping it over cells is a pure map. -/
theorem sourced_map_run (cells : List NeedSupply.Sourced) (s : EvalState) :
    (cells.mapM (fun (p : NeedSupply.Sourced) => do
        pure (p.1, ← needWrittenSource? p.1))).runState s =
      (.ok (cells.map fun p => (p.1, KatLang.NeedControl.Provenance.sourceAt s.needs p.1)), s) := by
  suffices h : ∀ (acc : List NeedSupply.Sourced),
      (List.mapM.loop (fun (p : NeedSupply.Sourced) => do pure (p.1, ← needWrittenSource? p.1)) cells acc).runState s =
        (.ok (acc.reverse ++ cells.map fun p => (p.1, KatLang.NeedControl.Provenance.sourceAt s.needs p.1)), s) by
    simpa [List.mapM] using h []
  induction cells with
  | nil => intro acc; simp [List.mapM.loop]
  | cons p rest ih =>
    intro acc
    simp only [List.mapM.loop, bind_run, KatLang.NeedControl.Provenance.source_run, pure_run]
    rw [ih]
    simp

/-- **Cell-preserving spread over a prepared plan.** The argument spread of `argView a` contributes
    exactly the plan's recorded cell ADDRESSES, in order, each with its own written source, and
    changes nothing: no cell is allocated, copied, wrapped or demanded. -/
theorem viewSupply_prepared (sp : NeedSupply.SpreadEval) (classify : NeedPlan.CallShape → EvalM PlanRoute)
    (a : Nat) (s : EvalState)
    (shape : NeedPlan.CallShape) (cell : NeedCell) (r : PlanRoute) (cells : List NeedSupply.Sourced)
    (hs : NeedPlan.shapeAt? s.needs a = some shape) (hc : s.needs[a]? = some cell)
    (hr : cell.route = some r) (hi : r ≠ .intrinsic)
    (hp : cell.plan = .prepared (.ok cells)) :
    (NeedPlan.viewSupply sp classify a).runState s =
      (.ok (.cells (cells.map fun p => (p.1, KatLang.NeedControl.Provenance.sourceAt s.needs p.1))), s) := by
  simp only [NeedPlan.viewSupply, bind_run, viewCells_prepared sp classify a s shape cell r _ hs hc hr hi hp]
  rw [sourced_map_run]
  rfl

/-- **The destination supply holds the ORIGINAL cells.** A computed spread slot whose capability
    returns the view's supply (`evalSupplySpread`'s `.view a` arm) supplies exactly the plan's
    recorded addresses — the identities the original call's VALUE and every `Invoke()` bind —
    and leaves the state unchanged. This relates the production SUPPLY REPRESENTATION, not
    computed values. -/
theorem view_spread_slot (ev sp : NeedSupply.SpreadEval) (classify : NeedPlan.CallShape → EvalM PlanRoute)
    (ctx : EvalCtx) (env : ValEnv)
    (operand : Expr) (a : Nat) (s : EvalState) (shape : NeedPlan.CallShape) (cell : NeedCell)
    (r : PlanRoute) (cells : List NeedSupply.Sourced)
    (hk : (spreadCollectorSlice? operand ctx).runState s = (.ok none, s))
    (hv : (ev (.sequenceSpread operand) ctx env).runState s = (NeedPlan.viewSupply sp classify a).runState s)
    (hs : NeedPlan.shapeAt? s.needs a = some shape) (hc : s.needs[a]? = some cell)
    (hr : cell.route = some r) (hi : r ≠ .intrinsic)
    (hp : cell.plan = .prepared (.ok cells)) :
    ∃ sourced, (NeedSupply.slot ev ctx env (.sequenceSpread operand)).runState s = (.ok sourced, s) ∧
      sourced.map Prod.fst = cells.map Prod.fst := by
  rw [viewSupply_prepared sp classify a s shape cell r cells hs hc hr hi hp] at hv
  refine ⟨_, KatLang.NeedControl.Formation.computed_spread_transports ev ctx env operand _ s s hk hv, ?_⟩
  simp

/-! ## `count`, `first`, `last` over a view (actual `argumentViewBuiltin`) -/

/-- **`count` reads the supply only.** Its outcome is the number of effective supplied cells,
    after exactly the supply read — whatever cell demand is installed. -/
theorem count_run (cellsOf : EvalM (List NeedSupply.Sourced)) (demand : Nat → EvalM Result)
    (s : EvalState) :
    (argumentViewBuiltin cellsOf demand .countBuiltin).runState s =
      (match cellsOf.runState s with
       | (.ok cells, t) => (.ok (.atom (Int.ofNat cells.length), 1), t)
       | (.error e, t) => (.error e, t)) := by
  simp only [argumentViewBuiltin, bind_run]
  rcases cellsOf.runState s with ⟨out, t⟩
  cases out <;> rfl

/-- **`count` demands no argument VALUE**: two runs that differ only in cell demand agree. -/
theorem count_demands_nothing (cellsOf : EvalM (List NeedSupply.Sourced))
    (d₁ d₂ : Nat → EvalM Result) (s : EvalState) :
    (argumentViewBuiltin cellsOf d₁ .countBuiltin).runState s =
      (argumentViewBuiltin cellsOf d₂ .countBuiltin).runState s := by
  rw [count_run, count_run]

/-- `first` demands only the FIRST cell: its outcome depends on cell demand only there. -/
theorem first_demands_only_first (cellsOf : EvalM (List NeedSupply.Sourced))
    (d₁ d₂ : Nat → EvalM Result) (s t : EvalState) (cells : List NeedSupply.Sourced)
    (hcells : cellsOf.runState s = (.ok cells, t))
    (hagree : ∀ p, cells.head? = some p → d₁ p.1 = d₂ p.1) :
    (argumentViewBuiltin cellsOf d₁ .firstBuiltin).runState s =
      (argumentViewBuiltin cellsOf d₂ .firstBuiltin).runState s := by
  simp only [argumentViewBuiltin, bind_run, hcells]
  cases hh : cells.head? with
  | none => rfl
  | some p =>
    obtain ⟨c, src⟩ := p
    have h := hagree (c, src) hh
    simp only at h
    simp only [h]

/-- `last` demands only the LAST cell. -/
theorem last_demands_only_last (cellsOf : EvalM (List NeedSupply.Sourced))
    (d₁ d₂ : Nat → EvalM Result) (s t : EvalState) (cells : List NeedSupply.Sourced)
    (hcells : cellsOf.runState s = (.ok cells, t))
    (hagree : ∀ p, cells.getLast? = some p → d₁ p.1 = d₂ p.1) :
    (argumentViewBuiltin cellsOf d₁ .lastBuiltin).runState s =
      (argumentViewBuiltin cellsOf d₂ .lastBuiltin).runState s := by
  simp only [argumentViewBuiltin, bind_run, hcells]
  cases hh : cells.getLast? with
  | none => rfl
  | some p =>
    obtain ⟨c, src⟩ := p
    have h := hagree (c, src) hh
    simp only at h
    simp only [h]

/-- An empty supply has no first or last position: the failure `first([])` reports. -/
theorem first_empty (cellsOf : EvalM (List NeedSupply.Sourced)) (demand : Nat → EvalM Result)
    (s t : EvalState) (hcells : cellsOf.runState s = (.ok [], t)) :
    (argumentViewBuiltin cellsOf demand .firstBuiltin).runState s =
      (.error (argumentViewEmptySelection .firstBuiltin), t) := by
  simp only [argumentViewBuiltin, bind_run, hcells]
  rfl

/-! ## Selection over a view (actual `selectViewWith`) -/

theorem expectInt_readonly (v : Result) (s : EvalState) : ((expectInt v).runState s).2 = s := by
  unfold expectInt
  split
  · rfl
  · rfl
  · split <;> rfl

theorem selectorIndex_readonly (v : Result) (s : EvalState) :
    ((selectorIndex v).runState s).2 = s := by
  simp only [selectorIndex, bind_run]
  have hro := expectInt_readonly v s
  rcases h : (expectInt v).runState s with ⟨o, t⟩
  rw [h] at hro
  simp only at hro
  subst hro
  cases o with
  | error e => rfl
  | ok n =>
    dsimp only
    split <;> rfl

/-- `selectPosition` is `selectorIndex` followed by the receiver's positional view. -/
theorem selectPosition_eq_selectorIndex (receiver selector : Result) (s : EvalState) :
    (selectPosition receiver selector).runState s =
      (do
        let n ← selectorIndex selector
        match Result.select? receiver n with
        | some selected => pure selected
        | none => throw Error.badIndex : EvalM Result).runState s := by
  simp only [selectPosition, selectorIndex, bind_run]
  rcases h : (expectInt selector).runState s with ⟨out, t⟩
  cases out with
  | error e => rfl
  | ok n =>
    dsimp only
    by_cases hn : n < 0
    · simp only [hn, ↓reduceIte]; rfl
    · simp only [hn, ↓reduceIte, pure_run]; rfl

/-- **An empty selection reads nothing**: `R.Arguments[]` prepares no supply. -/
theorem select_empty_reads_nothing {α : Type} (demand : α → EvalM Result)
    (cellsOf : EvalM (List NeedSupply.Sourced)) (demandCell : Nat → EvalM Result) (s : EvalState) :
    (selectViewWith demand cellsOf demandCell []).runState s = (.ok [], s) := rfl

/-- **An invalid selector fails before the supply is read**: a selector VALUE that fails
    `selectorIndex` (a non-number, a negative number) ends the selection with that failure, and
    `cellsOf` — the plan's preparation — never runs. -/
theorem select_invalid_before_supply {α : Type} (demand : α → EvalM Result)
    (cellsOf : EvalM (List NeedSupply.Sourced)) (demandCell : Nat → EvalM Result)
    (selector : α) (rest : List α) (s t : EvalState) (v : Result) (e : Error)
    (hd : (demand selector).runState s = (.ok v, t))
    (hi : ((selectorIndex v).runState t).1 = .error e) :
    (selectViewWith demand cellsOf demandCell (selector :: rest)).runState s = (.error e, t) := by
  have hro := selectorIndex_readonly v t
  simp only [selectViewWith, bind_run, hd]
  rcases hr : (selectorIndex v).runState t with ⟨out, u⟩
  rw [hr] at hi hro
  simp only at hi hro
  subst hi
  subst hro
  rfl

/-- **Selection demands only the selected cell.** For one valid selector, the outcome depends on
    cell demand only at the selected position of the view's supply. -/
theorem select_demands_only_selected {α : Type} (demand : α → EvalM Result)
    (cellsOf : EvalM (List NeedSupply.Sourced)) (d₁ d₂ : Nat → EvalM Result)
    (selector : α) (s t u : EvalState) (v : Result) (n : Nat) (cells : List NeedSupply.Sourced)
    (hd : (demand selector).runState s = (.ok v, t))
    (hi : (selectorIndex v).runState t = (.ok n, t))
    (hcells : cellsOf.runState t = (.ok cells, u))
    (hagree : ∀ p, cells[n]? = some p → d₁ p.1 = d₂ p.1) :
    (selectViewWith demand cellsOf d₁ [selector]).runState s =
      (selectViewWith demand cellsOf d₂ [selector]).runState s := by
  simp only [selectViewWith, bind_run, hd, hi, hcells]
  cases hp : cells[n]? with
  | none => rfl
  | some p =>
    obtain ⟨c, src⟩ := p
    have h := hagree (c, src) hp
    simp only at h
    simp only [h]

/-! ## The VALUE openers never open a view; elsewhere they are the pre-S2 openers -/

/-- The values a spread's successive stars open. -/
def openingAt : Nat → Result → Result
  | 0, v => v
  | Nat.succ n, v => openingAt n (Result.normalize (Result.sequenceValue v.spreadItems))

def isView : Result → Bool
  | .argView _ => true
  | _ => false

/-- **Conservative extension.** Wherever no star opens a view, `openSpreadItems` is the pre-S2
    opening `reopenSpreadLayers n v.spreadItems` exactly. -/
theorem openSpreadItems_eq_reopen : ∀ (n : Nat) (v : Result),
    (∀ k, k ≤ n → isView (openingAt k v) = false) →
    openSpreadItems n v = .ok (reopenSpreadLayers n v.spreadItems)
  | 0, v, h => by
    have h0 := h 0 (Nat.le_refl 0)
    cases v <;> simp_all [openSpreadItems, openingAt, isView, reopenSpreadLayers]
  | Nat.succ n, v, h => by
    have h0 := h 0 (Nat.zero_le _)
    have hrest : ∀ k, k ≤ n → isView (openingAt k (Result.normalize (Result.sequenceValue v.spreadItems))) = false :=
      fun k hk => h (k + 1) (Nat.succ_le_succ hk)
    have ih := openSpreadItems_eq_reopen n _ hrest
    cases v <;> simp_all [openSpreadItems, openingAt, isView, reopenSpreadLayers, reopenSpreadItems]

/-- A star that would open a view into values is refused. -/
theorem openSpreadItems_refuses_view (n a : Nat) :
    openSpreadItems n (.argView a) = .error (.typeMismatch argumentViewSpreadMessage) := by
  cases n <;> rfl

/-- The supply opener transports a view exactly when the LAST star opens it. -/
theorem openSupplySpread_view (a : Nat) : openSupplySpread 0 (.argView a) = .ok (.view a) := rfl

/-- **Conservative extension of supply formation.** Wherever no star opens a view, the supply
    opener yields the pre-S2 items. -/
theorem openSupplySpread_eq_items : ∀ (n : Nat) (v : Result),
    (∀ k, k ≤ n → isView (openingAt k v) = false) →
    openSupplySpread n v = .ok (.items (reopenSpreadLayers n v.spreadItems))
  | 0, v, h => by
    have h0 := h 0 (Nat.le_refl 0)
    cases v <;> simp_all [openSupplySpread, openSpreadItems, openingAt, isView, reopenSpreadLayers] <;> rfl
  | Nat.succ n, v, h => by
    have h0 := h 0 (Nat.zero_le _)
    have hrest : ∀ k, k ≤ n → isView (openingAt k (Result.normalize (Result.sequenceValue v.spreadItems))) = false :=
      fun k hk => h (k + 1) (Nat.succ_le_succ hk)
    have ih := openSupplySpread_eq_items n _ hrest
    cases v <;> simp_all [openSupplySpread, openingAt, isView, reopenSpreadLayers, reopenSpreadItems]

/-- **The stacked star is the grouped recapture, view refusal included** (S5, October 2026).
    For every value and every number of further stars, `n + 1` further stacked stars over a
    first opening open exactly what the GROUPED spelling opens: the first star's items, the
    capture arm's shallow combination of the spread's recovered slots
    (`combineOutputSlots ∘ countedTopLevelValues ∘ spreadSupplyResult`, the production route of
    `(A*)`), then the remaining stars — and an argument view is refused at the same point with
    the same error. No premise: this composes S2's checked opening with the value-level grouped
    layer law (`grouped_spread_layer_is_reopen`). It is about the total helpers; that the
    `partial` evaluator routes `A**` and `(A*)*` through them, and evaluates `A` once, stays a
    fact of its source (CoreTests `RepeatedSpread`). It says nothing about resources: C#'s
    grouped spelling reserves its inner supply a second time
    (`SequenceConstructSpreadReviewTests.StackedAndGroupedSpreadAgreeInValueButCanDifferUnderAResourceLimit`).
    `(V)*` — one star over a grouped VALUE — is a different spelling (`openSupplySpread 0`). -/
theorem stacked_star_is_grouped_recapture (n : Nat) (v : Result) :
    openSpreadItems (n + 1) v =
      ((openSpreadItems 0 v).bind fun items =>
        openSpreadItems n (combineOutputSlots (countedTopLevelValues (spreadSupplyResult items)))) := by
  cases v <;>
    simp [openSpreadItems, Except.bind, countedTopLevelValues_spreadSupplyResult,
      ← normalize_sequenceValue_eq_combineOutputSlots_map_normalize]

/-! ## The run boundary -/

theorem view_contains_reference (a : Nat) : (Result.argView a).containsCallRef = true := rfl

/-- A run result containing a view is refused, as one containing a reference. -/
theorem export_refuses_view (a : Nat) (s : EvalState) :
    (exportRunValue (.argView a)).runState s = (.error (.typeMismatch callReferenceLeavesRunMessage), s) :=
  KatLang.CallReferenceLaws.export_refuses _ s rfl

end KatLang.ArgumentViewLaws
