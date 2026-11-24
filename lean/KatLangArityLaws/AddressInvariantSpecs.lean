import KatLangArityLaws.AddressInvariantTactic

open KatLang KatLang.NeedControl.Allocation KatLang.HeapAddressValidity KatLang.AddressInvariant
open KatLang.CallPlan (bind_run map_run get_run pure_run modify_run throw_run lift_run evalAttempt_run
  effective_caller effective_values)

/-!
# FG-H1-FU-01 (M2): the callback-parameterized helper contracts

The supply former, invocation plans (preparation, route, callee cell, execution, invocation,
argument views), links (receiver cell, decoding), the VALUE and CALLABLE completion shells and
the loop setup are proved here for EVERY callback satisfying its named contract (`SpreadSpec`,
`ClassifySpec`, `ProjectSpec`, `DemandSpec`, `EvSpec`, `RouteSpec`). Each contract speaks only of
the callback's own inputs and result. Every contract is registered with `ht_tac`.
-/

namespace KatLang.AddressInvariant

/-! ## Registration of the primitive contracts -/

attribute [ht_spec] allocate_spec ready_spec supply_spec captured_spec record_spec bindParameters_spec enterAlgorithmBody_spec enterPropertyOwnerBody_spec needBindingContext_spec parameterContext_spec needActivateBranch_spec identifyRuntimeAlgorithm_spec

/-! ## The input records (ledger R-1): written, never address-bearing -/

/-- A step of the input records (ledger R-1): refused in the state it started from, or the input
    records rewritten — no address is stored there. -/
theorem cellInputsStep_spec {P : Array NeedCell → Prop} {α : Type}
    {step : CellRecords → Except Error (α × CellRecords)} :
    SoundI P (cellInputsStep step) (fun _ _ => True) :=
  SoundI.of_inputsOnly (fun s _ _ => ⟨by
      rw [cellInputsStep_run]
      cases step s.cellInputs <;> rfl,
    fun _ _ => trivial⟩)

theorem noteCellInput_spec {P : Array NeedCell → Prop} {ctx : EvalCtx} {a : Nat} {e : Error} :
    SoundI P (noteCellInput ctx a e) (fun _ _ => True) :=
  SoundI.of_inputsOnly (fun s _ _ => ⟨by
      rw [noteCellInput_run]
      split
      · rfl
      · exact EvalState.noteInput_eq _ _ _,
    fun _ _ => trivial⟩)

theorem recordCellInputs_spec {P : Array NeedCell → Prop} {address watermark : Nat} {refusal : Error} :
    SoundI P (recordCellInputs address watermark refusal) (fun _ _ => True) :=
  cellInputsStep_spec

theorem noteLocalOnlyRead_spec {P : Array NeedCell → Prop} {binding : PropDef} {a : Algorithm} {ctx : EvalCtx} :
    SoundI P (noteLocalOnlyRead binding a ctx) (fun _ _ => True) := by
  unfold noteLocalOnlyRead
  split
  · exact noteCellInput_spec
  · exact SoundI.pure () (fun _ _ => trivial)

/-- An admitted member access inside a retained cell's computation is a note (ledger R-1). -/
theorem noteMemberAccess_spec {P : Array NeedCell → Prop} {ctx : EvalCtx} {container : Algorithm}
    {p : PropDef} {refusal : Error} :
    SoundI P (noteMemberAccess ctx container p refusal) (fun _ _ => True) := by
  unfold noteMemberAccess
  split
  · exact SoundI.pure () (fun _ _ => trivial)
  · split
    · exact noteCellInput_spec
    · exact SoundI.pure () (fun _ _ => trivial)

/-- The judgment of a reuse is a step of the input records. -/
theorem judgeRetainedCellReuse_spec {P : Array NeedCell → Prop} {cell : Nat} {ctx : EvalCtx} :
    SoundI P (judgeRetainedCellReuse cell ctx) (fun _ _ => True) :=
  cellInputsStep_spec

attribute [ht_spec] cellInputsStep_spec noteCellInput_spec recordCellInputs_spec noteLocalOnlyRead_spec
  noteMemberAccess_spec judgeRetainedCellReuse_spec

/-! ## Callback contracts -/

/-- The computed-spread capability: Ready payloads and transported cells valid. -/
def SpreadSpec (spread : NeedSupply.SpreadEval) : Prop :=
  ∀ e ctx env, SoundI (fun h => ValidCtx h ctx ∧ VEV h env) (spread e ctx env) (fun x h => SupplyV h x)

/-- The route classifier: from a valid captured caller. -/
def ClassifySpec (classify : NeedPlan.CallShape → EvalM PlanRoute) : Prop :=
  ∀ shape, SoundI (fun h => ValidCtx h shape.caller ∧ VEV h shape.values) (classify shape) (fun _ _ => True)

/-- A CALLABLE capability over a valid address. -/
def ProjectSpec (project : Nat → EvalM (Option Algorithm)) : Prop :=
  ∀ a, SoundI (fun h => a < h.size) (project a) (fun _ _ => True)

/-- A VALUE capability over a valid address. -/
def DemandSpec (demand : Nat → EvalM CountedResult) : Prop :=
  ∀ a, SoundI (fun h => a < h.size) (demand a) (fun r h => CRV h r)

/-- A written-expression evaluator. -/
def EvSpec (ev : Expr → EvalCtx → ValEnv → EvalM CountedResult) : Prop :=
  ∀ e ctx env, SoundI (fun h => ValidCtx h ctx ∧ VEV h env) (ev e ctx env) (fun r h => CRV h r)

/-- A written-expression resolver. -/
def WrittenSpec (written : Expr → EvalCtx → EvalM (Option Algorithm)) : Prop :=
  ∀ e ctx, SoundI (fun h => ValidCtx h ctx) (written e ctx) (fun _ _ => True)

/-- An invocation-plan route. -/
structure RouteSpec (route : NeedPlan.Route) : Prop where
  target : ∀ e ctx, SoundI (fun h => ValidCtx h ctx) (route.target e ctx) (fun _ _ => True)
  normalize : ∀ a ctx, SoundI (fun h => ValidCtx h ctx) (route.normalize a ctx) (fun _ _ => True)
  dispatch : ∀ origin callee cells ctx env name,
    SoundI (fun h => OriginV h origin ∧ ValidSourced h cells ∧ ValidCtx h ctx ∧ VEV h env)
      (route.dispatch origin callee cells ctx env name) (fun r h => CRV h r)
  spread : SpreadSpec route.spread
  classify : ClassifySpec route.classify
  project : ProjectSpec route.project

theorem hmono_ctx_env (ctx : EvalCtx) (env : ValEnv) : HMono (fun h => ValidCtx h ctx ∧ VEV h env) :=
  fun _ _ g v => ⟨ValidCtx.mono g v.1, VEV.mono g v.2⟩
theorem hmono_ctx (ctx : EvalCtx) : HMono (fun h => ValidCtx h ctx) := fun _ _ g v => ValidCtx.mono g v
theorem hmono_lt (a : Nat) : HMono (fun h => a < h.size) := fun _ _ g v => Nat.lt_of_lt_of_le v g

theorem SpreadSpec.app {P : Array NeedCell → Prop} {spread : NeedSupply.SpreadEval} (hs : SpreadSpec spread)
    {e : Expr} {ctx : EvalCtx} {env : ValEnv} (hreq : ∀ h, P h → ValidCtx h ctx ∧ VEV h env) :
    SoundI P (spread e ctx env) (fun x h => SupplyV h x) :=
  SoundI.weaken (hs e ctx env) hreq (hmono_ctx_env ctx env) (fun _ _ h => h)

theorem ClassifySpec.app {P : Array NeedCell → Prop} {classify : NeedPlan.CallShape → EvalM PlanRoute}
    (hc : ClassifySpec classify) {shape : NeedPlan.CallShape}
    (hreq : ∀ h, P h → ValidCtx h shape.caller ∧ VEV h shape.values) :
    SoundI P (classify shape) (fun _ _ => True) :=
  SoundI.weaken (hc shape) hreq (hmono_ctx_env _ _) (fun _ _ h => h)

theorem ProjectSpec.app {P : Array NeedCell → Prop} {project : Nat → EvalM (Option Algorithm)}
    (hp : ProjectSpec project) {a : Nat} (hreq : ∀ h, P h → a < h.size) :
    SoundI P (project a) (fun _ _ => True) :=
  SoundI.weaken (hp a) hreq (hmono_lt a) (fun _ _ h => h)

theorem DemandSpec.app {P : Array NeedCell → Prop} {demand : Nat → EvalM CountedResult}
    (hd : DemandSpec demand) {a : Nat} (hreq : ∀ h, P h → a < h.size) :
    SoundI P (demand a) (fun r h => CRV h r) :=
  SoundI.weaken (hd a) hreq (hmono_lt a) (fun _ _ h => h)

theorem EvSpec.app {P : Array NeedCell → Prop} {ev : Expr → EvalCtx → ValEnv → EvalM CountedResult}
    (hev : EvSpec ev) {e : Expr} {ctx : EvalCtx} {env : ValEnv}
    (hreq : ∀ h, P h → ValidCtx h ctx ∧ VEV h env) : SoundI P (ev e ctx env) (fun r h => CRV h r) :=
  SoundI.weaken (hev e ctx env) hreq (hmono_ctx_env ctx env) (fun _ _ h => h)

theorem WrittenSpec.app {P : Array NeedCell → Prop} {written : Expr → EvalCtx → EvalM (Option Algorithm)}
    (hw : WrittenSpec written) {e : Expr} {ctx : EvalCtx} (hreq : ∀ h, P h → ValidCtx h ctx) :
    SoundI P (written e ctx) (fun _ _ => True) :=
  SoundI.weaken (hw e ctx) hreq (hmono_ctx ctx) (fun _ _ h => h)

theorem RouteSpec.target_app {P : Array NeedCell → Prop} {route : NeedPlan.Route} (hr : RouteSpec route)
    {e : Expr} {ctx : EvalCtx} (hreq : ∀ h, P h → ValidCtx h ctx) :
    SoundI P (route.target e ctx) (fun _ _ => True) :=
  SoundI.weaken (hr.target e ctx) hreq (hmono_ctx ctx) (fun _ _ h => h)

theorem RouteSpec.normalize_app {P : Array NeedCell → Prop} {route : NeedPlan.Route} (hr : RouteSpec route)
    {a : Algorithm} {ctx : EvalCtx} (hreq : ∀ h, P h → ValidCtx h ctx) :
    SoundI P (route.normalize a ctx) (fun _ _ => True) :=
  SoundI.weaken (hr.normalize a ctx) hreq (hmono_ctx ctx) (fun _ _ h => h)

theorem RouteSpec.dispatch_app {P : Array NeedCell → Prop} {route : NeedPlan.Route} (hr : RouteSpec route)
    {origin : CalleeOrigin} {callee : Algorithm} {cells : List NeedSupply.Sourced} {ctx : EvalCtx}
    {env : ValEnv} {name : String}
    (hreq : ∀ h, P h → OriginV h origin ∧ ValidSourced h cells ∧ ValidCtx h ctx ∧ VEV h env) :
    SoundI P (route.dispatch origin callee cells ctx env name) (fun r h => CRV h r) :=
  SoundI.weaken (hr.dispatch origin callee cells ctx env name) hreq
    (fun _ _ g v => ⟨OriginV.mono g v.1, ValidSourced.mono g v.2.1, ValidCtx.mono g v.2.2.1, VEV.mono g v.2.2.2⟩)
    (fun _ _ h => h)

theorem RouteSpec.project_app {P : Array NeedCell → Prop} {route : NeedPlan.Route} (hr : RouteSpec route)
    {a : Nat} (hreq : ∀ h, P h → a < h.size) : SoundI P (route.project a) (fun _ _ => True) :=
  hr.project.app hreq
theorem RouteSpec.classify_app {P : Array NeedCell → Prop} {route : NeedPlan.Route} (hr : RouteSpec route)
    {shape : NeedPlan.CallShape} (hreq : ∀ h, P h → ValidCtx h shape.caller ∧ VEV h shape.values) :
    SoundI P (route.classify shape) (fun _ _ => True) :=
  hr.classify.app hreq
theorem RouteSpec.spread_app {P : Array NeedCell → Prop} {route : NeedPlan.Route} (hr : RouteSpec route)
    {e : Expr} {ctx : EvalCtx} {env : ValEnv} (hreq : ∀ h, P h → ValidCtx h ctx ∧ VEV h env) :
    SoundI P (route.spread e ctx env) (fun x h => SupplyV h x) :=
  hr.spread.app hreq

attribute [ht_spec] SpreadSpec.app ClassifySpec.app ProjectSpec.app DemandSpec.app EvSpec.app WrittenSpec.app RouteSpec.target_app RouteSpec.normalize_app RouteSpec.dispatch_app RouteSpec.project_app RouteSpec.classify_app RouteSpec.spread_app
attribute [ht_lemmas] RouteSpec.spread RouteSpec.classify RouteSpec.project
attribute [ht_fwd] RouteSpec.spread RouteSpec.classify RouteSpec.project

/-! ## Shapes of plans -/

theorem callShape_ctx {e : Expr} {c : EvalCtx} {v : ValEnv} {shape : NeedPlan.CallShape}
    (h : NeedPlan.callShape? e c v = some shape) : shape.caller = c ∧ shape.values = v := by
  unfold NeedPlan.callShape? at h
  split at h
  · split at h <;> (try cases h) <;> exact ⟨rfl, rfl⟩
  · cases h; exact ⟨rfl, rfl⟩
  · cases h

theorem ofSuspension_ctx {susp : NeedSuspension} {shape : NeedPlan.CallShape}
    (h : NeedPlan.ofSuspension? susp = some shape) :
    ∃ e, susp = .expression e shape.caller shape.values := by
  cases susp with
  | expression e c v =>
    obtain ⟨h1, h2⟩ := callShape_ctx h
    exact ⟨e, by rw [h1, h2]⟩
  | collector _ => cases h
  | ready _ => cases h
  | applied _ _ _ _ _ => cases h

theorem CellV.shape_ctx {h : Array NeedCell} {c : NeedCell} (v : CellV h c) {shape : NeedPlan.CallShape}
    (hs : NeedPlan.ofSuspension? c.suspension = some shape) : ValidCtx h shape.caller := by
  obtain ⟨e, he⟩ := ofSuspension_ctx hs
  exact v.expr_ctx he

theorem CellV.shape_values {h : Array NeedCell} {c : NeedCell} (v : CellV h c) {shape : NeedPlan.CallShape}
    (hs : NeedPlan.ofSuspension? c.suspension = some shape) : VEV h shape.values := by
  obtain ⟨e, he⟩ := ofSuspension_ctx hs
  exact v.expr_values he

theorem GotV.shape_ctx {st : EvalState} {h : Array NeedCell} (v : GotV st h) {a : Nat}
    {shape : NeedPlan.CallShape} (hs : NeedPlan.shapeAt? st.needs a = some shape) :
    ValidCtx h shape.caller := by
  unfold NeedPlan.shapeAt? at hs
  split at hs
  · rename_i cell hcell; exact (v.cell hcell).shape_ctx hs
  · cases hs

theorem GotV.shape_values {st : EvalState} {h : Array NeedCell} (v : GotV st h) {a : Nat}
    {shape : NeedPlan.CallShape} (hs : NeedPlan.shapeAt? st.needs a = some shape) :
    VEV h shape.values := by
  unfold NeedPlan.shapeAt? at hs
  split at hs
  · rename_i cell hcell; exact (v.cell hcell).shape_values hs
  · cases hs

theorem GotV.shape_lt {st : EvalState} {h : Array NeedCell} (v : GotV st h) {a : Nat}
    {shape : NeedPlan.CallShape} (hs : NeedPlan.shapeAt? st.needs a = some shape) : a < h.size := by
  unfold NeedPlan.shapeAt? at hs
  split at hs
  · rename_i cell hcell; exact v.lt hcell
  · cases hs

theorem effective_ctx {h : Array NeedCell} {shape : NeedPlan.CallShape} (r : PlanRoute)
    (v : ValidCtx h shape.caller) : ValidCtx h (NeedPlan.effective shape r).caller := by
  rw [effective_caller]; exact v

theorem effective_vals {h : Array NeedCell} {shape : NeedPlan.CallShape} (r : PlanRoute)
    (v : VEV h shape.values) : VEV h (NeedPlan.effective shape r).values := by
  rw [effective_values]; exact v

theorem callShape_ctx_valid {h : Array NeedCell} {e : Expr} {c : EvalCtx} {vals : ValEnv}
    {shape : NeedPlan.CallShape} (hs : NeedPlan.callShape? e c vals = some shape) (v : ValidCtx h c) :
    ValidCtx h shape.caller := by rw [(callShape_ctx hs).1]; exact v

theorem callShape_vals_valid {h : Array NeedCell} {e : Expr} {c : EvalCtx} {vals : ValEnv}
    {shape : NeedPlan.CallShape} (hs : NeedPlan.callShape? e c vals = some shape) (v : VEV h vals) :
    VEV h shape.values := by rw [(callShape_ctx hs).2]; exact v

attribute [ht_lemmas] CellV.shape_ctx CellV.shape_values GotV.shape_ctx GotV.shape_values GotV.shape_lt
  effective_ctx effective_vals callShape_ctx_valid callShape_vals_valid
attribute [ht_fwd] CellV.shape_ctx CellV.shape_values GotV.shape_ctx GotV.shape_values GotV.shape_lt
  callShape_ctx_valid callShape_vals_valid

theorem RV.callRef_some {h : Array NeedCell} {val : Result} {a : Nat} (v : RV h val)
    (e : val = .callRef a) : a < h.size := by subst e; exact RV.callRef_lt v
attribute [ht_lemmas] RV.callRef_some

/-! ## Small helpers -/

theorem decodeCallRef_spec {P : Array NeedCell → Prop} {val : Result} (hreq : ∀ h, P h → RV h val) :
    SoundI P (decodeCallRef val) (fun a h => a < h.size) := by
  unfold decodeCallRef; ht_tac

attribute [ht_spec] decodeCallRef_spec

/-! ## Supply formation -/

theorem needWrittenSource_spec {P : Array NeedCell → Prop} {a : Nat} :
    SoundI P (needWrittenSource? a) (fun _ _ => True) := by
  unfold needWrittenSource?; ht_tac

theorem spreadCollectorSlice_spec {P : Array NeedCell → Prop} {operand : Expr} {caller : EvalCtx} :
    SoundI P (spreadCollectorSlice? operand caller)
      (fun r h => OptSliceV h r) := by
  refine SoundI.of_inputsOnly (fun s vs _ => ?_)
  obtain ⟨r, t, hr, ht, hfound⟩ := slice_run operand caller s
  rw [hr]
  refine ⟨ht, fun x hx slice hslice => ?_⟩
  subst hx hslice
  obtain ⟨a, cell, hc, hs⟩ := hfound slice rfl
  exact collector_members_valid vs.collectors hc hs

attribute [ht_spec] needWrittenSource_spec spreadCollectorSlice_spec

theorem SupplyV.items {h : Array NeedCell} {values : List Result} (v : SupplyV h (.items values)) : RLV h values := v
theorem SupplyV.cells {h : Array NeedCell} {cells : List NeedSupply.Sourced} (v : SupplyV h (.cells cells)) :
    ValidSourced h cells := v
attribute [ht_lemmas] SupplyV.items SupplyV.cells

theorem slot_spec {P : Array NeedCell → Prop} {spread : NeedSupply.SpreadEval} {ctx : EvalCtx}
    {env : ValEnv} {e : Expr} (hs : SpreadSpec spread) (hreq : ∀ h, P h → ValidCtx h ctx ∧ VEV h env) :
    SoundI P (NeedSupply.slot spread ctx env e) (fun xs h => ValidSourced h xs) := by
  unfold NeedSupply.slot; ht_tac

theorem form_spec {P : Array NeedCell → Prop} {spread : NeedSupply.SpreadEval} {ctx : EvalCtx}
    {env : ValEnv} {args : OutputBundle} (hs : SpreadSpec spread)
    (hreq : ∀ h, P h → ValidCtx h ctx ∧ VEV h env) :
    SoundI P (NeedSupply.form spread ctx env args) (fun xs h => ValidSourced h xs) := by
  induction args generalizing P with
  | nil => unfold NeedSupply.form; ht_tac
  | cons e rest ih =>
    unfold NeedSupply.form
    refine SoundI.bind (slot_spec hs hreq) (fun _ _ _ g v => ValidSourced.mono g v) ?_
    intro head
    refine SoundI.bind (ih (fun h ph => hreq h ph.1)) (fun _ _ _ g v => ValidSourced.mono g v) ?_
    intro tail
    exact SoundI.pure _ (fun h ph => ValidSourced.append ph.1.2 ph.2)

theorem addresses_spec {P : Array NeedCell → Prop} {spread : NeedSupply.SpreadEval} {ctx : EvalCtx}
    {env : ValEnv} {args : OutputBundle} (hs : SpreadSpec spread)
    (hreq : ∀ h, P h → ValidCtx h ctx ∧ VEV h env) :
    SoundI P (NeedSupply.addresses spread ctx env args) (fun xs h => ValidAddresses h xs) := by
  unfold NeedSupply.addresses
  refine SoundI.bind (form_spec hs hreq) (fun _ _ _ g v => ValidSourced.mono g v) ?_
  intro xs
  exact SoundI.pure _ (fun h ph => ph.2.addresses)

attribute [ht_spec] form_spec addresses_spec

/-! ## Invocation plans -/

theorem routeOf_spec {P : Array NeedCell → Prop} {classify : NeedPlan.CallShape → EvalM PlanRoute}
    {a : Nat} {shape : NeedPlan.CallShape} (hc : ClassifySpec classify)
    (hreq : ∀ h, P h → ValidCtx h shape.caller ∧ VEV h shape.values) :
    SoundI P (NeedPlan.routeOf classify a shape) (fun _ _ => True) := by
  unfold NeedPlan.routeOf NeedPlan.setRoute; ht_tac

/-- **The plan-supply write point.** Every `.prepared (.ok cells)` stored by `prepare` is valid
    in the heap at its write (`setSupply`), hence an `Inv` clause. -/
theorem prepare_spec {P : Array NeedCell → Prop} {spread : NeedSupply.SpreadEval}
    {a : Nat} {shape : NeedPlan.CallShape} (hs : SpreadSpec spread)
    (hreq : ∀ h, P h → ValidCtx h shape.caller ∧ VEV h shape.values) :
    SoundI P (NeedPlan.prepare spread a shape) (fun xs h => ValidSourced h xs) := by
  unfold NeedPlan.prepare NeedPlan.setSupply
  ht_tac

attribute [ht_spec] routeOf_spec prepare_spec

/-- **The callee-link write point.** The selected address remains valid after classification,
    including when a re-entrant callback recorded a different link before `setCallee`. -/
theorem calleeCell_spec {P : Array NeedCell → Prop} {classify : NeedPlan.CallShape → EvalM PlanRoute}
    {a : Nat} (hc : ClassifySpec classify) :
    SoundI P (NeedPlan.calleeCell classify a) (fun c h => c < h.size) := by
  unfold NeedPlan.calleeCell NeedPlan.setCallee; ht_tac

attribute [ht_spec] calleeCell_spec

/-- A callback over a context (callee resolvers, normalizers, receiver resolvers). -/
def CtxSpec {β α : Type} (f : β → EvalCtx → EvalM α) : Prop :=
  ∀ b ctx, SoundI (fun h => ValidCtx h ctx) (f b ctx) (fun _ _ => True)

theorem CtxSpec.app {P : Array NeedCell → Prop} {β α : Type} {f : β → EvalCtx → EvalM α}
    (hf : CtxSpec f) {b : β} {ctx : EvalCtx} (hreq : ∀ h, P h → ValidCtx h ctx) :
    SoundI P (f b ctx) (fun _ _ => True) :=
  SoundI.weaken (hf b ctx) hreq (hmono_ctx ctx) (fun _ _ h => h)

attribute [ht_spec] CtxSpec.app

theorem calleeAlong_spec {P : Array NeedCell → Prop} {route : NeedPlan.Route} {a : Nat}
    {eff : NeedPlan.CallShape} {r : PlanRoute} (hr : RouteSpec route)
    (hreq : ∀ h, P h → ValidCtx h eff.caller) :
    SoundI P (NeedPlan.calleeAlong route a eff r) (fun _ _ => True) := by
  cases r <;> (unfold NeedPlan.calleeAlong; ht_tac)

theorem dispatchName_spec {P : Array NeedCell → Prop} {a : Nat} {eff : NeedPlan.CallShape} {r : PlanRoute} :
    SoundI P (NeedPlan.dispatchName a eff r) (fun _ _ => True) := by
  unfold NeedPlan.dispatchName; ht_tac

theorem dispatchOriginIn_valid {h : Array NeedCell} {needs : Array NeedCell} (st : EvalState)
    (v : GotV st h) (hn : needs = st.needs) {a : Nat} {eff : NeedPlan.CallShape} {r : PlanRoute}
    (vc : ValidCtx h eff.caller) : OriginV h (NeedPlan.dispatchOriginIn needs a eff r) := by
  subst hn
  cases r with
  | algorithm =>
    simp only [NeedPlan.dispatchOriginIn]
    split
    · rename_i c hc
      simp only [Option.bind_eq_some_iff] at hc
      obtain ⟨p, _, cell, hcell, hcallee⟩ := hc
      exact (v.cell hcell).callee_lt hcallee
    · trivial
  | call => exact vc
  | extension => exact vc
  | intrinsic => exact vc

theorem dispatchOrigin_spec {P : Array NeedCell → Prop} {a : Nat} {eff : NeedPlan.CallShape} {r : PlanRoute}
    (hreq : ∀ h, P h → ValidCtx h eff.caller) :
    SoundI P (NeedPlan.dispatchOrigin a eff r) (fun o h => OriginV h o) := by
  intro hp s vs ps
  refine ⟨vs, Nat.le_refl _, fun x hx => ?_⟩
  cases hx
  exact dispatchOriginIn_valid s ⟨vs, Nat.le_refl _⟩ rfl (hreq _ ps)

attribute [ht_spec] calleeAlong_spec dispatchName_spec dispatchOrigin_spec

theorem executeAlong_spec {P : Array NeedCell → Prop} {route : NeedPlan.Route} {a : Nat}
    {shape : NeedPlan.CallShape} {r : PlanRoute} (hr : RouteSpec route)
    (hreq : ∀ h, P h → ValidCtx h shape.caller ∧ VEV h shape.values) :
    SoundI P (NeedPlan.executeAlong route a shape r) (fun x h => CRV h x) := by
  unfold NeedPlan.executeAlong; ht_tac

attribute [ht_spec] executeAlong_spec

theorem execute_spec {P : Array NeedCell → Prop} {route : NeedPlan.Route} {a : Nat}
    {shape : NeedPlan.CallShape} (hr : RouteSpec route)
    (hreq : ∀ h, P h → ValidCtx h shape.caller ∧ VEV h shape.values) :
    SoundI P (NeedPlan.execute route a shape) (fun x h => CRV h x) := by
  unfold NeedPlan.execute; ht_tac

attribute [ht_spec] execute_spec

theorem invoke_spec {P : Array NeedCell → Prop} {route : NeedPlan.Route} {r : NeedPlan.CallReference}
    (hr : RouteSpec route) : SoundI P (NeedPlan.invoke route r) (fun x h => CRV h x) := by
  unfold NeedPlan.invoke; ht_tac

theorem viewCells_spec {P : Array NeedCell → Prop} {spread : NeedSupply.SpreadEval}
    {classify : NeedPlan.CallShape → EvalM PlanRoute} {a : Nat} (hs : SpreadSpec spread)
    (hc : ClassifySpec classify) :
    SoundI P (NeedPlan.viewCells spread classify a) (fun xs h => ValidSourced h xs) := by
  unfold NeedPlan.viewCells; ht_tac

attribute [ht_spec] invoke_spec viewCells_spec

theorem viewSupply_spec {P : Array NeedCell → Prop} {spread : NeedSupply.SpreadEval}
    {classify : NeedPlan.CallShape → EvalM PlanRoute} {a : Nat} (hs : SpreadSpec spread)
    (hc : ClassifySpec classify) :
    SoundI P (NeedPlan.viewSupply spread classify a) (fun x h => SupplyV h x) := by
  unfold NeedPlan.viewSupply; ht_tac

theorem calleeName_spec {P : Array NeedCell → Prop} {a : Nat} :
    SoundI P (NeedPlan.calleeName a) (fun _ _ => True) := by
  unfold NeedPlan.calleeName; ht_tac

theorem reify_spec {P : Array NeedCell → Prop} {a : Nat} :
    SoundI P (NeedPlan.reify a) (fun r h => r.plan < h.size) := by
  intro _ s vs _
  have hrun : (NeedPlan.reify a).runState s = (NeedPlan.reifyResult s.needs a, s) := by
    unfold NeedPlan.reify
    rw [KatLang.CallPlan.bind_run, KatLang.CallPlan.get_run]
    exact KatLang.CallPlan.lift_run _ _
  rw [hrun]
  refine ⟨vs, Nat.le_refl _, fun x hx => ?_⟩
  simp only at hx
  unfold NeedPlan.reifyResult at hx
  split at hx
  · rename_i shape hsh
    cases hx
    exact GotV.shape_lt ⟨vs, Nat.le_refl _⟩ hsh
  · cases hx

attribute [ht_spec] reify_spec

theorem reference_spec {P : Array NeedCell → Prop} {a : Nat} :
    SoundI P (NeedPlan.reference a) (fun r h => r < h.size) := by
  unfold NeedPlan.reference; ht_tac

attribute [ht_spec] viewSupply_spec calleeName_spec reference_spec

/-! ## Links -/

theorem receiverCell_spec {P : Array NeedCell → Prop} {a : Nat} :
    SoundI P (NeedLink.receiverCell a) (fun r h => r < h.size) := by
  unfold NeedLink.receiverCell NeedLink.setReceiver; ht_tac

attribute [ht_spec] receiverCell_spec

theorem decodeCallee_spec {P : Array NeedCell → Prop} {classify : NeedPlan.CallShape → EvalM PlanRoute}
    {demand : Nat → EvalM CountedResult} {a : Nat} (hc : ClassifySpec classify) (hd : DemandSpec demand) :
    SoundI P (NeedLink.decodeCallee classify demand a) (fun r h => r < h.size) := by
  unfold NeedLink.decodeCallee; ht_tac

attribute [ht_spec] decodeCallee_spec

theorem linkValue_spec {P : Array NeedCell → Prop} {classify : NeedPlan.CallShape → EvalM PlanRoute}
    {demand : Nat → EvalM CountedResult} {a : Nat} (hc : ClassifySpec classify) (hd : DemandSpec demand) :
    SoundI P (NeedLink.value classify demand a) (fun r h => CRV h r) := by
  unfold NeedLink.value; ht_tac

theorem linkCallable_spec {P : Array NeedCell → Prop} {classify : NeedPlan.CallShape → EvalM PlanRoute}
    {demand : Nat → EvalM CountedResult} {project : Nat → EvalM (Option Algorithm)} {a : Nat}
    (hc : ClassifySpec classify) (hd : DemandSpec demand) (hp : ProjectSpec project) :
    SoundI P (NeedLink.callable classify demand project a) (fun _ _ => True) := by
  unfold NeedLink.callable; ht_tac

attribute [ht_spec] linkValue_spec linkCallable_spec

/-! ## The VALUE and CALLABLE completion shells -/

theorem materialize_spec {P : Array NeedCell → Prop} {demand : Nat → EvalM CountedResult}
    {slice : List Nat} (hd : DemandSpec demand) (hreq : ∀ h, P h → ValidAddresses h slice) :
    SoundI P (NeedDemand.materialize demand slice) (fun r h => CRV h r) := by
  unfold NeedDemand.materialize makeCollectionListResult; ht_tac

attribute [ht_spec] materialize_spec

theorem suspendedValue_spec {P : Array NeedCell → Prop} {ev : Expr → EvalCtx → ValEnv → EvalM CountedResult}
    {route : NeedPlan.Route} {demand : Nat → EvalM CountedResult} {a : Nat} {susp : NeedSuspension}
    (hev : EvSpec ev) (hr : RouteSpec route) (hd : DemandSpec demand)
    (hreq : ∀ h, P h → SuspV h susp) :
    SoundI P (NeedDemand.suspendedValue ev route demand a susp) (fun r h => CRV h r) := by
  cases susp <;> (unfold NeedDemand.suspendedValue reCountValueBoundary; ht_tac)
  -- A Ready cell holding a deferred list item demands that position's cell (issue #204): the
  -- cell is inside the heap because the Ready value is valid.
  rename_i value _ cell heq
  intro h hp
  have hv : RV h value.1 := hreq h hp
  rw [heq] at hv
  exact RV.deferred_iff.mp hv

attribute [ht_spec] suspendedValue_spec

/-- **The VALUE write point.** `NeedDemand.step` stores `.evaluating`, then the outcome of the
    cell's computation, valid in the heap at that write. -/
theorem demandStep_spec {P : Array NeedCell → Prop} {ev : Expr → EvalCtx → ValEnv → EvalM CountedResult}
    {route : NeedPlan.Route} {demand : Nat → EvalM CountedResult} {a : Nat}
    (hev : EvSpec ev) (hr : RouteSpec route) (hd : DemandSpec demand) :
    SoundI P (NeedDemand.step ev route demand a) (fun r h => CRV h r) := by
  unfold NeedDemand.step; ht_tac

attribute [ht_spec] demandStep_spec

/-- A suspension-level CALLABLE computation. -/
def SuspProjectSpec (project : NeedSuspension → EvalM (Option Algorithm)) : Prop :=
  ∀ susp, SoundI (fun h => SuspV h susp) (project susp) (fun _ _ => True)

theorem SuspProjectSpec.app {P : Array NeedCell → Prop} {project : NeedSuspension → EvalM (Option Algorithm)}
    (hp : SuspProjectSpec project) {susp : NeedSuspension} (hreq : ∀ h, P h → SuspV h susp) :
    SoundI P (project susp) (fun _ _ => True) :=
  SoundI.weaken (hp susp) hreq (fun _ _ g v => SuspV.mono g v) (fun _ _ h => h)

attribute [ht_spec] SuspProjectSpec.app

theorem projSuspended_spec {written : Expr → EvalCtx → EvalM (Option Algorithm)} (hw : WrittenSpec written) :
    SuspProjectSpec (NeedProjection.suspended written) := by
  intro susp
  cases susp <;> (unfold NeedProjection.suspended; ht_tac)

/-- **The CALLABLE write point.** `NeedProjection.step` writes only `callable`. -/
theorem projStep_spec {P : Array NeedCell → Prop} {project : NeedSuspension → EvalM (Option Algorithm)}
    {a : Nat} (hp : SuspProjectSpec project) :
    SoundI P (NeedProjection.step project a) (fun _ _ => True) := by
  unfold NeedProjection.step; ht_tac

attribute [ht_spec] projStep_spec
attribute [ht_lemmas] projSuspended_spec

/-! ## Opened items of a valid value are valid -/

section Items
variable {h : Array NeedCell}

theorem RV.toItems {r : Result} (v : RV h r) : RLV h r.toItems := by
  cases r with
  | sequenceValue xs => exact RV.seq_iff.1 v
  | _ => exact RLV.singleton v

theorem RV.spreadItems {r : Result} (v : RV h r) : RLV h r.spreadItems := by
  cases r with
  | listValue xs => exact RV.list_iff.1 v
  | _ => exact RV.toItems v

theorem RV.projectionItems {r : Result} (v : RV h r) : RLV h r.projectionItems := by
  cases r with
  | listValue xs => exact RV.list_iff.1 v
  | _ => exact RV.toItems v

theorem RV.sequencePatternItems {r : Result} {xs : List Result} (v : RV h r)
    (e : r.sequencePatternItems? = some xs) : RLV h xs := by
  cases r <;> simp [Result.sequencePatternItems?] at e
  subst e; exact RV.seq_iff.1 v

theorem RV.listPatternItems {r : Result} {xs : List Result} (v : RV h r)
    (e : r.listPatternItems? = some xs) : RLV h xs := by
  cases r <;> simp [Result.listPatternItems?] at e
  subst e; exact RV.list_iff.1 v

theorem RV.structureItems {r : Result} {xs : List Result} (v : RV h r)
    (e : r.structureItems? = some xs) : RLV h xs := by
  cases r <;> simp [Result.structureItems?] at e
  · subst e; exact RV.seq_iff.1 v
  · subst e; exact RV.list_iff.1 v

theorem RV.select {r x : Result} {i : Nat} (v : RV h r) (e : r.select? i = some x) : RV h x :=
  (RV.projectionItems v).getElem? e

end Items

attribute [ht_lemmas] RV.toItems RV.spreadItems RV.projectionItems RV.sequencePatternItems
  RV.listPatternItems RV.structureItems RV.select
attribute [ht_fwd] RV.sequencePatternItems RV.listPatternItems RV.structureItems RV.select

/-! ## Lazy collections (issue #204)

A deferred list item and a pending list's candidates carry need addresses (`Mentions`), so the
positional helpers read and allocate cells: each keeps `Inv` and returns valid values. -/

theorem CandV.nil {h : Array NeedCell} : CandV h [] := fun _ m => by cases m
theorem CandV.head {h : Array NeedCell} {c : Nat × Nat} {cs : List (Nat × Nat)} (v : CandV h (c :: cs)) :
    c.1 < h.size ∧ c.2 < h.size := v c List.mem_cons_self
theorem CandV.tail {h : Array NeedCell} {c : Nat × Nat} {cs : List (Nat × Nat)} (v : CandV h (c :: cs)) :
    CandV h cs := fun x m => v x (List.mem_cons_of_mem _ m)
theorem CandV.cons {h : Array NeedCell} {c : Nat × Nat} {cs : List (Nat × Nat)} (v1 : c.1 < h.size)
    (v2 : c.2 < h.size) (vs : CandV h cs) : CandV h (c :: cs) := by
  intro x m
  rcases List.mem_cons.mp m with rfl | m
  · exact ⟨v1, v2⟩
  · exact vs x m
theorem CandV.take {h : Array NeedCell} {cs : List (Nat × Nat)} (v : CandV h cs) (n : Nat) : CandV h (cs.take n) :=
  fun c m => v c (List.mem_of_mem_take m)
theorem CandV.diag {h : Array NeedCell} {cells : List Nat} (v : ValidAddresses h cells) :
    CandV h (cells.map (fun cell => (cell, cell))) := by
  intro c m
  obtain ⟨a, ma, rfl⟩ := List.mem_map.mp m
  exact ⟨v a ma, v a ma⟩
theorem CandV.verdicts {h : Array NeedCell} {cs : List (Nat × Nat)} (v : CandV h cs) :
    ValidAddresses h (cs.map Prod.snd) := by
  intro a m
  obtain ⟨c, mc, rfl⟩ := List.mem_map.mp m
  exact (v c mc).2
theorem mem_zipIdx_fst {α : Type} : ∀ (xs : List α) (n : Nat) (e : α × Nat), e ∈ xs.zipIdx n → e.1 ∈ xs
  | [], _, e, m => by simp at m
  | x :: rest, n, e, m => by
    rw [List.zipIdx_cons] at m
    rcases List.mem_cons.mp m with rfl | m
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (mem_zipIdx_fst rest _ e m)
theorem CandV.entry {h : Array NeedCell} {cs : List (Nat × Nat)} {entry : (Nat × Nat) × Nat}
    (m : entry ∈ cs.zipIdx) (v : CandV h cs) : entry.1.1 < h.size ∧ entry.1.2 < h.size :=
  v entry.1 (mem_zipIdx_fst cs 0 entry m)
theorem CandV.entry_position {h : Array NeedCell} {cs : List (Nat × Nat)} {entry : (Nat × Nat) × Nat}
    (m : entry ∈ cs.zipIdx) (v : CandV h cs) : entry.1.1 < h.size := (CandV.entry m v).1
theorem CandV.entry_verdict {h : Array NeedCell} {cs : List (Nat × Nat)} {entry : (Nat × Nat) × Nat}
    (m : entry ∈ cs.zipIdx) (v : CandV h cs) : entry.1.2 < h.size := (CandV.entry m v).2
theorem CandV.member_position {h : Array NeedCell} {cs : List (Nat × Nat)} {c : Nat × Nat}
    (m : c ∈ cs) (v : CandV h cs) : c.1 < h.size := (v c m).1
theorem CandV.member_verdict {h : Array NeedCell} {cs : List (Nat × Nat)} {c : Nat × Nat}
    (m : c ∈ cs) (v : CandV h cs) : c.2 < h.size := (v c m).2
theorem RLV.entry {h : Array NeedCell} {xs : List Result} {entry : Result × Nat}
    (m : entry ∈ xs.zipIdx) (v : RLV h xs) : RV h entry.1 := v entry.1 (mem_zipIdx_fst xs 0 entry m)
theorem RV.deferred_lt {h : Array NeedCell} {a : Nat} (v : RV h (.deferred a)) : a < h.size := RV.deferred_iff.1 v
theorem RV.pending_cand {h : Array NeedCell} {cs : List (Nat × Nat)} (v : RV h (.pendingList cs)) : CandV h cs :=
  RV.pendingList_iff.1 v
theorem RV.of_cand {h : Array NeedCell} {cs : List (Nat × Nat)} (v : CandV h cs) : RV h (.pendingList cs) :=
  RV.pendingList_iff.2 v

/-- The empty context binds no cell (the context of an internal pipeline step). -/
theorem ValidCtx.empty {h : Array NeedCell} : ValidCtx h EvalCtx.empty := fun _ m => by cases m

attribute [ht_lemmas] RV.deferred RV.of_cand RV.deferred_lt RV.pending_cand CandV.nil CandV.head CandV.tail CandV.cons
  CandV.take ValidCtx.empty VEV.nil CandV.diag CandV.verdicts CandV.entry_position CandV.entry_verdict
  CandV.member_position CandV.member_verdict RLV.entry
attribute [ht_fwd] RV.deferred_lt RV.pending_cand

set_option hygiene false in
macro_rules | `(tactic| ht_pmono) => `(tactic| (intro _ _ _ g v; exact CandV.mono g v))

/-- `mapM` producing candidates. -/
theorem SoundI.mapM_cand {α : Type} {P : Array NeedCell → Prop} {f : α → EvalM (Nat × Nat)} {xs : List α}
    (hf : ∀ x ∈ xs, SoundI P (f x) (fun c h => c.1 < h.size ∧ c.2 < h.size)) :
    SoundI P (xs.mapM f) (fun ys h => CandV h ys) :=
  SoundI.mapM (q := fun (c : Nat × Nat) h => c.1 < h.size ∧ c.2 < h.size)
    (fun _ _ _ g v => ⟨Nat.lt_of_lt_of_le v.1 g, Nat.lt_of_lt_of_le v.2 g⟩) xs hf

attribute [ht_spec] SoundI.mapM_cand

theorem forcePosition_spec {P : Array NeedCell → Prop} {demand : Nat → EvalM CountedResult} {value : Result}
    (hd : DemandSpec demand) (hreq : ∀ h, P h → RV h value) :
    SoundI P (forcePosition demand value) (fun r h => RV h r) := by
  unfold forcePosition; ht_tac

attribute [ht_spec] forcePosition_spec

theorem lazyDiscover_spec {demand : Nat → EvalM CountedResult} {visit : Nat → EvalM Result}
    (hd : DemandSpec demand)
    (hv : ∀ cell, SoundI (fun h => cell < h.size) (visit cell) (fun r h => RV h r)) :
    ∀ {candidates : List (Nat × Nat)} {P : Array NeedCell → Prop} {limit : Option Nat},
      (∀ h, P h → CandV h candidates) →
      SoundI P (LazyList.discover demand visit limit candidates) (fun rs h => RLV h rs) := by
  intro candidates
  induction candidates with
  | nil => intro P limit hreq; unfold LazyList.discover; ht_tac
  | cons c rest ih =>
    intro P limit hreq
    obtain ⟨cell, verdictCell⟩ := c
    unfold LazyList.discover
    split
    · exact SoundI.pure _ (fun _ _ => RLV.nil)
    · refine SoundI.bind (hd.app (fun h ph => (hreq h ph).head.2)) (fun _ _ _ g v => CRV.mono g v) ?_
      intro verdictValue
      refine SoundI.bind (Q := fun _ _ => True) ?_ PMono.true ?_
      · unfold LazyList.verdict; ht_tac
      · intro accepted
        split
        · refine SoundI.bind
            (SoundI.weaken (hv cell) (fun h ph => (hreq h ph.1.1).head.1) (hmono_lt cell) (fun _ _ v => v))
            (fun _ _ _ g v => RV.mono g v) ?_
          intro item
          refine SoundI.bind (ih (fun h ph => (hreq h ph.1.1.1).tail)) (fun _ _ _ g v => RLV.mono g v) ?_
          intro tail
          exact SoundI.pure _ (fun h ph => RLV.cons ph.1.2 ph.2)
        · exact ih (fun h ph => (hreq h ph.1.1).tail)

theorem lazyPositions_spec {P : Array NeedCell → Prop} {demand : Nat → EvalM CountedResult}
    {limit : Option Nat} {candidates : List (Nat × Nat)} (hd : DemandSpec demand)
    (hreq : ∀ h, P h → CandV h candidates) :
    SoundI P (LazyList.positions demand limit candidates) (fun rs h => RLV h rs) := by
  unfold LazyList.positions
  exact lazyDiscover_spec hd (fun cell => SoundI.pure _ (fun _ v => RV.deferred v)) hreq

theorem lazyValues_spec {P : Array NeedCell → Prop} {demand : Nat → EvalM CountedResult}
    {candidates : List (Nat × Nat)} (hd : DemandSpec demand) (hreq : ∀ h, P h → CandV h candidates) :
    SoundI P (LazyList.values demand candidates) (fun rs h => RLV h rs) := by
  unfold LazyList.values
  exact lazyDiscover_spec hd (fun cell => forcePosition_spec hd (fun _ v => RV.deferred v)) hreq

/-- `lazyDiscover_spec` in the procedure's contract shape (the visit is its callback). -/
theorem lazyDiscover_app {P : Array NeedCell → Prop} {demand : Nat → EvalM CountedResult}
    {visit : Nat → EvalM Result} {limit : Option Nat} {candidates : List (Nat × Nat)} (hd : DemandSpec demand)
    (hv : ∀ cell, SoundI (fun h => cell < h.size) (visit cell) (fun r h => RV h r))
    (hreq : ∀ h, P h → CandV h candidates) :
    SoundI P (LazyList.discover demand visit limit candidates) (fun rs h => RLV h rs) :=
  lazyDiscover_spec hd hv hreq

attribute [ht_spec] lazyPositions_spec lazyValues_spec lazyDiscover_app

/-- A counted value read back as a list, a sequence or a pending list: its parts are valid. -/
theorem CRV.list_of_eq {h : Array NeedCell} {p : CountedResult} {items : List Result} (v : CRV h p)
    (e : p.fst = .listValue items) : RLV h items := by
  have v' : RV h p.fst := v
  rw [e] at v'
  exact RV.list_iff.1 v'
theorem CRV.seq_of_eq {h : Array NeedCell} {p : CountedResult} {items : List Result} (v : CRV h p)
    (e : p.fst = .sequenceValue items) : RLV h items := by
  have v' : RV h p.fst := v
  rw [e] at v'
  exact RV.seq_iff.1 v'
theorem CRV.pending_of_eq {h : Array NeedCell} {p : CountedResult} {cs : List (Nat × Nat)} (v : CRV h p)
    (e : p.fst = .pendingList cs) : CandV h cs := by
  have v' : RV h p.fst := v
  rw [e] at v'
  exact RV.pending_cand v'
attribute [ht_lemmas] CRV.list_of_eq CRV.seq_of_eq CRV.pending_of_eq
attribute [ht_fwd] CRV.list_of_eq CRV.seq_of_eq CRV.pending_of_eq

theorem discoveredPositions_spec {P : Array NeedCell → Prop} {demand : Nat → EvalM CountedResult}
    {limit : Option Nat} {value : Result} (hd : DemandSpec demand) (hreq : ∀ h, P h → RV h value) :
    SoundI P (discoveredPositions demand limit value) (fun rs h => RLV h rs) := by
  unfold discoveredPositions; ht_tac

theorem forceLevel_spec {P : Array NeedCell → Prop} {demand : Nat → EvalM CountedResult} {value : Result}
    (hd : DemandSpec demand) (hreq : ∀ h, P h → RV h value) :
    SoundI P (forceLevel demand value) (fun r h => RV h r) := by
  unfold forceLevel; ht_tac

attribute [ht_spec] discoveredPositions_spec forceLevel_spec

theorem RLV.path {h : Array NeedCell} (visiting : List Nat) :
    RLV h (visiting.map (fun cell => Result.atom (Int.ofNat cell))) := by
  intro x m
  obtain ⟨n, _, rfl⟩ := List.mem_map.mp m
  exact RV.atom _
attribute [ht_lemmas] RLV.path

theorem materializeVia_spec {P : Array NeedCell → Prop} {demand : Nat → EvalM CountedResult} {value : Result}
    {visiting : List Nat} (hd : DemandSpec demand) (hreq : ∀ h, P h → RV h value) :
    SoundI P (materializeVia demand value visiting) (fun r h => RV h r) := by
  unfold materializeVia; ht_tac

attribute [ht_spec] materializeVia_spec

theorem materializePosition_spec {P : Array NeedCell → Prop} {demand : Nat → EvalM CountedResult}
    {value : Result} {visiting : List Nat} (hd : DemandSpec demand) (hreq : ∀ h, P h → RV h value) :
    SoundI P (materializePosition demand visiting value) (fun r h => RV h r) := by
  unfold materializePosition; ht_tac

attribute [ht_spec] materializePosition_spec

/-! ### The lazy stages: every cell a stage allocates is valid -/

theorem itemCell_spec {P : Array NeedCell → Prop} {item : Result} (hreq : ∀ h, P h → RV h item) :
    SoundI P (LazyList.itemCell item) (fun a h => a < h.size) := by
  unfold LazyList.itemCell; ht_tac

theorem earlierPositions_spec {P : Array NeedCell → Prop} {demand : Nat → EvalM CountedResult}
    {limit : Option Nat} {source : Result} {before : Int} (hd : DemandSpec demand)
    (hreq : ∀ h, P h → RV h source) :
    SoundI P (LazyList.earlierPositions demand limit source before) (fun rs h => RLV h rs) := by
  cases source <;> unfold LazyList.earlierPositions <;> ht_tac

theorem mappedCell_spec {P : Array NeedCell → Prop} {mapper : Nat × Option Expr} {caller : EvalCtx}
    {values : ValEnv} {item : Nat}
    (hreq : ∀ h, P h → item < h.size ∧ mapper.1 < h.size ∧ ValidCtx h caller ∧ VEV h values) :
    SoundI P (LazyList.mappedCell mapper caller values item) (fun a h => a < h.size) := by
  unfold LazyList.mappedCell
  exact allocate_spec (fun h ph =>
    ⟨ValidSourced.pair (hreq h ph).1 (ValidSourced.cons (hreq h ph).2.1 (fun _ m => by cases m)),
      (hreq h ph).2.2.1, (hreq h ph).2.2.2⟩)

attribute [ht_spec] itemCell_spec earlierPositions_spec mappedCell_spec

theorem mapItems_spec {P : Array NeedCell → Prop} {mapper : Nat × Option Expr} {caller : EvalCtx}
    {values : ValEnv} {items : List Result}
    (hreq : ∀ h, P h → RLV h items ∧ mapper.1 < h.size ∧ ValidCtx h caller ∧ VEV h values) :
    SoundI P (LazyList.mapItems mapper caller values items) (fun r h => RV h r) := by
  unfold LazyList.mapItems; ht_tac

theorem mapCandidates_spec {P : Array NeedCell → Prop} {mapper : Nat × Option Expr} {caller : EvalCtx}
    {values : ValEnv} {candidates : List (Nat × Nat)}
    (hreq : ∀ h, P h → CandV h candidates ∧ mapper.1 < h.size ∧ ValidCtx h caller ∧ VEV h values) :
    SoundI P (LazyList.mapCandidates mapper caller values candidates) (fun r h => RV h r) := by
  unfold LazyList.mapCandidates; ht_tac

theorem filterItems_spec {P : Array NeedCell → Prop} {predicate : Nat × Option Expr} {caller : EvalCtx}
    {values : ValEnv} {items : List Result}
    (hreq : ∀ h, P h → RLV h items ∧ predicate.1 < h.size ∧ ValidCtx h caller ∧ VEV h values) :
    SoundI P (LazyList.filterItems predicate caller values items) (fun r h => RV h r) := by
  unfold LazyList.filterItems; ht_tac
  intro h ⟨⟨⟨hp, source⟩, item⟩, marker⟩
  obtain ⟨_, pred, context, env⟩ := hreq h hp
  exact ⟨ValidSourced.cons pred (ValidSourced.pair item (ValidSourced.pair marker
    (ValidSourced.pair source (ValidSourced.pair marker ValidSourced.nil)))), context, env⟩

theorem filterCandidates_spec {P : Array NeedCell → Prop} {predicate : Nat × Option Expr} {caller : EvalCtx}
    {values : ValEnv} {candidates : List (Nat × Nat)}
    (hreq : ∀ h, P h → CandV h candidates ∧ predicate.1 < h.size ∧ ValidCtx h caller ∧ VEV h values) :
    SoundI P (LazyList.filterCandidates predicate caller values candidates) (fun r h => RV h r) := by
  unfold LazyList.filterCandidates; ht_tac
  intro h ⟨⟨hp, source⟩, offset⟩
  obtain ⟨candidatesValid, pred, context, env⟩ := hreq h hp
  exact ⟨ValidSourced.cons pred
    (ValidSourced.pair (CandV.entry_position (by assumption) candidatesValid)
      (ValidSourced.pair (CandV.entry_verdict (by assumption) candidatesValid)
        (ValidSourced.pair source (ValidSourced.pair offset ValidSourced.nil)))), context, env⟩

theorem takeCandidates_spec {P : Array NeedCell → Prop} {count : Int} {candidates : List (Nat × Nat)}
    (hreq : ∀ h, P h → CandV h candidates) :
    SoundI P (LazyList.takeCandidates count candidates) (fun r h => RV h r) := by
  unfold LazyList.takeCandidates; ht_tac

attribute [ht_spec] mapItems_spec mapCandidates_spec filterItems_spec filterCandidates_spec takeCandidates_spec

end KatLang.AddressInvariant
