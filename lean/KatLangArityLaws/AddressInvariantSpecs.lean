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
  refine SoundI.of_readonly (fun s vs _ => ?_)
  obtain ⟨r, hr, hfound⟩ := slice_run operand caller s
  rw [hr]
  refine ⟨rfl, fun x hx slice hslice => ?_⟩
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

end KatLang.AddressInvariant
