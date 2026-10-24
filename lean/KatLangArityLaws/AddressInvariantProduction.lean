import KatLangArityLaws.AddressInvariantBodies

open KatLang KatLang.NeedControl.Allocation KatLang.HeapAddressValidity KatLang.AddressInvariant
open KatLang.EvaluatorCore

/-!
# FG-H1-FU-01 (M4): production corollaries — no callback premise remains

With `evalStep_sound : BodySound` (M3), `production_sound` makes every production evaluator
operation `evalUnbounded c` keep the call contract, UNCONDITIONALLY (every outcome; a
non-completing search returns its entry state). The FG-H1 statements that needed the false
callback premises `SpreadSound evalSupplySpread ctx env` and `ChannelsSound bindingChannels` are
replaced here by premise-free (`Inv` + structural input validity) theorems:

* **Spreads** (`production_evalSupplySpread`, `production_spread_cells`, `production_spread_items`).
* **Supply formation** (`production_formNeedSupplySourced`, `production_formNeedSupply`,
  `production_form_failure_retains_prefix`).
* **Plans**: every `.prepared (.ok cells)` is valid (the `Inv` clause `CellV.plan`, written only
  by `prepare`, `prepare_spec`); read paths `production_prepared_reread`, `production_viewCells`,
  `production_argumentViewCells`, `production_viewSupply`, `production_metaLoopCapture`,
  `production_executeAlong`, `production_invoke`.
* **Binder**: `production_bindNeedPatterns` at `bindingChannels`, its user-call / loop-step /
  META-builtin instances, and clause-family dispatch `production_selectNeedFamilyBranch` /
  `production_needActivateBranch`.
* **Entry** (`production_entry_program`, `production_entry_eval`): `evalProgramOutput wired` and
  `eval e` from `{callStack := [preludeAlg]}` and `[]`, for EVERY `wired` / `e` (in particular every
  output of the opaque `identifyPropertyExpr` / `validateExprTree` passes of `runResultM`), from
  every `Inv` state, in particular `EvalState.empty`. The `runResultM`-level bridge stays open.
-/

namespace KatLang.AddressInvariant

/-- Every production evaluator operation keeps the call contract, on every outcome. -/
theorem production_sound_all (c : EvalCall) : SoundOver Inv (CallPre c) (evalUnbounded c) (CallPost c) :=
  production_sound evalStep_sound c

/-- The production answer keeps the call contract (`RecSound` form). -/
theorem production_recSound_all : RecSound evalUnbounded := production_recSound evalStep_sound

/-- Completed fuel runs of the core keep the call contract (premised on completion only). -/
theorem evalFuel_sound_all (n : Nat) (c : EvalCall) (s : EvalState) (hc : Completes (evalFuel n c) s)
    (vs : Inv s) (ps : CallPre c s.needs) :
    Inv ((evalFuel n c).runState s).2 ∧ s.needs.size ≤ ((evalFuel n c).runState s).2.needs.size ∧
      ∀ x, ((evalFuel n c).runState s).1 = .ok x → CallPost c x ((evalFuel n c).runState s).2.needs :=
  evalFuel_sound evalStep_sound n c s hc vs ps

/-! ## Spreads -/

/-- **Production computed spread.** -/
theorem production_evalSupplySpread (e : Expr) (ctx : EvalCtx) (env : ValEnv) :
    SoundOver Inv (fun h => ValidCtx h ctx ∧ VEV h env) (evalSupplySpread e ctx env) (fun x h => SupplyV h x) :=
  production_sound_all (.evalSupplySpread e ctx env)

/-- A successful computed spread's transported cells are valid in the final heap. -/
theorem production_spread_cells (e : Expr) (ctx : EvalCtx) (env : ValEnv) (s : EvalState) (vs : Inv s)
    (vc : ValidCtx s.needs ctx) (ve : VEV s.needs env) {cells : List NeedSupply.Sourced} {t : EvalState}
    (hr : (evalSupplySpread e ctx env).runState s = (.ok (.cells cells), t)) :
    Inv t ∧ s.needs.size ≤ t.needs.size ∧ ValidSourced t.needs cells := by
  obtain ⟨v, g, r⟩ := production_evalSupplySpread e ctx env s vs ⟨vc, ve⟩
  rw [hr] at v g r
  exact ⟨v, g, r _ rfl⟩

/-- A successful computed spread's Ready items are valid in the final heap. -/
theorem production_spread_items (e : Expr) (ctx : EvalCtx) (env : ValEnv) (s : EvalState) (vs : Inv s)
    (vc : ValidCtx s.needs ctx) (ve : VEV s.needs env) {items : List Result} {t : EvalState}
    (hr : (evalSupplySpread e ctx env).runState s = (.ok (.items items), t)) :
    Inv t ∧ s.needs.size ≤ t.needs.size ∧ RLV t.needs items := by
  obtain ⟨v, g, r⟩ := production_evalSupplySpread e ctx env s vs ⟨vc, ve⟩
  rw [hr] at v g r
  exact ⟨v, g, r _ rfl⟩

/-- The production spread capability satisfies the spread contract. -/
theorem production_spreadSpec : SpreadSpec evalSupplySpread := spreadSpec_rec production_recSound_all

/-- **FG-H1's `SpreadSound` premise, discharged under `Inv`**: for every caller tier and value
    environment valid in the entry heap. (FG-H1's statement over `StateValid` is false — see
    `AddressInvariantGuards`.) -/
theorem production_spread_sound_inv (operand : Expr) (ctx : EvalCtx) (env : ValEnv) :
    SoundOver Inv (fun h => ValidCtx h ctx ∧ VEV h env) (evalSupplySpread (.sequenceSpread operand) ctx env)
      (fun x h => SpreadSupplyValid h x) := by
  intro s vs ps
  obtain ⟨v, g, r⟩ := production_evalSupplySpread (.sequenceSpread operand) ctx env s vs ps
  refine ⟨v, g, fun x hx => ?_⟩
  have := r x hx
  cases x with
  | items _ => trivial
  | cells _ => exact this

/-! ## Supply formation -/

/-- **Production sourced supply** (`formNeedSupplySourced`): from `Inv` and a valid caller tier
    and value environment, every outcome leaves an `Inv` state with a heap no smaller, and a
    successful supply is valid in it. -/
theorem production_formNeedSupplySourced (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) :
    SoundOver Inv (fun h => ValidCtx h ctx ∧ VEV h env) (formNeedSupplySourced args ctx env)
      (fun xs h => ValidSourced h xs) :=
  form_spec production_spreadSpec (fun _ h => h) (hmono_ctx_env ctx env)

/-- **Production address supply** (`formNeedSupply`). -/
theorem production_formNeedSupply (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) :
    SoundOver Inv (fun h => ValidCtx h ctx ∧ VEV h env) (formNeedSupply args ctx env)
      (fun xs h => ValidAddresses h xs) := by
  intro s vs ps
  have hs : SoundI (fun h => ValidCtx h ctx ∧ VEV h env) (formNeedSupply args ctx env)
      (fun xs h => ValidAddresses h xs) := by
    unfold formNeedSupply formNeedSupplySourced
    refine SoundI.bind (form_spec production_spreadSpec (fun _ h => h)) (fun _ _ _ g v => ValidSourced.mono g v) ?_
    intro xs
    exact SoundI.pure _ (fun _ h => h.2.addresses)
  exact hs (hmono_ctx_env ctx env) s vs ps

/-- **The retained heap after an ordinary failure** (production): a valid formed prefix stays
    valid in the retained heap, which satisfies `Inv` and did not shrink. -/
theorem production_form_failure_retains_prefix (ctx : EvalCtx) (env : ValEnv) (leading tail : OutputBundle)
    (s t u : EvalState) (xs : List NeedSupply.Sourced) (e : Error) (vs : Inv s)
    (vc : ValidCtx s.needs ctx) (ve : VEV s.needs env)
    (hl : (NeedSupply.form evalSupplySpread ctx env leading).runState s = (.ok xs, t))
    (ht : (NeedSupply.form evalSupplySpread ctx env tail).runState t = (.error e, u)) :
    (NeedSupply.form evalSupplySpread ctx env (leading ++ tail)).runState s = (.error e, u) ∧
      Inv u ∧ s.needs.size ≤ u.needs.size ∧ ValidSourced u.needs xs := by
  have whole := form_append_failure evalSupplySpread ctx env leading tail s t u xs e hl ht
  have hm := hmono_ctx_env ctx env
  obtain ⟨vt, gt, rt⟩ := (form_spec (args := leading) production_spreadSpec (fun _ h => h)) hm s vs ⟨vc, ve⟩
  rw [hl] at vt gt rt
  obtain ⟨vu, gu, _⟩ := (form_spec (args := tail) production_spreadSpec (fun _ h => h)) hm t vt
    ⟨ValidCtx.mono gt vc, VEV.mono gt ve⟩
  rw [ht] at vu gu
  exact ⟨whole, vu, Nat.le_trans gt gu, ValidSourced.mono gu (rt xs rfl)⟩

/-- FG-H1's production supply theorem, now WITHOUT the `SpreadSound` premise (over `Inv`). -/
theorem formNeedSupplySourced_inv (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) (s : EvalState)
    (vs : Inv s) (vc : ValidCtx s.needs ctx) (ve : VEV s.needs env)
    {o : Except Error (List NeedSupply.Sourced)} {t : EvalState}
    (hr : (formNeedSupplySourced args ctx env).runState s = (o, t)) :
    StateValid t ∧ Inv t ∧ (∀ a, a < s.needs.size → a < t.needs.size) ∧ ∀ xs, o = .ok xs → ValidSourced t.needs xs := by
  obtain ⟨v, g, r⟩ := production_formNeedSupplySourced args ctx env s vs ⟨vc, ve⟩
  rw [hr] at v g r
  exact ⟨v.toStateValid, v, fun a ha => Nat.lt_of_lt_of_le ha g, r⟩

/-! ## Invocation plans -/

theorem production_routeSpec : RouteSpec productionPlanRoute := routeSpec_rec production_recSound_all

/-- **Plan supplies are valid** (the `Inv` clause, written only by `NeedPlan.prepare`): a reread of
    a prepared supply in an `Inv` state holds valid addresses. -/
theorem production_prepared_reread {s : EvalState} (vs : Inv s) {a : Nat} {cell : NeedCell}
    {cells : List NeedSupply.Sourced} (hc : s.needs[a]? = some cell) (hp : cell.plan = .prepared (.ok cells)) :
    ValidSourced s.needs cells :=
  (vs.cells a cell hc).prepared hp rfl

/-- Plan preparation at production. -/
theorem production_prepare (a : Nat) (shape : NeedPlan.CallShape) :
    SoundOver Inv (fun h => ValidCtx h shape.caller ∧ VEV h shape.values)
      (NeedPlan.prepare evalSupplySpread a shape) (fun xs h => ValidSourced h xs) :=
  prepare_spec production_spreadSpec (fun _ h => h) (hmono_ctx_env _ _)

/-- An argument view's cells (`viewCells` at production; `argumentViewCells`). -/
theorem production_viewCells (a : Nat) :
    SoundOver Inv (fun _ => True) (NeedPlan.viewCells evalSupplySpread productionPlanRoute.classify a)
      (fun xs h => ValidSourced h xs) :=
  viewCells_spec production_spreadSpec production_routeSpec.classify (fun _ _ _ _ => trivial)

theorem production_argumentViewCells (a : Nat) :
    SoundOver Inv (fun _ => True) (argumentViewCells a) (fun xs h => ValidSourced h xs) :=
  production_sound_all (.argumentViewCells a)

theorem production_viewSupply (a : Nat) :
    SoundOver Inv (fun _ => True) (NeedPlan.viewSupply evalSupplySpread productionPlanRoute.classify a)
      (fun x h => SupplyV h x) :=
  viewSupply_spec production_spreadSpec production_routeSpec.classify (fun _ _ _ _ => trivial)

theorem production_executeAlong (a : Nat) (shape : NeedPlan.CallShape) (r : PlanRoute) :
    SoundOver Inv (fun h => ValidCtx h shape.caller ∧ VEV h shape.values)
      (NeedPlan.executeAlong productionPlanRoute a shape r) (fun x h => CRV h x) :=
  executeAlong_spec production_routeSpec (fun _ h => h) (hmono_ctx_env _ _)

theorem production_invoke (r : NeedPlan.CallReference) :
    SoundOver Inv (fun _ => True) (invokeNeedCall r) (fun x h => CRV h x) :=
  invoke_spec production_routeSpec (fun _ _ _ _ => trivial)

/-- The captured step's loop setup at production: the step cell and the ORIGINAL initial cells
    (the plan's one supply) are valid. -/
theorem metaLoopCapture_aux {P : Array NeedCell → Prop} (hP : HMono P)
    {classify : NeedPlan.CallShape → EvalM PlanRoute}
    {read : Nat → EvalM CountedResult} {view : Nat → EvalM (List NeedSupply.Sourced)} {adapter : Nat}
    (hc : ClassifySpec classify) (hd : DemandSpec read)
    (hv : ∀ a, SoundI (fun h => P h ∧ a < h.size) (view a) (fun xs h => ValidSourced h xs))
    (hreq : ∀ h, P h → adapter < h.size) :
    SoundI P (metaLoopCapture classify read view adapter)
      (fun r h => r.1 < h.size ∧ ValidAddresses h r.2) := by
  unfold metaLoopCapture; ht_tac

theorem production_metaLoopCapture (adapter : Nat) :
    SoundOver Inv (fun h => adapter < h.size)
      (metaLoopCapture productionPlanRoute.classify demandNeedRecursive argumentViewCells adapter)
      (fun r h => r.1 < h.size ∧ ValidAddresses h r.2) :=
  metaLoopCapture_aux (hmono_lt adapter) production_routeSpec.classify (demandSpec_rec production_recSound_all)
    (fun a => (production_recSound_all (.argumentViewCells a)).weaken (fun _ _ => trivial)
      (fun _ _ _ _ => trivial) (fun _ _ h => h)) (fun _ h => h) (hmono_lt adapter)

/-! ## The binder and clause-family dispatch -/

theorem production_channelsSpec : ChannelsSpec bindingChannels := channelsSpec_rec production_recSound_all

/-- **FG-H1's `ChannelsSound` premise, discharged under `Inv`**: the production VALUE channel returns
    a valid counted result and both channels keep `Inv`. -/
theorem production_channels_value (a : Nat) :
    SoundOver Inv (fun _ => True) (bindingChannels.value a) (fun r h => CRV h r) :=
  (demandStep_spec (evSpec_suppliedAt production_recSound_all a) production_routeSpec
    (demandSpec_rec production_recSound_all)) (fun _ _ _ _ => trivial)

theorem production_channels_callable (a : Nat) :
    SoundOver Inv (fun _ => True) (bindingChannels.callable a) (fun _ _ => True) :=
  (projStep_spec (projSuspended_spec (writtenSpec_rec production_recSound_all a))) (fun _ _ _ _ => trivial)

/-- FG-H1's `ChannelsSound bindingChannels`, discharged over `Inv` (FG-H1's own statement over
    `StateValid` is false). -/
theorem production_channelsSound_inv : ChannelsSpec bindingChannels := production_channelsSpec

/-- **Production binder** (`bindNeedPatterns` at `bindingChannels`): from valid supplied cells, a
    valid callee need environment; `Inv` kept on success, non-match and every error. -/
theorem production_bindNeedPatterns (patterns : List NeedPattern) (cells : List Nat) (family : Bool) :
    SoundOver Inv (fun h => ValidAddresses h cells) (bindNeedPatterns bindingChannels patterns cells family)
      (fun r h => OptEnvValid r h) :=
  bindNeedPatterns_spec production_channelsSpec (fun _ h => h) (fun _ _ g v => ValidAddresses.mono g v)

/-- The user-call instantiation (`evalNeedUserSupplyOutput`, the explicit zero-supply invocation). -/
theorem production_user_binder (callee : Algorithm) (cells : List Nat) :
    SoundOver Inv (fun h => ValidAddresses h cells)
      (bindNeedPatterns bindingChannels ((Algorithm.parameterPatterns callee).map NeedPattern.ofParameter) cells)
      (fun r h => OptEnvValid r h) :=
  production_bindNeedPatterns _ cells false

/-- The loop-step instantiation (`runNeedStepWith` over the state cells). -/
theorem production_loop_step_binder (step : Algorithm) (cells : List Nat) :
    SoundOver Inv (fun h => ValidAddresses h cells)
      (bindNeedPatterns bindingChannels ((Algorithm.parameterPatterns step).map NeedPattern.ofParameter) cells)
      (fun r h => OptEnvValid r h) :=
  production_bindNeedPatterns _ cells false

/-- The META-builtin instantiation (`applyBuiltinCounted`'s `while`/`repeat` binding). -/
theorem production_meta_builtin_binder (b : Builtin) (cells : List Nat) :
    SoundOver Inv (fun h => ValidAddresses h cells)
      (bindNeedPatterns bindingChannels ((builtinSignature b).map NeedPattern.ofParameter) cells)
      (fun r h => OptEnvValid r h) :=
  production_bindNeedPatterns _ cells false

/-- **Production clause-family dispatch** (`selectNeedFamilyBranch` at `bindingChannels`). -/
theorem production_selectNeedFamilyBranch (callee : Algorithm) (cells : List Nat) (ctx : EvalCtx)
    (env : ValEnv) (calleeName : String) :
    SoundOver Inv (fun h => ValidAddresses h cells ∧ ValidCtx h ctx ∧ VEV h env)
      (selectNeedFamilyBranch bindingChannels callee cells ctx env calleeName)
      (fun r h => ValidCtx h r.2.1 ∧ VEV h r.2.2) :=
  selectNeedFamilyBranch_spec production_channelsSpec (fun _ h => h)
    (fun _ _ g v => ⟨ValidAddresses.mono g v.1, ValidCtx.mono g v.2.1, VEV.mono g v.2.2⟩)

/-- The selected clause's activation (`needActivateBranch`). -/
theorem production_needActivateBranch (callee : Algorithm) (ctx : EvalCtx) (env : ValEnv) (branch : CondBranch)
    (bindings : NeedEnv) :
    SoundOver Inv (fun h => ValidCtx h ctx ∧ VEV h env ∧ ValidNeedEnv h bindings)
      (needActivateBranch callee ctx env branch bindings) (fun r h => ValidCtx h r.2.1 ∧ VEV h r.2.2) :=
  needActivateBranch_spec (fun _ h => h)
    (fun _ _ g v => ⟨ValidCtx.mono g v.1, VEV.mono g v.2.1, ValidNeedEnv.mono g v.2.2⟩)

/-- FG-H1's production binder theorem, now WITHOUT the `ChannelsSound` premise (over `Inv`). -/
theorem bindNeedPatterns_inv (patterns : List NeedPattern) (cells : List Nat) (family : Bool) (s : EvalState)
    (vs : Inv s) (vc : ValidAddresses s.needs cells) :
    StateValid ((bindNeedPatterns bindingChannels patterns cells family).runState s).2 ∧
      Inv ((bindNeedPatterns bindingChannels patterns cells family).runState s).2 ∧
      s.needs.size ≤ ((bindNeedPatterns bindingChannels patterns cells family).runState s).2.needs.size ∧
      ∀ r, ((bindNeedPatterns bindingChannels patterns cells family).runState s).1 = .ok r →
        OptEnvValid r ((bindNeedPatterns bindingChannels patterns cells family).runState s).2.needs := by
  obtain ⟨v, g, r⟩ := production_bindNeedPatterns patterns cells family s vs vc
  exact ⟨v.toStateValid, v, g, r⟩

/-! ## The entry corollary (operation level) -/

theorem entry_ctx_valid (h : Array NeedCell) : ValidCtx h { callStack := [preludeAlg] } := fun _ m => by cases m

/-- **Entry (program root).** For EVERY root algorithm `wired` — in particular every output of the
    opaque preprocessing passes of `runResultM` — `evalProgramOutput wired {callStack :=
    [preludeAlg]} []` keeps `Inv` from every `Inv` state and returns a valid result. -/
theorem production_entry_program (wired : Algorithm) :
    SoundOver Inv (fun _ => True) (evalProgramOutput wired { callStack := [preludeAlg] } [])
      (fun r h => RV h r) :=
  fun s vs _ => production_sound_all (.evalProgramOutput wired { callStack := [preludeAlg] } []) s vs
    ⟨entry_ctx_valid _, VEV.nil⟩

/-- **Entry (expression).** -/
theorem production_entry_eval (e : Expr) :
    SoundOver Inv (fun _ => True) (eval e { callStack := [preludeAlg] } []) (fun r h => RV h r) :=
  fun s vs _ => production_sound_all (.eval e { callStack := [preludeAlg] } []) s vs
    ⟨entry_ctx_valid _, VEV.nil⟩

/-- Both entries from the empty state. -/
theorem production_entry_from_empty (wired : Algorithm) (e : Expr) :
    (Inv ((evalProgramOutput wired { callStack := [preludeAlg] } []).runState EvalState.empty).2 ∧
      ∀ r, ((evalProgramOutput wired { callStack := [preludeAlg] } []).runState EvalState.empty).1 = .ok r →
        RV ((evalProgramOutput wired { callStack := [preludeAlg] } []).runState EvalState.empty).2.needs r) ∧
    (Inv ((eval e { callStack := [preludeAlg] } []).runState EvalState.empty).2 ∧
      ∀ r, ((eval e { callStack := [preludeAlg] } []).runState EvalState.empty).1 = .ok r →
        RV ((eval e { callStack := [preludeAlg] } []).runState EvalState.empty).2.needs r) := by
  obtain ⟨v1, _, r1⟩ := production_entry_program wired EvalState.empty empty_inv trivial
  obtain ⟨v2, _, r2⟩ := production_entry_eval e EvalState.empty empty_inv trivial
  exact ⟨⟨v1, r1⟩, ⟨v2, r2⟩⟩

end KatLang.AddressInvariant
