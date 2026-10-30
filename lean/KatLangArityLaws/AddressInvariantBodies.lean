import KatLangArityLaws.AddressInvariantHelpers

open KatLang KatLang.NeedControl.Allocation KatLang.HeapAddressValidity KatLang.AddressInvariant
open KatLang.CallPlan (bind_run get_run pure_run modify_run throw_run lift_run evalAttempt_run)

/-!
# FG-H1-FU-01 (M3): the per-body obligation

For EVERY evaluator body `EvalBody.X` (one per `EvalCall` constructor, 102 in all), from an answer
`rec` that keeps the call contract (`RecSound rec`), the body keeps the contract of its own call:
`SoundI (CallPre c) (EvalBody.X rec …) (CallPost c)` (`EvalBody.X_sound`), hence
`evalStep_sound : BodySound`. The proofs are the syntax-directed procedure `ht_tac`
(`AddressInvariantTactic`) over the bodies as defined in `lean/KatLang.lean`, with the callback
contracts of the recursive answer discharged here once (`spreadSpec_rec`, `routeSpec_rec`,
`channelsSpec_rec`, …) and the bodies with state-reading/writing control proved with the same
combinators by hand where noted.

The opaque `partial` helpers the bodies reach (`peelSequenceSpreadLayers`,
`sequenceConstructLeavesLoop`, `requiredParameterOwner?` through `capturedParameterActivation?`,
`activeDeclaration?`, `scopeChainContains`, `reprStr` keys) return address-free data; every
proof here holds for ARBITRARY values of them (no equation about them is used).
-/

namespace KatLang.AddressInvariant

set_option hygiene false in
macro_rules | `(tactic| mono_atom $g) => `(tactic| exact callPre_mono _ _ _ $g ‹_›)
set_option hygiene false in
macro_rules | `(tactic| mono_atom $g) => `(tactic| exact callPost_mono _ _ _ _ $g ‹_›)
set_option hygiene false in
macro_rules | `(tactic| mono_atom $g) => `(tactic| exact ExcV.mono (callPost_mono _) _ _ _ $g ‹_›)

theorem ItemLV.head' {h : Array NeedCell} {x : CallableCallItem} {xs : List CallableCallItem}
    (v : ItemLV h (x :: xs)) : ItemV h x := v x List.mem_cons_self
theorem ItemLV.tail' {h : Array NeedCell} {x : CallableCallItem} {xs : List CallableCallItem}
    (v : ItemLV h (x :: xs)) : ItemLV h xs := fun y m => v y (List.mem_cons_of_mem _ m)
theorem ItemLV.cons' {h : Array NeedCell} {x : CallableCallItem} {xs : List CallableCallItem}
    (v : ItemV h x) (vs : ItemLV h xs) : ItemLV h (x :: xs) := by
  intro y m
  rcases List.mem_cons.mp m with rfl | m
  · exact v
  · exact vs y m
theorem ItemLV.nil' {h : Array NeedCell} : ItemLV h [] := fun _ m => by cases m
attribute [ht_lemmas] ItemLV.head' ItemLV.tail' ItemLV.cons' ItemLV.nil'
attribute [ht_fwd] ItemLV.head' ItemLV.tail'

theorem SuffixV.of_need {h : Array NeedCell} {a : Nat} (v : a < h.size) : SuffixV h (.needAlgorithm a) := v
theorem SuffixV.of_value {h : Array NeedCell} {r : Result} (v : RV h r) : SuffixV h (.value r) := v
theorem SuffixV.of_algorithm {h : Array NeedCell} {a : Algorithm} : SuffixV h (.algorithm a) := trivial
theorem SuffixV.of_whole {h : Array NeedCell} {n : Int} : SuffixV h (.wholeNumber n) := trivial
attribute [ht_lemmas] SuffixV.of_need SuffixV.of_value SuffixV.of_algorithm SuffixV.of_whole CRV.rv

theorem ItemV.with_value {h : Array NeedCell} {item : CallableCallItem} {r : Result} (v : ItemV h item)
    (hv : RV h r) : ItemV h { item with value? := some r } :=
  ⟨v.1, fun x e => by cases e; exact hv⟩
theorem ItemV.with_error {h : Array NeedCell} {item : CallableCallItem} {e : Error} (v : ItemV h item) :
    ItemV h { item with error? := some e } := ⟨v.1, v.2⟩
theorem ItemV.with_error_callable {h : Array NeedCell} {item : CallableCallItem} {e : Error}
    {c : Option Algorithm} (v : ItemV h item) : ItemV h { item with error? := some e, callable? := c } :=
  ⟨v.1, v.2⟩
theorem collectItems_valid {h : Array NeedCell} {args : List ResolvedArgumentAlgorithm} (v : RALV h args) :
    ItemLV h (collectSequenceCallableCallItems args) := by
  intro y m
  unfold collectSequenceCallableCallItems at m
  obtain ⟨x, mx, rfl⟩ := List.mem_map.mp m
  exact ⟨v x mx, fun _ e => by cases e⟩
theorem ItemLV.of_eq {h : Array NeedCell} {xs ys : List CallableCallItem} (v : ItemLV h xs) (e : xs = ys) :
    ItemLV h ys := e ▸ v
theorem BoundV.mk' {h : Array NeedCell} {p : PreparedSequenceBuiltinInput} {it : List CountedResult}
    {sa : List PreparedSequenceBuiltinSuffixArg} {view : Option Nat} (v1 : RLV h p.items) (v2 : CRLV h it)
    (v3 : SuffixLV h sa) (v4 : OptAddr h view) :
    BoundV h { preparedInput := p, iterationItems := it, suffixArgs := sa, view? := view } := ⟨v1, v2, v3, v4⟩
attribute [ht_lemmas] BoundV.mk'
attribute [ht_lemmas] ItemV.with_value ItemV.with_error ItemV.with_error_callable collectItems_valid ItemLV.of_eq
attribute [ht_fwd] collectItems_valid ItemLV.of_eq

/-! ## The callback contracts of a sound answer -/

section Rec
variable {rec : EvalRec}

theorem spreadSpec_rec (hrec : RecSound rec) : SpreadSpec rec.evalSupplySpread :=
  fun e ctx env => hrec (.evalSupplySpread e ctx env)
theorem demandSpec_rec (hrec : RecSound rec) : DemandSpec rec.demandNeedRecursive :=
  fun a => (hrec (.demandNeedRecursive a)).weaken (fun _ _ => trivial) (callPre_mono _) (fun _ _ h => h)
theorem projectSpec_rec (hrec : RecSound rec) : ProjectSpec rec.projectNeedCallable :=
  fun a => (hrec (.projectNeedCallable a)).weaken (fun _ _ => trivial) (callPre_mono _) (fun _ _ h => h)
theorem ctxSpec_dotReceiver (hrec : RecSound rec) : CtxSpec rec.resolveDotReceiver? :=
  fun e ctx => hrec (.resolveDotReceiver? e ctx)
theorem ctxSpec_intrinsicRoute (hrec : RecSound rec) : CtxSpec rec.algorithmIntrinsicRoute :=
  fun e ctx => hrec (.algorithmIntrinsicRoute e ctx)
theorem ctxSpec_resolveCalleeAlg (hrec : RecSound rec) : CtxSpec rec.resolveCalleeAlg :=
  fun e ctx => hrec (.resolveCalleeAlg e ctx)
theorem ctxSpec_normalize (hrec : RecSound rec) : CtxSpec rec.needPlanNormalizeCallee :=
  fun e ctx => hrec (.needPlanNormalizeCallee e ctx)
theorem evSpec_suppliedAt (hrec : RecSound rec) (a : Nat) : EvSpec (rec.evalSuppliedAt a) :=
  fun e ctx env => hrec (.evalSuppliedAt a e ctx env)
theorem writtenSpec_rec (hrec : RecSound rec) (a : Nat) : WrittenSpec (rec.projectNeedWrittenAt a) :=
  fun e ctx => hrec (.projectNeedWrittenAt a e ctx)

theorem classifySpec_with {resolve : Expr → EvalCtx → EvalM (Option Algorithm)}
    {route : Expr → EvalCtx → EvalM Bool} (hres : CtxSpec resolve) (hroute : CtxSpec route) :
    ClassifySpec (classifyPlanRouteWith resolve route) := by
  intro shape
  unfold classifyPlanRouteWith; ht_tac

theorem routeSpec_rec (hrec : RecSound rec) : RouteSpec rec.planRoute :=
  ⟨fun e ctx => hrec (.resolveCalleeAlg e ctx), fun a ctx => hrec (.needPlanNormalizeCallee a ctx),
   fun origin callee cells ctx env name => hrec (.evalSuppliedCallCounted origin callee cells ctx env name),
   spreadSpec_rec hrec, classifySpec_with (ctxSpec_dotReceiver hrec) (ctxSpec_intrinsicRoute hrec),
   projectSpec_rec hrec⟩

theorem classifySpec_rec (hrec : RecSound rec) : ClassifySpec rec.planRoute.classify :=
  (routeSpec_rec hrec).classify

theorem channelsSpec_rec (hrec : RecSound rec) : ChannelsSpec rec.bindingChannels :=
  shell_spec (evSpec_suppliedAt hrec) (routeSpec_rec hrec) (demandSpec_rec hrec) (writtenSpec_rec hrec)

end Rec

attribute [ht_lemmas] spreadSpec_rec demandSpec_rec projectSpec_rec ctxSpec_dotReceiver
  ctxSpec_intrinsicRoute ctxSpec_resolveCalleeAlg ctxSpec_normalize evSpec_suppliedAt writtenSpec_rec
  routeSpec_rec classifySpec_rec channelsSpec_rec

/-! ## Reading the auxiliary validity predicates -/

section Aux
variable {h : Array NeedCell}
theorem PreparedV.counted' {p : PreparedAlgorithmOutput} (v : PreparedV h p) : CRV h p.counted := v.1
theorem PreparedV.slots {p : PreparedAlgorithmOutput} (v : PreparedV h p) : RLV h p.outputSlots := v.2
theorem PreparedV.mk' {c : CountedResult} {xs : List Result} (v1 : CRV h c) (v2 : RLV h xs) :
    PreparedV h { counted := c, outputSlots := xs } := ⟨v1, v2⟩
theorem RAV.need {arg : ResolvedArgumentAlgorithm} {a : Nat} (v : RAV h arg) (e : arg.need? = some a) :
    a < h.size := v a e
theorem RAV.mk {arg : ResolvedArgumentAlgorithm} (v : OptAddr h arg.need?) : RAV h arg := v
theorem ItemV.need {x : CallableCallItem} {a : Nat} (v : ItemV h x) (e : x.need? = some a) : a < h.size := v.1 a e
theorem ItemV.value {x : CallableCallItem} {r : Result} (v : ItemV h x) (e : x.value? = some r) : RV h r := v.2 r e
theorem ItemV.mk' {x : CallableCallItem} (v1 : OptAddr h x.need?) (v2 : ∀ r, x.value? = some r → RV h r) :
    ItemV h x := ⟨v1, v2⟩
theorem BoundV.items {b : BoundSequenceBuiltinArguments} (v : BoundV h b) : RLV h b.preparedInput.items := v.1
theorem BoundV.iteration {b : BoundSequenceBuiltinArguments} (v : BoundV h b) : CRLV h b.iterationItems := v.2.1
theorem BoundV.suffix {b : BoundSequenceBuiltinArguments} (v : BoundV h b) : SuffixLV h b.suffixArgs := v.2.2.1
theorem BoundV.view {b : BoundSequenceBuiltinArguments} {a : Nat} (v : BoundV h b) (e : b.view? = some a) :
    a < h.size := v.2.2.2 a e
theorem SuffixLV.nil' : SuffixLV h [] := fun _ m => by cases m
theorem SuffixLV.cons' {x : PreparedSequenceBuiltinSuffixArg} {xs : List PreparedSequenceBuiltinSuffixArg}
    (v : SuffixV h x) (vs : SuffixLV h xs) : SuffixLV h (x :: xs) := by
  intro y m
  rcases List.mem_cons.mp m with rfl | m
  · exact v
  · exact vs y m
theorem SuffixLV.getElem? {xs : List PreparedSequenceBuiltinSuffixArg} {i : Nat}
    {x : PreparedSequenceBuiltinSuffixArg} (v : SuffixLV h xs) (e : xs[i]? = some x) : SuffixV h x :=
  v x (List.mem_of_getElem? e)
theorem SuffixV.need {a : Nat} (v : SuffixV h (.needAlgorithm a)) : a < h.size := v
theorem SuffixV.value {r : Result} (v : SuffixV h (.value r)) : RV h r := v
theorem OptRLV.some' {xs : List Result} (v : OptRLV h (some xs)) : RLV h xs := v xs rfl
theorem OptRLV.nothing : OptRLV h none := fun _ e => by cases e
theorem OptRLV.of_rlv {xs : List Result} (v : RLV h xs) : OptRLV h (some xs) := fun _ e => by cases e; exact v
theorem OriginV.cell' {a : Nat} (v : a < h.size) : OriginV h (.cell a) := v
theorem OriginV.written' {e : Expr} {c : EvalCtx} (v : ValidCtx h c) : OriginV h (.written e c) := v
theorem OriginV.none' : OriginV h .none := trivial
theorem OriginV.bound' {o : Algorithm} {p : PropDef} : OriginV h (.bound o p) := trivial
theorem CRLV.map_ready {xs : List Result} (v : RLV h xs) :
    CRLV h (xs.map fun value => (value, Result.valueCount value)) := by
  intro p m
  obtain ⟨x, mx, rfl⟩ := List.mem_map.mp m
  exact v x mx
end Aux

attribute [ht_lemmas] PreparedV.counted' PreparedV.slots PreparedV.mk' RAV.need RAV.mk ItemV.need
  ItemV.value ItemV.mk' BoundV.items BoundV.iteration BoundV.suffix BoundV.view SuffixLV.nil'
  SuffixLV.cons' SuffixLV.getElem? SuffixV.need SuffixV.value OptRLV.some' OptRLV.nothing OptRLV.of_rlv
  OriginV.cell' OriginV.written' OriginV.none' OriginV.bound' CRLV.map_ready
attribute [ht_fwd] PreparedV.counted' PreparedV.slots RAV.need ItemV.need ItemV.value BoundV.items
  BoundV.iteration BoundV.suffix BoundV.view SuffixLV.getElem? OptRLV.some'

theorem RALV.map_need {h : Array NeedCell} {α : Type} {xs : List α} {f : α → ResolvedArgumentAlgorithm}
    (v : ∀ x ∈ xs, OptAddr h (f x).need?) : RALV h (xs.map f) := by
  intro y m
  obtain ⟨x, mx, rfl⟩ := List.mem_map.mp m
  exact v x mx

theorem GotV.susp_map {st : EvalState} {h : Array NeedCell} (v : GotV st h) {i : Nat} {src : Expr}
    {caller : EvalCtx} {vals : ValEnv}
    (e : Option.map NeedCell.suspension st.needs[i]? = some (.expression src caller vals)) :
    ValidCtx h caller := by
  cases hc : st.needs[i]? with
  | none => rw [hc] at e; cases e
  | some c =>
    rw [hc] at e
    simp only [Option.map_some, Option.some.injEq] at e
    exact (v.cell hc).expr_ctx e

attribute [ht_lemmas] RALV.map_need GotV.susp_map
attribute [ht_fwd] GotV.susp_map

/-! ## The bodies' local loops (generalized over the precondition) -/

section Loops
variable {rec : EvalRec} (hrec : RecSound rec)
include hrec

theorem outputRowsCollect_spec (rowCtx : EvalCtx) (env : ValEnv) : ∀ (rows : List Expr) {P : Array NeedCell → Prop}
    (hP : HMono P) (acc : List Result) (emitted : Nat)
    (hreq : ∀ h, P h → ValidCtx h rowCtx ∧ VEV h env ∧ RLV h acc),
    SoundI P (EvalBody.evalOutputRowsPreparedCore.collect rec rowCtx env rows acc emitted)
      (fun p h => PreparedV h p) := by
  intro rows
  induction rows with
  | nil => intro P hP acc emitted hreq; unfold EvalBody.evalOutputRowsPreparedCore.collect; ht_tac
  | cons e rest ih => intro P hP acc emitted hreq; unfold EvalBody.evalOutputRowsPreparedCore.collect; ht_tac

theorem explicitRowsCollect_spec (rowCtx : EvalCtx) (env : ValEnv) : ∀ (rows : List Expr) {P : Array NeedCell → Prop}
    (hP : HMono P) (acc : List Result) (hreq : ∀ h, P h → ValidCtx h rowCtx ∧ VEV h env ∧ RLV h acc),
    SoundI P (EvalBody.evalExplicitSequenceValueRowSlots.collect rec rowCtx env rows acc)
      (fun xs h => RLV h xs) := by
  intro rows
  induction rows with
  | nil => intro P hP acc hreq; unfold EvalBody.evalExplicitSequenceValueRowSlots.collect; ht_tac
  | cons e rest ih => intro P hP acc hreq; unfold EvalBody.evalExplicitSequenceValueRowSlots.collect; ht_tac

theorem listLiteralCollect_spec (ctx : EvalCtx) (env : ValEnv) : ∀ (elements : List Expr) {P : Array NeedCell → Prop}
    (hP : HMono P) (acc : List Result) (hreq : ∀ h, P h → ValidCtx h ctx ∧ VEV h env ∧ RLV h acc),
    SoundI P (EvalBody.evalListLiteralCounted.collect rec ctx env elements acc) (fun xs h => RLV h xs) := by
  intro elements
  induction elements with
  | nil => intro P hP acc hreq; unfold EvalBody.evalListLiteralCounted.collect; ht_tac
  | cons e rest ih => intro P hP acc hreq; unfold EvalBody.evalListLiteralCounted.collect; ht_tac

theorem sequenceConstructLoop_spec (ctx : EvalCtx) (env : ValEnv) : ∀ (leaves : List Expr) {P : Array NeedCell → Prop}
    (hP : HMono P) (items : List Result) (hreq : ∀ h, P h → ValidCtx h ctx ∧ VEV h env ∧ RLV h items),
    SoundI P (EvalBody.evalSequenceConstructCounted.loop rec ctx env leaves items) (fun r h => CRV h r) := by
  intro leaves
  induction leaves with
  | nil => intro P hP items hreq; unfold EvalBody.evalSequenceConstructCounted.loop; ht_tac
  | cons e rest ih => intro P hP items hreq; unfold EvalBody.evalSequenceConstructCounted.loop; ht_tac

theorem prepareControls_spec (b : Builtin) (ctx : EvalCtx) (env : ValEnv) :
    ∀ (descriptors : List SequenceBuiltinSuffixArgDescriptor) {P : Array NeedCell → Prop} (hP : HMono P)
      (items : List CallableCallItem) (hreq : ∀ h, P h → ValidCtx h ctx ∧ VEV h env ∧ ItemLV h items),
    SoundI P (EvalBody.bindSequenceBuiltinArguments.prepareControls rec b ctx env descriptors items)
      (fun xs h => SuffixLV h xs) := by
  intro descriptors
  induction descriptors with
  | nil =>
    intro P hP items hreq
    cases items <;> (unfold EvalBody.bindSequenceBuiltinArguments.prepareControls; ht_tac)
  | cons d rest ih =>
    intro P hP items hreq
    cases items <;> (unfold EvalBody.bindSequenceBuiltinArguments.prepareControls; ht_tac)

theorem reduceLoop_spec (stepAlg : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    ∀ (items : List CountedResult) {P : Array NeedCell → Prop} (hP : HMono P) (acc : CountedResult)
      (hreq : ∀ h, P h → ValidCtx h ctx ∧ VEV h env ∧ CRLV h items ∧ CRV h acc),
    SoundI P (EvalBody.evalReduceCounted.reduceLoop rec stepAlg ctx env items acc) (fun r h => CRV h r) := by
  intro items
  induction items with
  | nil => intro P hP acc hreq; unfold EvalBody.evalReduceCounted.reduceLoop; ht_tac
  | cons i rest ih => intro P hP acc hreq; unfold EvalBody.evalReduceCounted.reduceLoop; ht_tac

theorem filterLoop_spec (predicateAlg : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    ∀ (items : List CountedResult) {P : Array NeedCell → Prop} (hP : HMono P) (index : Nat)
      (hreq : ∀ h, P h → ValidCtx h ctx ∧ VEV h env ∧ CRLV h items),
    SoundI P (EvalBody.evalFilterCounted.filterLoop rec predicateAlg ctx env index items) (fun xs h => RLV h xs) := by
  intro items
  induction items with
  | nil => intro P hP index hreq; unfold EvalBody.evalFilterCounted.filterLoop; ht_tac
  | cons i rest ih => intro P hP index hreq; unfold EvalBody.evalFilterCounted.filterLoop; ht_tac

theorem mapLoop_spec (transformAlg : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    ∀ (items : List CountedResult) {P : Array NeedCell → Prop} (hP : HMono P)
      (hreq : ∀ h, P h → ValidCtx h ctx ∧ VEV h env ∧ CRLV h items),
    SoundI P (EvalBody.evalMapCounted.mapLoop rec transformAlg ctx env items) (fun xs h => RLV h xs) := by
  intro items
  induction items with
  | nil => intro P hP hreq; unfold EvalBody.evalMapCounted.mapLoop; ht_tac
  | cons i rest ih => intro P hP hreq; unfold EvalBody.evalMapCounted.mapLoop; ht_tac

theorem repeatLoop_spec (ctx : EvalCtx) (env : ValEnv) (step : ResolvedArgumentAlgorithm) (stepName : String) :
    ∀ (remaining : Nat) {P : Array NeedCell → Prop} (hP : HMono P) (cells : List Nat)
      (hreq : ∀ h, P h → ValidCtx h ctx ∧ VEV h env ∧ RAV h step ∧ ValidAddresses h cells),
    SoundI P (EvalBody.applyBuiltinCounted.repeatLoop rec ctx env step stepName remaining cells)
      (fun xs h => ValidAddresses h xs) := by
  intro remaining
  induction remaining with
  | zero => intro P hP cells hreq; unfold EvalBody.applyBuiltinCounted.repeatLoop; ht_tac
  | succ k ih => intro P hP cells hreq; unfold EvalBody.applyBuiltinCounted.repeatLoop; ht_tac

end Loops

/-- The loop contracts at a call site (the procedure supplies `HMono` and the requirement). -/
theorem outputRowsCollect_app {rec : EvalRec} (hrec : RecSound rec) {rowCtx : EvalCtx} {env : ValEnv}
    {rows : List Expr} {P : Array NeedCell → Prop} {acc : List Result} {emitted : Nat}
    (hreq : ∀ h, P h → ValidCtx h rowCtx ∧ VEV h env ∧ RLV h acc) :
    SoundI P (EvalBody.evalOutputRowsPreparedCore.collect rec rowCtx env rows acc emitted) (fun p h => PreparedV h p) :=
  fun hP => outputRowsCollect_spec hrec rowCtx env rows hP acc emitted hreq hP
theorem explicitRowsCollect_app {rec : EvalRec} (hrec : RecSound rec) {rowCtx : EvalCtx} {env : ValEnv}
    {rows : List Expr} {P : Array NeedCell → Prop} {acc : List Result}
    (hreq : ∀ h, P h → ValidCtx h rowCtx ∧ VEV h env ∧ RLV h acc) :
    SoundI P (EvalBody.evalExplicitSequenceValueRowSlots.collect rec rowCtx env rows acc) (fun xs h => RLV h xs) :=
  fun hP => explicitRowsCollect_spec hrec rowCtx env rows hP acc hreq hP
theorem listLiteralCollect_app {rec : EvalRec} (hrec : RecSound rec) {ctx : EvalCtx} {env : ValEnv}
    {elements : List Expr} {P : Array NeedCell → Prop} {acc : List Result}
    (hreq : ∀ h, P h → ValidCtx h ctx ∧ VEV h env ∧ RLV h acc) :
    SoundI P (EvalBody.evalListLiteralCounted.collect rec ctx env elements acc) (fun xs h => RLV h xs) :=
  fun hP => listLiteralCollect_spec hrec ctx env elements hP acc hreq hP
theorem sequenceConstructLoop_app {rec : EvalRec} (hrec : RecSound rec) {ctx : EvalCtx} {env : ValEnv}
    {leaves : List Expr} {P : Array NeedCell → Prop} {items : List Result}
    (hreq : ∀ h, P h → ValidCtx h ctx ∧ VEV h env ∧ RLV h items) :
    SoundI P (EvalBody.evalSequenceConstructCounted.loop rec ctx env leaves items) (fun r h => CRV h r) :=
  fun hP => sequenceConstructLoop_spec hrec ctx env leaves hP items hreq hP
theorem prepareControls_app {rec : EvalRec} (hrec : RecSound rec) {b : Builtin} {ctx : EvalCtx} {env : ValEnv}
    {descriptors : List SequenceBuiltinSuffixArgDescriptor} {P : Array NeedCell → Prop} {items : List CallableCallItem}
    (hreq : ∀ h, P h → ValidCtx h ctx ∧ VEV h env ∧ ItemLV h items) :
    SoundI P (EvalBody.bindSequenceBuiltinArguments.prepareControls rec b ctx env descriptors items)
      (fun xs h => SuffixLV h xs) :=
  fun hP => prepareControls_spec hrec b ctx env descriptors hP items hreq hP
theorem reduceLoop_app {rec : EvalRec} (hrec : RecSound rec) {stepAlg : Algorithm} {ctx : EvalCtx} {env : ValEnv}
    {items : List CountedResult} {P : Array NeedCell → Prop} {acc : CountedResult}
    (hreq : ∀ h, P h → ValidCtx h ctx ∧ VEV h env ∧ CRLV h items ∧ CRV h acc) :
    SoundI P (EvalBody.evalReduceCounted.reduceLoop rec stepAlg ctx env items acc) (fun r h => CRV h r) :=
  fun hP => reduceLoop_spec hrec stepAlg ctx env items hP acc hreq hP
theorem filterLoop_app {rec : EvalRec} (hrec : RecSound rec) {predicateAlg : Algorithm} {ctx : EvalCtx}
    {env : ValEnv} {items : List CountedResult} {P : Array NeedCell → Prop} {index : Nat}
    (hreq : ∀ h, P h → ValidCtx h ctx ∧ VEV h env ∧ CRLV h items) :
    SoundI P (EvalBody.evalFilterCounted.filterLoop rec predicateAlg ctx env index items) (fun xs h => RLV h xs) :=
  fun hP => filterLoop_spec hrec predicateAlg ctx env items hP index hreq hP
theorem mapLoop_app {rec : EvalRec} (hrec : RecSound rec) {transformAlg : Algorithm} {ctx : EvalCtx}
    {env : ValEnv} {items : List CountedResult} {P : Array NeedCell → Prop}
    (hreq : ∀ h, P h → ValidCtx h ctx ∧ VEV h env ∧ CRLV h items) :
    SoundI P (EvalBody.evalMapCounted.mapLoop rec transformAlg ctx env items) (fun xs h => RLV h xs) :=
  fun hP => mapLoop_spec hrec transformAlg ctx env items hP hreq hP
theorem repeatLoop_app {rec : EvalRec} (hrec : RecSound rec) {ctx : EvalCtx} {env : ValEnv}
    {step : ResolvedArgumentAlgorithm} {stepName : String} {remaining : Nat} {P : Array NeedCell → Prop}
    {cells : List Nat} (hreq : ∀ h, P h → ValidCtx h ctx ∧ VEV h env ∧ RAV h step ∧ ValidAddresses h cells) :
    SoundI P (EvalBody.applyBuiltinCounted.repeatLoop rec ctx env step stepName remaining cells)
      (fun xs h => ValidAddresses h xs) :=
  fun hP => repeatLoop_spec hrec ctx env step stepName remaining hP cells hreq hP

attribute [ht_spec] outputRowsCollect_app explicitRowsCollect_app listLiteralCollect_app
  sequenceConstructLoop_app prepareControls_app reduceLoop_app filterLoop_app mapLoop_app repeatLoop_app

/-- The bare read at a VALUE terminal (OD-E, M4★): one evaluator call per terminal kind, each with the
    terminal's own context and environment. -/
theorem terminalAccess_spec {rec : EvalRec} (hrec : RecSound rec) (t : AliasTerminal) (ctx : EvalCtx)
    (env : ValEnv) {P : Array NeedCell → Prop} (_hP : HMono P) (hreq : ∀ h, P h → ValidCtx h ctx ∧ VEV h env) :
    SoundI P (EvalBody.terminalAccess rec t ctx env) (fun r h => CRV h r) := by
  cases t <;> (unfold EvalBody.terminalAccess; ht_tac)

theorem terminalAccess_app {rec : EvalRec} (hrec : RecSound rec) {t : AliasTerminal} {ctx : EvalCtx}
    {env : ValEnv} {P : Array NeedCell → Prop} (hreq : ∀ h, P h → ValidCtx h ctx ∧ VEV h env) :
    SoundI P (EvalBody.terminalAccess rec t ctx env) (fun r h => CRV h r) :=
  fun hP => terminalAccess_spec hrec t ctx env hP hreq hP

attribute [ht_spec] terminalAccess_app

theorem RALV.head' {h : Array NeedCell} {x : ResolvedArgumentAlgorithm} {xs : List ResolvedArgumentAlgorithm}
    (v : RALV h (x :: xs)) : RAV h x := v x List.mem_cons_self
theorem RALV.tail' {h : Array NeedCell} {x : ResolvedArgumentAlgorithm} {xs : List ResolvedArgumentAlgorithm}
    (v : RALV h (x :: xs)) : RALV h xs := fun y m => v y (List.mem_cons_of_mem _ m)
attribute [ht_lemmas] RALV.head' RALV.tail'
attribute [ht_fwd] RALV.head' RALV.tail'

theorem GotV.cache_lookup {st : EvalState} {h : Array NeedCell} (v : GotV st h) {key : ZeroArgPropertyCacheKey}
    {c : CountedResult} (e : ZeroArgPropertyCache.lookup st.zeroArgPropertyCache key = some c) : CRV h c := by
  have : ∀ (cache : ZeroArgPropertyCache), (∀ p ∈ cache, CRV st.needs p.2) →
      ZeroArgPropertyCache.lookup cache key = some c → CRV st.needs c := by
    intro cache
    induction cache with
    | nil => intro _ e; simp [ZeroArgPropertyCache.lookup] at e
    | cons p rest ih =>
      intro hv e
      obtain ⟨k, w⟩ := p
      simp only [ZeroArgPropertyCache.lookup] at e
      split at e
      · cases e; exact hv _ List.mem_cons_self
      · exact ih (fun q m => hv q (List.mem_cons_of_mem _ m)) e
  exact CRV.mono v.2 (this _ v.1.cache e)
attribute [ht_lemmas] GotV.cache_lookup
attribute [ht_fwd] GotV.cache_lookup

theorem set_run' (t s : EvalState) : (MonadStateOf.set t : EvalM PUnit).runState s = (.ok ⟨⟩, t) := rfl

theorem zeroArgPropertyCalc_spec {rec : EvalRec} (hrec : RecSound rec) {P : Array NeedCell → Prop}
    {request : ZeroArgPropertyRequest} {a : Algorithm} {ctx : EvalCtx} {env : ValEnv}
    (hreq : ∀ h, P h → ValidCtx h ctx ∧ VEV h env) :
    SoundI P (EvalBody.zeroArgPropertyCalculation rec request a ctx env) (fun r h => CRV h r) := by
  unfold EvalBody.zeroArgPropertyCalculation EvalBody.evalPropertyDemandCounted EvalBody.evalNeedUserSupplyOutput
  ht_tac

theorem RLV.of_eq {h : Array NeedCell} {xs ys : List Result} (v : RLV h xs) (e : xs = ys) : RLV h ys := e ▸ v
theorem SuffixLV.of_eq {h : Array NeedCell} {xs ys : List PreparedSequenceBuiltinSuffixArg} (v : SuffixLV h xs)
    (e : xs = ys) : SuffixLV h ys := e ▸ v
theorem SuffixLV.drop' {h : Array NeedCell} {xs : List PreparedSequenceBuiltinSuffixArg} (v : SuffixLV h xs)
    (n : Nat) : SuffixLV h (xs.drop n) := fun x m => v x (List.mem_of_mem_drop m)
theorem SuffixLV.head' {h : Array NeedCell} {x : PreparedSequenceBuiltinSuffixArg}
    {xs : List PreparedSequenceBuiltinSuffixArg} (v : SuffixLV h (x :: xs)) : SuffixV h x := v x List.mem_cons_self
theorem SuffixLV.tail' {h : Array NeedCell} {x : PreparedSequenceBuiltinSuffixArg}
    {xs : List PreparedSequenceBuiltinSuffixArg} (v : SuffixLV h (x :: xs)) : SuffixLV h xs :=
  fun y m => v y (List.mem_cons_of_mem _ m)
theorem SuffixLV.drop_eq {h : Array NeedCell} {xs ys : List PreparedSequenceBuiltinSuffixArg} {n : Nat}
    (v : SuffixLV h xs) (e : xs.drop n = ys) : SuffixLV h ys := e ▸ SuffixLV.drop' v n
theorem RLV.head_eq {h : Array NeedCell} {xs ys : List Result} {x : Result} (v : RLV h xs) (e : xs = x :: ys) :
    RV h x := (e ▸ v) x List.mem_cons_self
attribute [ht_lemmas] RLV.of_eq SuffixLV.of_eq SuffixLV.drop' SuffixLV.head' SuffixLV.tail' SuffixLV.drop_eq RLV.head_eq
attribute [ht_fwd] RLV.of_eq SuffixLV.drop_eq SuffixLV.head' SuffixLV.tail' RLV.head_eq

/-! ## The bodies -/

theorem EvalBody.whileLoop_sound (rec : EvalRec) (hrec : RecSound rec) (step : ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) (stepName : String) (cells : List Nat) :
    SoundI (CallPre (.whileLoop step ctx env stepName cells)) (EvalBody.whileLoop rec step ctx env stepName cells) (CallPost (.whileLoop step ctx env stepName cells)) := by
  unfold EvalBody.whileLoop; ht_tac

theorem EvalBody.aliasStepIsRuntime_sound (rec : EvalRec) (hrec : RecSound rec) (step : Algorithm) (target : Expr) (ctx : EvalCtx) (visited : List String) :
    SoundI (CallPre (.aliasStepIsRuntime step target ctx visited)) (EvalBody.aliasStepIsRuntime rec step target ctx visited) (CallPost (.aliasStepIsRuntime step target ctx visited)) := by
  unfold EvalBody.aliasStepIsRuntime; ht_tac

theorem EvalBody.aliasValue_sound (rec : EvalRec) (hrec : RecSound rec) (wired : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    SoundI (CallPre (.aliasValue wired ctx env)) (EvalBody.aliasValue rec wired ctx env) (CallPost (.aliasValue wired ctx env)) := by
  unfold EvalBody.aliasValue; ht_tac

theorem EvalBody.resolveAliasChase_sound (rec : EvalRec) (hrec : RecSound rec) (followCarriers projectRuntime : Bool) (a : Algorithm) (ctx : EvalCtx) (visited : List String) (last : Option (Algorithm × PropDef)) :
    SoundI (CallPre (.resolveAliasChase followCarriers projectRuntime a ctx visited last)) (EvalBody.resolveAliasChase rec followCarriers projectRuntime a ctx visited last) (CallPost (.resolveAliasChase followCarriers projectRuntime a ctx visited last)) := by
  unfold EvalBody.resolveAliasChase; ht_tac

theorem EvalBody.resolveAliasTarget_sound (rec : EvalRec) (hrec : RecSound rec) (a : Algorithm) (ctx : EvalCtx) :
    SoundI (CallPre (.resolveAliasTarget a ctx)) (EvalBody.resolveAliasTarget rec a ctx) (CallPost (.resolveAliasTarget a ctx)) := by
  unfold EvalBody.resolveAliasTarget; ht_tac

theorem EvalBody.resolveAliasStructure_sound (rec : EvalRec) (hrec : RecSound rec) (a : Algorithm) (ctx : EvalCtx) :
    SoundI (CallPre (.resolveAliasStructure a ctx)) (EvalBody.resolveAliasStructure rec a ctx) (CallPost (.resolveAliasStructure a ctx)) := by
  unfold EvalBody.resolveAliasStructure; ht_tac

theorem EvalBody.aliasOriginBinding?_sound (rec : EvalRec) (hrec : RecSound rec) (a : Algorithm) (ctx : EvalCtx) :
    SoundI (CallPre (.aliasOriginBinding? a ctx)) (EvalBody.aliasOriginBinding? rec a ctx) (CallPost (.aliasOriginBinding? a ctx)) := by
  unfold EvalBody.aliasOriginBinding?; ht_tac

theorem EvalBody.resolveAliasValueTarget_sound (rec : EvalRec) (hrec : RecSound rec) (a : Algorithm) (ctx : EvalCtx) :
    SoundI (CallPre (.resolveAliasValueTarget a ctx)) (EvalBody.resolveAliasValueTarget rec a ctx) (CallPost (.resolveAliasValueTarget a ctx)) := by
  unfold EvalBody.resolveAliasValueTarget; ht_tac

theorem EvalBody.lookupLexicalProperty_sound (rec : EvalRec) (hrec : RecSound rec) (a : Algorithm) (name : Ident) (ctx : EvalCtx) :
    SoundI (CallPre (.lookupLexicalProperty a name ctx)) (EvalBody.lookupLexicalProperty rec a name ctx) (CallPost (.lookupLexicalProperty a name ctx)) := by
  unfold EvalBody.lookupLexicalProperty; ht_tac

theorem EvalBody.lookupLexicalValueProperty_sound (rec : EvalRec) (hrec : RecSound rec) (a : Algorithm) (name : Ident) (ctx : EvalCtx) :
    SoundI (CallPre (.lookupLexicalValueProperty a name ctx)) (EvalBody.lookupLexicalValueProperty rec a name ctx) (CallPost (.lookupLexicalValueProperty a name ctx)) := by
  unfold EvalBody.lookupLexicalValueProperty; ht_tac

theorem EvalBody.lookupLexical_sound (rec : EvalRec) (hrec : RecSound rec) (a : Algorithm) (name : Ident) (ctx : EvalCtx) :
    SoundI (CallPre (.lookupLexical a name ctx)) (EvalBody.lookupLexical rec a name ctx) (CallPost (.lookupLexical a name ctx)) := by
  unfold EvalBody.lookupLexical; ht_tac

theorem EvalBody.needPlanNormalizeCallee_sound (rec : EvalRec) (hrec : RecSound rec) (callee : Algorithm) (ctx : EvalCtx) :
    SoundI (CallPre (.needPlanNormalizeCallee callee ctx)) (EvalBody.needPlanNormalizeCallee rec callee ctx) (CallPost (.needPlanNormalizeCallee callee ctx)) := by
  unfold EvalBody.needPlanNormalizeCallee; ht_tac

theorem EvalBody.resolveAlg_sound (rec : EvalRec) (hrec : RecSound rec) (e : Expr) (ctx : EvalCtx) :
    SoundI (CallPre (.resolveAlg e ctx)) (EvalBody.resolveAlg rec e ctx) (CallPost (.resolveAlg e ctx)) := by
  unfold EvalBody.resolveAlg; ht_tac

theorem EvalBody.projectNeedCallable_sound (rec : EvalRec) (hrec : RecSound rec) (address : Nat) :
    SoundI (CallPre (.projectNeedCallable address)) (EvalBody.projectNeedCallable rec address) (CallPost (.projectNeedCallable address)) := by
  unfold EvalBody.projectNeedCallable; ht_tac

theorem EvalBody.projectNeedWrittenAt_sound (rec : EvalRec) (hrec : RecSound rec) (address : Nat) (source : Expr) (caller : EvalCtx) :
    SoundI (CallPre (.projectNeedWrittenAt address source caller)) (EvalBody.projectNeedWrittenAt rec address source caller) (CallPost (.projectNeedWrittenAt address source caller)) := by
  unfold EvalBody.projectNeedWrittenAt; ht_tac

theorem EvalBody.linkCallable_sound (rec : EvalRec) (hrec : RecSound rec) (address : Nat) :
    SoundI (CallPre (.linkCallable address)) (EvalBody.linkCallable rec address) (CallPost (.linkCallable address)) := by
  unfold EvalBody.linkCallable; ht_tac

theorem EvalBody.projectParameterCallable_sound (rec : EvalRec) (hrec : RecSound rec) (x : Ident) (ctx : EvalCtx) :
    SoundI (CallPre (.projectParameterCallable x ctx)) (EvalBody.projectParameterCallable rec x ctx) (CallPost (.projectParameterCallable x ctx)) := by
  unfold EvalBody.projectParameterCallable; ht_tac

theorem EvalBody.projectNeedWritten_sound (rec : EvalRec) (hrec : RecSound rec) (source : Expr) (caller : EvalCtx) :
    SoundI (CallPre (.projectNeedWritten source caller)) (EvalBody.projectNeedWritten rec source caller) (CallPost (.projectNeedWritten source caller)) := by
  unfold EvalBody.projectNeedWritten; ht_tac

theorem EvalBody.projectNeedStructuralMember_sound (rec : EvalRec) (hrec : RecSound rec) (source : Expr) (ctx : EvalCtx) :
    SoundI (CallPre (.projectNeedStructuralMember source ctx)) (EvalBody.projectNeedStructuralMember rec source ctx) (CallPost (.projectNeedStructuralMember source ctx)) := by
  unfold EvalBody.projectNeedStructuralMember; ht_tac

theorem EvalBody.resolveCalleeAlg_sound (rec : EvalRec) (hrec : RecSound rec) (f : Expr) (ctx : EvalCtx) :
    SoundI (CallPre (.resolveCalleeAlg f ctx)) (EvalBody.resolveCalleeAlg rec f ctx) (CallPost (.resolveCalleeAlg f ctx)) := by
  unfold EvalBody.resolveCalleeAlg; ht_tac

theorem EvalBody.expectPreparedSequenceBuiltinAlgorithmSuffixArg_sound (rec : EvalRec) (hrec : RecSound rec) (b : Builtin) (descriptors : List SequenceBuiltinSuffixArgDescriptor) (args : List PreparedSequenceBuiltinSuffixArg) (index : Nat) :
    SoundI (CallPre (.expectPreparedSequenceBuiltinAlgorithmSuffixArg b descriptors args index)) (EvalBody.expectPreparedSequenceBuiltinAlgorithmSuffixArg rec b descriptors args index) (CallPost (.expectPreparedSequenceBuiltinAlgorithmSuffixArg b descriptors args index)) := by
  unfold EvalBody.expectPreparedSequenceBuiltinAlgorithmSuffixArg; ht_tac

theorem EvalBody.resolveDotReceiver?_sound (rec : EvalRec) (hrec : RecSound rec) (e : Expr) (ctx : EvalCtx) :
    SoundI (CallPre (.resolveDotReceiver? e ctx)) (EvalBody.resolveDotReceiver? rec e ctx) (CallPost (.resolveDotReceiver? e ctx)) := by
  unfold EvalBody.resolveDotReceiver?; ht_tac

theorem EvalBody.resolveDotReceiver_sound (rec : EvalRec) (hrec : RecSound rec) (e : Expr) (ctx : EvalCtx) :
    SoundI (CallPre (.resolveDotReceiver e ctx)) (EvalBody.resolveDotReceiver rec e ctx) (CallPost (.resolveDotReceiver e ctx)) := by
  unfold EvalBody.resolveDotReceiver; ht_tac

theorem EvalBody.algorithmIntrinsicRoute_sound (rec : EvalRec) (hrec : RecSound rec) (receiver : Expr) (ctx : EvalCtx) :
    SoundI (CallPre (.algorithmIntrinsicRoute receiver ctx)) (EvalBody.algorithmIntrinsicRoute rec receiver ctx) (CallPost (.algorithmIntrinsicRoute receiver ctx)) := by
  unfold EvalBody.algorithmIntrinsicRoute; ht_tac

theorem EvalBody.demandNeedRecursive_sound (rec : EvalRec) (hrec : RecSound rec) (address : Nat) :
    SoundI (CallPre (.demandNeedRecursive address)) (EvalBody.demandNeedRecursive rec address) (CallPost (.demandNeedRecursive address)) := by
  unfold EvalBody.demandNeedRecursive; ht_tac

theorem EvalBody.evalSuppliedAt_sound (rec : EvalRec) (hrec : RecSound rec) (address : Nat) (e : Expr) (ctx : EvalCtx) (env : ValEnv) :
    SoundI (CallPre (.evalSuppliedAt address e ctx env)) (EvalBody.evalSuppliedAt rec address e ctx env) (CallPost (.evalSuppliedAt address e ctx env)) := by
  unfold EvalBody.evalSuppliedAt; ht_tac

theorem EvalBody.linkValue_sound (rec : EvalRec) (hrec : RecSound rec) (address : Nat) :
    SoundI (CallPre (.linkValue address)) (EvalBody.linkValue rec address) (CallPost (.linkValue address)) := by
  unfold EvalBody.linkValue; ht_tac

theorem EvalBody.algorithmOfValue_sound (rec : EvalRec) (hrec : RecSound rec) (val : Result) (argsOpt : Option OutputBundle) (ctx : EvalCtx) (env : ValEnv) :
    SoundI (CallPre (.algorithmOfValue val argsOpt ctx env)) (EvalBody.algorithmOfValue rec val argsOpt ctx env) (CallPost (.algorithmOfValue val argsOpt ctx env)) := by
  unfold EvalBody.algorithmOfValue; ht_tac

theorem EvalBody.capturedCallee_sound (rec : EvalRec) (hrec : RecSound rec) (callee : Nat) :
    SoundI (CallPre (.capturedCallee callee)) (EvalBody.capturedCallee rec callee) (CallPost (.capturedCallee callee)) := by
  unfold EvalBody.capturedCallee; ht_tac

theorem EvalBody.referenceReceiverValue_sound (rec : EvalRec) (hrec : RecSound rec) (target : Expr) (targetAlg : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    SoundI (CallPre (.referenceReceiverValue target targetAlg ctx env)) (EvalBody.referenceReceiverValue rec target targetAlg ctx env) (CallPost (.referenceReceiverValue target targetAlg ctx env)) := by
  unfold EvalBody.referenceReceiverValue; ht_tac

theorem EvalBody.algorithmCalleeOf_sound (rec : EvalRec) (hrec : RecSound rec) (receiver : Expr) (ctx : EvalCtx) (env : ValEnv) :
    SoundI (CallPre (.algorithmCalleeOf receiver ctx env)) (EvalBody.algorithmCalleeOf rec receiver ctx env) (CallPost (.algorithmCalleeOf receiver ctx env)) := by
  unfold EvalBody.algorithmCalleeOf; ht_tac

theorem EvalBody.evalSuppliedCallCounted_sound (rec : EvalRec) (hrec : RecSound rec) (origin : CalleeOrigin) (callee : Algorithm) (cells : List NeedSupply.Sourced) (ctx : EvalCtx) (env : ValEnv) (calleeName : String) :
    SoundI (CallPre (.evalSuppliedCallCounted origin callee cells ctx env calleeName)) (EvalBody.evalSuppliedCallCounted rec origin callee cells ctx env calleeName) (CallPost (.evalSuppliedCallCounted origin callee cells ctx env calleeName)) := by
  unfold EvalBody.evalSuppliedCallCounted; ht_tac

theorem EvalBody.evalNeedUserSupply_sound (rec : EvalRec) (hrec : RecSound rec) (callee : Algorithm) (cells : List Nat) (ctx : EvalCtx) (env : ValEnv) :
    SoundI (CallPre (.evalNeedUserSupply callee cells ctx env)) (EvalBody.evalNeedUserSupply rec callee cells ctx env) (CallPost (.evalNeedUserSupply callee cells ctx env)) := by
  unfold EvalBody.evalNeedUserSupply; ht_tac

theorem EvalBody.evalNeedFamilySupply_sound (rec : EvalRec) (hrec : RecSound rec) (callee : Algorithm) (cells : List Nat) (ctx : EvalCtx) (env : ValEnv) (calleeName : String) :
    SoundI (CallPre (.evalNeedFamilySupply callee cells ctx env calleeName)) (EvalBody.evalNeedFamilySupply rec callee cells ctx env calleeName) (CallPost (.evalNeedFamilySupply callee cells ctx env calleeName)) := by
  unfold EvalBody.evalNeedFamilySupply; ht_tac

theorem EvalBody.invokeNeed_sound (rec : EvalRec) (hrec : RecSound rec) (arg : ResolvedArgumentAlgorithm) :
    SoundI (CallPre (.invokeNeed arg)) (EvalBody.invokeNeed rec arg) (CallPost (.invokeNeed arg)) := by
  unfold EvalBody.invokeNeed; ht_tac

theorem EvalBody.argumentNeed_sound (rec : EvalRec) (hrec : RecSound rec) (arg : ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) :
    SoundI (CallPre (.argumentNeed arg ctx env)) (EvalBody.argumentNeed rec arg ctx env) (CallPost (.argumentNeed arg ctx env)) := by
  unfold EvalBody.argumentNeed; ht_tac

theorem EvalBody.runNeedStepSlots_sound (rec : EvalRec) (hrec : RecSound rec) (step : Algorithm) (ctx : EvalCtx) (env : ValEnv) (cells : List Nat) (stepName : String) :
    SoundI (CallPre (.runNeedStepSlots step ctx env cells stepName)) (EvalBody.runNeedStepSlots rec step ctx env cells stepName) (CallPost (.runNeedStepSlots step ctx env cells stepName)) := by
  unfold EvalBody.runNeedStepSlots EvalBody.runNeedStepWith; ht_tac

theorem EvalBody.runNeedWhileRound_sound (rec : EvalRec) (hrec : RecSound rec) (step : Algorithm) (ctx : EvalCtx) (env : ValEnv) (cells : List Nat) (stepName : String) :
    SoundI (CallPre (.runNeedWhileRound step ctx env cells stepName)) (EvalBody.runNeedWhileRound rec step ctx env cells stepName) (CallPost (.runNeedWhileRound step ctx env cells stepName)) := by
  unfold EvalBody.runNeedWhileRound EvalBody.runNeedStepWith; ht_tac

theorem EvalBody.evalAlgOutputCore_sound (rec : EvalRec) (hrec : RecSound rec) (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    SoundI (CallPre (.evalAlgOutputCore a ctx env)) (EvalBody.evalAlgOutputCore rec a ctx env) (CallPost (.evalAlgOutputCore a ctx env)) := by
  unfold EvalBody.evalAlgOutputCore; ht_tac

theorem EvalBody.evalAlgOutput_sound (rec : EvalRec) (hrec : RecSound rec) (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    SoundI (CallPre (.evalAlgOutput a ctx env)) (EvalBody.evalAlgOutput rec a ctx env) (CallPost (.evalAlgOutput a ctx env)) := by
  unfold EvalBody.evalAlgOutput; ht_tac

theorem EvalBody.evalProgramOutput_sound (rec : EvalRec) (hrec : RecSound rec) (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    SoundI (CallPre (.evalProgramOutput a ctx env)) (EvalBody.evalProgramOutput rec a ctx env) (CallPost (.evalProgramOutput a ctx env)) := by
  unfold EvalBody.evalProgramOutput; ht_tac

theorem EvalBody.evalAlgOutputSlots_sound (rec : EvalRec) (hrec : RecSound rec) (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    SoundI (CallPre (.evalAlgOutputSlots a ctx env)) (EvalBody.evalAlgOutputSlots rec a ctx env) (CallPost (.evalAlgOutputSlots a ctx env)) := by
  unfold EvalBody.evalAlgOutputSlots ActivatedBody.readRows; ht_tac

theorem EvalBody.formOutputRow_sound (rec : EvalRec) (hrec : RecSound rec) (ctx : EvalCtx) (env : ValEnv) (e : Expr) :
    SoundI (CallPre (.formOutputRow ctx env e)) (EvalBody.formOutputRow rec ctx env e) (CallPost (.formOutputRow ctx env e)) := by
  unfold EvalBody.formOutputRow; ht_tac

theorem EvalBody.whileVerdictSlots_sound (rec : EvalRec) (hrec : RecSound rec) (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    SoundI (CallPre (.whileVerdictSlots a ctx env)) (EvalBody.whileVerdictSlots rec a ctx env) (CallPost (.whileVerdictSlots a ctx env)) := by
  unfold EvalBody.whileVerdictSlots ActivatedBody.readRows; ht_tac

theorem EvalBody.evalSequenceCallbackCall_sound (rec : EvalRec) (hrec : RecSound rec) (callee : Algorithm) (item : CountedResult) (ctx : EvalCtx) (env : ValEnv) (calleeName : String) :
    SoundI (CallPre (.evalSequenceCallbackCall callee item ctx env calleeName)) (EvalBody.evalSequenceCallbackCall rec callee item ctx env calleeName) (CallPost (.evalSequenceCallbackCall callee item ctx env calleeName)) := by
  unfold EvalBody.evalSequenceCallbackCall; ht_tac

theorem EvalBody.evalSequenceCallbackCallCounted_sound (rec : EvalRec) (hrec : RecSound rec) (callee : Algorithm) (item : CountedResult) (ctx : EvalCtx) (env : ValEnv) (calleeName : String) :
    SoundI (CallPre (.evalSequenceCallbackCallCounted callee item ctx env calleeName)) (EvalBody.evalSequenceCallbackCallCounted rec callee item ctx env calleeName) (CallPost (.evalSequenceCallbackCallCounted callee item ctx env calleeName)) := by
  unfold EvalBody.evalSequenceCallbackCallCounted; ht_tac

theorem EvalBody.evalAlgOutputPreparedCore_sound (rec : EvalRec) (hrec : RecSound rec) (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    SoundI (CallPre (.evalAlgOutputPreparedCore a ctx env)) (EvalBody.evalAlgOutputPreparedCore rec a ctx env) (CallPost (.evalAlgOutputPreparedCore a ctx env)) := by
  unfold EvalBody.evalAlgOutputPreparedCore; ht_tac

theorem EvalBody.evalOutputRowsPreparedCore_sound (rec : EvalRec) (hrec : RecSound rec) (rows : OutputBundle) (rowCtx : EvalCtx) (env : ValEnv) :
    SoundI (CallPre (.evalOutputRowsPreparedCore rows rowCtx env)) (EvalBody.evalOutputRowsPreparedCore rec rows rowCtx env) (CallPost (.evalOutputRowsPreparedCore rows rowCtx env)) := by
  unfold EvalBody.evalOutputRowsPreparedCore; ht_tac

theorem EvalBody.evalCapturePreparedCore_sound (rec : EvalRec) (hrec : RecSound rec) (rows : OutputBundle) (ctx : EvalCtx) (env : ValEnv) :
    SoundI (CallPre (.evalCapturePreparedCore rows ctx env)) (EvalBody.evalCapturePreparedCore rec rows ctx env) (CallPost (.evalCapturePreparedCore rows ctx env)) := by
  unfold EvalBody.evalCapturePreparedCore; ht_tac

theorem EvalBody.evalCaptureCountedCore_sound (rec : EvalRec) (hrec : RecSound rec) (rows : OutputBundle) (ctx : EvalCtx) (env : ValEnv) :
    SoundI (CallPre (.evalCaptureCountedCore rows ctx env)) (EvalBody.evalCaptureCountedCore rec rows ctx env) (CallPost (.evalCaptureCountedCore rows ctx env)) := by
  unfold EvalBody.evalCaptureCountedCore; ht_tac

theorem EvalBody.evalCaptureValue_sound (rec : EvalRec) (hrec : RecSound rec) (rows : OutputBundle) (ctx : EvalCtx) (env : ValEnv) :
    SoundI (CallPre (.evalCaptureValue rows ctx env)) (EvalBody.evalCaptureValue rec rows ctx env) (CallPost (.evalCaptureValue rows ctx env)) := by
  unfold EvalBody.evalCaptureValue; ht_tac

theorem EvalBody.evalAlgOutputCountedCore_sound (rec : EvalRec) (hrec : RecSound rec) (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    SoundI (CallPre (.evalAlgOutputCountedCore a ctx env)) (EvalBody.evalAlgOutputCountedCore rec a ctx env) (CallPost (.evalAlgOutputCountedCore a ctx env)) := by
  unfold EvalBody.evalAlgOutputCountedCore; ht_tac

theorem EvalBody.evalAlgOutputCounted_sound (rec : EvalRec) (hrec : RecSound rec) (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    SoundI (CallPre (.evalAlgOutputCounted a ctx env)) (EvalBody.evalAlgOutputCounted rec a ctx env) (CallPost (.evalAlgOutputCounted a ctx env)) := by
  unfold EvalBody.evalAlgOutputCounted; ht_tac

theorem EvalBody.evalZeroArgumentDemandOutputCounted_sound (rec : EvalRec) (hrec : RecSound rec) (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    SoundI (CallPre (.evalZeroArgumentDemandOutputCounted a ctx env)) (EvalBody.evalZeroArgumentDemandOutputCounted rec a ctx env) (CallPost (.evalZeroArgumentDemandOutputCounted a ctx env)) := by
  unfold EvalBody.evalZeroArgumentDemandOutputCounted; ht_tac

theorem EvalBody.evalZeroArgumentDemandOutput_sound (rec : EvalRec) (hrec : RecSound rec) (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    SoundI (CallPre (.evalZeroArgumentDemandOutput a ctx env)) (EvalBody.evalZeroArgumentDemandOutput rec a ctx env) (CallPost (.evalZeroArgumentDemandOutput a ctx env)) := by
  unfold EvalBody.evalZeroArgumentDemandOutput; ht_tac

theorem EvalBody.evalArgumentValueCounted_sound (rec : EvalRec) (hrec : RecSound rec) (arg : ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) :
    SoundI (CallPre (.evalArgumentValueCounted arg ctx env)) (EvalBody.evalArgumentValueCounted rec arg ctx env) (CallPost (.evalArgumentValueCounted arg ctx env)) := by
  unfold EvalBody.evalArgumentValueCounted; ht_tac

theorem EvalBody.evalArgumentValue_sound (rec : EvalRec) (hrec : RecSound rec) (arg : ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) :
    SoundI (CallPre (.evalArgumentValue arg ctx env)) (EvalBody.evalArgumentValue rec arg ctx env) (CallPost (.evalArgumentValue arg ctx env)) := by
  unfold EvalBody.evalArgumentValue; ht_tac

theorem EvalBody.evalZeroArgPropertyAccess_sound (rec : EvalRec) (hrec : RecSound rec) (accessKind : ZeroArgPropertyAccessKind) (owner : Algorithm) (binding : PropDef) (resolvedAlgorithm : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    SoundI (CallPre (.evalZeroArgPropertyAccess accessKind owner binding resolvedAlgorithm ctx env)) (EvalBody.evalZeroArgPropertyAccess rec accessKind owner binding resolvedAlgorithm ctx env) (CallPost (.evalZeroArgPropertyAccess accessKind owner binding resolvedAlgorithm ctx env)) := by
  unfold EvalBody.evalZeroArgPropertyAccess; ht_tac

theorem EvalBody.evalConditionalCallbackCallCounted_sound (rec : EvalRec) (hrec : RecSound rec) (callee : Algorithm) (args : List CountedResult) (ctx : EvalCtx) (env : ValEnv) (calleeName : String) :
    SoundI (CallPre (.evalConditionalCallbackCallCounted callee args ctx env calleeName)) (EvalBody.evalConditionalCallbackCallCounted rec callee args ctx env calleeName) (CallPost (.evalConditionalCallbackCallCounted callee args ctx env calleeName)) := by
  unfold EvalBody.evalConditionalCallbackCallCounted; ht_tac

theorem EvalBody.evalUserCallbackCallCounted_sound (rec : EvalRec) (hrec : RecSound rec) (callee : Algorithm) (args : List CountedResult) (ctx : EvalCtx) (env : ValEnv) :
    SoundI (CallPre (.evalUserCallbackCallCounted callee args ctx env)) (EvalBody.evalUserCallbackCallCounted rec callee args ctx env) (CallPost (.evalUserCallbackCallCounted callee args ctx env)) := by
  unfold EvalBody.evalUserCallbackCallCounted; ht_tac

theorem EvalBody.evalResolvedCallbackCallCounted_sound (rec : EvalRec) (hrec : RecSound rec) (callee : Algorithm) (args : List CountedResult) (ctx : EvalCtx) (env : ValEnv) (calleeName : String) :
    SoundI (CallPre (.evalResolvedCallbackCallCounted callee args ctx env calleeName)) (EvalBody.evalResolvedCallbackCallCounted rec callee args ctx env calleeName) (CallPost (.evalResolvedCallbackCallCounted callee args ctx env calleeName)) := by
  unfold EvalBody.evalResolvedCallbackCallCounted; ht_tac

theorem EvalBody.evalResolvedCallbackCall_sound (rec : EvalRec) (hrec : RecSound rec) (callee : Algorithm) (args : List CountedResult) (ctx : EvalCtx) (env : ValEnv) (calleeName : String) :
    SoundI (CallPre (.evalResolvedCallbackCall callee args ctx env calleeName)) (EvalBody.evalResolvedCallbackCall rec callee args ctx env calleeName) (CallPost (.evalResolvedCallbackCall callee args ctx env calleeName)) := by
  unfold EvalBody.evalResolvedCallbackCall; ht_tac

theorem EvalBody.evalSequenceReduceStepCounted_sound (rec : EvalRec) (hrec : RecSound rec) (callee : Algorithm) (element : CountedResult) (accumulator : Result) (ctx : EvalCtx) (env : ValEnv) (calleeName : String) :
    SoundI (CallPre (.evalSequenceReduceStepCounted callee element accumulator ctx env calleeName)) (EvalBody.evalSequenceReduceStepCounted rec callee element accumulator ctx env calleeName) (CallPost (.evalSequenceReduceStepCounted callee element accumulator ctx env calleeName)) := by
  unfold EvalBody.evalSequenceReduceStepCounted; ht_tac

theorem EvalBody.demandSequenceBuiltinCallItemValue_sound (rec : EvalRec) (hrec : RecSound rec) (item : CallableCallItem) (ctx : EvalCtx) (env : ValEnv) :
    SoundI (CallPre (.demandSequenceBuiltinCallItemValue item ctx env)) (EvalBody.demandSequenceBuiltinCallItemValue rec item ctx env) (CallPost (.demandSequenceBuiltinCallItemValue item ctx env)) := by
  unfold EvalBody.demandSequenceBuiltinCallItemValue; ht_tac

theorem EvalBody.bindSequenceBuiltinArguments_sound (rec : EvalRec) (hrec : RecSound rec) (b : Builtin) (metadata : SequenceBuiltinMetadata) (args : List ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) :
    SoundI (CallPre (.bindSequenceBuiltinArguments b metadata args ctx env)) (EvalBody.bindSequenceBuiltinArguments rec b metadata args ctx env) (CallPost (.bindSequenceBuiltinArguments b metadata args ctx env)) := by
  unfold EvalBody.bindSequenceBuiltinArguments; ht_tac

theorem EvalBody.evalReduceCounted_sound (rec : EvalRec) (hrec : RecSound rec) (collection : List CountedResult) (stepAlg : Algorithm) (initial : Result) (ctx : EvalCtx) (env : ValEnv) :
    SoundI (CallPre (.evalReduceCounted collection stepAlg initial ctx env)) (EvalBody.evalReduceCounted rec collection stepAlg initial ctx env) (CallPost (.evalReduceCounted collection stepAlg initial ctx env)) := by
  unfold EvalBody.evalReduceCounted; ht_tac

theorem EvalBody.evalFilterCounted_sound (rec : EvalRec) (hrec : RecSound rec) (items : List CountedResult) (predicateAlg : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    SoundI (CallPre (.evalFilterCounted items predicateAlg ctx env)) (EvalBody.evalFilterCounted rec items predicateAlg ctx env) (CallPost (.evalFilterCounted items predicateAlg ctx env)) := by
  unfold EvalBody.evalFilterCounted; ht_tac

theorem EvalBody.evalMapCounted_sound (rec : EvalRec) (hrec : RecSound rec) (collection : List CountedResult) (transformAlg : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    SoundI (CallPre (.evalMapCounted collection transformAlg ctx env)) (EvalBody.evalMapCounted rec collection transformAlg ctx env) (CallPost (.evalMapCounted collection transformAlg ctx env)) := by
  unfold EvalBody.evalMapCounted; ht_tac

set_option maxHeartbeats 2000000 in
theorem EvalBody.applyBuiltinCountedSequence_sound (rec : EvalRec) (hrec : RecSound rec) (b : Builtin) (metadata : SequenceBuiltinMetadata) (args : List ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) :
    SoundI (CallPre (.applyBuiltinCountedSequence b metadata args ctx env)) (EvalBody.applyBuiltinCountedSequence rec b metadata args ctx env) (CallPost (.applyBuiltinCountedSequence b metadata args ctx env)) := by
  unfold EvalBody.applyBuiltinCountedSequence; ht_tac

set_option maxHeartbeats 2000000 in
theorem EvalBody.applyBuiltinCounted_sound (rec : EvalRec) (hrec : RecSound rec) (b : Builtin) (args : List ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) :
    SoundI (CallPre (.applyBuiltinCounted b args ctx env)) (EvalBody.applyBuiltinCounted rec b args ctx env) (CallPost (.applyBuiltinCounted b args ctx env)) := by
  unfold EvalBody.applyBuiltinCounted; ht_tac

theorem EvalBody.applyBuiltin_sound (rec : EvalRec) (hrec : RecSound rec) (b : Builtin) (args : List ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) :
    SoundI (CallPre (.applyBuiltin b args ctx env)) (EvalBody.applyBuiltin rec b args ctx env) (CallPost (.applyBuiltin b args ctx env)) := by
  unfold EvalBody.applyBuiltin; ht_tac

theorem EvalBody.applyBuiltinCountedResolved_sound (rec : EvalRec) (hrec : RecSound rec) (b : Builtin) (args : List ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) :
    SoundI (CallPre (.applyBuiltinCountedResolved b args ctx env)) (EvalBody.applyBuiltinCountedResolved rec b args ctx env) (CallPost (.applyBuiltinCountedResolved b args ctx env)) := by
  unfold EvalBody.applyBuiltinCountedResolved; ht_tac

theorem EvalBody.evalExplicitSequenceValueItems_sound (rec : EvalRec) (hrec : RecSound rec) (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    SoundI (CallPre (.evalExplicitSequenceValueItems a ctx env)) (EvalBody.evalExplicitSequenceValueItems rec a ctx env) (CallPost (.evalExplicitSequenceValueItems a ctx env)) := by
  unfold EvalBody.evalExplicitSequenceValueItems; ht_tac

theorem EvalBody.evalExplicitSequenceValueRowSlots_sound (rec : EvalRec) (hrec : RecSound rec) (rows : OutputBundle) (rowCtx : EvalCtx) (env : ValEnv) :
    SoundI (CallPre (.evalExplicitSequenceValueRowSlots rows rowCtx env)) (EvalBody.evalExplicitSequenceValueRowSlots rec rows rowCtx env) (CallPost (.evalExplicitSequenceValueRowSlots rows rowCtx env)) := by
  unfold EvalBody.evalExplicitSequenceValueRowSlots; ht_tac

theorem EvalBody.evalExplicitSequenceValueExprSlots_sound (rec : EvalRec) (hrec : RecSound rec) (expr : Expr) (ctx : EvalCtx) (env : ValEnv) :
    SoundI (CallPre (.evalExplicitSequenceValueExprSlots expr ctx env)) (EvalBody.evalExplicitSequenceValueExprSlots rec expr ctx env) (CallPost (.evalExplicitSequenceValueExprSlots expr ctx env)) := by
  unfold EvalBody.evalExplicitSequenceValueExprSlots; ht_tac

theorem EvalBody.evalUserCallCounted_sound (rec : EvalRec) (hrec : RecSound rec) (callee : Algorithm) (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) :
    SoundI (CallPre (.evalUserCallCounted callee args ctx env)) (EvalBody.evalUserCallCounted rec callee args ctx env) (CallPost (.evalUserCallCounted callee args ctx env)) := by
  unfold EvalBody.evalUserCallCounted; ht_tac

theorem EvalBody.evalConditionalCallCounted_sound (rec : EvalRec) (hrec : RecSound rec) (callee : Algorithm) (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) (calleeName : String) :
    SoundI (CallPre (.evalConditionalCallCounted callee args ctx env calleeName)) (EvalBody.evalConditionalCallCounted rec callee args ctx env calleeName) (CallPost (.evalConditionalCallCounted callee args ctx env calleeName)) := by
  unfold EvalBody.evalConditionalCallCounted; ht_tac

theorem EvalBody.evalResolvedCall_sound (rec : EvalRec) (hrec : RecSound rec) (callee : Algorithm) (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) (calleeName : String) :
    SoundI (CallPre (.evalResolvedCall callee args ctx env calleeName)) (EvalBody.evalResolvedCall rec callee args ctx env calleeName) (CallPost (.evalResolvedCall callee args ctx env calleeName)) := by
  unfold EvalBody.evalResolvedCall; ht_tac

theorem EvalBody.evalResolvedCallCounted_sound (rec : EvalRec) (hrec : RecSound rec) (callee : Algorithm) (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) (calleeName : String) (origin : CalleeOrigin) :
    SoundI (CallPre (.evalResolvedCallCounted callee args ctx env calleeName origin)) (EvalBody.evalResolvedCallCounted rec callee args ctx env calleeName origin) (CallPost (.evalResolvedCallCounted callee args ctx env calleeName origin)) := by
  unfold EvalBody.evalResolvedCallCounted; ht_tac

theorem EvalBody.evalCallCountedExpr_sound (rec : EvalRec) (hrec : RecSound rec) (f : Expr) (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) :
    SoundI (CallPre (.evalCallCountedExpr f args ctx env)) (EvalBody.evalCallCountedExpr rec f args ctx env) (CallPost (.evalCallCountedExpr f args ctx env)) := by
  unfold EvalBody.evalCallCountedExpr; ht_tac

theorem EvalBody.callLexicalWithReceiverCounted_sound (rec : EvalRec) (hrec : RecSound rec) (name : Ident) (receiver : Expr) (fallback : Expr) (extraArgs : Option OutputBundle) (ctx : EvalCtx) (env : ValEnv) :
    SoundI (CallPre (.callLexicalWithReceiverCounted name receiver fallback extraArgs ctx env)) (EvalBody.callLexicalWithReceiverCounted rec name receiver fallback extraArgs ctx env) (CallPost (.callLexicalWithReceiverCounted name receiver fallback extraArgs ctx env)) := by
  unfold EvalBody.callLexicalWithReceiverCounted; ht_tac

theorem EvalBody.rejectDotStringIntrinsicArguments_sound (rec : EvalRec) (hrec : RecSound rec) (argsOpt : Option OutputBundle) (ctx : EvalCtx) (env : ValEnv) :
    SoundI (CallPre (.rejectDotStringIntrinsicArguments argsOpt ctx env)) (EvalBody.rejectDotStringIntrinsicArguments rec argsOpt ctx env) (CallPost (.rejectDotStringIntrinsicArguments argsOpt ctx env)) := by
  unfold EvalBody.rejectDotStringIntrinsicArguments; ht_tac

theorem EvalBody.evalDotStringReceiverValue_sound (rec : EvalRec) (hrec : RecSound rec) (target : Expr) (targetAlg : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    SoundI (CallPre (.evalDotStringReceiverValue target targetAlg ctx env)) (EvalBody.evalDotStringReceiverValue rec target targetAlg ctx env) (CallPost (.evalDotStringReceiverValue target targetAlg ctx env)) := by
  unfold EvalBody.evalDotStringReceiverValue; ht_tac

set_option maxHeartbeats 2000000 in
theorem EvalBody.evalDotCallCounted_sound (rec : EvalRec) (hrec : RecSound rec) (target : Expr) (name : Ident) (fallback : Expr) (argsOpt : Option OutputBundle) (ctx : EvalCtx) (env : ValEnv) :
    SoundI (CallPre (.evalDotCallCounted target name fallback argsOpt ctx env)) (EvalBody.evalDotCallCounted rec target name fallback argsOpt ctx env) (CallPost (.evalDotCallCounted target name fallback argsOpt ctx env)) := by
  unfold EvalBody.evalDotCallCounted; ht_tac

theorem EvalBody.rejectInvokeIntrinsicArguments_sound (rec : EvalRec) (hrec : RecSound rec) (argsOpt : Option OutputBundle) (ctx : EvalCtx) (env : ValEnv) :
    SoundI (CallPre (.rejectInvokeIntrinsicArguments argsOpt ctx env)) (EvalBody.rejectInvokeIntrinsicArguments rec argsOpt ctx env) (CallPost (.rejectInvokeIntrinsicArguments argsOpt ctx env)) := by
  unfold EvalBody.rejectInvokeIntrinsicArguments; ht_tac

theorem EvalBody.invokeCallReferenceValue_sound (rec : EvalRec) (hrec : RecSound rec) (val : Result) :
    SoundI (CallPre (.invokeCallReferenceValue val)) (EvalBody.invokeCallReferenceValue rec val) (CallPost (.invokeCallReferenceValue val)) := by
  unfold EvalBody.invokeCallReferenceValue; ht_tac

theorem EvalBody.argumentViewCells_sound (rec : EvalRec) (hrec : RecSound rec) (a : Nat) :
    SoundI (CallPre (.argumentViewCells a)) (EvalBody.argumentViewCells rec a) (CallPost (.argumentViewCells a)) := by
  unfold EvalBody.argumentViewCells; ht_tac

theorem EvalBody.evalArgumentViewBuiltin_sound (rec : EvalRec) (hrec : RecSound rec) (b : Builtin) (a : Nat) :
    SoundI (CallPre (.evalArgumentViewBuiltin b a)) (EvalBody.evalArgumentViewBuiltin rec b a) (CallPost (.evalArgumentViewBuiltin b a)) := by
  unfold EvalBody.evalArgumentViewBuiltin; ht_tac

theorem EvalBody.evalSequenceSpreadOperandValue_sound (rec : EvalRec) (hrec : RecSound rec) (e : Expr) (ctx : EvalCtx) (env : ValEnv) :
    SoundI (CallPre (.evalSequenceSpreadOperandValue e ctx env)) (EvalBody.evalSequenceSpreadOperandValue rec e ctx env) (CallPost (.evalSequenceSpreadOperandValue e ctx env)) := by
  unfold EvalBody.evalSequenceSpreadOperandValue; ht_tac

theorem EvalBody.evalSequenceSpreadCounted_sound (rec : EvalRec) (hrec : RecSound rec) (e : Expr) (ctx : EvalCtx) (env : ValEnv) :
    SoundI (CallPre (.evalSequenceSpreadCounted e ctx env)) (EvalBody.evalSequenceSpreadCounted rec e ctx env) (CallPost (.evalSequenceSpreadCounted e ctx env)) := by
  unfold EvalBody.evalSequenceSpreadCounted; ht_tac

theorem EvalBody.evalSupplySpread_sound (rec : EvalRec) (hrec : RecSound rec) (e : Expr) (ctx : EvalCtx) (env : ValEnv) :
    SoundI (CallPre (.evalSupplySpread e ctx env)) (EvalBody.evalSupplySpread rec e ctx env) (CallPost (.evalSupplySpread e ctx env)) := by
  unfold EvalBody.evalSupplySpread; ht_tac

theorem EvalBody.evalListLiteralCounted_sound (rec : EvalRec) (hrec : RecSound rec) (elements : List Expr) (ctx : EvalCtx) (env : ValEnv) :
    SoundI (CallPre (.evalListLiteralCounted elements ctx env)) (EvalBody.evalListLiteralCounted rec elements ctx env) (CallPost (.evalListLiteralCounted elements ctx env)) := by
  unfold EvalBody.evalListLiteralCounted; ht_tac

theorem EvalBody.evalSequenceConstructCounted_sound (rec : EvalRec) (hrec : RecSound rec) (e : Expr) (ctx : EvalCtx) (env : ValEnv) :
    SoundI (CallPre (.evalSequenceConstructCounted e ctx env)) (EvalBody.evalSequenceConstructCounted rec e ctx env) (CallPost (.evalSequenceConstructCounted e ctx env)) := by
  unfold EvalBody.evalSequenceConstructCounted; ht_tac

theorem EvalBody.evalUnaryCounted_sound (rec : EvalRec) (hrec : RecSound rec) (op : UnaryOp) (operand : Expr) (ctx : EvalCtx) (env : ValEnv) :
    SoundI (CallPre (.evalUnaryCounted op operand ctx env)) (EvalBody.evalUnaryCounted rec op operand ctx env) (CallPost (.evalUnaryCounted op operand ctx env)) := by
  unfold EvalBody.evalUnaryCounted; ht_tac

theorem EvalBody.evalBinaryCounted_sound (rec : EvalRec) (hrec : RecSound rec) (op : BinaryOp) (a : Expr) (b : Expr) (ctx : EvalCtx) (env : ValEnv) :
    SoundI (CallPre (.evalBinaryCounted op a b ctx env)) (EvalBody.evalBinaryCounted rec op a b ctx env) (CallPost (.evalBinaryCounted op a b ctx env)) := by
  unfold EvalBody.evalBinaryCounted; ht_tac

theorem EvalBody.evalComparisonCounted_sound (rec : EvalRec) (hrec : RecSound rec) (first : Expr) (links : List ComparisonLink) (ctx : EvalCtx) (env : ValEnv) :
    SoundI (CallPre (.evalComparisonCounted first links ctx env)) (EvalBody.evalComparisonCounted rec first links ctx env) (CallPost (.evalComparisonCounted first links ctx env)) := by
  unfold EvalBody.evalComparisonCounted; ht_tac

theorem EvalBody.evalComparisonLinksCounted_sound (rec : EvalRec) (hrec : RecSound rec) (previousExpr : Expr) (previous : Result) (holds : Bool) (links : List ComparisonLink) (ctx : EvalCtx) (env : ValEnv) :
    SoundI (CallPre (.evalComparisonLinksCounted previousExpr previous holds links ctx env)) (EvalBody.evalComparisonLinksCounted rec previousExpr previous holds links ctx env) (CallPost (.evalComparisonLinksCounted previousExpr previous holds links ctx env)) := by
  unfold EvalBody.evalComparisonLinksCounted; ht_tac

set_option maxHeartbeats 2000000 in
theorem EvalBody.evalCounted_sound (rec : EvalRec) (hrec : RecSound rec) (e : Expr) (ctx : EvalCtx) (env : ValEnv) :
    SoundI (CallPre (.evalCounted e ctx env)) (EvalBody.evalCounted rec e ctx env) (CallPost (.evalCounted e ctx env)) := by
  unfold EvalBody.evalCounted; ht_tac

theorem EvalBody.evalUserCall_sound (rec : EvalRec) (hrec : RecSound rec) (callee : Algorithm) (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) :
    SoundI (CallPre (.evalUserCall callee args ctx env)) (EvalBody.evalUserCall rec callee args ctx env) (CallPost (.evalUserCall callee args ctx env)) := by
  unfold EvalBody.evalUserCall; ht_tac

theorem EvalBody.evalConditionalCall_sound (rec : EvalRec) (hrec : RecSound rec) (callee : Algorithm) (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) (calleeName : String) :
    SoundI (CallPre (.evalConditionalCall callee args ctx env calleeName)) (EvalBody.evalConditionalCall rec callee args ctx env calleeName) (CallPost (.evalConditionalCall callee args ctx env calleeName)) := by
  unfold EvalBody.evalConditionalCall; ht_tac

theorem EvalBody.evalCallExpr_sound (rec : EvalRec) (hrec : RecSound rec) (f : Expr) (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) :
    SoundI (CallPre (.evalCallExpr f args ctx env)) (EvalBody.evalCallExpr rec f args ctx env) (CallPost (.evalCallExpr f args ctx env)) := by
  unfold EvalBody.evalCallExpr; ht_tac

theorem EvalBody.evalDotCall_sound (rec : EvalRec) (hrec : RecSound rec) (target : Expr) (name : Ident) (fallback : Expr) (argsOpt : Option OutputBundle) (ctx : EvalCtx) (env : ValEnv) :
    SoundI (CallPre (.evalDotCall target name fallback argsOpt ctx env)) (EvalBody.evalDotCall rec target name fallback argsOpt ctx env) (CallPost (.evalDotCall target name fallback argsOpt ctx env)) := by
  unfold EvalBody.evalDotCall; ht_tac

theorem EvalBody.eval_sound (rec : EvalRec) (hrec : RecSound rec) (e : Expr) (ctx : EvalCtx) (env : ValEnv) :
    SoundI (CallPre (.eval e ctx env)) (EvalBody.eval rec e ctx env) (CallPost (.eval e ctx env)) := by
  unfold EvalBody.eval; ht_tac

/-- **The property-cache publication write point** (`evalZeroArgPropertyAccessCounted`): a published
    counted result is valid in the heap at its publication; marking a key active changes no address. -/
theorem EvalBody.evalZeroArgPropertyAccessCounted_sound (rec : EvalRec) (hrec : RecSound rec) (accessKind : ZeroArgPropertyAccessKind) (owner : Algorithm) (binding : PropDef) (resolvedAlgorithm : Algorithm) (ctx : EvalCtx) (env : ValEnv) (request : ZeroArgPropertyRequest) :
    SoundI (CallPre (.evalZeroArgPropertyAccessCounted accessKind owner binding resolvedAlgorithm ctx env request)) (EvalBody.evalZeroArgPropertyAccessCounted rec accessKind owner binding resolvedAlgorithm ctx env request) (CallPost (.evalZeroArgPropertyAccessCounted accessKind owner binding resolvedAlgorithm ctx env request)) := by
  have hcalc : SoundI (CallPre (.evalZeroArgPropertyAccessCounted accessKind owner binding resolvedAlgorithm ctx env request))
      (EvalBody.zeroArgPropertyCalculation rec request resolvedAlgorithm ctx env) (fun r h => CRV h r) :=
    zeroArgPropertyCalc_spec hrec (fun h ph => ph)
  unfold EvalBody.evalZeroArgPropertyAccessCounted
  split
  · intro hp s vs ps
    rw [EvalM.bind_runState, get_run]
    dsimp only
    generalize zeroArgPropertyCacheKey accessKind owner binding ctx env
      (propertyOwnerBindingContext resolvedAlgorithm.parent s) = key
    cases hl : s.zeroArgPropertyCache.lookup key with
    | some cached =>
      simp only []
      cases request with
      | read =>
        exact ⟨vs, Nat.le_refl _, fun x hx => by
          cases hx; exact GotV.cache_lookup ⟨vs, Nat.le_refl _⟩ hl⟩
      | invoke name => exact hcalc hp s vs ps
    | none =>
      simp only []
      split
      · exact hcalc hp s vs ps
      · rw [EvalM.bind_runState, set_run']
        dsimp only
        have vt1 : Inv { s with activeZeroArgProperties := key :: s.activeZeroArgProperties } :=
          inv_of_fields vs rfl rfl rfl rfl
        have pt1 := ps
        rw [EvalM.bind_runState]
        obtain ⟨v2, g2, r2⟩ := SoundI.attempt hcalc hp _ vt1 pt1
        revert v2 g2 r2
        rcases (evalAttempt (EvalBody.zeroArgPropertyCalculation rec request resolvedAlgorithm ctx env)).runState
          { s with activeZeroArgProperties := key :: s.activeZeroArgProperties } with ⟨o2, t2⟩
        intro v2 g2 r2
        cases o2 with
        | error e => exact ⟨v2, g2, fun _ hx => by cases hx⟩
        | ok outcome =>
          dsimp only
          rw [EvalM.bind_runState, get_run]
          dsimp only
          cases outcome with
          | ok counted =>
            dsimp only
            rw [EvalM.bind_runState, set_run']
            have hc : CRV t2.needs counted := r2 _ rfl counted rfl
            refine ⟨inv_of_fields (inv_cache_insert v2 key counted hc) rfl rfl rfl rfl, g2, ?_⟩
            intro x hx; cases hx; exact hc
          | error err =>
            dsimp only
            rw [EvalM.bind_runState, set_run']
            exact ⟨inv_of_fields v2 rfl rfl rfl rfl, g2, fun _ hx => by cases hx⟩
  · exact hcalc
/-- **THE PER-BODY OBLIGATION** (M3): every evaluator body keeps the call contract whenever its
    recursive answer does. -/
theorem evalStep_sound : BodySound := by
  intro rec hrec c
  cases c with
  | whileLoop step ctx env stepName cells => exact EvalBody.whileLoop_sound rec hrec step ctx env stepName cells
  | aliasStepIsRuntime step target ctx visited => exact EvalBody.aliasStepIsRuntime_sound rec hrec step target ctx visited
  | aliasValue wired ctx env => exact EvalBody.aliasValue_sound rec hrec wired ctx env
  | resolveAliasChase followCarriers projectRuntime a ctx visited last => exact EvalBody.resolveAliasChase_sound rec hrec followCarriers projectRuntime a ctx visited last
  | resolveAliasStructure a ctx => exact EvalBody.resolveAliasStructure_sound rec hrec a ctx
  | aliasOriginBinding? a ctx => exact EvalBody.aliasOriginBinding?_sound rec hrec a ctx
  | resolveAliasTarget a ctx => exact EvalBody.resolveAliasTarget_sound rec hrec a ctx
  | resolveAliasValueTarget a ctx => exact EvalBody.resolveAliasValueTarget_sound rec hrec a ctx
  | lookupLexicalProperty a name ctx => exact EvalBody.lookupLexicalProperty_sound rec hrec a name ctx
  | lookupLexicalValueProperty a name ctx => exact EvalBody.lookupLexicalValueProperty_sound rec hrec a name ctx
  | lookupLexical a name ctx => exact EvalBody.lookupLexical_sound rec hrec a name ctx
  | needPlanNormalizeCallee callee ctx => exact EvalBody.needPlanNormalizeCallee_sound rec hrec callee ctx
  | resolveAlg e ctx => exact EvalBody.resolveAlg_sound rec hrec e ctx
  | projectNeedCallable address => exact EvalBody.projectNeedCallable_sound rec hrec address
  | projectNeedWrittenAt address source caller => exact EvalBody.projectNeedWrittenAt_sound rec hrec address source caller
  | linkCallable address => exact EvalBody.linkCallable_sound rec hrec address
  | projectParameterCallable x ctx => exact EvalBody.projectParameterCallable_sound rec hrec x ctx
  | projectNeedWritten source caller => exact EvalBody.projectNeedWritten_sound rec hrec source caller
  | projectNeedStructuralMember source ctx => exact EvalBody.projectNeedStructuralMember_sound rec hrec source ctx
  | resolveCalleeAlg f ctx => exact EvalBody.resolveCalleeAlg_sound rec hrec f ctx
  | expectPreparedSequenceBuiltinAlgorithmSuffixArg b descriptors args index => exact EvalBody.expectPreparedSequenceBuiltinAlgorithmSuffixArg_sound rec hrec b descriptors args index
  | resolveDotReceiver? e ctx => exact EvalBody.resolveDotReceiver?_sound rec hrec e ctx
  | resolveDotReceiver e ctx => exact EvalBody.resolveDotReceiver_sound rec hrec e ctx
  | algorithmIntrinsicRoute receiver ctx => exact EvalBody.algorithmIntrinsicRoute_sound rec hrec receiver ctx
  | demandNeedRecursive address => exact EvalBody.demandNeedRecursive_sound rec hrec address
  | evalSuppliedAt address e ctx env => exact EvalBody.evalSuppliedAt_sound rec hrec address e ctx env
  | linkValue address => exact EvalBody.linkValue_sound rec hrec address
  | algorithmOfValue val argsOpt ctx env => exact EvalBody.algorithmOfValue_sound rec hrec val argsOpt ctx env
  | capturedCallee callee => exact EvalBody.capturedCallee_sound rec hrec callee
  | referenceReceiverValue target targetAlg ctx env => exact EvalBody.referenceReceiverValue_sound rec hrec target targetAlg ctx env
  | algorithmCalleeOf receiver ctx env => exact EvalBody.algorithmCalleeOf_sound rec hrec receiver ctx env
  | evalSuppliedCallCounted origin callee cells ctx env calleeName => exact EvalBody.evalSuppliedCallCounted_sound rec hrec origin callee cells ctx env calleeName
  | evalNeedUserSupply callee cells ctx env => exact EvalBody.evalNeedUserSupply_sound rec hrec callee cells ctx env
  | evalNeedFamilySupply callee cells ctx env calleeName => exact EvalBody.evalNeedFamilySupply_sound rec hrec callee cells ctx env calleeName
  | invokeNeed arg => exact EvalBody.invokeNeed_sound rec hrec arg
  | argumentNeed arg ctx env => exact EvalBody.argumentNeed_sound rec hrec arg ctx env
  | runNeedStepSlots step ctx env cells stepName => exact EvalBody.runNeedStepSlots_sound rec hrec step ctx env cells stepName
  | runNeedWhileRound step ctx env cells stepName => exact EvalBody.runNeedWhileRound_sound rec hrec step ctx env cells stepName
  | evalAlgOutputCore a ctx env => exact EvalBody.evalAlgOutputCore_sound rec hrec a ctx env
  | evalAlgOutput a ctx env => exact EvalBody.evalAlgOutput_sound rec hrec a ctx env
  | evalProgramOutput a ctx env => exact EvalBody.evalProgramOutput_sound rec hrec a ctx env
  | evalAlgOutputSlots a ctx env => exact EvalBody.evalAlgOutputSlots_sound rec hrec a ctx env
  | formOutputRow ctx env e => exact EvalBody.formOutputRow_sound rec hrec ctx env e
  | whileVerdictSlots a ctx env => exact EvalBody.whileVerdictSlots_sound rec hrec a ctx env
  | evalSequenceCallbackCall callee item ctx env calleeName => exact EvalBody.evalSequenceCallbackCall_sound rec hrec callee item ctx env calleeName
  | evalSequenceCallbackCallCounted callee item ctx env calleeName => exact EvalBody.evalSequenceCallbackCallCounted_sound rec hrec callee item ctx env calleeName
  | evalAlgOutputPreparedCore a ctx env => exact EvalBody.evalAlgOutputPreparedCore_sound rec hrec a ctx env
  | evalOutputRowsPreparedCore rows rowCtx env => exact EvalBody.evalOutputRowsPreparedCore_sound rec hrec rows rowCtx env
  | evalCapturePreparedCore rows ctx env => exact EvalBody.evalCapturePreparedCore_sound rec hrec rows ctx env
  | evalCaptureCountedCore rows ctx env => exact EvalBody.evalCaptureCountedCore_sound rec hrec rows ctx env
  | evalCaptureValue rows ctx env => exact EvalBody.evalCaptureValue_sound rec hrec rows ctx env
  | evalAlgOutputCountedCore a ctx env => exact EvalBody.evalAlgOutputCountedCore_sound rec hrec a ctx env
  | evalAlgOutputCounted a ctx env => exact EvalBody.evalAlgOutputCounted_sound rec hrec a ctx env
  | evalZeroArgumentDemandOutputCounted a ctx env => exact EvalBody.evalZeroArgumentDemandOutputCounted_sound rec hrec a ctx env
  | evalZeroArgumentDemandOutput a ctx env => exact EvalBody.evalZeroArgumentDemandOutput_sound rec hrec a ctx env
  | evalArgumentValueCounted arg ctx env => exact EvalBody.evalArgumentValueCounted_sound rec hrec arg ctx env
  | evalArgumentValue arg ctx env => exact EvalBody.evalArgumentValue_sound rec hrec arg ctx env
  | evalZeroArgPropertyAccessCounted accessKind owner binding resolvedAlgorithm ctx env request => exact EvalBody.evalZeroArgPropertyAccessCounted_sound rec hrec accessKind owner binding resolvedAlgorithm ctx env request
  | evalZeroArgPropertyAccess accessKind owner binding resolvedAlgorithm ctx env => exact EvalBody.evalZeroArgPropertyAccess_sound rec hrec accessKind owner binding resolvedAlgorithm ctx env
  | evalConditionalCallbackCallCounted callee args ctx env calleeName => exact EvalBody.evalConditionalCallbackCallCounted_sound rec hrec callee args ctx env calleeName
  | evalUserCallbackCallCounted callee args ctx env => exact EvalBody.evalUserCallbackCallCounted_sound rec hrec callee args ctx env
  | evalResolvedCallbackCallCounted callee args ctx env calleeName => exact EvalBody.evalResolvedCallbackCallCounted_sound rec hrec callee args ctx env calleeName
  | evalResolvedCallbackCall callee args ctx env calleeName => exact EvalBody.evalResolvedCallbackCall_sound rec hrec callee args ctx env calleeName
  | evalSequenceReduceStepCounted callee element accumulator ctx env calleeName => exact EvalBody.evalSequenceReduceStepCounted_sound rec hrec callee element accumulator ctx env calleeName
  | demandSequenceBuiltinCallItemValue item ctx env => exact EvalBody.demandSequenceBuiltinCallItemValue_sound rec hrec item ctx env
  | bindSequenceBuiltinArguments b metadata args ctx env => exact EvalBody.bindSequenceBuiltinArguments_sound rec hrec b metadata args ctx env
  | evalReduceCounted collection stepAlg initial ctx env => exact EvalBody.evalReduceCounted_sound rec hrec collection stepAlg initial ctx env
  | evalFilterCounted items predicateAlg ctx env => exact EvalBody.evalFilterCounted_sound rec hrec items predicateAlg ctx env
  | evalMapCounted collection transformAlg ctx env => exact EvalBody.evalMapCounted_sound rec hrec collection transformAlg ctx env
  | applyBuiltinCountedSequence b metadata args ctx env => exact EvalBody.applyBuiltinCountedSequence_sound rec hrec b metadata args ctx env
  | applyBuiltinCounted b args ctx env => exact EvalBody.applyBuiltinCounted_sound rec hrec b args ctx env
  | applyBuiltin b args ctx env => exact EvalBody.applyBuiltin_sound rec hrec b args ctx env
  | applyBuiltinCountedResolved b args ctx env => exact EvalBody.applyBuiltinCountedResolved_sound rec hrec b args ctx env
  | evalExplicitSequenceValueItems a ctx env => exact EvalBody.evalExplicitSequenceValueItems_sound rec hrec a ctx env
  | evalExplicitSequenceValueRowSlots rows rowCtx env => exact EvalBody.evalExplicitSequenceValueRowSlots_sound rec hrec rows rowCtx env
  | evalExplicitSequenceValueExprSlots expr ctx env => exact EvalBody.evalExplicitSequenceValueExprSlots_sound rec hrec expr ctx env
  | evalUserCallCounted callee args ctx env => exact EvalBody.evalUserCallCounted_sound rec hrec callee args ctx env
  | evalConditionalCallCounted callee args ctx env calleeName => exact EvalBody.evalConditionalCallCounted_sound rec hrec callee args ctx env calleeName
  | evalResolvedCall callee args ctx env calleeName => exact EvalBody.evalResolvedCall_sound rec hrec callee args ctx env calleeName
  | evalResolvedCallCounted callee args ctx env calleeName origin => exact EvalBody.evalResolvedCallCounted_sound rec hrec callee args ctx env calleeName origin
  | evalCallCountedExpr f args ctx env => exact EvalBody.evalCallCountedExpr_sound rec hrec f args ctx env
  | callLexicalWithReceiverCounted name receiver fallback extraArgs ctx env => exact EvalBody.callLexicalWithReceiverCounted_sound rec hrec name receiver fallback extraArgs ctx env
  | rejectDotStringIntrinsicArguments argsOpt ctx env => exact EvalBody.rejectDotStringIntrinsicArguments_sound rec hrec argsOpt ctx env
  | evalDotStringReceiverValue target targetAlg ctx env => exact EvalBody.evalDotStringReceiverValue_sound rec hrec target targetAlg ctx env
  | evalDotCallCounted target name fallback argsOpt ctx env => exact EvalBody.evalDotCallCounted_sound rec hrec target name fallback argsOpt ctx env
  | rejectInvokeIntrinsicArguments argsOpt ctx env => exact EvalBody.rejectInvokeIntrinsicArguments_sound rec hrec argsOpt ctx env
  | invokeCallReferenceValue val => exact EvalBody.invokeCallReferenceValue_sound rec hrec val
  | argumentViewCells a => exact EvalBody.argumentViewCells_sound rec hrec a
  | evalArgumentViewBuiltin b a => exact EvalBody.evalArgumentViewBuiltin_sound rec hrec b a
  | evalSequenceSpreadOperandValue e ctx env => exact EvalBody.evalSequenceSpreadOperandValue_sound rec hrec e ctx env
  | evalSequenceSpreadCounted e ctx env => exact EvalBody.evalSequenceSpreadCounted_sound rec hrec e ctx env
  | evalSupplySpread e ctx env => exact EvalBody.evalSupplySpread_sound rec hrec e ctx env
  | evalListLiteralCounted elements ctx env => exact EvalBody.evalListLiteralCounted_sound rec hrec elements ctx env
  | evalSequenceConstructCounted e ctx env => exact EvalBody.evalSequenceConstructCounted_sound rec hrec e ctx env
  | evalUnaryCounted op operand ctx env => exact EvalBody.evalUnaryCounted_sound rec hrec op operand ctx env
  | evalBinaryCounted op a b ctx env => exact EvalBody.evalBinaryCounted_sound rec hrec op a b ctx env
  | evalComparisonCounted first links ctx env => exact EvalBody.evalComparisonCounted_sound rec hrec first links ctx env
  | evalComparisonLinksCounted previousExpr previous holds links ctx env => exact EvalBody.evalComparisonLinksCounted_sound rec hrec previousExpr previous holds links ctx env
  | evalCounted e ctx env => exact EvalBody.evalCounted_sound rec hrec e ctx env
  | evalUserCall callee args ctx env => exact EvalBody.evalUserCall_sound rec hrec callee args ctx env
  | evalConditionalCall callee args ctx env calleeName => exact EvalBody.evalConditionalCall_sound rec hrec callee args ctx env calleeName
  | evalCallExpr f args ctx env => exact EvalBody.evalCallExpr_sound rec hrec f args ctx env
  | evalDotCall target name fallback argsOpt ctx env => exact EvalBody.evalDotCall_sound rec hrec target name fallback argsOpt ctx env
  | eval e ctx env => exact EvalBody.eval_sound rec hrec e ctx env

end KatLang.AddressInvariant
