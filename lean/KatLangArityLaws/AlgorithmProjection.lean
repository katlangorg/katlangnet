import KatLangArityLaws.CallReference

open KatLang KatLang.CallPlan

/-! R7 checkpoint: the recursive evaluator control is now the total `EvalBody`/`evalFuel` core.
The `partial`/source-only installation descriptions below record the original proof boundary;
`EvaluatorCore.production_unfolds` connects completed operations to those bodies. This does not
prove reachable link-address validity, completed CALLABLE stability or end-to-end projection
refinement. The local theorems below retain their stated premises.

FG-M1 (2026-10-23): completed CALLABLE stability and recorded-link preservation across intervening
production evaluation are now proved in `EvaluatorMemoLinks.lean` (`production_keeps_memo_links`,
`production_callable_reread`, `production_callee_reread`, `production_receiver_reread`): a
completed CALLABLE outcome, a recorded `callee` and a recorded `receiver` present at an operation's
ENTRY survive every production operation, so the local reread laws below (`calleeCell_recorded`,
`receiverCell_recorded`, `NeedControl.Projection.projected_sticky`) apply after it. That is
entry-state preservation of the stored numbers and outcomes only: it proves neither that a recorded
address is valid (FG-H1), nor any in-flight first-writer law for a record first made inside an
establishing operation's own callback, nor end-to-end projection refinement. -/

/-!
# META-S3-1: the callable projection of a call reference, `R.Algorithm` (October 2026)

`R.Algorithm` denotes the captured invocation's CALLEE as a callable, independently of the
invocation's original argument supply (CR-13..CR-16). The authoritative definitions are in
`lean/KatLang.lean`:

* `NeedPlan.calleeCell` — every plan's ONE canonical callee cell (CR-13), recorded in
  `NeedCell.callee`;
* `NeedLink.receiverCell` — a supplied `X.Algorithm` link's ONE receiver cell (CR-15), recorded in
  `NeedCell.receiver`;
* `NeedPlan.supplyCallee` / `NeedLink.supplyReceiver` — the suppliers of those two cells. Since the
  E-18 receiver-read correction (November 11 2026; META-S3-4 D-3) the callee link of a PLANNED
  `.Algorithm` invocation is marked `NeedInvocationRole.link`, and its receiver cell — for a
  non-parameter receiver — is ONE cell marked `NeedInvocationRole.receiver` over the link's own edge,
  whose VALUE is the ordinary invocation receiver read (§ D-3 below; the read itself is
  `PlanRouteBridge.receiver_cell_reads_invocation_receiver`). A supplied link, and every link over a
  parameter receiver, keeps the pre-correction law (`receiverCell_establishes_ordinary`);
* `NeedLink.decodeCallee` / `NeedLink.value` / `NeedLink.callable` — the link's two channels, both
  through the one receiver and the one callee cell;
* `projectParameterWith` — the TYPED parameter projection of L2 (a failure is never absence).

The `partial` evaluator installs them: `linkValue` = `NeedLink.value demandNeedRecursive`,
`linkCallable` = `NeedLink.callable demandNeedRecursive projectNeedCallable`,
`projectParameterCallable` = `projectParameterWith projectNeedCallable` (read by `resolveAlg`'s
`.param` arm, `resolveDotReceiver?`'s and `projectNeedStructuralMember`'s parameter heads), the
`"Algorithm"` arms of `evalDotCallCounted` (`algorithmOfValue`), the link arm of
`evalCallCountedExpr` (`algorithmCalleeOf`), and `evalSuppliedAt` / `projectNeedWrittenAt`, the
address-indexed VALUE and CALLABLE of a supplied cell. That installation is a SOURCE FACT of the
`partial` definitions (Lean keeps them opaque), pinned by executable guards in
`AlgorithmProjectionGuards.lean`.

Proved here, over the total definitions:

* L3 / CR-13 — the callee cell is CANONICAL (`calleeCell_canonical`: a second observation returns
  the recorded cell and changes nothing), its establishment AFTER ROUTE ESTABLISHMENT is INERT
  (`calleeCell_inert`: every existing cell keeps its suspension, VALUE state, CALLABLE state and
  plan supply; META-S3-4: establishing the ROUTE itself runs the route classifier, which may demand
  a runtime-projection receiver — `calleeCell_route_first` — and is not claimed inert), and a
  PARAMETER callee is that parameter's own cell, allocating
  nothing (`calleeCell_parameter_transport`, P6);
* CR-15 — the link's receiver cell is canonical and inert likewise (`receiverCell_canonical`,
  `receiverCell_inert`);
* P5 — both channels reach the callee cell through `decodeCallee` (`link_value_is_callee_value`,
  `link_callable_is_callee_callable`), and once the receiver is decoded every later decode — by
  either channel — reads the same callee cell without any receiver computation
  (`decoded_link_reuses_receiver`);
* P7 — the link's CALLABLE depends on VALUE demand ONLY at its receiver cell
  (`callable_value_only_at_receiver`): never at the link's own address, never at the callee cell;
* L2 — the typed parameter projection propagates a projection failure with its error and keeps
  successful absence as absence (`parameter_projection_failure_propagates`,
  `parameter_projection_absence`, `parameter_projection_identity`, `parameter_without_cell`).

NOT claimed here (source facts with executable guards, or C#-only): that the `partial` evaluator's
arms call these definitions; fresh invocation with the NEW supply and ordinary family dispatch (P8,
guards); that no result construction exports CALLABLE (P9: `Result` gains no constructor — a source
fact of this candidate — and guards); C# concurrency, the CALLABLE single flight, asynchronous
resolution, cancellation, run ownership and resource terminality (C#-only, `NeedCell`,
`Evaluator.ResolveAsync`, `CheckCallReferenceOwnership`).
-/

namespace KatLang.AlgorithmProjectionLaws

/-- The fields establishment never touches: everything except the two META-S3-1 memo records. -/
structure CoreKept (c d : NeedCell) : Prop where
  suspension : d.suspension = c.suspension
  state : d.state = c.state
  callable : d.callable = c.callable
  plan : d.plan = c.plan

theorem CoreKept.refl (c : NeedCell) : CoreKept c c := ⟨rfl, rfl, rfl, rfl⟩

/-- A heap step that keeps the core of every existing cell. -/
def HeapCore (h h' : Array NeedCell) : Prop :=
  ∀ (b : Nat) (c : NeedCell), h[b]? = some c → ∃ d, h'[b]? = some d ∧ CoreKept c d

theorem HeapCore.refl (h : Array NeedCell) : HeapCore h h :=
  fun _ c hc => ⟨c, hc, CoreKept.refl c⟩

theorem HeapCore.trans {h1 h2 h3 : Array NeedCell} (a : HeapCore h1 h2) (b : HeapCore h2 h3) :
    HeapCore h1 h3 := by
  intro x c hc
  obtain ⟨d, hd, k1⟩ := a x c hc
  obtain ⟨e, he, k2⟩ := b x d hd
  exact ⟨e, he, ⟨k2.suspension.trans k1.suspension, k2.state.trans k1.state,
    k2.callable.trans k1.callable, k2.plan.trans k1.plan⟩⟩

theorem HeapCore.push (h : Array NeedCell) (n : NeedCell) : HeapCore h (h.push n) := by
  intro x c hc
  refine ⟨c, ?_, CoreKept.refl c⟩
  have hlt : x < h.size := by
    rcases Nat.lt_or_ge x h.size with hl | hl
    · exact hl
    · rw [Array.getElem?_eq_none hl] at hc; cases hc
  rw [Array.getElem?_push]
  simp [Nat.ne_of_lt hlt, hc]

/-- Recording a callee or receiver memo keeps every cell's core. -/
theorem HeapCore.memo (h : Array NeedCell) (a : Nat) (f : NeedCell → NeedCell)
    (hf : ∀ c, CoreKept c (f c)) : HeapCore h (h.modify a f) := by
  intro x c hc
  by_cases hx : a = x
  · subst hx
    exact ⟨f c, by simp [Array.getElem?_modify, hc], hf c⟩
  · exact ⟨c, by simp [Array.getElem?_modify, hx, hc], CoreKept.refl c⟩

/-! ## Reading a parameter's activation and supplying a cell -/

/-- `capturedParameterActivation?` is a pure read of the state. -/
theorem activation_read (name : Ident) (ctx : EvalCtx) (s : EvalState) :
    ∃ activation, (capturedParameterActivation? name ctx).runState s = (.ok activation, s) := by
  unfold capturedParameterActivation?
  split
  · split
    · exact ⟨none, rfl⟩
    · dsimp only
      split
      · exact ⟨none, rfl⟩
      · rename_i id _
        exact ⟨s.lexicalActivations[id]?, rfl⟩
  · exact ⟨none, rfl⟩

/-- ONE supply: a transported parameter changes nothing; every other source pushes one cell. -/
theorem supply_shape (source : Expr) (ctx : EvalCtx) (env : ValEnv) (s : EvalState) :
    ∃ r, (supplyNeed source ctx env).runState s = (.ok r, s)
      ∨ ((supplyNeed source ctx env).runState s =
          (.ok s.needs.size, { s with needs := s.needs.push { suspension := .expression source ctx env } })
         ∧ r = s.needs.size) := by
  cases source with
  | param name =>
    obtain ⟨activation, hc⟩ := activation_read name ctx s
    cases hl : lookupAssoc name (activation.map ParameterActivation.needs |>.getD ctx.needEnv) with
    | some a =>
      exact ⟨a, Or.inl (KatLang.NeedControl.Allocation.supply_param_transports name ctx env s activation a hc hl)⟩
    | none =>
      exact ⟨s.needs.size, Or.inr ⟨KatLang.NeedControl.Allocation.supply_unbound_param name ctx env s activation hc hl, rfl⟩⟩
  | _ =>
    exact ⟨s.needs.size, Or.inr ⟨KatLang.NeedControl.Allocation.supply_nonparameter _ ctx env s (by intro n h; cases h), rfl⟩⟩

/-- A supply keeps the core of every existing cell, and every existing address. -/
theorem supply_heap_core (source : Expr) (ctx : EvalCtx) (env : ValEnv) (s : EvalState)
    (r : Nat) (t : EvalState) (h : (supplyNeed source ctx env).runState s = (.ok r, t)) :
    HeapCore s.needs t.needs ∧ (∀ (b : Nat) (c : NeedCell), s.needs[b]? = some c → t.needs[b]? = some c) := by
  obtain ⟨r', hr⟩ := supply_shape source ctx env s
  rcases hr with hr | ⟨hr, _⟩
  · rw [hr] at h; cases h
    exact ⟨HeapCore.refl _, fun _ _ hc => hc⟩
  · rw [hr] at h; cases h
    refine ⟨HeapCore.push _ _, ?_⟩
    intro b c hc
    have hlt : b < s.needs.size := by
      rcases Nat.lt_or_ge b s.needs.size with hl | hl
      · exact hl
      · rw [Array.getElem?_eq_none hl] at hc; cases hc
    show (s.needs.push _)[b]? = some c
    rw [Array.getElem?_push]
    simp [Nat.ne_of_lt hlt, hc]

/-! ## D-3 — the invocation roles of a planned `.Algorithm` invocation's callee read

The two suppliers of the E-18 receiver-read correction (November 11 2026): `NeedPlan.supplyCallee`
marks the `.Algorithm` route's fresh link cell, `NeedLink.supplyReceiver` gives that link ONE
receiver cell that keeps the invocation receiver evaluator. Both are the ONE supply plus an
`invocation`-field write on a cell they have just allocated: they never fail, keep the core of
every existing cell, and leave every existing cell where it is. -/

/-- A cell kept except for its `invocation` field keeps its core. -/
theorem CoreKept.invocation (c : NeedCell) (role : NeedInvocationRole) :
    CoreKept c { c with invocation := role } := ⟨rfl, rfl, rfl, rfl⟩

/-- The invocation-link mark `supplyCallee` writes (D-3), as a state function: on the `.Algorithm`
    route, for a callee that is a link edge; the identity otherwise. -/
def markLink (eff : NeedPlan.CallShape) (r : PlanRoute) (c : Nat) (s : EvalState) : EvalState :=
  if r == .algorithm && (linkEdge? eff.callee).isSome then withInvocation c .link s else s

theorem markLink_core (eff : NeedPlan.CallShape) (r : PlanRoute) (c : Nat) (s : EvalState) :
    HeapCore s.needs (markLink eff r c s).needs := by
  unfold markLink
  split
  · exact HeapCore.memo _ c _ (fun cell => CoreKept.invocation cell .link)
  · exact HeapCore.refl _

/-- Off the `.Algorithm` route nothing is marked. -/
theorem markLink_other (eff : NeedPlan.CallShape) (r : PlanRoute) (c : Nat) (s : EvalState)
    (hr : r ≠ .algorithm) : markLink eff r c s = s := by
  unfold markLink
  have hb : (r == PlanRoute.algorithm) = false := by cases r <;> first | rfl | exact absurd rfl hr
  simp [hb]

/-- A callee that is no link edge — a name, a parameter, a member path not spelled `Algorithm` —
    is never marked, whatever the route. -/
theorem markLink_not_link (eff : NeedPlan.CallShape) (r : PlanRoute) (c : Nat) (s : EvalState)
    (hl : linkEdge? eff.callee = none) : markLink eff r c s = s := by
  unfold markLink
  simp [hl]

/-- The callee supplier is the ONE supply followed by the link mark. -/
theorem supplyCallee_run (eff : NeedPlan.CallShape) (r : PlanRoute) (s : EvalState) :
    (NeedPlan.supplyCallee eff r).runState s =
      (match (supplyNeed eff.callee eff.caller eff.values).runState s with
       | (.ok c, t) => (.ok c, markLink eff r c t)
       | (.error e, t) => (.error e, t)) := by
  simp only [NeedPlan.supplyCallee, bind_run]
  rcases (supplyNeed eff.callee eff.caller eff.values).runState s with ⟨_ | c, t⟩
  · rfl
  · by_cases hb : (r == PlanRoute.algorithm && (linkEdge? eff.callee).isSome) = true
    · simp only [markLink, NeedPlan.markCalleeLink, hb, ↓reduceIte, setInvocation_run]
      rfl
    · simp only [markLink, NeedPlan.markCalleeLink, hb]
      rfl

/-- The callee supplier never fails and keeps the core of every existing cell. -/
theorem supplyCallee_heap_core (eff : NeedPlan.CallShape) (r : PlanRoute) (s : EvalState) :
    ∃ c t, (NeedPlan.supplyCallee eff r).runState s = (.ok c, t) ∧ HeapCore s.needs t.needs := by
  rw [supplyCallee_run]
  obtain ⟨c, hc⟩ := supply_shape eff.callee eff.caller eff.values s
  rcases hc with hc | ⟨hc, _⟩
  · rw [hc]
    exact ⟨c, _, rfl, markLink_core eff r c s⟩
  · rw [hc]
    exact ⟨s.needs.size, markLink eff r s.needs.size
        { s with needs := s.needs.push { suspension := .expression eff.callee eff.caller eff.values } }, rfl,
      (HeapCore.push s.needs _).trans (markLink_core eff r s.needs.size
        { s with needs := s.needs.push { suspension := .expression eff.callee eff.caller eff.values } })⟩

/-- A SUPPLIED link, and every link over a PARAMETER receiver, supplies its receiver through the
    ONE supplier — exactly the pre-correction law. -/
theorem supplyReceiver_ordinary (role : NeedInvocationRole) (source receiver : Expr) (caller : EvalCtx)
    (values : ValEnv) (h : NeedLink.keepsInvocationReceiver role receiver = false) :
    NeedLink.supplyReceiver role source receiver caller values = supplyNeed receiver caller values := by
  simp [NeedLink.supplyReceiver, h]

theorem keepsInvocationReceiver_supplied (receiver : Expr) :
    NeedLink.keepsInvocationReceiver .supplied receiver = false := by
  cases receiver <;> rfl

theorem keepsInvocationReceiver_param (role : NeedInvocationRole) (name : Ident) :
    NeedLink.keepsInvocationReceiver role (.param name) = false := rfl

/-- The retained receiver cell of a planned `.Algorithm` invocation (D-3) as its link — written
    `source` in the context `caller` / `values` — allocates it: the link's own edge, marked
    `NeedInvocationRole.receiver`, suspended, unprojected and without records. -/
def invocationReceiverCell (source : Expr) (caller : EvalCtx) (values : ValEnv) : NeedCell :=
  { suspension := .expression source caller values, invocation := .receiver }

/-- Marking the cell a push has just appended is pushing the marked cell. -/
theorem push_then_mark (h : Array NeedCell) (source : Expr) (caller : EvalCtx) (values : ValEnv) :
    (h.push { suspension := .expression source caller values }).modify h.size
      (fun cell => { cell with invocation := .receiver }) =
    h.push (invocationReceiverCell source caller values) := by
  apply Array.ext_getElem?
  intro i
  simp only [Array.getElem?_modify, Array.getElem?_push]
  by_cases hi : i = h.size
  · subst hi; simp [invocationReceiverCell]
  · have hi' : ¬ h.size = i := fun e => hi e.symm
    simp [hi, hi']

/-- **D-3, the retained invocation receiver cell.** The callee link of a planned `.Algorithm`
    invocation allocates exactly ONE cell for a non-parameter receiver: the link's own written edge
    in its caller context, marked `NeedInvocationRole.receiver`, suspended and unprojected
    (`invocationReceiverCell`). Nothing is evaluated. -/
theorem supplyReceiver_invocation (role : NeedInvocationRole) (source receiver : Expr) (caller : EvalCtx)
    (values : ValEnv) (s : EvalState) (h : NeedLink.keepsInvocationReceiver role receiver = true) :
    (NeedLink.supplyReceiver role source receiver caller values).runState s =
      (.ok s.needs.size,
        { s with needs := s.needs.push (invocationReceiverCell source caller values) }) := by
  simp only [NeedLink.supplyReceiver, h, ↓reduceIte]
  rw [← push_then_mark]
  rfl

/-- The receiver supplier never fails, keeps the core of every existing cell, and leaves every
    existing cell at its address. -/
theorem supplyReceiver_heap_core (role : NeedInvocationRole) (source receiver : Expr) (caller : EvalCtx)
    (values : ValEnv) (s : EvalState) :
    ∃ r t, (NeedLink.supplyReceiver role source receiver caller values).runState s = (.ok r, t) ∧
      HeapCore s.needs t.needs ∧
      (∀ (b : Nat) (c : NeedCell), s.needs[b]? = some c → t.needs[b]? = some c) := by
  cases hk : NeedLink.keepsInvocationReceiver role receiver with
  | false =>
    rw [supplyReceiver_ordinary role source receiver caller values hk]
    obtain ⟨r, hr⟩ := supply_shape receiver caller values s
    rcases hr with hr | ⟨hr, _⟩
    · exact ⟨r, s, hr, HeapCore.refl _, fun _ _ hc => hc⟩
    · exact ⟨_, _, hr, (supply_heap_core receiver caller values s _ _ hr).1,
        (supply_heap_core receiver caller values s _ _ hr).2⟩
  | true =>
    rw [supplyReceiver_invocation role source receiver caller values s hk]
    refine ⟨_, _, rfl, HeapCore.push _ _, ?_⟩
    intro b c hc
    have hlt : b < s.needs.size := by
      rcases Nat.lt_or_ge b s.needs.size with hl | hl
      · exact hl
      · rw [Array.getElem?_eq_none hl] at hc; cases hc
    show (s.needs.push _)[b]? = some c
    rw [Array.getElem?_push]
    simp [Nat.ne_of_lt hlt, hc]

/-! ## L3 / CR-13 — the canonical callee cell -/

theorem setCallee_run (a c : Nat) (s : EvalState) :
    (NeedPlan.setCallee a c).runState s =
      (.ok (), { s with needs := s.needs.modify a (fun cell => { cell with callee := some c }) }) := rfl

/-- A recorded callee cell is read: nothing is classified, supplied, allocated or written. -/
theorem calleeCell_recorded (classify : NeedPlan.CallShape → EvalM PlanRoute)
    (a c : Nat) (s : EvalState) (cell : NeedCell)
    (hc : s.needs[a]? = some cell) (h : cell.callee = some c) :
    (NeedPlan.calleeCell classify a).runState s = (.ok c, s) := by
  simp only [NeedPlan.calleeCell, bind_run, get_run, hc, h]
  rfl

/-- The first observation of an unrecorded callee (META-S3-4): the plan's route (recorded, or
    classified now — `NeedPlan.routeOf`), then — on a callable route — the route's callee
    (`NeedPlan.effective`) supplied in the captured caller context (`NeedPlan.supplyCallee`: the ONE
    supply, and on the `.Algorithm` route the link mark of D-3, `supplyCallee_run`) and recorded; an
    intrinsic route is the refusal. -/
theorem calleeCell_unrecorded (classify : NeedPlan.CallShape → EvalM PlanRoute)
    (a : Nat) (s : EvalState) (cell : NeedCell) (shape : NeedPlan.CallShape)
    (hc : s.needs[a]? = some cell) (h : cell.callee = none)
    (hshape : NeedPlan.ofSuspension? cell.suspension = some shape) :
    (NeedPlan.calleeCell classify a).runState s =
      (match (NeedPlan.routeOf classify a shape).runState s with
       | (.error e, t) => (.error e, t)
       | (.ok r, t) =>
         if r = .intrinsic then (.error NeedPlan.invocationRefusal, t) else
         match (NeedPlan.supplyCallee (NeedPlan.effective shape r) r).runState t with
         | (.ok c, u) => (.ok c, { u with needs := u.needs.modify a (fun cell => { cell with callee := some c }) })
         | (.error e, u) => (.error e, u)) := by
  simp only [NeedPlan.calleeCell, bind_run, get_run, hc, h, hshape]
  rcases (NeedPlan.routeOf classify a shape).runState s with ⟨_ | r, t⟩
  · rfl
  · by_cases hi : r = .intrinsic
    · subst hi; rfl
    · have hb : (r == PlanRoute.intrinsic) = false := by
        cases r <;> first | rfl | exact absurd rfl hi
      simp only [hb, Bool.false_eq_true, ↓reduceIte, ite_eq_right hi, bind_run]
      rcases (NeedPlan.supplyCallee (NeedPlan.effective shape r) r).runState t with ⟨_ | c, u⟩ <;> rfl

/-- The inert half of the first observation (META-S3-4): with the plan's route `r` recorded and
    callable, the first observation supplies the route's callee in the captured caller context and
    records the cell. -/
theorem calleeCell_establishes (classify : NeedPlan.CallShape → EvalM PlanRoute)
    (a : Nat) (s : EvalState) (cell : NeedCell) (shape : NeedPlan.CallShape) (r : PlanRoute)
    (hc : s.needs[a]? = some cell) (h : cell.callee = none)
    (hshape : NeedPlan.ofSuspension? cell.suspension = some shape) (hr : cell.route = some r)
    (hi : r ≠ .intrinsic) :
    (NeedPlan.calleeCell classify a).runState s =
      (match (NeedPlan.supplyCallee (NeedPlan.effective shape r) r).runState s with
       | (.ok c, t) => (.ok c, { t with needs := t.needs.modify a (fun cell => { cell with callee := some c }) })
       | (.error e, t) => (.error e, t)) := by
  rw [calleeCell_unrecorded classify a s cell shape hc h hshape,
    routeOf_recorded classify a shape s cell r hc hr]
  exact ite_eq_right hi

/-- D-1A: an intrinsic route has no callee cell — the refusal, with no effect. -/
theorem calleeCell_intrinsic (classify : NeedPlan.CallShape → EvalM PlanRoute)
    (a : Nat) (s : EvalState) (cell : NeedCell) (shape : NeedPlan.CallShape)
    (hc : s.needs[a]? = some cell) (h : cell.callee = none)
    (hshape : NeedPlan.ofSuspension? cell.suspension = some shape) (hr : cell.route = some .intrinsic) :
    (NeedPlan.calleeCell classify a).runState s = (.error NeedPlan.invocationRefusal, s) := by
  rw [calleeCell_unrecorded classify a s cell shape hc h hshape,
    routeOf_recorded classify a shape s cell .intrinsic hc hr]
  rfl

/-- **Route first (META-S3-4, D-4).** With neither the callee nor the route recorded, the first
    observation runs the route classifier FIRST — the only part that may evaluate (a
    runtime-projection receiver's demand) — and then exactly the inert establishment from the state
    where the route is recorded. -/
theorem calleeCell_route_first (classify : NeedPlan.CallShape → EvalM PlanRoute)
    (a : Nat) (s : EvalState) (cell : NeedCell) (shape : NeedPlan.CallShape)
    (hc : s.needs[a]? = some cell) (h : cell.callee = none)
    (hshape : NeedPlan.ofSuspension? cell.suspension = some shape) (hr : cell.route = none) :
    (NeedPlan.calleeCell classify a).runState s =
      (match (classify shape).runState s with
       | (.error e, t) => (.error e, t)
       | (.ok r, t) =>
         let (r, t) := recordRoute a r t
         if r = .intrinsic then (.error NeedPlan.invocationRefusal, t) else
         match (NeedPlan.supplyCallee (NeedPlan.effective shape r) r).runState t with
         | (.ok c, u) => (.ok c, { u with needs := u.needs.modify a (fun cell => { cell with callee := some c }) })
         | (.error e, u) => (.error e, u)) := by
  rw [calleeCell_unrecorded classify a s cell shape hc h hshape,
    routeOf_fresh classify a shape s cell hc hr]
  rcases (classify shape).runState s with ⟨_ | r, t⟩ <;> rfl

/-- **CR-13, canonical identity (L3).** Whatever cell the first successful observation of plan `a`'s
    callee returns, observing it again from the resulting state returns the SAME cell and changes
    nothing: one canonical callee cell per plan, reused by CALLABLE projection, bare VALUE and fresh
    invocation alike. (META-S3-4: the route classifier runs at most at the first observation; it is
    assumed disciplined — it keeps every existing cell — as `ProductionDiscipline` proves for the
    production classifier.) -/
theorem calleeCell_canonical (classify : NeedPlan.CallShape → EvalM PlanRoute)
    (hclassify : ∀ shape, Disciplined (classify shape))
    (a c : Nat) (s t : EvalState)
    (h : (NeedPlan.calleeCell classify a).runState s = (.ok c, t)) :
    (NeedPlan.calleeCell classify a).runState t = (.ok c, t) := by
  have hd := disciplined_calleeCell classify hclassify a s
  rw [h] at hd
  cases hc : s.needs[a]? with
  | none =>
    simp only [NeedPlan.calleeCell, bind_run, get_run, hc] at h
    cases h
  | some cell =>
    cases hcal : cell.callee with
    | some c0 =>
      rw [calleeCell_recorded classify a c0 s cell hc hcal] at h
      cases h
      exact calleeCell_recorded classify a _ s cell hc hcal
    | none =>
      -- Every successful first observation ends with the callee record of `a`.
      have hrec : ∃ d, t.needs[a]? = some d ∧ d.callee = some c := by
        cases hshape : NeedPlan.ofSuspension? cell.suspension with
        | none =>
          simp only [NeedPlan.calleeCell, bind_run, get_run, hc, hcal, hshape] at h
          cases h
        | some shape =>
          rw [calleeCell_unrecorded classify a s cell shape hc hcal hshape] at h
          have k1 := disciplined_routeOf classify hclassify a shape s
          generalize hro : (NeedPlan.routeOf classify a shape).runState s = ro at h k1
          rcases ro with ⟨_ | r, t1⟩
          · cases h
          · obtain ⟨c1, hc1, _⟩ := k1 a cell hc
            dsimp only at h
            by_cases hi : r = .intrinsic
            · rw [ite_eq_left hi] at h; cases h
            · rw [ite_eq_right hi] at h
              have k2 := disciplined_supplyCallee (NeedPlan.effective shape r) r t1
              generalize hsu : (NeedPlan.supplyCallee (NeedPlan.effective shape r) r).runState t1 = su at h k2
              rcases su with ⟨_ | c2, t2⟩
              · cases h
              · obtain ⟨c3, hc3, _⟩ := k2 a c1 hc1
                cases h
                exact ⟨{ c3 with callee := some c }, by simp [Array.getElem?_modify, hc3], rfl⟩
      obtain ⟨d, hd', hdc⟩ := hrec
      exact calleeCell_recorded classify a c t d hd' hdc

/-- **CR-13, inert establishment after route establishment.** With the plan's route recorded,
    establishing (or reading) the callee cell evaluates, prepares, projects and demands nothing:
    every existing cell keeps its suspension, VALUE state, CALLABLE state and plan supply, whatever
    the outcome. (Establishing the route itself is `calleeCell_route_first`.) -/
theorem calleeCell_inert (classify : NeedPlan.CallShape → EvalM PlanRoute) (a : Nat) (s : EvalState)
    (hroute : ∀ cell, s.needs[a]? = some cell → cell.callee = none → ∃ r, cell.route = some r) :
    HeapCore s.needs ((NeedPlan.calleeCell classify a).runState s).2.needs := by
  cases hc : s.needs[a]? with
  | none =>
    simp only [NeedPlan.calleeCell, bind_run, get_run, hc]
    exact HeapCore.refl _
  | some cell =>
    cases hcal : cell.callee with
    | some c0 =>
      rw [calleeCell_recorded classify a c0 s cell hc hcal]
      exact HeapCore.refl _
    | none =>
      cases hshape : NeedPlan.ofSuspension? cell.suspension with
      | none =>
        simp only [NeedPlan.calleeCell, bind_run, get_run, hc, hcal, hshape]
        exact HeapCore.refl _
      | some shape =>
        obtain ⟨r, hr⟩ := hroute cell hc hcal
        by_cases hi : r = .intrinsic
        · subst hi
          rw [calleeCell_intrinsic classify a s cell shape hc hcal hshape hr]
          exact HeapCore.refl _
        · rw [calleeCell_establishes classify a s cell shape r hc hcal hshape hr hi]
          obtain ⟨c1, u, hsup, hcore⟩ := supplyCallee_heap_core (NeedPlan.effective shape r) r s
          rw [hsup]
          show HeapCore s.needs (u.needs.modify a _)
          exact hcore.trans (HeapCore.memo _ a _ (fun _ => ⟨rfl, rfl, rfl, rfl⟩))

/-- **P6, parameter callee transport.** A plan whose route's callee is a PARAMETER bound to a
    supplied cell `p` has `p` itself as its callee cell — the parameter's existing cell (NEED-01),
    never a replacement: no cell is allocated, and only the memo of `a` is written. -/
theorem calleeCell_parameter_transport (classify : NeedPlan.CallShape → EvalM PlanRoute)
    (a p : Nat) (name : Ident) (s : EvalState) (cell : NeedCell)
    (shape : NeedPlan.CallShape) (r : PlanRoute) (activation : Option ParameterActivation)
    (hc : s.needs[a]? = some cell) (h : cell.callee = none)
    (hshape : NeedPlan.ofSuspension? cell.suspension = some shape) (hr : cell.route = some r)
    (hi : r ≠ .intrinsic)
    (hcallee : (NeedPlan.effective shape r).callee = .param name)
    (hact : (capturedParameterActivation? name shape.caller).runState s = (.ok activation, s))
    (hfind : lookupAssoc name (activation.map ParameterActivation.needs |>.getD shape.caller.needEnv) = some p) :
    (NeedPlan.calleeCell classify a).runState s =
      (.ok p, { s with needs := s.needs.modify a (fun cell => { cell with callee := some p }) }) := by
  rw [calleeCell_establishes classify a s cell shape r hc h hshape hr hi, supplyCallee_run,
    effective_caller, effective_values, hcallee,
    KatLang.NeedControl.Allocation.supply_param_transports name shape.caller shape.values s activation p hact hfind]
  dsimp only
  rw [markLink_not_link _ r p s (by rw [hcallee]; rfl)]

/-! ## CR-15 — the link's canonical receiver cell -/

theorem receiverCell_recorded (a r : Nat) (s : EvalState) (cell : NeedCell)
    (hc : s.needs[a]? = some cell) (h : cell.receiver = some r) :
    (NeedLink.receiverCell a).runState s = (.ok r, s) := by
  simp only [NeedLink.receiverCell, bind_run, get_run, hc, h]
  rfl

theorem receiverCell_establishes (a : Nat) (s : EvalState) (cell : NeedCell)
    (source receiver fallback : Expr) (caller : EvalCtx) (values : ValEnv)
    (hc : s.needs[a]? = some cell) (h : cell.receiver = none)
    (hsusp : cell.suspension = .expression source caller values)
    (hlink : linkEdge? source = some (receiver, fallback)) :
    (NeedLink.receiverCell a).runState s =
      (match (NeedLink.supplyReceiver cell.invocation source receiver caller values).runState s with
       | (.ok r, t) => (.ok r, { t with needs := t.needs.modify a (fun cell => { cell with receiver := some r }) })
       | (.error e, t) => (.error e, t)) := by
  simp only [NeedLink.receiverCell, bind_run, get_run, hc, h, hsusp, hlink]
  rcases (NeedLink.supplyReceiver cell.invocation source receiver caller values).runState s with ⟨o, t⟩
  cases o <;> rfl

/-- A SUPPLIED link's first receiver observation is the pre-correction law: the receiver supplied
    through the ONE supplier and recorded (`supplyReceiver_ordinary`). The same holds for every
    link over a PARAMETER receiver. -/
theorem receiverCell_establishes_ordinary (a : Nat) (s : EvalState) (cell : NeedCell)
    (source receiver fallback : Expr) (caller : EvalCtx) (values : ValEnv)
    (hc : s.needs[a]? = some cell) (h : cell.receiver = none)
    (hsusp : cell.suspension = .expression source caller values)
    (hlink : linkEdge? source = some (receiver, fallback))
    (hk : NeedLink.keepsInvocationReceiver cell.invocation receiver = false) :
    (NeedLink.receiverCell a).runState s =
      (match (supplyNeed receiver caller values).runState s with
       | (.ok r, t) => (.ok r, { t with needs := t.needs.modify a (fun cell => { cell with receiver := some r }) })
       | (.error e, t) => (.error e, t)) := by
  rw [receiverCell_establishes a s cell source receiver fallback caller values hc h hsusp hlink,
    supplyReceiver_ordinary _ source receiver caller values hk]

/-- **D-3, the planned `.Algorithm` invocation's receiver cell.** The first receiver observation
    of an invocation link over a non-parameter receiver allocates ONE cell — the link's own edge,
    marked `NeedInvocationRole.receiver` — records it, and evaluates nothing. -/
theorem receiverCell_establishes_invocation (a : Nat) (s : EvalState) (cell : NeedCell)
    (source receiver fallback : Expr) (caller : EvalCtx) (values : ValEnv)
    (hc : s.needs[a]? = some cell) (h : cell.receiver = none)
    (hsusp : cell.suspension = .expression source caller values)
    (hlink : linkEdge? source = some (receiver, fallback))
    (hk : NeedLink.keepsInvocationReceiver cell.invocation receiver = true) :
    (NeedLink.receiverCell a).runState s =
      (.ok s.needs.size,
        { s with needs := (s.needs.push (invocationReceiverCell source caller values)).modify a
                            (fun cell => { cell with receiver := some s.needs.size }) }) := by
  rw [receiverCell_establishes a s cell source receiver fallback caller values hc h hsusp hlink,
    supplyReceiver_invocation _ source receiver caller values s hk]

/-- **CR-15, one receiver per link.** The link's receiver cell, once established, is the cell every
    later channel reads, and reading it changes nothing. -/
theorem receiverCell_canonical (a r : Nat) (s t : EvalState)
    (h : (NeedLink.receiverCell a).runState s = (.ok r, t)) :
    (NeedLink.receiverCell a).runState t = (.ok r, t) := by
  cases hc : s.needs[a]? with
  | none =>
    simp only [NeedLink.receiverCell, bind_run, get_run, hc] at h
    cases h
  | some cell =>
    cases hrec : cell.receiver with
    | some r0 =>
      rw [receiverCell_recorded a r0 s cell hc hrec] at h
      cases h
      exact receiverCell_recorded a _ s cell hc hrec
    | none =>
      cases hsusp : cell.suspension with
      | expression source caller values =>
        cases hlink : linkEdge? source with
        | none =>
          simp only [NeedLink.receiverCell, bind_run, get_run, hc, hrec, hsusp, hlink] at h
          cases h
        | some pair =>
          obtain ⟨receiver, fallback⟩ := pair
          rw [receiverCell_establishes a s cell source receiver fallback caller values hc hrec hsusp hlink] at h
          obtain ⟨r1, u, hsup, _, hkeepAll⟩ :=
            supplyReceiver_heap_core cell.invocation source receiver caller values s
          rw [hsup] at h
          cases h
          have hkeep := hkeepAll a cell hc
          apply receiverCell_recorded a r _ { cell with receiver := some r }
          · simp [Array.getElem?_modify, hkeep]
          · rfl
      | ready v =>
        simp only [NeedLink.receiverCell, bind_run, get_run, hc, hrec, hsusp] at h
        cases h
      | collector slice =>
        simp only [NeedLink.receiverCell, bind_run, get_run, hc, hrec, hsusp] at h
        cases h

/-- **CR-15, inert establishment.** Establishing the receiver cell evaluates nothing: every
    existing cell keeps its suspension, VALUE state, CALLABLE state and plan supply. -/
theorem receiverCell_inert (a : Nat) (s : EvalState) :
    HeapCore s.needs ((NeedLink.receiverCell a).runState s).2.needs := by
  cases hc : s.needs[a]? with
  | none =>
    simp only [NeedLink.receiverCell, bind_run, get_run, hc]
    exact HeapCore.refl _
  | some cell =>
    cases hrec : cell.receiver with
    | some r0 =>
      rw [receiverCell_recorded a r0 s cell hc hrec]
      exact HeapCore.refl _
    | none =>
      cases hsusp : cell.suspension with
      | expression source caller values =>
        cases hlink : linkEdge? source with
        | none =>
          simp only [NeedLink.receiverCell, bind_run, get_run, hc, hrec, hsusp, hlink]
          exact HeapCore.refl _
        | some pair =>
          obtain ⟨receiver, fallback⟩ := pair
          rw [receiverCell_establishes a s cell source receiver fallback caller values hc hrec hsusp hlink]
          obtain ⟨r1, u, hsup, hcore, _⟩ :=
            supplyReceiver_heap_core cell.invocation source receiver caller values s
          rw [hsup]
          show HeapCore s.needs (u.needs.modify a _)
          exact hcore.trans (HeapCore.memo _ a _ (fun _ => ⟨rfl, rfl, rfl, rfl⟩))
      | ready v =>
        simp only [NeedLink.receiverCell, bind_run, get_run, hc, hrec, hsusp]
        exact HeapCore.refl _
      | collector slice =>
        simp only [NeedLink.receiverCell, bind_run, get_run, hc, hrec, hsusp]
        exact HeapCore.refl _

/-! ## P5 / P7 — the link's two channels share one receiver and one callee cell -/

/-- The link's VALUE is the decoded callee cell's VALUE (CR-14 b). -/
theorem link_value_is_callee_value (classify : NeedPlan.CallShape → EvalM PlanRoute)
    (demand : Nat → EvalM CountedResult) (a : Nat) :
    NeedLink.value classify demand a = (do demand (← NeedLink.decodeCallee classify demand a)) := rfl

/-- The link's CALLABLE is the decoded callee cell's CALLABLE (CR-14 a). -/
theorem link_callable_is_callee_callable (classify : NeedPlan.CallShape → EvalM PlanRoute)
    (demand : Nat → EvalM CountedResult)
    (project : Nat → EvalM (Option Algorithm)) (a : Nat) :
    NeedLink.callable classify demand project a = (do project (← NeedLink.decodeCallee classify demand a)) := rfl

/-- **P5, receiver sharing.** Once link `a`'s receiver cell `r` is recorded and its VALUE has
    completed with call reference `p`, whose callee cell `c` is recorded, decoding the link — by its
    VALUE or by its CALLABLE — reads `r`'s completed outcome and `c` and changes nothing: no
    receiver computation repeats, and both channels reach the SAME callee cell. -/
theorem decoded_link_reuses_receiver (ev : Expr → EvalCtx → ValEnv → EvalM CountedResult)
    (route : NeedPlan.Route) (recur : Nat → EvalM CountedResult)
    (a r p c n : Nat) (s : EvalState) (link receiverCell planCell : NeedCell)
    (hl : s.needs[a]? = some link) (hrec : link.receiver = some r)
    (hr : s.needs[r]? = some receiverCell)
    (hdone : receiverCell.state = .completed (.ok (.callRef p, n)))
    (hp : s.needs[p]? = some planCell) (hcal : planCell.callee = some c) :
    (NeedLink.decodeCallee route.classify (NeedDemand.step ev route recur) a).runState s = (.ok c, s) := by
  simp only [NeedLink.decodeCallee, bind_run, receiverCell_recorded a r s link hl hrec,
    KatLang.NeedControl.Memo.completed_sticky ev route recur r s receiverCell _ hr hdone]
  simp only [decodeCallRef, pure_run]
  rw [calleeCell_recorded route.classify p c s planCell hp hcal]

/-- **P7, CALLABLE channel independence.** Once the receiver cell `r` is recorded, the link's
    CALLABLE depends on VALUE demand ONLY at `r`: any two demand functions that agree there give the
    same projection run — so the projection never demands the link's own VALUE nor the callee
    cell's VALUE (unless one of them IS the receiver cell). -/
theorem callable_value_only_at_receiver (classify : NeedPlan.CallShape → EvalM PlanRoute)
    (d1 d2 : Nat → EvalM CountedResult)
    (project : Nat → EvalM (Option Algorithm)) (a r : Nat) (s : EvalState) (link : NeedCell)
    (hl : s.needs[a]? = some link) (hrec : link.receiver = some r)
    (hagree : ∀ t, (d1 r).runState t = (d2 r).runState t) :
    (NeedLink.callable classify d1 project a).runState s = (NeedLink.callable classify d2 project a).runState s := by
  simp only [NeedLink.callable, NeedLink.decodeCallee, bind_run, receiverCell_recorded a r s link hl hrec,
    hagree s]

/-! ## L2 — the typed parameter projection -/

/-- A parameter whose supplied cell's projection FAILS fails with that error and state, whatever its
    kind (`notAnAlgorithm` and `illegalInEval` included): a runtime failure is never absence. -/
theorem parameter_projection_failure_propagates (project : Nat → EvalM (Option Algorithm))
    (x : Ident) (ctx : EvalCtx) (s t : EvalState) (activation : Option ParameterActivation)
    (address : Nat) (e : Error)
    (hact : (capturedParameterActivation? x ctx).runState s = (.ok activation, s))
    (hfind : lookupAssoc x (activation.map ParameterActivation.needs |>.getD ctx.needEnv) = some address)
    (hfail : (project address).runState s = (.error e, t)) :
    (projectParameterWith project x ctx).runState s = (.error e, t) := by
  simp only [projectParameterWith, bind_run, hact, hfind, hfail]

/-- Successful ABSENCE of identity stays absence. -/
theorem parameter_projection_absence (project : Nat → EvalM (Option Algorithm))
    (x : Ident) (ctx : EvalCtx) (s t : EvalState) (activation : Option ParameterActivation)
    (address : Nat)
    (hact : (capturedParameterActivation? x ctx).runState s = (.ok activation, s))
    (hfind : lookupAssoc x (activation.map ParameterActivation.needs |>.getD ctx.needEnv) = some address)
    (hnone : (project address).runState s = (.ok none, t)) :
    (projectParameterWith project x ctx).runState s = (.ok none, t) := by
  simp only [projectParameterWith, bind_run, hact, hfind, hnone]

/-- An identity is passed through unchanged. -/
theorem parameter_projection_identity (project : Nat → EvalM (Option Algorithm))
    (x : Ident) (ctx : EvalCtx) (s t : EvalState) (activation : Option ParameterActivation)
    (address : Nat) (algorithm : Algorithm)
    (hact : (capturedParameterActivation? x ctx).runState s = (.ok activation, s))
    (hfind : lookupAssoc x (activation.map ParameterActivation.needs |>.getD ctx.needEnv) = some address)
    (hsome : (project address).runState s = (.ok (some algorithm), t)) :
    (projectParameterWith project x ctx).runState s = (.ok (some algorithm), t) := by
  simp only [projectParameterWith, bind_run, hact, hfind, hsome]

/-- A parameter with no supplied cell has no identity, and nothing is projected. -/
theorem parameter_without_cell (project : Nat → EvalM (Option Algorithm))
    (x : Ident) (ctx : EvalCtx) (s : EvalState) (activation : Option ParameterActivation)
    (hact : (capturedParameterActivation? x ctx).runState s = (.ok activation, s))
    (hfind : lookupAssoc x (activation.map ParameterActivation.needs |>.getD ctx.needEnv) = none) :
    (projectParameterWith project x ctx).runState s = (.ok none, s) := by
  simp only [projectParameterWith, bind_run, hact, hfind]
  rfl

end KatLang.AlgorithmProjectionLaws
