import KatLangArityLaws.CallReference

open KatLang KatLang.CallPlan

/-!
# META-S3-1: the callable projection of a call reference, `R.Algorithm` (October 2026)

`R.Algorithm` denotes the captured invocation's CALLEE as a callable, independently of the
invocation's original argument supply (CR-13..CR-16). The authoritative definitions are in
`lean/KatLang.lean`:

* `NeedPlan.calleeCell` — every plan's ONE canonical callee cell (CR-13), recorded in
  `NeedCell.callee`;
* `NeedLink.receiverCell` — a supplied `X.Algorithm` link's ONE receiver cell (CR-15), recorded in
  `NeedCell.receiver`;
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
  the recorded cell and changes nothing), its establishment is INERT (`calleeCell_inert`: every
  existing cell keeps its suspension, VALUE state, CALLABLE state and plan supply), and a
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

/-! ## L3 / CR-13 — the canonical callee cell -/

theorem setCallee_run (a c : Nat) (s : EvalState) :
    (NeedPlan.setCallee a c).runState s =
      (.ok (), { s with needs := s.needs.modify a (fun cell => { cell with callee := some c }) }) := rfl

/-- A recorded callee cell is read: nothing is supplied, allocated or written. -/
theorem calleeCell_recorded (a c : Nat) (s : EvalState) (cell : NeedCell)
    (hc : s.needs[a]? = some cell) (h : cell.callee = some c) :
    (NeedPlan.calleeCell a).runState s = (.ok c, s) := by
  simp only [NeedPlan.calleeCell, bind_run, get_run, hc, h]
  rfl

/-- The first observation supplies the plan's written callee in the captured caller context and
    records the cell. -/
theorem calleeCell_establishes (a : Nat) (s : EvalState) (cell : NeedCell) (shape : NeedPlan.CallShape)
    (hc : s.needs[a]? = some cell) (h : cell.callee = none)
    (hshape : NeedPlan.ofSuspension? cell.suspension = some shape) :
    (NeedPlan.calleeCell a).runState s =
      (match (supplyNeed shape.callee shape.caller shape.values).runState s with
       | (.ok c, t) => (.ok c, { t with needs := t.needs.modify a (fun cell => { cell with callee := some c }) })
       | (.error e, t) => (.error e, t)) := by
  simp only [NeedPlan.calleeCell, bind_run, get_run, hc, h, hshape]
  rcases (supplyNeed shape.callee shape.caller shape.values).runState s with ⟨o, t⟩
  cases o <;> rfl

/-- **CR-13, canonical identity (L3).** Whatever cell the first successful observation of plan `a`'s
    callee returns, observing it again from the resulting state returns the SAME cell and changes
    nothing: one canonical callee cell per plan, reused by CALLABLE projection, bare VALUE and fresh
    invocation alike. -/
theorem calleeCell_canonical (a c : Nat) (s t : EvalState)
    (h : (NeedPlan.calleeCell a).runState s = (.ok c, t)) :
    (NeedPlan.calleeCell a).runState t = (.ok c, t) := by
  cases hc : s.needs[a]? with
  | none =>
    simp only [NeedPlan.calleeCell, bind_run, get_run, hc] at h
    cases h
  | some cell =>
    cases hcal : cell.callee with
    | some c0 =>
      rw [calleeCell_recorded a c0 s cell hc hcal] at h
      cases h
      exact calleeCell_recorded a _ s cell hc hcal
    | none =>
      cases hshape : NeedPlan.ofSuspension? cell.suspension with
      | none =>
        simp only [NeedPlan.calleeCell, bind_run, get_run, hc, hcal, hshape] at h
        cases h
      | some shape =>
        rw [calleeCell_establishes a s cell shape hc hcal hshape] at h
        cases hsup : (supplyNeed shape.callee shape.caller shape.values).runState s with
        | mk o u =>
          rw [hsup] at h
          cases o with
          | error e => cases h
          | ok c1 =>
            cases h
            have hkeep := (supply_heap_core _ _ _ s _ u hsup).2 a cell hc
            apply calleeCell_recorded a c _ { cell with callee := some c }
            · simp [Array.getElem?_modify, hkeep]
            · rfl

/-- **CR-13, inert establishment.** Establishing (or reading) the callee cell evaluates, prepares,
    projects and demands nothing: every existing cell keeps its suspension, VALUE state, CALLABLE
    state and plan supply, whatever the outcome. -/
theorem calleeCell_inert (a : Nat) (s : EvalState) :
    HeapCore s.needs ((NeedPlan.calleeCell a).runState s).2.needs := by
  cases hc : s.needs[a]? with
  | none =>
    simp only [NeedPlan.calleeCell, bind_run, get_run, hc]
    exact HeapCore.refl _
  | some cell =>
    cases hcal : cell.callee with
    | some c0 =>
      rw [calleeCell_recorded a c0 s cell hc hcal]
      exact HeapCore.refl _
    | none =>
      cases hshape : NeedPlan.ofSuspension? cell.suspension with
      | none =>
        simp only [NeedPlan.calleeCell, bind_run, get_run, hc, hcal, hshape]
        exact HeapCore.refl _
      | some shape =>
        rw [calleeCell_establishes a s cell shape hc hcal hshape]
        cases hsup : (supplyNeed shape.callee shape.caller shape.values).runState s with
        | mk o u =>
          have hcore := supply_heap_core shape.callee shape.caller shape.values s
          cases o with
          | error e =>
            show HeapCore s.needs u.needs
            obtain ⟨r, hr⟩ := supply_shape shape.callee shape.caller shape.values s
            rcases hr with hr | ⟨hr, _⟩ <;> rw [hr] at hsup <;> cases hsup
          | ok c1 =>
            show HeapCore s.needs (u.needs.modify a _)
            exact (hcore c1 u hsup).1.trans (HeapCore.memo _ a _ (fun _ => ⟨rfl, rfl, rfl, rfl⟩))

/-- **P6, parameter callee transport.** A plan whose written callee is a PARAMETER bound to a
    supplied cell `p` has `p` itself as its callee cell — the parameter's existing cell (NEED-01),
    never a replacement: no cell is allocated, and only the memo of `a` is written. -/
theorem calleeCell_parameter_transport (a p : Nat) (name : Ident) (s : EvalState) (cell : NeedCell)
    (shape : NeedPlan.CallShape) (activation : Option ParameterActivation)
    (hc : s.needs[a]? = some cell) (h : cell.callee = none)
    (hshape : NeedPlan.ofSuspension? cell.suspension = some shape)
    (hcallee : shape.callee = .param name)
    (hact : (capturedParameterActivation? name shape.caller).runState s = (.ok activation, s))
    (hfind : lookupAssoc name (activation.map ParameterActivation.needs |>.getD shape.caller.needEnv) = some p) :
    (NeedPlan.calleeCell a).runState s =
      (.ok p, { s with needs := s.needs.modify a (fun cell => { cell with callee := some p }) }) := by
  rw [calleeCell_establishes a s cell shape hc h hshape, hcallee,
    KatLang.NeedControl.Allocation.supply_param_transports name shape.caller shape.values s activation p hact hfind]

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
      (match (supplyNeed receiver caller values).runState s with
       | (.ok r, t) => (.ok r, { t with needs := t.needs.modify a (fun cell => { cell with receiver := some r }) })
       | (.error e, t) => (.error e, t)) := by
  simp only [NeedLink.receiverCell, bind_run, get_run, hc, h, hsusp, hlink]
  rcases (supplyNeed receiver caller values).runState s with ⟨o, t⟩
  cases o <;> rfl

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
          cases hsup : (supplyNeed receiver caller values).runState s with
          | mk o u =>
            rw [hsup] at h
            cases o with
            | error e => cases h
            | ok r1 =>
              cases h
              have hkeep := (supply_heap_core _ _ _ s _ u hsup).2 a cell hc
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
          cases hsup : (supplyNeed receiver caller values).runState s with
          | mk o u =>
            cases o with
            | error e =>
              show HeapCore s.needs u.needs
              obtain ⟨r, hr⟩ := supply_shape receiver caller values s
              rcases hr with hr | ⟨hr, _⟩ <;> rw [hr] at hsup <;> cases hsup
            | ok r1 =>
              show HeapCore s.needs (u.needs.modify a _)
              exact (supply_heap_core _ _ _ s r1 u hsup).1.trans
                (HeapCore.memo _ a _ (fun _ => ⟨rfl, rfl, rfl, rfl⟩))
      | ready v =>
        simp only [NeedLink.receiverCell, bind_run, get_run, hc, hrec, hsusp]
        exact HeapCore.refl _
      | collector slice =>
        simp only [NeedLink.receiverCell, bind_run, get_run, hc, hrec, hsusp]
        exact HeapCore.refl _

/-! ## P5 / P7 — the link's two channels share one receiver and one callee cell -/

/-- The link's VALUE is the decoded callee cell's VALUE (CR-14 b). -/
theorem link_value_is_callee_value (demand : Nat → EvalM CountedResult) (a : Nat) :
    NeedLink.value demand a = (do demand (← NeedLink.decodeCallee demand a)) := rfl

/-- The link's CALLABLE is the decoded callee cell's CALLABLE (CR-14 a). -/
theorem link_callable_is_callee_callable (demand : Nat → EvalM CountedResult)
    (project : Nat → EvalM (Option Algorithm)) (a : Nat) :
    NeedLink.callable demand project a = (do project (← NeedLink.decodeCallee demand a)) := rfl

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
    (NeedLink.decodeCallee (NeedDemand.step ev route recur) a).runState s = (.ok c, s) := by
  simp only [NeedLink.decodeCallee, bind_run, receiverCell_recorded a r s link hl hrec,
    KatLang.NeedControl.Memo.completed_sticky ev route recur r s receiverCell _ hr hdone]
  simp only [decodeCallRef, pure_run]
  rw [calleeCell_recorded p c s planCell hp hcal]

/-- **P7, CALLABLE channel independence.** Once the receiver cell `r` is recorded, the link's
    CALLABLE depends on VALUE demand ONLY at `r`: any two demand functions that agree there give the
    same projection run — so the projection never demands the link's own VALUE nor the callee
    cell's VALUE (unless one of them IS the receiver cell). -/
theorem callable_value_only_at_receiver (d1 d2 : Nat → EvalM CountedResult)
    (project : Nat → EvalM (Option Algorithm)) (a r : Nat) (s : EvalState) (link : NeedCell)
    (hl : s.needs[a]? = some link) (hrec : link.receiver = some r)
    (hagree : ∀ t, (d1 r).runState t = (d2 r).runState t) :
    (NeedLink.callable d1 project a).runState s = (NeedLink.callable d2 project a).runState s := by
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
