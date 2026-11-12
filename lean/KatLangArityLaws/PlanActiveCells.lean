import Lean
import KatLangArityLaws.EvaluatorDiscipline
import KatLangArityLaws.AlgorithmProjection

open KatLang KatLang.CallPlan KatLang.EvaluatorCore KatLang.AlgorithmProjectionLaws

/-!
# E-18: an `evaluating` cell stays `evaluating` across every production operation

Plan conservativity (`PlanConservativity.lean`, ledger E-18) compares two runs from the plan's
FLIGHT state, where the completion shell has marked the plan's cell `a` `evaluating`. Every
candidate invariant `P` of its two-run obligations (`BodyKeeps`, `BodyObliviousOn`) contains that
mark, `Active a` (`PlanConservativityAdmissible.lean`). This module discharges that component for
EVERY evaluator body, by the FG-M1 procedure of `EvaluatorMemoLinks.lean` (its framework and
per-body tactic, adapted to this relation) over the relation

* `ActKept c c'`: if `c` is `evaluating`, so is `c'`;
* `ActHeapKept h h'`: every cell of `h` is still present at its address in `h'`, `ActKept`;
* `ActDisc m`: `m` relates EVERY entry heap to its exit heap by `ActHeapKept` (successful and
  ordinary-error runs alike: `EvalM.runState` keeps the state of both).

`evalStep_actDisc` proves `ActDisc` for every one of the 104 `EvalCall` bodies given its recursive
answer; `evalFuel_actDisc` / `evalUnbounded_actDisc` transfer it through `invariant_transfer` /
`production_preserves`. The ONE writer of `NeedCell.state` is the completion shell
`NeedDemand.step`, and it writes only from an entry cell it read as `suspended` (an `evaluating`
entry cell is a `demandCycle` with no write): its `evaluating` mark and its final `completed` write
both target a cell that was NOT `evaluating` when the shell began (`actDisc_step`, entry-anchored
by `ActHeapKept.modify_anchor`). Every other write — plan record, route, callee, receiver,
invocation role, CALLABLE state, allocation — is a frame for the VALUE state.

THE CLAIM IS ENTRY-STATE PRESERVATION: a cell `evaluating` when an operation begins is
`evaluating` when it ends. It says nothing about cells marked during the operation, and nothing
about the C# runtime.
-/

namespace KatLang.ActiveCells

/-! ## The relation -/

/-- The one fact of a cell that must survive: an `evaluating` VALUE state. -/
structure ActKept (c c' : NeedCell) : Prop where
  active : c.state = .evaluating → c'.state = .evaluating

theorem ActKept.refl (c : NeedCell) : ActKept c c := ⟨fun h => h⟩

theorem ActKept.trans {c d e : NeedCell} (h1 : ActKept c d) (h2 : ActKept d e) : ActKept c e :=
  ⟨fun h => h2.active (h1.active h)⟩

/-- A write that leaves the VALUE state alone keeps it. -/
theorem actKept_of_same (c c' : NeedCell) (hs : c'.state = c.state) : ActKept c c' :=
  ⟨fun h => hs ▸ h⟩

/-- Any write over a cell that was not `evaluating` keeps the (vacuous) fact. -/
theorem actKept_of_not_active (c c' : NeedCell) (hs : c.state ≠ .evaluating) : ActKept c c' :=
  ⟨fun h => absurd h hs⟩

def ActHeapKept (h h' : Array NeedCell) : Prop :=
  ∀ (a : Nat) (c : NeedCell), h[a]? = some c → ∃ c', h'[a]? = some c' ∧ ActKept c c'

theorem ActHeapKept.refl (h : Array NeedCell) : ActHeapKept h h := fun _ c hc => ⟨c, hc, ActKept.refl c⟩

theorem ActHeapKept.trans {h1 h2 h3 : Array NeedCell} (k1 : ActHeapKept h1 h2) (k2 : ActHeapKept h2 h3) :
    ActHeapKept h1 h3 := by
  intro a c hc
  obtain ⟨d, hd, kd⟩ := k1 a c hc
  obtain ⟨e, he, ke⟩ := k2 a d hd
  exact ⟨e, he, kd.trans ke⟩

theorem lt_of_get {h : Array NeedCell} {a : Nat} {c : NeedCell} (hc : h[a]? = some c) : a < h.size := by
  rcases Nat.lt_or_ge a h.size with hl | hl
  · exact hl
  · rw [Array.getElem?_eq_none hl] at hc; cases hc

/-- Heap extension by allocation keeps every existing cell exactly. -/
theorem ActHeapKept.push (h : Array NeedCell) (c : NeedCell) : ActHeapKept h (h.push c) := by
  intro a d hd
  refine ⟨d, ?_, ActKept.refl d⟩
  rw [Array.getElem?_push]
  simp [Nat.ne_of_lt (lt_of_get hd), hd]

/-- A write at `a` whose result keeps the VALUE state fact of the cell it rewrites. -/
theorem ActHeapKept.modify (h : Array NeedCell) (a : Nat) (f : NeedCell → NeedCell)
    (hf : ∀ c, h[a]? = some c → ActKept c (f c)) : ActHeapKept h (h.modify a f) := by
  intro b c hc
  rw [modify_get]
  by_cases hab : a = b
  · subst hab
    exact ⟨f c, by simp [hc], hf c hc⟩
  · exact ⟨c, by simp [hab, hc], ActKept.refl c⟩

/-- **The entry-anchored write.** After `h0 ↦ h1` (kept), a write `g` at `a` keeps `h0`'s facts when
    it keeps, for the entry cell `c0` of `a`, the fact `c0` had. -/
theorem ActHeapKept.modify_anchor {h0 h1 : Array NeedCell} (k : ActHeapKept h0 h1) (a : Nat)
    (g : NeedCell → NeedCell)
    (hg : ∀ c0 c1, h0[a]? = some c0 → ActKept c0 c1 → ActKept c0 (g c1)) :
    ActHeapKept h0 (h1.modify a g) := by
  intro b c hc
  obtain ⟨c1, hc1, k1⟩ := k b c hc
  rw [modify_get]
  by_cases hab : a = b
  · subst hab
    exact ⟨g c1, by simp [hc1], hg c c1 hc k1⟩
  · exact ⟨c1, by simp [hab, hc1], k1⟩

/-- An off-target or same-field-preserving whole-cell write of the cell CURRENTLY at `a`. -/
theorem ActHeapKept.set_bang (h : Array NeedCell) (a : Nat) (c c' : NeedCell) (hc : h[a]? = some c)
    (hk : ActKept c c') : ActHeapKept h (h.set! a c') := by
  intro b d hd
  have ha := lt_of_get hc
  by_cases hab : a = b
  · subst hab
    rw [hc] at hd; cases hd
    exact ⟨c', by simp [Array.set!, ha], hk⟩
  · exact ⟨d, by simp [Array.set!, hab, hd], ActKept.refl d⟩

/-- `m` keeps every existing `evaluating` mark, over EVERY entry state, whatever its outcome
    (value or ordinary error; the state of both is `runState`'s). -/
def ActDisc {α : Type} (m : EvalM α) : Prop :=
  ∀ s, ActHeapKept s.needs (m.runState s).2.needs

theorem actDisc_of_needs {α : Type} (m : EvalM α)
    (h : ∀ s, (m.runState s).2.needs = s.needs) : ActDisc m := by
  intro s; rw [h s]; exact ActHeapKept.refl _

theorem ActDisc.bind {α β : Type} {m : EvalM α} {f : α → EvalM β}
    (hm : ActDisc m) (hf : ∀ x, ActDisc (f x)) : ActDisc (m >>= f) := by
  intro s
  rw [bind_run]
  have k := hm s
  cases hr : m.runState s with
  | mk out t =>
    rw [hr] at k
    cases out with
    | error e => exact k
    | ok x => exact k.trans (hf x t)

theorem ActDisc.map {α β : Type} {m : EvalM α} (f : α → β) (hm : ActDisc m) : ActDisc (f <$> m) := by
  intro s
  rw [map_run]
  have k := hm s
  cases hr : m.runState s with
  | mk out t => rw [hr] at k; cases out <;> exact k

theorem actDisc_pure {α : Type} (a : α) : ActDisc (pure a : EvalM α) := actDisc_of_needs _ (fun _ => rfl)
theorem actDisc_get : ActDisc (get : EvalM EvalState) := actDisc_of_needs _ (fun _ => rfl)
theorem actDisc_throw {α : Type} (e : Error) : ActDisc (throw e : EvalM α) := actDisc_of_needs _ (fun _ => rfl)
theorem actDisc_evalError {α : Type} (e : Error) : ActDisc (EvalM.error e : EvalM α) :=
  actDisc_of_needs _ (fun _ => rfl)
theorem actDisc_lift {α : Type} (o : Except Error α) : ActDisc (monadLift o : EvalM α) :=
  actDisc_of_needs _ (fun s => by rw [lift_run])

theorem ActDisc.attempt {α : Type} {m : EvalM α} (hm : ActDisc m) : ActDisc (evalAttempt m) := by
  intro s; rw [evalAttempt_run]; split <;> exact hm s

theorem ActDisc.withCtx {α : Type} {m : EvalM α} (c : String) (hm : ActDisc m) : ActDisc (withCtx c m) := by
  unfold KatLang.withCtx
  refine ActDisc.bind hm.attempt (fun r => ?_)
  cases r with
  | ok x => exact actDisc_pure x
  | error e => exact actDisc_evalError _

theorem ActDisc.withNestedMissingOutput {α : Type} {m : EvalM α} (hm : ActDisc m) :
    ActDisc (withNestedMissingOutput m) := by
  unfold KatLang.withNestedMissingOutput
  refine ActDisc.bind hm.attempt (fun r => ?_)
  cases r with
  | ok x => exact actDisc_pure x
  | error e => exact actDisc_evalError _

theorem ActDisc.captureMeta (name : Ident) {m : EvalM Nat} (hm : ActDisc m) :
    ActDisc (NeedBinder.captureMeta name m) := by
  intro s
  have k := hm s
  show ActHeapKept s.needs ((NeedBinder.captureMeta name m).runState s).2.needs
  rw [NeedBinder.captureMeta_runState]
  revert k
  rcases m.runState s with ⟨r, t⟩
  intro k
  cases r <;> exact k

theorem actDisc_allocate (suspension : NeedSuspension) : ActDisc (allocateNeed suspension) := by
  intro s; rw [KatLang.NeedControl.Allocation.allocate_run]; exact ActHeapKept.push _ _

theorem actDisc_supply (source : Expr) (caller : EvalCtx) (values : ValEnv) :
    ActDisc (supplyNeed source caller values) := by
  intro s
  rcases supply_cases source caller values s with h | h <;> rw [h]
  · exact ActHeapKept.refl _
  · exact ActHeapKept.push _ _

theorem actDisc_mapM {α β : Type} (f : α → EvalM β) (hf : ∀ x, ActDisc (f x)) (xs : List α) :
    ActDisc (xs.mapM f) := by
  suffices h : ∀ (acc : List β), ActDisc (List.mapM.loop f xs acc) from h []
  induction xs with
  | nil => intro acc; exact actDisc_pure _
  | cons x rest ih => intro acc; exact ActDisc.bind (hf x) (fun y => ih (y :: acc))

/-- A frame write: a state write that keeps every `evaluating` mark. -/
theorem act_modify (f : EvalState → EvalState) (h : ∀ s : EvalState, ActHeapKept s.needs (f s).needs) :
    ActDisc (modify f : EvalM Unit) := fun s => h s

/-! ## D-3: the invocation-role writes of a planned `.Algorithm` invocation's callee read

`NeedPlan.setInvocation` writes only the `invocation` field, never the VALUE state, so
the two suppliers of the E-18 receiver-read correction keep every entry fact. -/

theorem actDisc_setInvocation (c : Nat) (role : NeedInvocationRole) :
    ActDisc (NeedPlan.setInvocation c role) :=
  act_modify _ (fun s => ActHeapKept.modify _ c _ (fun _ _ => actKept_of_same _ _ rfl))

theorem actDisc_markCalleeLink (eff : NeedPlan.CallShape) (r : PlanRoute) (c : Nat) :
    ActDisc (NeedPlan.markCalleeLink eff r c) := by
  unfold NeedPlan.markCalleeLink
  split
  · exact actDisc_setInvocation c .link
  · exact actDisc_pure _

theorem actDisc_supplyCallee (eff : NeedPlan.CallShape) (r : PlanRoute) :
    ActDisc (NeedPlan.supplyCallee eff r) :=
  ActDisc.bind (actDisc_supply _ _ _) (fun c =>
    ActDisc.bind (actDisc_markCalleeLink eff r c) (fun _ => actDisc_pure _))

theorem actDisc_supplyReceiver (role : NeedInvocationRole) (source receiver : Expr) (caller : EvalCtx)
    (values : ValEnv) : ActDisc (NeedLink.supplyReceiver role source receiver caller values) := by
  unfold NeedLink.supplyReceiver
  split
  · exact ActDisc.bind (actDisc_allocate _) (fun r =>
      ActDisc.bind (actDisc_setInvocation r .receiver) (fun _ => actDisc_pure _))
  · exact actDisc_supply _ _ _

/-! ## Reads followed by writes (entry-anchored) -/

def ActAt {α : Type} (st : EvalState) (m : EvalM α) : Prop := ActHeapKept st.needs (m.runState st).2.needs

theorem act_get_bind {β : Type} (f : EvalState → EvalM β) (h : ∀ st, ActAt st (f st)) :
    ActDisc (get >>= f) := by
  intro s; rw [bind_run, get_run]; exact h s

theorem ActAt.of_disc {α : Type} {st : EvalState} {m : EvalM α} (h : ActDisc m) : ActAt st m := h st

theorem ActAt.bind {α β : Type} {st : EvalState} {m : EvalM α} {f : α → EvalM β}
    (hm : ActAt st m) (hf : ∀ x, ActDisc (f x)) : ActAt st (m >>= f) := by
  unfold ActAt at *
  rw [bind_run]
  cases hr : m.runState st with
  | mk out t =>
    rw [hr] at hm
    cases out with
    | error e => exact hm
    | ok x => exact hm.trans (hf x t)

theorem ActAt.set {st t : EvalState} (h : ActHeapKept st.needs t.needs) : ActAt st (set t : EvalM PUnit) := h

/-! ## Loops -/

theorem act_forIn'_loop {α β : Type} (as : List α) (f : (a : α) → a ∈ as → β → EvalM (ForInStep β))
    (hf : ∀ a h b, ActDisc (f a h b)) :
    ∀ (as' : List α) (b : β) (h : ∃ bs, bs ++ as' = as), ActDisc (List.forIn'.loop as f as' b h)
  | [], b, h => by unfold List.forIn'.loop; exact actDisc_pure _
  | a :: as', b, h => by
    unfold List.forIn'.loop
    apply ActDisc.bind (hf _ _ _)
    intro r
    cases r with
    | done b => exact actDisc_pure _
    | yield b => exact act_forIn'_loop as f hf as' b _

theorem act_forIn {α β : Type} (xs : List α) (init : β) (f : α → β → EvalM (ForInStep β))
    (h : ∀ a b, ActDisc (f a b)) : ActDisc (forIn xs init f) :=
  act_forIn'_loop xs (fun a _ b => f a b) (fun a _ b => h a b) xs init ⟨[], rfl⟩

theorem act_forM {α : Type} (xs : List α) (f : α → EvalM PUnit) (h : ∀ a, ActDisc (f a)) :
    ActDisc (xs.forM f) := by
  induction xs with
  | nil => exact actDisc_pure _
  | cons x xs ih => unfold List.forM; exact ActDisc.bind (h x) (fun _ => ih)

theorem act_foldlM {α β : Type} (f : β → α → EvalM β) (h : ∀ b a, ActDisc (f b a))
    (init : β) (xs : List α) : ActDisc (xs.foldlM f init) := by
  induction xs generalizing init with
  | nil => exact actDisc_pure _
  | cons x xs ih => unfold List.foldlM; exact ActDisc.bind (h _ _) (fun b => ih b)

/-! ## Supply formation, preparation, routes (frame writes) -/

theorem actDisc_slice (operand : Expr) (ctx : EvalCtx) : ActDisc (spreadCollectorSlice? operand ctx) :=
  actDisc_of_needs _ (fun s => by rw [spread_slice_readonly])

theorem actDisc_source (a : Nat) : ActDisc (needWrittenSource? a) :=
  actDisc_of_needs _ (fun s => by rw [KatLang.NeedControl.Provenance.source_run])

theorem actDisc_slot (ev : NeedSupply.SpreadEval) (hev : ∀ e c v, ActDisc (ev e c v))
    (ctx : EvalCtx) (env : ValEnv) (e : Expr) : ActDisc (NeedSupply.slot ev ctx env e) := by
  cases e with
  | sequenceSpread operand =>
    refine ActDisc.bind (actDisc_slice operand ctx) (fun known => ?_)
    cases known with
    | some slice =>
      exact actDisc_mapM _ (fun a => ActDisc.bind (actDisc_source a) (fun _ => actDisc_pure _)) slice
    | none =>
      refine ActDisc.bind (hev _ _ _) (fun supplied => ?_)
      cases supplied with
      | items values =>
        exact actDisc_mapM _ (fun v => ActDisc.bind (actDisc_allocate _) (fun _ => actDisc_pure _)) values
      | cells cells => exact actDisc_pure _
  | _ => exact ActDisc.bind (actDisc_supply _ _ _) (fun _ => actDisc_pure _)

theorem actDisc_form (ev : NeedSupply.SpreadEval) (hev : ∀ e c v, ActDisc (ev e c v))
    (ctx : EvalCtx) (env : ValEnv) (args : OutputBundle) : ActDisc (NeedSupply.form ev ctx env args) := by
  induction args with
  | nil => exact actDisc_pure _
  | cons e rest ih =>
    exact ActDisc.bind (actDisc_slot ev hev ctx env e) (fun _ => ActDisc.bind ih (fun _ => actDisc_pure _))

theorem act_frame (a : Nat) (g : NeedCell → NeedCell)
    (hg : ∀ c, (g c).state = c.state) :
    ActDisc (modify fun s => { s with needs := s.needs.modify a g } : EvalM Unit) :=
  act_modify _ (fun _ => ActHeapKept.modify _ a _ (fun c _ =>
    actKept_of_same _ _ (hg c)))

theorem actDisc_setSupply (a : Nat) (p : NeedPlanSupply) : ActDisc (NeedPlan.setSupply a p) :=
  act_frame a _ (fun _ => rfl)

theorem actDisc_setRoute (a : Nat) (r : PlanRoute) : ActDisc (NeedPlan.setRoute a r) :=
  act_frame a _ (fun _ => rfl)

/-- Preparation writes only the plan record: a frame over its formation. -/
theorem actDisc_prepare (ev : NeedSupply.SpreadEval) (hev : ∀ e c v, ActDisc (ev e c v))
    (a : Nat) (shape : NeedPlan.CallShape) : ActDisc (NeedPlan.prepare ev a shape) := by
  unfold NeedPlan.prepare
  refine ActDisc.bind actDisc_get (fun st => ?_)
  split
  · split
    · exact actDisc_lift _
    · exact actDisc_throw _
    · exact ActDisc.bind (actDisc_setSupply _ _) (fun _ =>
        ActDisc.bind (actDisc_form ev hev _ _ _).attempt (fun _ =>
          ActDisc.bind (actDisc_setSupply _ _) (fun _ => actDisc_lift _)))
  · exact actDisc_throw _

theorem actDisc_routeOf (classify : NeedPlan.CallShape → EvalM PlanRoute)
    (hclassify : ∀ shape, ActDisc (classify shape)) (a : Nat) (shape : NeedPlan.CallShape) :
    ActDisc (NeedPlan.routeOf classify a shape) := by
  unfold NeedPlan.routeOf
  refine ActDisc.bind actDisc_get (fun st => ?_)
  split
  · split
    · exact actDisc_pure _
    · exact ActDisc.bind (hclassify _) (fun r => ActDisc.bind actDisc_get (fun _ => by
        split
        · exact actDisc_pure _
        · exact ActDisc.bind (actDisc_setRoute _ _) (fun _ => actDisc_pure _)))
  · exact actDisc_throw _

/-! ## The three guarded writers of OTHER fields (frames for the VALUE state) -/

/-- **CALLABLE publication keeps every `evaluating` mark.** It writes only the CALLABLE state of
    `a`, over the callback's final state, whose marks the callback keeps. -/
theorem actDisc_projectionStep (project : NeedSuspension → EvalM (Option Algorithm))
    (hp : ∀ x, ActDisc (project x)) (a : Nat) : ActDisc (NeedProjection.step project a) := by
  intro s
  cases hc : s.needs[a]? with
  | none =>
    rw [KatLang.NeedControl.Projection.invalid_address project a s hc]; exact ActHeapKept.refl _
  | some cell =>
    cases hs : cell.callable with
    | projected o =>
      rw [KatLang.NeedControl.Projection.projected_sticky project a s cell o hc hs]
      exact ActHeapKept.refl _
    | projecting =>
      rw [KatLang.NeedControl.Projection.projecting_reentry_cycle project a s cell hc hs]
      exact ActHeapKept.refl _
    | unprojected =>
      -- the `projecting` mark: the entry cell had no completed outcome
      have k1 : ActHeapKept s.needs (KatLang.NeedControl.Projection.setCallable a .projecting s).needs :=
        ActHeapKept.modify _ a _ (fun c hc' => by
          rw [hc] at hc'; cases hc'
          exact ⟨fun h => h⟩)
      have k2 := hp cell.suspension (KatLang.NeedControl.Projection.setCallable a .projecting s)
      generalize hr : (project cell.suspension).runState
        (KatLang.NeedControl.Projection.setCallable a .projecting s) = r at k2
      rcases r with ⟨outcome, t⟩
      have k12 := k1.trans k2
      cases hinc : outcome.isIncomplete with
      | false =>
        rw [KatLang.NeedControl.Projection.unprojected_publishes project a s t cell outcome hc hs hr hinc]
        exact ActHeapKept.modify_anchor k12 a _ (fun c0 c1 h0 kk => by
          rw [hc] at h0; cases h0
          exact ⟨fun h => kk.active h⟩)
      | true =>
        have hrun : (NeedProjection.step project a).runState s = (.error .fuelExhausted, t) := by
          simp only [NeedProjection.step, bind_run, get_run, hc, hs, EvalM.modify_runState]
          simp only [KatLang.NeedControl.Projection.setCallable] at hr
          rw [evalAttempt_run, hr]
          simp only [hinc, ite_true]
        rw [hrun]; exact k12

/-- **Callee establishment keeps entry facts.** A recorded callee is returned with no write; an
    unrecorded one is established after the route and the one supply — the record overwrites at
    most a callee recorded DURING that work (an in-flight fact, not an entry fact). -/
theorem actDisc_calleeCell (classify : NeedPlan.CallShape → EvalM PlanRoute)
    (hclassify : ∀ shape, ActDisc (classify shape)) (a : Nat) :
    ActDisc (NeedPlan.calleeCell classify a) := by
  intro s
  cases hc : s.needs[a]? with
  | none =>
    have : (NeedPlan.calleeCell classify a).runState s = (.error (.illegalInEval "invalid need address"), s) := by
      simp only [NeedPlan.calleeCell, bind_run, get_run, hc]; rfl
    rw [this]; exact ActHeapKept.refl _
  | some cell =>
    cases hcal : cell.callee with
    | some x => rw [calleeCell_recorded classify a x s cell hc hcal]; exact ActHeapKept.refl _
    | none =>
      cases hshape : NeedPlan.ofSuspension? cell.suspension with
      | none =>
        have : (NeedPlan.calleeCell classify a).runState s = (.error NeedPlan.metaRefusal, s) := by
          simp only [NeedPlan.calleeCell, bind_run, get_run, hc, hcal, hshape]; rfl
        rw [this]; exact ActHeapKept.refl _
      | some shape =>
        rw [calleeCell_unrecorded classify a s cell shape hc hcal hshape]
        have k1 := actDisc_routeOf classify hclassify a shape s
        rcases hro : (NeedPlan.routeOf classify a shape).runState s with ⟨_ | r, t⟩ <;> rw [hro] at k1
        · exact k1
        · dsimp only
          split
          · exact k1
          · have k2 := actDisc_supplyCallee (NeedPlan.effective shape r) r t
            rcases hsu : (NeedPlan.supplyCallee (NeedPlan.effective shape r) r).runState t
              with ⟨_ | x, u⟩ <;> rw [hsu] at k2
            · exact k1.trans k2
            · exact ActHeapKept.modify_anchor (k1.trans k2) a _ (fun c0 c1 h0 kk => by
                rw [hc] at h0; cases h0
                exact ⟨fun h => kk.active h⟩)

/-- **Receiver establishment keeps entry facts**: the one supply between the read and the record. -/
theorem actDisc_receiverCell (a : Nat) : ActDisc (NeedLink.receiverCell a) := by
  intro s
  cases hc : s.needs[a]? with
  | none =>
    have : (NeedLink.receiverCell a).runState s = (.error (.illegalInEval "invalid need address"), s) := by
      simp only [NeedLink.receiverCell, bind_run, get_run, hc]; rfl
    rw [this]; exact ActHeapKept.refl _
  | some cell =>
    cases hrec : cell.receiver with
    | some x => rw [receiverCell_recorded a x s cell hc hrec]; exact ActHeapKept.refl _
    | none =>
      have hother : ∀ (e : Error), (NeedLink.receiverCell a).runState s = (.error e, s) →
          ActHeapKept s.needs ((NeedLink.receiverCell a).runState s).2.needs := by
        intro e h; rw [h]; exact ActHeapKept.refl _
      cases hsusp : cell.suspension with
      | expression source caller values =>
        cases hl : linkEdge? source with
        | none =>
          apply hother (.illegalInEval "not a link")
          simp only [NeedLink.receiverCell, bind_run, get_run, hc, hrec, hsusp, hl]; rfl
        | some p =>
          rcases p with ⟨receiver, fallback⟩
          rw [receiverCell_establishes a s cell source receiver fallback caller values hc hrec hsusp hl]
          have k := actDisc_supplyReceiver cell.invocation source receiver caller values s
          rcases hsu : (NeedLink.supplyReceiver cell.invocation source receiver caller values).runState s
            with ⟨_ | x, u⟩ <;> rw [hsu] at k
          · exact k
          · exact ActHeapKept.modify_anchor k a _ (fun c0 c1 h0 kk => by
              rw [hc] at h0; cases h0
              exact ⟨fun h => kk.active h⟩)
      | ready v =>
        apply hother (.illegalInEval "not a link")
        simp only [NeedLink.receiverCell, bind_run, get_run, hc, hrec, hsusp]; rfl
      | collector sl =>
        apply hother (.illegalInEval "not a link")
        simp only [NeedLink.receiverCell, bind_run, get_run, hc, hrec, hsusp]; rfl


/-! ## The shared link decoder and its two channels -/

/-- Both link channels preserve entry facts through the same decoder, provided its route
    classifier and receiver demand do. No contract on the returned addresses is needed here. -/
theorem actDisc_decodeCallee (classify : NeedPlan.CallShape → EvalM PlanRoute)
    (hclassify : ∀ shape, ActDisc (classify shape))
    (demand : Nat → EvalM CountedResult) (hdemand : ∀ a, ActDisc (demand a)) (a : Nat) :
    ActDisc (NeedLink.decodeCallee classify demand a) := by
  unfold NeedLink.decodeCallee
  refine ActDisc.bind (actDisc_receiverCell a) (fun receiver => ?_)
  refine ActDisc.bind (hdemand receiver) (fun value => ?_)
  refine ActDisc.bind ?_ (fun plan => actDisc_calleeCell classify hclassify plan)
  cases value.1 <;> first | exact actDisc_pure _ | exact actDisc_evalError _

/-- The VALUE link channel adds only the callee's VALUE demand to the shared decoder. -/
theorem actDisc_linkValue (classify : NeedPlan.CallShape → EvalM PlanRoute)
    (hclassify : ∀ shape, ActDisc (classify shape))
    (demand : Nat → EvalM CountedResult) (hdemand : ∀ a, ActDisc (demand a)) (a : Nat) :
    ActDisc (NeedLink.value classify demand a) :=
  ActDisc.bind (actDisc_decodeCallee classify hclassify demand hdemand a) hdemand

/-- The CALLABLE link channel adds only the callee's CALLABLE projection to the shared decoder. -/
theorem actDisc_linkCallable (classify : NeedPlan.CallShape → EvalM PlanRoute)
    (hclassify : ∀ shape, ActDisc (classify shape))
    (demand : Nat → EvalM CountedResult) (hdemand : ∀ a, ActDisc (demand a))
    (project : Nat → EvalM (Option Algorithm)) (hproject : ∀ a, ActDisc (project a)) (a : Nat) :
    ActDisc (NeedLink.callable classify demand project a) :=
  ActDisc.bind (actDisc_decodeCallee classify hclassify demand hdemand a) hproject

/-! ## Plan execution, the VALUE shell, META, invocation, capture and the argument view -/

theorem actDisc_calleeAlong (route : NeedPlan.Route)
    (htarget : ∀ f c, ActDisc (route.target f c))
    (hclassify : ∀ shape, ActDisc (route.classify shape))
    (hproject : ∀ c, ActDisc (route.project c))
    (a : Nat) (eff : NeedPlan.CallShape) (r : PlanRoute) :
    ActDisc (NeedPlan.calleeAlong route a eff r) := by
  cases r with
  | algorithm =>
    simp only [NeedPlan.calleeAlong]
    refine ActDisc.bind (actDisc_calleeCell route.classify hclassify a) (fun c => ?_)
    refine ActDisc.bind (hproject c) (fun o => ?_)
    cases o with
    | some _ => exact actDisc_pure _
    | none => exact actDisc_throw _
  | intrinsic => exact actDisc_throw _
  | call => exact htarget _ _
  | extension => exact htarget _ _

theorem actDisc_executeAlong (route : NeedPlan.Route)
    (hspread : ∀ e c v, ActDisc (route.spread e c v))
    (htarget : ∀ f c, ActDisc (route.target f c))
    (hnormal : ∀ g c, ActDisc (route.normalize g c))
    (hdispatch : ∀ o g cells c v n, ActDisc (route.dispatch o g cells c v n))
    (hclassify : ∀ shape, ActDisc (route.classify shape))
    (hproject : ∀ c, ActDisc (route.project c))
    (a : Nat) (shape : NeedPlan.CallShape) (r : PlanRoute) :
    ActDisc (NeedPlan.executeAlong route a shape r) := by
  unfold NeedPlan.executeAlong NeedPlan.dispatchName NeedPlan.dispatchOrigin
  exact ActDisc.bind (ActDisc.withCtx _ (actDisc_calleeAlong route htarget hclassify hproject a _ r)) (fun _ =>
    ActDisc.bind (ActDisc.bind actDisc_get (fun _ => actDisc_pure _)) (fun _ =>
    ActDisc.bind (ActDisc.bind actDisc_get (fun _ => actDisc_pure _)) (fun _ =>
    ActDisc.bind (ActDisc.withCtx _ (ActDisc.bind (hnormal _ _) (fun _ =>
      ActDisc.bind (actDisc_prepare route.spread hspread a _) (fun _ => hdispatch _ _ _ _ _ _))))
      (fun _ => actDisc_pure _))))

theorem actDisc_execute (route : NeedPlan.Route)
    (hspread : ∀ e c v, ActDisc (route.spread e c v))
    (htarget : ∀ f c, ActDisc (route.target f c))
    (hnormal : ∀ g c, ActDisc (route.normalize g c))
    (hdispatch : ∀ o g cells c v n, ActDisc (route.dispatch o g cells c v n))
    (hclassify : ∀ shape, ActDisc (route.classify shape))
    (hproject : ∀ c, ActDisc (route.project c))
    (a : Nat) (shape : NeedPlan.CallShape) :
    ActDisc (NeedPlan.execute route a shape) := by
  unfold NeedPlan.execute
  refine ActDisc.bind (ActDisc.withCtx _ (actDisc_routeOf route.classify hclassify a shape)) (fun r => ?_)
  cases r with
  | intrinsic => exact actDisc_throw _
  | _ => exact actDisc_executeAlong route hspread htarget hnormal hdispatch hclassify hproject a shape _

theorem actDisc_suspendedValue (ev : Expr → EvalCtx → ValEnv → EvalM CountedResult)
    (route : NeedPlan.Route) (demand : Nat → EvalM CountedResult)
    (hev : ∀ e c v, ActDisc (ev e c v))
    (hspread : ∀ e c v, ActDisc (route.spread e c v))
    (htarget : ∀ f c, ActDisc (route.target f c))
    (hnormal : ∀ g c, ActDisc (route.normalize g c))
    (hdispatch : ∀ o g cells c v n, ActDisc (route.dispatch o g cells c v n))
    (hclassify : ∀ shape, ActDisc (route.classify shape))
    (hproject : ∀ c, ActDisc (route.project c))
    (hdemand : ∀ b, ActDisc (demand b)) (a : Nat) (suspension : NeedSuspension) :
    ActDisc (NeedDemand.suspendedValue ev route demand a suspension) := by
  cases suspension with
  | ready value => exact actDisc_pure _
  | expression e c v =>
    simp only [NeedDemand.suspendedValue]
    split
    · refine ActDisc.bind (ActDisc.withCtx _ (actDisc_routeOf route.classify hclassify a _)) (fun r => ?_)
      cases r with
      | intrinsic => exact ActDisc.map _ (hev e c v)
      | _ => exact actDisc_executeAlong route hspread htarget hnormal hdispatch hclassify hproject a _ _
    · exact ActDisc.map _ (hev e c v)
  | collector slice =>
    exact ActDisc.withNestedMissingOutput
      (ActDisc.bind (actDisc_mapM _ (fun b => ActDisc.map _ (hdemand b)) slice)
        (fun _ => actDisc_pure _))

/-- The VALUE completion shell writes only the VALUE state: a frame over its computation. -/
theorem actDisc_step (ev : Expr → EvalCtx → ValEnv → EvalM CountedResult)
    (route : NeedPlan.Route) (demand : Nat → EvalM CountedResult)
    (hev : ∀ e c v, ActDisc (ev e c v))
    (hspread : ∀ e c v, ActDisc (route.spread e c v))
    (htarget : ∀ f c, ActDisc (route.target f c))
    (hnormal : ∀ g c, ActDisc (route.normalize g c))
    (hdispatch : ∀ o g cells c v n, ActDisc (route.dispatch o g cells c v n))
    (hclassify : ∀ shape, ActDisc (route.classify shape))
    (hproject : ∀ c, ActDisc (route.project c))
    (hdemand : ∀ b, ActDisc (demand b)) (a : Nat) :
    ActDisc (NeedDemand.step ev route demand a) := by
  unfold NeedDemand.step
  apply act_get_bind
  intro st
  split
  · rename_i cell hcell
    split
    · exact ActAt.of_disc (actDisc_lift _)
    · exact ActAt.of_disc (actDisc_throw _)
    · rename_i hsus
      -- both writes target the entry cell `cell`, which was `suspended`, never `evaluating`
      have hna : cell.state ≠ .evaluating := by rw [hsus]; intro h; cases h
      have hX := (actDisc_suspendedValue ev route demand hev hspread htarget hnormal hdispatch
          hclassify hproject hdemand a cell.suspension).attempt
      unfold ActAt
      simp only [bind_run, EvalM.modify_runState]
      have k1 : ActHeapKept st.needs (st.needs.modify a (fun cell => { cell with state := .evaluating })) :=
        ActHeapKept.modify _ a _ (fun c hc => by
          rw [hcell] at hc; cases hc; exact actKept_of_not_active _ _ hna)
      have k2 := hX { st with needs := st.needs.modify a (fun cell => { cell with state := .evaluating }) }
      generalize (evalAttempt (NeedDemand.suspendedValue ev route demand a cell.suspension)).runState
        { st with needs := st.needs.modify a (fun cell => { cell with state := .evaluating }) } = r at k2 ⊢
      rcases r with ⟨o, t⟩
      cases o with
      | error e => exact k1.trans k2
      | ok outcome =>
        dsimp only
        rw [lift_run]
        exact ActHeapKept.modify_anchor (k1.trans k2) a _ (fun c0 c1 h0 _ => by
          rw [hcell] at h0; cases h0; exact actKept_of_not_active _ _ hna)
  · exact ActAt.of_disc (actDisc_throw _)
theorem actDisc_reify (a : Nat) : ActDisc (NeedPlan.reify a) :=
  actDisc_of_needs _ (fun s => by rw [reify_inert])

theorem actDisc_invoke (route : NeedPlan.Route)
    (hspread : ∀ e c v, ActDisc (route.spread e c v))
    (htarget : ∀ f c, ActDisc (route.target f c))
    (hnormal : ∀ g c, ActDisc (route.normalize g c))
    (hdispatch : ∀ o g cells c v n, ActDisc (route.dispatch o g cells c v n))
    (hclassify : ∀ shape, ActDisc (route.classify shape))
    (hproject : ∀ c, ActDisc (route.project c))
    (r : NeedPlan.CallReference) : ActDisc (NeedPlan.invoke route r) := by
  unfold NeedPlan.invoke
  refine ActDisc.bind actDisc_get (fun st => ?_)
  split
  · exact actDisc_execute route hspread htarget hnormal hdispatch hclassify hproject _ _
  · exact actDisc_throw _

theorem actDisc_reference (a : Nat) : ActDisc (NeedPlan.reference a) := by
  intro s
  rw [KatLang.CallReferenceLaws.reference_run]
  cases NeedPlan.reifyResult s.needs a with
  | error e => exact ActHeapKept.refl _
  | ok r => exact ActHeapKept.push _ _

theorem actDisc_viewCells (sp : NeedSupply.SpreadEval) (hsp : ∀ e c v, ActDisc (sp e c v))
    (classify : NeedPlan.CallShape → EvalM PlanRoute) (hclassify : ∀ shape, ActDisc (classify shape))
    (a : Nat) : ActDisc (NeedPlan.viewCells sp classify a) := by
  unfold NeedPlan.viewCells
  refine ActDisc.bind actDisc_get (fun st => ?_)
  split
  · refine ActDisc.bind (actDisc_routeOf classify hclassify a _) (fun r => ?_)
    split
    · exact ActDisc.bind (actDisc_throw _) (fun _ => actDisc_prepare sp hsp a _)
    · exact actDisc_prepare sp hsp a _
  · exact actDisc_throw _

/-! ## The syntax-directed per-body procedure (the `EvaluatorDiscipline` procedure over `ActDisc`) -/

open Lean Meta Elab Tactic in
/-- Unfolds the head constant of the computation in a `ActDisc` goal (a total helper with
    no lemma of its own), so the syntax-directed procedure can continue inside it. -/
elab "act_unfold_head" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let ty ← instantiateMVars (← goal.getType)
    let_expr KatLang.ActiveCells.ActDisc _ m := ty | throwError "act_unfold_head: not a link-discipline goal"
    let m := m.headBeta
    let some c := m.getAppFn.constName? | throwError "act_unfold_head: no head constant"
    if c ∈ [``Bind.bind, ``Pure.pure, ``Functor.map, ``KatLang.evalAttempt, ``ForIn.forIn,
        ``MonadState.get, ``MonadStateOf.get, ``MonadState.set, ``MonadStateOf.set,
        ``MonadState.modifyGet, ``modify, ``get, ``set, ``List.forM, ``List.mapM, ``List.foldlM] then
      throwError "act_unfold_head: combinator"
    let g' ← Lean.Meta.unfoldTarget goal c
    let ty' ← instantiateMVars (← g'.getType)
    if (ty'.find? (fun e => e.isConstOf c)).isSome then
      throwError "act_unfold_head: recursive definition"
    replaceMainGoal [g']

open Lean Meta Elab Tactic in
/-- Closes `ActDisc (rec c)` from a hypothesis `∀ c, ActDisc (rec c)`. -/
elab "act_rec" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let ty ← instantiateMVars (← goal.getType)
    let_expr KatLang.ActiveCells.ActDisc _ m := ty | throwError "act_rec: not a link-discipline goal"
    let m := m.headBeta
    unless m.isApp && m.appFn!.isFVar do throwError "act_rec: not a recursive call"
    let f := m.appFn!
    for d in (← getLCtx) do
      unless d.isImplementationDetail do
        let t ← instantiateMVars d.type
        if t.isForall then
          let body := t.bindingBody!
          if let some (_, m') := body.app2? ``KatLang.ActiveCells.ActDisc then
            if m'.isApp && m'.appFn! == f && m'.appArg! == .bvar 0 then
              goal.assign (mkApp d.toExpr m.appArg!)
              return
    throwError "act_rec: no hypothesis"

open Lean Meta Elab Tactic in
/-- Closes a goal from a local hypothesis, instantiating its leading universal binders, at
    reducible transparency (cheap: never evaluates a computation). -/
elab "act_hyp" : tactic => do
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
  unless ok do throwError "act_hyp: no hypothesis"

open Lean Meta Elab Tactic in
/-- Zeta-reduces the top-level local definitions (`let`/`have`) of the computation in a
    `ActDisc`/`ActAt` goal, and nothing else. -/
elab "act_zeta" : tactic => do
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
    if n == 0 then throwError "act_zeta: no local definition"
    replaceMainGoal [← goal.replaceTargetDefEq (ty.updateApp! ty.appFn! m')]

open Lean Meta Elab Tactic in
/-- `intro` on a goal that is syntactically a binder (never unfolding a definition to find one). -/
elab "act_intro_syntactic" : tactic => do
  let goal ← getMainGoal
  unless (← instantiateMVars (← goal.getType)).isForall do throwError "act_intro_syntactic: no binder"
  let (_, g) ← goal.intro1
  replaceMainGoal [g]

open Lean Meta Elab Tactic in
/-- Closes an impossible branch: a hypothesis `∀ xs, a = b → False` whose equation holds by `rfl`
    for some instantiation. -/
elab "act_absurd" : tactic => do
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
  unless ok do throwError "act_absurd: no contradiction"

open Lean Meta Elab Tactic in
/-- Beta/projection/constructor-iota normal form (`whnfCore`, no definition unfolding) of the
    computation in a `ActDisc` goal. -/
elab "act_whnf_core" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let ty ← instantiateMVars (← goal.getType)
    let_expr KatLang.ActiveCells.ActDisc _ m := ty | throwError "act_whnf_core: not a link-discipline goal"
    let m' ← whnfCore m
    if m' == m then throwError "act_whnf_core: no progress"
    replaceMainGoal [← goal.replaceTargetDefEq (ty.updateApp! ty.appFn! m')]

/-- The evaluator helpers `rec.f args` are `rec (.f args)`. -/
macro "act_unfold_rec" : tactic => `(tactic| dsimp (config := { proj := false }) only [EvalRec.whileLoop, EvalRec.aliasStepIsRuntime, EvalRec.aliasValue, EvalRec.resolveAliasChase, EvalRec.resolveAliasTarget, EvalRec.resolveAliasValueTarget, EvalRec.lookupLexicalProperty, EvalRec.lookupLexicalValueProperty, EvalRec.lookupLexical, EvalRec.needPlanNormalizeCallee, EvalRec.resolveAlg, EvalRec.projectNeedCallable, EvalRec.projectNeedWrittenAt, EvalRec.linkCallable, EvalRec.projectParameterCallable, EvalRec.projectNeedWritten, EvalRec.projectNeedStructuralMember, EvalRec.resolveCalleeAlg, EvalRec.expectPreparedSequenceBuiltinAlgorithmSuffixArg, EvalRec.resolveDotReceiver?, EvalRec.resolveDotReceiver, EvalRec.algorithmIntrinsicRoute, EvalRec.demandNeedRecursive, EvalRec.evalSuppliedAt, EvalRec.linkValue, EvalRec.algorithmOfValue, EvalRec.capturedCallee, EvalRec.referenceReceiverValue, EvalRec.algorithmCalleeOf, EvalRec.evalSuppliedCallCounted, EvalRec.evalNeedUserSupply, EvalRec.evalNeedFamilySupply, EvalRec.invokeNeed, EvalRec.argumentNeed, EvalRec.runNeedStepSlots, EvalRec.runNeedWhileRound, EvalRec.evalAlgOutputCore, EvalRec.evalAlgOutput, EvalRec.evalProgramOutput, EvalRec.evalAlgOutputSlots, EvalRec.formOutputRow, EvalRec.whileVerdictSlots, EvalRec.evalSequenceCallbackCall, EvalRec.evalSequenceCallbackCallCounted, EvalRec.evalAlgOutputPreparedCore, EvalRec.evalOutputRowsPreparedCore, EvalRec.evalCapturePreparedCore, EvalRec.evalCaptureCountedCore, EvalRec.evalCaptureValue, EvalRec.evalAlgOutputCountedCore, EvalRec.evalAlgOutputCounted, EvalRec.evalZeroArgumentDemandOutputCounted, EvalRec.evalZeroArgumentDemandOutput, EvalRec.evalArgumentValueCounted, EvalRec.evalArgumentValue, EvalRec.evalZeroArgPropertyAccessCounted, EvalRec.evalZeroArgPropertyAccess, EvalRec.evalConditionalCallbackCallCounted, EvalRec.evalUserCallbackCallCounted, EvalRec.evalResolvedCallbackCallCounted, EvalRec.evalResolvedCallbackCall, EvalRec.evalSequenceReduceStepCounted, EvalRec.demandSequenceBuiltinCallItemValue, EvalRec.bindSequenceBuiltinArguments, EvalRec.evalReduceCounted, EvalRec.evalFilterCounted, EvalRec.evalMapCounted, EvalRec.applyBuiltinCountedSequence, EvalRec.applyBuiltinCounted, EvalRec.applyBuiltin, EvalRec.applyBuiltinCountedResolved, EvalRec.evalExplicitSequenceValueItems, EvalRec.evalExplicitSequenceValueRowSlots, EvalRec.evalExplicitSequenceValueExprSlots, EvalRec.evalUserCallCounted, EvalRec.evalConditionalCallCounted, EvalRec.evalResolvedCall, EvalRec.evalResolvedCallCounted, EvalRec.evalCallCountedExpr, EvalRec.callLexicalWithReceiverCounted, EvalRec.rejectDotStringIntrinsicArguments, EvalRec.evalDotStringReceiverValue, EvalRec.evalDotCallCounted, EvalRec.rejectInvokeIntrinsicArguments, EvalRec.invokeCallReferenceValue, EvalRec.argumentViewCells, EvalRec.evalArgumentViewBuiltin, EvalRec.evalSequenceSpreadOperandValue, EvalRec.evalSequenceSpreadCounted, EvalRec.evalSupplySpread, EvalRec.evalListLiteralCounted, EvalRec.evalSequenceConstructCounted, EvalRec.evalUnaryCounted, EvalRec.evalBinaryCounted, EvalRec.evalComparisonCounted, EvalRec.evalComparisonLinksCounted, EvalRec.evalCounted, EvalRec.evalUserCall, EvalRec.evalConditionalCall, EvalRec.evalCallExpr, EvalRec.evalDotCall, EvalRec.eval, EvalRec.planRoute,
  EvalRec.bindingChannels, NeedChannels.shell, NeedChannels.capabilities] at *)

set_option hygiene false in
/-- Syntax-directed `evaluating`-mark preservation (base: no recursive helper lemmas), given
    that `hrec` preserves the marks. -/
macro "act_tac_base" : tactic => `(tactic| without_info_trees ((try act_unfold_rec) <;> repeat' (first
  | act_rec
  | act_hyp
  | act_absurd
  | (with_reducible apply act_get_bind)
  | (with_reducible apply ActAt.bind)
  | (with_reducible apply ActAt.set; first
      | exact ActHeapKept.refl _
      | (apply ActHeapKept.set_bang <;> first | act_hyp | (exact actKept_of_same _ _ rfl)))
  | (with_reducible apply ActDisc.withCtx)
  | (with_reducible apply ActDisc.captureMeta)
  | (with_reducible apply ActDisc.attempt)
  | (with_reducible apply ActDisc.map)
  | (with_reducible apply ActDisc.bind)
  | (with_reducible apply actDisc_pure)
  | (with_reducible apply actDisc_get)
  | (with_reducible apply actDisc_throw)
  | (with_reducible apply actDisc_evalError)
  | (with_reducible apply actDisc_lift)
  | (with_reducible apply actDisc_allocate)
  | (with_reducible apply actDisc_supply)
  | (with_reducible apply actDisc_mapM)
  | (with_reducible apply actDisc_form)
  | (with_reducible apply actDisc_slot)
  | (with_reducible apply actDisc_prepare)
  | (with_reducible apply actDisc_routeOf)
  | (with_reducible apply actDisc_calleeCell)
  | (with_reducible apply actDisc_projectionStep)
  | (with_reducible apply actDisc_receiverCell)
  | (with_reducible apply actDisc_linkCallable)
  | (with_reducible apply actDisc_linkValue)
  | (with_reducible apply actDisc_decodeCallee)
  | (with_reducible apply actDisc_execute)
  | (with_reducible apply actDisc_step)
  | (with_reducible apply actDisc_reify)
  | (with_reducible apply actDisc_invoke)
  | (with_reducible apply actDisc_reference)
  | (with_reducible apply actDisc_viewCells)
  | (with_reducible apply act_modify; intro s; first
      | exact ActHeapKept.refl _
      | (apply ActHeapKept.modify; intro c _; exact actKept_of_same _ _ rfl))
  | (with_reducible apply act_forIn)
  | (with_reducible apply act_forM)
  | (with_reducible apply act_foldlM)
  | (with_reducible apply CapsAct.mk)

  | split
  | act_intro_syntactic
  | act_zeta
  | act_whnf_core
  | act_unfold_head
  | (with_reducible apply ActAt.of_disc))))

/-! ## Link discipline of the recursive total helpers -/

theorem act_formLeftToRight (form : Expr → EvalM (List Result)) (h : ∀ e, ActDisc (form e))
    (rows : List Expr) : ActDisc (OutputRows.formLeftToRight form rows) := by
  induction rows with
  | nil => unfold OutputRows.formLeftToRight; act_tac_base
  | cons e rest ih => unfold OutputRows.formLeftToRight; act_tac_base

theorem act_discover (form : Expr → EvalM (List Result)) (h : ∀ e, ActDisc (form e))
    (rows : List Expr) : ActDisc (WhileRound.discover form rows) := by
  induction rows with
  | nil => unfold WhileRound.discover; act_tac_base
  | cons e rest ih => unfold WhileRound.discover; act_tac_base

theorem act_selectWith {α : Type} (demand : α → EvalM Result) (h : ∀ a, ActDisc (demand a))
    (receiver : Result) (cells : List α) : ActDisc (selectWith demand receiver cells) := by
  induction cells with
  | nil => unfold selectWith; act_tac_base
  | cons c rest ih => unfold selectWith; act_tac_base

theorem act_selectViewWith {α : Type} (demand : α → EvalM Result) (hd : ∀ a, ActDisc (demand a))
    (cellsOf : EvalM (List NeedSupply.Sourced)) (hc : ActDisc cellsOf)
    (demandCell : Nat → EvalM Result) (hdc : ∀ a, ActDisc (demandCell a)) (selectors : List α) :
    ActDisc (selectViewWith demand cellsOf demandCell selectors) := by
  induction selectors with
  | nil => unfold selectViewWith; act_tac_base
  | cons c rest ih => unfold selectViewWith; act_tac_base

/-- Capabilities whose every field is mark-preserving. -/
structure CapsAct (caps : NeedCapabilities EvalM) : Prop where
  value : ∀ a, ActDisc (caps.value a)
  callable : ∀ a, ActDisc (caps.callable a)
  allocate : ∀ s, ActDisc (caps.allocate s)
  reference : ∀ a, ActDisc (caps.reference a)

/-- NEED-04's data-anchor check demands only through the VALUE capability. -/
theorem act_checkAnchor (caps : NeedCapabilities EvalM) (hc : CapsAct caps) (name : Ident)
    (anchor : CountedResult) (family : Bool) (cells : List Nat) :
    ActDisc (NeedBinder.checkAnchor caps name anchor family cells) := by
  have hv := hc.value
  induction cells with
  | nil => unfold NeedBinder.checkAnchor; act_tac_base
  | cons c rest ih => unfold NeedBinder.checkAnchor; act_tac_base

theorem act_binder (caps : NeedCapabilities EvalM) (hc : CapsAct caps) (repeated : List Ident)
    (family : Bool) :
    (∀ pattern address bound,
      ActDisc (NeedBinder.bindOne caps pattern address repeated bound family)) ∧
    (∀ patterns sources current,
      ActDisc (NeedBinder.bindSources caps patterns sources repeated current family)) := by
  have hv := hc.value; have hcl := hc.callable; have hal := hc.allocate; have hre := hc.reference
  have hck := act_checkAnchor caps hc
  refine NeedBinder.bindOne.mutual_induct
    (motive_1 := fun pattern address bound =>
      ActDisc (NeedBinder.bindOne caps pattern address repeated bound family))
    (motive_2 := fun patterns sources current =>
      ActDisc (NeedBinder.bindSources caps patterns sources repeated current family))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals intros
  all_goals first
    | (simp only [NeedBinder.bindOne]; act_tac_base)
    | (simp only [NeedBinder.bindSources]; act_tac_base)

theorem act_bindPatterns (caps : NeedCapabilities EvalM) (hc : CapsAct caps)
    (patterns : List NeedPattern) (cells : List Nat) (family : Bool) :
    ActDisc (NeedBinder.bindPatterns caps patterns cells family) := by
  unfold NeedBinder.bindPatterns NeedBinder.bindLevel NeedBinder.cardinalityGate
  have := (act_binder caps hc (needRepeatedNames patterns) family).2
  act_tac_base

theorem act_chooseBranch {β : Type} (caps : NeedCapabilities EvalM) (hc : CapsAct caps)
    (cells : List Nat) (calleeName : String) (activate : CondBranch → NeedEnv → EvalM β)
    (ha : ∀ b e, ActDisc (activate b e)) (branches : List CondBranch) :
    ActDisc (NeedBinder.chooseBranch caps cells calleeName activate branches) := by
  induction branches with
  | nil => unfold NeedBinder.chooseBranch; act_tac_base
  | cons b rest ih =>
    unfold NeedBinder.chooseBranch
    have := fun ps fam => act_bindPatterns caps hc ps cells fam
    act_tac_base

theorem act_selectFamily {β : Type} (caps : NeedCapabilities EvalM) (hc : CapsAct caps)
    (callee : Algorithm) (cells : List Nat) (calleeName : String)
    (activate : CondBranch → NeedEnv → EvalM β) (ha : ∀ b e, ActDisc (activate b e)) :
    ActDisc (NeedBinder.selectFamily caps callee cells calleeName activate) := by
  unfold NeedBinder.selectFamily
  have := act_chooseBranch caps hc cells calleeName activate ha
  act_tac_base


theorem act_collectSingleAtomicNumbers (b : Builtin) (index : Nat) (items : List Result) :
    ActDisc (collectSingleAtomicNumbers b index items) := by
  induction items generalizing index with
  | nil => unfold collectSingleAtomicNumbers; act_tac_base
  | cons i rest ih => unfold collectSingleAtomicNumbers; act_tac_base

theorem act_minLoop (numbers : List Int) (current : Int) :
    ActDisc (evalMinCounted.minLoop numbers current) := by
  induction numbers generalizing current with
  | nil => unfold evalMinCounted.minLoop; act_tac_base
  | cons n rest ih => unfold evalMinCounted.minLoop; act_tac_base

theorem act_maxLoop (numbers : List Int) (current : Int) :
    ActDisc (evalMaxCounted.maxLoop numbers current) := by
  induction numbers generalizing current with
  | nil => unfold evalMaxCounted.maxLoop; act_tac_base
  | cons n rest ih => unfold evalMaxCounted.maxLoop; act_tac_base

theorem act_openNavigateWith (structureOf : Algorithm → EvalM Algorithm)
    (h : ∀ a, ActDisc (structureOf a)) (ctx : EvalCtx) (notStatic : Error)
    (value : Algorithm) (receiverName : String) (steps : List Ident) :
    ActDisc (openNavigateWith structureOf ctx notStatic value receiverName steps) := by
  induction steps generalizing value receiverName with
  | nil => unfold openNavigateWith; act_tac_base
  | cons member rest ih => unfold openNavigateWith; act_tac_base

theorem act_openStructure (fuel : Nat) (ctx : EvalCtx) (a : Algorithm) :
    ActDisc (openStructure fuel ctx a) := by
  induction fuel generalizing a with
  | zero => simp only [openStructure]; act_tac_base
  | succ n ih =>
    have := act_openNavigateWith (fun value => openStructure n ctx value) ih
    simp only [openStructure]; act_tac_base

theorem act_resolveAlgForOpen (ctx : EvalCtx) (e : Expr) : ActDisc (resolveAlgForOpen e ctx) := by
  have := act_openStructure
  induction e using resolveAlgForOpen.induct ctx with
  | case7 o n a ih => unfold resolveAlgForOpen; act_tac_base
  | _ => unfold resolveAlgForOpen; act_tac_base

theorem act_lookupOpenProperties (a : Algorithm) (name : Ident) (ctx : EvalCtx) :
    ActDisc (lookupOpenProperties a name ctx) := by
  have := act_resolveAlgForOpen
  have := act_openStructure
  unfold lookupOpenProperties; act_tac_base

theorem act_lookupOpenPropertiesInParentChain (name : Ident) (ctx : EvalCtx) (sc : ScopeCtx) :
    ActDisc (lookupOpenPropertiesInParentChain sc name ctx) := by
  induction sc using lookupOpenPropertiesInParentChain.induct with
  | _ t ih =>
    have := act_lookupOpenProperties
    unfold lookupOpenPropertiesInParentChain
    cases t with
    | mk parent _ _ _ _ _ _ _ => cases parent <;> act_tac_base

theorem act_aliasStepNavigateWith (structureOf : Algorithm → EvalCtx → EvalM (Option Algorithm))
    (h : ∀ a c, ActDisc (structureOf a c)) (stepCtx : EvalCtx) (notStatic : Error)
    (value : Algorithm) (last : Option ResolvedProperty) (receiverName : String) (steps : List Ident) :
    ActDisc (aliasStepNavigateWith structureOf stepCtx notStatic value last receiverName steps) := by
  induction steps generalizing value last receiverName with
  | nil => unfold aliasStepNavigateWith; act_tac_base
  | cons member rest ih => unfold aliasStepNavigateWith; act_tac_base

theorem act_staticPathSelectWith (structureOf : Algorithm → EvalCtx → EvalM (Option Algorithm))
    (h : ∀ a c, ActDisc (structureOf a c)) (owner : Algorithm) (target : Expr) (stepCtx : EvalCtx) :
    ActDisc (staticPathSelectWith structureOf owner target stepCtx) := by
  have := act_aliasStepNavigateWith structureOf h
  have := act_lookupOpenProperties
  have := act_lookupOpenPropertiesInParentChain
  unfold staticPathSelectWith; act_tac_base

theorem act_resolveAliasStepWith (structureOf : Algorithm → EvalCtx → EvalM (Option Algorithm))
    (h : ∀ a c, ActDisc (structureOf a c)) (step : Algorithm) (target : Expr) (ctx : EvalCtx) :
    ActDisc (resolveAliasStepWith structureOf step target ctx) := by
  unfold resolveAliasStepWith; exact act_staticPathSelectWith structureOf h step target (ctx.push step)

theorem act_aliasRouteIsIntrinsicWith (structureOf : Algorithm → EvalCtx → EvalM (Option Algorithm))
    (h : ∀ a c, ActDisc (structureOf a c)) (receiver : Expr) (ctx : EvalCtx) :
    ActDisc (aliasRouteIsIntrinsicWith structureOf receiver ctx) := by
  have := act_aliasStepNavigateWith structureOf h
  have := act_lookupOpenProperties
  have := act_lookupOpenPropertiesInParentChain
  unfold aliasRouteIsIntrinsicWith; act_tac_base

section LocalLoops
variable (rec : EvalRec) (hrec : ∀ c, ActDisc (rec c))
include hrec

theorem act_outputRowsCollect (rowCtx : EvalCtx) (env : ValEnv) (rows : List Expr)
    (acc : List Result) (emitted : Nat) :
    ActDisc (EvalBody.evalOutputRowsPreparedCore.collect rec rowCtx env rows acc emitted) := by
  induction rows generalizing acc emitted with
  | nil => unfold EvalBody.evalOutputRowsPreparedCore.collect; act_tac_base
  | cons e rest ih => unfold EvalBody.evalOutputRowsPreparedCore.collect; act_tac_base

theorem act_explicitRowsCollect (rowCtx : EvalCtx) (env : ValEnv) (rows : List Expr) (acc : List Result) :
    ActDisc (EvalBody.evalExplicitSequenceValueRowSlots.collect rec rowCtx env rows acc) := by
  induction rows generalizing acc with
  | nil => unfold EvalBody.evalExplicitSequenceValueRowSlots.collect; act_tac_base
  | cons e rest ih => unfold EvalBody.evalExplicitSequenceValueRowSlots.collect; act_tac_base

theorem act_listLiteralCollect (ctx : EvalCtx) (env : ValEnv) (elements : List Expr) (acc : List Result) :
    ActDisc (EvalBody.evalListLiteralCounted.collect rec ctx env elements acc) := by
  induction elements generalizing acc with
  | nil => unfold EvalBody.evalListLiteralCounted.collect; act_tac_base
  | cons e rest ih => unfold EvalBody.evalListLiteralCounted.collect; act_tac_base

theorem act_sequenceConstructLoop (ctx : EvalCtx) (env : ValEnv) (leaves : List Expr) (items : List Result) :
    ActDisc (EvalBody.evalSequenceConstructCounted.loop rec ctx env leaves items) := by
  induction leaves generalizing items with
  | nil => unfold EvalBody.evalSequenceConstructCounted.loop; act_tac_base
  | cons e rest ih => unfold EvalBody.evalSequenceConstructCounted.loop; act_tac_base

theorem act_prepareControls (b : Builtin) (ctx : EvalCtx) (env : ValEnv)
    (descriptors : List SequenceBuiltinSuffixArgDescriptor) (items : List CallableCallItem) :
    ActDisc (EvalBody.bindSequenceBuiltinArguments.prepareControls rec b ctx env descriptors items) := by
  induction descriptors generalizing items with
  | nil => cases items <;> (unfold EvalBody.bindSequenceBuiltinArguments.prepareControls; act_tac_base)
  | cons d rest ih => cases items <;> (unfold EvalBody.bindSequenceBuiltinArguments.prepareControls; act_tac_base)

theorem act_reduceLoop (stepAlg : Algorithm) (ctx : EvalCtx) (env : ValEnv)
    (items : List CountedResult) (acc : CountedResult) :
    ActDisc (EvalBody.evalReduceCounted.reduceLoop rec stepAlg ctx env items acc) := by
  induction items generalizing acc with
  | nil => unfold EvalBody.evalReduceCounted.reduceLoop; act_tac_base
  | cons i rest ih => unfold EvalBody.evalReduceCounted.reduceLoop; act_tac_base

theorem act_filterLoop (predicateAlg : Algorithm) (ctx : EvalCtx) (env : ValEnv)
    (index : Nat) (items : List CountedResult) :
    ActDisc (EvalBody.evalFilterCounted.filterLoop rec predicateAlg ctx env index items) := by
  induction items generalizing index with
  | nil => unfold EvalBody.evalFilterCounted.filterLoop; act_tac_base
  | cons i rest ih => unfold EvalBody.evalFilterCounted.filterLoop; act_tac_base

theorem act_mapLoop (transformAlg : Algorithm) (ctx : EvalCtx) (env : ValEnv) (items : List CountedResult) :
    ActDisc (EvalBody.evalMapCounted.mapLoop rec transformAlg ctx env items) := by
  induction items with
  | nil => unfold EvalBody.evalMapCounted.mapLoop; act_tac_base
  | cons i rest ih => unfold EvalBody.evalMapCounted.mapLoop; act_tac_base

theorem act_repeatLoop (ctx : EvalCtx) (env : ValEnv) (step : ResolvedArgumentAlgorithm)
    (stepName : String) (remaining : Nat) (cells : List Nat) :
    ActDisc (EvalBody.applyBuiltinCounted.repeatLoop rec ctx env step stepName remaining cells) := by
  induction remaining generalizing cells with
  | zero => unfold EvalBody.applyBuiltinCounted.repeatLoop; act_tac_base
  | succ k ih => unfold EvalBody.applyBuiltinCounted.repeatLoop; act_tac_base

end LocalLoops

set_option hygiene false in
/-- Syntax-directed `evaluating`-mark preservation of an evaluator body, given that its
    recursive answer `hrec` preserves the marks. -/
macro "act_tac" : tactic => `(tactic| without_info_trees ((try act_unfold_rec) <;> repeat' (first
  | act_rec
  | act_hyp
  | act_absurd
  | (with_reducible apply act_get_bind)
  | (with_reducible apply ActAt.bind)
  | (with_reducible apply ActAt.set; first
      | exact ActHeapKept.refl _
      | (apply ActHeapKept.set_bang <;> first | act_hyp | (exact actKept_of_same _ _ rfl)))
  | (with_reducible apply ActDisc.withCtx)
  | (with_reducible apply ActDisc.captureMeta)
  | (with_reducible apply ActDisc.attempt)
  | (with_reducible apply ActDisc.map)
  | (with_reducible apply ActDisc.bind)
  | (with_reducible apply actDisc_pure)
  | (with_reducible apply actDisc_get)
  | (with_reducible apply actDisc_throw)
  | (with_reducible apply actDisc_evalError)
  | (with_reducible apply actDisc_lift)
  | (with_reducible apply actDisc_allocate)
  | (with_reducible apply actDisc_supply)
  | (with_reducible apply actDisc_mapM)
  | (with_reducible apply actDisc_form)
  | (with_reducible apply actDisc_slot)
  | (with_reducible apply actDisc_prepare)
  | (with_reducible apply actDisc_routeOf)
  | (with_reducible apply actDisc_calleeCell)
  | (with_reducible apply actDisc_projectionStep)
  | (with_reducible apply actDisc_receiverCell)
  | (with_reducible apply actDisc_linkCallable)
  | (with_reducible apply actDisc_linkValue)
  | (with_reducible apply actDisc_decodeCallee)
  | (with_reducible apply actDisc_execute)
  | (with_reducible apply actDisc_step)
  | (with_reducible apply actDisc_reify)
  | (with_reducible apply actDisc_invoke)
  | (with_reducible apply actDisc_reference)
  | (with_reducible apply actDisc_viewCells)
  | (with_reducible apply act_modify; intro s; first
      | exact ActHeapKept.refl _
      | (apply ActHeapKept.modify; intro c _; exact actKept_of_same _ _ rfl))
  | (with_reducible apply act_forIn)
  | (with_reducible apply act_forM)
  | (with_reducible apply act_foldlM)
  | (with_reducible apply act_formLeftToRight)
  | (with_reducible apply act_discover)
  | (with_reducible apply act_selectWith)
  | (with_reducible apply act_selectViewWith)
  | (with_reducible apply act_bindPatterns)
  | (with_reducible apply act_selectFamily)
  | (with_reducible apply act_collectSingleAtomicNumbers)
  | (with_reducible apply act_minLoop)
  | (with_reducible apply act_maxLoop)
  | (with_reducible apply act_resolveAlgForOpen)
  | (with_reducible apply act_openStructure)
  | (with_reducible apply act_resolveAliasStepWith)
  | (with_reducible apply act_staticPathSelectWith)
  | (with_reducible apply act_aliasRouteIsIntrinsicWith)
  | (with_reducible apply act_lookupOpenProperties)
  | (with_reducible apply act_lookupOpenPropertiesInParentChain)
  | (with_reducible apply EvalBody.terminalAccess_actDisc rec hrec)
  | (with_reducible apply EvalBody.staticReferenceTerminal_actDisc rec hrec)
  | (with_reducible apply EvalBody.transparentCollectorSlice_actDisc rec hrec)
  | (with_reducible apply EvalBody.transparentRetainedCell_actDisc rec hrec)
  | (with_reducible apply EvalBody.retainedSliceAt_actDisc rec hrec)
  | (with_reducible apply EvalBody.writtenCollectorSlice_actDisc rec hrec)
  | (with_reducible apply retainedCollectorBuiltin_actDisc rec hrec)
  | (with_reducible apply act_outputRowsCollect rec hrec)
  | (with_reducible apply act_explicitRowsCollect rec hrec)
  | (with_reducible apply act_listLiteralCollect rec hrec)
  | (with_reducible apply act_sequenceConstructLoop rec hrec)
  | (with_reducible apply act_prepareControls rec hrec)
  | (with_reducible apply act_reduceLoop rec hrec)
  | (with_reducible apply act_filterLoop rec hrec)
  | (with_reducible apply act_mapLoop rec hrec)
  | (with_reducible apply act_repeatLoop rec hrec)
  | (with_reducible apply CapsAct.mk)

  | split
  | act_intro_syntactic
  | act_zeta
  | act_whnf_core
  | act_unfold_head
  | (with_reducible apply ActAt.of_disc))))

theorem EvalBody.whileLoop_actDisc (rec : EvalRec) (hrec : ∀ c, ActDisc (rec c)) (step : ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) (stepName : String) (cells : List Nat) :
    ActDisc (EvalBody.whileLoop rec step ctx env stepName cells) := by
  unfold EvalBody.whileLoop; act_tac

theorem EvalBody.aliasStepIsRuntime_actDisc (rec : EvalRec) (hrec : ∀ c, ActDisc (rec c)) (step : Algorithm) (target : Expr) (ctx : EvalCtx) (visited : List String) :
    ActDisc (EvalBody.aliasStepIsRuntime rec step target ctx visited) := by
  unfold EvalBody.aliasStepIsRuntime; act_tac

theorem EvalBody.aliasValue_actDisc (rec : EvalRec) (hrec : ∀ c, ActDisc (rec c)) (wired : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    ActDisc (EvalBody.aliasValue rec wired ctx env) := by
  unfold EvalBody.aliasValue; act_tac

theorem EvalBody.resolveAliasChase_actDisc (rec : EvalRec) (hrec : ∀ c, ActDisc (rec c)) (followCarriers projectRuntime : Bool) (a : Algorithm) (ctx : EvalCtx) (visited : List String) (last : Option (Algorithm × PropDef)) :
    ActDisc (EvalBody.resolveAliasChase rec followCarriers projectRuntime a ctx visited last) := by
  unfold EvalBody.resolveAliasChase; act_tac

theorem EvalBody.resolveAliasStructure_actDisc (rec : EvalRec) (hrec : ∀ c, ActDisc (rec c)) (a : Algorithm) (ctx : EvalCtx) :
    ActDisc (EvalBody.resolveAliasStructure rec a ctx) := by
  unfold EvalBody.resolveAliasStructure; act_tac

theorem EvalBody.aliasOriginBinding?_actDisc (rec : EvalRec) (hrec : ∀ c, ActDisc (rec c)) (a : Algorithm) (ctx : EvalCtx) :
    ActDisc (EvalBody.aliasOriginBinding? rec a ctx) := by
  unfold EvalBody.aliasOriginBinding?; act_tac

theorem EvalBody.resolveAliasTarget_actDisc (rec : EvalRec) (hrec : ∀ c, ActDisc (rec c)) (a : Algorithm) (ctx : EvalCtx) :
    ActDisc (EvalBody.resolveAliasTarget rec a ctx) := by
  unfold EvalBody.resolveAliasTarget; act_tac

theorem EvalBody.resolveAliasValueTarget_actDisc (rec : EvalRec) (hrec : ∀ c, ActDisc (rec c)) (a : Algorithm) (ctx : EvalCtx) :
    ActDisc (EvalBody.resolveAliasValueTarget rec a ctx) := by
  unfold EvalBody.resolveAliasValueTarget; act_tac

theorem EvalBody.lookupLexicalProperty_actDisc (rec : EvalRec) (hrec : ∀ c, ActDisc (rec c)) (a : Algorithm) (name : Ident) (ctx : EvalCtx) :
    ActDisc (EvalBody.lookupLexicalProperty rec a name ctx) := by
  unfold EvalBody.lookupLexicalProperty; act_tac

theorem EvalBody.lookupLexicalValueProperty_actDisc (rec : EvalRec) (hrec : ∀ c, ActDisc (rec c)) (a : Algorithm) (name : Ident) (ctx : EvalCtx) :
    ActDisc (EvalBody.lookupLexicalValueProperty rec a name ctx) := by
  unfold EvalBody.lookupLexicalValueProperty; act_tac

theorem EvalBody.lookupLexical_actDisc (rec : EvalRec) (hrec : ∀ c, ActDisc (rec c)) (a : Algorithm) (name : Ident) (ctx : EvalCtx) :
    ActDisc (EvalBody.lookupLexical rec a name ctx) := by
  unfold EvalBody.lookupLexical; act_tac

theorem EvalBody.needPlanNormalizeCallee_actDisc (rec : EvalRec) (hrec : ∀ c, ActDisc (rec c)) (callee : Algorithm) (ctx : EvalCtx) :
    ActDisc (EvalBody.needPlanNormalizeCallee rec callee ctx) := by
  unfold EvalBody.needPlanNormalizeCallee; act_tac

theorem EvalBody.resolveAlg_actDisc (rec : EvalRec) (hrec : ∀ c, ActDisc (rec c)) (e : Expr) (ctx : EvalCtx) :
    ActDisc (EvalBody.resolveAlg rec e ctx) := by
  unfold EvalBody.resolveAlg; act_tac

theorem EvalBody.projectNeedCallable_actDisc (rec : EvalRec) (hrec : ∀ c, ActDisc (rec c)) (address : Nat) :
    ActDisc (EvalBody.projectNeedCallable rec address) := by
  unfold EvalBody.projectNeedCallable; act_tac

theorem EvalBody.projectNeedWrittenAt_actDisc (rec : EvalRec) (hrec : ∀ c, ActDisc (rec c)) (address : Nat) (source : Expr) (caller : EvalCtx) :
    ActDisc (EvalBody.projectNeedWrittenAt rec address source caller) := by
  unfold EvalBody.projectNeedWrittenAt; act_tac

theorem EvalBody.linkCallable_actDisc (rec : EvalRec) (hrec : ∀ c, ActDisc (rec c)) (address : Nat) :
    ActDisc (EvalBody.linkCallable rec address) := by
  unfold EvalBody.linkCallable; act_tac

theorem EvalBody.projectParameterCallable_actDisc (rec : EvalRec) (hrec : ∀ c, ActDisc (rec c)) (x : Ident) (ctx : EvalCtx) :
    ActDisc (EvalBody.projectParameterCallable rec x ctx) := by
  unfold EvalBody.projectParameterCallable; act_tac

theorem EvalBody.projectNeedWritten_actDisc (rec : EvalRec) (hrec : ∀ c, ActDisc (rec c)) (source : Expr) (caller : EvalCtx) :
    ActDisc (EvalBody.projectNeedWritten rec source caller) := by
  unfold EvalBody.projectNeedWritten; act_tac

theorem EvalBody.projectNeedStructuralMember_actDisc (rec : EvalRec) (hrec : ∀ c, ActDisc (rec c)) (source : Expr) (ctx : EvalCtx) :
    ActDisc (EvalBody.projectNeedStructuralMember rec source ctx) := by
  unfold EvalBody.projectNeedStructuralMember; act_tac

theorem EvalBody.resolveCalleeAlg_actDisc (rec : EvalRec) (hrec : ∀ c, ActDisc (rec c)) (f : Expr) (ctx : EvalCtx) :
    ActDisc (EvalBody.resolveCalleeAlg rec f ctx) := by
  unfold EvalBody.resolveCalleeAlg; act_tac

theorem EvalBody.expectPreparedSequenceBuiltinAlgorithmSuffixArg_actDisc (rec : EvalRec) (hrec : ∀ c, ActDisc (rec c)) (b : Builtin) (descriptors : List SequenceBuiltinSuffixArgDescriptor) (args : List PreparedSequenceBuiltinSuffixArg) (index : Nat) :
    ActDisc (EvalBody.expectPreparedSequenceBuiltinAlgorithmSuffixArg rec b descriptors args index) := by
  unfold EvalBody.expectPreparedSequenceBuiltinAlgorithmSuffixArg; act_tac

theorem EvalBody.resolveDotReceiver?_actDisc (rec : EvalRec) (hrec : ∀ c, ActDisc (rec c)) (e : Expr) (ctx : EvalCtx) :
    ActDisc (EvalBody.resolveDotReceiver? rec e ctx) := by
  unfold EvalBody.resolveDotReceiver?; act_tac

theorem EvalBody.resolveDotReceiver_actDisc (rec : EvalRec) (hrec : ∀ c, ActDisc (rec c)) (e : Expr) (ctx : EvalCtx) :
    ActDisc (EvalBody.resolveDotReceiver rec e ctx) := by
  unfold EvalBody.resolveDotReceiver; act_tac

theorem EvalBody.algorithmIntrinsicRoute_actDisc (rec : EvalRec) (hrec : ∀ c, ActDisc (rec c)) (receiver : Expr) (ctx : EvalCtx) :
    ActDisc (EvalBody.algorithmIntrinsicRoute rec receiver ctx) := by
  unfold EvalBody.algorithmIntrinsicRoute; act_tac

theorem EvalBody.demandNeedRecursive_actDisc (rec : EvalRec) (hrec : ∀ c, ActDisc (rec c)) (address : Nat) :
    ActDisc (EvalBody.demandNeedRecursive rec address) := by
  unfold EvalBody.demandNeedRecursive; act_tac

theorem EvalBody.evalSuppliedAt_actDisc (rec : EvalRec) (hrec : ∀ c, ActDisc (rec c)) (address : Nat) (e : Expr) (ctx : EvalCtx) (env : ValEnv) :
    ActDisc (EvalBody.evalSuppliedAt rec address e ctx env) := by
  unfold EvalBody.evalSuppliedAt; act_tac

theorem EvalBody.linkValue_actDisc (rec : EvalRec) (hrec : ∀ c, ActDisc (rec c)) (address : Nat) :
    ActDisc (EvalBody.linkValue rec address) := by
  unfold EvalBody.linkValue; act_tac

theorem EvalBody.algorithmOfValue_actDisc (rec : EvalRec) (hrec : ∀ c, ActDisc (rec c)) (val : Result) (argsOpt : Option OutputBundle) (ctx : EvalCtx) (env : ValEnv) :
    ActDisc (EvalBody.algorithmOfValue rec val argsOpt ctx env) := by
  unfold EvalBody.algorithmOfValue; act_tac

theorem EvalBody.capturedCallee_actDisc (rec : EvalRec) (hrec : ∀ c, ActDisc (rec c)) (callee : Nat) :
    ActDisc (EvalBody.capturedCallee rec callee) := by
  unfold EvalBody.capturedCallee; act_tac

theorem EvalBody.referenceReceiverValue_actDisc (rec : EvalRec) (hrec : ∀ c, ActDisc (rec c)) (target : Expr) (targetAlg : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    ActDisc (EvalBody.referenceReceiverValue rec target targetAlg ctx env) := by
  unfold EvalBody.referenceReceiverValue; act_tac

theorem EvalBody.algorithmCalleeOf_actDisc (rec : EvalRec) (hrec : ∀ c, ActDisc (rec c)) (receiver : Expr) (ctx : EvalCtx) (env : ValEnv) :
    ActDisc (EvalBody.algorithmCalleeOf rec receiver ctx env) := by
  unfold EvalBody.algorithmCalleeOf; act_tac

/-- D-3 (E-18 receiver-read correction): the planned `.Algorithm` invocation's callee read — the
    production route's `project` — keeps every `evaluating` mark. -/
theorem EvalBody.plannedLinkCallable_actDisc (rec : EvalRec) (hrec : ∀ c, ActDisc (rec c)) (link : Nat) :
    ActDisc (EvalBody.plannedLinkCallable rec link) := by
  unfold EvalBody.plannedLinkCallable; act_tac

theorem EvalBody.evalSuppliedCallCounted_actDisc (rec : EvalRec) (hrec : ∀ c, ActDisc (rec c)) (origin : CalleeOrigin) (callee : Algorithm) (cells : List NeedSupply.Sourced) (ctx : EvalCtx) (env : ValEnv) (calleeName : String) :
    ActDisc (EvalBody.evalSuppliedCallCounted rec origin callee cells ctx env calleeName) := by
  unfold EvalBody.evalSuppliedCallCounted; act_tac

theorem EvalBody.evalNeedUserSupply_actDisc (rec : EvalRec) (hrec : ∀ c, ActDisc (rec c)) (callee : Algorithm) (cells : List Nat) (ctx : EvalCtx) (env : ValEnv) :
    ActDisc (EvalBody.evalNeedUserSupply rec callee cells ctx env) := by
  unfold EvalBody.evalNeedUserSupply; act_tac

theorem EvalBody.evalNeedFamilySupply_actDisc (rec : EvalRec) (hrec : ∀ c, ActDisc (rec c)) (callee : Algorithm) (cells : List Nat) (ctx : EvalCtx) (env : ValEnv) (calleeName : String) :
    ActDisc (EvalBody.evalNeedFamilySupply rec callee cells ctx env calleeName) := by
  unfold EvalBody.evalNeedFamilySupply; act_tac

theorem EvalBody.invokeNeed_actDisc (rec : EvalRec) (hrec : ∀ c, ActDisc (rec c)) (arg : ResolvedArgumentAlgorithm) :
    ActDisc (EvalBody.invokeNeed rec arg) := by
  unfold EvalBody.invokeNeed; act_tac

theorem EvalBody.argumentNeed_actDisc (rec : EvalRec) (hrec : ∀ c, ActDisc (rec c)) (arg : ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) :
    ActDisc (EvalBody.argumentNeed rec arg ctx env) := by
  unfold EvalBody.argumentNeed; act_tac

theorem EvalBody.runNeedStepSlots_actDisc (rec : EvalRec) (hrec : ∀ c, ActDisc (rec c)) (step : Algorithm) (ctx : EvalCtx) (env : ValEnv) (cells : List Nat) (stepName : String) :
    ActDisc (EvalBody.runNeedStepSlots rec step ctx env cells stepName) := by
  unfold EvalBody.runNeedStepSlots EvalBody.runNeedStepWith; act_tac

theorem EvalBody.runNeedWhileRound_actDisc (rec : EvalRec) (hrec : ∀ c, ActDisc (rec c)) (step : Algorithm) (ctx : EvalCtx) (env : ValEnv) (cells : List Nat) (stepName : String) :
    ActDisc (EvalBody.runNeedWhileRound rec step ctx env cells stepName) := by
  unfold EvalBody.runNeedWhileRound EvalBody.runNeedStepWith; act_tac

theorem EvalBody.evalAlgOutputCore_actDisc (rec : EvalRec) (hrec : ∀ c, ActDisc (rec c)) (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    ActDisc (EvalBody.evalAlgOutputCore rec a ctx env) := by
  unfold EvalBody.evalAlgOutputCore; act_tac

theorem EvalBody.evalAlgOutput_actDisc (rec : EvalRec) (hrec : ∀ c, ActDisc (rec c)) (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    ActDisc (EvalBody.evalAlgOutput rec a ctx env) := by
  unfold EvalBody.evalAlgOutput; act_tac

theorem EvalBody.evalProgramOutput_actDisc (rec : EvalRec) (hrec : ∀ c, ActDisc (rec c)) (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    ActDisc (EvalBody.evalProgramOutput rec a ctx env) := by
  unfold EvalBody.evalProgramOutput; act_tac

theorem EvalBody.evalAlgOutputSlots_actDisc (rec : EvalRec) (hrec : ∀ c, ActDisc (rec c)) (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    ActDisc (EvalBody.evalAlgOutputSlots rec a ctx env) := by
  unfold EvalBody.evalAlgOutputSlots ActivatedBody.readRows; act_tac

theorem EvalBody.formOutputRow_actDisc (rec : EvalRec) (hrec : ∀ c, ActDisc (rec c)) (ctx : EvalCtx) (env : ValEnv) (e : Expr) :
    ActDisc (EvalBody.formOutputRow rec ctx env e) := by
  unfold EvalBody.formOutputRow; act_tac

theorem EvalBody.whileVerdictSlots_actDisc (rec : EvalRec) (hrec : ∀ c, ActDisc (rec c)) (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    ActDisc (EvalBody.whileVerdictSlots rec a ctx env) := by
  unfold EvalBody.whileVerdictSlots ActivatedBody.readRows; act_tac

theorem EvalBody.evalSequenceCallbackCall_actDisc (rec : EvalRec) (hrec : ∀ c, ActDisc (rec c)) (callee : Algorithm) (item : CountedResult) (ctx : EvalCtx) (env : ValEnv) (calleeName : String) :
    ActDisc (EvalBody.evalSequenceCallbackCall rec callee item ctx env calleeName) := by
  unfold EvalBody.evalSequenceCallbackCall; act_tac

theorem EvalBody.evalSequenceCallbackCallCounted_actDisc (rec : EvalRec) (hrec : ∀ c, ActDisc (rec c)) (callee : Algorithm) (item : CountedResult) (ctx : EvalCtx) (env : ValEnv) (calleeName : String) :
    ActDisc (EvalBody.evalSequenceCallbackCallCounted rec callee item ctx env calleeName) := by
  unfold EvalBody.evalSequenceCallbackCallCounted; act_tac

theorem EvalBody.evalAlgOutputPreparedCore_actDisc (rec : EvalRec) (hrec : ∀ c, ActDisc (rec c)) (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    ActDisc (EvalBody.evalAlgOutputPreparedCore rec a ctx env) := by
  unfold EvalBody.evalAlgOutputPreparedCore; act_tac

theorem EvalBody.evalOutputRowsPreparedCore_actDisc (rec : EvalRec) (hrec : ∀ c, ActDisc (rec c)) (rows : OutputBundle) (rowCtx : EvalCtx) (env : ValEnv) :
    ActDisc (EvalBody.evalOutputRowsPreparedCore rec rows rowCtx env) := by
  unfold EvalBody.evalOutputRowsPreparedCore; act_tac

theorem EvalBody.evalCapturePreparedCore_actDisc (rec : EvalRec) (hrec : ∀ c, ActDisc (rec c)) (rows : OutputBundle) (ctx : EvalCtx) (env : ValEnv) :
    ActDisc (EvalBody.evalCapturePreparedCore rec rows ctx env) := by
  unfold EvalBody.evalCapturePreparedCore; act_tac

theorem EvalBody.evalCaptureCountedCore_actDisc (rec : EvalRec) (hrec : ∀ c, ActDisc (rec c)) (rows : OutputBundle) (ctx : EvalCtx) (env : ValEnv) :
    ActDisc (EvalBody.evalCaptureCountedCore rec rows ctx env) := by
  unfold EvalBody.evalCaptureCountedCore; act_tac

theorem EvalBody.evalCaptureValue_actDisc (rec : EvalRec) (hrec : ∀ c, ActDisc (rec c)) (rows : OutputBundle) (ctx : EvalCtx) (env : ValEnv) :
    ActDisc (EvalBody.evalCaptureValue rec rows ctx env) := by
  unfold EvalBody.evalCaptureValue; act_tac

theorem EvalBody.evalAlgOutputCountedCore_actDisc (rec : EvalRec) (hrec : ∀ c, ActDisc (rec c)) (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    ActDisc (EvalBody.evalAlgOutputCountedCore rec a ctx env) := by
  unfold EvalBody.evalAlgOutputCountedCore; act_tac

theorem EvalBody.evalAlgOutputCounted_actDisc (rec : EvalRec) (hrec : ∀ c, ActDisc (rec c)) (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    ActDisc (EvalBody.evalAlgOutputCounted rec a ctx env) := by
  unfold EvalBody.evalAlgOutputCounted; act_tac

/-- A VALUE terminal's read (`EvalBody.terminalAccess`), proved once and used by every body that
    reads one, so those bodies never unfold it inline (M4★). -/
theorem EvalBody.terminalAccess_actDisc (rec : EvalRec) (hrec : ∀ c, ActDisc (rec c)) (t : AliasTerminal) (ctx : EvalCtx) (env : ValEnv) :
    ActDisc (EvalBody.terminalAccess rec t ctx env) := by
  unfold EvalBody.terminalAccess; act_tac

theorem EvalBody.evalZeroArgumentDemandOutputCounted_actDisc (rec : EvalRec) (hrec : ∀ c, ActDisc (rec c)) (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    ActDisc (EvalBody.evalZeroArgumentDemandOutputCounted rec a ctx env) := by
  unfold EvalBody.evalZeroArgumentDemandOutputCounted; act_tac

theorem EvalBody.evalZeroArgumentDemandOutput_actDisc (rec : EvalRec) (hrec : ∀ c, ActDisc (rec c)) (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    ActDisc (EvalBody.evalZeroArgumentDemandOutput rec a ctx env) := by
  unfold EvalBody.evalZeroArgumentDemandOutput; act_tac

theorem EvalBody.evalArgumentValueCounted_actDisc (rec : EvalRec) (hrec : ∀ c, ActDisc (rec c)) (arg : ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) :
    ActDisc (EvalBody.evalArgumentValueCounted rec arg ctx env) := by
  unfold EvalBody.evalArgumentValueCounted; act_tac

theorem EvalBody.evalArgumentValue_actDisc (rec : EvalRec) (hrec : ∀ c, ActDisc (rec c)) (arg : ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) :
    ActDisc (EvalBody.evalArgumentValue rec arg ctx env) := by
  unfold EvalBody.evalArgumentValue; act_tac

/-- CACHE-PUB-1: a property request's calculation (a read's demand, an invocation's fresh call) is
    mark-preserving whenever its recursive answer is. -/
theorem EvalBody.zeroArgPropertyCalculation_actDisc (rec : EvalRec) (hrec : ∀ c, ActDisc (rec c)) (request : ZeroArgPropertyRequest) (resolvedAlgorithm : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    ActDisc (EvalBody.zeroArgPropertyCalculation rec request resolvedAlgorithm ctx env) := by
  unfold EvalBody.zeroArgPropertyCalculation; act_tac

theorem EvalBody.evalZeroArgPropertyAccessCounted_actDisc (rec : EvalRec) (hrec : ∀ c, ActDisc (rec c)) (accessKind : ZeroArgPropertyAccessKind) (owner : Algorithm) (binding : PropDef) (resolvedAlgorithm : Algorithm) (ctx : EvalCtx) (env : ValEnv) (request : ZeroArgPropertyRequest) :
    ActDisc (EvalBody.evalZeroArgPropertyAccessCounted rec accessKind owner binding resolvedAlgorithm ctx env request) := by
  have hcalc : ∀ q, ActDisc (EvalBody.zeroArgPropertyCalculation rec q resolvedAlgorithm ctx env) :=
    fun q => EvalBody.zeroArgPropertyCalculation_actDisc rec hrec q resolvedAlgorithm ctx env
  unfold EvalBody.evalZeroArgPropertyAccessCounted; act_tac

theorem EvalBody.evalZeroArgPropertyAccess_actDisc (rec : EvalRec) (hrec : ∀ c, ActDisc (rec c)) (accessKind : ZeroArgPropertyAccessKind) (owner : Algorithm) (binding : PropDef) (resolvedAlgorithm : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    ActDisc (EvalBody.evalZeroArgPropertyAccess rec accessKind owner binding resolvedAlgorithm ctx env) := by
  unfold EvalBody.evalZeroArgPropertyAccess; act_tac

theorem EvalBody.evalConditionalCallbackCallCounted_actDisc (rec : EvalRec) (hrec : ∀ c, ActDisc (rec c)) (callee : Algorithm) (args : List CountedResult) (ctx : EvalCtx) (env : ValEnv) (calleeName : String) :
    ActDisc (EvalBody.evalConditionalCallbackCallCounted rec callee args ctx env calleeName) := by
  unfold EvalBody.evalConditionalCallbackCallCounted; act_tac

theorem EvalBody.evalUserCallbackCallCounted_actDisc (rec : EvalRec) (hrec : ∀ c, ActDisc (rec c)) (callee : Algorithm) (args : List CountedResult) (ctx : EvalCtx) (env : ValEnv) :
    ActDisc (EvalBody.evalUserCallbackCallCounted rec callee args ctx env) := by
  unfold EvalBody.evalUserCallbackCallCounted; act_tac

theorem EvalBody.evalResolvedCallbackCallCounted_actDisc (rec : EvalRec) (hrec : ∀ c, ActDisc (rec c)) (callee : Algorithm) (args : List CountedResult) (ctx : EvalCtx) (env : ValEnv) (calleeName : String) :
    ActDisc (EvalBody.evalResolvedCallbackCallCounted rec callee args ctx env calleeName) := by
  unfold EvalBody.evalResolvedCallbackCallCounted; act_tac

theorem EvalBody.evalResolvedCallbackCall_actDisc (rec : EvalRec) (hrec : ∀ c, ActDisc (rec c)) (callee : Algorithm) (args : List CountedResult) (ctx : EvalCtx) (env : ValEnv) (calleeName : String) :
    ActDisc (EvalBody.evalResolvedCallbackCall rec callee args ctx env calleeName) := by
  unfold EvalBody.evalResolvedCallbackCall; act_tac

theorem EvalBody.evalSequenceReduceStepCounted_actDisc (rec : EvalRec) (hrec : ∀ c, ActDisc (rec c)) (callee : Algorithm) (element : CountedResult) (accumulator : Result) (ctx : EvalCtx) (env : ValEnv) (calleeName : String) :
    ActDisc (EvalBody.evalSequenceReduceStepCounted rec callee element accumulator ctx env calleeName) := by
  unfold EvalBody.evalSequenceReduceStepCounted; act_tac

theorem EvalBody.demandSequenceBuiltinCallItemValue_actDisc (rec : EvalRec) (hrec : ∀ c, ActDisc (rec c)) (item : CallableCallItem) (ctx : EvalCtx) (env : ValEnv) :
    ActDisc (EvalBody.demandSequenceBuiltinCallItemValue rec item ctx env) := by
  unfold EvalBody.demandSequenceBuiltinCallItemValue; act_tac

theorem EvalBody.staticReferenceTerminal_actDisc (rec : EvalRec) (hrec : ∀ c, ActDisc (rec c)) (owner : Algorithm) (reference : Expr) (ctx : EvalCtx) :
    ActDisc (EvalBody.staticReferenceTerminal rec owner reference ctx) := by
  unfold EvalBody.staticReferenceTerminal; act_tac

theorem EvalBody.transparentRetainedCell_actDisc (rec : EvalRec) (hrec : ∀ c, ActDisc (rec c)) (reference : Expr) (ctx : EvalCtx) :
    ActDisc (EvalBody.transparentRetainedCell? rec reference ctx) := by
  unfold EvalBody.transparentRetainedCell? parameterNeedAddress?; act_tac

theorem EvalBody.retainedCellSlice_actDisc (rec : EvalRec) (hrec : ∀ c, ActDisc (rec c)) (fuel address : Nat) :
    ActDisc (EvalBody.retainedCellSlice? rec fuel address) := by
  induction fuel generalizing address with
  | zero => unfold EvalBody.retainedCellSlice?; act_tac
  | succ n ih => unfold EvalBody.retainedCellSlice?; act_tac

theorem EvalBody.retainedSliceAt_actDisc (rec : EvalRec) (hrec : ∀ c, ActDisc (rec c)) (address : Nat) :
    ActDisc (EvalBody.retainedSliceAt? rec address) := by
  have := EvalBody.retainedCellSlice_actDisc rec hrec
  unfold EvalBody.retainedSliceAt?; act_tac

theorem EvalBody.writtenCollectorSlice_actDisc (rec : EvalRec) (hrec : ∀ c, ActDisc (rec c)) (receiver : Expr) (ctx : EvalCtx) :
    ActDisc (EvalBody.writtenCollectorSlice? rec receiver ctx) := by
  unfold EvalBody.writtenCollectorSlice? parameterNeedAddress?; act_tac

theorem retainedCollectorBuiltin_actDisc (rec : EvalRec) (hrec : ∀ c, ActDisc (rec c)) (b : Builtin)
    (metadata : SequenceBuiltinMetadata) (suffixArgs : List PreparedSequenceBuiltinSuffixArg) (slice : List Nat) :
    ActDisc (retainedCollectorBuiltin rec.demandNeedRecursive b metadata suffixArgs slice) := by
  unfold retainedCollectorBuiltin argumentViewBuiltin NeedDemand.materialize; act_tac

set_option maxHeartbeats 2000000 in
theorem EvalBody.bindSequenceBuiltinArguments_actDisc (rec : EvalRec) (hrec : ∀ c, ActDisc (rec c)) (b : Builtin) (metadata : SequenceBuiltinMetadata) (args : List ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) :
    ActDisc (EvalBody.bindSequenceBuiltinArguments rec b metadata args ctx env) := by
  unfold EvalBody.bindSequenceBuiltinArguments; act_tac

theorem EvalBody.evalReduceCounted_actDisc (rec : EvalRec) (hrec : ∀ c, ActDisc (rec c)) (collection : List CountedResult) (stepAlg : Algorithm) (initial : Result) (ctx : EvalCtx) (env : ValEnv) :
    ActDisc (EvalBody.evalReduceCounted rec collection stepAlg initial ctx env) := by
  unfold EvalBody.evalReduceCounted; act_tac

theorem EvalBody.evalFilterCounted_actDisc (rec : EvalRec) (hrec : ∀ c, ActDisc (rec c)) (items : List CountedResult) (predicateAlg : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    ActDisc (EvalBody.evalFilterCounted rec items predicateAlg ctx env) := by
  unfold EvalBody.evalFilterCounted; act_tac

theorem EvalBody.evalMapCounted_actDisc (rec : EvalRec) (hrec : ∀ c, ActDisc (rec c)) (collection : List CountedResult) (transformAlg : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    ActDisc (EvalBody.evalMapCounted rec collection transformAlg ctx env) := by
  unfold EvalBody.evalMapCounted; act_tac

theorem EvalBody.applyBuiltinCountedSequence_actDisc (rec : EvalRec) (hrec : ∀ c, ActDisc (rec c)) (b : Builtin) (metadata : SequenceBuiltinMetadata) (args : List ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) :
    ActDisc (EvalBody.applyBuiltinCountedSequence rec b metadata args ctx env) := by
  unfold EvalBody.applyBuiltinCountedSequence; act_tac

-- META-S3-3 enlarged this body (the builtin META binding branch); the same tactic needs more time.
set_option maxHeartbeats 1600000 in
theorem EvalBody.applyBuiltinCounted_actDisc (rec : EvalRec) (hrec : ∀ c, ActDisc (rec c)) (b : Builtin) (args : List ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) :
    ActDisc (EvalBody.applyBuiltinCounted rec b args ctx env) := by
  unfold EvalBody.applyBuiltinCounted; act_tac

theorem EvalBody.applyBuiltin_actDisc (rec : EvalRec) (hrec : ∀ c, ActDisc (rec c)) (b : Builtin) (args : List ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) :
    ActDisc (EvalBody.applyBuiltin rec b args ctx env) := by
  unfold EvalBody.applyBuiltin; act_tac

theorem EvalBody.applyBuiltinCountedResolved_actDisc (rec : EvalRec) (hrec : ∀ c, ActDisc (rec c)) (b : Builtin) (args : List ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) :
    ActDisc (EvalBody.applyBuiltinCountedResolved rec b args ctx env) := by
  unfold EvalBody.applyBuiltinCountedResolved; act_tac

theorem EvalBody.evalExplicitSequenceValueItems_actDisc (rec : EvalRec) (hrec : ∀ c, ActDisc (rec c)) (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    ActDisc (EvalBody.evalExplicitSequenceValueItems rec a ctx env) := by
  unfold EvalBody.evalExplicitSequenceValueItems; act_tac

theorem EvalBody.evalExplicitSequenceValueRowSlots_actDisc (rec : EvalRec) (hrec : ∀ c, ActDisc (rec c)) (rows : OutputBundle) (rowCtx : EvalCtx) (env : ValEnv) :
    ActDisc (EvalBody.evalExplicitSequenceValueRowSlots rec rows rowCtx env) := by
  unfold EvalBody.evalExplicitSequenceValueRowSlots; act_tac

theorem EvalBody.evalExplicitSequenceValueExprSlots_actDisc (rec : EvalRec) (hrec : ∀ c, ActDisc (rec c)) (expr : Expr) (ctx : EvalCtx) (env : ValEnv) :
    ActDisc (EvalBody.evalExplicitSequenceValueExprSlots rec expr ctx env) := by
  unfold EvalBody.evalExplicitSequenceValueExprSlots; act_tac

theorem EvalBody.evalUserCallCounted_actDisc (rec : EvalRec) (hrec : ∀ c, ActDisc (rec c)) (callee : Algorithm) (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) :
    ActDisc (EvalBody.evalUserCallCounted rec callee args ctx env) := by
  unfold EvalBody.evalUserCallCounted; act_tac

theorem EvalBody.evalConditionalCallCounted_actDisc (rec : EvalRec) (hrec : ∀ c, ActDisc (rec c)) (callee : Algorithm) (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) (calleeName : String) :
    ActDisc (EvalBody.evalConditionalCallCounted rec callee args ctx env calleeName) := by
  unfold EvalBody.evalConditionalCallCounted; act_tac

theorem EvalBody.evalResolvedCall_actDisc (rec : EvalRec) (hrec : ∀ c, ActDisc (rec c)) (callee : Algorithm) (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) (calleeName : String) :
    ActDisc (EvalBody.evalResolvedCall rec callee args ctx env calleeName) := by
  unfold EvalBody.evalResolvedCall; act_tac

theorem EvalBody.evalResolvedCallCounted_actDisc (rec : EvalRec) (hrec : ∀ c, ActDisc (rec c)) (callee : Algorithm) (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) (calleeName : String) (origin : CalleeOrigin) :
    ActDisc (EvalBody.evalResolvedCallCounted rec callee args ctx env calleeName origin) := by
  unfold EvalBody.evalResolvedCallCounted; act_tac

theorem EvalBody.evalCallCountedExpr_actDisc (rec : EvalRec) (hrec : ∀ c, ActDisc (rec c)) (f : Expr) (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) :
    ActDisc (EvalBody.evalCallCountedExpr rec f args ctx env) := by
  unfold EvalBody.evalCallCountedExpr; act_tac

theorem EvalBody.callLexicalWithReceiverCounted_actDisc (rec : EvalRec) (hrec : ∀ c, ActDisc (rec c)) (name : Ident) (receiver : Expr) (fallback : Expr) (extraArgs : Option OutputBundle) (ctx : EvalCtx) (env : ValEnv) :
    ActDisc (EvalBody.callLexicalWithReceiverCounted rec name receiver fallback extraArgs ctx env) := by
  unfold EvalBody.callLexicalWithReceiverCounted; act_tac

theorem EvalBody.rejectDotStringIntrinsicArguments_actDisc (rec : EvalRec) (hrec : ∀ c, ActDisc (rec c)) (argsOpt : Option OutputBundle) (ctx : EvalCtx) (env : ValEnv) :
    ActDisc (EvalBody.rejectDotStringIntrinsicArguments rec argsOpt ctx env) := by
  unfold EvalBody.rejectDotStringIntrinsicArguments; act_tac

theorem EvalBody.evalDotStringReceiverValue_actDisc (rec : EvalRec) (hrec : ∀ c, ActDisc (rec c)) (target : Expr) (targetAlg : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    ActDisc (EvalBody.evalDotStringReceiverValue rec target targetAlg ctx env) := by
  unfold EvalBody.evalDotStringReceiverValue; act_tac

set_option maxHeartbeats 4000000 in
theorem EvalBody.evalDotCallCounted_actDisc (rec : EvalRec) (hrec : ∀ c, ActDisc (rec c)) (target : Expr) (name : Ident) (fallback : Expr) (argsOpt : Option OutputBundle) (ctx : EvalCtx) (env : ValEnv) :
    ActDisc (EvalBody.evalDotCallCounted rec target name fallback argsOpt ctx env) := by
  unfold EvalBody.evalDotCallCounted; act_tac

theorem EvalBody.rejectInvokeIntrinsicArguments_actDisc (rec : EvalRec) (hrec : ∀ c, ActDisc (rec c)) (argsOpt : Option OutputBundle) (ctx : EvalCtx) (env : ValEnv) :
    ActDisc (EvalBody.rejectInvokeIntrinsicArguments rec argsOpt ctx env) := by
  unfold EvalBody.rejectInvokeIntrinsicArguments; act_tac

theorem EvalBody.invokeCallReferenceValue_actDisc (rec : EvalRec) (hrec : ∀ c, ActDisc (rec c)) (val : Result) :
    ActDisc (EvalBody.invokeCallReferenceValue rec val) := by
  unfold EvalBody.invokeCallReferenceValue; act_tac

theorem EvalBody.argumentViewCells_actDisc (rec : EvalRec) (hrec : ∀ c, ActDisc (rec c)) (a : Nat) :
    ActDisc (EvalBody.argumentViewCells rec a) := by
  unfold EvalBody.argumentViewCells; act_tac

theorem EvalBody.evalArgumentViewBuiltin_actDisc (rec : EvalRec) (hrec : ∀ c, ActDisc (rec c)) (b : Builtin) (a : Nat) :
    ActDisc (EvalBody.evalArgumentViewBuiltin rec b a) := by
  unfold EvalBody.evalArgumentViewBuiltin; act_tac

theorem EvalBody.evalSequenceSpreadOperandValue_actDisc (rec : EvalRec) (hrec : ∀ c, ActDisc (rec c)) (e : Expr) (ctx : EvalCtx) (env : ValEnv) :
    ActDisc (EvalBody.evalSequenceSpreadOperandValue rec e ctx env) := by
  unfold EvalBody.evalSequenceSpreadOperandValue; act_tac

theorem EvalBody.evalSequenceSpreadCounted_actDisc (rec : EvalRec) (hrec : ∀ c, ActDisc (rec c)) (e : Expr) (ctx : EvalCtx) (env : ValEnv) :
    ActDisc (EvalBody.evalSequenceSpreadCounted rec e ctx env) := by
  unfold EvalBody.evalSequenceSpreadCounted; act_tac

theorem EvalBody.transparentCollectorSlice_actDisc (rec : EvalRec) (hrec : ∀ c, ActDisc (rec c)) (e : Expr) (ctx : EvalCtx) :
    ActDisc (EvalBody.transparentCollectorSlice? rec e ctx) := by
  unfold EvalBody.transparentCollectorSlice?; act_tac

theorem EvalBody.evalSupplySpread_actDisc (rec : EvalRec) (hrec : ∀ c, ActDisc (rec c)) (e : Expr) (ctx : EvalCtx) (env : ValEnv) :
    ActDisc (EvalBody.evalSupplySpread rec e ctx env) := by
  unfold EvalBody.evalSupplySpread; act_tac

theorem EvalBody.evalListLiteralCounted_actDisc (rec : EvalRec) (hrec : ∀ c, ActDisc (rec c)) (elements : List Expr) (ctx : EvalCtx) (env : ValEnv) :
    ActDisc (EvalBody.evalListLiteralCounted rec elements ctx env) := by
  unfold EvalBody.evalListLiteralCounted; act_tac

theorem EvalBody.evalSequenceConstructCounted_actDisc (rec : EvalRec) (hrec : ∀ c, ActDisc (rec c)) (e : Expr) (ctx : EvalCtx) (env : ValEnv) :
    ActDisc (EvalBody.evalSequenceConstructCounted rec e ctx env) := by
  unfold EvalBody.evalSequenceConstructCounted; act_tac

theorem EvalBody.evalUnaryCounted_actDisc (rec : EvalRec) (hrec : ∀ c, ActDisc (rec c)) (op : UnaryOp) (operand : Expr) (ctx : EvalCtx) (env : ValEnv) :
    ActDisc (EvalBody.evalUnaryCounted rec op operand ctx env) := by
  unfold EvalBody.evalUnaryCounted; act_tac

theorem EvalBody.evalBinaryCounted_actDisc (rec : EvalRec) (hrec : ∀ c, ActDisc (rec c)) (op : BinaryOp) (a b : Expr) (ctx : EvalCtx) (env : ValEnv) :
    ActDisc (EvalBody.evalBinaryCounted rec op a b ctx env) := by
  unfold EvalBody.evalBinaryCounted; act_tac

theorem EvalBody.evalComparisonCounted_actDisc (rec : EvalRec) (hrec : ∀ c, ActDisc (rec c)) (first : Expr) (links : List ComparisonLink) (ctx : EvalCtx) (env : ValEnv) :
    ActDisc (EvalBody.evalComparisonCounted rec first links ctx env) := by
  unfold EvalBody.evalComparisonCounted; act_tac

theorem EvalBody.evalComparisonLinksCounted_actDisc (rec : EvalRec) (hrec : ∀ c, ActDisc (rec c)) (previousExpr : Expr) (previous : Result) (holds : Bool) (links : List ComparisonLink) (ctx : EvalCtx) (env : ValEnv) :
    ActDisc (EvalBody.evalComparisonLinksCounted rec previousExpr previous holds links ctx env) := by
  unfold EvalBody.evalComparisonLinksCounted; act_tac

theorem EvalBody.evalCounted_actDisc (rec : EvalRec) (hrec : ∀ c, ActDisc (rec c)) (e : Expr) (ctx : EvalCtx) (env : ValEnv) :
    ActDisc (EvalBody.evalCounted rec e ctx env) := by
  unfold EvalBody.evalCounted; act_tac

theorem EvalBody.evalUserCall_actDisc (rec : EvalRec) (hrec : ∀ c, ActDisc (rec c)) (callee : Algorithm) (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) :
    ActDisc (EvalBody.evalUserCall rec callee args ctx env) := by
  unfold EvalBody.evalUserCall; act_tac

theorem EvalBody.evalConditionalCall_actDisc (rec : EvalRec) (hrec : ∀ c, ActDisc (rec c)) (callee : Algorithm) (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) (calleeName : String) :
    ActDisc (EvalBody.evalConditionalCall rec callee args ctx env calleeName) := by
  unfold EvalBody.evalConditionalCall; act_tac

theorem EvalBody.evalCallExpr_actDisc (rec : EvalRec) (hrec : ∀ c, ActDisc (rec c)) (f : Expr) (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) :
    ActDisc (EvalBody.evalCallExpr rec f args ctx env) := by
  unfold EvalBody.evalCallExpr; act_tac

theorem EvalBody.evalDotCall_actDisc (rec : EvalRec) (hrec : ∀ c, ActDisc (rec c)) (target : Expr) (name : Ident) (fallback : Expr) (argsOpt : Option OutputBundle) (ctx : EvalCtx) (env : ValEnv) :
    ActDisc (EvalBody.evalDotCall rec target name fallback argsOpt ctx env) := by
  unfold EvalBody.evalDotCall; act_tac

theorem EvalBody.eval_actDisc (rec : EvalRec) (hrec : ∀ c, ActDisc (rec c)) (e : Expr) (ctx : EvalCtx) (env : ValEnv) :
    ActDisc (EvalBody.eval rec e ctx env) := by
  unfold EvalBody.eval; act_tac

theorem evalStep_actDisc (rec : EvalRec) (hrec : ∀ c, ActDisc (rec c)) :
    ∀ c, ActDisc (evalStep rec c) := by
  intro c
  cases c with
  | whileLoop step ctx env stepName cells => exact EvalBody.whileLoop_actDisc rec hrec step ctx env stepName cells
  | aliasStepIsRuntime step target ctx visited => exact EvalBody.aliasStepIsRuntime_actDisc rec hrec step target ctx visited
  | aliasValue wired ctx env => exact EvalBody.aliasValue_actDisc rec hrec wired ctx env
  | resolveAliasChase followCarriers projectRuntime a ctx visited last => exact EvalBody.resolveAliasChase_actDisc rec hrec followCarriers projectRuntime a ctx visited last
  | resolveAliasStructure a ctx => exact EvalBody.resolveAliasStructure_actDisc rec hrec a ctx
  | aliasOriginBinding? a ctx => exact EvalBody.aliasOriginBinding?_actDisc rec hrec a ctx
  | resolveAliasTarget a ctx => exact EvalBody.resolveAliasTarget_actDisc rec hrec a ctx
  | resolveAliasValueTarget a ctx => exact EvalBody.resolveAliasValueTarget_actDisc rec hrec a ctx
  | lookupLexicalProperty a name ctx => exact EvalBody.lookupLexicalProperty_actDisc rec hrec a name ctx
  | lookupLexicalValueProperty a name ctx => exact EvalBody.lookupLexicalValueProperty_actDisc rec hrec a name ctx
  | lookupLexical a name ctx => exact EvalBody.lookupLexical_actDisc rec hrec a name ctx
  | needPlanNormalizeCallee callee ctx => exact EvalBody.needPlanNormalizeCallee_actDisc rec hrec callee ctx
  | resolveAlg e ctx => exact EvalBody.resolveAlg_actDisc rec hrec e ctx
  | projectNeedCallable address => exact EvalBody.projectNeedCallable_actDisc rec hrec address
  | projectNeedWrittenAt address source caller => exact EvalBody.projectNeedWrittenAt_actDisc rec hrec address source caller
  | linkCallable address => exact EvalBody.linkCallable_actDisc rec hrec address
  | projectParameterCallable x ctx => exact EvalBody.projectParameterCallable_actDisc rec hrec x ctx
  | projectNeedWritten source caller => exact EvalBody.projectNeedWritten_actDisc rec hrec source caller
  | projectNeedStructuralMember source ctx => exact EvalBody.projectNeedStructuralMember_actDisc rec hrec source ctx
  | resolveCalleeAlg f ctx => exact EvalBody.resolveCalleeAlg_actDisc rec hrec f ctx
  | expectPreparedSequenceBuiltinAlgorithmSuffixArg b descriptors args index => exact EvalBody.expectPreparedSequenceBuiltinAlgorithmSuffixArg_actDisc rec hrec b descriptors args index
  | resolveDotReceiver? e ctx => exact EvalBody.resolveDotReceiver?_actDisc rec hrec e ctx
  | resolveDotReceiver e ctx => exact EvalBody.resolveDotReceiver_actDisc rec hrec e ctx
  | algorithmIntrinsicRoute receiver ctx => exact EvalBody.algorithmIntrinsicRoute_actDisc rec hrec receiver ctx
  | demandNeedRecursive address => exact EvalBody.demandNeedRecursive_actDisc rec hrec address
  | evalSuppliedAt address e ctx env => exact EvalBody.evalSuppliedAt_actDisc rec hrec address e ctx env
  | linkValue address => exact EvalBody.linkValue_actDisc rec hrec address
  | algorithmOfValue val argsOpt ctx env => exact EvalBody.algorithmOfValue_actDisc rec hrec val argsOpt ctx env
  | capturedCallee callee => exact EvalBody.capturedCallee_actDisc rec hrec callee
  | referenceReceiverValue target targetAlg ctx env => exact EvalBody.referenceReceiverValue_actDisc rec hrec target targetAlg ctx env
  | algorithmCalleeOf receiver ctx env => exact EvalBody.algorithmCalleeOf_actDisc rec hrec receiver ctx env
  | evalSuppliedCallCounted origin callee cells ctx env calleeName => exact EvalBody.evalSuppliedCallCounted_actDisc rec hrec origin callee cells ctx env calleeName
  | evalNeedUserSupply callee cells ctx env => exact EvalBody.evalNeedUserSupply_actDisc rec hrec callee cells ctx env
  | evalNeedFamilySupply callee cells ctx env calleeName => exact EvalBody.evalNeedFamilySupply_actDisc rec hrec callee cells ctx env calleeName
  | invokeNeed arg => exact EvalBody.invokeNeed_actDisc rec hrec arg
  | argumentNeed arg ctx env => exact EvalBody.argumentNeed_actDisc rec hrec arg ctx env
  | runNeedStepSlots step ctx env cells stepName => exact EvalBody.runNeedStepSlots_actDisc rec hrec step ctx env cells stepName
  | runNeedWhileRound step ctx env cells stepName => exact EvalBody.runNeedWhileRound_actDisc rec hrec step ctx env cells stepName
  | evalAlgOutputCore a ctx env => exact EvalBody.evalAlgOutputCore_actDisc rec hrec a ctx env
  | evalAlgOutput a ctx env => exact EvalBody.evalAlgOutput_actDisc rec hrec a ctx env
  | evalProgramOutput a ctx env => exact EvalBody.evalProgramOutput_actDisc rec hrec a ctx env
  | evalAlgOutputSlots a ctx env => exact EvalBody.evalAlgOutputSlots_actDisc rec hrec a ctx env
  | formOutputRow ctx env e => exact EvalBody.formOutputRow_actDisc rec hrec ctx env e
  | whileVerdictSlots a ctx env => exact EvalBody.whileVerdictSlots_actDisc rec hrec a ctx env
  | evalSequenceCallbackCall callee item ctx env calleeName => exact EvalBody.evalSequenceCallbackCall_actDisc rec hrec callee item ctx env calleeName
  | evalSequenceCallbackCallCounted callee item ctx env calleeName => exact EvalBody.evalSequenceCallbackCallCounted_actDisc rec hrec callee item ctx env calleeName
  | evalAlgOutputPreparedCore a ctx env => exact EvalBody.evalAlgOutputPreparedCore_actDisc rec hrec a ctx env
  | evalOutputRowsPreparedCore rows rowCtx env => exact EvalBody.evalOutputRowsPreparedCore_actDisc rec hrec rows rowCtx env
  | evalCapturePreparedCore rows ctx env => exact EvalBody.evalCapturePreparedCore_actDisc rec hrec rows ctx env
  | evalCaptureCountedCore rows ctx env => exact EvalBody.evalCaptureCountedCore_actDisc rec hrec rows ctx env
  | evalCaptureValue rows ctx env => exact EvalBody.evalCaptureValue_actDisc rec hrec rows ctx env
  | evalAlgOutputCountedCore a ctx env => exact EvalBody.evalAlgOutputCountedCore_actDisc rec hrec a ctx env
  | evalAlgOutputCounted a ctx env => exact EvalBody.evalAlgOutputCounted_actDisc rec hrec a ctx env
  | evalZeroArgumentDemandOutputCounted a ctx env => exact EvalBody.evalZeroArgumentDemandOutputCounted_actDisc rec hrec a ctx env
  | evalZeroArgumentDemandOutput a ctx env => exact EvalBody.evalZeroArgumentDemandOutput_actDisc rec hrec a ctx env
  | evalArgumentValueCounted arg ctx env => exact EvalBody.evalArgumentValueCounted_actDisc rec hrec arg ctx env
  | evalArgumentValue arg ctx env => exact EvalBody.evalArgumentValue_actDisc rec hrec arg ctx env
  | evalZeroArgPropertyAccessCounted accessKind owner binding resolvedAlgorithm ctx env request => exact EvalBody.evalZeroArgPropertyAccessCounted_actDisc rec hrec accessKind owner binding resolvedAlgorithm ctx env request
  | evalZeroArgPropertyAccess accessKind owner binding resolvedAlgorithm ctx env => exact EvalBody.evalZeroArgPropertyAccess_actDisc rec hrec accessKind owner binding resolvedAlgorithm ctx env
  | evalConditionalCallbackCallCounted callee args ctx env calleeName => exact EvalBody.evalConditionalCallbackCallCounted_actDisc rec hrec callee args ctx env calleeName
  | evalUserCallbackCallCounted callee args ctx env => exact EvalBody.evalUserCallbackCallCounted_actDisc rec hrec callee args ctx env
  | evalResolvedCallbackCallCounted callee args ctx env calleeName => exact EvalBody.evalResolvedCallbackCallCounted_actDisc rec hrec callee args ctx env calleeName
  | evalResolvedCallbackCall callee args ctx env calleeName => exact EvalBody.evalResolvedCallbackCall_actDisc rec hrec callee args ctx env calleeName
  | evalSequenceReduceStepCounted callee element accumulator ctx env calleeName => exact EvalBody.evalSequenceReduceStepCounted_actDisc rec hrec callee element accumulator ctx env calleeName
  | demandSequenceBuiltinCallItemValue item ctx env => exact EvalBody.demandSequenceBuiltinCallItemValue_actDisc rec hrec item ctx env
  | bindSequenceBuiltinArguments b metadata args ctx env => exact EvalBody.bindSequenceBuiltinArguments_actDisc rec hrec b metadata args ctx env
  | evalReduceCounted collection stepAlg initial ctx env => exact EvalBody.evalReduceCounted_actDisc rec hrec collection stepAlg initial ctx env
  | evalFilterCounted items predicateAlg ctx env => exact EvalBody.evalFilterCounted_actDisc rec hrec items predicateAlg ctx env
  | evalMapCounted collection transformAlg ctx env => exact EvalBody.evalMapCounted_actDisc rec hrec collection transformAlg ctx env
  | applyBuiltinCountedSequence b metadata args ctx env => exact EvalBody.applyBuiltinCountedSequence_actDisc rec hrec b metadata args ctx env
  | applyBuiltinCounted b args ctx env => exact EvalBody.applyBuiltinCounted_actDisc rec hrec b args ctx env
  | applyBuiltin b args ctx env => exact EvalBody.applyBuiltin_actDisc rec hrec b args ctx env
  | applyBuiltinCountedResolved b args ctx env => exact EvalBody.applyBuiltinCountedResolved_actDisc rec hrec b args ctx env
  | evalExplicitSequenceValueItems a ctx env => exact EvalBody.evalExplicitSequenceValueItems_actDisc rec hrec a ctx env
  | evalExplicitSequenceValueRowSlots rows rowCtx env => exact EvalBody.evalExplicitSequenceValueRowSlots_actDisc rec hrec rows rowCtx env
  | evalExplicitSequenceValueExprSlots expr ctx env => exact EvalBody.evalExplicitSequenceValueExprSlots_actDisc rec hrec expr ctx env
  | evalUserCallCounted callee args ctx env => exact EvalBody.evalUserCallCounted_actDisc rec hrec callee args ctx env
  | evalConditionalCallCounted callee args ctx env calleeName => exact EvalBody.evalConditionalCallCounted_actDisc rec hrec callee args ctx env calleeName
  | evalResolvedCall callee args ctx env calleeName => exact EvalBody.evalResolvedCall_actDisc rec hrec callee args ctx env calleeName
  | evalResolvedCallCounted callee args ctx env calleeName origin => exact EvalBody.evalResolvedCallCounted_actDisc rec hrec callee args ctx env calleeName origin
  | evalCallCountedExpr f args ctx env => exact EvalBody.evalCallCountedExpr_actDisc rec hrec f args ctx env
  | callLexicalWithReceiverCounted name receiver fallback extraArgs ctx env => exact EvalBody.callLexicalWithReceiverCounted_actDisc rec hrec name receiver fallback extraArgs ctx env
  | rejectDotStringIntrinsicArguments argsOpt ctx env => exact EvalBody.rejectDotStringIntrinsicArguments_actDisc rec hrec argsOpt ctx env
  | evalDotStringReceiverValue target targetAlg ctx env => exact EvalBody.evalDotStringReceiverValue_actDisc rec hrec target targetAlg ctx env
  | evalDotCallCounted target name fallback argsOpt ctx env => exact EvalBody.evalDotCallCounted_actDisc rec hrec target name fallback argsOpt ctx env
  | rejectInvokeIntrinsicArguments argsOpt ctx env => exact EvalBody.rejectInvokeIntrinsicArguments_actDisc rec hrec argsOpt ctx env
  | invokeCallReferenceValue val => exact EvalBody.invokeCallReferenceValue_actDisc rec hrec val
  | argumentViewCells a => exact EvalBody.argumentViewCells_actDisc rec hrec a
  | evalArgumentViewBuiltin b a => exact EvalBody.evalArgumentViewBuiltin_actDisc rec hrec b a
  | evalSequenceSpreadOperandValue e ctx env => exact EvalBody.evalSequenceSpreadOperandValue_actDisc rec hrec e ctx env
  | evalSequenceSpreadCounted e ctx env => exact EvalBody.evalSequenceSpreadCounted_actDisc rec hrec e ctx env
  | evalSupplySpread e ctx env => exact EvalBody.evalSupplySpread_actDisc rec hrec e ctx env
  | evalListLiteralCounted elements ctx env => exact EvalBody.evalListLiteralCounted_actDisc rec hrec elements ctx env
  | evalSequenceConstructCounted e ctx env => exact EvalBody.evalSequenceConstructCounted_actDisc rec hrec e ctx env
  | evalUnaryCounted op operand ctx env => exact EvalBody.evalUnaryCounted_actDisc rec hrec op operand ctx env
  | evalBinaryCounted op a b ctx env => exact EvalBody.evalBinaryCounted_actDisc rec hrec op a b ctx env
  | evalComparisonCounted first links ctx env => exact EvalBody.evalComparisonCounted_actDisc rec hrec first links ctx env
  | evalComparisonLinksCounted previousExpr previous holds links ctx env => exact EvalBody.evalComparisonLinksCounted_actDisc rec hrec previousExpr previous holds links ctx env
  | evalCounted e ctx env => exact EvalBody.evalCounted_actDisc rec hrec e ctx env
  | evalUserCall callee args ctx env => exact EvalBody.evalUserCall_actDisc rec hrec callee args ctx env
  | evalConditionalCall callee args ctx env calleeName => exact EvalBody.evalConditionalCall_actDisc rec hrec callee args ctx env calleeName
  | evalCallExpr f args ctx env => exact EvalBody.evalCallExpr_actDisc rec hrec f args ctx env
  | evalDotCall target name fallback argsOpt ctx env => exact EvalBody.evalDotCall_actDisc rec hrec target name fallback argsOpt ctx env
  | eval e ctx env => exact EvalBody.eval_actDisc rec hrec e ctx env

/-! ## Whole-run preservation of `evaluating` marks by the production evaluator -/

/-- Every evaluator body keeps every entry `evaluating` mark whenever its recursive answer does. -/
theorem body_step_actDisc : ∀ rec : EvalRec,
    (∀ c, Preserves (fun s t => ActHeapKept s.needs t.needs) (rec c)) →
    ∀ c, Preserves (fun s t => ActHeapKept s.needs t.needs) (evalStep rec c) :=
  fun rec hrec c => evalStep_actDisc rec hrec c

/-- **Every completed run of the total core, at every fuel, from every state, keeps every cell
    that was `evaluating` at entry `evaluating`.** -/
theorem evalFuel_actDisc (n : Nat) (c : EvalCall) (s : EvalState)
    (hc : Completes (evalFuel n c) s) :
    ActHeapKept s.needs ((evalFuel n c).runState s).2.needs :=
  invariant_transfer (fun s t => ActHeapKept s.needs t.needs) (fun _ => ActHeapKept.refl _)
    body_step_actDisc n c s hc

/-- **Every production evaluator operation keeps every entry `evaluating` mark**, over EVERY entry
    state and whatever its outcome (a run that never completes returns its entry state). -/
theorem evalUnbounded_actDisc (c : EvalCall) : ActDisc (evalUnbounded c) :=
  production_preserves (fun s t => ActHeapKept s.needs t.needs) (fun _ => ActHeapKept.refl _)
    body_step_actDisc c

/-- The cell-level reading: a cell `evaluating` at the entry of ANY production operation is
    present and `evaluating` in its retained state, after success or ordinary failure. -/
theorem production_keeps_evaluating (c : EvalCall) (s : EvalState) (a : Nat) (cell : NeedCell)
    (hc : s.needs[a]? = some cell) (hs : cell.state = .evaluating) :
    ∃ cell', ((evalUnbounded c).runState s).2.needs[a]? = some cell' ∧ cell'.state = .evaluating := by
  obtain ⟨cell', h', k⟩ := evalUnbounded_actDisc c s a cell hc
  exact ⟨cell', h', k.active hs⟩

/-- The production plan-route classifier keeps every `evaluating` mark. -/
theorem classify_actDisc (shape : NeedPlan.CallShape) :
    ActDisc (classifyPlanRouteWith resolveDotReceiver? algorithmIntrinsicRoute shape) := by
  unfold classifyPlanRouteWith
  split
  · split
    · exact ActDisc.bind (evalUnbounded_actDisc (.algorithmIntrinsicRoute _ _))
        (fun b => by split <;> exact actDisc_pure _)
    · exact actDisc_pure _
  · exact ActDisc.bind (evalUnbounded_actDisc (.resolveDotReceiver? _ _))
      (fun t => by split <;> first | exact actDisc_throw _ | exact actDisc_pure _)

/-- The public VALUE demand keeps every `evaluating` mark (of OTHER cells: its own cell's mark is
    the one it writes, from a `suspended` entry). -/
theorem demandNeed_actDisc (a : Nat) : ActDisc (demandNeed a) := by
  unfold demandNeed
  apply actDisc_step
  · exact fun e c v => evalUnbounded_actDisc (.evalSuppliedAt a e c v)
  · exact fun e c v => evalUnbounded_actDisc (.evalSupplySpread e c v)
  · exact fun f c => evalUnbounded_actDisc (.resolveCalleeAlg f c)
  · exact fun g c => evalUnbounded_actDisc (.needPlanNormalizeCallee g c)
  · exact fun o g cells c v n => evalUnbounded_actDisc (.evalSuppliedCallCounted o g cells c v n)
  · exact classify_actDisc
  · exact fun b => EvalBody.plannedLinkCallable_actDisc evalUnbounded evalUnbounded_actDisc b
  · exact fun b => evalUnbounded_actDisc (.demandNeedRecursive b)

/-- One production plan execution keeps every `evaluating` mark — in particular its own cell's,
    at the flight state where the completion shell has marked it. -/
theorem execute_actDisc (a : Nat) (shape : NeedPlan.CallShape) :
    ActDisc (NeedPlan.execute productionPlanRoute a shape) :=
  actDisc_execute productionPlanRoute (fun e c v => evalUnbounded_actDisc (.evalSupplySpread e c v))
    (fun f c => evalUnbounded_actDisc (.resolveCalleeAlg f c))
    (fun g c => evalUnbounded_actDisc (.needPlanNormalizeCallee g c))
    (fun o g cells c v n => evalUnbounded_actDisc (.evalSuppliedCallCounted o g cells c v n))
    classify_actDisc
    (fun b => EvalBody.plannedLinkCallable_actDisc evalUnbounded evalUnbounded_actDisc b) a shape

end KatLang.ActiveCells
