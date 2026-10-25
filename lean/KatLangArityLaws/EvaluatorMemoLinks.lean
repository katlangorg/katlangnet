import Lean
import KatLangArityLaws.EvaluatorDiscipline
import KatLangArityLaws.AlgorithmProjection

open KatLang KatLang.CallPlan KatLang.EvaluatorCore KatLang.AlgorithmProjectionLaws

/-!
# FG-M1: completed CALLABLE outcomes and recorded links survive production evaluation

`CellKept` / `HeapKept` / `Disciplined` (`InvocationPlan.lean`, proved for every production
operation by `EvaluatorDiscipline.productionDiscipline_holds`) constrain a cell's suspension,
completed VALUE, prepared supply and recorded route. They say nothing about the three remaining
memo/link fields, so the local reread laws (`NeedControl.Projection.projected_sticky`,
`calleeCell_recorded`, `receiverCell_recorded`) did not by themselves survive an arbitrary
intervening operation. This module adds the COMPANION relation

* `LinkKept c c'`: a completed CALLABLE outcome (`NeedCell.callable = .projected o` — identity,
  successful absence or failure, compared by Lean equality on the whole outcome), a recorded
  canonical callee cell (`NeedCell.callee = some x`) and a recorded receiver cell
  (`NeedCell.receiver = some x`) of `c` are all still present, unchanged, in `c'`;
* `LinkHeapKept h h'`: every cell of `h` is still present at its address in `h'`, `LinkKept`;
* `LinkDisc m`: `m` relates EVERY entry heap to its exit heap by `LinkHeapKept` (successful and
  ordinary-error runs alike: `EvalM.runState` keeps the state of both),

and proves `LinkDisc` for every evaluator body given its recursive answer (`evalStep_linkDisc`),
then transfers it through `invariant_transfer` / `production_preserves` (`evalFuel_linkDisc`,
`evalUnbounded_linkDisc`). The old relation is untouched: `MemoKept` packages both for users.

THE CLAIM IS ENTRY-STATE PRESERVATION, NOT AN IN-FLIGHT FIRST-WRITER LAW. The protected facts are
those present when an operation BEGINS. A `.unprojected` cell may become projected, an absent
link may be established; the guarded writers write only from those entry states:

| writer | field | write condition at its entry read |
| --- | --- | --- |
| `NeedProjection.step` | `callable` (`projecting`, then `projected o`) | entry `callable = .unprojected` |
| `NeedPlan.calleeCell` → `setCallee` | `callee` | entry `callee = none` (route/supply run in between) |
| `NeedLink.receiverCell` → `setReceiver` | `receiver` | entry `receiver = none` (only `supplyNeed` in between) |
| `aliasBareCell` | whole cell `{cell with aliasUse/aliasBare}` | snapshot `cell`; intermediate effects keep cells EXACTLY |
| `takeTerminalAliasInvocation` | whole cell `claimTerminalAliasInitial cell` | immediately after the read |
| VALUE / plan / route / allocation | other fields, or a push | frame |

A value first written INSIDE a re-entrant callback of such a writer (e.g. a callee recorded by
the route classifier's own nested observation) may be overwritten by the enclosing writer's later
publication; that is outside this relation and not claimed (`EvaluatorMemoLinksGuards` pins the
raw-setter boundary). Not claimed either: validity of the recorded addresses (FG-H1), collector
ordering, reachability, projection refinement, or anything about the C# runtime.
-/

namespace KatLang.MemoLinks

/-! ## The relation -/

/-- The three FG-M1 facts of a cell that must survive: a completed CALLABLE outcome, a recorded
    callee cell and a recorded receiver cell. -/
structure LinkKept (c c' : NeedCell) : Prop where
  callable : ∀ o, c.callable = .projected o → c'.callable = .projected o
  callee : ∀ x, c.callee = some x → c'.callee = some x
  receiver : ∀ x, c.receiver = some x → c'.receiver = some x

theorem LinkKept.refl (c : NeedCell) : LinkKept c c := ⟨fun _ h => h, fun _ h => h, fun _ h => h⟩

theorem LinkKept.trans {c d e : NeedCell} (h1 : LinkKept c d) (h2 : LinkKept d e) : LinkKept c e :=
  ⟨fun o h => h2.callable o (h1.callable o h), fun x h => h2.callee x (h1.callee x h),
    fun x h => h2.receiver x (h1.receiver x h)⟩

/-- A write that leaves the three fields alone keeps them. -/
theorem linkKept_of_same (c c' : NeedCell) (hc : c'.callable = c.callable)
    (he : c'.callee = c.callee) (hr : c'.receiver = c.receiver) : LinkKept c c' :=
  ⟨fun _ h => hc ▸ h, fun _ h => he ▸ h, fun _ h => hr ▸ h⟩

def LinkHeapKept (h h' : Array NeedCell) : Prop :=
  ∀ (a : Nat) (c : NeedCell), h[a]? = some c → ∃ c', h'[a]? = some c' ∧ LinkKept c c'

theorem LinkHeapKept.refl (h : Array NeedCell) : LinkHeapKept h h := fun _ c hc => ⟨c, hc, LinkKept.refl c⟩

theorem LinkHeapKept.trans {h1 h2 h3 : Array NeedCell} (k1 : LinkHeapKept h1 h2) (k2 : LinkHeapKept h2 h3) :
    LinkHeapKept h1 h3 := by
  intro a c hc
  obtain ⟨d, hd, kd⟩ := k1 a c hc
  obtain ⟨e, he, ke⟩ := k2 a d hd
  exact ⟨e, he, kd.trans ke⟩

theorem lt_of_get {h : Array NeedCell} {a : Nat} {c : NeedCell} (hc : h[a]? = some c) : a < h.size := by
  rcases Nat.lt_or_ge a h.size with hl | hl
  · exact hl
  · rw [Array.getElem?_eq_none hl] at hc; cases hc

/-- Heap extension by allocation keeps every existing cell exactly. -/
theorem LinkHeapKept.push (h : Array NeedCell) (c : NeedCell) : LinkHeapKept h (h.push c) := by
  intro a d hd
  refine ⟨d, ?_, LinkKept.refl d⟩
  rw [Array.getElem?_push]
  simp [Nat.ne_of_lt (lt_of_get hd), hd]

/-- A write at `a` whose result keeps the three fields of the cell it rewrites. -/
theorem LinkHeapKept.modify (h : Array NeedCell) (a : Nat) (f : NeedCell → NeedCell)
    (hf : ∀ c, h[a]? = some c → LinkKept c (f c)) : LinkHeapKept h (h.modify a f) := by
  intro b c hc
  rw [modify_get]
  by_cases hab : a = b
  · subst hab
    exact ⟨f c, by simp [hc], hf c hc⟩
  · exact ⟨c, by simp [hab, hc], LinkKept.refl c⟩

/-- **The entry-anchored write.** After `h0 ↦ h1` (kept), a write `g` at `a` keeps `h0`'s facts when
    it keeps, for the entry cell `c0` of `a`, every fact `c0` had — even if `g` overwrites a fact
    first established between `h0` and `h1`. -/
theorem LinkHeapKept.modify_anchor {h0 h1 : Array NeedCell} (k : LinkHeapKept h0 h1) (a : Nat)
    (g : NeedCell → NeedCell)
    (hg : ∀ c0 c1, h0[a]? = some c0 → LinkKept c0 c1 → LinkKept c0 (g c1)) :
    LinkHeapKept h0 (h1.modify a g) := by
  intro b c hc
  obtain ⟨c1, hc1, k1⟩ := k b c hc
  rw [modify_get]
  by_cases hab : a = b
  · subst hab
    exact ⟨g c1, by simp [hc1], hg c c1 hc k1⟩
  · exact ⟨c1, by simp [hab, hc1], k1⟩

/-- An off-target or same-field-preserving whole-cell write of the cell CURRENTLY at `a`. -/
theorem LinkHeapKept.set_bang (h : Array NeedCell) (a : Nat) (c c' : NeedCell) (hc : h[a]? = some c)
    (hk : LinkKept c c') : LinkHeapKept h (h.set! a c') := by
  intro b d hd
  have ha := lt_of_get hc
  by_cases hab : a = b
  · subst hab
    rw [hc] at hd; cases hd
    exact ⟨c', by simp [Array.set!, ha], hk⟩
  · exact ⟨d, by simp [Array.set!, hab, hd], LinkKept.refl d⟩

/-- `m` keeps the three fields of every existing cell, over EVERY entry state, whatever its
    outcome (value or ordinary error; the state of both is `runState`'s). -/
def LinkDisc {α : Type} (m : EvalM α) : Prop :=
  ∀ s, LinkHeapKept s.needs (m.runState s).2.needs

/-- Both whole-run heap relations: the established `HeapKept` and the FG-M1 `LinkHeapKept`. -/
def MemoKept (h h' : Array NeedCell) : Prop := HeapKept h h' ∧ LinkHeapKept h h'

theorem MemoKept.refl (h : Array NeedCell) : MemoKept h h := ⟨HeapKept.refl h, LinkHeapKept.refl h⟩

theorem MemoKept.trans {h1 h2 h3 : Array NeedCell} (k1 : MemoKept h1 h2) (k2 : MemoKept h2 h3) :
    MemoKept h1 h3 := ⟨k1.1.trans k2.1, k1.2.trans k2.2⟩

/-- A kept cell is still present at its address, with both relations' facts. -/
theorem MemoKept.cell {h h' : Array NeedCell} (k : MemoKept h h') (a : Nat) (c : NeedCell)
    (hc : h[a]? = some c) : ∃ c', h'[a]? = some c' ∧ CellKept c c' ∧ LinkKept c c' := by
  obtain ⟨c1, hc1, k1⟩ := k.1 a c hc
  obtain ⟨c2, hc2, k2⟩ := k.2 a c hc
  rw [hc1] at hc2; cases hc2
  exact ⟨c1, hc1, k1, k2⟩

theorem linkDisc_of_needs {α : Type} (m : EvalM α)
    (h : ∀ s, (m.runState s).2.needs = s.needs) : LinkDisc m := by
  intro s; rw [h s]; exact LinkHeapKept.refl _

theorem LinkDisc.bind {α β : Type} {m : EvalM α} {f : α → EvalM β}
    (hm : LinkDisc m) (hf : ∀ x, LinkDisc (f x)) : LinkDisc (m >>= f) := by
  intro s
  rw [bind_run]
  have k := hm s
  cases hr : m.runState s with
  | mk out t =>
    rw [hr] at k
    cases out with
    | error e => exact k
    | ok x => exact k.trans (hf x t)

theorem LinkDisc.map {α β : Type} {m : EvalM α} (f : α → β) (hm : LinkDisc m) : LinkDisc (f <$> m) := by
  intro s
  rw [map_run]
  have k := hm s
  cases hr : m.runState s with
  | mk out t => rw [hr] at k; cases out <;> exact k

theorem linkDisc_pure {α : Type} (a : α) : LinkDisc (pure a : EvalM α) := linkDisc_of_needs _ (fun _ => rfl)
theorem linkDisc_get : LinkDisc (get : EvalM EvalState) := linkDisc_of_needs _ (fun _ => rfl)
theorem linkDisc_throw {α : Type} (e : Error) : LinkDisc (throw e : EvalM α) := linkDisc_of_needs _ (fun _ => rfl)
theorem linkDisc_evalError {α : Type} (e : Error) : LinkDisc (EvalM.error e : EvalM α) :=
  linkDisc_of_needs _ (fun _ => rfl)
theorem linkDisc_lift {α : Type} (o : Except Error α) : LinkDisc (monadLift o : EvalM α) :=
  linkDisc_of_needs _ (fun s => by rw [lift_run])

theorem LinkDisc.attempt {α : Type} {m : EvalM α} (hm : LinkDisc m) : LinkDisc (evalAttempt m) := by
  intro s; rw [evalAttempt_run]; split <;> exact hm s

theorem LinkDisc.withCtx {α : Type} {m : EvalM α} (c : String) (hm : LinkDisc m) : LinkDisc (withCtx c m) := by
  unfold KatLang.withCtx
  refine LinkDisc.bind hm.attempt (fun r => ?_)
  cases r with
  | ok x => exact linkDisc_pure x
  | error e => exact linkDisc_evalError _

theorem LinkDisc.withNestedMissingOutput {α : Type} {m : EvalM α} (hm : LinkDisc m) :
    LinkDisc (withNestedMissingOutput m) := by
  unfold KatLang.withNestedMissingOutput
  refine LinkDisc.bind hm.attempt (fun r => ?_)
  cases r with
  | ok x => exact linkDisc_pure x
  | error e => exact linkDisc_evalError _

theorem LinkDisc.captureMeta (name : Ident) {m : EvalM Nat} (hm : LinkDisc m) :
    LinkDisc (NeedBinder.captureMeta name m) := by
  intro s
  have k := hm s
  show LinkHeapKept s.needs ((NeedBinder.captureMeta name m).runState s).2.needs
  rw [NeedBinder.captureMeta_runState]
  revert k
  rcases m.runState s with ⟨r, t⟩
  intro k
  cases r <;> exact k

theorem linkDisc_allocate (suspension : NeedSuspension) : LinkDisc (allocateNeed suspension) := by
  intro s; rw [KatLang.NeedControl.Allocation.allocate_run]; exact LinkHeapKept.push _ _

theorem linkDisc_supply (source : Expr) (caller : EvalCtx) (values : ValEnv) :
    LinkDisc (supplyNeed source caller values) := by
  intro s
  rcases supply_cases source caller values s with h | h <;> rw [h]
  · exact LinkHeapKept.refl _
  · exact LinkHeapKept.push _ _

theorem linkDisc_mapM {α β : Type} (f : α → EvalM β) (hf : ∀ x, LinkDisc (f x)) (xs : List α) :
    LinkDisc (xs.mapM f) := by
  suffices h : ∀ (acc : List β), LinkDisc (List.mapM.loop f xs acc) from h []
  induction xs with
  | nil => intro acc; exact linkDisc_pure _
  | cons x rest ih => intro acc; exact LinkDisc.bind (hf x) (fun y => ih (y :: acc))

/-- A frame write: a state write that keeps the three fields everywhere. -/
theorem link_modify (f : EvalState → EvalState) (h : ∀ s : EvalState, LinkHeapKept s.needs (f s).needs) :
    LinkDisc (modify f : EvalM Unit) := fun s => h s

/-! ## Reads followed by writes (entry-anchored) -/

def LinkAt {α : Type} (st : EvalState) (m : EvalM α) : Prop := LinkHeapKept st.needs (m.runState st).2.needs

theorem link_get_bind {β : Type} (f : EvalState → EvalM β) (h : ∀ st, LinkAt st (f st)) :
    LinkDisc (get >>= f) := by
  intro s; rw [bind_run, get_run]; exact h s

theorem LinkAt.of_disc {α : Type} {st : EvalState} {m : EvalM α} (h : LinkDisc m) : LinkAt st m := h st

theorem LinkAt.bind {α β : Type} {st : EvalState} {m : EvalM α} {f : α → EvalM β}
    (hm : LinkAt st m) (hf : ∀ x, LinkDisc (f x)) : LinkAt st (m >>= f) := by
  unfold LinkAt at *
  rw [bind_run]
  cases hr : m.runState st with
  | mk out t =>
    rw [hr] at hm
    cases out with
    | error e => exact hm
    | ok x => exact hm.trans (hf x t)

theorem LinkAt.set {st t : EvalState} (h : LinkHeapKept st.needs t.needs) : LinkAt st (set t : EvalM PUnit) := h

/-! ## Loops -/

theorem link_forIn'_loop {α β : Type} (as : List α) (f : (a : α) → a ∈ as → β → EvalM (ForInStep β))
    (hf : ∀ a h b, LinkDisc (f a h b)) :
    ∀ (as' : List α) (b : β) (h : ∃ bs, bs ++ as' = as), LinkDisc (List.forIn'.loop as f as' b h)
  | [], b, h => by unfold List.forIn'.loop; exact linkDisc_pure _
  | a :: as', b, h => by
    unfold List.forIn'.loop
    apply LinkDisc.bind (hf _ _ _)
    intro r
    cases r with
    | done b => exact linkDisc_pure _
    | yield b => exact link_forIn'_loop as f hf as' b _

theorem link_forIn {α β : Type} (xs : List α) (init : β) (f : α → β → EvalM (ForInStep β))
    (h : ∀ a b, LinkDisc (f a b)) : LinkDisc (forIn xs init f) :=
  link_forIn'_loop xs (fun a _ b => f a b) (fun a _ b => h a b) xs init ⟨[], rfl⟩

theorem link_forM {α : Type} (xs : List α) (f : α → EvalM PUnit) (h : ∀ a, LinkDisc (f a)) :
    LinkDisc (xs.forM f) := by
  induction xs with
  | nil => exact linkDisc_pure _
  | cons x xs ih => unfold List.forM; exact LinkDisc.bind (h x) (fun _ => ih)

theorem link_foldlM {α β : Type} (f : β → α → EvalM β) (h : ∀ b a, LinkDisc (f b a))
    (init : β) (xs : List α) : LinkDisc (xs.foldlM f init) := by
  induction xs generalizing init with
  | nil => exact linkDisc_pure _
  | cons x xs ih => unfold List.foldlM; exact LinkDisc.bind (h _ _) (fun b => ih b)

/-! ## Supply formation, preparation, routes (frame writes) -/

theorem linkDisc_slice (operand : Expr) (ctx : EvalCtx) : LinkDisc (spreadCollectorSlice? operand ctx) :=
  linkDisc_of_needs _ (fun s => by rw [spread_slice_readonly])

theorem linkDisc_source (a : Nat) : LinkDisc (needWrittenSource? a) :=
  linkDisc_of_needs _ (fun s => by rw [KatLang.NeedControl.Provenance.source_run])

theorem linkDisc_slot (ev : NeedSupply.SpreadEval) (hev : ∀ e c v, LinkDisc (ev e c v))
    (ctx : EvalCtx) (env : ValEnv) (e : Expr) : LinkDisc (NeedSupply.slot ev ctx env e) := by
  cases e with
  | sequenceSpread operand =>
    refine LinkDisc.bind (linkDisc_slice operand ctx) (fun known => ?_)
    cases known with
    | some slice =>
      exact linkDisc_mapM _ (fun a => LinkDisc.bind (linkDisc_source a) (fun _ => linkDisc_pure _)) slice
    | none =>
      refine LinkDisc.bind (hev _ _ _) (fun supplied => ?_)
      cases supplied with
      | items values =>
        exact linkDisc_mapM _ (fun v => LinkDisc.bind (linkDisc_allocate _) (fun _ => linkDisc_pure _)) values
      | cells cells => exact linkDisc_pure _
  | _ => exact LinkDisc.bind (linkDisc_supply _ _ _) (fun _ => linkDisc_pure _)

theorem linkDisc_form (ev : NeedSupply.SpreadEval) (hev : ∀ e c v, LinkDisc (ev e c v))
    (ctx : EvalCtx) (env : ValEnv) (args : OutputBundle) : LinkDisc (NeedSupply.form ev ctx env args) := by
  induction args with
  | nil => exact linkDisc_pure _
  | cons e rest ih =>
    exact LinkDisc.bind (linkDisc_slot ev hev ctx env e) (fun _ => LinkDisc.bind ih (fun _ => linkDisc_pure _))

theorem link_frame (a : Nat) (g : NeedCell → NeedCell)
    (hg : ∀ c, (g c).callable = c.callable ∧ (g c).callee = c.callee ∧ (g c).receiver = c.receiver) :
    LinkDisc (modify fun s => { s with needs := s.needs.modify a g } : EvalM Unit) :=
  link_modify _ (fun _ => LinkHeapKept.modify _ a _ (fun c _ =>
    linkKept_of_same _ _ (hg c).1 (hg c).2.1 (hg c).2.2))

theorem linkDisc_setSupply (a : Nat) (p : NeedPlanSupply) : LinkDisc (NeedPlan.setSupply a p) :=
  link_frame a _ (fun _ => ⟨rfl, rfl, rfl⟩)

theorem linkDisc_setRoute (a : Nat) (r : PlanRoute) : LinkDisc (NeedPlan.setRoute a r) :=
  link_frame a _ (fun _ => ⟨rfl, rfl, rfl⟩)

/-- Preparation writes only the plan record: a frame over its formation. -/
theorem linkDisc_prepare (ev : NeedSupply.SpreadEval) (hev : ∀ e c v, LinkDisc (ev e c v))
    (a : Nat) (shape : NeedPlan.CallShape) : LinkDisc (NeedPlan.prepare ev a shape) := by
  unfold NeedPlan.prepare
  refine LinkDisc.bind linkDisc_get (fun st => ?_)
  split
  · split
    · exact linkDisc_lift _
    · exact linkDisc_throw _
    · exact LinkDisc.bind (linkDisc_setSupply _ _) (fun _ =>
        LinkDisc.bind (linkDisc_form ev hev _ _ _).attempt (fun _ =>
          LinkDisc.bind (linkDisc_setSupply _ _) (fun _ => linkDisc_lift _)))
  · exact linkDisc_throw _

theorem linkDisc_routeOf (classify : NeedPlan.CallShape → EvalM PlanRoute)
    (hclassify : ∀ shape, LinkDisc (classify shape)) (a : Nat) (shape : NeedPlan.CallShape) :
    LinkDisc (NeedPlan.routeOf classify a shape) := by
  unfold NeedPlan.routeOf
  refine LinkDisc.bind linkDisc_get (fun st => ?_)
  split
  · split
    · exact linkDisc_pure _
    · exact LinkDisc.bind (hclassify _) (fun r => LinkDisc.bind linkDisc_get (fun _ => by
        split
        · exact linkDisc_pure _
        · exact LinkDisc.bind (linkDisc_setRoute _ _) (fun _ => linkDisc_pure _)))
  · exact linkDisc_throw _

/-! ## The three guarded writers -/

/-- **CALLABLE publication keeps entry facts.** A completed outcome is returned with no write; an
    active projection is a cycle with no write; only an UNPROJECTED entry cell is marked
    `projecting` and later published — over the callback's final state, whose other cells and
    whose callee/receiver fields of `a` the callback keeps. -/
theorem linkDisc_projectionStep (project : NeedSuspension → EvalM (Option Algorithm))
    (hp : ∀ x, LinkDisc (project x)) (a : Nat) : LinkDisc (NeedProjection.step project a) := by
  intro s
  cases hc : s.needs[a]? with
  | none =>
    rw [KatLang.NeedControl.Projection.invalid_address project a s hc]; exact LinkHeapKept.refl _
  | some cell =>
    cases hs : cell.callable with
    | projected o =>
      rw [KatLang.NeedControl.Projection.projected_sticky project a s cell o hc hs]
      exact LinkHeapKept.refl _
    | projecting =>
      rw [KatLang.NeedControl.Projection.projecting_reentry_cycle project a s cell hc hs]
      exact LinkHeapKept.refl _
    | unprojected =>
      -- the `projecting` mark: the entry cell had no completed outcome
      have k1 : LinkHeapKept s.needs (KatLang.NeedControl.Projection.setCallable a .projecting s).needs :=
        LinkHeapKept.modify _ a _ (fun c hc' => by
          rw [hc] at hc'; cases hc'
          exact ⟨fun o h => (by rw [hs] at h; cases h), fun _ h => h, fun _ h => h⟩)
      have k2 := hp cell.suspension (KatLang.NeedControl.Projection.setCallable a .projecting s)
      generalize hr : (project cell.suspension).runState
        (KatLang.NeedControl.Projection.setCallable a .projecting s) = r at k2
      rcases r with ⟨outcome, t⟩
      have k12 := k1.trans k2
      cases hinc : outcome.isIncomplete with
      | false =>
        rw [KatLang.NeedControl.Projection.unprojected_publishes project a s t cell outcome hc hs hr hinc]
        exact LinkHeapKept.modify_anchor k12 a _ (fun c0 c1 h0 kk => by
          rw [hc] at h0; cases h0
          exact ⟨fun o h => (by rw [hs] at h; cases h), kk.callee, kk.receiver⟩)
      | true =>
        have hrun : (NeedProjection.step project a).runState s = (.error .fuelExhausted, t) := by
          simp only [NeedProjection.step, bind_run, get_run, hc, hs, EvalM.modify_runState]
          simp only [KatLang.NeedControl.Projection.setCallable] at hr
          rw [evalAttempt_run, hr]
          simp only [hinc, if_true]
        rw [hrun]; exact k12

/-- **Callee establishment keeps entry facts.** A recorded callee is returned with no write; an
    unrecorded one is established after the route and the one supply — the record overwrites at
    most a callee recorded DURING that work (an in-flight fact, not an entry fact). -/
theorem linkDisc_calleeCell (classify : NeedPlan.CallShape → EvalM PlanRoute)
    (hclassify : ∀ shape, LinkDisc (classify shape)) (a : Nat) :
    LinkDisc (NeedPlan.calleeCell classify a) := by
  intro s
  cases hc : s.needs[a]? with
  | none =>
    have : (NeedPlan.calleeCell classify a).runState s = (.error (.illegalInEval "invalid need address"), s) := by
      simp only [NeedPlan.calleeCell, bind_run, get_run, hc]; rfl
    rw [this]; exact LinkHeapKept.refl _
  | some cell =>
    cases hcal : cell.callee with
    | some x => rw [calleeCell_recorded classify a x s cell hc hcal]; exact LinkHeapKept.refl _
    | none =>
      cases hshape : NeedPlan.ofSuspension? cell.suspension with
      | none =>
        have : (NeedPlan.calleeCell classify a).runState s = (.error NeedPlan.metaRefusal, s) := by
          simp only [NeedPlan.calleeCell, bind_run, get_run, hc, hcal, hshape]; rfl
        rw [this]; exact LinkHeapKept.refl _
      | some shape =>
        rw [calleeCell_unrecorded classify a s cell shape hc hcal hshape]
        have k1 := linkDisc_routeOf classify hclassify a shape s
        rcases hro : (NeedPlan.routeOf classify a shape).runState s with ⟨_ | r, t⟩ <;> rw [hro] at k1
        · exact k1
        · dsimp only
          split
          · exact k1
          · have k2 := linkDisc_supply (NeedPlan.effective shape r).callee shape.caller shape.values t
            rcases hsu : (supplyNeed (NeedPlan.effective shape r).callee shape.caller shape.values).runState t
              with ⟨_ | x, u⟩ <;> rw [hsu] at k2
            · exact k1.trans k2
            · exact LinkHeapKept.modify_anchor (k1.trans k2) a _ (fun c0 c1 h0 kk => by
                rw [hc] at h0; cases h0
                exact ⟨kk.callable, fun y h => (by rw [hcal] at h; cases h), kk.receiver⟩)

/-- **Receiver establishment keeps entry facts**: the one supply between the read and the record. -/
theorem linkDisc_receiverCell (a : Nat) : LinkDisc (NeedLink.receiverCell a) := by
  intro s
  cases hc : s.needs[a]? with
  | none =>
    have : (NeedLink.receiverCell a).runState s = (.error (.illegalInEval "invalid need address"), s) := by
      simp only [NeedLink.receiverCell, bind_run, get_run, hc]; rfl
    rw [this]; exact LinkHeapKept.refl _
  | some cell =>
    cases hrec : cell.receiver with
    | some x => rw [receiverCell_recorded a x s cell hc hrec]; exact LinkHeapKept.refl _
    | none =>
      have hother : ∀ (e : Error), (NeedLink.receiverCell a).runState s = (.error e, s) →
          LinkHeapKept s.needs ((NeedLink.receiverCell a).runState s).2.needs := by
        intro e h; rw [h]; exact LinkHeapKept.refl _
      cases hsusp : cell.suspension with
      | expression source caller values =>
        cases hl : linkEdge? source with
        | none =>
          apply hother (.illegalInEval "not a link")
          simp only [NeedLink.receiverCell, bind_run, get_run, hc, hrec, hsusp, hl]; rfl
        | some p =>
          rcases p with ⟨receiver, fallback⟩
          rw [receiverCell_establishes a s cell source receiver fallback caller values hc hrec hsusp hl]
          have k := linkDisc_supply receiver caller values s
          rcases hsu : (supplyNeed receiver caller values).runState s with ⟨_ | x, u⟩ <;> rw [hsu] at k
          · exact k
          · exact LinkHeapKept.modify_anchor k a _ (fun c0 c1 h0 kk => by
              rw [hc] at h0; cases h0
              exact ⟨kk.callable, kk.callee, fun y h => (by rw [hrec] at h; cases h)⟩)
      | ready v =>
        apply hother (.illegalInEval "not a link")
        simp only [NeedLink.receiverCell, bind_run, get_run, hc, hrec, hsusp]; rfl
      | collector sl =>
        apply hother (.illegalInEval "not a link")
        simp only [NeedLink.receiverCell, bind_run, get_run, hc, hrec, hsusp]; rfl


/-! ## The shared link decoder and its two channels -/

/-- Both link channels preserve entry facts through the same decoder, provided its route
    classifier and receiver demand do. No contract on the returned addresses is needed here. -/
theorem linkDisc_decodeCallee (classify : NeedPlan.CallShape → EvalM PlanRoute)
    (hclassify : ∀ shape, LinkDisc (classify shape))
    (demand : Nat → EvalM CountedResult) (hdemand : ∀ a, LinkDisc (demand a)) (a : Nat) :
    LinkDisc (NeedLink.decodeCallee classify demand a) := by
  unfold NeedLink.decodeCallee
  refine LinkDisc.bind (linkDisc_receiverCell a) (fun receiver => ?_)
  refine LinkDisc.bind (hdemand receiver) (fun value => ?_)
  refine LinkDisc.bind ?_ (fun plan => linkDisc_calleeCell classify hclassify plan)
  cases value.1 <;> first | exact linkDisc_pure _ | exact linkDisc_evalError _

/-- The VALUE link channel adds only the callee's VALUE demand to the shared decoder. -/
theorem linkDisc_linkValue (classify : NeedPlan.CallShape → EvalM PlanRoute)
    (hclassify : ∀ shape, LinkDisc (classify shape))
    (demand : Nat → EvalM CountedResult) (hdemand : ∀ a, LinkDisc (demand a)) (a : Nat) :
    LinkDisc (NeedLink.value classify demand a) :=
  LinkDisc.bind (linkDisc_decodeCallee classify hclassify demand hdemand a) hdemand

/-- The CALLABLE link channel adds only the callee's CALLABLE projection to the shared decoder. -/
theorem linkDisc_linkCallable (classify : NeedPlan.CallShape → EvalM PlanRoute)
    (hclassify : ∀ shape, LinkDisc (classify shape))
    (demand : Nat → EvalM CountedResult) (hdemand : ∀ a, LinkDisc (demand a))
    (project : Nat → EvalM (Option Algorithm)) (hproject : ∀ a, LinkDisc (project a)) (a : Nat) :
    LinkDisc (NeedLink.callable classify demand project a) :=
  LinkDisc.bind (linkDisc_decodeCallee classify hclassify demand hdemand a) hproject

/-! ## Plan execution, the VALUE shell, META, invocation, capture and the argument view -/

theorem linkDisc_calleeAlong (route : NeedPlan.Route)
    (htarget : ∀ f c, LinkDisc (route.target f c))
    (hclassify : ∀ shape, LinkDisc (route.classify shape))
    (hproject : ∀ c, LinkDisc (route.project c))
    (a : Nat) (eff : NeedPlan.CallShape) (r : PlanRoute) :
    LinkDisc (NeedPlan.calleeAlong route a eff r) := by
  cases r with
  | algorithm =>
    simp only [NeedPlan.calleeAlong]
    refine LinkDisc.bind (linkDisc_calleeCell route.classify hclassify a) (fun c => ?_)
    refine LinkDisc.bind (hproject c) (fun o => ?_)
    cases o with
    | some _ => exact linkDisc_pure _
    | none => exact linkDisc_throw _
  | intrinsic => exact linkDisc_throw _
  | call => exact htarget _ _
  | extension => exact htarget _ _

theorem linkDisc_executeAlong (route : NeedPlan.Route)
    (hspread : ∀ e c v, LinkDisc (route.spread e c v))
    (htarget : ∀ f c, LinkDisc (route.target f c))
    (hnormal : ∀ g c, LinkDisc (route.normalize g c))
    (hdispatch : ∀ o g cells c v n, LinkDisc (route.dispatch o g cells c v n))
    (hclassify : ∀ shape, LinkDisc (route.classify shape))
    (hproject : ∀ c, LinkDisc (route.project c))
    (a : Nat) (shape : NeedPlan.CallShape) (r : PlanRoute) :
    LinkDisc (NeedPlan.executeAlong route a shape r) := by
  unfold NeedPlan.executeAlong NeedPlan.dispatchName NeedPlan.dispatchOrigin
  exact LinkDisc.bind (LinkDisc.withCtx _ (linkDisc_calleeAlong route htarget hclassify hproject a _ r)) (fun _ =>
    LinkDisc.bind (LinkDisc.bind linkDisc_get (fun _ => linkDisc_pure _)) (fun _ =>
    LinkDisc.bind (LinkDisc.bind linkDisc_get (fun _ => linkDisc_pure _)) (fun _ =>
    LinkDisc.bind (LinkDisc.withCtx _ (LinkDisc.bind (hnormal _ _) (fun _ =>
      LinkDisc.bind (linkDisc_prepare route.spread hspread a _) (fun _ => hdispatch _ _ _ _ _ _))))
      (fun _ => linkDisc_pure _))))

theorem linkDisc_execute (route : NeedPlan.Route)
    (hspread : ∀ e c v, LinkDisc (route.spread e c v))
    (htarget : ∀ f c, LinkDisc (route.target f c))
    (hnormal : ∀ g c, LinkDisc (route.normalize g c))
    (hdispatch : ∀ o g cells c v n, LinkDisc (route.dispatch o g cells c v n))
    (hclassify : ∀ shape, LinkDisc (route.classify shape))
    (hproject : ∀ c, LinkDisc (route.project c))
    (a : Nat) (shape : NeedPlan.CallShape) :
    LinkDisc (NeedPlan.execute route a shape) := by
  unfold NeedPlan.execute
  refine LinkDisc.bind (LinkDisc.withCtx _ (linkDisc_routeOf route.classify hclassify a shape)) (fun r => ?_)
  cases r with
  | intrinsic => exact linkDisc_throw _
  | _ => exact linkDisc_executeAlong route hspread htarget hnormal hdispatch hclassify hproject a shape _

theorem linkDisc_suspendedValue (ev : Expr → EvalCtx → ValEnv → EvalM CountedResult)
    (route : NeedPlan.Route) (demand : Nat → EvalM CountedResult)
    (hev : ∀ e c v, LinkDisc (ev e c v))
    (hspread : ∀ e c v, LinkDisc (route.spread e c v))
    (htarget : ∀ f c, LinkDisc (route.target f c))
    (hnormal : ∀ g c, LinkDisc (route.normalize g c))
    (hdispatch : ∀ o g cells c v n, LinkDisc (route.dispatch o g cells c v n))
    (hclassify : ∀ shape, LinkDisc (route.classify shape))
    (hproject : ∀ c, LinkDisc (route.project c))
    (hdemand : ∀ b, LinkDisc (demand b)) (a : Nat) (suspension : NeedSuspension) :
    LinkDisc (NeedDemand.suspendedValue ev route demand a suspension) := by
  cases suspension with
  | ready value => exact linkDisc_pure _
  | expression e c v =>
    simp only [NeedDemand.suspendedValue]
    split
    · refine LinkDisc.bind (LinkDisc.withCtx _ (linkDisc_routeOf route.classify hclassify a _)) (fun r => ?_)
      cases r with
      | intrinsic => exact LinkDisc.map _ (hev e c v)
      | _ => exact linkDisc_executeAlong route hspread htarget hnormal hdispatch hclassify hproject a _ _
    · exact LinkDisc.map _ (hev e c v)
  | collector slice =>
    exact LinkDisc.withNestedMissingOutput
      (LinkDisc.bind (linkDisc_mapM _ (fun b => LinkDisc.map _ (hdemand b)) slice)
        (fun _ => linkDisc_pure _))

/-- The VALUE completion shell writes only the VALUE state: a frame over its computation. -/
theorem linkDisc_step (ev : Expr → EvalCtx → ValEnv → EvalM CountedResult)
    (route : NeedPlan.Route) (demand : Nat → EvalM CountedResult)
    (hev : ∀ e c v, LinkDisc (ev e c v))
    (hspread : ∀ e c v, LinkDisc (route.spread e c v))
    (htarget : ∀ f c, LinkDisc (route.target f c))
    (hnormal : ∀ g c, LinkDisc (route.normalize g c))
    (hdispatch : ∀ o g cells c v n, LinkDisc (route.dispatch o g cells c v n))
    (hclassify : ∀ shape, LinkDisc (route.classify shape))
    (hproject : ∀ c, LinkDisc (route.project c))
    (hdemand : ∀ b, LinkDisc (demand b)) (a : Nat) :
    LinkDisc (NeedDemand.step ev route demand a) := by
  unfold NeedDemand.step
  refine LinkDisc.bind linkDisc_get (fun st => ?_)
  split
  · split
    · exact linkDisc_lift _
    · exact linkDisc_throw _
    · exact LinkDisc.bind (link_frame a _ (fun _ => ⟨rfl, rfl, rfl⟩)) (fun _ =>
        LinkDisc.bind (linkDisc_suspendedValue ev route demand hev hspread htarget hnormal hdispatch
          hclassify hproject hdemand a _).attempt (fun _ =>
          LinkDisc.bind (link_frame a _ (fun _ => ⟨rfl, rfl, rfl⟩)) (fun _ => linkDisc_lift _)))
  · exact linkDisc_throw _

theorem linkDisc_reify (a : Nat) : LinkDisc (NeedPlan.reify a) :=
  linkDisc_of_needs _ (fun s => by rw [reify_inert])

theorem linkDisc_invoke (route : NeedPlan.Route)
    (hspread : ∀ e c v, LinkDisc (route.spread e c v))
    (htarget : ∀ f c, LinkDisc (route.target f c))
    (hnormal : ∀ g c, LinkDisc (route.normalize g c))
    (hdispatch : ∀ o g cells c v n, LinkDisc (route.dispatch o g cells c v n))
    (hclassify : ∀ shape, LinkDisc (route.classify shape))
    (hproject : ∀ c, LinkDisc (route.project c))
    (r : NeedPlan.CallReference) : LinkDisc (NeedPlan.invoke route r) := by
  unfold NeedPlan.invoke
  refine LinkDisc.bind linkDisc_get (fun st => ?_)
  split
  · exact linkDisc_execute route hspread htarget hnormal hdispatch hclassify hproject _ _
  · exact linkDisc_throw _

theorem linkDisc_reference (a : Nat) : LinkDisc (NeedPlan.reference a) := by
  intro s
  rw [KatLang.CallReferenceLaws.reference_run]
  cases NeedPlan.reifyResult s.needs a with
  | error e => exact LinkHeapKept.refl _
  | ok r => exact LinkHeapKept.push _ _

theorem linkDisc_viewCells (sp : NeedSupply.SpreadEval) (hsp : ∀ e c v, LinkDisc (sp e c v))
    (classify : NeedPlan.CallShape → EvalM PlanRoute) (hclassify : ∀ shape, LinkDisc (classify shape))
    (a : Nat) : LinkDisc (NeedPlan.viewCells sp classify a) := by
  unfold NeedPlan.viewCells
  refine LinkDisc.bind linkDisc_get (fun st => ?_)
  split
  · refine LinkDisc.bind (linkDisc_routeOf classify hclassify a _) (fun r => ?_)
    split
    · exact LinkDisc.bind (linkDisc_throw _) (fun _ => linkDisc_prepare sp hsp a _)
    · exact linkDisc_prepare sp hsp a _
  · exact linkDisc_throw _

/-! ## The D4 alias writes -/

theorem linkKept_of_claim (cell claimed : NeedCell) (h : claimTerminalAliasInitial cell = some claimed) :
    LinkKept cell claimed := by
  unfold claimTerminalAliasInitial at h
  split at h
  · cases h; exact linkKept_of_same _ _ rfl rfl rfl
  · cases h

open KatLang.EvaluatorDiscipline in
/-- The bare-cell write stores back a cell read BEFORE three intermediate operations; it keeps the
    three fields because those operations keep every existing cell EXACTLY (they only push). -/
theorem link_aliasBareTail (wired : Algorithm) (target : Expr) (ctx : EvalCtx) (address : Nat)
    (cell : NeedCell) (t : EvalState) (hc : t.needs[address]? = some cell) :
    LinkAt t (do
      let bindingCtx ← EvalCtx.bindParameters [] ctx
      let declaringCtx ← enterAlgorithmBody wired bindingCtx []
      let bare ← supplyNeed target declaringCtx []
      modify fun s => { s with needs := s.needs.set! address { cell with aliasBare := some bare } }
      pure bare : EvalM Nat) := by
  unfold LinkAt
  rw [bind_run]
  generalize hb : (EvalCtx.bindParameters [] ctx).runState t = rb
  have hb1 : rb.2.needs = t.needs := by rw [← hb]; exact needs_bindParameters [] ctx t
  rcases rb with ⟨ob, t1⟩
  cases ob with
  | error e => simp only at hb1 ⊢; rw [hb1]; exact LinkHeapKept.refl _
  | ok bindingCtx =>
    simp only at hb1 ⊢
    rw [bind_run]
    generalize he : (enterAlgorithmBody wired bindingCtx []).runState t1 = re
    have he1 : re.2.needs = t1.needs := by rw [← he]; exact needs_enterAlgorithmBody wired bindingCtx [] t1
    rcases re with ⟨oe, t2⟩
    cases oe with
    | error e => simp only at he1 ⊢; rw [he1, hb1]; exact LinkHeapKept.refl _
    | ok declaringCtx =>
      simp only at he1 ⊢
      rw [bind_run]
      have hc2 : t2.needs[address]? = some cell := by rw [he1, hb1]; exact hc
      have kp : LinkHeapKept t.needs ((supplyNeed target declaringCtx []).runState t2).2.needs := by
        intro b d hd
        refine ⟨d, ?_, LinkKept.refl d⟩
        apply supply_keeps_cells
        rw [he1, hb1]; exact hd
      have hc3 := supply_keeps_cells target declaringCtx [] t2 address cell hc2
      generalize hs : (supplyNeed target declaringCtx []).runState t2 = rs at kp hc3
      rcases rs with ⟨os, t3⟩
      cases os with
      | error e => exact kp
      | ok bare =>
        simp only at kp hc3 ⊢
        rw [bind_run, modify_run]
        exact kp.trans (LinkHeapKept.set_bang _ _ _ _ hc3 (linkKept_of_same _ _ rfl rfl rfl))

theorem link_aliasBareCell (wired : Algorithm) (target : Expr) (ctx : EvalCtx)
    (hbind : LinkDisc (aliasBindingCell wired target ctx)) :
    LinkDisc (aliasBareCell wired target ctx) := by
  unfold aliasBareCell
  apply LinkDisc.bind hbind
  intro address
  apply link_get_bind
  intro st
  split
  · rename_i cell hcell
    split
    · apply LinkAt.bind
      · exact LinkAt.set (LinkHeapKept.set_bang _ _ _ _ hcell (linkKept_of_same _ _ rfl rfl rfl))
      · intro _; exact linkDisc_pure _
    · split
      · exact LinkAt.of_disc (linkDisc_pure _)
      · exact link_aliasBareTail wired target ctx address cell st hcell
  · exact LinkAt.of_disc (linkDisc_pure _)


/-! ## The syntax-directed per-body procedure (the `EvaluatorDiscipline` procedure over `LinkDisc`) -/

open Lean Meta Elab Tactic in
/-- Unfolds the head constant of the computation in a `LinkDisc` goal (a total helper with
    no lemma of its own), so the syntax-directed procedure can continue inside it. -/
elab "link_unfold_head" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let ty ← instantiateMVars (← goal.getType)
    let_expr KatLang.MemoLinks.LinkDisc _ m := ty | throwError "link_unfold_head: not a link-discipline goal"
    let m := m.headBeta
    let some c := m.getAppFn.constName? | throwError "link_unfold_head: no head constant"
    if c ∈ [``Bind.bind, ``Pure.pure, ``Functor.map, ``KatLang.evalAttempt, ``ForIn.forIn,
        ``MonadState.get, ``MonadStateOf.get, ``MonadState.set, ``MonadStateOf.set,
        ``MonadState.modifyGet, ``modify, ``get, ``set, ``List.forM, ``List.mapM, ``List.foldlM] then
      throwError "link_unfold_head: combinator"
    let g' ← Lean.Meta.unfoldTarget goal c
    let ty' ← instantiateMVars (← g'.getType)
    if (ty'.find? (fun e => e.isConstOf c)).isSome then
      throwError "link_unfold_head: recursive definition"
    replaceMainGoal [g']

open Lean Meta Elab Tactic in
/-- Closes `LinkDisc (rec c)` from a hypothesis `∀ c, LinkDisc (rec c)`. -/
elab "link_rec" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let ty ← instantiateMVars (← goal.getType)
    let_expr KatLang.MemoLinks.LinkDisc _ m := ty | throwError "link_rec: not a link-discipline goal"
    let m := m.headBeta
    unless m.isApp && m.appFn!.isFVar do throwError "link_rec: not a recursive call"
    let f := m.appFn!
    for d in (← getLCtx) do
      unless d.isImplementationDetail do
        let t ← instantiateMVars d.type
        if t.isForall then
          let body := t.bindingBody!
          if let some (_, m') := body.app2? ``KatLang.MemoLinks.LinkDisc then
            if m'.isApp && m'.appFn! == f && m'.appArg! == .bvar 0 then
              goal.assign (mkApp d.toExpr m.appArg!)
              return
    throwError "link_rec: no hypothesis"

open Lean Meta Elab Tactic in
/-- Closes a goal from a local hypothesis, instantiating its leading universal binders, at
    reducible transparency (cheap: never evaluates a computation). -/
elab "link_hyp" : tactic => do
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
  unless ok do throwError "link_hyp: no hypothesis"

open Lean Meta Elab Tactic in
/-- Zeta-reduces the top-level local definitions (`let`/`have`) of the computation in a
    `LinkDisc`/`LinkAt` goal, and nothing else. -/
elab "link_zeta" : tactic => do
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
    if n == 0 then throwError "link_zeta: no local definition"
    replaceMainGoal [← goal.replaceTargetDefEq (ty.updateApp! ty.appFn! m')]

open Lean Meta Elab Tactic in
/-- `intro` on a goal that is syntactically a binder (never unfolding a definition to find one). -/
elab "link_intro_syntactic" : tactic => do
  let goal ← getMainGoal
  unless (← instantiateMVars (← goal.getType)).isForall do throwError "link_intro_syntactic: no binder"
  let (_, g) ← goal.intro1
  replaceMainGoal [g]

open Lean Meta Elab Tactic in
/-- Closes an impossible branch: a hypothesis `∀ xs, a = b → False` whose equation holds by `rfl`
    for some instantiation. -/
elab "link_absurd" : tactic => do
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
  unless ok do throwError "link_absurd: no contradiction"

open Lean Meta Elab Tactic in
/-- Beta/projection/constructor-iota normal form (`whnfCore`, no definition unfolding) of the
    computation in a `LinkDisc` goal. -/
elab "link_whnf_core" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let ty ← instantiateMVars (← goal.getType)
    let_expr KatLang.MemoLinks.LinkDisc _ m := ty | throwError "link_whnf_core: not a link-discipline goal"
    let m' ← whnfCore m
    if m' == m then throwError "link_whnf_core: no progress"
    replaceMainGoal [← goal.replaceTargetDefEq (ty.updateApp! ty.appFn! m')]

/-- The evaluator helpers `rec.f args` are `rec (.f args)`. -/
macro "link_unfold_rec" : tactic => `(tactic| dsimp (config := { proj := false }) only [EvalRec.whileLoop, EvalRec.aliasStepIsRuntime, EvalRec.aliasValue, EvalRec.resolveAliasChase, EvalRec.resolveAliasTarget, EvalRec.resolveAliasValueTarget, EvalRec.lookupLexicalProperty, EvalRec.lookupLexicalValueProperty, EvalRec.lookupLexical, EvalRec.needPlanNormalizeCallee, EvalRec.resolveAlg, EvalRec.projectNeedCallable, EvalRec.projectNeedWrittenAt, EvalRec.linkCallable, EvalRec.projectParameterCallable, EvalRec.projectNeedWritten, EvalRec.projectNeedStructuralMember, EvalRec.resolveCalleeAlg, EvalRec.expectPreparedSequenceBuiltinAlgorithmSuffixArg, EvalRec.resolveDotReceiver?, EvalRec.resolveDotReceiver, EvalRec.algorithmIntrinsicRoute, EvalRec.demandNeedRecursive, EvalRec.evalSuppliedAt, EvalRec.linkValue, EvalRec.algorithmOfValue, EvalRec.capturedCallee, EvalRec.referenceReceiverValue, EvalRec.algorithmCalleeOf, EvalRec.evalSuppliedCallCounted, EvalRec.evalNeedUserSupply, EvalRec.evalNeedFamilySupply, EvalRec.invokeNeed, EvalRec.argumentNeed, EvalRec.runNeedStepSlots, EvalRec.runNeedWhileRound, EvalRec.evalAlgOutputCore, EvalRec.evalAlgOutput, EvalRec.evalProgramOutput, EvalRec.evalAlgOutputSlots, EvalRec.formOutputRow, EvalRec.whileVerdictSlots, EvalRec.evalSequenceCallbackCall, EvalRec.evalSequenceCallbackCallCounted, EvalRec.evalAlgOutputPreparedCore, EvalRec.evalOutputRowsPreparedCore, EvalRec.evalCapturePreparedCore, EvalRec.evalCaptureCountedCore, EvalRec.evalCaptureValue, EvalRec.evalAlgOutputCountedCore, EvalRec.evalAlgOutputCounted, EvalRec.evalZeroArgumentDemandOutputCounted, EvalRec.evalZeroArgumentDemandOutput, EvalRec.evalArgumentValueCounted, EvalRec.evalArgumentValue, EvalRec.evalZeroArgPropertyAccessCounted, EvalRec.evalZeroArgPropertyAccess, EvalRec.evalConditionalCallbackCallCounted, EvalRec.evalUserCallbackCallCounted, EvalRec.evalResolvedCallbackCallCounted, EvalRec.evalResolvedCallbackCall, EvalRec.evalSequenceReduceStepCounted, EvalRec.demandSequenceBuiltinCallItemValue, EvalRec.bindSequenceBuiltinArguments, EvalRec.evalReduceCounted, EvalRec.evalFilterCounted, EvalRec.evalMapCounted, EvalRec.applyBuiltinCountedSequence, EvalRec.applyBuiltinCounted, EvalRec.applyBuiltin, EvalRec.applyBuiltinCountedResolved, EvalRec.evalExplicitSequenceValueItems, EvalRec.evalExplicitSequenceValueRowSlots, EvalRec.evalExplicitSequenceValueExprSlots, EvalRec.evalUserCallCounted, EvalRec.evalConditionalCallCounted, EvalRec.evalResolvedCall, EvalRec.evalResolvedCallCounted, EvalRec.evalCallCountedExpr, EvalRec.callLexicalWithReceiverCounted, EvalRec.rejectDotStringIntrinsicArguments, EvalRec.evalDotStringReceiverValue, EvalRec.evalDotCallCounted, EvalRec.rejectInvokeIntrinsicArguments, EvalRec.invokeCallReferenceValue, EvalRec.argumentViewCells, EvalRec.evalArgumentViewBuiltin, EvalRec.evalSequenceSpreadOperandValue, EvalRec.evalSequenceSpreadCounted, EvalRec.evalSupplySpread, EvalRec.evalListLiteralCounted, EvalRec.evalSequenceConstructCounted, EvalRec.evalUnaryCounted, EvalRec.evalBinaryCounted, EvalRec.evalComparisonCounted, EvalRec.evalComparisonLinksCounted, EvalRec.evalCounted, EvalRec.evalUserCall, EvalRec.evalConditionalCall, EvalRec.evalCallExpr, EvalRec.evalDotCall, EvalRec.eval, EvalRec.planRoute,
  EvalRec.bindingChannels, NeedChannels.shell, NeedChannels.capabilities] at *)

set_option hygiene false in
/-- Syntax-directed link discipline (base: no recursive helper lemmas), given that `hrec`
    is link-disciplined. -/
macro "link_tac_base" : tactic => `(tactic| ((try link_unfold_rec) <;> repeat' (first
  | link_rec
  | link_hyp
  | link_absurd
  | (with_reducible apply link_get_bind)
  | (with_reducible apply LinkAt.bind)
  | (with_reducible apply LinkAt.set; first
      | exact LinkHeapKept.refl _
      | (apply LinkHeapKept.set_bang <;> first | link_hyp | (exact linkKept_of_same _ _ rfl rfl rfl) | (apply linkKept_of_claim; link_hyp)))
  | (with_reducible apply LinkDisc.withCtx)
  | (with_reducible apply LinkDisc.captureMeta)
  | (with_reducible apply LinkDisc.attempt)
  | (with_reducible apply LinkDisc.map)
  | (with_reducible apply LinkDisc.bind)
  | (with_reducible apply linkDisc_pure)
  | (with_reducible apply linkDisc_get)
  | (with_reducible apply linkDisc_throw)
  | (with_reducible apply linkDisc_evalError)
  | (with_reducible apply linkDisc_lift)
  | (with_reducible apply linkDisc_allocate)
  | (with_reducible apply linkDisc_supply)
  | (with_reducible apply linkDisc_mapM)
  | (with_reducible apply linkDisc_form)
  | (with_reducible apply linkDisc_slot)
  | (with_reducible apply linkDisc_prepare)
  | (with_reducible apply linkDisc_routeOf)
  | (with_reducible apply linkDisc_calleeCell)
  | (with_reducible apply linkDisc_projectionStep)
  | (with_reducible apply linkDisc_receiverCell)
  | (with_reducible apply linkDisc_linkCallable)
  | (with_reducible apply linkDisc_linkValue)
  | (with_reducible apply linkDisc_decodeCallee)
  | (with_reducible apply linkDisc_execute)
  | (with_reducible apply linkDisc_step)
  | (with_reducible apply linkDisc_reify)
  | (with_reducible apply linkDisc_invoke)
  | (with_reducible apply linkDisc_reference)
  | (with_reducible apply linkDisc_viewCells)
  | (with_reducible apply link_modify; intro s; first
      | exact LinkHeapKept.refl _
      | (apply LinkHeapKept.modify; intro c _; exact linkKept_of_same _ _ rfl rfl rfl))
  | (with_reducible apply link_forIn)
  | (with_reducible apply link_forM)
  | (with_reducible apply link_foldlM)
  | (with_reducible apply CapsLink.mk)

  | split
  | link_intro_syntactic
  | link_zeta
  | link_whnf_core
  | link_unfold_head
  | (with_reducible apply LinkAt.of_disc))))

/-! ## Link discipline of the recursive total helpers -/

theorem link_formLeftToRight (form : Expr → EvalM (List Result)) (h : ∀ e, LinkDisc (form e))
    (rows : List Expr) : LinkDisc (OutputRows.formLeftToRight form rows) := by
  induction rows with
  | nil => unfold OutputRows.formLeftToRight; link_tac_base
  | cons e rest ih => unfold OutputRows.formLeftToRight; link_tac_base

theorem link_discover (form : Expr → EvalM (List Result)) (h : ∀ e, LinkDisc (form e))
    (rows : List Expr) : LinkDisc (WhileRound.discover form rows) := by
  induction rows with
  | nil => unfold WhileRound.discover; link_tac_base
  | cons e rest ih => unfold WhileRound.discover; link_tac_base

theorem link_selectWith {α : Type} (demand : α → EvalM Result) (h : ∀ a, LinkDisc (demand a))
    (receiver : Result) (cells : List α) : LinkDisc (selectWith demand receiver cells) := by
  induction cells with
  | nil => unfold selectWith; link_tac_base
  | cons c rest ih => unfold selectWith; link_tac_base

theorem link_selectViewWith {α : Type} (demand : α → EvalM Result) (hd : ∀ a, LinkDisc (demand a))
    (cellsOf : EvalM (List NeedSupply.Sourced)) (hc : LinkDisc cellsOf)
    (demandCell : Nat → EvalM Result) (hdc : ∀ a, LinkDisc (demandCell a)) (selectors : List α) :
    LinkDisc (selectViewWith demand cellsOf demandCell selectors) := by
  induction selectors with
  | nil => unfold selectViewWith; link_tac_base
  | cons c rest ih => unfold selectViewWith; link_tac_base

theorem link_interpolateWith (value : Expr → EvalM Result) (h : ∀ e, LinkDisc (value e))
    (acc : String) (links : List InterpolationLink) :
    LinkDisc (interpolateWith value acc links) := by
  induction links generalizing acc with
  | nil => unfold interpolateWith; link_tac_base
  | cons l rest ih => unfold interpolateWith; link_tac_base

/-- Capabilities whose every field is link-disciplined. -/
structure CapsLink (caps : NeedCapabilities EvalM) : Prop where
  value : ∀ a, LinkDisc (caps.value a)
  callable : ∀ a, LinkDisc (caps.callable a)
  allocate : ∀ s, LinkDisc (caps.allocate s)
  reference : ∀ a, LinkDisc (caps.reference a)

theorem link_binder (caps : NeedCapabilities EvalM) (hc : CapsLink caps) (repeated : List Ident)
    (family : Bool) :
    (∀ pattern address bound,
      LinkDisc (NeedBinder.bindOne caps pattern address repeated bound family)) ∧
    (∀ patterns sources current,
      LinkDisc (NeedBinder.bindSources caps patterns sources repeated current family)) := by
  have hv := hc.value; have hcl := hc.callable; have hal := hc.allocate; have hre := hc.reference
  refine NeedBinder.bindOne.mutual_induct
    (motive_1 := fun pattern address bound =>
      LinkDisc (NeedBinder.bindOne caps pattern address repeated bound family))
    (motive_2 := fun patterns sources current =>
      LinkDisc (NeedBinder.bindSources caps patterns sources repeated current family))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals intros
  all_goals first
    | (simp only [NeedBinder.bindOne]; link_tac_base)
    | (simp only [NeedBinder.bindSources]; link_tac_base)

theorem link_bindPatterns (caps : NeedCapabilities EvalM) (hc : CapsLink caps)
    (patterns : List NeedPattern) (cells : List Nat) (family : Bool) :
    LinkDisc (NeedBinder.bindPatterns caps patterns cells family) := by
  unfold NeedBinder.bindPatterns NeedBinder.bindLevel NeedBinder.cardinalityGate
  have := (link_binder caps hc (needRepeatedNames patterns) family).2
  link_tac_base

theorem link_chooseBranch {β : Type} (caps : NeedCapabilities EvalM) (hc : CapsLink caps)
    (cells : List Nat) (calleeName : String) (activate : CondBranch → NeedEnv → EvalM β)
    (ha : ∀ b e, LinkDisc (activate b e)) (branches : List CondBranch) :
    LinkDisc (NeedBinder.chooseBranch caps cells calleeName activate branches) := by
  induction branches with
  | nil => unfold NeedBinder.chooseBranch; link_tac_base
  | cons b rest ih =>
    unfold NeedBinder.chooseBranch
    have := fun ps fam => link_bindPatterns caps hc ps cells fam
    link_tac_base

theorem link_selectFamily {β : Type} (caps : NeedCapabilities EvalM) (hc : CapsLink caps)
    (callee : Algorithm) (cells : List Nat) (calleeName : String)
    (activate : CondBranch → NeedEnv → EvalM β) (ha : ∀ b e, LinkDisc (activate b e)) :
    LinkDisc (NeedBinder.selectFamily caps callee cells calleeName activate) := by
  unfold NeedBinder.selectFamily
  have := link_chooseBranch caps hc cells calleeName activate ha
  link_tac_base


theorem link_collectSingleAtomicNumbers (b : Builtin) (index : Nat) (items : List Result) :
    LinkDisc (collectSingleAtomicNumbers b index items) := by
  induction items generalizing index with
  | nil => unfold collectSingleAtomicNumbers; link_tac_base
  | cons i rest ih => unfold collectSingleAtomicNumbers; link_tac_base

theorem link_minLoop (numbers : List Int) (current : Int) :
    LinkDisc (evalMinCounted.minLoop numbers current) := by
  induction numbers generalizing current with
  | nil => unfold evalMinCounted.minLoop; link_tac_base
  | cons n rest ih => unfold evalMinCounted.minLoop; link_tac_base

theorem link_maxLoop (numbers : List Int) (current : Int) :
    LinkDisc (evalMaxCounted.maxLoop numbers current) := by
  induction numbers generalizing current with
  | nil => unfold evalMaxCounted.maxLoop; link_tac_base
  | cons n rest ih => unfold evalMaxCounted.maxLoop; link_tac_base

theorem link_resolveAlgForOpen (ctx : EvalCtx) (e : Expr) : LinkDisc (resolveAlgForOpen e ctx) := by
  induction e using resolveAlgForOpen.induct ctx with
  | case7 o n a ih => unfold resolveAlgForOpen; link_tac_base
  | _ => unfold resolveAlgForOpen; link_tac_base

theorem link_lookupOpenProperties (a : Algorithm) (name : Ident) (ctx : EvalCtx) :
    LinkDisc (lookupOpenProperties a name ctx) := by
  have := link_resolveAlgForOpen
  unfold lookupOpenProperties; link_tac_base

theorem link_lookupOpenPropertiesInParentChain (name : Ident) (ctx : EvalCtx) (sc : ScopeCtx) :
    LinkDisc (lookupOpenPropertiesInParentChain sc name ctx) := by
  induction sc using lookupOpenPropertiesInParentChain.induct with
  | _ t ih =>
    have := link_lookupOpenProperties
    unfold lookupOpenPropertiesInParentChain
    cases t with
    | mk parent _ _ _ _ _ _ _ => cases parent <;> link_tac_base

section LocalLoops
variable (rec : EvalRec) (hrec : ∀ c, LinkDisc (rec c))
include hrec

theorem link_outputRowsCollect (rowCtx : EvalCtx) (env : ValEnv) (rows : List Expr)
    (acc : List Result) (emitted : Nat) :
    LinkDisc (EvalBody.evalOutputRowsPreparedCore.collect rec rowCtx env rows acc emitted) := by
  induction rows generalizing acc emitted with
  | nil => unfold EvalBody.evalOutputRowsPreparedCore.collect; link_tac_base
  | cons e rest ih => unfold EvalBody.evalOutputRowsPreparedCore.collect; link_tac_base

theorem link_explicitRowsCollect (rowCtx : EvalCtx) (env : ValEnv) (rows : List Expr) (acc : List Result) :
    LinkDisc (EvalBody.evalExplicitSequenceValueRowSlots.collect rec rowCtx env rows acc) := by
  induction rows generalizing acc with
  | nil => unfold EvalBody.evalExplicitSequenceValueRowSlots.collect; link_tac_base
  | cons e rest ih => unfold EvalBody.evalExplicitSequenceValueRowSlots.collect; link_tac_base

theorem link_listLiteralCollect (ctx : EvalCtx) (env : ValEnv) (elements : List Expr) (acc : List Result) :
    LinkDisc (EvalBody.evalListLiteralCounted.collect rec ctx env elements acc) := by
  induction elements generalizing acc with
  | nil => unfold EvalBody.evalListLiteralCounted.collect; link_tac_base
  | cons e rest ih => unfold EvalBody.evalListLiteralCounted.collect; link_tac_base

theorem link_sequenceConstructLoop (ctx : EvalCtx) (env : ValEnv) (leaves : List Expr) (items : List Result) :
    LinkDisc (EvalBody.evalSequenceConstructCounted.loop rec ctx env leaves items) := by
  induction leaves generalizing items with
  | nil => unfold EvalBody.evalSequenceConstructCounted.loop; link_tac_base
  | cons e rest ih => unfold EvalBody.evalSequenceConstructCounted.loop; link_tac_base

theorem link_prepareControls (b : Builtin) (ctx : EvalCtx) (env : ValEnv)
    (descriptors : List SequenceBuiltinSuffixArgDescriptor) (items : List CallableCallItem) :
    LinkDisc (EvalBody.bindSequenceBuiltinArguments.prepareControls rec b ctx env descriptors items) := by
  induction descriptors generalizing items with
  | nil => cases items <;> (unfold EvalBody.bindSequenceBuiltinArguments.prepareControls; link_tac_base)
  | cons d rest ih => cases items <;> (unfold EvalBody.bindSequenceBuiltinArguments.prepareControls; link_tac_base)

theorem link_reduceLoop (stepAlg : Algorithm) (ctx : EvalCtx) (env : ValEnv)
    (items : List CountedResult) (acc : CountedResult) :
    LinkDisc (EvalBody.evalReduceCounted.reduceLoop rec stepAlg ctx env items acc) := by
  induction items generalizing acc with
  | nil => unfold EvalBody.evalReduceCounted.reduceLoop; link_tac_base
  | cons i rest ih => unfold EvalBody.evalReduceCounted.reduceLoop; link_tac_base

theorem link_filterLoop (predicateAlg : Algorithm) (ctx : EvalCtx) (env : ValEnv)
    (index : Nat) (items : List CountedResult) :
    LinkDisc (EvalBody.evalFilterCounted.filterLoop rec predicateAlg ctx env index items) := by
  induction items generalizing index with
  | nil => unfold EvalBody.evalFilterCounted.filterLoop; link_tac_base
  | cons i rest ih => unfold EvalBody.evalFilterCounted.filterLoop; link_tac_base

theorem link_mapLoop (transformAlg : Algorithm) (ctx : EvalCtx) (env : ValEnv) (items : List CountedResult) :
    LinkDisc (EvalBody.evalMapCounted.mapLoop rec transformAlg ctx env items) := by
  induction items with
  | nil => unfold EvalBody.evalMapCounted.mapLoop; link_tac_base
  | cons i rest ih => unfold EvalBody.evalMapCounted.mapLoop; link_tac_base

theorem link_repeatLoop (ctx : EvalCtx) (env : ValEnv) (step : ResolvedArgumentAlgorithm)
    (stepName : String) (remaining : Nat) (cells : List Nat) :
    LinkDisc (EvalBody.applyBuiltinCounted.repeatLoop rec ctx env step stepName remaining cells) := by
  induction remaining generalizing cells with
  | zero => unfold EvalBody.applyBuiltinCounted.repeatLoop; link_tac_base
  | succ k ih => unfold EvalBody.applyBuiltinCounted.repeatLoop; link_tac_base

end LocalLoops

set_option hygiene false in
/-- Syntax-directed link discipline of an evaluator body, given that its recursive answer `hrec`
    is link-disciplined. -/
macro "link_tac" : tactic => `(tactic| ((try link_unfold_rec) <;> repeat' (first
  | link_rec
  | link_hyp
  | link_absurd
  | (with_reducible apply link_get_bind)
  | (with_reducible apply LinkAt.bind)
  | (with_reducible apply LinkAt.set; first
      | exact LinkHeapKept.refl _
      | (apply LinkHeapKept.set_bang <;> first | link_hyp | (exact linkKept_of_same _ _ rfl rfl rfl) | (apply linkKept_of_claim; link_hyp)))
  | (with_reducible apply LinkDisc.withCtx)
  | (with_reducible apply LinkDisc.captureMeta)
  | (with_reducible apply LinkDisc.attempt)
  | (with_reducible apply LinkDisc.map)
  | (with_reducible apply LinkDisc.bind)
  | (with_reducible apply linkDisc_pure)
  | (with_reducible apply linkDisc_get)
  | (with_reducible apply linkDisc_throw)
  | (with_reducible apply linkDisc_evalError)
  | (with_reducible apply linkDisc_lift)
  | (with_reducible apply linkDisc_allocate)
  | (with_reducible apply linkDisc_supply)
  | (with_reducible apply linkDisc_mapM)
  | (with_reducible apply linkDisc_form)
  | (with_reducible apply linkDisc_slot)
  | (with_reducible apply linkDisc_prepare)
  | (with_reducible apply linkDisc_routeOf)
  | (with_reducible apply linkDisc_calleeCell)
  | (with_reducible apply linkDisc_projectionStep)
  | (with_reducible apply linkDisc_receiverCell)
  | (with_reducible apply linkDisc_linkCallable)
  | (with_reducible apply linkDisc_linkValue)
  | (with_reducible apply linkDisc_decodeCallee)
  | (with_reducible apply linkDisc_execute)
  | (with_reducible apply linkDisc_step)
  | (with_reducible apply linkDisc_reify)
  | (with_reducible apply linkDisc_invoke)
  | (with_reducible apply linkDisc_reference)
  | (with_reducible apply linkDisc_viewCells)
  | (with_reducible apply link_modify; intro s; first
      | exact LinkHeapKept.refl _
      | (apply LinkHeapKept.modify; intro c _; exact linkKept_of_same _ _ rfl rfl rfl))
  | (with_reducible apply link_forIn)
  | (with_reducible apply link_forM)
  | (with_reducible apply link_foldlM)
  | (with_reducible apply link_formLeftToRight)
  | (with_reducible apply link_discover)
  | (with_reducible apply link_selectWith)
  | (with_reducible apply link_selectViewWith)
  | (with_reducible apply link_interpolateWith)
  | (with_reducible apply link_bindPatterns)
  | (with_reducible apply link_selectFamily)
  | (with_reducible apply link_collectSingleAtomicNumbers)
  | (with_reducible apply link_minLoop)
  | (with_reducible apply link_maxLoop)
  | (with_reducible apply link_resolveAlgForOpen)
  | (with_reducible apply link_lookupOpenProperties)
  | (with_reducible apply link_lookupOpenPropertiesInParentChain)
  | (with_reducible apply link_outputRowsCollect rec hrec)
  | (with_reducible apply link_explicitRowsCollect rec hrec)
  | (with_reducible apply link_listLiteralCollect rec hrec)
  | (with_reducible apply link_sequenceConstructLoop rec hrec)
  | (with_reducible apply link_prepareControls rec hrec)
  | (with_reducible apply link_reduceLoop rec hrec)
  | (with_reducible apply link_filterLoop rec hrec)
  | (with_reducible apply link_mapLoop rec hrec)
  | (with_reducible apply link_repeatLoop rec hrec)
  | (with_reducible apply link_aliasBareCell)
  | (with_reducible apply CapsLink.mk)

  | split
  | link_intro_syntactic
  | link_zeta
  | link_whnf_core
  | link_unfold_head
  | (with_reducible apply LinkAt.of_disc))))

theorem EvalBody.whileLoop_linkDisc (rec : EvalRec) (hrec : ∀ c, LinkDisc (rec c)) (step : ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) (stepName : String) (cells : List Nat) :
    LinkDisc (EvalBody.whileLoop rec step ctx env stepName cells) := by
  unfold EvalBody.whileLoop; link_tac

theorem EvalBody.aliasStepIsRuntime_linkDisc (rec : EvalRec) (hrec : ∀ c, LinkDisc (rec c)) (step : Algorithm) (target : Expr) (ctx : EvalCtx) :
    LinkDisc (EvalBody.aliasStepIsRuntime rec step target ctx) := by
  unfold EvalBody.aliasStepIsRuntime; link_tac

theorem EvalBody.aliasValue_linkDisc (rec : EvalRec) (hrec : ∀ c, LinkDisc (rec c)) (wired : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    LinkDisc (EvalBody.aliasValue rec wired ctx env) := by
  unfold EvalBody.aliasValue; link_tac

theorem EvalBody.resolveAliasChase_linkDisc (rec : EvalRec) (hrec : ∀ c, LinkDisc (rec c)) (callable : Bool) (a : Algorithm) (ctx : EvalCtx) (visited : List String) (projectedFrom : Option Algorithm) :
    LinkDisc (EvalBody.resolveAliasChase rec callable a ctx visited projectedFrom) := by
  unfold EvalBody.resolveAliasChase; link_tac

theorem EvalBody.resolveAliasTarget_linkDisc (rec : EvalRec) (hrec : ∀ c, LinkDisc (rec c)) (a : Algorithm) (ctx : EvalCtx) :
    LinkDisc (EvalBody.resolveAliasTarget rec a ctx) := by
  unfold EvalBody.resolveAliasTarget; link_tac

theorem EvalBody.resolveAliasValueTarget_linkDisc (rec : EvalRec) (hrec : ∀ c, LinkDisc (rec c)) (a : Algorithm) (ctx : EvalCtx) :
    LinkDisc (EvalBody.resolveAliasValueTarget rec a ctx) := by
  unfold EvalBody.resolveAliasValueTarget; link_tac

theorem EvalBody.lookupLexicalProperty_linkDisc (rec : EvalRec) (hrec : ∀ c, LinkDisc (rec c)) (a : Algorithm) (name : Ident) (ctx : EvalCtx) :
    LinkDisc (EvalBody.lookupLexicalProperty rec a name ctx) := by
  unfold EvalBody.lookupLexicalProperty; link_tac

theorem EvalBody.lookupLexicalValueProperty_linkDisc (rec : EvalRec) (hrec : ∀ c, LinkDisc (rec c)) (a : Algorithm) (name : Ident) (ctx : EvalCtx) :
    LinkDisc (EvalBody.lookupLexicalValueProperty rec a name ctx) := by
  unfold EvalBody.lookupLexicalValueProperty; link_tac

theorem EvalBody.lookupLexical_linkDisc (rec : EvalRec) (hrec : ∀ c, LinkDisc (rec c)) (a : Algorithm) (name : Ident) (ctx : EvalCtx) :
    LinkDisc (EvalBody.lookupLexical rec a name ctx) := by
  unfold EvalBody.lookupLexical; link_tac

theorem EvalBody.needPlanNormalizeCallee_linkDisc (rec : EvalRec) (hrec : ∀ c, LinkDisc (rec c)) (callee : Algorithm) (ctx : EvalCtx) :
    LinkDisc (EvalBody.needPlanNormalizeCallee rec callee ctx) := by
  unfold EvalBody.needPlanNormalizeCallee; link_tac

theorem EvalBody.resolveAlg_linkDisc (rec : EvalRec) (hrec : ∀ c, LinkDisc (rec c)) (e : Expr) (ctx : EvalCtx) :
    LinkDisc (EvalBody.resolveAlg rec e ctx) := by
  unfold EvalBody.resolveAlg; link_tac

theorem EvalBody.projectNeedCallable_linkDisc (rec : EvalRec) (hrec : ∀ c, LinkDisc (rec c)) (address : Nat) :
    LinkDisc (EvalBody.projectNeedCallable rec address) := by
  unfold EvalBody.projectNeedCallable; link_tac

theorem EvalBody.projectNeedWrittenAt_linkDisc (rec : EvalRec) (hrec : ∀ c, LinkDisc (rec c)) (address : Nat) (source : Expr) (caller : EvalCtx) :
    LinkDisc (EvalBody.projectNeedWrittenAt rec address source caller) := by
  unfold EvalBody.projectNeedWrittenAt; link_tac

theorem EvalBody.linkCallable_linkDisc (rec : EvalRec) (hrec : ∀ c, LinkDisc (rec c)) (address : Nat) :
    LinkDisc (EvalBody.linkCallable rec address) := by
  unfold EvalBody.linkCallable; link_tac

theorem EvalBody.projectParameterCallable_linkDisc (rec : EvalRec) (hrec : ∀ c, LinkDisc (rec c)) (x : Ident) (ctx : EvalCtx) :
    LinkDisc (EvalBody.projectParameterCallable rec x ctx) := by
  unfold EvalBody.projectParameterCallable; link_tac

theorem EvalBody.projectNeedWritten_linkDisc (rec : EvalRec) (hrec : ∀ c, LinkDisc (rec c)) (source : Expr) (caller : EvalCtx) :
    LinkDisc (EvalBody.projectNeedWritten rec source caller) := by
  unfold EvalBody.projectNeedWritten; link_tac

theorem EvalBody.projectNeedStructuralMember_linkDisc (rec : EvalRec) (hrec : ∀ c, LinkDisc (rec c)) (source : Expr) (ctx : EvalCtx) :
    LinkDisc (EvalBody.projectNeedStructuralMember rec source ctx) := by
  unfold EvalBody.projectNeedStructuralMember; link_tac

theorem EvalBody.resolveCalleeAlg_linkDisc (rec : EvalRec) (hrec : ∀ c, LinkDisc (rec c)) (f : Expr) (ctx : EvalCtx) :
    LinkDisc (EvalBody.resolveCalleeAlg rec f ctx) := by
  unfold EvalBody.resolveCalleeAlg; link_tac

theorem EvalBody.expectPreparedSequenceBuiltinAlgorithmSuffixArg_linkDisc (rec : EvalRec) (hrec : ∀ c, LinkDisc (rec c)) (b : Builtin) (descriptors : List SequenceBuiltinSuffixArgDescriptor) (args : List PreparedSequenceBuiltinSuffixArg) (index : Nat) :
    LinkDisc (EvalBody.expectPreparedSequenceBuiltinAlgorithmSuffixArg rec b descriptors args index) := by
  unfold EvalBody.expectPreparedSequenceBuiltinAlgorithmSuffixArg; link_tac

theorem EvalBody.resolveDotReceiver?_linkDisc (rec : EvalRec) (hrec : ∀ c, LinkDisc (rec c)) (e : Expr) (ctx : EvalCtx) :
    LinkDisc (EvalBody.resolveDotReceiver? rec e ctx) := by
  unfold EvalBody.resolveDotReceiver?; link_tac

theorem EvalBody.resolveDotReceiver_linkDisc (rec : EvalRec) (hrec : ∀ c, LinkDisc (rec c)) (e : Expr) (ctx : EvalCtx) :
    LinkDisc (EvalBody.resolveDotReceiver rec e ctx) := by
  unfold EvalBody.resolveDotReceiver; link_tac

theorem EvalBody.algorithmIntrinsicRoute_linkDisc (rec : EvalRec) (hrec : ∀ c, LinkDisc (rec c)) (receiver : Expr) (ctx : EvalCtx) :
    LinkDisc (EvalBody.algorithmIntrinsicRoute rec receiver ctx) := by
  unfold EvalBody.algorithmIntrinsicRoute; link_tac

theorem EvalBody.demandNeedRecursive_linkDisc (rec : EvalRec) (hrec : ∀ c, LinkDisc (rec c)) (address : Nat) :
    LinkDisc (EvalBody.demandNeedRecursive rec address) := by
  unfold EvalBody.demandNeedRecursive; link_tac

theorem EvalBody.evalSuppliedAt_linkDisc (rec : EvalRec) (hrec : ∀ c, LinkDisc (rec c)) (address : Nat) (e : Expr) (ctx : EvalCtx) (env : ValEnv) :
    LinkDisc (EvalBody.evalSuppliedAt rec address e ctx env) := by
  unfold EvalBody.evalSuppliedAt; link_tac

theorem EvalBody.linkValue_linkDisc (rec : EvalRec) (hrec : ∀ c, LinkDisc (rec c)) (address : Nat) :
    LinkDisc (EvalBody.linkValue rec address) := by
  unfold EvalBody.linkValue; link_tac

theorem EvalBody.algorithmOfValue_linkDisc (rec : EvalRec) (hrec : ∀ c, LinkDisc (rec c)) (val : Result) (argsOpt : Option OutputBundle) (ctx : EvalCtx) (env : ValEnv) :
    LinkDisc (EvalBody.algorithmOfValue rec val argsOpt ctx env) := by
  unfold EvalBody.algorithmOfValue; link_tac

theorem EvalBody.capturedCallee_linkDisc (rec : EvalRec) (hrec : ∀ c, LinkDisc (rec c)) (callee : Nat) :
    LinkDisc (EvalBody.capturedCallee rec callee) := by
  unfold EvalBody.capturedCallee; link_tac

theorem EvalBody.referenceReceiverValue_linkDisc (rec : EvalRec) (hrec : ∀ c, LinkDisc (rec c)) (target : Expr) (targetAlg : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    LinkDisc (EvalBody.referenceReceiverValue rec target targetAlg ctx env) := by
  unfold EvalBody.referenceReceiverValue; link_tac

theorem EvalBody.algorithmCalleeOf_linkDisc (rec : EvalRec) (hrec : ∀ c, LinkDisc (rec c)) (receiver : Expr) (ctx : EvalCtx) (env : ValEnv) :
    LinkDisc (EvalBody.algorithmCalleeOf rec receiver ctx env) := by
  unfold EvalBody.algorithmCalleeOf; link_tac

theorem EvalBody.evalSuppliedCallCounted_linkDisc (rec : EvalRec) (hrec : ∀ c, LinkDisc (rec c)) (origin : CalleeOrigin) (callee : Algorithm) (cells : List NeedSupply.Sourced) (ctx : EvalCtx) (env : ValEnv) (calleeName : String) :
    LinkDisc (EvalBody.evalSuppliedCallCounted rec origin callee cells ctx env calleeName) := by
  unfold EvalBody.evalSuppliedCallCounted; link_tac

theorem EvalBody.evalNeedUserSupply_linkDisc (rec : EvalRec) (hrec : ∀ c, LinkDisc (rec c)) (callee : Algorithm) (cells : List Nat) (ctx : EvalCtx) (env : ValEnv) :
    LinkDisc (EvalBody.evalNeedUserSupply rec callee cells ctx env) := by
  unfold EvalBody.evalNeedUserSupply; link_tac

theorem EvalBody.evalNeedFamilySupply_linkDisc (rec : EvalRec) (hrec : ∀ c, LinkDisc (rec c)) (callee : Algorithm) (cells : List Nat) (ctx : EvalCtx) (env : ValEnv) (calleeName : String) :
    LinkDisc (EvalBody.evalNeedFamilySupply rec callee cells ctx env calleeName) := by
  unfold EvalBody.evalNeedFamilySupply; link_tac

theorem EvalBody.invokeNeed_linkDisc (rec : EvalRec) (hrec : ∀ c, LinkDisc (rec c)) (arg : ResolvedArgumentAlgorithm) :
    LinkDisc (EvalBody.invokeNeed rec arg) := by
  unfold EvalBody.invokeNeed; link_tac

theorem EvalBody.argumentNeed_linkDisc (rec : EvalRec) (hrec : ∀ c, LinkDisc (rec c)) (arg : ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) :
    LinkDisc (EvalBody.argumentNeed rec arg ctx env) := by
  unfold EvalBody.argumentNeed; link_tac

theorem EvalBody.runNeedStepSlots_linkDisc (rec : EvalRec) (hrec : ∀ c, LinkDisc (rec c)) (step : Algorithm) (ctx : EvalCtx) (env : ValEnv) (cells : List Nat) (stepName : String) :
    LinkDisc (EvalBody.runNeedStepSlots rec step ctx env cells stepName) := by
  unfold EvalBody.runNeedStepSlots EvalBody.runNeedStepWith; link_tac

theorem EvalBody.runNeedWhileRound_linkDisc (rec : EvalRec) (hrec : ∀ c, LinkDisc (rec c)) (step : Algorithm) (ctx : EvalCtx) (env : ValEnv) (cells : List Nat) (stepName : String) :
    LinkDisc (EvalBody.runNeedWhileRound rec step ctx env cells stepName) := by
  unfold EvalBody.runNeedWhileRound EvalBody.runNeedStepWith; link_tac

theorem EvalBody.evalAlgOutputCore_linkDisc (rec : EvalRec) (hrec : ∀ c, LinkDisc (rec c)) (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    LinkDisc (EvalBody.evalAlgOutputCore rec a ctx env) := by
  unfold EvalBody.evalAlgOutputCore; link_tac

theorem EvalBody.evalAlgOutput_linkDisc (rec : EvalRec) (hrec : ∀ c, LinkDisc (rec c)) (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    LinkDisc (EvalBody.evalAlgOutput rec a ctx env) := by
  unfold EvalBody.evalAlgOutput; link_tac

theorem EvalBody.evalProgramOutput_linkDisc (rec : EvalRec) (hrec : ∀ c, LinkDisc (rec c)) (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    LinkDisc (EvalBody.evalProgramOutput rec a ctx env) := by
  unfold EvalBody.evalProgramOutput; link_tac

theorem EvalBody.evalAlgOutputSlots_linkDisc (rec : EvalRec) (hrec : ∀ c, LinkDisc (rec c)) (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    LinkDisc (EvalBody.evalAlgOutputSlots rec a ctx env) := by
  unfold EvalBody.evalAlgOutputSlots ActivatedBody.readRows; link_tac

theorem EvalBody.formOutputRow_linkDisc (rec : EvalRec) (hrec : ∀ c, LinkDisc (rec c)) (ctx : EvalCtx) (env : ValEnv) (e : Expr) :
    LinkDisc (EvalBody.formOutputRow rec ctx env e) := by
  unfold EvalBody.formOutputRow; link_tac

theorem EvalBody.whileVerdictSlots_linkDisc (rec : EvalRec) (hrec : ∀ c, LinkDisc (rec c)) (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    LinkDisc (EvalBody.whileVerdictSlots rec a ctx env) := by
  unfold EvalBody.whileVerdictSlots ActivatedBody.readRows; link_tac

theorem EvalBody.evalSequenceCallbackCall_linkDisc (rec : EvalRec) (hrec : ∀ c, LinkDisc (rec c)) (callee : Algorithm) (item : CountedResult) (ctx : EvalCtx) (env : ValEnv) (calleeName : String) :
    LinkDisc (EvalBody.evalSequenceCallbackCall rec callee item ctx env calleeName) := by
  unfold EvalBody.evalSequenceCallbackCall; link_tac

theorem EvalBody.evalSequenceCallbackCallCounted_linkDisc (rec : EvalRec) (hrec : ∀ c, LinkDisc (rec c)) (callee : Algorithm) (item : CountedResult) (ctx : EvalCtx) (env : ValEnv) (calleeName : String) :
    LinkDisc (EvalBody.evalSequenceCallbackCallCounted rec callee item ctx env calleeName) := by
  unfold EvalBody.evalSequenceCallbackCallCounted; link_tac

theorem EvalBody.evalAlgOutputPreparedCore_linkDisc (rec : EvalRec) (hrec : ∀ c, LinkDisc (rec c)) (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    LinkDisc (EvalBody.evalAlgOutputPreparedCore rec a ctx env) := by
  unfold EvalBody.evalAlgOutputPreparedCore; link_tac

theorem EvalBody.evalOutputRowsPreparedCore_linkDisc (rec : EvalRec) (hrec : ∀ c, LinkDisc (rec c)) (rows : OutputBundle) (rowCtx : EvalCtx) (env : ValEnv) :
    LinkDisc (EvalBody.evalOutputRowsPreparedCore rec rows rowCtx env) := by
  unfold EvalBody.evalOutputRowsPreparedCore; link_tac

theorem EvalBody.evalCapturePreparedCore_linkDisc (rec : EvalRec) (hrec : ∀ c, LinkDisc (rec c)) (rows : OutputBundle) (ctx : EvalCtx) (env : ValEnv) :
    LinkDisc (EvalBody.evalCapturePreparedCore rec rows ctx env) := by
  unfold EvalBody.evalCapturePreparedCore; link_tac

theorem EvalBody.evalCaptureCountedCore_linkDisc (rec : EvalRec) (hrec : ∀ c, LinkDisc (rec c)) (rows : OutputBundle) (ctx : EvalCtx) (env : ValEnv) :
    LinkDisc (EvalBody.evalCaptureCountedCore rec rows ctx env) := by
  unfold EvalBody.evalCaptureCountedCore; link_tac

theorem EvalBody.evalCaptureValue_linkDisc (rec : EvalRec) (hrec : ∀ c, LinkDisc (rec c)) (rows : OutputBundle) (ctx : EvalCtx) (env : ValEnv) :
    LinkDisc (EvalBody.evalCaptureValue rec rows ctx env) := by
  unfold EvalBody.evalCaptureValue; link_tac

theorem EvalBody.evalAlgOutputCountedCore_linkDisc (rec : EvalRec) (hrec : ∀ c, LinkDisc (rec c)) (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    LinkDisc (EvalBody.evalAlgOutputCountedCore rec a ctx env) := by
  unfold EvalBody.evalAlgOutputCountedCore; link_tac

theorem EvalBody.evalAlgOutputCounted_linkDisc (rec : EvalRec) (hrec : ∀ c, LinkDisc (rec c)) (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    LinkDisc (EvalBody.evalAlgOutputCounted rec a ctx env) := by
  unfold EvalBody.evalAlgOutputCounted; link_tac

theorem EvalBody.evalZeroArgumentDemandOutputCounted_linkDisc (rec : EvalRec) (hrec : ∀ c, LinkDisc (rec c)) (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    LinkDisc (EvalBody.evalZeroArgumentDemandOutputCounted rec a ctx env) := by
  unfold EvalBody.evalZeroArgumentDemandOutputCounted; link_tac

theorem EvalBody.evalZeroArgumentDemandOutput_linkDisc (rec : EvalRec) (hrec : ∀ c, LinkDisc (rec c)) (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    LinkDisc (EvalBody.evalZeroArgumentDemandOutput rec a ctx env) := by
  unfold EvalBody.evalZeroArgumentDemandOutput; link_tac

theorem EvalBody.evalArgumentValueCounted_linkDisc (rec : EvalRec) (hrec : ∀ c, LinkDisc (rec c)) (arg : ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) :
    LinkDisc (EvalBody.evalArgumentValueCounted rec arg ctx env) := by
  unfold EvalBody.evalArgumentValueCounted; link_tac

theorem EvalBody.evalArgumentValue_linkDisc (rec : EvalRec) (hrec : ∀ c, LinkDisc (rec c)) (arg : ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) :
    LinkDisc (EvalBody.evalArgumentValue rec arg ctx env) := by
  unfold EvalBody.evalArgumentValue; link_tac

/-- CACHE-PUB-1: a property request's calculation (a read's demand, an invocation's fresh call) is
    link-disciplined whenever its recursive answer is. -/
theorem EvalBody.zeroArgPropertyCalculation_linkDisc (rec : EvalRec) (hrec : ∀ c, LinkDisc (rec c)) (request : ZeroArgPropertyRequest) (resolvedAlgorithm : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    LinkDisc (EvalBody.zeroArgPropertyCalculation rec request resolvedAlgorithm ctx env) := by
  unfold EvalBody.zeroArgPropertyCalculation; link_tac

theorem EvalBody.evalZeroArgPropertyAccessCounted_linkDisc (rec : EvalRec) (hrec : ∀ c, LinkDisc (rec c)) (accessKind : ZeroArgPropertyAccessKind) (owner : Algorithm) (binding : PropDef) (resolvedAlgorithm : Algorithm) (ctx : EvalCtx) (env : ValEnv) (request : ZeroArgPropertyRequest) :
    LinkDisc (EvalBody.evalZeroArgPropertyAccessCounted rec accessKind owner binding resolvedAlgorithm ctx env request) := by
  have hcalc : ∀ q, LinkDisc (EvalBody.zeroArgPropertyCalculation rec q resolvedAlgorithm ctx env) :=
    fun q => EvalBody.zeroArgPropertyCalculation_linkDisc rec hrec q resolvedAlgorithm ctx env
  unfold EvalBody.evalZeroArgPropertyAccessCounted; link_tac

theorem EvalBody.evalZeroArgPropertyAccess_linkDisc (rec : EvalRec) (hrec : ∀ c, LinkDisc (rec c)) (accessKind : ZeroArgPropertyAccessKind) (owner : Algorithm) (binding : PropDef) (resolvedAlgorithm : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    LinkDisc (EvalBody.evalZeroArgPropertyAccess rec accessKind owner binding resolvedAlgorithm ctx env) := by
  unfold EvalBody.evalZeroArgPropertyAccess; link_tac

theorem EvalBody.evalConditionalCallbackCallCounted_linkDisc (rec : EvalRec) (hrec : ∀ c, LinkDisc (rec c)) (callee : Algorithm) (args : List CountedResult) (ctx : EvalCtx) (env : ValEnv) (calleeName : String) :
    LinkDisc (EvalBody.evalConditionalCallbackCallCounted rec callee args ctx env calleeName) := by
  unfold EvalBody.evalConditionalCallbackCallCounted; link_tac

theorem EvalBody.evalUserCallbackCallCounted_linkDisc (rec : EvalRec) (hrec : ∀ c, LinkDisc (rec c)) (callee : Algorithm) (args : List CountedResult) (ctx : EvalCtx) (env : ValEnv) :
    LinkDisc (EvalBody.evalUserCallbackCallCounted rec callee args ctx env) := by
  unfold EvalBody.evalUserCallbackCallCounted; link_tac

theorem EvalBody.evalResolvedCallbackCallCounted_linkDisc (rec : EvalRec) (hrec : ∀ c, LinkDisc (rec c)) (callee : Algorithm) (args : List CountedResult) (ctx : EvalCtx) (env : ValEnv) (calleeName : String) :
    LinkDisc (EvalBody.evalResolvedCallbackCallCounted rec callee args ctx env calleeName) := by
  unfold EvalBody.evalResolvedCallbackCallCounted; link_tac

theorem EvalBody.evalResolvedCallbackCall_linkDisc (rec : EvalRec) (hrec : ∀ c, LinkDisc (rec c)) (callee : Algorithm) (args : List CountedResult) (ctx : EvalCtx) (env : ValEnv) (calleeName : String) :
    LinkDisc (EvalBody.evalResolvedCallbackCall rec callee args ctx env calleeName) := by
  unfold EvalBody.evalResolvedCallbackCall; link_tac

theorem EvalBody.evalSequenceReduceStepCounted_linkDisc (rec : EvalRec) (hrec : ∀ c, LinkDisc (rec c)) (callee : Algorithm) (element : CountedResult) (accumulator : Result) (ctx : EvalCtx) (env : ValEnv) (calleeName : String) :
    LinkDisc (EvalBody.evalSequenceReduceStepCounted rec callee element accumulator ctx env calleeName) := by
  unfold EvalBody.evalSequenceReduceStepCounted; link_tac

theorem EvalBody.demandSequenceBuiltinCallItemValue_linkDisc (rec : EvalRec) (hrec : ∀ c, LinkDisc (rec c)) (item : CallableCallItem) (ctx : EvalCtx) (env : ValEnv) :
    LinkDisc (EvalBody.demandSequenceBuiltinCallItemValue rec item ctx env) := by
  unfold EvalBody.demandSequenceBuiltinCallItemValue; link_tac

theorem EvalBody.bindSequenceBuiltinArguments_linkDisc (rec : EvalRec) (hrec : ∀ c, LinkDisc (rec c)) (b : Builtin) (metadata : SequenceBuiltinMetadata) (args : List ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) :
    LinkDisc (EvalBody.bindSequenceBuiltinArguments rec b metadata args ctx env) := by
  unfold EvalBody.bindSequenceBuiltinArguments; link_tac

theorem EvalBody.evalReduceCounted_linkDisc (rec : EvalRec) (hrec : ∀ c, LinkDisc (rec c)) (collection : List CountedResult) (stepAlg : Algorithm) (initial : Result) (ctx : EvalCtx) (env : ValEnv) :
    LinkDisc (EvalBody.evalReduceCounted rec collection stepAlg initial ctx env) := by
  unfold EvalBody.evalReduceCounted; link_tac

theorem EvalBody.evalFilterCounted_linkDisc (rec : EvalRec) (hrec : ∀ c, LinkDisc (rec c)) (items : List CountedResult) (predicateAlg : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    LinkDisc (EvalBody.evalFilterCounted rec items predicateAlg ctx env) := by
  unfold EvalBody.evalFilterCounted; link_tac

theorem EvalBody.evalMapCounted_linkDisc (rec : EvalRec) (hrec : ∀ c, LinkDisc (rec c)) (collection : List CountedResult) (transformAlg : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    LinkDisc (EvalBody.evalMapCounted rec collection transformAlg ctx env) := by
  unfold EvalBody.evalMapCounted; link_tac

theorem EvalBody.applyBuiltinCountedSequence_linkDisc (rec : EvalRec) (hrec : ∀ c, LinkDisc (rec c)) (b : Builtin) (metadata : SequenceBuiltinMetadata) (args : List ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) :
    LinkDisc (EvalBody.applyBuiltinCountedSequence rec b metadata args ctx env) := by
  unfold EvalBody.applyBuiltinCountedSequence; link_tac

-- META-S3-3 enlarged this body (the builtin META binding branch); the same tactic needs more time.
set_option maxHeartbeats 1600000 in
theorem EvalBody.applyBuiltinCounted_linkDisc (rec : EvalRec) (hrec : ∀ c, LinkDisc (rec c)) (b : Builtin) (args : List ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) :
    LinkDisc (EvalBody.applyBuiltinCounted rec b args ctx env) := by
  unfold EvalBody.applyBuiltinCounted; link_tac

theorem EvalBody.applyBuiltin_linkDisc (rec : EvalRec) (hrec : ∀ c, LinkDisc (rec c)) (b : Builtin) (args : List ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) :
    LinkDisc (EvalBody.applyBuiltin rec b args ctx env) := by
  unfold EvalBody.applyBuiltin; link_tac

theorem EvalBody.applyBuiltinCountedResolved_linkDisc (rec : EvalRec) (hrec : ∀ c, LinkDisc (rec c)) (b : Builtin) (args : List ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) :
    LinkDisc (EvalBody.applyBuiltinCountedResolved rec b args ctx env) := by
  unfold EvalBody.applyBuiltinCountedResolved; link_tac

theorem EvalBody.evalExplicitSequenceValueItems_linkDisc (rec : EvalRec) (hrec : ∀ c, LinkDisc (rec c)) (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    LinkDisc (EvalBody.evalExplicitSequenceValueItems rec a ctx env) := by
  unfold EvalBody.evalExplicitSequenceValueItems; link_tac

theorem EvalBody.evalExplicitSequenceValueRowSlots_linkDisc (rec : EvalRec) (hrec : ∀ c, LinkDisc (rec c)) (rows : OutputBundle) (rowCtx : EvalCtx) (env : ValEnv) :
    LinkDisc (EvalBody.evalExplicitSequenceValueRowSlots rec rows rowCtx env) := by
  unfold EvalBody.evalExplicitSequenceValueRowSlots; link_tac

theorem EvalBody.evalExplicitSequenceValueExprSlots_linkDisc (rec : EvalRec) (hrec : ∀ c, LinkDisc (rec c)) (expr : Expr) (ctx : EvalCtx) (env : ValEnv) :
    LinkDisc (EvalBody.evalExplicitSequenceValueExprSlots rec expr ctx env) := by
  unfold EvalBody.evalExplicitSequenceValueExprSlots; link_tac

theorem EvalBody.evalUserCallCounted_linkDisc (rec : EvalRec) (hrec : ∀ c, LinkDisc (rec c)) (callee : Algorithm) (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) :
    LinkDisc (EvalBody.evalUserCallCounted rec callee args ctx env) := by
  unfold EvalBody.evalUserCallCounted; link_tac

theorem EvalBody.evalConditionalCallCounted_linkDisc (rec : EvalRec) (hrec : ∀ c, LinkDisc (rec c)) (callee : Algorithm) (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) (calleeName : String) :
    LinkDisc (EvalBody.evalConditionalCallCounted rec callee args ctx env calleeName) := by
  unfold EvalBody.evalConditionalCallCounted; link_tac

theorem EvalBody.evalResolvedCall_linkDisc (rec : EvalRec) (hrec : ∀ c, LinkDisc (rec c)) (callee : Algorithm) (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) (calleeName : String) :
    LinkDisc (EvalBody.evalResolvedCall rec callee args ctx env calleeName) := by
  unfold EvalBody.evalResolvedCall; link_tac

theorem EvalBody.evalResolvedCallCounted_linkDisc (rec : EvalRec) (hrec : ∀ c, LinkDisc (rec c)) (callee : Algorithm) (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) (calleeName : String) (origin : CalleeOrigin) :
    LinkDisc (EvalBody.evalResolvedCallCounted rec callee args ctx env calleeName origin) := by
  unfold EvalBody.evalResolvedCallCounted; link_tac

theorem EvalBody.evalCallCountedExpr_linkDisc (rec : EvalRec) (hrec : ∀ c, LinkDisc (rec c)) (f : Expr) (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) :
    LinkDisc (EvalBody.evalCallCountedExpr rec f args ctx env) := by
  unfold EvalBody.evalCallCountedExpr; link_tac

theorem EvalBody.callLexicalWithReceiverCounted_linkDisc (rec : EvalRec) (hrec : ∀ c, LinkDisc (rec c)) (name : Ident) (receiver : Expr) (fallback : Expr) (extraArgs : Option OutputBundle) (ctx : EvalCtx) (env : ValEnv) :
    LinkDisc (EvalBody.callLexicalWithReceiverCounted rec name receiver fallback extraArgs ctx env) := by
  unfold EvalBody.callLexicalWithReceiverCounted; link_tac

theorem EvalBody.rejectDotStringIntrinsicArguments_linkDisc (rec : EvalRec) (hrec : ∀ c, LinkDisc (rec c)) (argsOpt : Option OutputBundle) (ctx : EvalCtx) (env : ValEnv) :
    LinkDisc (EvalBody.rejectDotStringIntrinsicArguments rec argsOpt ctx env) := by
  unfold EvalBody.rejectDotStringIntrinsicArguments; link_tac

theorem EvalBody.evalDotStringReceiverValue_linkDisc (rec : EvalRec) (hrec : ∀ c, LinkDisc (rec c)) (target : Expr) (targetAlg : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    LinkDisc (EvalBody.evalDotStringReceiverValue rec target targetAlg ctx env) := by
  unfold EvalBody.evalDotStringReceiverValue; link_tac

set_option maxHeartbeats 4000000 in
theorem EvalBody.evalDotCallCounted_linkDisc (rec : EvalRec) (hrec : ∀ c, LinkDisc (rec c)) (target : Expr) (name : Ident) (fallback : Expr) (argsOpt : Option OutputBundle) (ctx : EvalCtx) (env : ValEnv) :
    LinkDisc (EvalBody.evalDotCallCounted rec target name fallback argsOpt ctx env) := by
  unfold EvalBody.evalDotCallCounted; link_tac

theorem EvalBody.rejectInvokeIntrinsicArguments_linkDisc (rec : EvalRec) (hrec : ∀ c, LinkDisc (rec c)) (argsOpt : Option OutputBundle) (ctx : EvalCtx) (env : ValEnv) :
    LinkDisc (EvalBody.rejectInvokeIntrinsicArguments rec argsOpt ctx env) := by
  unfold EvalBody.rejectInvokeIntrinsicArguments; link_tac

theorem EvalBody.invokeCallReferenceValue_linkDisc (rec : EvalRec) (hrec : ∀ c, LinkDisc (rec c)) (val : Result) :
    LinkDisc (EvalBody.invokeCallReferenceValue rec val) := by
  unfold EvalBody.invokeCallReferenceValue; link_tac

theorem EvalBody.argumentViewCells_linkDisc (rec : EvalRec) (hrec : ∀ c, LinkDisc (rec c)) (a : Nat) :
    LinkDisc (EvalBody.argumentViewCells rec a) := by
  unfold EvalBody.argumentViewCells; link_tac

theorem EvalBody.evalArgumentViewBuiltin_linkDisc (rec : EvalRec) (hrec : ∀ c, LinkDisc (rec c)) (b : Builtin) (a : Nat) :
    LinkDisc (EvalBody.evalArgumentViewBuiltin rec b a) := by
  unfold EvalBody.evalArgumentViewBuiltin; link_tac

theorem EvalBody.evalSequenceSpreadOperandValue_linkDisc (rec : EvalRec) (hrec : ∀ c, LinkDisc (rec c)) (e : Expr) (ctx : EvalCtx) (env : ValEnv) :
    LinkDisc (EvalBody.evalSequenceSpreadOperandValue rec e ctx env) := by
  unfold EvalBody.evalSequenceSpreadOperandValue; link_tac

theorem EvalBody.evalSequenceSpreadCounted_linkDisc (rec : EvalRec) (hrec : ∀ c, LinkDisc (rec c)) (e : Expr) (ctx : EvalCtx) (env : ValEnv) :
    LinkDisc (EvalBody.evalSequenceSpreadCounted rec e ctx env) := by
  unfold EvalBody.evalSequenceSpreadCounted; link_tac

theorem EvalBody.evalSupplySpread_linkDisc (rec : EvalRec) (hrec : ∀ c, LinkDisc (rec c)) (e : Expr) (ctx : EvalCtx) (env : ValEnv) :
    LinkDisc (EvalBody.evalSupplySpread rec e ctx env) := by
  unfold EvalBody.evalSupplySpread; link_tac

theorem EvalBody.evalListLiteralCounted_linkDisc (rec : EvalRec) (hrec : ∀ c, LinkDisc (rec c)) (elements : List Expr) (ctx : EvalCtx) (env : ValEnv) :
    LinkDisc (EvalBody.evalListLiteralCounted rec elements ctx env) := by
  unfold EvalBody.evalListLiteralCounted; link_tac

theorem EvalBody.evalSequenceConstructCounted_linkDisc (rec : EvalRec) (hrec : ∀ c, LinkDisc (rec c)) (e : Expr) (ctx : EvalCtx) (env : ValEnv) :
    LinkDisc (EvalBody.evalSequenceConstructCounted rec e ctx env) := by
  unfold EvalBody.evalSequenceConstructCounted; link_tac

theorem EvalBody.evalUnaryCounted_linkDisc (rec : EvalRec) (hrec : ∀ c, LinkDisc (rec c)) (op : UnaryOp) (operand : Expr) (ctx : EvalCtx) (env : ValEnv) :
    LinkDisc (EvalBody.evalUnaryCounted rec op operand ctx env) := by
  unfold EvalBody.evalUnaryCounted; link_tac

theorem EvalBody.evalBinaryCounted_linkDisc (rec : EvalRec) (hrec : ∀ c, LinkDisc (rec c)) (op : BinaryOp) (a b : Expr) (ctx : EvalCtx) (env : ValEnv) :
    LinkDisc (EvalBody.evalBinaryCounted rec op a b ctx env) := by
  unfold EvalBody.evalBinaryCounted; link_tac

theorem EvalBody.evalComparisonCounted_linkDisc (rec : EvalRec) (hrec : ∀ c, LinkDisc (rec c)) (first : Expr) (links : List ComparisonLink) (ctx : EvalCtx) (env : ValEnv) :
    LinkDisc (EvalBody.evalComparisonCounted rec first links ctx env) := by
  unfold EvalBody.evalComparisonCounted; link_tac

theorem EvalBody.evalComparisonLinksCounted_linkDisc (rec : EvalRec) (hrec : ∀ c, LinkDisc (rec c)) (previousExpr : Expr) (previous : Result) (holds : Bool) (links : List ComparisonLink) (ctx : EvalCtx) (env : ValEnv) :
    LinkDisc (EvalBody.evalComparisonLinksCounted rec previousExpr previous holds links ctx env) := by
  unfold EvalBody.evalComparisonLinksCounted; link_tac

theorem EvalBody.evalCounted_linkDisc (rec : EvalRec) (hrec : ∀ c, LinkDisc (rec c)) (e : Expr) (ctx : EvalCtx) (env : ValEnv) :
    LinkDisc (EvalBody.evalCounted rec e ctx env) := by
  unfold EvalBody.evalCounted; link_tac

theorem EvalBody.evalUserCall_linkDisc (rec : EvalRec) (hrec : ∀ c, LinkDisc (rec c)) (callee : Algorithm) (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) :
    LinkDisc (EvalBody.evalUserCall rec callee args ctx env) := by
  unfold EvalBody.evalUserCall; link_tac

theorem EvalBody.evalConditionalCall_linkDisc (rec : EvalRec) (hrec : ∀ c, LinkDisc (rec c)) (callee : Algorithm) (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) (calleeName : String) :
    LinkDisc (EvalBody.evalConditionalCall rec callee args ctx env calleeName) := by
  unfold EvalBody.evalConditionalCall; link_tac

theorem EvalBody.evalCallExpr_linkDisc (rec : EvalRec) (hrec : ∀ c, LinkDisc (rec c)) (f : Expr) (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) :
    LinkDisc (EvalBody.evalCallExpr rec f args ctx env) := by
  unfold EvalBody.evalCallExpr; link_tac

theorem EvalBody.evalDotCall_linkDisc (rec : EvalRec) (hrec : ∀ c, LinkDisc (rec c)) (target : Expr) (name : Ident) (fallback : Expr) (argsOpt : Option OutputBundle) (ctx : EvalCtx) (env : ValEnv) :
    LinkDisc (EvalBody.evalDotCall rec target name fallback argsOpt ctx env) := by
  unfold EvalBody.evalDotCall; link_tac

theorem EvalBody.eval_linkDisc (rec : EvalRec) (hrec : ∀ c, LinkDisc (rec c)) (e : Expr) (ctx : EvalCtx) (env : ValEnv) :
    LinkDisc (EvalBody.eval rec e ctx env) := by
  unfold EvalBody.eval; link_tac

theorem evalStep_linkDisc (rec : EvalRec) (hrec : ∀ c, LinkDisc (rec c)) :
    ∀ c, LinkDisc (evalStep rec c) := by
  intro c
  cases c with
  | whileLoop step ctx env stepName cells => exact EvalBody.whileLoop_linkDisc rec hrec step ctx env stepName cells
  | aliasStepIsRuntime step target ctx => exact EvalBody.aliasStepIsRuntime_linkDisc rec hrec step target ctx
  | aliasValue wired ctx env => exact EvalBody.aliasValue_linkDisc rec hrec wired ctx env
  | resolveAliasChase callable a ctx visited projectedFrom => exact EvalBody.resolveAliasChase_linkDisc rec hrec callable a ctx visited projectedFrom
  | resolveAliasTarget a ctx => exact EvalBody.resolveAliasTarget_linkDisc rec hrec a ctx
  | resolveAliasValueTarget a ctx => exact EvalBody.resolveAliasValueTarget_linkDisc rec hrec a ctx
  | lookupLexicalProperty a name ctx => exact EvalBody.lookupLexicalProperty_linkDisc rec hrec a name ctx
  | lookupLexicalValueProperty a name ctx => exact EvalBody.lookupLexicalValueProperty_linkDisc rec hrec a name ctx
  | lookupLexical a name ctx => exact EvalBody.lookupLexical_linkDisc rec hrec a name ctx
  | needPlanNormalizeCallee callee ctx => exact EvalBody.needPlanNormalizeCallee_linkDisc rec hrec callee ctx
  | resolveAlg e ctx => exact EvalBody.resolveAlg_linkDisc rec hrec e ctx
  | projectNeedCallable address => exact EvalBody.projectNeedCallable_linkDisc rec hrec address
  | projectNeedWrittenAt address source caller => exact EvalBody.projectNeedWrittenAt_linkDisc rec hrec address source caller
  | linkCallable address => exact EvalBody.linkCallable_linkDisc rec hrec address
  | projectParameterCallable x ctx => exact EvalBody.projectParameterCallable_linkDisc rec hrec x ctx
  | projectNeedWritten source caller => exact EvalBody.projectNeedWritten_linkDisc rec hrec source caller
  | projectNeedStructuralMember source ctx => exact EvalBody.projectNeedStructuralMember_linkDisc rec hrec source ctx
  | resolveCalleeAlg f ctx => exact EvalBody.resolveCalleeAlg_linkDisc rec hrec f ctx
  | expectPreparedSequenceBuiltinAlgorithmSuffixArg b descriptors args index => exact EvalBody.expectPreparedSequenceBuiltinAlgorithmSuffixArg_linkDisc rec hrec b descriptors args index
  | resolveDotReceiver? e ctx => exact EvalBody.resolveDotReceiver?_linkDisc rec hrec e ctx
  | resolveDotReceiver e ctx => exact EvalBody.resolveDotReceiver_linkDisc rec hrec e ctx
  | algorithmIntrinsicRoute receiver ctx => exact EvalBody.algorithmIntrinsicRoute_linkDisc rec hrec receiver ctx
  | demandNeedRecursive address => exact EvalBody.demandNeedRecursive_linkDisc rec hrec address
  | evalSuppliedAt address e ctx env => exact EvalBody.evalSuppliedAt_linkDisc rec hrec address e ctx env
  | linkValue address => exact EvalBody.linkValue_linkDisc rec hrec address
  | algorithmOfValue val argsOpt ctx env => exact EvalBody.algorithmOfValue_linkDisc rec hrec val argsOpt ctx env
  | capturedCallee callee => exact EvalBody.capturedCallee_linkDisc rec hrec callee
  | referenceReceiverValue target targetAlg ctx env => exact EvalBody.referenceReceiverValue_linkDisc rec hrec target targetAlg ctx env
  | algorithmCalleeOf receiver ctx env => exact EvalBody.algorithmCalleeOf_linkDisc rec hrec receiver ctx env
  | evalSuppliedCallCounted origin callee cells ctx env calleeName => exact EvalBody.evalSuppliedCallCounted_linkDisc rec hrec origin callee cells ctx env calleeName
  | evalNeedUserSupply callee cells ctx env => exact EvalBody.evalNeedUserSupply_linkDisc rec hrec callee cells ctx env
  | evalNeedFamilySupply callee cells ctx env calleeName => exact EvalBody.evalNeedFamilySupply_linkDisc rec hrec callee cells ctx env calleeName
  | invokeNeed arg => exact EvalBody.invokeNeed_linkDisc rec hrec arg
  | argumentNeed arg ctx env => exact EvalBody.argumentNeed_linkDisc rec hrec arg ctx env
  | runNeedStepSlots step ctx env cells stepName => exact EvalBody.runNeedStepSlots_linkDisc rec hrec step ctx env cells stepName
  | runNeedWhileRound step ctx env cells stepName => exact EvalBody.runNeedWhileRound_linkDisc rec hrec step ctx env cells stepName
  | evalAlgOutputCore a ctx env => exact EvalBody.evalAlgOutputCore_linkDisc rec hrec a ctx env
  | evalAlgOutput a ctx env => exact EvalBody.evalAlgOutput_linkDisc rec hrec a ctx env
  | evalProgramOutput a ctx env => exact EvalBody.evalProgramOutput_linkDisc rec hrec a ctx env
  | evalAlgOutputSlots a ctx env => exact EvalBody.evalAlgOutputSlots_linkDisc rec hrec a ctx env
  | formOutputRow ctx env e => exact EvalBody.formOutputRow_linkDisc rec hrec ctx env e
  | whileVerdictSlots a ctx env => exact EvalBody.whileVerdictSlots_linkDisc rec hrec a ctx env
  | evalSequenceCallbackCall callee item ctx env calleeName => exact EvalBody.evalSequenceCallbackCall_linkDisc rec hrec callee item ctx env calleeName
  | evalSequenceCallbackCallCounted callee item ctx env calleeName => exact EvalBody.evalSequenceCallbackCallCounted_linkDisc rec hrec callee item ctx env calleeName
  | evalAlgOutputPreparedCore a ctx env => exact EvalBody.evalAlgOutputPreparedCore_linkDisc rec hrec a ctx env
  | evalOutputRowsPreparedCore rows rowCtx env => exact EvalBody.evalOutputRowsPreparedCore_linkDisc rec hrec rows rowCtx env
  | evalCapturePreparedCore rows ctx env => exact EvalBody.evalCapturePreparedCore_linkDisc rec hrec rows ctx env
  | evalCaptureCountedCore rows ctx env => exact EvalBody.evalCaptureCountedCore_linkDisc rec hrec rows ctx env
  | evalCaptureValue rows ctx env => exact EvalBody.evalCaptureValue_linkDisc rec hrec rows ctx env
  | evalAlgOutputCountedCore a ctx env => exact EvalBody.evalAlgOutputCountedCore_linkDisc rec hrec a ctx env
  | evalAlgOutputCounted a ctx env => exact EvalBody.evalAlgOutputCounted_linkDisc rec hrec a ctx env
  | evalZeroArgumentDemandOutputCounted a ctx env => exact EvalBody.evalZeroArgumentDemandOutputCounted_linkDisc rec hrec a ctx env
  | evalZeroArgumentDemandOutput a ctx env => exact EvalBody.evalZeroArgumentDemandOutput_linkDisc rec hrec a ctx env
  | evalArgumentValueCounted arg ctx env => exact EvalBody.evalArgumentValueCounted_linkDisc rec hrec arg ctx env
  | evalArgumentValue arg ctx env => exact EvalBody.evalArgumentValue_linkDisc rec hrec arg ctx env
  | evalZeroArgPropertyAccessCounted accessKind owner binding resolvedAlgorithm ctx env request => exact EvalBody.evalZeroArgPropertyAccessCounted_linkDisc rec hrec accessKind owner binding resolvedAlgorithm ctx env request
  | evalZeroArgPropertyAccess accessKind owner binding resolvedAlgorithm ctx env => exact EvalBody.evalZeroArgPropertyAccess_linkDisc rec hrec accessKind owner binding resolvedAlgorithm ctx env
  | evalConditionalCallbackCallCounted callee args ctx env calleeName => exact EvalBody.evalConditionalCallbackCallCounted_linkDisc rec hrec callee args ctx env calleeName
  | evalUserCallbackCallCounted callee args ctx env => exact EvalBody.evalUserCallbackCallCounted_linkDisc rec hrec callee args ctx env
  | evalResolvedCallbackCallCounted callee args ctx env calleeName => exact EvalBody.evalResolvedCallbackCallCounted_linkDisc rec hrec callee args ctx env calleeName
  | evalResolvedCallbackCall callee args ctx env calleeName => exact EvalBody.evalResolvedCallbackCall_linkDisc rec hrec callee args ctx env calleeName
  | evalSequenceReduceStepCounted callee element accumulator ctx env calleeName => exact EvalBody.evalSequenceReduceStepCounted_linkDisc rec hrec callee element accumulator ctx env calleeName
  | demandSequenceBuiltinCallItemValue item ctx env => exact EvalBody.demandSequenceBuiltinCallItemValue_linkDisc rec hrec item ctx env
  | bindSequenceBuiltinArguments b metadata args ctx env => exact EvalBody.bindSequenceBuiltinArguments_linkDisc rec hrec b metadata args ctx env
  | evalReduceCounted collection stepAlg initial ctx env => exact EvalBody.evalReduceCounted_linkDisc rec hrec collection stepAlg initial ctx env
  | evalFilterCounted items predicateAlg ctx env => exact EvalBody.evalFilterCounted_linkDisc rec hrec items predicateAlg ctx env
  | evalMapCounted collection transformAlg ctx env => exact EvalBody.evalMapCounted_linkDisc rec hrec collection transformAlg ctx env
  | applyBuiltinCountedSequence b metadata args ctx env => exact EvalBody.applyBuiltinCountedSequence_linkDisc rec hrec b metadata args ctx env
  | applyBuiltinCounted b args ctx env => exact EvalBody.applyBuiltinCounted_linkDisc rec hrec b args ctx env
  | applyBuiltin b args ctx env => exact EvalBody.applyBuiltin_linkDisc rec hrec b args ctx env
  | applyBuiltinCountedResolved b args ctx env => exact EvalBody.applyBuiltinCountedResolved_linkDisc rec hrec b args ctx env
  | evalExplicitSequenceValueItems a ctx env => exact EvalBody.evalExplicitSequenceValueItems_linkDisc rec hrec a ctx env
  | evalExplicitSequenceValueRowSlots rows rowCtx env => exact EvalBody.evalExplicitSequenceValueRowSlots_linkDisc rec hrec rows rowCtx env
  | evalExplicitSequenceValueExprSlots expr ctx env => exact EvalBody.evalExplicitSequenceValueExprSlots_linkDisc rec hrec expr ctx env
  | evalUserCallCounted callee args ctx env => exact EvalBody.evalUserCallCounted_linkDisc rec hrec callee args ctx env
  | evalConditionalCallCounted callee args ctx env calleeName => exact EvalBody.evalConditionalCallCounted_linkDisc rec hrec callee args ctx env calleeName
  | evalResolvedCall callee args ctx env calleeName => exact EvalBody.evalResolvedCall_linkDisc rec hrec callee args ctx env calleeName
  | evalResolvedCallCounted callee args ctx env calleeName origin => exact EvalBody.evalResolvedCallCounted_linkDisc rec hrec callee args ctx env calleeName origin
  | evalCallCountedExpr f args ctx env => exact EvalBody.evalCallCountedExpr_linkDisc rec hrec f args ctx env
  | callLexicalWithReceiverCounted name receiver fallback extraArgs ctx env => exact EvalBody.callLexicalWithReceiverCounted_linkDisc rec hrec name receiver fallback extraArgs ctx env
  | rejectDotStringIntrinsicArguments argsOpt ctx env => exact EvalBody.rejectDotStringIntrinsicArguments_linkDisc rec hrec argsOpt ctx env
  | evalDotStringReceiverValue target targetAlg ctx env => exact EvalBody.evalDotStringReceiverValue_linkDisc rec hrec target targetAlg ctx env
  | evalDotCallCounted target name fallback argsOpt ctx env => exact EvalBody.evalDotCallCounted_linkDisc rec hrec target name fallback argsOpt ctx env
  | rejectInvokeIntrinsicArguments argsOpt ctx env => exact EvalBody.rejectInvokeIntrinsicArguments_linkDisc rec hrec argsOpt ctx env
  | invokeCallReferenceValue val => exact EvalBody.invokeCallReferenceValue_linkDisc rec hrec val
  | argumentViewCells a => exact EvalBody.argumentViewCells_linkDisc rec hrec a
  | evalArgumentViewBuiltin b a => exact EvalBody.evalArgumentViewBuiltin_linkDisc rec hrec b a
  | evalSequenceSpreadOperandValue e ctx env => exact EvalBody.evalSequenceSpreadOperandValue_linkDisc rec hrec e ctx env
  | evalSequenceSpreadCounted e ctx env => exact EvalBody.evalSequenceSpreadCounted_linkDisc rec hrec e ctx env
  | evalSupplySpread e ctx env => exact EvalBody.evalSupplySpread_linkDisc rec hrec e ctx env
  | evalListLiteralCounted elements ctx env => exact EvalBody.evalListLiteralCounted_linkDisc rec hrec elements ctx env
  | evalSequenceConstructCounted e ctx env => exact EvalBody.evalSequenceConstructCounted_linkDisc rec hrec e ctx env
  | evalUnaryCounted op operand ctx env => exact EvalBody.evalUnaryCounted_linkDisc rec hrec op operand ctx env
  | evalBinaryCounted op a b ctx env => exact EvalBody.evalBinaryCounted_linkDisc rec hrec op a b ctx env
  | evalComparisonCounted first links ctx env => exact EvalBody.evalComparisonCounted_linkDisc rec hrec first links ctx env
  | evalComparisonLinksCounted previousExpr previous holds links ctx env => exact EvalBody.evalComparisonLinksCounted_linkDisc rec hrec previousExpr previous holds links ctx env
  | evalCounted e ctx env => exact EvalBody.evalCounted_linkDisc rec hrec e ctx env
  | evalUserCall callee args ctx env => exact EvalBody.evalUserCall_linkDisc rec hrec callee args ctx env
  | evalConditionalCall callee args ctx env calleeName => exact EvalBody.evalConditionalCall_linkDisc rec hrec callee args ctx env calleeName
  | evalCallExpr f args ctx env => exact EvalBody.evalCallExpr_linkDisc rec hrec f args ctx env
  | evalDotCall target name fallback argsOpt ctx env => exact EvalBody.evalDotCall_linkDisc rec hrec target name fallback argsOpt ctx env
  | eval e ctx env => exact EvalBody.eval_linkDisc rec hrec e ctx env

/-! ## Whole-run link discipline of the production evaluator -/

/-- Every evaluator body keeps the FG-M1 facts whenever its recursive answer does. -/
theorem body_step_linkDisc : ∀ rec : EvalRec,
    (∀ c, Preserves (fun s t => LinkHeapKept s.needs t.needs) (rec c)) →
    ∀ c, Preserves (fun s t => LinkHeapKept s.needs t.needs) (evalStep rec c) :=
  fun rec hrec c => evalStep_linkDisc rec hrec c

/-- **Every completed run of the total core, at every fuel, from every state, keeps every existing
    cell's completed CALLABLE outcome, recorded callee and recorded receiver** (the completion
    predicate of R7: an ordinary error is a completed run; `fuelExhausted` is not). -/
theorem evalFuel_linkDisc (n : Nat) (c : EvalCall) (s : EvalState)
    (hc : Completes (evalFuel n c) s) :
    LinkHeapKept s.needs ((evalFuel n c).runState s).2.needs :=
  invariant_transfer (fun s t => LinkHeapKept s.needs t.needs) (fun _ => LinkHeapKept.refl _)
    body_step_linkDisc n c s hc

/-- **Every production evaluator operation keeps the FG-M1 facts**, over EVERY entry state and
    whatever its outcome. For a run that never completes, the kernel-level fallback of
    `evalUnbounded` returns the entry state (`production_incomplete_state`), which keeps them
    trivially: this is not a termination claim. -/
theorem evalUnbounded_linkDisc (c : EvalCall) : LinkDisc (evalUnbounded c) :=
  production_preserves (fun s t => LinkHeapKept s.needs t.needs) (fun _ => LinkHeapKept.refl _)
    body_step_linkDisc c

/-- Both whole-run relations at once, for a completed core run. -/
theorem evalFuel_memoKept (n : Nat) (c : EvalCall) (s : EvalState)
    (hc : Completes (evalFuel n c) s) :
    MemoKept s.needs ((evalFuel n c).runState s).2.needs :=
  ⟨KatLang.EvaluatorDiscipline.evalFuel_disciplined n c s hc, evalFuel_linkDisc n c s hc⟩

/-- Both whole-run relations at once, for every production operation. -/
theorem evalUnbounded_memoKept (c : EvalCall) (s : EvalState) :
    MemoKept s.needs ((evalUnbounded c).runState s).2.needs :=
  ⟨KatLang.EvaluatorDiscipline.evalUnbounded_disciplined c s, evalUnbounded_linkDisc c s⟩

/-- **FG-M1, the principal production theorem.** For every production operation `c` and every
    entry state `s`, every cell present at an address `a` of `s` is still present at `a` in the
    retained state of `(evalUnbounded c).runState s` — after success OR ordinary failure — and
    keeps the established facts (`CellKept`: suspension, completed VALUE, prepared supply, recorded
    route) and EXACTLY its completed CALLABLE outcome, its recorded callee cell and its recorded
    receiver cell. -/
theorem production_keeps_memo_links (c : EvalCall) (s : EvalState) (a : Nat) (cell : NeedCell)
    (hc : s.needs[a]? = some cell) :
    ∃ cell', ((evalUnbounded c).runState s).2.needs[a]? = some cell' ∧ CellKept cell cell' ∧
      (∀ o, cell.callable = .projected o → cell'.callable = .projected o) ∧
      (∀ x, cell.callee = some x → cell'.callee = some x) ∧
      (∀ x, cell.receiver = some x → cell'.receiver = some x) := by
  obtain ⟨cell', h', k, l⟩ := (evalUnbounded_memoKept c s).cell a cell hc
  exact ⟨cell', h', k, l.callable, l.callee, l.receiver⟩

/-- The same, read off an ORDINARY FAILURE's retained state. -/
theorem production_failure_keeps_memo_links (c : EvalCall) (s t : EvalState) (e : Error)
    (hrun : (evalUnbounded c).runState s = (.error e, t)) (a : Nat) (cell : NeedCell)
    (hc : s.needs[a]? = some cell) :
    ∃ cell', t.needs[a]? = some cell' ∧ CellKept cell cell' ∧ LinkKept cell cell' := by
  have := (evalUnbounded_memoKept c s).cell a cell hc
  rw [hrun] at this
  exact this

/-! ### Finite sequences of intervening operations -/

/-- The retained state after running production operations one after the other, each from the
    state the previous one LEFT — whatever its outcome (so a failed operation does not stop the
    sequence: its retained state is the next entry state). -/
def runOps : List EvalCall → EvalState → EvalState
  | [], s => s
  | c :: cs, s => runOps cs ((evalUnbounded c).runState s).2

theorem runOps_memoKept : ∀ (ops : List EvalCall) (s : EvalState), MemoKept s.needs (runOps ops s).needs
  | [], _ => MemoKept.refl _
  | c :: cs, s => (evalUnbounded_memoKept c s).trans (runOps_memoKept cs _)

/-- A monadic sequence of production operations (outcomes discarded, the first failure ends it). -/
theorem linkDisc_productionSequence (ops : List EvalCall) :
    LinkDisc (ops.forM fun c => (fun _ => ()) <$> evalUnbounded c) :=
  link_forM ops _ (fun c => LinkDisc.map _ (evalUnbounded_linkDisc c))

/-! ## "After intervening evaluation" reread corollaries -/

/-- A completed CALLABLE outcome survives any link-disciplined computation, and re-projecting it
    — through the ONE projection shell, for ANY projection callback — returns exactly that outcome
    and leaves the state unchanged: the callback never runs again. -/
theorem callable_survives {α : Type} (m : EvalM α) (hm : LinkDisc m)
    (project : NeedSuspension → EvalM (Option Algorithm)) (a : Nat) (s : EvalState) (cell : NeedCell)
    (outcome : Except Error (Option Algorithm))
    (hc : s.needs[a]? = some cell) (hs : cell.callable = .projected outcome) :
    (NeedProjection.step project a).runState (m.runState s).2 = (outcome, (m.runState s).2) := by
  obtain ⟨c', hc', k⟩ := hm s a cell hc
  exact KatLang.NeedControl.Projection.projected_sticky project a _ c' outcome hc' (k.callable outcome hs)

/-- A recorded callee survives any link-disciplined computation; re-observing it — for ANY route
    classifier — returns the same address and changes nothing (no route classification, no supply,
    no record). -/
theorem callee_survives {α : Type} (m : EvalM α) (hm : LinkDisc m)
    (classify : NeedPlan.CallShape → EvalM PlanRoute) (a x : Nat) (s : EvalState) (cell : NeedCell)
    (hc : s.needs[a]? = some cell) (hx : cell.callee = some x) :
    (NeedPlan.calleeCell classify a).runState (m.runState s).2 = (.ok x, (m.runState s).2) := by
  obtain ⟨c', hc', k⟩ := hm s a cell hc
  exact calleeCell_recorded classify a x _ c' hc' (k.callee x hx)

/-- A recorded receiver survives any link-disciplined computation; re-observing it returns the same
    address and changes nothing (no supply, no record). -/
theorem receiver_survives {α : Type} (m : EvalM α) (hm : LinkDisc m)
    (a x : Nat) (s : EvalState) (cell : NeedCell)
    (hc : s.needs[a]? = some cell) (hx : cell.receiver = some x) :
    (NeedLink.receiverCell a).runState (m.runState s).2 = (.ok x, (m.runState s).2) := by
  obtain ⟨c', hc', k⟩ := hm s a cell hc
  exact receiverCell_recorded a x _ c' hc' (k.receiver x hx)

theorem evalStep_projectNeedCallable (rec : EvalRec) (a : Nat) :
    evalStep rec (.projectNeedCallable a) =
      NeedProjection.step (NeedProjection.suspended (rec.projectNeedWrittenAt a)) a := rfl

/-- **The production CALLABLE reread.** At a state where cell `a`'s CALLABLE is completed with
    `outcome`, the production `projectNeedCallable a` returns exactly `outcome` and leaves the state
    unchanged — unconditionally (an `outcome` that is itself `fuelExhausted` is returned by the
    kernel-level fallback, again with the state unchanged). -/
theorem projectNeedCallable_projected (a : Nat) (t : EvalState) (cell : NeedCell)
    (outcome : Except Error (Option Algorithm))
    (hc : t.needs[a]? = some cell) (hs : cell.callable = .projected outcome) :
    (projectNeedCallable a).runState t = (outcome, t) := by
  have hbody : ∀ rec : EvalRec, (evalStep rec (.projectNeedCallable a)).runState t = (outcome, t) :=
    fun rec => KatLang.NeedControl.Projection.projected_sticky _ a t cell outcome hc hs
  show (evalUnbounded (.projectNeedCallable a)).runState t = (outcome, t)
  by_cases hinc : outcome = .error .fuelExhausted
  · subst hinc
    apply production_incomplete_state
    intro hpc
    obtain ⟨m, _, hm⟩ := (production_completes_iff _ t _).1 ⟨rfl, hpc⟩
    cases m with
    | zero => exact hm rfl
    | succ k =>
      apply hm
      unfold EvalM.IsIncompleteAt
      rw [evalFuel_succ]
      exact normalize_of_incomplete _ t (by rw [hbody])
  · have hfuel : (evalFuel 1 (.projectNeedCallable a)).runState t = (outcome, t) := by
      rw [evalFuel_succ, normalize_of_complete _ t (by rw [hbody]; exact hinc), hbody]
    exact ((production_completes_iff _ t _).2
      ⟨1, hfuel, (evalFuel_completes_iff 1 _ t).2 (by rw [hfuel]; exact hinc)⟩).1

/-- **FG-M1 CALLABLE corollary over production.** A cell whose CALLABLE is completed — identity
    `.ok (some g)`, successful absence `.ok none` or failure `.error e` — at the entry of ANY
    production operation still holds exactly that outcome afterwards, and the production
    `projectNeedCallable` then returns it with no effect. -/
theorem production_callable_reread (c : EvalCall) (a : Nat) (s : EvalState) (cell : NeedCell)
    (outcome : Except Error (Option Algorithm))
    (hc : s.needs[a]? = some cell) (hs : cell.callable = .projected outcome) :
    (∃ cell', ((evalUnbounded c).runState s).2.needs[a]? = some cell' ∧
        cell'.callable = .projected outcome) ∧
    (projectNeedCallable a).runState ((evalUnbounded c).runState s).2 =
      (outcome, ((evalUnbounded c).runState s).2) := by
  obtain ⟨c', hc', k⟩ := evalUnbounded_linkDisc c s a cell hc
  exact ⟨⟨c', hc', k.callable outcome hs⟩, projectNeedCallable_projected a _ c' outcome hc' (k.callable outcome hs)⟩

/-- The same after a finite sequence of production operations. -/
theorem runOps_callable_reread (ops : List EvalCall) (a : Nat) (s : EvalState) (cell : NeedCell)
    (outcome : Except Error (Option Algorithm))
    (hc : s.needs[a]? = some cell) (hs : cell.callable = .projected outcome) :
    (projectNeedCallable a).runState (runOps ops s) = (outcome, runOps ops s) := by
  obtain ⟨c', hc', k⟩ := (runOps_memoKept ops s).2 a cell hc
  exact projectNeedCallable_projected a _ c' outcome hc' (k.callable outcome hs)

/-- **FG-M1 callee corollary over production.** A recorded callee cell survives any production
    operation, and the canonical-callee accessor — over the production route classifier or any
    other — then returns the same address with no effect. -/
theorem production_callee_reread (c : EvalCall) (classify : NeedPlan.CallShape → EvalM PlanRoute)
    (a x : Nat) (s : EvalState) (cell : NeedCell)
    (hc : s.needs[a]? = some cell) (hx : cell.callee = some x) :
    (NeedPlan.calleeCell classify a).runState ((evalUnbounded c).runState s).2 =
      (.ok x, ((evalUnbounded c).runState s).2) :=
  callee_survives _ (evalUnbounded_linkDisc c) classify a x s cell hc hx

/-- **FG-M1 receiver corollary over production.** -/
theorem production_receiver_reread (c : EvalCall) (a x : Nat) (s : EvalState) (cell : NeedCell)
    (hc : s.needs[a]? = some cell) (hx : cell.receiver = some x) :
    (NeedLink.receiverCell a).runState ((evalUnbounded c).runState s).2 =
      (.ok x, ((evalUnbounded c).runState s).2) :=
  receiver_survives _ (evalUnbounded_linkDisc c) a x s cell hc hx

theorem runOps_callee_reread (ops : List EvalCall) (classify : NeedPlan.CallShape → EvalM PlanRoute)
    (a x : Nat) (s : EvalState) (cell : NeedCell)
    (hc : s.needs[a]? = some cell) (hx : cell.callee = some x) :
    (NeedPlan.calleeCell classify a).runState (runOps ops s) = (.ok x, runOps ops s) := by
  obtain ⟨c', hc', k⟩ := (runOps_memoKept ops s).2 a cell hc
  exact calleeCell_recorded classify a x _ c' hc' (k.callee x hx)

theorem runOps_receiver_reread (ops : List EvalCall) (a x : Nat) (s : EvalState) (cell : NeedCell)
    (hc : s.needs[a]? = some cell) (hx : cell.receiver = some x) :
    (NeedLink.receiverCell a).runState (runOps ops s) = (.ok x, runOps ops s) := by
  obtain ⟨c', hc', k⟩ := (runOps_memoKept ops s).2 a cell hc
  exact receiverCell_recorded a x _ c' hc' (k.receiver x hx)

/-- The production plan-route classifier keeps the FG-M1 facts. -/
theorem classify_linkDisc (shape : NeedPlan.CallShape) :
    LinkDisc (classifyPlanRouteWith resolveDotReceiver? algorithmIntrinsicRoute shape) := by
  unfold classifyPlanRouteWith
  split
  · split
    · exact LinkDisc.bind (evalUnbounded_linkDisc (.algorithmIntrinsicRoute _ _))
        (fun b => by split <;> exact linkDisc_pure _)
    · exact linkDisc_pure _
  · exact LinkDisc.bind (evalUnbounded_linkDisc (.resolveDotReceiver? _ _))
      (fun t => by split <;> first | exact linkDisc_throw _ | exact linkDisc_pure _)

/-- The public VALUE demand (whose callbacks are the production operations) keeps the FG-M1 facts. -/
theorem demandNeed_linkDisc (a : Nat) : LinkDisc (demandNeed a) := by
  unfold demandNeed
  apply linkDisc_step
  · exact fun e c v => evalUnbounded_linkDisc (.evalSuppliedAt a e c v)
  · exact fun e c v => evalUnbounded_linkDisc (.evalSupplySpread e c v)
  · exact fun f c => evalUnbounded_linkDisc (.resolveCalleeAlg f c)
  · exact fun g c => evalUnbounded_linkDisc (.needPlanNormalizeCallee g c)
  · exact fun o g cells c v n => evalUnbounded_linkDisc (.evalSuppliedCallCounted o g cells c v n)
  · exact classify_linkDisc
  · exact fun b => evalUnbounded_linkDisc (.projectNeedCallable b)
  · exact fun b => evalUnbounded_linkDisc (.demandNeedRecursive b)

end KatLang.MemoLinks
