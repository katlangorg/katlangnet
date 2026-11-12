import Lean
import KatLangArityLaws.EvaluatorMemoLinks
import KatLangArityLaws.PlanRouteBridge

open KatLang KatLang.CallPlan KatLang.EvaluatorCore KatLang.AlgorithmProjectionLaws

/-!
# E-18 step 1 (M1): every CALLABLE identity production PUBLISHES is accounted for

`MemoLinks.LinkHeapKept` says what a production operation KEEPS of the CALLABLE memos it found. It
says nothing of the memos the operation WRITES: a state could hold any algorithm as a completed
CALLABLE (`StoredCallableNormal.storedCallableNeedNotBeNormal`), and nothing so far excluded that a
production projection publishes a transparent reference. This module proves the companion
relation, in the same per-body style:

* `Accounted h g`: the identity `g` is STRUCTURE-NORMAL (`PlanRouteBridge.structureNormal`: no
  transparent reference), or it is a completed CALLABLE identity of some cell of the heap `h`;
* `PubHeapKept h h'`: **every identity published in `h'` is accounted for in `h`** — it is
  structure-normal, or it was already a published identity of `h` (at any address);
* `PubDisc m`: `m` relates EVERY entry heap to its exit heap by `PubHeapKept`, whatever its outcome.

The relation is UNCONDITIONAL — no premise on the entry heap — which is what makes it a whole-run
relation: an arbitrary heap may hold a reference as a completed CALLABLE, and a parameter that
forwards that cell publishes the same reference again; that identity is accounted for by the cell
it came from. On a heap whose published identities are all structure-normal (`NormalHeap`, the
empty heap first) the relation leaves only the first disjunct (`PubHeapKept.normal`).

The CALLABLE field has ONE writer, `NeedProjection.step`, which publishes its callback's outcome.
`pubDisc_projectionStep` therefore needs, besides the callback's own `PubDisc`, a RESULT contract:
an identity the callback returns is accounted for in the callback's exit heap (`hres`). Every other
writer keeps the field of the cell it rewrites (`pubKept_of_same`) or pushes a cell with the
default CALLABLE (`PubHeapKept.push`). `evalStep_pubDisc` is the per-body step: every evaluator
body keeps the relation whenever its recursive answer does AND the answer's written-projection
callback satisfies the result contract (`ResSusp`). The result contracts themselves, the transfer
through the fuel core and production, and the consequences for `structureNormal` are in
`PublishedCallableNormal`.

GENERATED from `EvaluatorMemoLinks.lean` (the `link_tac` procedure and its body lemmas under a
renaming) by `artifacts/validation/e18-step1-m1-review-20261112/scratch/gen_publications.py`; the
relation, its API lemmas and `pubDisc_projectionStep` are hand-written in that script's header
files. Not claimed: anything about a cell's VALUE, addresses, activations, or C#.
-/

-- Every body lemma carries the result contract `hres`; only the bodies that reach the publishing
-- writer use it.
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace KatLang.Publications

open KatLang.PlanRouteBridge (structureNormal)

/-! ## The relation -/

/-- **Accounted for in `h`.** The identity `g` is structure-normal, or it is the completed
    CALLABLE identity of some cell of `h`. -/
def Accounted (h : Array NeedCell) (g : Algorithm) : Prop :=
  structureNormal g = true ∨ ∃ (b : Nat) (c : NeedCell), h[b]? = some c ∧ c.callable = .projected (.ok (some g))

theorem Accounted.normal {h : Array NeedCell} {g : Algorithm} (hg : structureNormal g = true) :
    Accounted h g := .inl hg

theorem Accounted.published {h : Array NeedCell} {g : Algorithm} {b : Nat} {c : NeedCell}
    (hc : h[b]? = some c) (hg : c.callable = .projected (.ok (some g))) : Accounted h g :=
  .inr ⟨b, c, hc, hg⟩

/-- An optional identity, accounted for when present. -/
def OptAccounted (h : Array NeedCell) (o : Option Algorithm) : Prop := ∀ g, o = some g → Accounted h g

theorem OptAccounted.none {h : Array NeedCell} : OptAccounted h none := fun _ e => by cases e

theorem OptAccounted.some {h : Array NeedCell} {g : Algorithm} (hg : Accounted h g) :
    OptAccounted h (some g) := fun _ e => by cases e; exact hg

/-- The cell relation of a write that publishes NOTHING at the cell it rewrites: an identity the
    cell holds afterwards, it held before. -/
def PubKept (c c' : NeedCell) : Prop :=
  ∀ g, c'.callable = .projected (.ok (some g)) → c.callable = .projected (.ok (some g))

theorem PubKept.refl (c : NeedCell) : PubKept c c := fun _ h => h

theorem PubKept.trans {c d e : NeedCell} (h1 : PubKept c d) (h2 : PubKept d e) : PubKept c e :=
  fun g h => h1 g (h2 g h)

/-- A write that leaves the CALLABLE field alone publishes nothing. (The two further premises keep
    the statement interchangeable with `MemoLinks.linkKept_of_same`.) -/
theorem pubKept_of_same (c c' : NeedCell) (hc : c'.callable = c.callable)
    (_he : c'.callee = c.callee) (_hr : c'.receiver = c.receiver) : PubKept c c' :=
  fun _ h => hc ▸ h

theorem pubKept_of_callable (c c' : NeedCell) (hc : c'.callable = c.callable) : PubKept c c' :=
  fun _ h => hc ▸ h

/-- **THE PUBLICATION RELATION.** Every identity published in `h'` is accounted for in `h`. -/
def PubHeapKept (h h' : Array NeedCell) : Prop :=
  ∀ (a : Nat) (c' : NeedCell) (g : Algorithm), h'[a]? = some c' →
    c'.callable = .projected (.ok (some g)) → Accounted h g

theorem PubHeapKept.refl (h : Array NeedCell) : PubHeapKept h h :=
  fun _ _ _ hc hg => Accounted.published hc hg

/-- An identity accounted for in the later heap is accounted for in the earlier one. -/
theorem Accounted.back {h h' : Array NeedCell} (k : PubHeapKept h h') {g : Algorithm}
    (hg : Accounted h' g) : Accounted h g := by
  rcases hg with hn | ⟨b, c, hc, hp⟩
  · exact .inl hn
  · exact k b c g hc hp

theorem OptAccounted.back {h h' : Array NeedCell} (k : PubHeapKept h h') {o : Option Algorithm}
    (ho : OptAccounted h' o) : OptAccounted h o := fun g e => (ho g e).back k

theorem PubHeapKept.trans {h1 h2 h3 : Array NeedCell} (k1 : PubHeapKept h1 h2) (k2 : PubHeapKept h2 h3) :
    PubHeapKept h1 h3 := fun a c g hc hg => (k2 a c g hc hg).back k1

/-- Heap extension by a cell that holds no completed identity publishes nothing. -/
theorem PubHeapKept.push (h : Array NeedCell) (c : NeedCell)
    (hc : ∀ g, c.callable = .projected (.ok (some g)) → False) : PubHeapKept h (h.push c) := by
  intro a d g hd hg
  rw [Array.getElem?_push] at hd
  split at hd
  · cases hd
    exact absurd hg (hc g)
  · exact Accounted.published hd hg

/-- A write at `a` that publishes nothing at the cell it rewrites. -/
theorem PubHeapKept.modify (h : Array NeedCell) (a : Nat) (f : NeedCell → NeedCell)
    (hf : ∀ c, h[a]? = some c → PubKept c (f c)) : PubHeapKept h (h.modify a f) := by
  intro b c' g hc hg
  rw [modify_get] at hc
  by_cases hab : a = b
  · subst hab
    rw [ite_eq_left rfl] at hc
    cases hcur : h[a]? with
    | none => rw [hcur] at hc; cases hc
    | some c =>
      rw [hcur] at hc
      cases hc
      exact Accounted.published hcur (hf c hcur g hg)
  · rw [ite_eq_right hab] at hc
    exact Accounted.published hc hg

/-- After `h0 ↦ h1`, a write at `a` that publishes nothing at the cell CURRENTLY there. -/
theorem PubHeapKept.modify_anchor {h0 h1 : Array NeedCell} (k : PubHeapKept h0 h1) (a : Nat)
    (g : NeedCell → NeedCell) (hg : ∀ c1, h1[a]? = some c1 → PubKept c1 (g c1)) :
    PubHeapKept h0 (h1.modify a g) :=
  k.trans (PubHeapKept.modify h1 a g hg)

/-- A whole-cell write of the cell CURRENTLY at `a` that publishes nothing there. -/
theorem PubHeapKept.set_bang (h : Array NeedCell) (a : Nat) (c c' : NeedCell) (hc : h[a]? = some c)
    (hk : PubKept c c') : PubHeapKept h (h.set! a c') := by
  intro b d g hd hg
  have ha : a < h.size := KatLang.MemoLinks.lt_of_get hc
  by_cases hab : a = b
  · subst hab
    have hd' : (h.set! a c')[a]? = some c' := by simp [Array.set!, ha]
    rw [hd'] at hd
    cases hd
    exact Accounted.published hc (hk g hg)
  · have hd' : (h.set! a c')[b]? = h[b]? := by simp [Array.set!, hab]
    rw [hd'] at hd
    exact Accounted.published hd hg

/-- `m` publishes only accounted identities, over EVERY entry state, whatever its outcome. -/
def PubDisc {α : Type} (m : EvalM α) : Prop :=
  ∀ s, PubHeapKept s.needs (m.runState s).2.needs

/-- **The result contract of the written-projection callback** of an answer `rec`: an identity the
    callback of `NeedProjection.step` returns is accounted for in the heap the callback leaves. -/
def ResSusp (rec : EvalRec) : Prop :=
  ∀ (a : Nat) (x : NeedSuspension) (s : EvalState) (g : Algorithm) (t : EvalState),
    (NeedProjection.suspended (rec.projectNeedWrittenAt a) x).runState s = (.ok (some g), t) →
    Accounted t.needs g

set_option hygiene false in
/-- Closes the result-contract premise of the publishing writer from the local `hres`. -/
macro "pub_res" : tactic => `(tactic| exact hres _)

theorem pubDisc_of_needs {α : Type} (m : EvalM α)
    (h : ∀ s, (m.runState s).2.needs = s.needs) : PubDisc m := by
  intro s; rw [h s]; exact PubHeapKept.refl _

theorem PubDisc.bind {α β : Type} {m : EvalM α} {f : α → EvalM β}
    (hm : PubDisc m) (hf : ∀ x, PubDisc (f x)) : PubDisc (m >>= f) := by
  intro s
  rw [bind_run]
  have k := hm s
  cases hr : m.runState s with
  | mk out t =>
    rw [hr] at k
    cases out with
    | error e => exact k
    | ok x => exact k.trans (hf x t)

theorem PubDisc.map {α β : Type} {m : EvalM α} (f : α → β) (hm : PubDisc m) : PubDisc (f <$> m) := by
  intro s
  rw [map_run]
  have k := hm s
  cases hr : m.runState s with
  | mk out t => rw [hr] at k; cases out <;> exact k

theorem pubDisc_pure {α : Type} (a : α) : PubDisc (pure a : EvalM α) := pubDisc_of_needs _ (fun _ => rfl)
theorem pubDisc_get : PubDisc (get : EvalM EvalState) := pubDisc_of_needs _ (fun _ => rfl)
theorem pubDisc_throw {α : Type} (e : Error) : PubDisc (throw e : EvalM α) := pubDisc_of_needs _ (fun _ => rfl)
theorem pubDisc_evalError {α : Type} (e : Error) : PubDisc (EvalM.error e : EvalM α) :=
  pubDisc_of_needs _ (fun _ => rfl)
theorem pubDisc_lift {α : Type} (o : Except Error α) : PubDisc (monadLift o : EvalM α) :=
  pubDisc_of_needs _ (fun s => by rw [lift_run])

theorem PubDisc.attempt {α : Type} {m : EvalM α} (hm : PubDisc m) : PubDisc (evalAttempt m) := by
  intro s; rw [evalAttempt_run]; split <;> exact hm s

theorem PubDisc.withCtx {α : Type} {m : EvalM α} (c : String) (hm : PubDisc m) : PubDisc (withCtx c m) := by
  unfold KatLang.withCtx
  refine PubDisc.bind hm.attempt (fun r => ?_)
  cases r with
  | ok x => exact pubDisc_pure x
  | error e => exact pubDisc_evalError _

theorem PubDisc.withNestedMissingOutput {α : Type} {m : EvalM α} (hm : PubDisc m) :
    PubDisc (withNestedMissingOutput m) := by
  unfold KatLang.withNestedMissingOutput
  refine PubDisc.bind hm.attempt (fun r => ?_)
  cases r with
  | ok x => exact pubDisc_pure x
  | error e => exact pubDisc_evalError _

theorem PubDisc.captureMeta (name : Ident) {m : EvalM Nat} (hm : PubDisc m) :
    PubDisc (NeedBinder.captureMeta name m) := by
  intro s
  have k := hm s
  show PubHeapKept s.needs ((NeedBinder.captureMeta name m).runState s).2.needs
  rw [NeedBinder.captureMeta_runState]
  revert k
  rcases m.runState s with ⟨r, t⟩
  intro k
  cases r <;> exact k

theorem pubDisc_allocate (suspension : NeedSuspension) : PubDisc (allocateNeed suspension) := by
  intro s; rw [KatLang.NeedControl.Allocation.allocate_run]; exact PubHeapKept.push _ _ (fun g h => by cases h)

theorem pubDisc_supply (source : Expr) (caller : EvalCtx) (values : ValEnv) :
    PubDisc (supplyNeed source caller values) := by
  intro s
  rcases supply_cases source caller values s with h | h <;> rw [h]
  · exact PubHeapKept.refl _
  · exact PubHeapKept.push _ _ (fun g h => by cases h)

theorem pubDisc_mapM {α β : Type} (f : α → EvalM β) (hf : ∀ x, PubDisc (f x)) (xs : List α) :
    PubDisc (xs.mapM f) := by
  suffices h : ∀ (acc : List β), PubDisc (List.mapM.loop f xs acc) from h []
  induction xs with
  | nil => intro acc; exact pubDisc_pure _
  | cons x rest ih => intro acc; exact PubDisc.bind (hf x) (fun y => ih (y :: acc))

/-- A frame write: a state write that keeps the three fields everywhere. -/
theorem pub_modify (f : EvalState → EvalState) (h : ∀ s : EvalState, PubHeapKept s.needs (f s).needs) :
    PubDisc (modify f : EvalM Unit) := fun s => h s

/-! ## D-3: the invocation-role writes of a planned `.Algorithm` invocation's callee read

`NeedPlan.setInvocation` writes only the `invocation` field — none of the three FG-M1 fields — so
the two suppliers of the E-18 receiver-read correction keep every entry fact. -/

theorem pubDisc_setInvocation (c : Nat) (role : NeedInvocationRole) :
    PubDisc (NeedPlan.setInvocation c role) :=
  pub_modify _ (fun s => PubHeapKept.modify _ c _ (fun _ _ => pubKept_of_same _ _ rfl rfl rfl))

theorem pubDisc_markCalleeLink (eff : NeedPlan.CallShape) (r : PlanRoute) (c : Nat) :
    PubDisc (NeedPlan.markCalleeLink eff r c) := by
  unfold NeedPlan.markCalleeLink
  split
  · exact pubDisc_setInvocation c .link
  · exact pubDisc_pure _

theorem pubDisc_supplyCallee (eff : NeedPlan.CallShape) (r : PlanRoute) :
    PubDisc (NeedPlan.supplyCallee eff r) :=
  PubDisc.bind (pubDisc_supply _ _ _) (fun c =>
    PubDisc.bind (pubDisc_markCalleeLink eff r c) (fun _ => pubDisc_pure _))

theorem pubDisc_supplyReceiver (role : NeedInvocationRole) (source receiver : Expr) (caller : EvalCtx)
    (values : ValEnv) : PubDisc (NeedLink.supplyReceiver role source receiver caller values) := by
  unfold NeedLink.supplyReceiver
  split
  · exact PubDisc.bind (pubDisc_allocate _) (fun r =>
      PubDisc.bind (pubDisc_setInvocation r .receiver) (fun _ => pubDisc_pure _))
  · exact pubDisc_supply _ _ _

/-! ## Reads followed by writes (entry-anchored) -/

def PubAt {α : Type} (st : EvalState) (m : EvalM α) : Prop := PubHeapKept st.needs (m.runState st).2.needs

theorem pub_get_bind {β : Type} (f : EvalState → EvalM β) (h : ∀ st, PubAt st (f st)) :
    PubDisc (get >>= f) := by
  intro s; rw [bind_run, get_run]; exact h s

theorem PubAt.of_disc {α : Type} {st : EvalState} {m : EvalM α} (h : PubDisc m) : PubAt st m := h st

theorem PubAt.bind {α β : Type} {st : EvalState} {m : EvalM α} {f : α → EvalM β}
    (hm : PubAt st m) (hf : ∀ x, PubDisc (f x)) : PubAt st (m >>= f) := by
  unfold PubAt at *
  rw [bind_run]
  cases hr : m.runState st with
  | mk out t =>
    rw [hr] at hm
    cases out with
    | error e => exact hm
    | ok x => exact hm.trans (hf x t)

theorem PubAt.set {st t : EvalState} (h : PubHeapKept st.needs t.needs) : PubAt st (set t : EvalM PUnit) := h

/-! ## Loops -/

theorem pub_forIn'_loop {α β : Type} (as : List α) (f : (a : α) → a ∈ as → β → EvalM (ForInStep β))
    (hf : ∀ a h b, PubDisc (f a h b)) :
    ∀ (as' : List α) (b : β) (h : ∃ bs, bs ++ as' = as), PubDisc (List.forIn'.loop as f as' b h)
  | [], b, h => by unfold List.forIn'.loop; exact pubDisc_pure _
  | a :: as', b, h => by
    unfold List.forIn'.loop
    apply PubDisc.bind (hf _ _ _)
    intro r
    cases r with
    | done b => exact pubDisc_pure _
    | yield b => exact pub_forIn'_loop as f hf as' b _

theorem pub_forIn {α β : Type} (xs : List α) (init : β) (f : α → β → EvalM (ForInStep β))
    (h : ∀ a b, PubDisc (f a b)) : PubDisc (forIn xs init f) :=
  pub_forIn'_loop xs (fun a _ b => f a b) (fun a _ b => h a b) xs init ⟨[], rfl⟩

theorem pub_forM {α : Type} (xs : List α) (f : α → EvalM PUnit) (h : ∀ a, PubDisc (f a)) :
    PubDisc (xs.forM f) := by
  induction xs with
  | nil => exact pubDisc_pure _
  | cons x xs ih => unfold List.forM; exact PubDisc.bind (h x) (fun _ => ih)

theorem pub_foldlM {α β : Type} (f : β → α → EvalM β) (h : ∀ b a, PubDisc (f b a))
    (init : β) (xs : List α) : PubDisc (xs.foldlM f init) := by
  induction xs generalizing init with
  | nil => exact pubDisc_pure _
  | cons x xs ih => unfold List.foldlM; exact PubDisc.bind (h _ _) (fun b => ih b)

/-! ## Supply formation, preparation, routes (frame writes) -/

theorem pubDisc_slice (operand : Expr) (ctx : EvalCtx) : PubDisc (spreadCollectorSlice? operand ctx) :=
  pubDisc_of_needs _ (fun s => by rw [spread_slice_readonly])

theorem pubDisc_source (a : Nat) : PubDisc (needWrittenSource? a) :=
  pubDisc_of_needs _ (fun s => by rw [KatLang.NeedControl.Provenance.source_run])

theorem pubDisc_slot (ev : NeedSupply.SpreadEval) (hev : ∀ e c v, PubDisc (ev e c v))
    (ctx : EvalCtx) (env : ValEnv) (e : Expr) : PubDisc (NeedSupply.slot ev ctx env e) := by
  cases e with
  | sequenceSpread operand =>
    refine PubDisc.bind (pubDisc_slice operand ctx) (fun known => ?_)
    cases known with
    | some slice =>
      exact pubDisc_mapM _ (fun a => PubDisc.bind (pubDisc_source a) (fun _ => pubDisc_pure _)) slice
    | none =>
      refine PubDisc.bind (hev _ _ _) (fun supplied => ?_)
      cases supplied with
      | items values =>
        exact pubDisc_mapM _ (fun v => PubDisc.bind (pubDisc_allocate _) (fun _ => pubDisc_pure _)) values
      | cells cells => exact pubDisc_pure _
  | _ => exact PubDisc.bind (pubDisc_supply _ _ _) (fun _ => pubDisc_pure _)

theorem pubDisc_form (ev : NeedSupply.SpreadEval) (hev : ∀ e c v, PubDisc (ev e c v))
    (ctx : EvalCtx) (env : ValEnv) (args : OutputBundle) : PubDisc (NeedSupply.form ev ctx env args) := by
  induction args with
  | nil => exact pubDisc_pure _
  | cons e rest ih =>
    exact PubDisc.bind (pubDisc_slot ev hev ctx env e) (fun _ => PubDisc.bind ih (fun _ => pubDisc_pure _))

theorem pub_frame (a : Nat) (g : NeedCell → NeedCell)
    (hg : ∀ c, (g c).callable = c.callable ∧ (g c).callee = c.callee ∧ (g c).receiver = c.receiver) :
    PubDisc (modify fun s => { s with needs := s.needs.modify a g } : EvalM Unit) :=
  pub_modify _ (fun _ => PubHeapKept.modify _ a _ (fun c _ =>
    pubKept_of_same _ _ (hg c).1 (hg c).2.1 (hg c).2.2))

theorem pubDisc_setSupply (a : Nat) (p : NeedPlanSupply) : PubDisc (NeedPlan.setSupply a p) :=
  pub_frame a _ (fun _ => ⟨rfl, rfl, rfl⟩)

theorem pubDisc_setRoute (a : Nat) (r : PlanRoute) : PubDisc (NeedPlan.setRoute a r) :=
  pub_frame a _ (fun _ => ⟨rfl, rfl, rfl⟩)

/-- Preparation writes only the plan record: a frame over its formation. -/
theorem pubDisc_prepare (ev : NeedSupply.SpreadEval) (hev : ∀ e c v, PubDisc (ev e c v))
    (a : Nat) (shape : NeedPlan.CallShape) : PubDisc (NeedPlan.prepare ev a shape) := by
  unfold NeedPlan.prepare
  refine PubDisc.bind pubDisc_get (fun st => ?_)
  split
  · split
    · exact pubDisc_lift _
    · exact pubDisc_throw _
    · exact PubDisc.bind (pubDisc_setSupply _ _) (fun _ =>
        PubDisc.bind (pubDisc_form ev hev _ _ _).attempt (fun _ =>
          PubDisc.bind (pubDisc_setSupply _ _) (fun _ => pubDisc_lift _)))
  · exact pubDisc_throw _

theorem pubDisc_routeOf (classify : NeedPlan.CallShape → EvalM PlanRoute)
    (hclassify : ∀ shape, PubDisc (classify shape)) (a : Nat) (shape : NeedPlan.CallShape) :
    PubDisc (NeedPlan.routeOf classify a shape) := by
  unfold NeedPlan.routeOf
  refine PubDisc.bind pubDisc_get (fun st => ?_)
  split
  · split
    · exact pubDisc_pure _
    · exact PubDisc.bind (hclassify _) (fun r => PubDisc.bind pubDisc_get (fun _ => by
        split
        · exact pubDisc_pure _
        · exact PubDisc.bind (pubDisc_setRoute _ _) (fun _ => pubDisc_pure _)))
  · exact pubDisc_throw _

/-! ## The publishing writer, and the two record writers -/

/-- **CALLABLE publication is accounted for.** A completed outcome is returned with no write; an
    active projection is a cycle with no write; an UNPROJECTED entry cell is marked `projecting`
    (no identity) and then holds the callback's outcome — an identity that the callback's result
    contract accounts for in the callback's exit heap (`hres`), hence in the entry heap. -/
theorem pubDisc_projectionStep (project : NeedSuspension → EvalM (Option Algorithm))
    (hp : ∀ x, PubDisc (project x))
    (hres : ∀ x s g t, (project x).runState s = (.ok (some g), t) → Accounted t.needs g)
    (a : Nat) : PubDisc (NeedProjection.step project a) := by
  intro s
  cases hc : s.needs[a]? with
  | none =>
    rw [KatLang.NeedControl.Projection.invalid_address project a s hc]; exact PubHeapKept.refl _
  | some cell =>
    cases hs : cell.callable with
    | projected o =>
      rw [KatLang.NeedControl.Projection.projected_sticky project a s cell o hc hs]
      exact PubHeapKept.refl _
    | projecting =>
      rw [KatLang.NeedControl.Projection.projecting_reentry_cycle project a s cell hc hs]
      exact PubHeapKept.refl _
    | unprojected =>
      have k1 : PubHeapKept s.needs (KatLang.NeedControl.Projection.setCallable a .projecting s).needs :=
        PubHeapKept.modify _ a _ (fun c _ g h => by cases h)
      have k2 := hp cell.suspension (KatLang.NeedControl.Projection.setCallable a .projecting s)
      generalize hr : (project cell.suspension).runState
        (KatLang.NeedControl.Projection.setCallable a .projecting s) = r at k2
      rcases r with ⟨outcome, t⟩
      have k12 := k1.trans k2
      cases hinc : outcome.isIncomplete with
      | false =>
        rw [KatLang.NeedControl.Projection.unprojected_publishes project a s t cell outcome hc hs hr hinc]
        show PubHeapKept s.needs (t.needs.modify a (fun c => { c with callable := .projected outcome }))
        intro b c' g hb hg
        rw [modify_get] at hb
        by_cases hab : a = b
        · subst hab
          rw [ite_eq_left rfl] at hb
          cases hcur : t.needs[a]? with
          | none => rw [hcur] at hb; cases hb
          | some cur =>
            rw [hcur] at hb
            cases hb
            have ho : outcome = .ok (some g) := by
              have h' : NeedCallableState.projected outcome = .projected (.ok (some g)) := hg
              cases h'
              rfl
            subst ho
            exact (hres cell.suspension _ g t hr).back k12
        · rw [ite_eq_right hab] at hb
          exact k12 b c' g hb hg
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
theorem pubDisc_calleeCell (classify : NeedPlan.CallShape → EvalM PlanRoute)
    (hclassify : ∀ shape, PubDisc (classify shape)) (a : Nat) :
    PubDisc (NeedPlan.calleeCell classify a) := by
  intro s
  cases hc : s.needs[a]? with
  | none =>
    have : (NeedPlan.calleeCell classify a).runState s = (.error (.illegalInEval "invalid need address"), s) := by
      simp only [NeedPlan.calleeCell, bind_run, get_run, hc]; rfl
    rw [this]; exact PubHeapKept.refl _
  | some cell =>
    cases hcal : cell.callee with
    | some x => rw [calleeCell_recorded classify a x s cell hc hcal]; exact PubHeapKept.refl _
    | none =>
      cases hshape : NeedPlan.ofSuspension? cell.suspension with
      | none =>
        have : (NeedPlan.calleeCell classify a).runState s = (.error NeedPlan.metaRefusal, s) := by
          simp only [NeedPlan.calleeCell, bind_run, get_run, hc, hcal, hshape]; rfl
        rw [this]; exact PubHeapKept.refl _
      | some shape =>
        rw [calleeCell_unrecorded classify a s cell shape hc hcal hshape]
        have k1 := pubDisc_routeOf classify hclassify a shape s
        rcases hro : (NeedPlan.routeOf classify a shape).runState s with ⟨_ | r, t⟩ <;> rw [hro] at k1
        · exact k1
        · dsimp only
          split
          · exact k1
          · have k2 := pubDisc_supplyCallee (NeedPlan.effective shape r) r t
            rcases hsu : (NeedPlan.supplyCallee (NeedPlan.effective shape r) r).runState t
              with ⟨_ | x, u⟩ <;> rw [hsu] at k2
            · exact k1.trans k2
            · exact PubHeapKept.modify_anchor (k1.trans k2) a _ (fun c1 _ => pubKept_of_callable _ _ rfl)

/-- **Receiver establishment keeps entry facts**: the one supply between the read and the record. -/
theorem pubDisc_receiverCell (a : Nat) : PubDisc (NeedLink.receiverCell a) := by
  intro s
  cases hc : s.needs[a]? with
  | none =>
    have : (NeedLink.receiverCell a).runState s = (.error (.illegalInEval "invalid need address"), s) := by
      simp only [NeedLink.receiverCell, bind_run, get_run, hc]; rfl
    rw [this]; exact PubHeapKept.refl _
  | some cell =>
    cases hrec : cell.receiver with
    | some x => rw [receiverCell_recorded a x s cell hc hrec]; exact PubHeapKept.refl _
    | none =>
      have hother : ∀ (e : Error), (NeedLink.receiverCell a).runState s = (.error e, s) →
          PubHeapKept s.needs ((NeedLink.receiverCell a).runState s).2.needs := by
        intro e h; rw [h]; exact PubHeapKept.refl _
      cases hsusp : cell.suspension with
      | expression source caller values =>
        cases hl : linkEdge? source with
        | none =>
          apply hother (.illegalInEval "not a link")
          simp only [NeedLink.receiverCell, bind_run, get_run, hc, hrec, hsusp, hl]; rfl
        | some p =>
          rcases p with ⟨receiver, fallback⟩
          rw [receiverCell_establishes a s cell source receiver fallback caller values hc hrec hsusp hl]
          have k := pubDisc_supplyReceiver cell.invocation source receiver caller values s
          rcases hsu : (NeedLink.supplyReceiver cell.invocation source receiver caller values).runState s
            with ⟨_ | x, u⟩ <;> rw [hsu] at k
          · exact k
          · exact PubHeapKept.modify_anchor k a _ (fun c1 _ => pubKept_of_callable _ _ rfl)
      | ready v =>
        apply hother (.illegalInEval "not a link")
        simp only [NeedLink.receiverCell, bind_run, get_run, hc, hrec, hsusp]; rfl
      | collector sl =>
        apply hother (.illegalInEval "not a link")
        simp only [NeedLink.receiverCell, bind_run, get_run, hc, hrec, hsusp]; rfl


/-! ## The shared link decoder and its two channels -/

/-- Both link channels preserve entry facts through the same decoder, provided its route
    classifier and receiver demand do. No contract on the returned addresses is needed here. -/
theorem pubDisc_decodeCallee (classify : NeedPlan.CallShape → EvalM PlanRoute)
    (hclassify : ∀ shape, PubDisc (classify shape))
    (demand : Nat → EvalM CountedResult) (hdemand : ∀ a, PubDisc (demand a)) (a : Nat) :
    PubDisc (NeedLink.decodeCallee classify demand a) := by
  unfold NeedLink.decodeCallee
  refine PubDisc.bind (pubDisc_receiverCell a) (fun receiver => ?_)
  refine PubDisc.bind (hdemand receiver) (fun value => ?_)
  refine PubDisc.bind ?_ (fun plan => pubDisc_calleeCell classify hclassify plan)
  cases value.1 <;> first | exact pubDisc_pure _ | exact pubDisc_evalError _

/-- The VALUE link channel adds only the callee's VALUE demand to the shared decoder. -/
theorem pubDisc_linkValue (classify : NeedPlan.CallShape → EvalM PlanRoute)
    (hclassify : ∀ shape, PubDisc (classify shape))
    (demand : Nat → EvalM CountedResult) (hdemand : ∀ a, PubDisc (demand a)) (a : Nat) :
    PubDisc (NeedLink.value classify demand a) :=
  PubDisc.bind (pubDisc_decodeCallee classify hclassify demand hdemand a) hdemand

/-- The CALLABLE link channel adds only the callee's CALLABLE projection to the shared decoder. -/
theorem pubDisc_linkCallable (classify : NeedPlan.CallShape → EvalM PlanRoute)
    (hclassify : ∀ shape, PubDisc (classify shape))
    (demand : Nat → EvalM CountedResult) (hdemand : ∀ a, PubDisc (demand a))
    (project : Nat → EvalM (Option Algorithm)) (hproject : ∀ a, PubDisc (project a)) (a : Nat) :
    PubDisc (NeedLink.callable classify demand project a) :=
  PubDisc.bind (pubDisc_decodeCallee classify hclassify demand hdemand a) hproject

/-! ## Plan execution, the VALUE shell, META, invocation, capture and the argument view -/

theorem pubDisc_calleeAlong (route : NeedPlan.Route)
    (htarget : ∀ f c, PubDisc (route.target f c))
    (hclassify : ∀ shape, PubDisc (route.classify shape))
    (hproject : ∀ c, PubDisc (route.project c))
    (a : Nat) (eff : NeedPlan.CallShape) (r : PlanRoute) :
    PubDisc (NeedPlan.calleeAlong route a eff r) := by
  cases r with
  | algorithm =>
    simp only [NeedPlan.calleeAlong]
    refine PubDisc.bind (pubDisc_calleeCell route.classify hclassify a) (fun c => ?_)
    refine PubDisc.bind (hproject c) (fun o => ?_)
    cases o with
    | some _ => exact pubDisc_pure _
    | none => exact pubDisc_throw _
  | intrinsic => exact pubDisc_throw _
  | call => exact htarget _ _
  | extension => exact htarget _ _

theorem pubDisc_executeAlong (route : NeedPlan.Route)
    (hspread : ∀ e c v, PubDisc (route.spread e c v))
    (htarget : ∀ f c, PubDisc (route.target f c))
    (hnormal : ∀ g c, PubDisc (route.normalize g c))
    (hdispatch : ∀ o g cells c v n, PubDisc (route.dispatch o g cells c v n))
    (hclassify : ∀ shape, PubDisc (route.classify shape))
    (hproject : ∀ c, PubDisc (route.project c))
    (a : Nat) (shape : NeedPlan.CallShape) (r : PlanRoute) :
    PubDisc (NeedPlan.executeAlong route a shape r) := by
  unfold NeedPlan.executeAlong NeedPlan.dispatchName NeedPlan.dispatchOrigin
  exact PubDisc.bind (PubDisc.withCtx _ (pubDisc_calleeAlong route htarget hclassify hproject a _ r)) (fun _ =>
    PubDisc.bind (PubDisc.bind pubDisc_get (fun _ => pubDisc_pure _)) (fun _ =>
    PubDisc.bind (PubDisc.bind pubDisc_get (fun _ => pubDisc_pure _)) (fun _ =>
    PubDisc.bind (PubDisc.withCtx _ (PubDisc.bind (hnormal _ _) (fun _ =>
      PubDisc.bind (pubDisc_prepare route.spread hspread a _) (fun _ => hdispatch _ _ _ _ _ _))))
      (fun _ => pubDisc_pure _))))

theorem pubDisc_execute (route : NeedPlan.Route)
    (hspread : ∀ e c v, PubDisc (route.spread e c v))
    (htarget : ∀ f c, PubDisc (route.target f c))
    (hnormal : ∀ g c, PubDisc (route.normalize g c))
    (hdispatch : ∀ o g cells c v n, PubDisc (route.dispatch o g cells c v n))
    (hclassify : ∀ shape, PubDisc (route.classify shape))
    (hproject : ∀ c, PubDisc (route.project c))
    (a : Nat) (shape : NeedPlan.CallShape) :
    PubDisc (NeedPlan.execute route a shape) := by
  unfold NeedPlan.execute
  refine PubDisc.bind (PubDisc.withCtx _ (pubDisc_routeOf route.classify hclassify a shape)) (fun r => ?_)
  cases r with
  | intrinsic => exact pubDisc_throw _
  | _ => exact pubDisc_executeAlong route hspread htarget hnormal hdispatch hclassify hproject a shape _

theorem pubDisc_suspendedValue (ev : Expr → EvalCtx → ValEnv → EvalM CountedResult)
    (route : NeedPlan.Route) (demand : Nat → EvalM CountedResult)
    (hev : ∀ e c v, PubDisc (ev e c v))
    (hspread : ∀ e c v, PubDisc (route.spread e c v))
    (htarget : ∀ f c, PubDisc (route.target f c))
    (hnormal : ∀ g c, PubDisc (route.normalize g c))
    (hdispatch : ∀ o g cells c v n, PubDisc (route.dispatch o g cells c v n))
    (hclassify : ∀ shape, PubDisc (route.classify shape))
    (hproject : ∀ c, PubDisc (route.project c))
    (hdemand : ∀ b, PubDisc (demand b)) (a : Nat) (suspension : NeedSuspension) :
    PubDisc (NeedDemand.suspendedValue ev route demand a suspension) := by
  cases suspension with
  | ready value => exact pubDisc_pure _
  | expression e c v =>
    simp only [NeedDemand.suspendedValue]
    split
    · refine PubDisc.bind (PubDisc.withCtx _ (pubDisc_routeOf route.classify hclassify a _)) (fun r => ?_)
      cases r with
      | intrinsic => exact PubDisc.map _ (hev e c v)
      | _ => exact pubDisc_executeAlong route hspread htarget hnormal hdispatch hclassify hproject a _ _
    · exact PubDisc.map _ (hev e c v)
  | collector slice =>
    exact PubDisc.withNestedMissingOutput
      (PubDisc.bind (pubDisc_mapM _ (fun b => PubDisc.map _ (hdemand b)) slice)
        (fun _ => pubDisc_pure _))

/-- The VALUE completion shell writes only the VALUE state: a frame over its computation. -/
theorem pubDisc_step (ev : Expr → EvalCtx → ValEnv → EvalM CountedResult)
    (route : NeedPlan.Route) (demand : Nat → EvalM CountedResult)
    (hev : ∀ e c v, PubDisc (ev e c v))
    (hspread : ∀ e c v, PubDisc (route.spread e c v))
    (htarget : ∀ f c, PubDisc (route.target f c))
    (hnormal : ∀ g c, PubDisc (route.normalize g c))
    (hdispatch : ∀ o g cells c v n, PubDisc (route.dispatch o g cells c v n))
    (hclassify : ∀ shape, PubDisc (route.classify shape))
    (hproject : ∀ c, PubDisc (route.project c))
    (hdemand : ∀ b, PubDisc (demand b)) (a : Nat) :
    PubDisc (NeedDemand.step ev route demand a) := by
  unfold NeedDemand.step
  refine PubDisc.bind pubDisc_get (fun st => ?_)
  split
  · split
    · exact pubDisc_lift _
    · exact pubDisc_throw _
    · exact PubDisc.bind (pub_frame a _ (fun _ => ⟨rfl, rfl, rfl⟩)) (fun _ =>
        PubDisc.bind (pubDisc_suspendedValue ev route demand hev hspread htarget hnormal hdispatch
          hclassify hproject hdemand a _).attempt (fun _ =>
          PubDisc.bind (pub_frame a _ (fun _ => ⟨rfl, rfl, rfl⟩)) (fun _ => pubDisc_lift _)))
  · exact pubDisc_throw _

theorem pubDisc_reify (a : Nat) : PubDisc (NeedPlan.reify a) :=
  pubDisc_of_needs _ (fun s => by rw [reify_inert])

theorem pubDisc_invoke (route : NeedPlan.Route)
    (hspread : ∀ e c v, PubDisc (route.spread e c v))
    (htarget : ∀ f c, PubDisc (route.target f c))
    (hnormal : ∀ g c, PubDisc (route.normalize g c))
    (hdispatch : ∀ o g cells c v n, PubDisc (route.dispatch o g cells c v n))
    (hclassify : ∀ shape, PubDisc (route.classify shape))
    (hproject : ∀ c, PubDisc (route.project c))
    (r : NeedPlan.CallReference) : PubDisc (NeedPlan.invoke route r) := by
  unfold NeedPlan.invoke
  refine PubDisc.bind pubDisc_get (fun st => ?_)
  split
  · exact pubDisc_execute route hspread htarget hnormal hdispatch hclassify hproject _ _
  · exact pubDisc_throw _

theorem pubDisc_reference (a : Nat) : PubDisc (NeedPlan.reference a) := by
  intro s
  rw [KatLang.CallReferenceLaws.reference_run]
  cases NeedPlan.reifyResult s.needs a with
  | error e => exact PubHeapKept.refl _
  | ok r => exact PubHeapKept.push _ _ (fun g h => by cases h)

theorem pubDisc_viewCells (sp : NeedSupply.SpreadEval) (hsp : ∀ e c v, PubDisc (sp e c v))
    (classify : NeedPlan.CallShape → EvalM PlanRoute) (hclassify : ∀ shape, PubDisc (classify shape))
    (a : Nat) : PubDisc (NeedPlan.viewCells sp classify a) := by
  unfold NeedPlan.viewCells
  refine PubDisc.bind pubDisc_get (fun st => ?_)
  split
  · refine PubDisc.bind (pubDisc_routeOf classify hclassify a _) (fun r => ?_)
    split
    · exact PubDisc.bind (pubDisc_throw _) (fun _ => pubDisc_prepare sp hsp a _)
    · exact pubDisc_prepare sp hsp a _
  · exact pubDisc_throw _

/-! ## The syntax-directed per-body procedure (the `EvaluatorDiscipline` procedure over `PubDisc`) -/

open Lean Meta Elab Tactic in
/-- Unfolds the head constant of the computation in a `PubDisc` goal (a total helper with
    no lemma of its own), so the syntax-directed procedure can continue inside it. -/
elab "pub_unfold_head" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let ty ← instantiateMVars (← goal.getType)
    let_expr KatLang.Publications.PubDisc _ m := ty | throwError "pub_unfold_head: not a link-discipline goal"
    let m := m.headBeta
    let some c := m.getAppFn.constName? | throwError "pub_unfold_head: no head constant"
    if c ∈ [``Bind.bind, ``Pure.pure, ``Functor.map, ``KatLang.evalAttempt, ``ForIn.forIn,
        ``MonadState.get, ``MonadStateOf.get, ``MonadState.set, ``MonadStateOf.set,
        ``MonadState.modifyGet, ``modify, ``get, ``set, ``List.forM, ``List.mapM, ``List.foldlM] then
      throwError "pub_unfold_head: combinator"
    let g' ← Lean.Meta.unfoldTarget goal c
    let ty' ← instantiateMVars (← g'.getType)
    if (ty'.find? (fun e => e.isConstOf c)).isSome then
      throwError "pub_unfold_head: recursive definition"
    replaceMainGoal [g']

open Lean Meta Elab Tactic in
/-- Closes `PubDisc (rec c)` from a hypothesis `∀ c, PubDisc (rec c)`. -/
elab "pub_rec" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let ty ← instantiateMVars (← goal.getType)
    let_expr KatLang.Publications.PubDisc _ m := ty | throwError "pub_rec: not a link-discipline goal"
    let m := m.headBeta
    unless m.isApp && m.appFn!.isFVar do throwError "pub_rec: not a recursive call"
    let f := m.appFn!
    for d in (← getLCtx) do
      unless d.isImplementationDetail do
        let t ← instantiateMVars d.type
        if t.isForall then
          let body := t.bindingBody!
          if let some (_, m') := body.app2? ``KatLang.Publications.PubDisc then
            if m'.isApp && m'.appFn! == f && m'.appArg! == .bvar 0 then
              goal.assign (mkApp d.toExpr m.appArg!)
              return
    throwError "pub_rec: no hypothesis"

open Lean Meta Elab Tactic in
/-- Closes a goal from a local hypothesis, instantiating its leading universal binders, at
    reducible transparency (cheap: never evaluates a computation). -/
elab "pub_hyp" : tactic => do
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
  unless ok do throwError "pub_hyp: no hypothesis"

open Lean Meta Elab Tactic in
/-- Zeta-reduces the top-level local definitions (`let`/`have`) of the computation in a
    `PubDisc`/`PubAt` goal, and nothing else. -/
elab "pub_zeta" : tactic => do
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
    if n == 0 then throwError "pub_zeta: no local definition"
    replaceMainGoal [← goal.replaceTargetDefEq (ty.updateApp! ty.appFn! m')]

open Lean Meta Elab Tactic in
/-- `intro` on a goal that is syntactically a binder (never unfolding a definition to find one). -/
elab "pub_intro_syntactic" : tactic => do
  let goal ← getMainGoal
  unless (← instantiateMVars (← goal.getType)).isForall do throwError "pub_intro_syntactic: no binder"
  let (_, g) ← goal.intro1
  replaceMainGoal [g]

open Lean Meta Elab Tactic in
/-- Closes an impossible branch: a hypothesis `∀ xs, a = b → False` whose equation holds by `rfl`
    for some instantiation. -/
elab "pub_absurd" : tactic => do
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
  unless ok do throwError "pub_absurd: no contradiction"

open Lean Meta Elab Tactic in
/-- Beta/projection/constructor-iota normal form (`whnfCore`, no definition unfolding) of the
    computation in a `PubDisc` goal. -/
elab "pub_whnf_core" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let ty ← instantiateMVars (← goal.getType)
    let_expr KatLang.Publications.PubDisc _ m := ty | throwError "pub_whnf_core: not a link-discipline goal"
    let m' ← whnfCore m
    if m' == m then throwError "pub_whnf_core: no progress"
    replaceMainGoal [← goal.replaceTargetDefEq (ty.updateApp! ty.appFn! m')]

/-- The evaluator helpers `rec.f args` are `rec (.f args)`. -/
macro "pub_unfold_rec" : tactic => `(tactic| dsimp (config := { proj := false }) only [EvalRec.whileLoop, EvalRec.aliasStepIsRuntime, EvalRec.aliasValue, EvalRec.resolveAliasChase, EvalRec.resolveAliasTarget, EvalRec.resolveAliasValueTarget, EvalRec.lookupLexicalProperty, EvalRec.lookupLexicalValueProperty, EvalRec.lookupLexical, EvalRec.needPlanNormalizeCallee, EvalRec.resolveAlg, EvalRec.projectNeedCallable, EvalRec.projectNeedWrittenAt, EvalRec.linkCallable, EvalRec.projectParameterCallable, EvalRec.projectNeedWritten, EvalRec.projectNeedStructuralMember, EvalRec.resolveCalleeAlg, EvalRec.expectPreparedSequenceBuiltinAlgorithmSuffixArg, EvalRec.resolveDotReceiver?, EvalRec.resolveDotReceiver, EvalRec.algorithmIntrinsicRoute, EvalRec.demandNeedRecursive, EvalRec.evalSuppliedAt, EvalRec.linkValue, EvalRec.algorithmOfValue, EvalRec.capturedCallee, EvalRec.referenceReceiverValue, EvalRec.algorithmCalleeOf, EvalRec.evalSuppliedCallCounted, EvalRec.evalNeedUserSupply, EvalRec.evalNeedFamilySupply, EvalRec.invokeNeed, EvalRec.argumentNeed, EvalRec.runNeedStepSlots, EvalRec.runNeedWhileRound, EvalRec.evalAlgOutputCore, EvalRec.evalAlgOutput, EvalRec.evalProgramOutput, EvalRec.evalAlgOutputSlots, EvalRec.formOutputRow, EvalRec.whileVerdictSlots, EvalRec.evalSequenceCallbackCall, EvalRec.evalSequenceCallbackCallCounted, EvalRec.evalAlgOutputPreparedCore, EvalRec.evalOutputRowsPreparedCore, EvalRec.evalCapturePreparedCore, EvalRec.evalCaptureCountedCore, EvalRec.evalCaptureValue, EvalRec.evalAlgOutputCountedCore, EvalRec.evalAlgOutputCounted, EvalRec.evalZeroArgumentDemandOutputCounted, EvalRec.evalZeroArgumentDemandOutput, EvalRec.evalArgumentValueCounted, EvalRec.evalArgumentValue, EvalRec.evalZeroArgPropertyAccessCounted, EvalRec.evalZeroArgPropertyAccess, EvalRec.evalConditionalCallbackCallCounted, EvalRec.evalUserCallbackCallCounted, EvalRec.evalResolvedCallbackCallCounted, EvalRec.evalResolvedCallbackCall, EvalRec.evalSequenceReduceStepCounted, EvalRec.demandSequenceBuiltinCallItemValue, EvalRec.bindSequenceBuiltinArguments, EvalRec.evalReduceCounted, EvalRec.evalFilterCounted, EvalRec.evalMapCounted, EvalRec.applyBuiltinCountedSequence, EvalRec.applyBuiltinCounted, EvalRec.applyBuiltin, EvalRec.applyBuiltinCountedResolved, EvalRec.evalExplicitSequenceValueItems, EvalRec.evalExplicitSequenceValueRowSlots, EvalRec.evalExplicitSequenceValueExprSlots, EvalRec.evalUserCallCounted, EvalRec.evalConditionalCallCounted, EvalRec.evalResolvedCall, EvalRec.evalResolvedCallCounted, EvalRec.evalCallCountedExpr, EvalRec.callLexicalWithReceiverCounted, EvalRec.rejectDotStringIntrinsicArguments, EvalRec.evalDotStringReceiverValue, EvalRec.evalDotCallCounted, EvalRec.rejectInvokeIntrinsicArguments, EvalRec.invokeCallReferenceValue, EvalRec.argumentViewCells, EvalRec.evalArgumentViewBuiltin, EvalRec.evalSequenceSpreadOperandValue, EvalRec.evalSequenceSpreadCounted, EvalRec.evalSupplySpread, EvalRec.evalListLiteralCounted, EvalRec.evalSequenceConstructCounted, EvalRec.evalUnaryCounted, EvalRec.evalBinaryCounted, EvalRec.evalComparisonCounted, EvalRec.evalComparisonLinksCounted, EvalRec.evalCounted, EvalRec.evalUserCall, EvalRec.evalConditionalCall, EvalRec.evalCallExpr, EvalRec.evalDotCall, EvalRec.eval, EvalRec.planRoute,
  EvalRec.bindingChannels, NeedChannels.shell, NeedChannels.capabilities] at *)

set_option hygiene false in
/-- Syntax-directed link discipline (base: no recursive helper lemmas), given that `hrec`
    is link-disciplined. -/
macro "pub_tac_base" : tactic => `(tactic| without_info_trees ((try pub_unfold_rec) <;> repeat' (first
  | pub_res
  | pub_rec
  | pub_hyp
  | pub_absurd
  | (with_reducible apply pub_get_bind)
  | (with_reducible apply PubAt.bind)
  | (with_reducible apply PubAt.set; first
      | exact PubHeapKept.refl _
      | (apply PubHeapKept.set_bang <;> first | pub_hyp | (exact pubKept_of_same _ _ rfl rfl rfl)))
  | (with_reducible apply PubDisc.withCtx)
  | (with_reducible apply PubDisc.captureMeta)
  | (with_reducible apply PubDisc.attempt)
  | (with_reducible apply PubDisc.map)
  | (with_reducible apply PubDisc.bind)
  | (with_reducible apply pubDisc_pure)
  | (with_reducible apply pubDisc_get)
  | (with_reducible apply pubDisc_throw)
  | (with_reducible apply pubDisc_evalError)
  | (with_reducible apply pubDisc_lift)
  | (with_reducible apply pubDisc_allocate)
  | (with_reducible apply pubDisc_supply)
  | (with_reducible apply pubDisc_mapM)
  | (with_reducible apply pubDisc_form)
  | (with_reducible apply pubDisc_slot)
  | (with_reducible apply pubDisc_prepare)
  | (with_reducible apply pubDisc_routeOf)
  | (with_reducible apply pubDisc_calleeCell)
  | (with_reducible apply pubDisc_projectionStep)
  | (with_reducible apply pubDisc_receiverCell)
  | (with_reducible apply pubDisc_linkCallable)
  | (with_reducible apply pubDisc_linkValue)
  | (with_reducible apply pubDisc_decodeCallee)
  | (with_reducible apply pubDisc_execute)
  | (with_reducible apply pubDisc_step)
  | (with_reducible apply pubDisc_reify)
  | (with_reducible apply pubDisc_invoke)
  | (with_reducible apply pubDisc_reference)
  | (with_reducible apply pubDisc_viewCells)
  | (with_reducible apply pub_modify; intro s; first
      | exact PubHeapKept.refl _
      | (apply PubHeapKept.modify; intro c _; exact pubKept_of_same _ _ rfl rfl rfl))
  | (with_reducible apply pub_forIn)
  | (with_reducible apply pub_forM)
  | (with_reducible apply pub_foldlM)
  | (with_reducible apply CapsPub.mk)

  | split
  | pub_intro_syntactic
  | pub_zeta
  | pub_whnf_core
  | pub_unfold_head
  | (with_reducible apply PubAt.of_disc))))

/-! ## Link discipline of the recursive total helpers -/

theorem pub_formLeftToRight (form : Expr → EvalM (List Result)) (h : ∀ e, PubDisc (form e))
    (rows : List Expr) : PubDisc (OutputRows.formLeftToRight form rows) := by
  induction rows with
  | nil => unfold OutputRows.formLeftToRight; pub_tac_base
  | cons e rest ih => unfold OutputRows.formLeftToRight; pub_tac_base

theorem pub_discover (form : Expr → EvalM (List Result)) (h : ∀ e, PubDisc (form e))
    (rows : List Expr) : PubDisc (WhileRound.discover form rows) := by
  induction rows with
  | nil => unfold WhileRound.discover; pub_tac_base
  | cons e rest ih => unfold WhileRound.discover; pub_tac_base

theorem pub_selectWith {α : Type} (demand : α → EvalM Result) (h : ∀ a, PubDisc (demand a))
    (receiver : Result) (cells : List α) : PubDisc (selectWith demand receiver cells) := by
  induction cells with
  | nil => unfold selectWith; pub_tac_base
  | cons c rest ih => unfold selectWith; pub_tac_base

theorem pub_selectViewWith {α : Type} (demand : α → EvalM Result) (hd : ∀ a, PubDisc (demand a))
    (cellsOf : EvalM (List NeedSupply.Sourced)) (hc : PubDisc cellsOf)
    (demandCell : Nat → EvalM Result) (hdc : ∀ a, PubDisc (demandCell a)) (selectors : List α) :
    PubDisc (selectViewWith demand cellsOf demandCell selectors) := by
  induction selectors with
  | nil => unfold selectViewWith; pub_tac_base
  | cons c rest ih => unfold selectViewWith; pub_tac_base

/-- Capabilities whose every field is link-disciplined. -/
structure CapsPub (caps : NeedCapabilities EvalM) : Prop where
  value : ∀ a, PubDisc (caps.value a)
  callable : ∀ a, PubDisc (caps.callable a)
  allocate : ∀ s, PubDisc (caps.allocate s)
  reference : ∀ a, PubDisc (caps.reference a)

/-- NEED-04's data-anchor check demands only through the VALUE capability. -/
theorem pub_checkAnchor (caps : NeedCapabilities EvalM) (hc : CapsPub caps) (name : Ident)
    (anchor : CountedResult) (family : Bool) (cells : List Nat) :
    PubDisc (NeedBinder.checkAnchor caps name anchor family cells) := by
  have hv := hc.value
  induction cells with
  | nil => unfold NeedBinder.checkAnchor; pub_tac_base
  | cons c rest ih => unfold NeedBinder.checkAnchor; pub_tac_base

theorem pub_binder (caps : NeedCapabilities EvalM) (hc : CapsPub caps) (repeated : List Ident)
    (family : Bool) :
    (∀ pattern address bound,
      PubDisc (NeedBinder.bindOne caps pattern address repeated bound family)) ∧
    (∀ patterns sources current,
      PubDisc (NeedBinder.bindSources caps patterns sources repeated current family)) := by
  have hv := hc.value; have hcl := hc.callable; have hal := hc.allocate; have hre := hc.reference
  have hck := pub_checkAnchor caps hc
  refine NeedBinder.bindOne.mutual_induct
    (motive_1 := fun pattern address bound =>
      PubDisc (NeedBinder.bindOne caps pattern address repeated bound family))
    (motive_2 := fun patterns sources current =>
      PubDisc (NeedBinder.bindSources caps patterns sources repeated current family))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals intros
  all_goals first
    | (simp only [NeedBinder.bindOne]; pub_tac_base)
    | (simp only [NeedBinder.bindSources]; pub_tac_base)

theorem pub_bindPatterns (caps : NeedCapabilities EvalM) (hc : CapsPub caps)
    (patterns : List NeedPattern) (cells : List Nat) (family : Bool) :
    PubDisc (NeedBinder.bindPatterns caps patterns cells family) := by
  unfold NeedBinder.bindPatterns NeedBinder.bindLevel NeedBinder.cardinalityGate
  have := (pub_binder caps hc (needRepeatedNames patterns) family).2
  pub_tac_base

theorem pub_chooseBranch {β : Type} (caps : NeedCapabilities EvalM) (hc : CapsPub caps)
    (cells : List Nat) (calleeName : String) (activate : CondBranch → NeedEnv → EvalM β)
    (ha : ∀ b e, PubDisc (activate b e)) (branches : List CondBranch) :
    PubDisc (NeedBinder.chooseBranch caps cells calleeName activate branches) := by
  induction branches with
  | nil => unfold NeedBinder.chooseBranch; pub_tac_base
  | cons b rest ih =>
    unfold NeedBinder.chooseBranch
    have := fun ps fam => pub_bindPatterns caps hc ps cells fam
    pub_tac_base

theorem pub_selectFamily {β : Type} (caps : NeedCapabilities EvalM) (hc : CapsPub caps)
    (callee : Algorithm) (cells : List Nat) (calleeName : String)
    (activate : CondBranch → NeedEnv → EvalM β) (ha : ∀ b e, PubDisc (activate b e)) :
    PubDisc (NeedBinder.selectFamily caps callee cells calleeName activate) := by
  unfold NeedBinder.selectFamily
  have := pub_chooseBranch caps hc cells calleeName activate ha
  pub_tac_base


theorem pub_collectSingleAtomicNumbers (b : Builtin) (index : Nat) (items : List Result) :
    PubDisc (collectSingleAtomicNumbers b index items) := by
  induction items generalizing index with
  | nil => unfold collectSingleAtomicNumbers; pub_tac_base
  | cons i rest ih => unfold collectSingleAtomicNumbers; pub_tac_base

theorem pub_minLoop (numbers : List Int) (current : Int) :
    PubDisc (evalMinCounted.minLoop numbers current) := by
  induction numbers generalizing current with
  | nil => unfold evalMinCounted.minLoop; pub_tac_base
  | cons n rest ih => unfold evalMinCounted.minLoop; pub_tac_base

theorem pub_maxLoop (numbers : List Int) (current : Int) :
    PubDisc (evalMaxCounted.maxLoop numbers current) := by
  induction numbers generalizing current with
  | nil => unfold evalMaxCounted.maxLoop; pub_tac_base
  | cons n rest ih => unfold evalMaxCounted.maxLoop; pub_tac_base

theorem pub_openNavigateWith (structureOf : Algorithm → EvalM Algorithm)
    (h : ∀ a, PubDisc (structureOf a)) (ctx : EvalCtx) (notStatic : Error)
    (value : Algorithm) (receiverName : String) (steps : List Ident) :
    PubDisc (openNavigateWith structureOf ctx notStatic value receiverName steps) := by
  induction steps generalizing value receiverName with
  | nil => unfold openNavigateWith; pub_tac_base
  | cons member rest ih => unfold openNavigateWith; pub_tac_base

theorem pub_openStructure (fuel : Nat) (ctx : EvalCtx) (a : Algorithm) :
    PubDisc (openStructure fuel ctx a) := by
  induction fuel generalizing a with
  | zero => simp only [openStructure]; pub_tac_base
  | succ n ih =>
    have := pub_openNavigateWith (fun value => openStructure n ctx value) ih
    simp only [openStructure]; pub_tac_base

theorem pub_resolveAlgForOpen (ctx : EvalCtx) (e : Expr) : PubDisc (resolveAlgForOpen e ctx) := by
  have := pub_openStructure
  induction e using resolveAlgForOpen.induct ctx with
  | case7 o n a ih => unfold resolveAlgForOpen; pub_tac_base
  | _ => unfold resolveAlgForOpen; pub_tac_base

theorem pub_lookupOpenProperties (a : Algorithm) (name : Ident) (ctx : EvalCtx) :
    PubDisc (lookupOpenProperties a name ctx) := by
  have := pub_resolveAlgForOpen
  have := pub_openStructure
  unfold lookupOpenProperties; pub_tac_base

theorem pub_lookupOpenPropertiesInParentChain (name : Ident) (ctx : EvalCtx) (sc : ScopeCtx) :
    PubDisc (lookupOpenPropertiesInParentChain sc name ctx) := by
  induction sc using lookupOpenPropertiesInParentChain.induct with
  | _ t ih =>
    have := pub_lookupOpenProperties
    unfold lookupOpenPropertiesInParentChain
    cases t with
    | mk parent _ _ _ _ _ _ _ => cases parent <;> pub_tac_base

theorem pub_aliasStepNavigateWith (structureOf : Algorithm → EvalCtx → EvalM (Option Algorithm))
    (h : ∀ a c, PubDisc (structureOf a c)) (stepCtx : EvalCtx) (notStatic : Error)
    (value : Algorithm) (last : Option ResolvedProperty) (receiverName : String) (steps : List Ident) :
    PubDisc (aliasStepNavigateWith structureOf stepCtx notStatic value last receiverName steps) := by
  induction steps generalizing value last receiverName with
  | nil => unfold aliasStepNavigateWith; pub_tac_base
  | cons member rest ih => unfold aliasStepNavigateWith; pub_tac_base

theorem pub_staticPathSelectWith (structureOf : Algorithm → EvalCtx → EvalM (Option Algorithm))
    (h : ∀ a c, PubDisc (structureOf a c)) (owner : Algorithm) (target : Expr) (stepCtx : EvalCtx) :
    PubDisc (staticPathSelectWith structureOf owner target stepCtx) := by
  have := pub_aliasStepNavigateWith structureOf h
  have := pub_lookupOpenProperties
  have := pub_lookupOpenPropertiesInParentChain
  unfold staticPathSelectWith; pub_tac_base

theorem pub_resolveAliasStepWith (structureOf : Algorithm → EvalCtx → EvalM (Option Algorithm))
    (h : ∀ a c, PubDisc (structureOf a c)) (step : Algorithm) (target : Expr) (ctx : EvalCtx) :
    PubDisc (resolveAliasStepWith structureOf step target ctx) := by
  unfold resolveAliasStepWith; exact pub_staticPathSelectWith structureOf h step target (ctx.push step)

theorem pub_aliasRouteIsIntrinsicWith (structureOf : Algorithm → EvalCtx → EvalM (Option Algorithm))
    (h : ∀ a c, PubDisc (structureOf a c)) (receiver : Expr) (ctx : EvalCtx) :
    PubDisc (aliasRouteIsIntrinsicWith structureOf receiver ctx) := by
  have := pub_aliasStepNavigateWith structureOf h
  have := pub_lookupOpenProperties
  have := pub_lookupOpenPropertiesInParentChain
  unfold aliasRouteIsIntrinsicWith; pub_tac_base

section LocalLoops
variable (rec : EvalRec) (hrec : ∀ c, PubDisc (rec c)) (hres : ResSusp rec)
include hrec hres

theorem pub_outputRowsCollect (rowCtx : EvalCtx) (env : ValEnv) (rows : List Expr)
    (acc : List Result) (emitted : Nat) :
    PubDisc (EvalBody.evalOutputRowsPreparedCore.collect rec rowCtx env rows acc emitted) := by
  induction rows generalizing acc emitted with
  | nil => unfold EvalBody.evalOutputRowsPreparedCore.collect; pub_tac_base
  | cons e rest ih => unfold EvalBody.evalOutputRowsPreparedCore.collect; pub_tac_base

theorem pub_explicitRowsCollect (rowCtx : EvalCtx) (env : ValEnv) (rows : List Expr) (acc : List Result) :
    PubDisc (EvalBody.evalExplicitSequenceValueRowSlots.collect rec rowCtx env rows acc) := by
  induction rows generalizing acc with
  | nil => unfold EvalBody.evalExplicitSequenceValueRowSlots.collect; pub_tac_base
  | cons e rest ih => unfold EvalBody.evalExplicitSequenceValueRowSlots.collect; pub_tac_base

theorem pub_listLiteralCollect (ctx : EvalCtx) (env : ValEnv) (elements : List Expr) (acc : List Result) :
    PubDisc (EvalBody.evalListLiteralCounted.collect rec ctx env elements acc) := by
  induction elements generalizing acc with
  | nil => unfold EvalBody.evalListLiteralCounted.collect; pub_tac_base
  | cons e rest ih => unfold EvalBody.evalListLiteralCounted.collect; pub_tac_base

theorem pub_sequenceConstructLoop (ctx : EvalCtx) (env : ValEnv) (leaves : List Expr) (items : List Result) :
    PubDisc (EvalBody.evalSequenceConstructCounted.loop rec ctx env leaves items) := by
  induction leaves generalizing items with
  | nil => unfold EvalBody.evalSequenceConstructCounted.loop; pub_tac_base
  | cons e rest ih => unfold EvalBody.evalSequenceConstructCounted.loop; pub_tac_base

theorem pub_prepareControls (b : Builtin) (ctx : EvalCtx) (env : ValEnv)
    (descriptors : List SequenceBuiltinSuffixArgDescriptor) (items : List CallableCallItem) :
    PubDisc (EvalBody.bindSequenceBuiltinArguments.prepareControls rec b ctx env descriptors items) := by
  induction descriptors generalizing items with
  | nil => cases items <;> (unfold EvalBody.bindSequenceBuiltinArguments.prepareControls; pub_tac_base)
  | cons d rest ih => cases items <;> (unfold EvalBody.bindSequenceBuiltinArguments.prepareControls; pub_tac_base)

theorem pub_reduceLoop (stepAlg : Algorithm) (ctx : EvalCtx) (env : ValEnv)
    (items : List CountedResult) (acc : CountedResult) :
    PubDisc (EvalBody.evalReduceCounted.reduceLoop rec stepAlg ctx env items acc) := by
  induction items generalizing acc with
  | nil => unfold EvalBody.evalReduceCounted.reduceLoop; pub_tac_base
  | cons i rest ih => unfold EvalBody.evalReduceCounted.reduceLoop; pub_tac_base

theorem pub_filterLoop (predicateAlg : Algorithm) (ctx : EvalCtx) (env : ValEnv)
    (index : Nat) (items : List CountedResult) :
    PubDisc (EvalBody.evalFilterCounted.filterLoop rec predicateAlg ctx env index items) := by
  induction items generalizing index with
  | nil => unfold EvalBody.evalFilterCounted.filterLoop; pub_tac_base
  | cons i rest ih => unfold EvalBody.evalFilterCounted.filterLoop; pub_tac_base

theorem pub_mapLoop (transformAlg : Algorithm) (ctx : EvalCtx) (env : ValEnv) (items : List CountedResult) :
    PubDisc (EvalBody.evalMapCounted.mapLoop rec transformAlg ctx env items) := by
  induction items with
  | nil => unfold EvalBody.evalMapCounted.mapLoop; pub_tac_base
  | cons i rest ih => unfold EvalBody.evalMapCounted.mapLoop; pub_tac_base

theorem pub_repeatLoop (ctx : EvalCtx) (env : ValEnv) (step : ResolvedArgumentAlgorithm)
    (stepName : String) (remaining : Nat) (cells : List Nat) :
    PubDisc (EvalBody.applyBuiltinCounted.repeatLoop rec ctx env step stepName remaining cells) := by
  induction remaining generalizing cells with
  | zero => unfold EvalBody.applyBuiltinCounted.repeatLoop; pub_tac_base
  | succ k ih => unfold EvalBody.applyBuiltinCounted.repeatLoop; pub_tac_base

end LocalLoops

set_option hygiene false in
/-- Syntax-directed link discipline of an evaluator body, given that its recursive answer `hrec`
    is link-disciplined. -/
macro "pub_tac" : tactic => `(tactic| without_info_trees ((try pub_unfold_rec) <;> repeat' (first
  | pub_res
  | pub_rec
  | pub_hyp
  | pub_absurd
  | (with_reducible apply pub_get_bind)
  | (with_reducible apply PubAt.bind)
  | (with_reducible apply PubAt.set; first
      | exact PubHeapKept.refl _
      | (apply PubHeapKept.set_bang <;> first | pub_hyp | (exact pubKept_of_same _ _ rfl rfl rfl)))
  | (with_reducible apply PubDisc.withCtx)
  | (with_reducible apply PubDisc.captureMeta)
  | (with_reducible apply PubDisc.attempt)
  | (with_reducible apply PubDisc.map)
  | (with_reducible apply PubDisc.bind)
  | (with_reducible apply pubDisc_pure)
  | (with_reducible apply pubDisc_get)
  | (with_reducible apply pubDisc_throw)
  | (with_reducible apply pubDisc_evalError)
  | (with_reducible apply pubDisc_lift)
  | (with_reducible apply pubDisc_allocate)
  | (with_reducible apply pubDisc_supply)
  | (with_reducible apply pubDisc_mapM)
  | (with_reducible apply pubDisc_form)
  | (with_reducible apply pubDisc_slot)
  | (with_reducible apply pubDisc_prepare)
  | (with_reducible apply pubDisc_routeOf)
  | (with_reducible apply pubDisc_calleeCell)
  | (with_reducible apply pubDisc_projectionStep)
  | (with_reducible apply pubDisc_receiverCell)
  | (with_reducible apply pubDisc_linkCallable)
  | (with_reducible apply pubDisc_linkValue)
  | (with_reducible apply pubDisc_decodeCallee)
  | (with_reducible apply pubDisc_execute)
  | (with_reducible apply pubDisc_step)
  | (with_reducible apply pubDisc_reify)
  | (with_reducible apply pubDisc_invoke)
  | (with_reducible apply pubDisc_reference)
  | (with_reducible apply pubDisc_viewCells)
  | (with_reducible apply pub_modify; intro s; first
      | exact PubHeapKept.refl _
      | (apply PubHeapKept.modify; intro c _; exact pubKept_of_same _ _ rfl rfl rfl))
  | (with_reducible apply pub_forIn)
  | (with_reducible apply pub_forM)
  | (with_reducible apply pub_foldlM)
  | (with_reducible apply pub_formLeftToRight)
  | (with_reducible apply pub_discover)
  | (with_reducible apply pub_selectWith)
  | (with_reducible apply pub_selectViewWith)
  | (with_reducible apply pub_bindPatterns)
  | (with_reducible apply pub_selectFamily)
  | (with_reducible apply pub_collectSingleAtomicNumbers)
  | (with_reducible apply pub_minLoop)
  | (with_reducible apply pub_maxLoop)
  | (with_reducible apply pub_resolveAlgForOpen)
  | (with_reducible apply pub_openStructure)
  | (with_reducible apply pub_resolveAliasStepWith)
  | (with_reducible apply pub_staticPathSelectWith)
  | (with_reducible apply pub_aliasRouteIsIntrinsicWith)
  | (with_reducible apply pub_lookupOpenProperties)
  | (with_reducible apply pub_lookupOpenPropertiesInParentChain)
  | (with_reducible apply EvalBody.terminalAccess_pubDisc rec hrec hres)
  | (with_reducible apply EvalBody.staticReferenceTerminal_pubDisc rec hrec hres)
  | (with_reducible apply EvalBody.transparentCollectorSlice_pubDisc rec hrec hres)
  | (with_reducible apply EvalBody.transparentRetainedCell_pubDisc rec hrec hres)
  | (with_reducible apply EvalBody.retainedSliceAt_pubDisc rec hrec hres)
  | (with_reducible apply EvalBody.writtenCollectorSlice_pubDisc rec hrec hres)
  | (with_reducible apply retainedCollectorBuiltin_pubDisc rec hrec hres)
  | (with_reducible apply pub_outputRowsCollect rec hrec hres)
  | (with_reducible apply pub_explicitRowsCollect rec hrec hres)
  | (with_reducible apply pub_listLiteralCollect rec hrec hres)
  | (with_reducible apply pub_sequenceConstructLoop rec hrec hres)
  | (with_reducible apply pub_prepareControls rec hrec hres)
  | (with_reducible apply pub_reduceLoop rec hrec hres)
  | (with_reducible apply pub_filterLoop rec hrec hres)
  | (with_reducible apply pub_mapLoop rec hrec hres)
  | (with_reducible apply pub_repeatLoop rec hrec hres)
  | (with_reducible apply CapsPub.mk)

  | split
  | pub_intro_syntactic
  | pub_zeta
  | pub_whnf_core
  | pub_unfold_head
  | (with_reducible apply PubAt.of_disc))))

theorem EvalBody.whileLoop_pubDisc (rec : EvalRec) (hrec : ∀ c, PubDisc (rec c)) (hres : ResSusp rec) (step : ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) (stepName : String) (cells : List Nat) :
    PubDisc (EvalBody.whileLoop rec step ctx env stepName cells) := by
  unfold EvalBody.whileLoop; pub_tac

theorem EvalBody.aliasStepIsRuntime_pubDisc (rec : EvalRec) (hrec : ∀ c, PubDisc (rec c)) (hres : ResSusp rec) (step : Algorithm) (target : Expr) (ctx : EvalCtx) (visited : List String) :
    PubDisc (EvalBody.aliasStepIsRuntime rec step target ctx visited) := by
  unfold EvalBody.aliasStepIsRuntime; pub_tac

theorem EvalBody.aliasValue_pubDisc (rec : EvalRec) (hrec : ∀ c, PubDisc (rec c)) (hres : ResSusp rec) (wired : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    PubDisc (EvalBody.aliasValue rec wired ctx env) := by
  unfold EvalBody.aliasValue; pub_tac

theorem EvalBody.resolveAliasChase_pubDisc (rec : EvalRec) (hrec : ∀ c, PubDisc (rec c)) (hres : ResSusp rec) (followCarriers projectRuntime : Bool) (a : Algorithm) (ctx : EvalCtx) (visited : List String) (last : Option (Algorithm × PropDef)) :
    PubDisc (EvalBody.resolveAliasChase rec followCarriers projectRuntime a ctx visited last) := by
  unfold EvalBody.resolveAliasChase; pub_tac

theorem EvalBody.resolveAliasStructure_pubDisc (rec : EvalRec) (hrec : ∀ c, PubDisc (rec c)) (hres : ResSusp rec) (a : Algorithm) (ctx : EvalCtx) :
    PubDisc (EvalBody.resolveAliasStructure rec a ctx) := by
  unfold EvalBody.resolveAliasStructure; pub_tac

theorem EvalBody.aliasOriginBinding?_pubDisc (rec : EvalRec) (hrec : ∀ c, PubDisc (rec c)) (hres : ResSusp rec) (a : Algorithm) (ctx : EvalCtx) :
    PubDisc (EvalBody.aliasOriginBinding? rec a ctx) := by
  unfold EvalBody.aliasOriginBinding?; pub_tac

theorem EvalBody.resolveAliasTarget_pubDisc (rec : EvalRec) (hrec : ∀ c, PubDisc (rec c)) (hres : ResSusp rec) (a : Algorithm) (ctx : EvalCtx) :
    PubDisc (EvalBody.resolveAliasTarget rec a ctx) := by
  unfold EvalBody.resolveAliasTarget; pub_tac

theorem EvalBody.resolveAliasValueTarget_pubDisc (rec : EvalRec) (hrec : ∀ c, PubDisc (rec c)) (hres : ResSusp rec) (a : Algorithm) (ctx : EvalCtx) :
    PubDisc (EvalBody.resolveAliasValueTarget rec a ctx) := by
  unfold EvalBody.resolveAliasValueTarget; pub_tac

theorem EvalBody.lookupLexicalProperty_pubDisc (rec : EvalRec) (hrec : ∀ c, PubDisc (rec c)) (hres : ResSusp rec) (a : Algorithm) (name : Ident) (ctx : EvalCtx) :
    PubDisc (EvalBody.lookupLexicalProperty rec a name ctx) := by
  unfold EvalBody.lookupLexicalProperty; pub_tac

theorem EvalBody.lookupLexicalValueProperty_pubDisc (rec : EvalRec) (hrec : ∀ c, PubDisc (rec c)) (hres : ResSusp rec) (a : Algorithm) (name : Ident) (ctx : EvalCtx) :
    PubDisc (EvalBody.lookupLexicalValueProperty rec a name ctx) := by
  unfold EvalBody.lookupLexicalValueProperty; pub_tac

theorem EvalBody.lookupLexical_pubDisc (rec : EvalRec) (hrec : ∀ c, PubDisc (rec c)) (hres : ResSusp rec) (a : Algorithm) (name : Ident) (ctx : EvalCtx) :
    PubDisc (EvalBody.lookupLexical rec a name ctx) := by
  unfold EvalBody.lookupLexical; pub_tac

theorem EvalBody.needPlanNormalizeCallee_pubDisc (rec : EvalRec) (hrec : ∀ c, PubDisc (rec c)) (hres : ResSusp rec) (callee : Algorithm) (ctx : EvalCtx) :
    PubDisc (EvalBody.needPlanNormalizeCallee rec callee ctx) := by
  unfold EvalBody.needPlanNormalizeCallee; pub_tac

theorem EvalBody.resolveAlg_pubDisc (rec : EvalRec) (hrec : ∀ c, PubDisc (rec c)) (hres : ResSusp rec) (e : Expr) (ctx : EvalCtx) :
    PubDisc (EvalBody.resolveAlg rec e ctx) := by
  unfold EvalBody.resolveAlg; pub_tac

theorem EvalBody.projectNeedCallable_pubDisc (rec : EvalRec) (hrec : ∀ c, PubDisc (rec c)) (hres : ResSusp rec) (address : Nat) :
    PubDisc (EvalBody.projectNeedCallable rec address) := by
  unfold EvalBody.projectNeedCallable; pub_tac

theorem EvalBody.projectNeedWrittenAt_pubDisc (rec : EvalRec) (hrec : ∀ c, PubDisc (rec c)) (hres : ResSusp rec) (address : Nat) (source : Expr) (caller : EvalCtx) :
    PubDisc (EvalBody.projectNeedWrittenAt rec address source caller) := by
  unfold EvalBody.projectNeedWrittenAt; pub_tac

theorem EvalBody.linkCallable_pubDisc (rec : EvalRec) (hrec : ∀ c, PubDisc (rec c)) (hres : ResSusp rec) (address : Nat) :
    PubDisc (EvalBody.linkCallable rec address) := by
  unfold EvalBody.linkCallable; pub_tac

theorem EvalBody.projectParameterCallable_pubDisc (rec : EvalRec) (hrec : ∀ c, PubDisc (rec c)) (hres : ResSusp rec) (x : Ident) (ctx : EvalCtx) :
    PubDisc (EvalBody.projectParameterCallable rec x ctx) := by
  unfold EvalBody.projectParameterCallable; pub_tac

theorem EvalBody.projectNeedWritten_pubDisc (rec : EvalRec) (hrec : ∀ c, PubDisc (rec c)) (hres : ResSusp rec) (source : Expr) (caller : EvalCtx) :
    PubDisc (EvalBody.projectNeedWritten rec source caller) := by
  unfold EvalBody.projectNeedWritten; pub_tac

theorem EvalBody.projectNeedStructuralMember_pubDisc (rec : EvalRec) (hrec : ∀ c, PubDisc (rec c)) (hres : ResSusp rec) (source : Expr) (ctx : EvalCtx) :
    PubDisc (EvalBody.projectNeedStructuralMember rec source ctx) := by
  unfold EvalBody.projectNeedStructuralMember; pub_tac

theorem EvalBody.resolveCalleeAlg_pubDisc (rec : EvalRec) (hrec : ∀ c, PubDisc (rec c)) (hres : ResSusp rec) (f : Expr) (ctx : EvalCtx) :
    PubDisc (EvalBody.resolveCalleeAlg rec f ctx) := by
  unfold EvalBody.resolveCalleeAlg; pub_tac

theorem EvalBody.expectPreparedSequenceBuiltinAlgorithmSuffixArg_pubDisc (rec : EvalRec) (hrec : ∀ c, PubDisc (rec c)) (hres : ResSusp rec) (b : Builtin) (descriptors : List SequenceBuiltinSuffixArgDescriptor) (args : List PreparedSequenceBuiltinSuffixArg) (index : Nat) :
    PubDisc (EvalBody.expectPreparedSequenceBuiltinAlgorithmSuffixArg rec b descriptors args index) := by
  unfold EvalBody.expectPreparedSequenceBuiltinAlgorithmSuffixArg; pub_tac

theorem EvalBody.resolveDotReceiver?_pubDisc (rec : EvalRec) (hrec : ∀ c, PubDisc (rec c)) (hres : ResSusp rec) (e : Expr) (ctx : EvalCtx) :
    PubDisc (EvalBody.resolveDotReceiver? rec e ctx) := by
  unfold EvalBody.resolveDotReceiver?; pub_tac

theorem EvalBody.resolveDotReceiver_pubDisc (rec : EvalRec) (hrec : ∀ c, PubDisc (rec c)) (hres : ResSusp rec) (e : Expr) (ctx : EvalCtx) :
    PubDisc (EvalBody.resolveDotReceiver rec e ctx) := by
  unfold EvalBody.resolveDotReceiver; pub_tac

theorem EvalBody.algorithmIntrinsicRoute_pubDisc (rec : EvalRec) (hrec : ∀ c, PubDisc (rec c)) (hres : ResSusp rec) (receiver : Expr) (ctx : EvalCtx) :
    PubDisc (EvalBody.algorithmIntrinsicRoute rec receiver ctx) := by
  unfold EvalBody.algorithmIntrinsicRoute; pub_tac

theorem EvalBody.demandNeedRecursive_pubDisc (rec : EvalRec) (hrec : ∀ c, PubDisc (rec c)) (hres : ResSusp rec) (address : Nat) :
    PubDisc (EvalBody.demandNeedRecursive rec address) := by
  unfold EvalBody.demandNeedRecursive; pub_tac

theorem EvalBody.evalSuppliedAt_pubDisc (rec : EvalRec) (hrec : ∀ c, PubDisc (rec c)) (hres : ResSusp rec) (address : Nat) (e : Expr) (ctx : EvalCtx) (env : ValEnv) :
    PubDisc (EvalBody.evalSuppliedAt rec address e ctx env) := by
  unfold EvalBody.evalSuppliedAt; pub_tac

theorem EvalBody.linkValue_pubDisc (rec : EvalRec) (hrec : ∀ c, PubDisc (rec c)) (hres : ResSusp rec) (address : Nat) :
    PubDisc (EvalBody.linkValue rec address) := by
  unfold EvalBody.linkValue; pub_tac

theorem EvalBody.algorithmOfValue_pubDisc (rec : EvalRec) (hrec : ∀ c, PubDisc (rec c)) (hres : ResSusp rec) (val : Result) (argsOpt : Option OutputBundle) (ctx : EvalCtx) (env : ValEnv) :
    PubDisc (EvalBody.algorithmOfValue rec val argsOpt ctx env) := by
  unfold EvalBody.algorithmOfValue; pub_tac

theorem EvalBody.capturedCallee_pubDisc (rec : EvalRec) (hrec : ∀ c, PubDisc (rec c)) (hres : ResSusp rec) (callee : Nat) :
    PubDisc (EvalBody.capturedCallee rec callee) := by
  unfold EvalBody.capturedCallee; pub_tac

theorem EvalBody.referenceReceiverValue_pubDisc (rec : EvalRec) (hrec : ∀ c, PubDisc (rec c)) (hres : ResSusp rec) (target : Expr) (targetAlg : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    PubDisc (EvalBody.referenceReceiverValue rec target targetAlg ctx env) := by
  unfold EvalBody.referenceReceiverValue; pub_tac

theorem EvalBody.algorithmCalleeOf_pubDisc (rec : EvalRec) (hrec : ∀ c, PubDisc (rec c)) (hres : ResSusp rec) (receiver : Expr) (ctx : EvalCtx) (env : ValEnv) :
    PubDisc (EvalBody.algorithmCalleeOf rec receiver ctx env) := by
  unfold EvalBody.algorithmCalleeOf; pub_tac

/-- D-3 (E-18 receiver-read correction): the planned `.Algorithm` invocation's callee read — the
    production route's `project` — keeps the FG-M1 entry facts. -/
theorem EvalBody.plannedLinkCallable_pubDisc (rec : EvalRec) (hrec : ∀ c, PubDisc (rec c)) (hres : ResSusp rec) (link : Nat) :
    PubDisc (EvalBody.plannedLinkCallable rec link) := by
  unfold EvalBody.plannedLinkCallable; pub_tac

theorem EvalBody.evalSuppliedCallCounted_pubDisc (rec : EvalRec) (hrec : ∀ c, PubDisc (rec c)) (hres : ResSusp rec) (origin : CalleeOrigin) (callee : Algorithm) (cells : List NeedSupply.Sourced) (ctx : EvalCtx) (env : ValEnv) (calleeName : String) :
    PubDisc (EvalBody.evalSuppliedCallCounted rec origin callee cells ctx env calleeName) := by
  unfold EvalBody.evalSuppliedCallCounted; pub_tac

theorem EvalBody.evalNeedUserSupply_pubDisc (rec : EvalRec) (hrec : ∀ c, PubDisc (rec c)) (hres : ResSusp rec) (callee : Algorithm) (cells : List Nat) (ctx : EvalCtx) (env : ValEnv) :
    PubDisc (EvalBody.evalNeedUserSupply rec callee cells ctx env) := by
  unfold EvalBody.evalNeedUserSupply; pub_tac

theorem EvalBody.evalNeedFamilySupply_pubDisc (rec : EvalRec) (hrec : ∀ c, PubDisc (rec c)) (hres : ResSusp rec) (callee : Algorithm) (cells : List Nat) (ctx : EvalCtx) (env : ValEnv) (calleeName : String) :
    PubDisc (EvalBody.evalNeedFamilySupply rec callee cells ctx env calleeName) := by
  unfold EvalBody.evalNeedFamilySupply; pub_tac

theorem EvalBody.invokeNeed_pubDisc (rec : EvalRec) (hrec : ∀ c, PubDisc (rec c)) (hres : ResSusp rec) (arg : ResolvedArgumentAlgorithm) :
    PubDisc (EvalBody.invokeNeed rec arg) := by
  unfold EvalBody.invokeNeed; pub_tac

theorem EvalBody.argumentNeed_pubDisc (rec : EvalRec) (hrec : ∀ c, PubDisc (rec c)) (hres : ResSusp rec) (arg : ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) :
    PubDisc (EvalBody.argumentNeed rec arg ctx env) := by
  unfold EvalBody.argumentNeed; pub_tac

theorem EvalBody.runNeedStepSlots_pubDisc (rec : EvalRec) (hrec : ∀ c, PubDisc (rec c)) (hres : ResSusp rec) (step : Algorithm) (ctx : EvalCtx) (env : ValEnv) (cells : List Nat) (stepName : String) :
    PubDisc (EvalBody.runNeedStepSlots rec step ctx env cells stepName) := by
  unfold EvalBody.runNeedStepSlots EvalBody.runNeedStepWith; pub_tac

theorem EvalBody.runNeedWhileRound_pubDisc (rec : EvalRec) (hrec : ∀ c, PubDisc (rec c)) (hres : ResSusp rec) (step : Algorithm) (ctx : EvalCtx) (env : ValEnv) (cells : List Nat) (stepName : String) :
    PubDisc (EvalBody.runNeedWhileRound rec step ctx env cells stepName) := by
  unfold EvalBody.runNeedWhileRound EvalBody.runNeedStepWith; pub_tac

theorem EvalBody.evalAlgOutputCore_pubDisc (rec : EvalRec) (hrec : ∀ c, PubDisc (rec c)) (hres : ResSusp rec) (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    PubDisc (EvalBody.evalAlgOutputCore rec a ctx env) := by
  unfold EvalBody.evalAlgOutputCore; pub_tac

theorem EvalBody.evalAlgOutput_pubDisc (rec : EvalRec) (hrec : ∀ c, PubDisc (rec c)) (hres : ResSusp rec) (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    PubDisc (EvalBody.evalAlgOutput rec a ctx env) := by
  unfold EvalBody.evalAlgOutput; pub_tac

theorem EvalBody.evalProgramOutput_pubDisc (rec : EvalRec) (hrec : ∀ c, PubDisc (rec c)) (hres : ResSusp rec) (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    PubDisc (EvalBody.evalProgramOutput rec a ctx env) := by
  unfold EvalBody.evalProgramOutput; pub_tac

theorem EvalBody.evalAlgOutputSlots_pubDisc (rec : EvalRec) (hrec : ∀ c, PubDisc (rec c)) (hres : ResSusp rec) (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    PubDisc (EvalBody.evalAlgOutputSlots rec a ctx env) := by
  unfold EvalBody.evalAlgOutputSlots ActivatedBody.readRows; pub_tac

theorem EvalBody.formOutputRow_pubDisc (rec : EvalRec) (hrec : ∀ c, PubDisc (rec c)) (hres : ResSusp rec) (ctx : EvalCtx) (env : ValEnv) (e : Expr) :
    PubDisc (EvalBody.formOutputRow rec ctx env e) := by
  unfold EvalBody.formOutputRow; pub_tac

theorem EvalBody.whileVerdictSlots_pubDisc (rec : EvalRec) (hrec : ∀ c, PubDisc (rec c)) (hres : ResSusp rec) (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    PubDisc (EvalBody.whileVerdictSlots rec a ctx env) := by
  unfold EvalBody.whileVerdictSlots ActivatedBody.readRows; pub_tac

theorem EvalBody.evalSequenceCallbackCall_pubDisc (rec : EvalRec) (hrec : ∀ c, PubDisc (rec c)) (hres : ResSusp rec) (callee : Algorithm) (item : CountedResult) (ctx : EvalCtx) (env : ValEnv) (calleeName : String) :
    PubDisc (EvalBody.evalSequenceCallbackCall rec callee item ctx env calleeName) := by
  unfold EvalBody.evalSequenceCallbackCall; pub_tac

theorem EvalBody.evalSequenceCallbackCallCounted_pubDisc (rec : EvalRec) (hrec : ∀ c, PubDisc (rec c)) (hres : ResSusp rec) (callee : Algorithm) (item : CountedResult) (ctx : EvalCtx) (env : ValEnv) (calleeName : String) :
    PubDisc (EvalBody.evalSequenceCallbackCallCounted rec callee item ctx env calleeName) := by
  unfold EvalBody.evalSequenceCallbackCallCounted; pub_tac

theorem EvalBody.evalAlgOutputPreparedCore_pubDisc (rec : EvalRec) (hrec : ∀ c, PubDisc (rec c)) (hres : ResSusp rec) (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    PubDisc (EvalBody.evalAlgOutputPreparedCore rec a ctx env) := by
  unfold EvalBody.evalAlgOutputPreparedCore; pub_tac

theorem EvalBody.evalOutputRowsPreparedCore_pubDisc (rec : EvalRec) (hrec : ∀ c, PubDisc (rec c)) (hres : ResSusp rec) (rows : OutputBundle) (rowCtx : EvalCtx) (env : ValEnv) :
    PubDisc (EvalBody.evalOutputRowsPreparedCore rec rows rowCtx env) := by
  unfold EvalBody.evalOutputRowsPreparedCore; pub_tac

theorem EvalBody.evalCapturePreparedCore_pubDisc (rec : EvalRec) (hrec : ∀ c, PubDisc (rec c)) (hres : ResSusp rec) (rows : OutputBundle) (ctx : EvalCtx) (env : ValEnv) :
    PubDisc (EvalBody.evalCapturePreparedCore rec rows ctx env) := by
  unfold EvalBody.evalCapturePreparedCore; pub_tac

theorem EvalBody.evalCaptureCountedCore_pubDisc (rec : EvalRec) (hrec : ∀ c, PubDisc (rec c)) (hres : ResSusp rec) (rows : OutputBundle) (ctx : EvalCtx) (env : ValEnv) :
    PubDisc (EvalBody.evalCaptureCountedCore rec rows ctx env) := by
  unfold EvalBody.evalCaptureCountedCore; pub_tac

theorem EvalBody.evalCaptureValue_pubDisc (rec : EvalRec) (hrec : ∀ c, PubDisc (rec c)) (hres : ResSusp rec) (rows : OutputBundle) (ctx : EvalCtx) (env : ValEnv) :
    PubDisc (EvalBody.evalCaptureValue rec rows ctx env) := by
  unfold EvalBody.evalCaptureValue; pub_tac

theorem EvalBody.evalAlgOutputCountedCore_pubDisc (rec : EvalRec) (hrec : ∀ c, PubDisc (rec c)) (hres : ResSusp rec) (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    PubDisc (EvalBody.evalAlgOutputCountedCore rec a ctx env) := by
  unfold EvalBody.evalAlgOutputCountedCore; pub_tac

theorem EvalBody.evalAlgOutputCounted_pubDisc (rec : EvalRec) (hrec : ∀ c, PubDisc (rec c)) (hres : ResSusp rec) (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    PubDisc (EvalBody.evalAlgOutputCounted rec a ctx env) := by
  unfold EvalBody.evalAlgOutputCounted; pub_tac

/-- A VALUE terminal's read (`EvalBody.terminalAccess`), proved once and used by every body that
    reads one, so those bodies never unfold it inline (M4★). -/
theorem EvalBody.terminalAccess_pubDisc (rec : EvalRec) (hrec : ∀ c, PubDisc (rec c)) (hres : ResSusp rec) (t : AliasTerminal) (ctx : EvalCtx) (env : ValEnv) :
    PubDisc (EvalBody.terminalAccess rec t ctx env) := by
  unfold EvalBody.terminalAccess; pub_tac

theorem EvalBody.evalZeroArgumentDemandOutputCounted_pubDisc (rec : EvalRec) (hrec : ∀ c, PubDisc (rec c)) (hres : ResSusp rec) (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    PubDisc (EvalBody.evalZeroArgumentDemandOutputCounted rec a ctx env) := by
  unfold EvalBody.evalZeroArgumentDemandOutputCounted; pub_tac

theorem EvalBody.evalZeroArgumentDemandOutput_pubDisc (rec : EvalRec) (hrec : ∀ c, PubDisc (rec c)) (hres : ResSusp rec) (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    PubDisc (EvalBody.evalZeroArgumentDemandOutput rec a ctx env) := by
  unfold EvalBody.evalZeroArgumentDemandOutput; pub_tac

theorem EvalBody.evalArgumentValueCounted_pubDisc (rec : EvalRec) (hrec : ∀ c, PubDisc (rec c)) (hres : ResSusp rec) (arg : ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) :
    PubDisc (EvalBody.evalArgumentValueCounted rec arg ctx env) := by
  unfold EvalBody.evalArgumentValueCounted; pub_tac

theorem EvalBody.evalArgumentValue_pubDisc (rec : EvalRec) (hrec : ∀ c, PubDisc (rec c)) (hres : ResSusp rec) (arg : ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) :
    PubDisc (EvalBody.evalArgumentValue rec arg ctx env) := by
  unfold EvalBody.evalArgumentValue; pub_tac

/-- CACHE-PUB-1: a property request's calculation (a read's demand, an invocation's fresh call) is
    link-disciplined whenever its recursive answer is. -/
theorem EvalBody.zeroArgPropertyCalculation_pubDisc (rec : EvalRec) (hrec : ∀ c, PubDisc (rec c)) (hres : ResSusp rec) (request : ZeroArgPropertyRequest) (resolvedAlgorithm : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    PubDisc (EvalBody.zeroArgPropertyCalculation rec request resolvedAlgorithm ctx env) := by
  unfold EvalBody.zeroArgPropertyCalculation; pub_tac

theorem EvalBody.evalZeroArgPropertyAccessCounted_pubDisc (rec : EvalRec) (hrec : ∀ c, PubDisc (rec c)) (hres : ResSusp rec) (accessKind : ZeroArgPropertyAccessKind) (owner : Algorithm) (binding : PropDef) (resolvedAlgorithm : Algorithm) (ctx : EvalCtx) (env : ValEnv) (request : ZeroArgPropertyRequest) :
    PubDisc (EvalBody.evalZeroArgPropertyAccessCounted rec accessKind owner binding resolvedAlgorithm ctx env request) := by
  have hcalc : ∀ q, PubDisc (EvalBody.zeroArgPropertyCalculation rec q resolvedAlgorithm ctx env) :=
    fun q => EvalBody.zeroArgPropertyCalculation_pubDisc rec hrec hres q resolvedAlgorithm ctx env
  unfold EvalBody.evalZeroArgPropertyAccessCounted; pub_tac

theorem EvalBody.evalZeroArgPropertyAccess_pubDisc (rec : EvalRec) (hrec : ∀ c, PubDisc (rec c)) (hres : ResSusp rec) (accessKind : ZeroArgPropertyAccessKind) (owner : Algorithm) (binding : PropDef) (resolvedAlgorithm : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    PubDisc (EvalBody.evalZeroArgPropertyAccess rec accessKind owner binding resolvedAlgorithm ctx env) := by
  unfold EvalBody.evalZeroArgPropertyAccess; pub_tac

theorem EvalBody.evalConditionalCallbackCallCounted_pubDisc (rec : EvalRec) (hrec : ∀ c, PubDisc (rec c)) (hres : ResSusp rec) (callee : Algorithm) (args : List CountedResult) (ctx : EvalCtx) (env : ValEnv) (calleeName : String) :
    PubDisc (EvalBody.evalConditionalCallbackCallCounted rec callee args ctx env calleeName) := by
  unfold EvalBody.evalConditionalCallbackCallCounted; pub_tac

theorem EvalBody.evalUserCallbackCallCounted_pubDisc (rec : EvalRec) (hrec : ∀ c, PubDisc (rec c)) (hres : ResSusp rec) (callee : Algorithm) (args : List CountedResult) (ctx : EvalCtx) (env : ValEnv) :
    PubDisc (EvalBody.evalUserCallbackCallCounted rec callee args ctx env) := by
  unfold EvalBody.evalUserCallbackCallCounted; pub_tac

theorem EvalBody.evalResolvedCallbackCallCounted_pubDisc (rec : EvalRec) (hrec : ∀ c, PubDisc (rec c)) (hres : ResSusp rec) (callee : Algorithm) (args : List CountedResult) (ctx : EvalCtx) (env : ValEnv) (calleeName : String) :
    PubDisc (EvalBody.evalResolvedCallbackCallCounted rec callee args ctx env calleeName) := by
  unfold EvalBody.evalResolvedCallbackCallCounted; pub_tac

theorem EvalBody.evalResolvedCallbackCall_pubDisc (rec : EvalRec) (hrec : ∀ c, PubDisc (rec c)) (hres : ResSusp rec) (callee : Algorithm) (args : List CountedResult) (ctx : EvalCtx) (env : ValEnv) (calleeName : String) :
    PubDisc (EvalBody.evalResolvedCallbackCall rec callee args ctx env calleeName) := by
  unfold EvalBody.evalResolvedCallbackCall; pub_tac

theorem EvalBody.evalSequenceReduceStepCounted_pubDisc (rec : EvalRec) (hrec : ∀ c, PubDisc (rec c)) (hres : ResSusp rec) (callee : Algorithm) (element : CountedResult) (accumulator : Result) (ctx : EvalCtx) (env : ValEnv) (calleeName : String) :
    PubDisc (EvalBody.evalSequenceReduceStepCounted rec callee element accumulator ctx env calleeName) := by
  unfold EvalBody.evalSequenceReduceStepCounted; pub_tac

theorem EvalBody.demandSequenceBuiltinCallItemValue_pubDisc (rec : EvalRec) (hrec : ∀ c, PubDisc (rec c)) (hres : ResSusp rec) (item : CallableCallItem) (ctx : EvalCtx) (env : ValEnv) :
    PubDisc (EvalBody.demandSequenceBuiltinCallItemValue rec item ctx env) := by
  unfold EvalBody.demandSequenceBuiltinCallItemValue; pub_tac

theorem EvalBody.staticReferenceTerminal_pubDisc (rec : EvalRec) (hrec : ∀ c, PubDisc (rec c)) (hres : ResSusp rec) (owner : Algorithm) (reference : Expr) (ctx : EvalCtx) :
    PubDisc (EvalBody.staticReferenceTerminal rec owner reference ctx) := by
  unfold EvalBody.staticReferenceTerminal; pub_tac

theorem EvalBody.transparentRetainedCell_pubDisc (rec : EvalRec) (hrec : ∀ c, PubDisc (rec c)) (hres : ResSusp rec) (reference : Expr) (ctx : EvalCtx) :
    PubDisc (EvalBody.transparentRetainedCell? rec reference ctx) := by
  unfold EvalBody.transparentRetainedCell? parameterNeedAddress?; pub_tac

theorem EvalBody.retainedCellSlice_pubDisc (rec : EvalRec) (hrec : ∀ c, PubDisc (rec c)) (hres : ResSusp rec) (fuel address : Nat) :
    PubDisc (EvalBody.retainedCellSlice? rec fuel address) := by
  induction fuel generalizing address with
  | zero => unfold EvalBody.retainedCellSlice?; pub_tac
  | succ n ih => unfold EvalBody.retainedCellSlice?; pub_tac

theorem EvalBody.retainedSliceAt_pubDisc (rec : EvalRec) (hrec : ∀ c, PubDisc (rec c)) (hres : ResSusp rec) (address : Nat) :
    PubDisc (EvalBody.retainedSliceAt? rec address) := by
  have := EvalBody.retainedCellSlice_pubDisc rec hrec hres
  unfold EvalBody.retainedSliceAt?; pub_tac

theorem EvalBody.writtenCollectorSlice_pubDisc (rec : EvalRec) (hrec : ∀ c, PubDisc (rec c)) (hres : ResSusp rec) (receiver : Expr) (ctx : EvalCtx) :
    PubDisc (EvalBody.writtenCollectorSlice? rec receiver ctx) := by
  unfold EvalBody.writtenCollectorSlice? parameterNeedAddress?; pub_tac

theorem retainedCollectorBuiltin_pubDisc (rec : EvalRec) (hrec : ∀ c, PubDisc (rec c)) (hres : ResSusp rec) (b : Builtin)
    (metadata : SequenceBuiltinMetadata) (suffixArgs : List PreparedSequenceBuiltinSuffixArg) (slice : List Nat) :
    PubDisc (retainedCollectorBuiltin rec.demandNeedRecursive b metadata suffixArgs slice) := by
  unfold retainedCollectorBuiltin argumentViewBuiltin NeedDemand.materialize; pub_tac

set_option maxHeartbeats 2000000 in
theorem EvalBody.bindSequenceBuiltinArguments_pubDisc (rec : EvalRec) (hrec : ∀ c, PubDisc (rec c)) (hres : ResSusp rec) (b : Builtin) (metadata : SequenceBuiltinMetadata) (args : List ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) :
    PubDisc (EvalBody.bindSequenceBuiltinArguments rec b metadata args ctx env) := by
  unfold EvalBody.bindSequenceBuiltinArguments; pub_tac

theorem EvalBody.evalReduceCounted_pubDisc (rec : EvalRec) (hrec : ∀ c, PubDisc (rec c)) (hres : ResSusp rec) (collection : List CountedResult) (stepAlg : Algorithm) (initial : Result) (ctx : EvalCtx) (env : ValEnv) :
    PubDisc (EvalBody.evalReduceCounted rec collection stepAlg initial ctx env) := by
  unfold EvalBody.evalReduceCounted; pub_tac

theorem EvalBody.evalFilterCounted_pubDisc (rec : EvalRec) (hrec : ∀ c, PubDisc (rec c)) (hres : ResSusp rec) (items : List CountedResult) (predicateAlg : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    PubDisc (EvalBody.evalFilterCounted rec items predicateAlg ctx env) := by
  unfold EvalBody.evalFilterCounted; pub_tac

theorem EvalBody.evalMapCounted_pubDisc (rec : EvalRec) (hrec : ∀ c, PubDisc (rec c)) (hres : ResSusp rec) (collection : List CountedResult) (transformAlg : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    PubDisc (EvalBody.evalMapCounted rec collection transformAlg ctx env) := by
  unfold EvalBody.evalMapCounted; pub_tac

theorem EvalBody.applyBuiltinCountedSequence_pubDisc (rec : EvalRec) (hrec : ∀ c, PubDisc (rec c)) (hres : ResSusp rec) (b : Builtin) (metadata : SequenceBuiltinMetadata) (args : List ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) :
    PubDisc (EvalBody.applyBuiltinCountedSequence rec b metadata args ctx env) := by
  unfold EvalBody.applyBuiltinCountedSequence; pub_tac

-- META-S3-3 enlarged this body (the builtin META binding branch); the same tactic needs more time.
set_option maxHeartbeats 1600000 in
theorem EvalBody.applyBuiltinCounted_pubDisc (rec : EvalRec) (hrec : ∀ c, PubDisc (rec c)) (hres : ResSusp rec) (b : Builtin) (args : List ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) :
    PubDisc (EvalBody.applyBuiltinCounted rec b args ctx env) := by
  unfold EvalBody.applyBuiltinCounted; pub_tac

theorem EvalBody.applyBuiltin_pubDisc (rec : EvalRec) (hrec : ∀ c, PubDisc (rec c)) (hres : ResSusp rec) (b : Builtin) (args : List ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) :
    PubDisc (EvalBody.applyBuiltin rec b args ctx env) := by
  unfold EvalBody.applyBuiltin; pub_tac

theorem EvalBody.applyBuiltinCountedResolved_pubDisc (rec : EvalRec) (hrec : ∀ c, PubDisc (rec c)) (hres : ResSusp rec) (b : Builtin) (args : List ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) :
    PubDisc (EvalBody.applyBuiltinCountedResolved rec b args ctx env) := by
  unfold EvalBody.applyBuiltinCountedResolved; pub_tac

theorem EvalBody.evalExplicitSequenceValueItems_pubDisc (rec : EvalRec) (hrec : ∀ c, PubDisc (rec c)) (hres : ResSusp rec) (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    PubDisc (EvalBody.evalExplicitSequenceValueItems rec a ctx env) := by
  unfold EvalBody.evalExplicitSequenceValueItems; pub_tac

theorem EvalBody.evalExplicitSequenceValueRowSlots_pubDisc (rec : EvalRec) (hrec : ∀ c, PubDisc (rec c)) (hres : ResSusp rec) (rows : OutputBundle) (rowCtx : EvalCtx) (env : ValEnv) :
    PubDisc (EvalBody.evalExplicitSequenceValueRowSlots rec rows rowCtx env) := by
  unfold EvalBody.evalExplicitSequenceValueRowSlots; pub_tac

theorem EvalBody.evalExplicitSequenceValueExprSlots_pubDisc (rec : EvalRec) (hrec : ∀ c, PubDisc (rec c)) (hres : ResSusp rec) (expr : Expr) (ctx : EvalCtx) (env : ValEnv) :
    PubDisc (EvalBody.evalExplicitSequenceValueExprSlots rec expr ctx env) := by
  unfold EvalBody.evalExplicitSequenceValueExprSlots; pub_tac

theorem EvalBody.evalUserCallCounted_pubDisc (rec : EvalRec) (hrec : ∀ c, PubDisc (rec c)) (hres : ResSusp rec) (callee : Algorithm) (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) :
    PubDisc (EvalBody.evalUserCallCounted rec callee args ctx env) := by
  unfold EvalBody.evalUserCallCounted; pub_tac

theorem EvalBody.evalConditionalCallCounted_pubDisc (rec : EvalRec) (hrec : ∀ c, PubDisc (rec c)) (hres : ResSusp rec) (callee : Algorithm) (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) (calleeName : String) :
    PubDisc (EvalBody.evalConditionalCallCounted rec callee args ctx env calleeName) := by
  unfold EvalBody.evalConditionalCallCounted; pub_tac

theorem EvalBody.evalResolvedCall_pubDisc (rec : EvalRec) (hrec : ∀ c, PubDisc (rec c)) (hres : ResSusp rec) (callee : Algorithm) (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) (calleeName : String) :
    PubDisc (EvalBody.evalResolvedCall rec callee args ctx env calleeName) := by
  unfold EvalBody.evalResolvedCall; pub_tac

theorem EvalBody.evalResolvedCallCounted_pubDisc (rec : EvalRec) (hrec : ∀ c, PubDisc (rec c)) (hres : ResSusp rec) (callee : Algorithm) (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) (calleeName : String) (origin : CalleeOrigin) :
    PubDisc (EvalBody.evalResolvedCallCounted rec callee args ctx env calleeName origin) := by
  unfold EvalBody.evalResolvedCallCounted; pub_tac

theorem EvalBody.evalCallCountedExpr_pubDisc (rec : EvalRec) (hrec : ∀ c, PubDisc (rec c)) (hres : ResSusp rec) (f : Expr) (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) :
    PubDisc (EvalBody.evalCallCountedExpr rec f args ctx env) := by
  unfold EvalBody.evalCallCountedExpr; pub_tac

theorem EvalBody.callLexicalWithReceiverCounted_pubDisc (rec : EvalRec) (hrec : ∀ c, PubDisc (rec c)) (hres : ResSusp rec) (name : Ident) (receiver : Expr) (fallback : Expr) (extraArgs : Option OutputBundle) (ctx : EvalCtx) (env : ValEnv) :
    PubDisc (EvalBody.callLexicalWithReceiverCounted rec name receiver fallback extraArgs ctx env) := by
  unfold EvalBody.callLexicalWithReceiverCounted; pub_tac

theorem EvalBody.rejectDotStringIntrinsicArguments_pubDisc (rec : EvalRec) (hrec : ∀ c, PubDisc (rec c)) (hres : ResSusp rec) (argsOpt : Option OutputBundle) (ctx : EvalCtx) (env : ValEnv) :
    PubDisc (EvalBody.rejectDotStringIntrinsicArguments rec argsOpt ctx env) := by
  unfold EvalBody.rejectDotStringIntrinsicArguments; pub_tac

theorem EvalBody.evalDotStringReceiverValue_pubDisc (rec : EvalRec) (hrec : ∀ c, PubDisc (rec c)) (hres : ResSusp rec) (target : Expr) (targetAlg : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    PubDisc (EvalBody.evalDotStringReceiverValue rec target targetAlg ctx env) := by
  unfold EvalBody.evalDotStringReceiverValue; pub_tac

set_option maxHeartbeats 4000000 in
theorem EvalBody.evalDotCallCounted_pubDisc (rec : EvalRec) (hrec : ∀ c, PubDisc (rec c)) (hres : ResSusp rec) (target : Expr) (name : Ident) (fallback : Expr) (argsOpt : Option OutputBundle) (ctx : EvalCtx) (env : ValEnv) :
    PubDisc (EvalBody.evalDotCallCounted rec target name fallback argsOpt ctx env) := by
  unfold EvalBody.evalDotCallCounted; pub_tac

theorem EvalBody.rejectInvokeIntrinsicArguments_pubDisc (rec : EvalRec) (hrec : ∀ c, PubDisc (rec c)) (hres : ResSusp rec) (argsOpt : Option OutputBundle) (ctx : EvalCtx) (env : ValEnv) :
    PubDisc (EvalBody.rejectInvokeIntrinsicArguments rec argsOpt ctx env) := by
  unfold EvalBody.rejectInvokeIntrinsicArguments; pub_tac

theorem EvalBody.invokeCallReferenceValue_pubDisc (rec : EvalRec) (hrec : ∀ c, PubDisc (rec c)) (hres : ResSusp rec) (val : Result) :
    PubDisc (EvalBody.invokeCallReferenceValue rec val) := by
  unfold EvalBody.invokeCallReferenceValue; pub_tac

theorem EvalBody.argumentViewCells_pubDisc (rec : EvalRec) (hrec : ∀ c, PubDisc (rec c)) (hres : ResSusp rec) (a : Nat) :
    PubDisc (EvalBody.argumentViewCells rec a) := by
  unfold EvalBody.argumentViewCells; pub_tac

theorem EvalBody.evalArgumentViewBuiltin_pubDisc (rec : EvalRec) (hrec : ∀ c, PubDisc (rec c)) (hres : ResSusp rec) (b : Builtin) (a : Nat) :
    PubDisc (EvalBody.evalArgumentViewBuiltin rec b a) := by
  unfold EvalBody.evalArgumentViewBuiltin; pub_tac

theorem EvalBody.evalSequenceSpreadOperandValue_pubDisc (rec : EvalRec) (hrec : ∀ c, PubDisc (rec c)) (hres : ResSusp rec) (e : Expr) (ctx : EvalCtx) (env : ValEnv) :
    PubDisc (EvalBody.evalSequenceSpreadOperandValue rec e ctx env) := by
  unfold EvalBody.evalSequenceSpreadOperandValue; pub_tac

theorem EvalBody.evalSequenceSpreadCounted_pubDisc (rec : EvalRec) (hrec : ∀ c, PubDisc (rec c)) (hres : ResSusp rec) (e : Expr) (ctx : EvalCtx) (env : ValEnv) :
    PubDisc (EvalBody.evalSequenceSpreadCounted rec e ctx env) := by
  unfold EvalBody.evalSequenceSpreadCounted; pub_tac

theorem EvalBody.transparentCollectorSlice_pubDisc (rec : EvalRec) (hrec : ∀ c, PubDisc (rec c)) (hres : ResSusp rec) (e : Expr) (ctx : EvalCtx) :
    PubDisc (EvalBody.transparentCollectorSlice? rec e ctx) := by
  unfold EvalBody.transparentCollectorSlice?; pub_tac

theorem EvalBody.evalSupplySpread_pubDisc (rec : EvalRec) (hrec : ∀ c, PubDisc (rec c)) (hres : ResSusp rec) (e : Expr) (ctx : EvalCtx) (env : ValEnv) :
    PubDisc (EvalBody.evalSupplySpread rec e ctx env) := by
  unfold EvalBody.evalSupplySpread; pub_tac

theorem EvalBody.evalListLiteralCounted_pubDisc (rec : EvalRec) (hrec : ∀ c, PubDisc (rec c)) (hres : ResSusp rec) (elements : List Expr) (ctx : EvalCtx) (env : ValEnv) :
    PubDisc (EvalBody.evalListLiteralCounted rec elements ctx env) := by
  unfold EvalBody.evalListLiteralCounted; pub_tac

theorem EvalBody.evalSequenceConstructCounted_pubDisc (rec : EvalRec) (hrec : ∀ c, PubDisc (rec c)) (hres : ResSusp rec) (e : Expr) (ctx : EvalCtx) (env : ValEnv) :
    PubDisc (EvalBody.evalSequenceConstructCounted rec e ctx env) := by
  unfold EvalBody.evalSequenceConstructCounted; pub_tac

theorem EvalBody.evalUnaryCounted_pubDisc (rec : EvalRec) (hrec : ∀ c, PubDisc (rec c)) (hres : ResSusp rec) (op : UnaryOp) (operand : Expr) (ctx : EvalCtx) (env : ValEnv) :
    PubDisc (EvalBody.evalUnaryCounted rec op operand ctx env) := by
  unfold EvalBody.evalUnaryCounted; pub_tac

theorem EvalBody.evalBinaryCounted_pubDisc (rec : EvalRec) (hrec : ∀ c, PubDisc (rec c)) (hres : ResSusp rec) (op : BinaryOp) (a b : Expr) (ctx : EvalCtx) (env : ValEnv) :
    PubDisc (EvalBody.evalBinaryCounted rec op a b ctx env) := by
  unfold EvalBody.evalBinaryCounted; pub_tac

theorem EvalBody.evalComparisonCounted_pubDisc (rec : EvalRec) (hrec : ∀ c, PubDisc (rec c)) (hres : ResSusp rec) (first : Expr) (links : List ComparisonLink) (ctx : EvalCtx) (env : ValEnv) :
    PubDisc (EvalBody.evalComparisonCounted rec first links ctx env) := by
  unfold EvalBody.evalComparisonCounted; pub_tac

theorem EvalBody.evalComparisonLinksCounted_pubDisc (rec : EvalRec) (hrec : ∀ c, PubDisc (rec c)) (hres : ResSusp rec) (previousExpr : Expr) (previous : Result) (holds : Bool) (links : List ComparisonLink) (ctx : EvalCtx) (env : ValEnv) :
    PubDisc (EvalBody.evalComparisonLinksCounted rec previousExpr previous holds links ctx env) := by
  unfold EvalBody.evalComparisonLinksCounted; pub_tac

theorem EvalBody.evalCounted_pubDisc (rec : EvalRec) (hrec : ∀ c, PubDisc (rec c)) (hres : ResSusp rec) (e : Expr) (ctx : EvalCtx) (env : ValEnv) :
    PubDisc (EvalBody.evalCounted rec e ctx env) := by
  unfold EvalBody.evalCounted; pub_tac

theorem EvalBody.evalUserCall_pubDisc (rec : EvalRec) (hrec : ∀ c, PubDisc (rec c)) (hres : ResSusp rec) (callee : Algorithm) (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) :
    PubDisc (EvalBody.evalUserCall rec callee args ctx env) := by
  unfold EvalBody.evalUserCall; pub_tac

theorem EvalBody.evalConditionalCall_pubDisc (rec : EvalRec) (hrec : ∀ c, PubDisc (rec c)) (hres : ResSusp rec) (callee : Algorithm) (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) (calleeName : String) :
    PubDisc (EvalBody.evalConditionalCall rec callee args ctx env calleeName) := by
  unfold EvalBody.evalConditionalCall; pub_tac

theorem EvalBody.evalCallExpr_pubDisc (rec : EvalRec) (hrec : ∀ c, PubDisc (rec c)) (hres : ResSusp rec) (f : Expr) (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv) :
    PubDisc (EvalBody.evalCallExpr rec f args ctx env) := by
  unfold EvalBody.evalCallExpr; pub_tac

theorem EvalBody.evalDotCall_pubDisc (rec : EvalRec) (hrec : ∀ c, PubDisc (rec c)) (hres : ResSusp rec) (target : Expr) (name : Ident) (fallback : Expr) (argsOpt : Option OutputBundle) (ctx : EvalCtx) (env : ValEnv) :
    PubDisc (EvalBody.evalDotCall rec target name fallback argsOpt ctx env) := by
  unfold EvalBody.evalDotCall; pub_tac

theorem EvalBody.eval_pubDisc (rec : EvalRec) (hrec : ∀ c, PubDisc (rec c)) (hres : ResSusp rec) (e : Expr) (ctx : EvalCtx) (env : ValEnv) :
    PubDisc (EvalBody.eval rec e ctx env) := by
  unfold EvalBody.eval; pub_tac

theorem evalStep_pubDisc (rec : EvalRec) (hrec : ∀ c, PubDisc (rec c)) (hres : ResSusp rec) :
    ∀ c, PubDisc (evalStep rec c) := by
  intro c
  cases c with
  | whileLoop step ctx env stepName cells => exact EvalBody.whileLoop_pubDisc rec hrec hres step ctx env stepName cells
  | aliasStepIsRuntime step target ctx visited => exact EvalBody.aliasStepIsRuntime_pubDisc rec hrec hres step target ctx visited
  | aliasValue wired ctx env => exact EvalBody.aliasValue_pubDisc rec hrec hres wired ctx env
  | resolveAliasChase followCarriers projectRuntime a ctx visited last => exact EvalBody.resolveAliasChase_pubDisc rec hrec hres followCarriers projectRuntime a ctx visited last
  | resolveAliasStructure a ctx => exact EvalBody.resolveAliasStructure_pubDisc rec hrec hres a ctx
  | aliasOriginBinding? a ctx => exact EvalBody.aliasOriginBinding?_pubDisc rec hrec hres a ctx
  | resolveAliasTarget a ctx => exact EvalBody.resolveAliasTarget_pubDisc rec hrec hres a ctx
  | resolveAliasValueTarget a ctx => exact EvalBody.resolveAliasValueTarget_pubDisc rec hrec hres a ctx
  | lookupLexicalProperty a name ctx => exact EvalBody.lookupLexicalProperty_pubDisc rec hrec hres a name ctx
  | lookupLexicalValueProperty a name ctx => exact EvalBody.lookupLexicalValueProperty_pubDisc rec hrec hres a name ctx
  | lookupLexical a name ctx => exact EvalBody.lookupLexical_pubDisc rec hrec hres a name ctx
  | needPlanNormalizeCallee callee ctx => exact EvalBody.needPlanNormalizeCallee_pubDisc rec hrec hres callee ctx
  | resolveAlg e ctx => exact EvalBody.resolveAlg_pubDisc rec hrec hres e ctx
  | projectNeedCallable address => exact EvalBody.projectNeedCallable_pubDisc rec hrec hres address
  | projectNeedWrittenAt address source caller => exact EvalBody.projectNeedWrittenAt_pubDisc rec hrec hres address source caller
  | linkCallable address => exact EvalBody.linkCallable_pubDisc rec hrec hres address
  | projectParameterCallable x ctx => exact EvalBody.projectParameterCallable_pubDisc rec hrec hres x ctx
  | projectNeedWritten source caller => exact EvalBody.projectNeedWritten_pubDisc rec hrec hres source caller
  | projectNeedStructuralMember source ctx => exact EvalBody.projectNeedStructuralMember_pubDisc rec hrec hres source ctx
  | resolveCalleeAlg f ctx => exact EvalBody.resolveCalleeAlg_pubDisc rec hrec hres f ctx
  | expectPreparedSequenceBuiltinAlgorithmSuffixArg b descriptors args index => exact EvalBody.expectPreparedSequenceBuiltinAlgorithmSuffixArg_pubDisc rec hrec hres b descriptors args index
  | resolveDotReceiver? e ctx => exact EvalBody.resolveDotReceiver?_pubDisc rec hrec hres e ctx
  | resolveDotReceiver e ctx => exact EvalBody.resolveDotReceiver_pubDisc rec hrec hres e ctx
  | algorithmIntrinsicRoute receiver ctx => exact EvalBody.algorithmIntrinsicRoute_pubDisc rec hrec hres receiver ctx
  | demandNeedRecursive address => exact EvalBody.demandNeedRecursive_pubDisc rec hrec hres address
  | evalSuppliedAt address e ctx env => exact EvalBody.evalSuppliedAt_pubDisc rec hrec hres address e ctx env
  | linkValue address => exact EvalBody.linkValue_pubDisc rec hrec hres address
  | algorithmOfValue val argsOpt ctx env => exact EvalBody.algorithmOfValue_pubDisc rec hrec hres val argsOpt ctx env
  | capturedCallee callee => exact EvalBody.capturedCallee_pubDisc rec hrec hres callee
  | referenceReceiverValue target targetAlg ctx env => exact EvalBody.referenceReceiverValue_pubDisc rec hrec hres target targetAlg ctx env
  | algorithmCalleeOf receiver ctx env => exact EvalBody.algorithmCalleeOf_pubDisc rec hrec hres receiver ctx env
  | evalSuppliedCallCounted origin callee cells ctx env calleeName => exact EvalBody.evalSuppliedCallCounted_pubDisc rec hrec hres origin callee cells ctx env calleeName
  | evalNeedUserSupply callee cells ctx env => exact EvalBody.evalNeedUserSupply_pubDisc rec hrec hres callee cells ctx env
  | evalNeedFamilySupply callee cells ctx env calleeName => exact EvalBody.evalNeedFamilySupply_pubDisc rec hrec hres callee cells ctx env calleeName
  | invokeNeed arg => exact EvalBody.invokeNeed_pubDisc rec hrec hres arg
  | argumentNeed arg ctx env => exact EvalBody.argumentNeed_pubDisc rec hrec hres arg ctx env
  | runNeedStepSlots step ctx env cells stepName => exact EvalBody.runNeedStepSlots_pubDisc rec hrec hres step ctx env cells stepName
  | runNeedWhileRound step ctx env cells stepName => exact EvalBody.runNeedWhileRound_pubDisc rec hrec hres step ctx env cells stepName
  | evalAlgOutputCore a ctx env => exact EvalBody.evalAlgOutputCore_pubDisc rec hrec hres a ctx env
  | evalAlgOutput a ctx env => exact EvalBody.evalAlgOutput_pubDisc rec hrec hres a ctx env
  | evalProgramOutput a ctx env => exact EvalBody.evalProgramOutput_pubDisc rec hrec hres a ctx env
  | evalAlgOutputSlots a ctx env => exact EvalBody.evalAlgOutputSlots_pubDisc rec hrec hres a ctx env
  | formOutputRow ctx env e => exact EvalBody.formOutputRow_pubDisc rec hrec hres ctx env e
  | whileVerdictSlots a ctx env => exact EvalBody.whileVerdictSlots_pubDisc rec hrec hres a ctx env
  | evalSequenceCallbackCall callee item ctx env calleeName => exact EvalBody.evalSequenceCallbackCall_pubDisc rec hrec hres callee item ctx env calleeName
  | evalSequenceCallbackCallCounted callee item ctx env calleeName => exact EvalBody.evalSequenceCallbackCallCounted_pubDisc rec hrec hres callee item ctx env calleeName
  | evalAlgOutputPreparedCore a ctx env => exact EvalBody.evalAlgOutputPreparedCore_pubDisc rec hrec hres a ctx env
  | evalOutputRowsPreparedCore rows rowCtx env => exact EvalBody.evalOutputRowsPreparedCore_pubDisc rec hrec hres rows rowCtx env
  | evalCapturePreparedCore rows ctx env => exact EvalBody.evalCapturePreparedCore_pubDisc rec hrec hres rows ctx env
  | evalCaptureCountedCore rows ctx env => exact EvalBody.evalCaptureCountedCore_pubDisc rec hrec hres rows ctx env
  | evalCaptureValue rows ctx env => exact EvalBody.evalCaptureValue_pubDisc rec hrec hres rows ctx env
  | evalAlgOutputCountedCore a ctx env => exact EvalBody.evalAlgOutputCountedCore_pubDisc rec hrec hres a ctx env
  | evalAlgOutputCounted a ctx env => exact EvalBody.evalAlgOutputCounted_pubDisc rec hrec hres a ctx env
  | evalZeroArgumentDemandOutputCounted a ctx env => exact EvalBody.evalZeroArgumentDemandOutputCounted_pubDisc rec hrec hres a ctx env
  | evalZeroArgumentDemandOutput a ctx env => exact EvalBody.evalZeroArgumentDemandOutput_pubDisc rec hrec hres a ctx env
  | evalArgumentValueCounted arg ctx env => exact EvalBody.evalArgumentValueCounted_pubDisc rec hrec hres arg ctx env
  | evalArgumentValue arg ctx env => exact EvalBody.evalArgumentValue_pubDisc rec hrec hres arg ctx env
  | evalZeroArgPropertyAccessCounted accessKind owner binding resolvedAlgorithm ctx env request => exact EvalBody.evalZeroArgPropertyAccessCounted_pubDisc rec hrec hres accessKind owner binding resolvedAlgorithm ctx env request
  | evalZeroArgPropertyAccess accessKind owner binding resolvedAlgorithm ctx env => exact EvalBody.evalZeroArgPropertyAccess_pubDisc rec hrec hres accessKind owner binding resolvedAlgorithm ctx env
  | evalConditionalCallbackCallCounted callee args ctx env calleeName => exact EvalBody.evalConditionalCallbackCallCounted_pubDisc rec hrec hres callee args ctx env calleeName
  | evalUserCallbackCallCounted callee args ctx env => exact EvalBody.evalUserCallbackCallCounted_pubDisc rec hrec hres callee args ctx env
  | evalResolvedCallbackCallCounted callee args ctx env calleeName => exact EvalBody.evalResolvedCallbackCallCounted_pubDisc rec hrec hres callee args ctx env calleeName
  | evalResolvedCallbackCall callee args ctx env calleeName => exact EvalBody.evalResolvedCallbackCall_pubDisc rec hrec hres callee args ctx env calleeName
  | evalSequenceReduceStepCounted callee element accumulator ctx env calleeName => exact EvalBody.evalSequenceReduceStepCounted_pubDisc rec hrec hres callee element accumulator ctx env calleeName
  | demandSequenceBuiltinCallItemValue item ctx env => exact EvalBody.demandSequenceBuiltinCallItemValue_pubDisc rec hrec hres item ctx env
  | bindSequenceBuiltinArguments b metadata args ctx env => exact EvalBody.bindSequenceBuiltinArguments_pubDisc rec hrec hres b metadata args ctx env
  | evalReduceCounted collection stepAlg initial ctx env => exact EvalBody.evalReduceCounted_pubDisc rec hrec hres collection stepAlg initial ctx env
  | evalFilterCounted items predicateAlg ctx env => exact EvalBody.evalFilterCounted_pubDisc rec hrec hres items predicateAlg ctx env
  | evalMapCounted collection transformAlg ctx env => exact EvalBody.evalMapCounted_pubDisc rec hrec hres collection transformAlg ctx env
  | applyBuiltinCountedSequence b metadata args ctx env => exact EvalBody.applyBuiltinCountedSequence_pubDisc rec hrec hres b metadata args ctx env
  | applyBuiltinCounted b args ctx env => exact EvalBody.applyBuiltinCounted_pubDisc rec hrec hres b args ctx env
  | applyBuiltin b args ctx env => exact EvalBody.applyBuiltin_pubDisc rec hrec hres b args ctx env
  | applyBuiltinCountedResolved b args ctx env => exact EvalBody.applyBuiltinCountedResolved_pubDisc rec hrec hres b args ctx env
  | evalExplicitSequenceValueItems a ctx env => exact EvalBody.evalExplicitSequenceValueItems_pubDisc rec hrec hres a ctx env
  | evalExplicitSequenceValueRowSlots rows rowCtx env => exact EvalBody.evalExplicitSequenceValueRowSlots_pubDisc rec hrec hres rows rowCtx env
  | evalExplicitSequenceValueExprSlots expr ctx env => exact EvalBody.evalExplicitSequenceValueExprSlots_pubDisc rec hrec hres expr ctx env
  | evalUserCallCounted callee args ctx env => exact EvalBody.evalUserCallCounted_pubDisc rec hrec hres callee args ctx env
  | evalConditionalCallCounted callee args ctx env calleeName => exact EvalBody.evalConditionalCallCounted_pubDisc rec hrec hres callee args ctx env calleeName
  | evalResolvedCall callee args ctx env calleeName => exact EvalBody.evalResolvedCall_pubDisc rec hrec hres callee args ctx env calleeName
  | evalResolvedCallCounted callee args ctx env calleeName origin => exact EvalBody.evalResolvedCallCounted_pubDisc rec hrec hres callee args ctx env calleeName origin
  | evalCallCountedExpr f args ctx env => exact EvalBody.evalCallCountedExpr_pubDisc rec hrec hres f args ctx env
  | callLexicalWithReceiverCounted name receiver fallback extraArgs ctx env => exact EvalBody.callLexicalWithReceiverCounted_pubDisc rec hrec hres name receiver fallback extraArgs ctx env
  | rejectDotStringIntrinsicArguments argsOpt ctx env => exact EvalBody.rejectDotStringIntrinsicArguments_pubDisc rec hrec hres argsOpt ctx env
  | evalDotStringReceiverValue target targetAlg ctx env => exact EvalBody.evalDotStringReceiverValue_pubDisc rec hrec hres target targetAlg ctx env
  | evalDotCallCounted target name fallback argsOpt ctx env => exact EvalBody.evalDotCallCounted_pubDisc rec hrec hres target name fallback argsOpt ctx env
  | rejectInvokeIntrinsicArguments argsOpt ctx env => exact EvalBody.rejectInvokeIntrinsicArguments_pubDisc rec hrec hres argsOpt ctx env
  | invokeCallReferenceValue val => exact EvalBody.invokeCallReferenceValue_pubDisc rec hrec hres val
  | argumentViewCells a => exact EvalBody.argumentViewCells_pubDisc rec hrec hres a
  | evalArgumentViewBuiltin b a => exact EvalBody.evalArgumentViewBuiltin_pubDisc rec hrec hres b a
  | evalSequenceSpreadOperandValue e ctx env => exact EvalBody.evalSequenceSpreadOperandValue_pubDisc rec hrec hres e ctx env
  | evalSequenceSpreadCounted e ctx env => exact EvalBody.evalSequenceSpreadCounted_pubDisc rec hrec hres e ctx env
  | evalSupplySpread e ctx env => exact EvalBody.evalSupplySpread_pubDisc rec hrec hres e ctx env
  | evalListLiteralCounted elements ctx env => exact EvalBody.evalListLiteralCounted_pubDisc rec hrec hres elements ctx env
  | evalSequenceConstructCounted e ctx env => exact EvalBody.evalSequenceConstructCounted_pubDisc rec hrec hres e ctx env
  | evalUnaryCounted op operand ctx env => exact EvalBody.evalUnaryCounted_pubDisc rec hrec hres op operand ctx env
  | evalBinaryCounted op a b ctx env => exact EvalBody.evalBinaryCounted_pubDisc rec hrec hres op a b ctx env
  | evalComparisonCounted first links ctx env => exact EvalBody.evalComparisonCounted_pubDisc rec hrec hres first links ctx env
  | evalComparisonLinksCounted previousExpr previous holds links ctx env => exact EvalBody.evalComparisonLinksCounted_pubDisc rec hrec hres previousExpr previous holds links ctx env
  | evalCounted e ctx env => exact EvalBody.evalCounted_pubDisc rec hrec hres e ctx env
  | evalUserCall callee args ctx env => exact EvalBody.evalUserCall_pubDisc rec hrec hres callee args ctx env
  | evalConditionalCall callee args ctx env calleeName => exact EvalBody.evalConditionalCall_pubDisc rec hrec hres callee args ctx env calleeName
  | evalCallExpr f args ctx env => exact EvalBody.evalCallExpr_pubDisc rec hrec hres f args ctx env
  | evalDotCall target name fallback argsOpt ctx env => exact EvalBody.evalDotCall_pubDisc rec hrec hres target name fallback argsOpt ctx env
  | eval e ctx env => exact EvalBody.eval_pubDisc rec hrec hres e ctx env

/-! ## Normal heaps -/

/-- **A normal heap**: every completed CALLABLE identity it holds is structure-normal. -/
def NormalHeap (h : Array NeedCell) : Prop :=
  ∀ (a : Nat) (c : NeedCell) (g : Algorithm), h[a]? = some c →
    c.callable = .projected (.ok (some g)) → structureNormal g = true

theorem NormalHeap.empty : NormalHeap #[] := fun _ _ _ h => by simp at h

/-- On a normal heap, accounted for IS structure-normal. -/
theorem NormalHeap.accounted {h : Array NeedCell} (hn : NormalHeap h) {g : Algorithm}
    (hg : Accounted h g) : structureNormal g = true := by
  rcases hg with hg | ⟨b, c, hc, hp⟩
  · exact hg
  · exact hn b c g hc hp

/-- **The publication relation keeps a heap normal.** -/
theorem PubHeapKept.normal {h h' : Array NeedCell} (k : PubHeapKept h h') (hn : NormalHeap h) :
    NormalHeap h' := fun a c g hc hg => hn.accounted (k a c g hc hg)

/-- A publishing-disciplined computation keeps a normal heap normal, whatever its outcome. -/
theorem PubDisc.normal {α : Type} {m : EvalM α} (hm : PubDisc m) (s : EvalState)
    (hn : NormalHeap s.needs) : NormalHeap (m.runState s).2.needs := (hm s).normal hn

end KatLang.Publications
