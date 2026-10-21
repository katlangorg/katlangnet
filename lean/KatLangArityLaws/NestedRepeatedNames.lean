import KatLangArityLaws.CallableIdentityDomain
import KatLangArityLaws.CallReference

open KatLang KatLang.BinderTrace KatLang.RepeatedNameLaws

/-!
# Repeated names in nested and mixed heads (R4 / Q-66, S6a, October 2026)

S5 (`RepeatedNameLaws.lean`) proved Q-28's representative fold `retain` and connected it to the
production binder on FLAT levels of name patterns over supplied cells with a fixed observation.
This module lifts the connection to EVERY head the binder accepts — sequence, list and unpack
patterns at any depth, literals, fixed and collecting names, META captures — and supplies the
production instance of its stability premise.

THE OBSERVATION MODEL (`Model`). A run is described by what the binder can observe of each address:
its counted VALUE and CALLABLE outcome (`view`, `none` outside the stable domain), whether META
reifies it (`plan`), and the next fresh address (`size`). Allocation PUSHES: a fresh Ready child
of an opened item `v` is observed as `((v, valueCount v), none)` (Ready data has no identity), a
META adapter as `((callRef a, 1), none)`, a collector cell is unobserved. Earlier observations
never change (`one_shape`, `sources_shape`): the observation domain GROWS with the heap.

THE WALK (`walkOne` / `walkSources`, `walkHead`). The observation-level reading of one binder run,
pattern by pattern in written order, with the binder's own pure pieces (`nameStep` — proved to be
`NeedBinder.bindName` in S5 —, `matchPattern`, the kind views, `needLevelSources`, the cardinality
gate) and an occurrence LOG: every name occurrence `(name, address)` the run visits, in written
traversal order and at its depth, nested ones carrying their freshly allocated addresses. It is
`none` exactly when the run would demand an unobserved cell. It is not a second binder: its
erasure IS the production core's run (`one_model`, `sources_model`, `head_model`) for every
capability record meeting `ModelCaps`, outcome and state relation included, on success, non-match
and every error alike.

THE PRODUCTION INSTANCE (`ProdRel`, `shell_model_caps`). `ModelCaps` holds for the binder
capabilities of `NeedChannels.shell ev route demand written` — the total VALUE shell
`NeedDemand.step` and CALLABLE shell `NeedProjection.step` over ANY recursive drivers — with the
production allocator and META capability, over the state invariant `ProdRel`: every observed
address is a COMPLETED successful VALUE or a SUSPENDED Ready cell, and its CALLABLE is a published
successful outcome or an UNPROJECTED Ready cell (identityless). VALUE demand and CALLABLE projection
publish their memo; allocation appends; nothing else changes. The evaluator's binder call sites pass
exactly `NeedChannels.shell evalSuppliedAt ⟨…⟩ demandNeedRecursive projectNeedWrittenAt`
(`bindingChannels`): that wiring is a SOURCE fact of the `partial` call sites, the channel
behaviour on this domain is a kernel theorem.

THE LAWS (per repeated name `X`, its contributions = its logged occurrences, `occ X log`):
* `one_tracks`, `sources_tracks`: on success, `X` is bound to the representative `retain` keeps over its own
  contributions in written order (from its binding before the walk);
* `one_conflict`, `sources_conflict`: if `X`'s fold over its logged contributions fails, the run stopped AT that
  contribution (the last logged occurrence is `X`'s) with exactly the binder's verdict for that
  conflict — so the prefix includes the very contribution that fails, and at most one name fails;
* `head_provenance`: every contribution is a supplied cell or an address the
  walk allocated, observed with the counted value its allocation stored; earlier cells keep their
  observations;
* `head_defined`: the walk is defined on every head whose repeated names occur only as
  non-collecting names, over observed supplied cells — the validated-signature domain;
* consequences on that domain: representative provenance, callable retention, first-richest
  selection and observation-preserving permutation of a name's COMPLETED contributions
  (`head_*` theorems below), with `CallableTransOn` explicit in the generic permutation law.
  `production_head_walk_no_cross` discharges it from the initial observed identity domain
  `ModelNoCross`: no allocation adds a callable identity. This does not assert that every
  source-reachable supplied identity belongs to that domain.

NOT CLAIMED. Whole-head success is NOT repeated-name compatibility: literal, kind, cardinality,
missing-source and META checks are independent (`compatible_is_not_success`). Permutation is of
one name's completed contributions, never of source expressions, structural checks or effectful
inspections; two runs' fresh addresses are not equated (only observations). Failure ORDER stays
R3's schedule. Arbitrary suspended expression cells, recursive collector materialization and
failing or state-dependent channels are outside `ProdRel`.
-/

namespace KatLang.NestedRepeatedNames

/-! ## The observation model -/

/-- What the binder can observe of one address: its counted VALUE and CALLABLE outcome. -/
abbrev Obs := CountedResult × Option Algorithm

/-- The observation model of the need heap during one binder run. -/
structure Model where
  view : Nat → Option Obs
  plan : Nat → Bool
  size : Nat

/-- The observation of a META adapter of the supplied call at `a` (`NeedPlan.reference`). -/
def adapterObs (a : Nat) : Option Obs := some ((.callRef a, 1), none)

/-- The observation of a fresh Ready cell holding `v` (`allocateNeed (.ready v)`). -/
def readyObs (v : CountedResult) : Option Obs := some (v, none)

namespace Model

/-- Allocation of the next address with the given observation. -/
def push (M : Model) (o : Option Obs) : Model where
  view b := if b = M.size then o else M.view b
  plan b := if b = M.size then false else M.plan b
  size := M.size + 1

/-- The observation of an observed address (a default elsewhere, never consulted there). -/
def obs (M : Model) (a : Nat) : Obs := (M.view a).getD ((.sequenceValue [], 0), none)

def observed (M : Model) (a : Nat) : Bool := (M.view a).isSome

/-- Only allocated addresses are observed. -/
def WF (M : Model) : Prop := ∀ a, M.observed a = true → a < M.size

/-- `N` extends `M`: no address is lost and every observation is kept. -/
def Extends (M N : Model) : Prop :=
  M.size ≤ N.size ∧ ∀ a, a < M.size → N.view a = M.view a ∧ N.plan a = M.plan a

theorem extends_refl (M : Model) : Extends M M := ⟨Nat.le_refl _, fun _ _ => ⟨rfl, rfl⟩⟩

theorem extends_trans {M N P : Model} (h1 : Extends M N) (h2 : Extends N P) : Extends M P :=
  ⟨Nat.le_trans h1.1 h2.1, fun a ha =>
    ⟨(h2.2 a (Nat.lt_of_lt_of_le ha h1.1)).1.trans (h1.2 a ha).1,
     (h2.2 a (Nat.lt_of_lt_of_le ha h1.1)).2.trans (h1.2 a ha).2⟩⟩

theorem push_extends (M : Model) (o : Option Obs) : Extends M (M.push o) :=
  ⟨Nat.le_succ _, fun a ha => by simp [push, Nat.ne_of_lt ha]⟩

theorem push_wf (M : Model) (o : Option Obs) (hw : WF M) : WF (M.push o) := by
  intro a ha
  simp only [push, observed] at ha ⊢
  by_cases h : a = M.size
  · omega
  · simp only [h, ↓reduceIte] at ha
    have := hw a (by simpa [observed] using ha)
    omega

theorem push_view_new (M : Model) (o : Option Obs) : (M.push o).view M.size = o := by
  simp [push]

theorem observed_of_extends {M N : Model} (h : Extends M N) (hw : WF M) (a : Nat) (ha : M.observed a = true) :
    N.observed a = true ∧ N.obs a = M.obs a := by
  have hv := (h.2 a (hw a ha)).1
  refine ⟨?_, ?_⟩
  · simp only [observed] at ha ⊢; rw [hv]; exact ha
  · simp only [obs]; rw [hv]

end Model

/-! ## The walk -/

/-- One binder run's observation: its outcome, the model after it, and its occurrence log. -/
abbrev Outcome := Except Error (Option NeedEnv)
abbrev Log := List (Ident × Nat)
abbrev Walk := Outcome × Model × Log

/-- The demands one name occurrence makes are all observed: its own cell when the name is
    repeated, and the retained representative's when it is already bound. -/
def nameDefined (M : Model) (name : Ident) (address : Nat) (repeated : List Ident) (bound : NeedEnv) : Bool :=
  !repeated.contains name || (M.observed address &&
    match lookupAssoc name bound with
    | none => true
    | some p => M.observed p)

/-- The fresh Ready children of the opened items, in item order (`allocateNeed (.ready …)`). -/
def allocReady : Model → List Result → List Nat × Model
  | M, [] => ([], M)
  | M, item :: rest =>
    let r := allocReady (M.push (readyObs (item, Result.valueCount item))) rest
    (M.size :: r.1, r.2)

/-- Continue after one pattern: a binding continues with the rest (logs concatenated), a
    non-match or an error stops with its own log. -/
def andThen (w : Option Walk) (k : Model → NeedEnv → Option Walk) : Option Walk :=
  match w with
  | none => none
  | some (.ok (some next), M, log) => (k M next).map (fun r => (r.1, r.2.1, log ++ r.2.2))
  | some r => some r

/-- The cardinality gate of an opened level. -/
def gateWalk (ps : List NeedPattern) (cells : List Nat) (family : Bool) (M : Model)
    (accepted : Option Walk) : Option Walk :=
  if !needAcceptsCardinality ps cells.length then
    some (if family then .ok none else .error (Error.arityMismatch (needMinimumSuppliedSlots ps) cells.length), M, [])
  else accepted

mutual
  /-- The walk of one pattern against the cell at `address`. -/
  def walkOne (M : Model) : NeedPattern → Nat → List Ident → NeedEnv → Bool → Option Walk
    | .bind name _, address, repeated, bound, family =>
      if nameDefined M name address repeated bound then
        some (nameStep M.obs repeated family bound name address, M, [(name, address)])
      else none
    | .metaRef name, address, repeated, bound, family =>
      if M.plan address then
        if nameDefined (M.push (adapterObs address)) name M.size repeated bound then
          some (nameStep (M.push (adapterObs address)).obs repeated family bound name M.size,
            M.push (adapterObs address), [(name, M.size)])
        else none
      else some (.error (NeedPlan.metaBindingRefusal name), M, [])
    | .literal literal, address, _, bound, _ =>
      if M.observed address then
        some (.ok (if (matchPattern literal (M.obs address).1.1).isSome then some bound else none), M, [])
      else none
    | .sequence ps, address, repeated, bound, family =>
      if M.observed address then
        match Result.sequencePatternItems? (M.obs address).1.1 with
        | none => some (if family then .ok none
            else .error (structuralPatternKindMismatch (NeedPattern.sequence ps).toParameter (M.obs address).1.1), M, [])
        | some items =>
          gateWalk ps (allocReady M items).1 family (allocReady M items).2
            (walkSources (allocReady M items).2 ps (needLevelSources ps (allocReady M items).1) repeated bound family)
      else none
    | .list ps, address, repeated, bound, family =>
      if M.observed address then
        match Result.listPatternItems? (M.obs address).1.1 with
        | none => some (if family then .ok none
            else .error (structuralPatternKindMismatch (NeedPattern.list ps).toParameter (M.obs address).1.1), M, [])
        | some items =>
          gateWalk ps (allocReady M items).1 family (allocReady M items).2
            (walkSources (allocReady M items).2 ps (needLevelSources ps (allocReady M items).1) repeated bound family)
      else none
    | .unpack ps, address, repeated, bound, family =>
      if M.observed address then
        gateWalk ps (allocReady M (Result.spreadItems (M.obs address).1.1)).1 family
          (allocReady M (Result.spreadItems (M.obs address).1.1)).2
          (walkSources (allocReady M (Result.spreadItems (M.obs address).1.1)).2 ps
            (needLevelSources ps (allocReady M (Result.spreadItems (M.obs address).1.1)).1) repeated bound family)
      else none

  /-- The walk of one level's patterns over their sources, in written order. -/
  def walkSources (M : Model) : List NeedPattern → List (NeedSource Nat) → List Ident → NeedEnv → Bool →
      Option Walk
    | [], _, _, current, _ => some (.ok (some current), M, [])
    | pattern :: rest, sources, repeated, current, family =>
      match sources.headD .missing with
      | .missing => some (.error Error.badArity, M, [])
      | .cell address =>
        andThen (walkOne M pattern address repeated current family)
          (fun M2 next => walkSources M2 rest sources.tail repeated next family)
      | .collector _ =>
        andThen (walkOne (M.push none) pattern M.size repeated current family)
          (fun M2 next => walkSources M2 rest sources.tail repeated next family)
end

/-- The walk of a whole head (`NeedBinder.bindPatterns`). -/
def walkHead (M : Model) (ps : List NeedPattern) (cells : List Nat) (family : Bool) : Option Walk :=
  gateWalk ps cells family M (walkSources M ps (needLevelSources ps cells) (needRepeatedNames ps) [] family)

/-! ## The capabilities a model describes -/

/-- A capability record DESCRIBED by the model along the state relation `Rel`: an observed
    address's VALUE and CALLABLE return its observation, allocation returns the model's next
    address and pushes the corresponding observation, META reifies exactly the `plan` addresses —
    each re-establishing the relation. -/
structure ModelCaps (k : NeedCapabilities EvalM) (Rel : Model → EvalState → Prop) : Prop where
  value : ∀ M s a, Rel M s → M.observed a = true →
    ∃ t, runEval (k.value a) s = (.ok (M.obs a).1, t) ∧ Rel M t
  callable : ∀ M s a, Rel M s → M.observed a = true →
    ∃ t, runEval (k.callable a) s = (.ok (M.obs a).2, t) ∧ Rel M t
  ready : ∀ M s v, Rel M s →
    ∃ t, runEval (k.allocate (.ready v)) s = (.ok M.size, t) ∧ Rel (M.push (readyObs v)) t
  collector : ∀ M s slice, Rel M s →
    ∃ t, runEval (k.allocate (.collector slice)) s = (.ok M.size, t) ∧ Rel (M.push none) t
  referenceOk : ∀ M s a, Rel M s → M.plan a = true →
    ∃ t, runEval (k.reference a) s = (.ok M.size, t) ∧ Rel (M.push (adapterObs a)) t
  referenceRefused : ∀ M s a, Rel M s → M.plan a = false →
    ∃ t, runEval (k.reference a) s = (.error NeedPlan.metaRefusal, t) ∧ Rel M t

section Correspondence

variable {k : NeedCapabilities EvalM} {Rel : Model → EvalState → Prop}

/-- ONE NAME OCCURRENCE: on observed demands, the production `bindName` is `nameStep` over the
    model's observations (S5's per-occurrence law, now over a growing model). -/
theorem name_model (hk : ModelCaps k Rel) (M : Model) (s : EvalState) (name : Ident) (address : Nat)
    (repeated : List Ident) (bound : NeedEnv) (family : Bool) (hs : Rel M s)
    (hd : nameDefined M name address repeated bound = true) :
    ∃ t, runEval (NeedBinder.bindName k name address repeated bound family) s
      = (nameStep M.obs repeated family bound name address, t) ∧ Rel M t := by
  by_cases hr : repeated.contains name = true
  · simp only [nameDefined, hr, Bool.not_true, Bool.false_or, Bool.and_eq_true] at hd
    obtain ⟨ha, hp⟩ := hd
    rw [repeated_name_binding k name address repeated bound family s hr]
    obtain ⟨t1, h1, i1⟩ := hk.value M s address hs ha
    simp only [h1]
    cases hl : lookupAssoc name bound with
    | none => exact ⟨t1, by simp only [nameStep, hr, hl, rebind, ↓reduceIte], i1⟩
    | some previous =>
      rw [hl] at hp
      obtain ⟨t2, h2, i2⟩ := hk.value M t1 previous i1 hp
      simp only [h2]
      by_cases hbv : (!((M.obs previous).1 == (M.obs address).1)) = true
      · exact ⟨t2, by simp only [nameStep, hr, hl, hbv, ↓reduceIte], i2⟩
      · obtain ⟨t3, h3, i3⟩ := hk.callable M t2 previous i2 hp
        obtain ⟨t4, h4, i4⟩ := hk.callable M t3 address i3 ha
        refine ⟨t4, ?_, i4⟩
        simp only [nameStep, hr, hl, hbv, h3, h4, ↓reduceIte, Bool.false_eq_true]
  · have hr' : repeated.contains name = false := by simpa using hr
    rw [BinderCore.core_plain_name_is_pure k name address repeated bound family hr']
    exact ⟨s, by simp only [runEval_pure, nameStep, hr', rebind, Bool.false_eq_true, ↓reduceIte], hs⟩

theorem ready_loop_model (hk : ModelCaps k Rel) : ∀ (items : List Result) (acc : List Nat) (M : Model) (s : EvalState),
    Rel M s → ∃ t,
      runEval (List.mapM.loop (fun item => k.allocate (.ready (item, Result.valueCount item))) items acc) s
        = (.ok (acc.reverse ++ (allocReady M items).1), t) ∧ Rel (allocReady M items).2 t
  | [], acc, M, s, hs => ⟨s, by simp [List.mapM.loop, allocReady], hs⟩
  | item :: rest, acc, M, s, hs => by
    obtain ⟨t1, h1, i1⟩ := hk.ready M s (item, Result.valueCount item) hs
    obtain ⟨t, h, i⟩ := ready_loop_model hk rest (M.size :: acc) _ t1 i1
    refine ⟨t, ?_, i⟩
    simp only [List.mapM.loop, runEval_bind, h1, thenRun_ok]
    rw [h]
    simp [allocReady]

/-- FRESH READY CHILDREN: opening the items allocates exactly the model's next addresses and
    pushes each item's production counted value. -/
theorem ready_model (hk : ModelCaps k Rel) (items : List Result) (M : Model) (s : EvalState) (hs : Rel M s) :
    ∃ t, runEval (items.mapM (fun item => k.allocate (.ready (item, Result.valueCount item)))) s
        = (.ok (allocReady M items).1, t) ∧ Rel (allocReady M items).2 t := by
  obtain ⟨t, h, i⟩ := ready_loop_model hk items [] M s hs
  refine ⟨t, ?_, i⟩
  simp only [List.reverse_nil, List.nil_append] at h
  exact h

theorem gate_model (ps : List NeedPattern) (cells : List Nat) (family : Bool) (M : Model)
    (accepted : Option Walk) (w : Walk) (hw : gateWalk ps cells family M accepted = some w)
    (rest : EvalM (Option NeedEnv)) (s : EvalState) (hs : Rel M s)
    (hrest : needAcceptsCardinality ps cells.length = true → accepted = some w →
      ∃ t, runEval rest s = (w.1, t) ∧ Rel w.2.1 t) :
    ∃ t, runEval (NeedBinder.cardinalityGate ps cells.length family rest) s = (w.1, t) ∧ Rel w.2.1 t := by
  unfold gateWalk at hw
  unfold NeedBinder.cardinalityGate
  cases hacc : needAcceptsCardinality ps cells.length
  · simp only [hacc, Bool.not_false, ↓reduceIte, Option.some.injEq] at hw
    subst hw
    cases family <;> exact ⟨s, rfl, hs⟩
  · simp only [hacc, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hw ⊢
    exact hrest hacc hw

/-- One pattern of a level, then the rest: wherever the walk continues, the production `bindSources`
    over `p :: rest` follows it (its source already resolved to `address`). -/
theorem cons_model (p : NeedPattern) (rest : List NeedPattern) (sources : List (NeedSource Nat))
    (repeated : List Ident) (bound : NeedEnv) (family : Bool) (s t0 : EvalState) (address : Nat)
    (hsa : runEval (NeedBinder.sourceAddress k.allocate (sources.headD .missing)) s = (.ok address, t0))
    (w0 : Option Walk) (w : Walk)
    (hw : andThen w0 (fun M2 next => walkSources M2 rest sources.tail repeated next family) = some w)
    (hfirst : ∀ w1, w0 = some w1 →
      ∃ t, runEval (NeedBinder.bindOne k p address repeated bound family) t0 = (w1.1, t) ∧ Rel w1.2.1 t)
    (hrest : ∀ M2 next t w2, Rel M2 t → walkSources M2 rest sources.tail repeated next family = some w2 →
      ∃ t', runEval (NeedBinder.bindSources k rest sources.tail repeated next family) t = (w2.1, t') ∧ Rel w2.2.1 t') :
    ∃ t, runEval (NeedBinder.bindSources k (p :: rest) sources repeated bound family) s = (w.1, t) ∧ Rel w.2.1 t := by
  simp only [NeedBinder.bindSources, runEval_bind, hsa, thenRun_ok]
  unfold andThen at hw
  rcases w0 with _ | ⟨r, M2, log1⟩
  · cases hw
  · obtain ⟨t1, h1, i1⟩ := hfirst _ rfl
    rw [h1]
    rcases r with e | (_ | next)
    · simp only [Option.some.injEq] at hw; subst hw; exact ⟨t1, rfl, i1⟩
    · simp only [Option.some.injEq] at hw; subst hw; exact ⟨t1, rfl, i1⟩
    · simp only [Option.map_eq_some_iff] at hw
      obtain ⟨w2, hw2, rfl⟩ := hw
      obtain ⟨t', h', i'⟩ := hrest M2 next t1 w2 i1 hw2
      exact ⟨t', by simp only [thenRun_ok]; exact h', i'⟩
mutual
  /-- THE CORRESPONDENCE, one pattern: wherever the walk is defined, the production core's
      `bindOne` at `k` returns the walk's outcome, in a state related to the walk's model. -/
  theorem one_model (hk : ModelCaps k Rel) (p : NeedPattern) (address : Nat) (repeated : List Ident)
      (bound : NeedEnv) (family : Bool) (M : Model) (s : EvalState) (w : Walk) (hs : Rel M s)
      (hw : walkOne M p address repeated bound family = some w) :
      ∃ t, runEval (NeedBinder.bindOne k p address repeated bound family) s = (w.1, t) ∧ Rel w.2.1 t := by
    cases p with
    | bind name collecting =>
      simp only [walkOne] at hw
      split at hw
      · rename_i hd
        cases hw
        simp only [NeedBinder.bindOne]
        exact name_model hk M s name address repeated bound family hs hd
      · cases hw
    | metaRef name =>
      simp only [walkOne] at hw
      simp only [NeedBinder.bindOne, runEval_bind, runEval_captureMeta]
      cases hp : M.plan address
      · simp only [hp, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hw
        subst hw
        obtain ⟨t, h, i⟩ := hk.referenceRefused M s address hs hp
        exact ⟨t, by simp [h], i⟩
      · simp only [hp, ↓reduceIte] at hw
        split at hw
        · rename_i hd
          cases hw
          obtain ⟨t1, h1, i1⟩ := hk.referenceOk M s address hs hp
          simp only [h1, thenRun_ok]
          exact name_model hk _ t1 name M.size repeated bound family i1 hd
        · cases hw
    | literal literal =>
      simp only [walkOne] at hw
      split at hw
      · rename_i ho
        cases hw
        obtain ⟨t, h, i⟩ := hk.value M s address hs ho
        refine ⟨t, ?_, i⟩
        simp only [NeedBinder.bindOne, runEval_bind, h, thenRun_ok]
        rfl
      · cases hw
    | sequence ps =>
      simp only [walkOne] at hw
      split at hw
      · rename_i ho
        obtain ⟨t1, h1, i1⟩ := hk.value M s address hs ho
        simp only [NeedBinder.bindOne, runEval_bind, h1, thenRun_ok]
        cases hi : Result.sequencePatternItems? (M.obs address).1.1 with
        | none =>
          simp only [hi, Option.some.injEq] at hw
          subst hw
          cases family <;> exact ⟨t1, rfl, i1⟩
        | some items =>
          simp only [hi] at hw
          obtain ⟨t2, h2, i2⟩ := ready_model hk items M t1 i1
          simp only [runEval_bind, h2, thenRun_ok]
          exact gate_model ps _ family _ _ w hw _ t2 i2 (fun _ hacc =>
            sources_model hk ps _ repeated bound family _ t2 w i2 hacc)
      · cases hw
    | list ps =>
      simp only [walkOne] at hw
      split at hw
      · rename_i ho
        obtain ⟨t1, h1, i1⟩ := hk.value M s address hs ho
        simp only [NeedBinder.bindOne, runEval_bind, h1, thenRun_ok]
        cases hi : Result.listPatternItems? (M.obs address).1.1 with
        | none =>
          simp only [hi, Option.some.injEq] at hw
          subst hw
          cases family <;> exact ⟨t1, rfl, i1⟩
        | some items =>
          simp only [hi] at hw
          obtain ⟨t2, h2, i2⟩ := ready_model hk items M t1 i1
          simp only [runEval_bind, h2, thenRun_ok]
          exact gate_model ps _ family _ _ w hw _ t2 i2 (fun _ hacc =>
            sources_model hk ps _ repeated bound family _ t2 w i2 hacc)
      · cases hw
    | unpack ps =>
      simp only [walkOne] at hw
      split at hw
      · rename_i ho
        obtain ⟨t1, h1, i1⟩ := hk.value M s address hs ho
        simp only [NeedBinder.bindOne, runEval_bind, h1, thenRun_ok]
        obtain ⟨t2, h2, i2⟩ := ready_model hk (Result.spreadItems (M.obs address).1.1) M t1 i1
        simp only [h2, thenRun_ok]
        exact gate_model ps _ family _ _ w hw _ t2 i2 (fun _ hacc =>
          sources_model hk ps _ repeated bound family _ t2 w i2 hacc)
      · cases hw

  /-- THE CORRESPONDENCE, one level's patterns over their sources. -/
  theorem sources_model (hk : ModelCaps k Rel) (ps : List NeedPattern) (sources : List (NeedSource Nat))
      (repeated : List Ident) (bound : NeedEnv) (family : Bool) (M : Model) (s : EvalState) (w : Walk)
      (hs : Rel M s) (hw : walkSources M ps sources repeated bound family = some w) :
      ∃ t, runEval (NeedBinder.bindSources k ps sources repeated bound family) s = (w.1, t) ∧ Rel w.2.1 t := by
    cases ps with
    | nil =>
      simp only [walkSources, Option.some.injEq] at hw
      subst hw
      exact ⟨s, rfl, hs⟩
    | cons p rest =>
      simp only [walkSources] at hw
      cases hsrc : sources.headD .missing with
      | missing =>
        simp only [hsrc, Option.some.injEq] at hw
        subst hw
        exact ⟨s, by simp only [NeedBinder.bindSources, runEval_bind]; rw [hsrc]; rfl, hs⟩
      | cell a =>
        simp only [hsrc] at hw
        exact cons_model p rest sources repeated bound family s s a
          (by rw [hsrc]; rfl) _ w hw
          (fun w1 h1 => one_model hk p a repeated bound family M s w1 hs h1)
          (fun M2 next t w2 i2 h2 => sources_model hk rest sources.tail repeated next family M2 t w2 i2 h2)
      | collector slice =>
        simp only [hsrc] at hw
        obtain ⟨t0, h0, i0⟩ := hk.collector M s slice hs
        exact cons_model p rest sources repeated bound family s t0 M.size
          (by rw [hsrc]; exact h0) _ w hw
          (fun w1 h1 => one_model hk p M.size repeated bound family (M.push none) t0 w1 i0 h1)
          (fun M2 next t w2 i2 h2 => sources_model hk rest sources.tail repeated next family M2 t w2 i2 h2)
end

/-- THE CORRESPONDENCE, a whole head: wherever the walk is defined, the production core's
    `bindPatterns` (by definition `bindNeedPatterns` at the production channels) returns the
    walk's outcome. -/
theorem head_model (hk : ModelCaps k Rel) (ps : List NeedPattern) (cells : List Nat) (family : Bool)
    (M : Model) (s : EvalState) (w : Walk) (hs : Rel M s) (hw : walkHead M ps cells family = some w) :
    ∃ t, runEval (NeedBinder.bindPatterns k ps cells family) s = (w.1, t) ∧ Rel w.2.1 t := by
  unfold walkHead at hw
  simp only [NeedBinder.bindPatterns, NeedBinder.bindLevel]
  exact gate_model ps cells family M _ w hw _ s hs (fun _ hacc =>
    sources_model hk ps _ (needRepeatedNames ps) [] family M s w hs hacc)

end Correspondence

/-! ## The walk's laws: growth and provenance -/

/-- Every address `N` observes beyond `M` holds the counted value its allocation stored and no
    callable identity: a fresh Ready child `(v, valueCount v)` or a META adapter. A nested Ready
    cell never inherits a callable identity from the value it contains. -/
def FreshIdless (M N : Model) : Prop :=
  ∀ a o, N.view a = some o → M.size ≤ a → ∃ v, o = ((v, Result.valueCount v), none)

theorem freshIdless_refl (M : Model) (hw : M.WF) : FreshIdless M M := by
  intro a o h ha
  have := hw a (by simp [Model.observed, h])
  omega

theorem freshIdless_trans {M N P : Model} (h1 : FreshIdless M N) (h2 : FreshIdless N P)
    (hNP : Model.Extends N P) : FreshIdless M P := by
  intro a o h ha
  by_cases hlt : a < N.size
  · rw [(hNP.2 a hlt).1] at h; exact h1 a o h ha
  · exact h2 a o h (Nat.le_of_not_lt hlt)

theorem push_fresh (M : Model) (hw : M.WF) (v : Result) :
    FreshIdless M (M.push (some ((v, Result.valueCount v), none))) := by
  intro a o h ha
  simp only [Model.push] at h
  by_cases e : a = M.size
  · simp only [e, ↓reduceIte, Option.some.injEq] at h
    exact ⟨v, h.symm⟩
  · simp only [e, ↓reduceIte] at h
    have := hw a (by simp [Model.observed, h])
    omega

theorem push_none_fresh (M : Model) (hw : M.WF) : FreshIdless M (M.push none) := by
  intro a o h ha
  simp only [Model.push] at h
  by_cases e : a = M.size
  · simp [e] at h
  · simp only [e, ↓reduceIte] at h
    have := hw a (by simp [Model.observed, h])
    omega

theorem adapter_obs_eq (a : Nat) : adapterObs a = some ((.callRef a, Result.valueCount (.callRef a)), none) := rfl

theorem push_observed_new (M : Model) (o : Obs) : (M.push (some o)).observed M.size = true := by
  simp [Model.observed, Model.push]

/-- FRESH READY CHILDREN in the model: consecutive fresh addresses, each observed, the model only
    growing and every new observation identityless. -/
theorem allocReady_shape : ∀ (items : List Result) (M : Model), M.WF →
    Model.Extends M (allocReady M items).2 ∧ (allocReady M items).2.WF ∧ FreshIdless M (allocReady M items).2 ∧
    ∀ a ∈ (allocReady M items).1, M.size ≤ a ∧ (allocReady M items).2.observed a = true
  | [], M, hw => ⟨Model.extends_refl M, hw, freshIdless_refl M hw, by simp [allocReady]⟩
  | item :: rest, M, hw => by
    have hw1 := Model.push_wf M (readyObs (item, Result.valueCount item)) hw
    obtain ⟨e, w, f, c⟩ := allocReady_shape rest _ hw1
    refine ⟨Model.extends_trans (Model.push_extends _ _) e, w,
      freshIdless_trans (push_fresh M hw item) f e, ?_⟩
    intro a ha
    simp only [allocReady, List.mem_cons] at ha
    rcases ha with rfl | ha
    · exact ⟨Nat.le_refl _, (Model.observed_of_extends e hw1 _ (push_observed_new M _)).1⟩
    · have h1 := (c a ha).1
      simp only [Model.push] at h1
      exact ⟨by omega, (c a ha).2⟩

/-- A supplied `.cell` source of a level is one of the level's cells. -/
theorem cell_mem_level_sources (ps : List NeedPattern) (cells : List Nat) (a : Nat)
    (h : NeedSource.cell a ∈ needLevelSources ps cells) : a ∈ cells := by
  simp only [needLevelSources, List.mem_map, List.mem_range] at h
  obtain ⟨i, -, hi⟩ := h
  unfold needSourceAt at hi
  split at hi
  · cases hi
  · split at hi
    · rename_i cell hcell
      cases hi
      exact List.mem_of_getElem? hcell
    · cases hi

theorem head_cell_mem (sources : List (NeedSource Nat)) (a : Nat)
    (h : sources.headD .missing = .cell a) : NeedSource.cell a ∈ sources := by
  cases sources with
  | nil => simp at h
  | cons x xs => simp only [List.headD_cons] at h; subst h; exact List.mem_cons_self

/-- What a walk leaves: the model only grows and stays well formed, every fresh observation is
    identityless, every logged occurrence is at one of the pattern's own cells (`own`) or at an
    address the walk allocated, and every logged occurrence of a repeated name is observed. -/
def Shape (M : Model) (repeated : List Ident) (own : Nat → Prop) (w : Walk) : Prop :=
  Model.Extends M w.2.1 ∧ w.2.1.WF ∧ FreshIdless M w.2.1 ∧
  (∀ e ∈ w.2.2, own e.2 ∨ M.size ≤ e.2) ∧
  (∀ e ∈ w.2.2, repeated.contains e.1 = true → w.2.1.observed e.2 = true)

theorem shape_trivial (M : Model) (repeated : List Ident) (own : Nat → Prop) (r : Outcome) (hw : M.WF) :
    Shape M repeated own (r, M, []) :=
  ⟨Model.extends_refl M, hw, freshIdless_refl M hw, by simp, by simp⟩

theorem shape_mono {M : Model} {repeated : List Ident} {own own' : Nat → Prop} {w : Walk}
    (h : Shape M repeated own w) (ho : ∀ a, own a → own' a ∨ M.size ≤ a) : Shape M repeated own' w := by
  refine ⟨h.1, h.2.1, h.2.2.1, fun e he => ?_, h.2.2.2.2⟩
  rcases h.2.2.2.1 e he with h1 | h1
  · exact ho _ h1
  · exact Or.inr h1

/-- A walk preceded by growth from `M` to `M1` (an allocation): the shape relative to `M`. -/
theorem shape_after {M M1 : Model} {repeated : List Ident} {own : Nat → Prop} {w : Walk}
    (he : Model.Extends M M1) (hf : FreshIdless M M1) (h : Shape M1 repeated own w) :
    Shape M repeated (fun a => own a ∨ M1.size ≤ a) w := by
  refine ⟨Model.extends_trans he h.1, h.2.1, freshIdless_trans hf h.2.2.1 h.1, fun e hm => ?_, h.2.2.2.2⟩
  rcases h.2.2.2.1 e hm with h1 | h1
  · exact Or.inl (Or.inl h1)
  · exact Or.inl (Or.inr h1)

/-- The inversion of `andThen`: the first walk bound and the rest continued (logs concatenated),
    or the first walk is the whole result and did not bind. -/
theorem andThen_eq_some {w0 : Option Walk} {k : Model → NeedEnv → Option Walk} {r : Walk}
    (h : andThen w0 k = some r) :
    (∃ M2 next log1 r2, w0 = some (.ok (some next), M2, log1) ∧ k M2 next = some r2 ∧
      r = (r2.1, r2.2.1, log1 ++ r2.2.2)) ∨
    (w0 = some r ∧ ∀ next, r.1 ≠ .ok (some next)) := by
  unfold andThen at h
  rcases w0 with _ | ⟨o, M2, log1⟩
  · cases h
  · rcases o with e | (_ | next)
    · simp only [Option.some.injEq] at h; subst h; exact Or.inr ⟨rfl, by intro n hn; cases hn⟩
    · simp only [Option.some.injEq] at h; subst h; exact Or.inr ⟨rfl, by intro n hn; cases hn⟩
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨r2, h2, rfl⟩ := h
      exact Or.inl ⟨M2, next, log1, r2, rfl, h2, rfl⟩

mutual
  /-- GROWTH AND PROVENANCE, one pattern: every logged occurrence is the pattern's own cell or a
      fresh address of this walk. -/
  theorem one_shape (p : NeedPattern) (address : Nat) (repeated : List Ident) (bound : NeedEnv)
      (family : Bool) (M : Model) (w : Walk) (hw : M.WF)
      (h : walkOne M p address repeated bound family = some w) :
      Shape M repeated (· = address) w := by
    cases p with
    | bind name collecting =>
      simp only [walkOne] at h
      split at h
      · rename_i hd
        cases h
        refine ⟨Model.extends_refl M, hw, freshIdless_refl M hw, by simp, ?_⟩
        intro e he hr
        simp only [List.mem_singleton] at he
        subst he
        simp only [nameDefined, hr, Bool.not_true, Bool.false_or, Bool.and_eq_true] at hd
        exact hd.1
      · cases h
    | metaRef name =>
      simp only [walkOne] at h
      cases hp : M.plan address
      · simp only [hp, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at h
        subst h; exact shape_trivial M repeated _ _ hw
      · simp only [hp, ↓reduceIte] at h
        split at h
        · rename_i hd
          cases h
          have hw1 := Model.push_wf M (adapterObs address) hw
          refine ⟨Model.push_extends _ _, hw1, by rw [adapter_obs_eq]; exact push_fresh M hw _,
            by simp, ?_⟩
          intro e he hr
          simp only [List.mem_singleton] at he
          subst he
          simp only [nameDefined, hr, Bool.not_true, Bool.false_or, Bool.and_eq_true] at hd
          exact hd.1
        · cases h
    | literal literal =>
      simp only [walkOne] at h
      split at h
      · cases h; exact shape_trivial M repeated _ _ hw
      · cases h
    | sequence ps =>
      simp only [walkOne] at h
      split at h
      · split at h
        · simp only [Option.some.injEq] at h; subst h; exact shape_trivial M repeated _ _ hw
        · rename_i items _
          obtain ⟨e1, w1, f1, c1⟩ := allocReady_shape items M hw
          unfold gateWalk at h
          split at h
          · simp only [Option.some.injEq] at h; subst h
            exact ⟨e1, w1, f1, by simp, by simp⟩
          · have hs := sources_shape ps _ repeated bound family _ w w1 h
            refine shape_mono (shape_after e1 f1 hs) ?_
            intro a ha
            rcases ha with ha | ha
            · exact Or.inr (c1 a (cell_mem_level_sources ps _ a ha)).1
            · exact Or.inr (Nat.le_trans e1.1 ha)
      · cases h
    | list ps =>
      simp only [walkOne] at h
      split at h
      · split at h
        · simp only [Option.some.injEq] at h; subst h; exact shape_trivial M repeated _ _ hw
        · rename_i items _
          obtain ⟨e1, w1, f1, c1⟩ := allocReady_shape items M hw
          unfold gateWalk at h
          split at h
          · simp only [Option.some.injEq] at h; subst h
            exact ⟨e1, w1, f1, by simp, by simp⟩
          · have hs := sources_shape ps _ repeated bound family _ w w1 h
            refine shape_mono (shape_after e1 f1 hs) ?_
            intro a ha
            rcases ha with ha | ha
            · exact Or.inr (c1 a (cell_mem_level_sources ps _ a ha)).1
            · exact Or.inr (Nat.le_trans e1.1 ha)
      · cases h
    | unpack ps =>
      simp only [walkOne] at h
      split at h
      · obtain ⟨e1, w1, f1, c1⟩ := allocReady_shape (Result.spreadItems (M.obs address).1.1) M hw
        unfold gateWalk at h
        split at h
        · simp only [Option.some.injEq] at h; subst h
          exact ⟨e1, w1, f1, by simp, by simp⟩
        · have hs := sources_shape ps _ repeated bound family _ w w1 h
          refine shape_mono (shape_after e1 f1 hs) ?_
          intro a ha
          rcases ha with ha | ha
          · exact Or.inr (c1 a (cell_mem_level_sources ps _ a ha)).1
          · exact Or.inr (Nat.le_trans e1.1 ha)
      · cases h

  /-- GROWTH AND PROVENANCE, one level: every logged occurrence is a supplied `.cell` source of
      the level or a fresh address of this walk. -/
  theorem sources_shape (ps : List NeedPattern) (sources : List (NeedSource Nat)) (repeated : List Ident)
      (bound : NeedEnv) (family : Bool) (M : Model) (w : Walk) (hw : M.WF)
      (h : walkSources M ps sources repeated bound family = some w) :
      Shape M repeated (fun a => NeedSource.cell a ∈ sources) w := by
    cases ps with
    | nil =>
      simp only [walkSources, Option.some.injEq] at h
      subst h; exact shape_trivial M repeated _ _ hw
    | cons p rest =>
      simp only [walkSources] at h
      cases hsrc : sources.headD .missing with
      | missing =>
        simp only [hsrc, Option.some.injEq] at h
        subst h; exact shape_trivial M repeated _ _ hw
      | cell a =>
        simp only [hsrc] at h
        have hown : NeedSource.cell a ∈ sources := head_cell_mem sources a hsrc
        rcases andThen_eq_some h with ⟨M2, next, log1, r2, h1, h2, rfl⟩ | ⟨h1, -⟩
        · have s1 := one_shape p a repeated bound family M _ hw h1
          have s2 := sources_shape rest sources.tail repeated next family M2 r2 s1.2.1 h2
          refine ⟨Model.extends_trans s1.1 s2.1, s2.2.1, freshIdless_trans s1.2.2.1 s2.2.2.1 s2.1,
            ?_, ?_⟩
          · intro e he
            rcases List.mem_append.mp he with he | he
            · rcases s1.2.2.2.1 e he with h | h
              · exact Or.inl (h ▸ hown)
              · exact Or.inr h
            · rcases s2.2.2.2.1 e he with h | h
              · exact Or.inl (List.mem_of_mem_tail h)
              · exact Or.inr (Nat.le_trans s1.1.1 h)
          · intro e he hr
            rcases List.mem_append.mp he with he | he
            · exact (Model.observed_of_extends s2.1 s1.2.1 _ (s1.2.2.2.2 e he hr)).1
            · exact s2.2.2.2.2 e he hr
        · exact shape_mono (one_shape p a repeated bound family M w hw h1)
            (fun b hb => Or.inl (hb ▸ hown))
      | collector slice =>
        simp only [hsrc] at h
        have hw0 := Model.push_wf M none hw
        have e0 := Model.push_extends M none
        have f0 := push_none_fresh M hw
        rcases andThen_eq_some h with ⟨M2, next, log1, r2, h1, h2, rfl⟩ | ⟨h1, -⟩
        · have s1 := one_shape p M.size repeated bound family _ _ hw0 h1
          have s2 := sources_shape rest sources.tail repeated next family M2 r2 s1.2.1 h2
          refine ⟨Model.extends_trans e0 (Model.extends_trans s1.1 s2.1), s2.2.1,
            freshIdless_trans f0 (freshIdless_trans s1.2.2.1 s2.2.2.1 s2.1)
              (Model.extends_trans s1.1 s2.1), ?_, ?_⟩
          · intro e he
            rcases List.mem_append.mp he with he | he
            · rcases s1.2.2.2.1 e he with h | h
              · exact Or.inr (Nat.le_of_eq h.symm)
              · exact Or.inr (Nat.le_trans e0.1 h)
            · rcases s2.2.2.2.1 e he with h | h
              · exact Or.inl (List.mem_of_mem_tail h)
              · exact Or.inr (Nat.le_trans e0.1 (Nat.le_trans s1.1.1 h))
          · intro e he hr
            rcases List.mem_append.mp he with he | he
            · exact (Model.observed_of_extends s2.1 s1.2.1 _ (s1.2.2.2.2 e he hr)).1
            · exact s2.2.2.2.2 e he hr
        · have s1 := one_shape p M.size repeated bound family _ w hw0 h1
          refine ⟨Model.extends_trans e0 s1.1, s1.2.1, freshIdless_trans f0 s1.2.2.1 s1.1, ?_, s1.2.2.2.2⟩
          intro e he
          rcases s1.2.2.2.1 e he with h | h
          · exact Or.inr (Nat.le_of_eq h.symm)
          · exact Or.inr (Nat.le_trans e0.1 h)
end

/-! ## The walk's laws: each repeated name's fold -/

/-- What a walk did to one repeated name: from its binding `start` before the walk, over its
    logged contributions `as` in written order, it ended bound as `final` — the representative
    `retain` keeps (S5's `perName`); a refused fold is impossible on a successful walk. -/
def Tracks (O : Nat → Obs) (start : Option Nat) (as : List Nat) (final : Option Nat) : Prop :=
  match perName O start as with
  | none => final = none
  | some (.ok r) => final = some r.address
  | some (.error _) => False

/-- `O` agrees with every observation of `M`. -/
def Agrees (O : Nat → Obs) (M : Model) : Prop := ∀ a, M.observed a = true → O a = M.obs a

theorem agrees_of_extends {O : Nat → Obs} {M N : Model} (h : Agrees O N) (he : Model.Extends M N) (hw : M.WF) :
    Agrees O M := by
  intro a ha
  obtain ⟨h1, h2⟩ := Model.observed_of_extends he hw a ha
  rw [h a h1, h2]

theorem retain_append : ∀ (rep : Contribution) (xs ys : List Contribution),
    retain rep (xs ++ ys) = match retain rep xs with
      | .ok r => retain r ys
      | .error e => .error e
  | rep, [], ys => by simp [retain]
  | rep, x :: xs, ys => by
    simp only [List.cons_append, retain]
    cases retainStep rep x with
    | error e => rfl
    | ok next => exact retain_append next xs ys

theorem retain_contrib (O : Nat → Obs) (a : Nat) (as : List Nat) (r : Contribution)
    (h : retain (contrib O a) (as.map (contrib O)) = .ok r) : r = contrib O r.address := by
  have hm := retain_mem _ _ r h
  rw [← List.map_cons] at hm
  obtain ⟨x, -, rfl⟩ := List.mem_map.mp hm
  rfl

/-- A fold that tracked to `mid` continues from `mid`. -/
theorem perName_append (O : Nat → Obs) (start mid : Option Nat) (as bs : List Nat)
    (h : Tracks O start as mid) : perName O start (as ++ bs) = perName O mid bs := by
  unfold Tracks at h
  cases hp : perName O start as with
  | none =>
    rw [hp] at h; subst h
    cases start with
    | none => cases as with
      | nil => rfl
      | cons _ _ => simp [perName] at hp
    | some _ => simp [perName] at hp
  | some res =>
    rw [hp] at h
    rcases res with c | r
    · exact h.elim
    · subst h
      cases start with
      | none =>
        cases as with
        | nil => simp [perName] at hp
        | cons a as' =>
          simp only [perName, Option.some.injEq] at hp
          simp only [perName, List.cons_append, List.map_append, retain_append, hp]
          rw [← retain_contrib O a as' r hp]
      | some p =>
        simp only [perName, Option.some.injEq] at hp
        have hp' : retain (contrib O p) (as.map (contrib O)) = .ok r := hp
        simp only [perName, List.map_append, retain_append, hp']
        have := retain_contrib O p as r (by simpa using hp')
        rw [← this]

theorem tracks_append {O : Nat → Obs} {start mid final : Option Nat} {as bs : List Nat}
    (h1 : Tracks O start as mid) (h2 : Tracks O mid bs final) : Tracks O start (as ++ bs) final := by
  unfold Tracks at h2 ⊢
  rw [perName_append O start mid as bs h1]
  exact h2

theorem occ_append (X : Ident) (l1 l2 : Log) : occ X (l1 ++ l2) = occ X l1 ++ occ X l2 := by
  simp [occ, List.filter_append]

theorem occ_single_self (X : Ident) (a : Nat) : occ X [(X, a)] = [a] := by simp [occ]

theorem occ_single_other (X n : Ident) (a : Nat) (h : n ≠ X) : occ X [(n, a)] = [] := by
  simp [occ, h]

theorem tracks_nil (O : Nat → Obs) (start : Option Nat) : Tracks O start [] start := by
  cases start <;> simp [Tracks, perName, retain, contrib]

/-- The binding of every other name is unchanged by an occurrence. -/
theorem nameStep_other (O : Nat → Obs) (repeated : List Ident) (family : Bool) (bound next : NeedEnv)
    (n X : Ident) (a : Nat) (h : nameStep O repeated family bound n a = .ok (some next)) (hX : n ≠ X) :
    lookupAssoc X next = lookupAssoc X bound := by
  rcases nameStep_ok_cases O repeated family bound next n a h with rfl | rfl
  · rfl
  · simp [rebind, BinderCorrespondence.lookupAssoc_rebind, Ne.symm hX]

/-- ONE OCCURRENCE TRACKS: a binding occurrence advances its own name's fold by exactly its own
    contribution and leaves every other name's fold where it was. -/
theorem nameStep_tracks (O : Nat → Obs) (repeated : List Ident) (family : Bool) (bound next : NeedEnv)
    (n : Ident) (a : Nat) (h : nameStep O repeated family bound n a = .ok (some next))
    (X : Ident) (hX : repeated.contains X = true) :
    Tracks O (lookupAssoc X bound) (occ X [(n, a)]) (lookupAssoc X next) := by
  by_cases hnX : n = X
  · subst hnX
    rw [occ_single_self]
    cases hl : lookupAssoc n bound with
    | none =>
      rw [nameStep_rebinds O repeated family bound n a (Or.inr hl)] at h
      cases h
      simp [Tracks, perName, retain, contrib, rebind, BinderCorrespondence.lookupAssoc_rebind]
    | some p =>
      obtain ⟨r, hst, hln, -⟩ := nameStep_repeated_ok O repeated family bound next n a p hX hl h
      simp only [Tracks, perName, List.map_cons, List.map_nil, retain, hst, hln]
  · rw [occ_single_other X n a hnX, nameStep_other O repeated family bound next n X a h hnX]
    exact tracks_nil O _

/-- The binder's ordinary verdict for a refused repeated contribution of `name`: the family
    non-match, otherwise `badArity` under the repeated-parameter context (counted VALUE) or the
    callable-identity `typeMismatch` (NEED-04, Q-27). -/
def conflictOutcome (name : Ident) (c : Conflict) (family : Bool) : Outcome :=
  if family then .ok none
  else match c with
    | .value => .error (Error.withContext (repeatedParameterContext name) Error.badArity)
    | .callable => .error (Error.typeMismatch "Repeated bind equality requires the same callable identity")

/-- ONE OCCURRENCE CONFLICTS: if its own contribution refuses its name's fold, the occurrence is
    that name's, and the binder's verdict is exactly the conflict's. -/
theorem nameStep_conflict (O : Nat → Obs) (repeated : List Ident) (family : Bool) (bound : NeedEnv)
    (n : Ident) (a : Nat) (X : Ident) (hX : repeated.contains X = true) (c : Conflict)
    (h : perName O (lookupAssoc X bound) (occ X [(n, a)]) = some (.error c)) :
    n = X ∧ nameStep O repeated family bound n a = conflictOutcome X c family := by
  by_cases hnX : n = X
  · subst hnX
    refine ⟨rfl, ?_⟩
    rw [occ_single_self] at h
    cases hl : lookupAssoc n bound with
    | none => rw [hl] at h; simp [perName, retain] at h
    | some p =>
      rw [hl] at h
      simp only [perName, List.map_cons, List.map_nil, retain, Option.some.injEq] at h
      rcases nameStep_repeated_spec O repeated family bound n a p hX hl with
        ⟨hs, -⟩ | ⟨hs, -⟩ | ⟨hs, he⟩ | ⟨hs, he⟩ <;> rw [hs] at h
      · cases h
      · cases h
      · cases h; rw [he]; cases family <;> rfl
      · cases h; rw [he]; cases family <;> rfl
  · rw [occ_single_other X n a hnX] at h
    cases hl : lookupAssoc X bound <;> rw [hl] at h <;> simp [perName, retain] at h

theorem nameStep_congr (O1 O2 : Nat → Obs) (repeated : List Ident) (family : Bool) (bound : NeedEnv)
    (name : Ident) (address : Nat)
    (h : repeated.contains name = true → O1 address = O2 address ∧ ∀ p, lookupAssoc name bound = some p → O1 p = O2 p) :
    nameStep O1 repeated family bound name address = nameStep O2 repeated family bound name address := by
  by_cases hr : repeated.contains name = true
  · obtain ⟨h1, h2⟩ := h hr
    unfold nameStep
    simp only [hr, ↓reduceIte]
    cases hl : lookupAssoc name bound with
    | none => rfl
    | some p => simp only [h1, h2 p hl]
  · have hr' : repeated.contains name = false := by simpa using hr
    simp only [nameStep, hr', Bool.false_eq_true, ↓reduceIte]

/-- On defined demands, the walk's `nameStep` over the model is `nameStep` over any agreeing `O`. -/
theorem nameStep_model_eq (O : Nat → Obs) (M : Model) (hO : Agrees O M) (repeated : List Ident)
    (family : Bool) (bound : NeedEnv) (name : Ident) (address : Nat)
    (hd : nameDefined M name address repeated bound = true) :
    nameStep M.obs repeated family bound name address = nameStep O repeated family bound name address := by
  apply nameStep_congr
  intro hr
  simp only [nameDefined, hr, Bool.not_true, Bool.false_or, Bool.and_eq_true] at hd
  refine ⟨(hO address hd.1).symm, fun p hp => ?_⟩
  rw [hp] at hd
  exact (hO p hd.2).symm

theorem perName_nil_not_error (O : Nat → Obs) (start : Option Nat) (c : Conflict) :
    perName O start [] ≠ some (.error c) := by
  cases start <;> simp [perName, retain]

theorem walk_single_last (X : Ident) (a : Nat) : [(X, a)].getLast? = some (X, a) := rfl

mutual
  /-- TRAVERSAL CORRESPONDENCE PER NAME, one pattern: on a binding walk every repeated name ends
      bound to the representative its fold keeps over the occurrences the walk logged for it, in
      written order, from its binding before the pattern; every other occurrence leaves it alone. -/
  theorem one_tracks (O : Nat → Obs) (p : NeedPattern) (address : Nat) (repeated : List Ident)
      (bound env : NeedEnv) (family : Bool) (M M' : Model) (log : Log) (hw : M.WF)
      (h : walkOne M p address repeated bound family = some (.ok (some env), M', log)) (hO : Agrees O M')
      (X : Ident) (hX : repeated.contains X = true) :
      Tracks O (lookupAssoc X bound) (occ X log) (lookupAssoc X env) := by
    cases p with
    | bind name collecting =>
      simp only [walkOne] at h
      split at h
      · rename_i hd
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨hr, rfl, rfl⟩ := h
        rw [nameStep_model_eq O M hO repeated family bound name address hd] at hr
        exact nameStep_tracks O repeated family bound env name address hr X hX
      · cases h
    | metaRef name =>
      simp only [walkOne] at h
      cases hp : M.plan address
      · simp [hp] at h
      · simp only [hp, ↓reduceIte] at h
        split at h
        · rename_i hd
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨hr, rfl, rfl⟩ := h
          rw [nameStep_model_eq O _ hO repeated family bound name M.size hd] at hr
          exact nameStep_tracks O repeated family bound env name M.size hr X hX
        · cases h
    | literal literal =>
      simp only [walkOne] at h
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨hr, rfl, rfl⟩ := h
        split at hr
        · cases hr; simpa [occ] using tracks_nil O (lookupAssoc X bound)
        · cases hr
      · cases h
    | sequence ps =>
      simp only [walkOne] at h
      split at h
      · split at h
        · cases family <;> simp at h
        · rename_i items _
          unfold gateWalk at h
          split at h
          · cases family <;> simp at h
          · exact sources_tracks O ps _ repeated bound env family _ M' log (allocReady_shape items M hw).2.1 h hO X hX
      · cases h
    | list ps =>
      simp only [walkOne] at h
      split at h
      · split at h
        · cases family <;> simp at h
        · rename_i items _
          unfold gateWalk at h
          split at h
          · cases family <;> simp at h
          · exact sources_tracks O ps _ repeated bound env family _ M' log (allocReady_shape items M hw).2.1 h hO X hX
      · cases h
    | unpack ps =>
      simp only [walkOne] at h
      split at h
      · unfold gateWalk at h
        split at h
        · cases family <;> simp at h
        · exact sources_tracks O ps _ repeated bound env family _ M' log
            (allocReady_shape _ M hw).2.1 h hO X hX
      · cases h

  /-- TRAVERSAL CORRESPONDENCE PER NAME, one level (see `one_tracks`). -/
  theorem sources_tracks (O : Nat → Obs) (ps : List NeedPattern) (sources : List (NeedSource Nat))
      (repeated : List Ident) (bound env : NeedEnv) (family : Bool) (M M' : Model) (log : Log) (hw : M.WF)
      (h : walkSources M ps sources repeated bound family = some (.ok (some env), M', log)) (hO : Agrees O M')
      (X : Ident) (hX : repeated.contains X = true) :
      Tracks O (lookupAssoc X bound) (occ X log) (lookupAssoc X env) := by
    cases ps with
    | nil =>
      simp only [walkSources, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨h1, rfl, rfl⟩ := h
      cases h1
      simpa [occ] using tracks_nil O (lookupAssoc X bound)
    | cons p rest =>
      simp only [walkSources] at h
      cases hsrc : sources.headD .missing with
      | missing => rw [hsrc] at h; simp at h
      | cell a =>
        simp only [hsrc] at h
        rcases andThen_eq_some h with ⟨M2, next, log1, ⟨r2o, M3, log2⟩, h1, h2, hr⟩ | ⟨-, hne⟩
        · simp only [Prod.mk.injEq] at hr
          obtain ⟨rfl, rfl, rfl⟩ := hr
          have s1 := one_shape p a repeated bound family M _ hw h1
          have s2 := sources_shape rest sources.tail repeated next family M2 _ s1.2.1 h2
          have t1 := one_tracks O p a repeated bound next family M M2 log1 hw h1
            (agrees_of_extends hO s2.1 s1.2.1) X hX
          have t2 := sources_tracks O rest sources.tail repeated next env family M2 _ _ s1.2.1 h2 hO X hX
          rw [occ_append]; exact tracks_append t1 t2
        · exact absurd rfl (hne env)
      | collector slice =>
        simp only [hsrc] at h
        have hw0 := Model.push_wf M none hw
        rcases andThen_eq_some h with ⟨M2, next, log1, ⟨r2o, M3, log2⟩, h1, h2, hr⟩ | ⟨-, hne⟩
        · simp only [Prod.mk.injEq] at hr
          obtain ⟨rfl, rfl, rfl⟩ := hr
          have s1 := one_shape p M.size repeated bound family _ _ hw0 h1
          have s2 := sources_shape rest sources.tail repeated next family M2 _ s1.2.1 h2
          have t1 := one_tracks O p M.size repeated bound next family _ M2 log1 hw0 h1
            (agrees_of_extends hO s2.1 s1.2.1) X hX
          have t2 := sources_tracks O rest sources.tail repeated next env family M2 _ _ s1.2.1 h2 hO X hX
          rw [occ_append]; exact tracks_append t1 t2
        · exact absurd rfl (hne env)
end

mutual
  /-- THE FIRST CONFLICT, one pattern: if a repeated name's fold over the occurrences the walk
      logged for it is REFUSED, the walk stopped at exactly that contribution — its last logged
      occurrence is that name's — with exactly the binder's verdict for that conflict. The prefix
      therefore contains the very contribution that fails, and no later inspection ran. -/
  theorem one_conflict (O : Nat → Obs) (p : NeedPattern) (address : Nat) (repeated : List Ident)
      (bound : NeedEnv) (family : Bool) (M : Model) (w : Walk) (hw : M.WF)
      (h : walkOne M p address repeated bound family = some w) (hO : Agrees O w.2.1)
      (X : Ident) (hX : repeated.contains X = true) (c : Conflict)
      (hc : perName O (lookupAssoc X bound) (occ X w.2.2) = some (.error c)) :
      w.1 = conflictOutcome X c family ∧ ∃ a, w.2.2.getLast? = some (X, a) := by
    cases p with
    | bind name collecting =>
      simp only [walkOne] at h
      split at h
      · rename_i hd
        cases h
        obtain ⟨rfl, he⟩ := nameStep_conflict O repeated family bound name address X hX c hc
        exact ⟨(nameStep_model_eq O M hO repeated family bound name address hd).trans he, address, rfl⟩
      · cases h
    | metaRef name =>
      simp only [walkOne] at h
      cases hp : M.plan address
      · simp only [hp, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at h
        subst h; exact absurd hc (perName_nil_not_error O _ c)
      · simp only [hp, ↓reduceIte] at h
        split at h
        · rename_i hd
          cases h
          obtain ⟨rfl, he⟩ := nameStep_conflict O repeated family bound name M.size X hX c hc
          exact ⟨(nameStep_model_eq O _ hO repeated family bound name M.size hd).trans he, M.size, rfl⟩
        · cases h
    | literal literal =>
      simp only [walkOne] at h
      split at h
      · cases h; exact absurd hc (perName_nil_not_error O _ c)
      · cases h
    | sequence ps =>
      simp only [walkOne] at h
      split at h
      · split at h
        · simp only [Option.some.injEq] at h; subst h; exact absurd hc (perName_nil_not_error O _ c)
        · rename_i items _
          unfold gateWalk at h
          split at h
          · simp only [Option.some.injEq] at h; subst h; exact absurd hc (perName_nil_not_error O _ c)
          · exact sources_conflict O ps _ repeated bound family _ w (allocReady_shape items M hw).2.1 h hO X hX c hc
      · cases h
    | list ps =>
      simp only [walkOne] at h
      split at h
      · split at h
        · simp only [Option.some.injEq] at h; subst h; exact absurd hc (perName_nil_not_error O _ c)
        · rename_i items _
          unfold gateWalk at h
          split at h
          · simp only [Option.some.injEq] at h; subst h; exact absurd hc (perName_nil_not_error O _ c)
          · exact sources_conflict O ps _ repeated bound family _ w (allocReady_shape items M hw).2.1 h hO X hX c hc
      · cases h
    | unpack ps =>
      simp only [walkOne] at h
      split at h
      · unfold gateWalk at h
        split at h
        · simp only [Option.some.injEq] at h; subst h; exact absurd hc (perName_nil_not_error O _ c)
        · exact sources_conflict O ps _ repeated bound family _ w (allocReady_shape _ M hw).2.1 h hO X hX c hc
      · cases h

  /-- THE FIRST CONFLICT, one level (see `one_conflict`). -/
  theorem sources_conflict (O : Nat → Obs) (ps : List NeedPattern) (sources : List (NeedSource Nat))
      (repeated : List Ident) (bound : NeedEnv) (family : Bool) (M : Model) (w : Walk) (hw : M.WF)
      (h : walkSources M ps sources repeated bound family = some w) (hO : Agrees O w.2.1)
      (X : Ident) (hX : repeated.contains X = true) (c : Conflict)
      (hc : perName O (lookupAssoc X bound) (occ X w.2.2) = some (.error c)) :
      w.1 = conflictOutcome X c family ∧ ∃ a, w.2.2.getLast? = some (X, a) := by
    cases ps with
    | nil =>
      simp only [walkSources, Option.some.injEq] at h
      subst h; exact absurd hc (perName_nil_not_error O _ c)
    | cons p rest =>
      simp only [walkSources] at h
      cases hsrc : sources.headD .missing with
      | missing =>
        simp only [hsrc, Option.some.injEq] at h
        subst h; exact absurd hc (perName_nil_not_error O _ c)
      | cell a =>
        simp only [hsrc] at h
        rcases andThen_eq_some h with ⟨M2, next, log1, r2, h1, h2, rfl⟩ | ⟨h1, -⟩
        · have s1 := one_shape p a repeated bound family M _ hw h1
          have s2 := sources_shape rest sources.tail repeated next family M2 r2 s1.2.1 h2
          have t1 := one_tracks O p a repeated bound next family M M2 log1 hw h1
            (agrees_of_extends hO s2.1 s1.2.1) X hX
          simp only [occ_append, perName_append O _ _ _ _ t1] at hc
          obtain ⟨hr, b, hb⟩ := sources_conflict O rest sources.tail repeated next family M2 r2 s1.2.1 h2 hO X hX c hc
          exact ⟨hr, b, by simp [List.getLast?_append, hb]⟩
        · exact one_conflict O p a repeated bound family M w hw h1 hO X hX c hc
      | collector slice =>
        simp only [hsrc] at h
        have hw0 := Model.push_wf M none hw
        rcases andThen_eq_some h with ⟨M2, next, log1, r2, h1, h2, rfl⟩ | ⟨h1, -⟩
        · have s1 := one_shape p M.size repeated bound family _ _ hw0 h1
          have s2 := sources_shape rest sources.tail repeated next family M2 r2 s1.2.1 h2
          have t1 := one_tracks O p M.size repeated bound next family _ M2 log1 hw0 h1
            (agrees_of_extends hO s2.1 s1.2.1) X hX
          simp only [occ_append, perName_append O _ _ _ _ t1] at hc
          obtain ⟨hr, b, hb⟩ := sources_conflict O rest sources.tail repeated next family M2 r2 s1.2.1 h2 hO X hX c hc
          exact ⟨hr, b, by simp [List.getLast?_append, hb]⟩
        · exact one_conflict O p M.size repeated bound family _ w hw0 h1 hO X hX c hc
end

/-! ## The walk is defined on validated heads -/

mutual
  /-- THE VALIDATED-HEAD DOMAIN: every occurrence of a repeated name is a NON-COLLECTING name. A
      repeated collecting name is an invalid signature (X-02, `RepeatedNameIncludesCollecting`);
      literals, META captures (a repeated META binder is invalid too, but harmless here: its
      adapter is observed) and every structural kind are unrestricted. -/
  def RepeatedPlain (repeated : List Ident) : NeedPattern → Prop
    | .bind n collecting => repeated.contains n = true → collecting = false
    | .metaRef _ => True
    | .literal _ => True
    | .sequence ps => RepeatedPlainList repeated ps
    | .list ps => RepeatedPlainList repeated ps
    | .unpack ps => RepeatedPlainList repeated ps

  def RepeatedPlainList (repeated : List Ident) : List NeedPattern → Prop
    | [] => True
    | p :: ps => RepeatedPlain repeated p ∧ RepeatedPlainList repeated ps
end

/-- Whether a pattern demands its own cell: a repeated name, a literal and every structural
    pattern do; a non-repeated name and a META capture do not. -/
def needsCell (repeated : List Ident) : NeedPattern → Bool
  | .bind n _ => repeated.contains n
  | .metaRef _ => false
  | _ => true

/-- A level's sources FIT its patterns: every supplied cell a pattern demands is observed, and a
    collector source belongs to a collecting pattern. Plain names may transport ANY cell — an
    arbitrary suspended expression included. -/
def Fits (M : Model) (repeated : List Ident) (ps : List NeedPattern) (sources : List (NeedSource Nat)) : Prop :=
  ∀ (i : Nat) (p : NeedPattern), ps[i]? = some p →
    match (sources[i]? : Option (NeedSource Nat)) with
    | some (NeedSource.cell a) => needsCell repeated p = true → M.observed a = true
    | some (NeedSource.collector _) => p.isCollecting = true
    | _ => True

/-- The repeated names' current bindings are observed. -/
def BoundObs (M : Model) (repeated : List Ident) (bound : NeedEnv) : Prop :=
  ∀ X q, repeated.contains X = true → lookupAssoc X bound = some q → M.observed q = true

theorem fits_tail {M : Model} {repeated : List Ident} {p : NeedPattern} {rest : List NeedPattern}
    {sources : List (NeedSource Nat)} (h : Fits M repeated (p :: rest) sources) : Fits M repeated rest sources.tail := by
  intro i q hq
  have := h (i + 1) q (by simpa using hq)
  simpa [List.getElem?_tail] using this

theorem fits_head {M : Model} {repeated : List Ident} {p : NeedPattern} {rest : List NeedPattern}
    {sources : List (NeedSource Nat)} (h : Fits M repeated (p :: rest) sources) :
    (∀ a, sources.headD .missing = .cell a → needsCell repeated p = true → M.observed a = true) ∧
    (∀ sl, sources.headD .missing = .collector sl → p.isCollecting = true) := by
  have h0 := h 0 p rfl
  cases sources with
  | nil => exact ⟨by simp, by simp⟩
  | cons x xs =>
    simp only [List.getElem?_cons_zero] at h0
    refine ⟨fun a ha => ?_, fun sl hs => ?_⟩
    · simp only [List.headD_cons] at ha; subst ha; exact h0
    · simp only [List.headD_cons] at hs; subst hs; exact h0

theorem fits_mono {M N : Model} {repeated : List Ident} {ps : List NeedPattern} {sources : List (NeedSource Nat)}
    (h : Fits M repeated ps sources) (he : Model.Extends M N) (hw : M.WF) : Fits N repeated ps sources := by
  intro i p hp
  have := h i p hp
  split
  · rename_i a ha; rw [ha] at this
    exact fun hn => (Model.observed_of_extends he hw a (this hn)).1
  · rename_i sl hs; rw [hs] at this; exact this
  · trivial

theorem bound_obs_mono {M N : Model} {repeated : List Ident} {bound : NeedEnv}
    (h : BoundObs M repeated bound) (he : Model.Extends M N) (hw : M.WF) : BoundObs N repeated bound :=
  fun X q hX hq => (Model.observed_of_extends he hw q (h X q hX hq)).1

/-- An opened level whose cells are all observed fits any patterns. -/
theorem level_sources_fit (M : Model) (repeated : List Ident) (ps : List NeedPattern) (cells : List Nat)
    (hc : ∀ a ∈ cells, M.observed a = true) : Fits M repeated ps (needLevelSources ps cells) := by
  intro i p hp
  split
  · rename_i a ha
    exact fun _ => hc a (cell_mem_level_sources ps cells a (List.mem_of_getElem? ha))
  · rename_i sl hs
    have hi : i < ps.length := (List.getElem?_eq_some_iff.mp hp).1
    simp only [needLevelSources, List.getElem?_map, List.getElem?_range hi, Option.map_some,
      Option.some.injEq] at hs
    unfold needSourceAt at hs
    split at hs
    · rename_i hcol
      have hfind : ps.findIdx? NeedPattern.isCollecting = some i := by simpa using hcol
      obtain ⟨hlt, hcoll, -⟩ := List.findIdx?_eq_some_iff_getElem.mp hfind
      have : ps[i] = p := by simpa [List.getElem?_eq_getElem hlt] using hp
      rw [← this]; exact hcoll
    · split at hs <;> cases hs
  · trivial

/-- A name bound after a successful walk is bound to its earlier cell or to a logged occurrence. -/
theorem retain_address_mem (O : Nat → Obs) (a : Nat) (as : List Nat) (r : Contribution)
    (h : retain (contrib O a) (as.map (contrib O)) = .ok r) : r.address ∈ a :: as := by
  have hm := retain_mem _ _ r h
  rw [← List.map_cons] at hm
  obtain ⟨x, hx, hxr⟩ := List.mem_map.mp hm
  rw [← hxr]
  exact hx

theorem tracks_final_mem (O : Nat → Obs) (start : Option Nat) (as : List Nat) (q : Nat)
    (h : Tracks O start as (some q)) : start = some q ∨ q ∈ as := by
  unfold Tracks at h
  cases start with
  | none =>
    cases as with
    | nil => simp [perName] at h
    | cons a as' =>
      cases hr : retain (contrib O a) (as'.map (contrib O)) with
      | error e => simp [perName, hr] at h
      | ok r =>
        simp only [perName, hr, Option.some.injEq] at h
        exact Or.inr (by rw [h]; exact retain_address_mem O a as' r hr)
  | some p =>
    cases hr : retain (contrib O p) (as.map (contrib O)) with
    | error e => simp [perName, hr] at h
    | ok r =>
      simp only [perName, hr, Option.some.injEq] at h
      rcases List.mem_cons.mp (retain_address_mem O p as r hr) with h1 | h1
      · exact Or.inl (by rw [h, h1])
      · exact Or.inr (by rw [h]; exact h1)

theorem occ_mem (X : Ident) (log : Log) (q : Nat) (h : q ∈ occ X log) : (X, q) ∈ log := by
  simp only [occ, List.mem_map, List.mem_filter, beq_iff_eq] at h
  obtain ⟨⟨n, a⟩, ⟨hm, hn⟩, rfl⟩ := h
  simp only at hn; subst hn; exact hm

/-- After a successful walk the repeated names' bindings are observed. -/
theorem one_bound_obs (p : NeedPattern) (address : Nat) (repeated : List Ident) (bound env : NeedEnv)
    (family : Bool) (M M' : Model) (log : Log) (hw : M.WF)
    (h : walkOne M p address repeated bound family = some (.ok (some env), M', log))
    (hb : BoundObs M repeated bound) : BoundObs M' repeated env := by
  have s := one_shape p address repeated bound family M _ hw h
  intro X q hX hq
  have t := one_tracks M'.obs p address repeated bound env family M M' log hw h (fun _ _ => rfl) X hX
  rw [hq] at t
  rcases tracks_final_mem _ _ _ q t with h1 | h1
  · exact (Model.observed_of_extends s.1 hw q (hb X q hX h1)).1
  · exact s.2.2.2.2 (X, q) (occ_mem X log q h1) hX

theorem sources_bound_obs (ps : List NeedPattern) (sources : List (NeedSource Nat)) (repeated : List Ident)
    (bound env : NeedEnv) (family : Bool) (M M' : Model) (log : Log) (hw : M.WF)
    (h : walkSources M ps sources repeated bound family = some (.ok (some env), M', log))
    (hb : BoundObs M repeated bound) : BoundObs M' repeated env := by
  have s := sources_shape ps sources repeated bound family M _ hw h
  intro X q hX hq
  have t := sources_tracks M'.obs ps sources repeated bound env family M M' log hw h (fun _ _ => rfl) X hX
  rw [hq] at t
  rcases tracks_final_mem _ _ _ q t with h1 | h1
  · exact (Model.observed_of_extends s.1 hw q (hb X q hX h1)).1
  · exact s.2.2.2.2 (X, q) (occ_mem X log q h1) hX

theorem name_defined_of (M : Model) (name : Ident) (address : Nat) (repeated : List Ident) (bound : NeedEnv)
    (ha : repeated.contains name = true → M.observed address = true) (hb : BoundObs M repeated bound) :
    nameDefined M name address repeated bound = true := by
  unfold nameDefined
  cases hr : repeated.contains name
  · rfl
  · simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true]
    refine ⟨ha hr, ?_⟩
    cases hl : lookupAssoc name bound with
    | none => rfl
    | some q => exact hb name q hr hl

theorem andThen_defined {w0 : Option Walk} {k : Model → NeedEnv → Option Walk} (h0 : ∃ w, w0 = some w)
    (hk : ∀ M2 next log1, w0 = some (.ok (some next), M2, log1) → ∃ w, k M2 next = some w) :
    ∃ w, andThen w0 k = some w := by
  obtain ⟨⟨r, M2, log1⟩, rfl⟩ := h0
  unfold andThen
  rcases r with e | (_ | next)
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩
  · obtain ⟨w, hw⟩ := hk M2 next log1 rfl
    exact ⟨(w.1, w.2.1, log1 ++ w.2.2), by simp [hw]⟩

mutual
  /-- DEFINEDNESS, one pattern: on the validated domain, with its own cell observed when it is
      demanded and the repeated names' bindings observed, the walk is defined. -/
  theorem one_defined (p : NeedPattern) (address : Nat) (repeated : List Ident) (bound : NeedEnv)
      (family : Bool) (M : Model) (hw : M.WF) (hp : RepeatedPlain repeated p)
      (ha : needsCell repeated p = true → M.observed address = true) (hb : BoundObs M repeated bound) :
      ∃ w, walkOne M p address repeated bound family = some w := by
    cases p with
    | bind name collecting =>
      simp only [walkOne, name_defined_of M name address repeated bound (fun hr => ha hr) hb, ↓reduceIte]
      exact ⟨_, rfl⟩
    | metaRef name =>
      simp only [walkOne]
      cases hp' : M.plan address
      · exact ⟨_, rfl⟩
      · have hd := name_defined_of (M.push (adapterObs address)) name M.size repeated bound
          (fun _ => push_observed_new M _) (bound_obs_mono hb (Model.push_extends _ _) hw)
        simp only [↓reduceIte, hd]
        exact ⟨_, rfl⟩
    | literal literal =>
      simp only [walkOne, ha rfl, ↓reduceIte]
      exact ⟨_, rfl⟩
    | sequence ps =>
      simp only [walkOne, ha rfl, ↓reduceIte]
      split
      · exact ⟨_, rfl⟩
      · rename_i items _
        obtain ⟨e1, w1, -, c1⟩ := allocReady_shape items M hw
        unfold gateWalk
        split
        · exact ⟨_, rfl⟩
        · exact sources_defined ps _ repeated bound family _ w1 hp
            (level_sources_fit _ repeated ps _ (fun a h => (c1 a h).2)) (bound_obs_mono hb e1 hw)
    | list ps =>
      simp only [walkOne, ha rfl, ↓reduceIte]
      split
      · exact ⟨_, rfl⟩
      · rename_i items _
        obtain ⟨e1, w1, -, c1⟩ := allocReady_shape items M hw
        unfold gateWalk
        split
        · exact ⟨_, rfl⟩
        · exact sources_defined ps _ repeated bound family _ w1 hp
            (level_sources_fit _ repeated ps _ (fun a h => (c1 a h).2)) (bound_obs_mono hb e1 hw)
    | unpack ps =>
      simp only [walkOne, ha rfl, ↓reduceIte]
      obtain ⟨e1, w1, -, c1⟩ := allocReady_shape (Result.spreadItems (M.obs address).1.1) M hw
      unfold gateWalk
      split
      · exact ⟨_, rfl⟩
      · exact sources_defined ps _ repeated bound family _ w1 hp
          (level_sources_fit _ repeated ps _ (fun a h => (c1 a h).2)) (bound_obs_mono hb e1 hw)

  /-- DEFINEDNESS, one level. -/
  theorem sources_defined (ps : List NeedPattern) (sources : List (NeedSource Nat)) (repeated : List Ident)
      (bound : NeedEnv) (family : Bool) (M : Model) (hw : M.WF) (hp : RepeatedPlainList repeated ps)
      (hf : Fits M repeated ps sources) (hb : BoundObs M repeated bound) :
      ∃ w, walkSources M ps sources repeated bound family = some w := by
    cases ps with
    | nil => exact ⟨_, rfl⟩
    | cons p rest =>
      obtain ⟨hp1, hp2⟩ := hp
      obtain ⟨hcell, hcol⟩ := fits_head hf
      have hft := fits_tail hf
      simp only [walkSources]
      cases hsrc : sources.headD .missing with
      | missing => exact ⟨_, rfl⟩
      | cell a =>
        refine andThen_defined (one_defined p a repeated bound family M hw hp1 (hcell a hsrc) hb) ?_
        intro M2 next log1 h1
        have s1 := one_shape p a repeated bound family M _ hw h1
        exact sources_defined rest sources.tail repeated next family M2 s1.2.1 hp2
          (fits_mono hft s1.1 hw) (one_bound_obs p a repeated bound next family M M2 log1 hw h1 hb)
      | collector slice =>
        have hcoll := hcol slice hsrc
        have hw0 := Model.push_wf M none hw
        have hneed : needsCell repeated p = false := by
          cases p with
          | bind n c =>
            simp only [NeedPattern.isCollecting] at hcoll
            subst hcoll
            simp only [needsCell]
            cases hr : repeated.contains n
            · rfl
            · exact absurd (hp1 hr) (by simp)
          | _ => simp [NeedPattern.isCollecting] at hcoll
        refine andThen_defined (one_defined p M.size repeated bound family _ hw0 hp1
          (by rw [hneed]; intro h; cases h) (bound_obs_mono hb (Model.push_extends _ _) hw)) ?_
        intro M2 next log1 h1
        have s1 := one_shape p M.size repeated bound family _ _ hw0 h1
        have e0 := Model.push_extends M none
        exact sources_defined rest sources.tail repeated next family M2 s1.2.1 hp2
          (fits_mono hft (Model.extends_trans e0 s1.1) hw)
          (one_bound_obs p M.size repeated bound next family _ M2 log1 hw0 h1
            (bound_obs_mono hb e0 hw))
end

/-- DEFINEDNESS, a whole head: on a validated head whose demanded supplied cells are observed. -/
theorem head_defined (M : Model) (ps : List NeedPattern) (cells : List Nat) (family : Bool) (hw : M.WF)
    (hp : RepeatedPlainList (needRepeatedNames ps) ps)
    (hf : Fits M (needRepeatedNames ps) ps (needLevelSources ps cells)) :
    ∃ w, walkHead M ps cells family = some w := by
  unfold walkHead gateWalk
  split
  · exact ⟨_, rfl⟩
  · exact sources_defined ps _ _ [] family M hw hp hf (by intro X q _ h; cases h)

/-! ## The production instance (Obligation B) -/

/-- A cell's VALUE is stable with counted value `v`: already COMPLETED with it, or a SUSPENDED Ready
    cell holding it (its first demand completes it with `v` and publishes the memo). -/
def ValueStable (c : NeedCell) (v : CountedResult) : Prop :=
  c.state = .completed (.ok v) ∨ (c.state = .suspended ∧ c.suspension = .ready v)

/-- A cell's CALLABLE is stable with outcome `o`: an already PUBLISHED successful projection (an
    identity or its absence), or an UNPROJECTED Ready cell (its first projection publishes the
    absence of identity). Completed VALUE alone says nothing about this channel. -/
def CallableStable (c : NeedCell) (o : Option Algorithm) : Prop :=
  c.callable = .projected (.ok o) ∨ (c.callable = .unprojected ∧ o = none ∧ ∃ w, c.suspension = .ready w)

/-- The cell at `a` exists and is stable on both channels with the observation `o`. -/
def StableAt (s : EvalState) (a : Nat) (o : Obs) : Prop :=
  ∃ c, s.needs[a]? = some c ∧ ValueStable c o.1 ∧ CallableStable c o.2

/-- THE PRODUCTION STATE INVARIANT: the model's next address is the heap size, every observed
    address is stable with its observation, and `plan` is exactly META's reification test. -/
structure ProdRel (M : Model) (s : EvalState) : Prop where
  size : s.needs.size = M.size
  stable : ∀ a o, M.view a = some o → StableAt s a o
  plan : ∀ a, (NeedPlan.shapeAt? s.needs a).isSome = M.plan a

theorem obs_of_view {M : Model} {a : Nat} {o : Obs} (h : M.view a = some o) : M.obs a = o := by
  simp [Model.obs, h]

theorem view_of_observed {M : Model} {a : Nat} (h : M.observed a = true) : ∃ o, M.view a = some o :=
  Option.isSome_iff_exists.mp h

theorem prodRel_wf {M : Model} {s : EvalState} (hs : ProdRel M s) : M.WF := by
  intro a ha
  obtain ⟨o, ho⟩ := view_of_observed ha
  obtain ⟨c, hc, -⟩ := hs.stable a o ho
  rw [← hs.size]
  exact (Array.getElem?_eq_some_iff.mp hc).1

/-- One cell updated in place, keeping its suspension and its stability: the invariant holds. -/
theorem prodRel_update {M : Model} {s t : EvalState} {a : Nat} {c c' : NeedCell} (hs : ProdRel M s)
    (hc : s.needs[a]? = some c) (hc' : t.needs[a]? = some c') (hsize : t.needs.size = s.needs.size)
    (hother : ∀ b, b ≠ a → t.needs[b]? = s.needs[b]?) (hsus : c'.suspension = c.suspension)
    (hstab : ∀ o, M.view a = some o → ValueStable c' o.1 ∧ CallableStable c' o.2) : ProdRel M t where
  size := hsize.trans hs.size
  stable b o hb := by
    by_cases h : b = a
    · subst h; exact ⟨c', hc', hstab o hb⟩
    · unfold StableAt; rw [hother b h]; exact hs.stable b o hb
  plan b := by
    rw [← hs.plan b]
    by_cases h : b = a
    · subst h; simp [NeedPlan.shapeAt?, hc, hc', hsus]
    · simp [NeedPlan.shapeAt?, hother b h]

/-- One cell appended: the invariant holds for the pushed model when the new cell is stable with
    the pushed observation and is no invocation plan. -/
theorem prodRel_push {M : Model} {s : EvalState} (hs : ProdRel M s) (cell : NeedCell) (o : Option Obs)
    (hstab : ∀ x, o = some x → ValueStable cell x.1 ∧ CallableStable cell x.2)
    (hplan : NeedPlan.ofSuspension? cell.suspension = none) :
    ProdRel (M.push o) { s with needs := s.needs.push cell } where
  size := by simp [Model.push, hs.size]
  stable b x hb := by
    simp only [Model.push] at hb
    by_cases h : b = M.size
    · subst h
      simp only [↓reduceIte] at hb
      exact ⟨cell, by rw [← hs.size]; simp, hstab x hb⟩
    · simp only [h, ↓reduceIte] at hb
      obtain ⟨c, hc, hv⟩ := hs.stable b x hb
      have hb' : b ≠ s.needs.size := by rw [hs.size]; exact h
      exact ⟨c, by simp [Array.getElem?_push, hb', hc], hv⟩
  plan b := by
    simp only [Model.push]
    by_cases h : b = M.size
    · subst h; rw [← hs.size]; simp [NeedPlan.shapeAt?, hplan]
    · have hb' : b ≠ s.needs.size := by rw [hs.size]; exact h
      rw [← hs.plan b]; simp [NeedPlan.shapeAt?, Array.getElem?_push, hb', h]

section Production
open KatLang.NeedControl

variable (ev : Nat → Expr → EvalCtx → ValEnv → EvalM CountedResult) (route : NeedPlan.Route)
  (demand : Nat → EvalM CountedResult) (written : Nat → Expr → EvalCtx → EvalM (Option Algorithm))

/-- THE VALUE SHELL ON THE STABLE DOMAIN: a completed cell returns its memo and changes nothing;
    a suspended Ready cell returns its value and publishes it as the cell's completed memo — for
    EVERY written evaluator, route and recursive driver. -/
theorem shell_value (M : Model) (s : EvalState) (a : Nat) (hs : ProdRel M s) (ha : M.observed a = true) :
    ∃ t, runEval ((NeedChannels.shell ev route demand written).capabilities.value a) s = (.ok (M.obs a).1, t) ∧
      ProdRel M t := by
  obtain ⟨o, ho⟩ := view_of_observed ha
  rw [obs_of_view ho]
  obtain ⟨c, hc, hv, hcal⟩ := hs.stable a o ho
  show ∃ t, (NeedDemand.step (ev a) route demand a).runState s = _ ∧ _
  rcases hv with hv | ⟨hv, hsus⟩
  · exact ⟨s, Memo.completed_sticky (ev a) route demand a s c _ hc hv, hs⟩
  · have hr : (NeedDemand.suspendedValue (ev a) route demand a c.suspension).runState
        { s with needs := s.needs.modify a (fun c => { c with state := .evaluating }) } =
        (.ok o.1, { s with needs := s.needs.modify a (fun c => { c with state := .evaluating }) }) := by
      rw [hsus]; rfl
    refine ⟨_, Memo.suspended_retains_state (ev a) route demand a s _ c (.ok o.1) hc hv hr rfl, ?_⟩
    refine prodRel_update (c' := { c with state := .completed (.ok o.1) }) hs hc ?_ (by simp) ?_ rfl ?_
    · simp [Array.getElem?_modify, hc]
    · intro b hb; simp [Array.getElem?_modify, Ne.symm hb]
    · intro o' ho'
      rw [ho] at ho'; cases ho'
      exact ⟨Or.inl rfl, hcal⟩

/-- THE CALLABLE SHELL ON THE STABLE DOMAIN: a published outcome is reused unchanged
    (`projected_sticky`); an unprojected Ready cell publishes the successful absence of identity
    and changes nothing else (`identityless_projection`) — for EVERY written resolver. -/
theorem shell_callable (M : Model) (s : EvalState) (a : Nat) (hs : ProdRel M s) (ha : M.observed a = true) :
    ∃ t, runEval ((NeedChannels.shell ev route demand written).capabilities.callable a) s = (.ok (M.obs a).2, t) ∧
      ProdRel M t := by
  obtain ⟨o, ho⟩ := view_of_observed ha
  rw [obs_of_view ho]
  obtain ⟨c, hc, hv, hcal⟩ := hs.stable a o ho
  show ∃ t, (NeedProjection.step (NeedProjection.suspended (written a)) a).runState s = _ ∧ _
  rcases hcal with hp | ⟨hu, hnone, w, hw⟩
  · exact ⟨s, Projection.projected_sticky _ a s c _ hc hp, hs⟩
  · rw [hnone]
    refine ⟨_, Projection.identityless_projection (written a) a s c hc hu
      (by intro src caller values h; rw [hw] at h; cases h), ?_⟩
    refine prodRel_update (c' := { c with callable := .projected (.ok none) }) hs hc
      (Projection.setCallable_at s a _ c hc) (by simp [Projection.setCallable])
      (fun b hb => Projection.setCallable_other s a b _ hb) rfl ?_
    intro o' ho'
    rw [ho] at ho'; cases ho'
    exact ⟨hv, Or.inl (by rw [hnone])⟩

/-- THE PRODUCTION INSTANCE OF `ModelCaps` (Obligation B): the binder capabilities of the total
    shells — over ANY written evaluator, route, recursive VALUE driver and written resolver, so in
    particular over the production `evalSuppliedAt`, `productionPlanRoute`, `demandNeedRecursive`
    and `projectNeedWrittenAt` (`bindingChannels`) — with the production allocator `allocateNeed`
    and META capability `NeedPlan.reference`, are described by the model along `ProdRel`. -/
theorem shell_model_caps :
    ModelCaps (NeedChannels.shell ev route demand written).capabilities ProdRel where
  value M s a hs ha := shell_value ev route demand written M s a hs ha
  callable M s a hs ha := shell_callable ev route demand written M s a hs ha
  ready M s v hs := by
    refine ⟨_, ?_, prodRel_push hs { suspension := .ready v } (readyObs v) ?_ rfl⟩
    · show (allocateNeed (.ready v)).runState s = _
      rw [Allocation.allocate_run, hs.size]
    · intro x hx
      simp only [readyObs, Option.some.injEq] at hx
      subst hx
      exact ⟨Or.inr ⟨rfl, rfl⟩, Or.inr ⟨rfl, rfl, _, rfl⟩⟩
  collector M s slice hs := by
    refine ⟨_, ?_, prodRel_push hs { suspension := .collector slice } none (by intro x hx; cases hx) rfl⟩
    show (allocateNeed (.collector slice)).runState s = _
    rw [Allocation.allocate_run, hs.size]
  referenceOk M s a hs hp := by
    have hshape : (NeedPlan.shapeAt? s.needs a).isSome = true := by rw [hs.plan a]; exact hp
    obtain ⟨shape, hsh⟩ := Option.isSome_iff_exists.mp hshape
    refine ⟨_, ?_, prodRel_push hs (CallReferenceLaws.adapterCell a) (adapterObs a) ?_ rfl⟩
    · show (NeedPlan.reference a).runState s = _
      rw [CallReferenceLaws.capture_on_plan a s shape hsh, hs.size]
    · intro x hx
      simp only [adapterObs, Option.some.injEq] at hx
      subst hx
      exact ⟨Or.inr ⟨rfl, rfl⟩, Or.inr ⟨rfl, rfl, _, rfl⟩⟩
  referenceRefused M s a hs hp := by
    have hshape : NeedPlan.shapeAt? s.needs a = none := by
      cases h : NeedPlan.shapeAt? s.needs a with
      | none => rfl
      | some _ => have := hs.plan a; rw [h, hp] at this; cases this
    refine ⟨s, ?_, hs⟩
    show (NeedPlan.reference a).runState s = _
    rw [CallReferenceLaws.reference_run]
    simp [NeedPlan.reifyResult, hshape]

end Production

/-- The evaluator's binder channels ARE an instance of the shell: the theorems above apply to
    them as written (`bindingChannels`, KatLang.lean). -/
theorem binding_channels_model_caps : ModelCaps bindingChannels.capabilities ProdRel :=
  shell_model_caps evalSuppliedAt productionPlanRoute demandNeedRecursive projectNeedWrittenAt

/-- The binder's VALUE channel is the public total `demandNeed`, by definition. -/
theorem binding_channels_value : bindingChannels.value = demandNeed := rfl

/-! ## The production binder on nested and mixed heads -/

/-- THE PRODUCTION THEOREM (Obligations A + B): on a validated head whose DEMANDED supplied cells
    are stable (`ProdRel`, `Fits`; plain names may transport any cell), the walk is defined and the
    production binder over the shell channels — the evaluator's own `bindingChannels` among them —
    returns exactly its outcome, on success, non-match and every error alike, in a state that
    satisfies the invariant for the grown model (every earlier observation kept). -/
theorem production_head_walk (ev : Nat → Expr → EvalCtx → ValEnv → EvalM CountedResult)
    (route : NeedPlan.Route) (demand : Nat → EvalM CountedResult)
    (written : Nat → Expr → EvalCtx → EvalM (Option Algorithm)) (M : Model) (s : EvalState)
    (ps : List NeedPattern) (cells : List Nat) (family : Bool) (hs : ProdRel M s)
    (hp : RepeatedPlainList (needRepeatedNames ps) ps)
    (hf : Fits M (needRepeatedNames ps) ps (needLevelSources ps cells)) :
    ∃ w t, walkHead M ps cells family = some w ∧
      runEval (bindNeedPatterns (NeedChannels.shell ev route demand written) ps cells family) s = (w.1, t) ∧
      ProdRel w.2.1 t := by
  obtain ⟨w, hw⟩ := head_defined M ps cells family (prodRel_wf hs) hp hf
  obtain ⟨t, ht, hr⟩ := head_model (shell_model_caps ev route demand written) ps cells family M s w hs hw
  exact ⟨w, t, hw, ht, hr⟩

/-- Every supplied cell observed: the `Fits` premise holds for any head. -/
theorem fits_of_observed (M : Model) (ps : List NeedPattern) (cells : List Nat)
    (hc : ∀ a ∈ cells, M.observed a = true) : Fits M (needRepeatedNames ps) ps (needLevelSources ps cells) :=
  level_sources_fit M _ ps cells hc

/-- GROWTH AND PROVENANCE of a whole head: every logged occurrence is a supplied cell or an
    address this run allocated; every allocated address a repeated name contributes is
    identityless and holds its allocation's counted value; every earlier observation is kept. -/
theorem head_provenance (M : Model) (ps : List NeedPattern) (cells : List Nat) (family : Bool) (w : Walk)
    (hw : M.WF) (h : walkHead M ps cells family = some w) :
    Model.Extends M w.2.1 ∧
    ∀ e ∈ w.2.2, (e.2 ∈ cells ∨ M.size ≤ e.2) ∧
      ((needRepeatedNames ps).contains e.1 = true → M.size ≤ e.2 →
        ∃ v, w.2.1.obs e.2 = ((v, Result.valueCount v), none)) := by
  unfold walkHead gateWalk at h
  split at h
  · simp only [Option.some.injEq] at h; subst h
    exact ⟨Model.extends_refl M, by simp⟩
  · have s := sources_shape ps _ _ [] family M w hw h
    refine ⟨s.1, fun e he => ⟨?_, fun hr hfresh => ?_⟩⟩
    · rcases s.2.2.2.1 e he with h1 | h1
      · exact Or.inl (cell_mem_level_sources ps cells _ h1)
      · exact Or.inr h1
    · obtain ⟨o, ho⟩ := view_of_observed (s.2.2.2.2 e he hr)
      obtain ⟨v, rfl⟩ := s.2.2.1 e.2 o ho hfresh
      exact ⟨v, obs_of_view ho⟩

/-- REPRESENTATIVE (success): each repeated name of a head is bound to the representative `retain`
    keeps over the contributions the run logged for it, in written traversal order, at every depth;
    a name with no logged contribution is unbound. -/
theorem head_binding_is_retain (M : Model) (ps : List NeedPattern) (cells : List Nat) (family : Bool)
    (env : NeedEnv) (N : Model) (log : Log) (hw : M.WF)
    (h : walkHead M ps cells family = some (.ok (some env), N, log))
    (X : Ident) (hX : (needRepeatedNames ps).contains X = true) :
    match occ X log with
    | [] => lookupAssoc X env = none
    | a :: as => ∃ r, retain (contrib N.obs a) (as.map (contrib N.obs)) = .ok r ∧
        lookupAssoc X env = some r.address := by
  unfold walkHead gateWalk at h
  split at h
  · cases family <;> simp at h
  · have t := sources_tracks N.obs ps _ _ [] env family M N log hw h (fun _ _ => rfl) X hX
    simp only [lookupAssoc] at t
    unfold Tracks at t
    cases ho : occ X log with
    | nil => rw [ho] at t; simpa [perName] using t
    | cons a as =>
      rw [ho] at t
      simp only [perName] at t
      cases hr : retain (contrib N.obs a) (as.map (contrib N.obs)) with
      | error e => rw [hr] at t; exact t.elim
      | ok r => rw [hr] at t; exact ⟨r, hr, t⟩

/-- FIRST CONFLICT (failure or non-match): if a repeated name's fold over its logged
    contributions is refused, the run ended at exactly that contribution — the log's last
    occurrence is that name's — with the binder's verdict for that conflict. -/
theorem head_conflict (M : Model) (ps : List NeedPattern) (cells : List Nat) (family : Bool) (w : Walk)
    (hw : M.WF) (h : walkHead M ps cells family = some w)
    (X : Ident) (hX : (needRepeatedNames ps).contains X = true) (a : Nat) (as : List Nat)
    (ho : occ X w.2.2 = a :: as) (c : Conflict)
    (hc : retain (contrib w.2.1.obs a) (as.map (contrib w.2.1.obs)) = .error c) :
    w.1 = conflictOutcome X c family ∧ ∃ b, w.2.2.getLast? = some (X, b) := by
  unfold walkHead gateWalk at h
  split at h
  · simp only [Option.some.injEq] at h; subst h; simp [occ] at ho
  · exact sources_conflict w.2.1.obs ps _ _ [] family M w hw h (fun _ _ => rfl) X hX c
      (by simp only [lookupAssoc, ho, perName, hc])

/-- Results 3–5 of `RepeatedNameLaws` on the production head (success): the representative is an
    actual contributed cell, it carries a callable identity iff some contribution does, and it is
    the FIRST richest contribution in written traversal order. -/
theorem head_representative (M : Model) (ps : List NeedPattern) (cells : List Nat) (family : Bool)
    (env : NeedEnv) (N : Model) (log : Log) (hw : M.WF)
    (h : walkHead M ps cells family = some (.ok (some env), N, log))
    (X : Ident) (hX : (needRepeatedNames ps).contains X = true) (a : Nat) (as : List Nat)
    (ho : occ X log = a :: as) :
    ∃ r, lookupAssoc X env = some r.address ∧ r.address ∈ a :: as ∧ r = contrib N.obs r.address ∧
      (r.callable.isSome = true ↔ ∃ x ∈ a :: as, (N.obs x).2.isSome = true) ∧
      r = (((a :: as).map (contrib N.obs)).find? (fun x => x.callable.isSome)).getD (contrib N.obs a) := by
  have hb := head_binding_is_retain M ps cells family env N log hw h X hX
  rw [ho] at hb
  obtain ⟨r, hr, hl⟩ := hb
  refine ⟨r, hl, retain_address_mem N.obs a as r hr, retain_contrib N.obs a as r hr, ?_, ?_⟩
  · rw [retain_callable_isSome_iff _ _ r hr]
    constructor
    · rintro ⟨x, hx, hs⟩
      rw [← List.map_cons] at hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      exact ⟨y, hy, hs⟩
    · rintro ⟨y, hy, hs⟩
      exact ⟨contrib N.obs y, by rw [← List.map_cons]; exact List.mem_map_of_mem hy, hs⟩
  · rw [retain_first_richest _ _ r hr]; rfl

/-- A name contributed only by FRESH cells (opened structure items or META adapters) retains no
    callable identity: allocated Ready data carries none. -/
theorem head_fresh_contributions_identityless (M : Model) (ps : List NeedPattern) (cells : List Nat)
    (family : Bool) (env : NeedEnv) (N : Model) (log : Log) (hw : M.WF)
    (h : walkHead M ps cells family = some (.ok (some env), N, log))
    (X : Ident) (hX : (needRepeatedNames ps).contains X = true) (a : Nat) (as : List Nat)
    (ho : occ X log = a :: as) (hfresh : ∀ x ∈ a :: as, M.size ≤ x) :
    ∃ q, lookupAssoc X env = some q ∧ (N.obs q).2 = none := by
  obtain ⟨r, hl, hm, hrc, -, -⟩ := head_representative M ps cells family env N log hw h X hX a as ho
  refine ⟨r.address, hl, ?_⟩
  have hp := (head_provenance M ps cells family _ hw h).2 (X, r.address)
    (occ_mem X log _ (by rw [ho]; exact hm))
  obtain ⟨v, hv⟩ := hp.2 hX (hfresh _ hm)
  rw [hv]

/-! ## Permutation of completed contributions, up to addresses -/

/-- An identity present in the observed part of the heap. -/
def ModelPresent (M : Model) (a : Algorithm) : Prop :=
  ∃ address v, M.view address = some (v, some a)

/-- The initial identity domain: observed CALLABLEs pairwise avoid a successful
    identified/anonymous fallback. This is a condition on the supplied observations, not a
    claim that every algorithm reachable from a validated program satisfies it. -/
def ModelNoCross (M : Model) : Prop :=
  ∀ a b, ModelPresent M a → ModelPresent M b → CallableIdentityDomain.IdentityNoCross a b

theorem model_present_of_obs (M : Model) (address : Nat) (a : Algorithm)
    (h : (M.obs address).2 = some a) : ModelPresent M a := by
  cases hv : M.view address with
  | none => simp [Model.obs, hv] at h
  | some o =>
    rcases o with ⟨v, cal⟩
    simp only [Model.obs, hv, Option.getD_some] at h
    exact ⟨address, v, by simpa [h] using hv⟩

/-- Allocation contributes no new identities: every present identity after the walk was
    already present initially. This includes Ready children and META adapters; collector cells
    remain outside the observation domain. -/
theorem model_present_before_growth {M N : Model} (he : Model.Extends M N)
    (hf : FreshIdless M N) (a : Algorithm) (h : ModelPresent N a) : ModelPresent M a := by
  obtain ⟨address, v, hv⟩ := h
  by_cases hlt : address < M.size
  · exact ⟨address, v, ((he.2 address hlt).1).symm.trans hv⟩
  · obtain ⟨w, hw⟩ := hf address _ hv (Nat.le_of_not_lt hlt)
    have impossible : (some a : Option Algorithm) = none := congrArg Prod.snd hw
    cases impossible

theorem model_no_cross_after_growth {M N : Model} (he : Model.Extends M N)
    (hf : FreshIdless M N) (h : ModelNoCross M) : ModelNoCross N :=
  fun a b ha hb => h a b (model_present_before_growth he hf a ha)
    (model_present_before_growth he hf b hb)

/-- A concrete sufficient initial domain: all observed identities have the same parent profile
    (parentless callables and builtins are examples). The more general `ModelNoCross` also admits
    the unequal-profile pairs covered by `CallableIdentityDomain`. -/
theorem model_no_cross_of_profiles (M : Model) (profile : Option (List Bool))
    (h : ∀ a, ModelPresent M a → parentProfile a = profile) : ModelNoCross M := by
  intro a b ha hb
  exact CallableIdentityDomain.identity_no_cross_of_profiles a b ((h a ha).trans (h b hb).symm)

/-- PRODUCTION DOMAIN BRIDGE: a defined head walk preserves its initial no-cross identity domain.
    Every completed contribution list from the final model therefore satisfies `CallableTransOn`.
    Together with `production_head_walk` this applies to the evaluator's binder channels, including
    structural, collector and META allocations, without assuming transitivity again after the run. -/
theorem head_callable_trans_on_of_no_cross (M : Model) (ps : List NeedPattern) (cells : List Nat)
    (family : Bool) (w : Walk) (hw : M.WF) (h : walkHead M ps cells family = some w)
    (hd : ModelNoCross M) (addresses : List Nat) :
    CallableTransOn (addresses.map (contrib w.2.1.obs)) := by
  have hn : ModelNoCross w.2.1 := by
    unfold walkHead gateWalk at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      exact hd
    · have shape := sources_shape ps _ _ [] family M w hw h
      exact model_no_cross_after_growth shape.1 shape.2.2.1 hd
  apply CallableIdentityDomain.callable_trans_on_of_no_cross
  intro a b ha hb
  obtain ⟨ca, hca, hia⟩ := ha
  obtain ⟨cb, hcb, hib⟩ := hb
  obtain ⟨aa, -, rfl⟩ := List.mem_map.mp hca
  obtain ⟨ab, -, rfl⟩ := List.mem_map.mp hcb
  exact hn a b (model_present_of_obs _ aa a hia) (model_present_of_obs _ ab b hib)

/-- The production channel instance with the identity-domain obligation discharged for every
    final contribution list. The initial `ModelNoCross` condition is independent of successful
    binding: different identities may still conflict, and unrelated head checks may still fail. -/
theorem production_head_walk_no_cross (ev : Nat → Expr → EvalCtx → ValEnv → EvalM CountedResult)
    (route : NeedPlan.Route) (demand : Nat → EvalM CountedResult)
    (written : Nat → Expr → EvalCtx → EvalM (Option Algorithm)) (M : Model) (s : EvalState)
    (ps : List NeedPattern) (cells : List Nat) (family : Bool) (hs : ProdRel M s)
    (hp : RepeatedPlainList (needRepeatedNames ps) ps)
    (hf : Fits M (needRepeatedNames ps) ps (needLevelSources ps cells)) (hd : ModelNoCross M) :
    ∃ w t, walkHead M ps cells family = some w ∧
      runEval (bindNeedPatterns (NeedChannels.shell ev route demand written) ps cells family) s = (w.1, t) ∧
      ProdRel w.2.1 t ∧ ∀ addresses : List Nat, CallableTransOn (addresses.map (contrib w.2.1.obs)) := by
  obtain ⟨w, t, hw, ht, hr⟩ := production_head_walk ev route demand written M s ps cells family hs hp hf
  exact ⟨w, t, hw, ht, hr, fun addresses =>
    head_callable_trans_on_of_no_cross M ps cells family w (prodRel_wf hs) hw hd addresses⟩

/-- A contribution's observation without its address. -/
def strip (c : Contribution) : Contribution := { c with address := 0 }

theorem retainStep_strip (rep c : Contribution) :
    retainStep (strip rep) (strip c) = (retainStep rep c).map strip := by
  obtain ⟨ra, rv, rc⟩ := rep
  obtain ⟨ca, cv, cc⟩ := c
  simp only [retainStep, strip]
  by_cases hv : (rv == cv) = true
  · simp only [hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rcases rc with _ | a <;> rcases cc with _ | b
    · simp [Except.map, strip]
    · simp [Except.map, strip]
    · simp [Except.map, strip]
    · by_cases hs : sameRepeatedCallableIdentity a b = true <;> simp [hs, Except.map, strip]
  · simp [hv, Except.map]

theorem retain_strip : ∀ (rep : Contribution) (cs : List Contribution),
    retain (strip rep) (cs.map strip) = (retain rep cs).map strip
  | rep, [] => rfl
  | rep, c :: cs => by
    simp only [List.map_cons, retain, retainStep_strip]
    cases retainStep rep c with
    | error e => rfl
    | ok next => exact retain_strip next cs

theorem callable_trans_on_strip (l : List Contribution) (h : CallableTransOn l) :
    CallableTransOn (l.map strip) := by
  have pres : ∀ x, Present (l.map strip) x → Present l x := by
    rintro x ⟨y, hy, hyx⟩
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy
    exact ⟨z, hz, hyx⟩
  intro a b c ha hb hc
  exact h a b c (pres a ha) (pres b hb) (pres c hc)

/-- SATISFIABILITY under permutation of completed contributions whose OBSERVATIONS are permuted —
    the two lists may come from different runs with different (fresh) addresses. -/
theorem retain_satisfiable_perm_up_to_address (c d : Contribution) (cs ds : List Contribution)
    (hp : ((c :: cs).map strip).Perm ((d :: ds).map strip)) (hT : CallableTransOn (c :: cs)) :
    (∃ r, retain c cs = .ok r) ↔ (∃ r, retain d ds = .ok r) := by
  have key := retain_satisfiable_perm (strip c) (strip d) (cs.map strip) (ds.map strip) hp
    (callable_trans_on_strip _ hT)
  rw [retain_strip, retain_strip] at key
  constructor
  · rintro ⟨r, hr⟩
    obtain ⟨r', hr'⟩ := key.mp ⟨strip r, by rw [hr]; rfl⟩
    cases h : retain d ds with
    | error e => rw [h] at hr'; cases hr'
    | ok x => exact ⟨x, rfl⟩
  · rintro ⟨r, hr⟩
    obtain ⟨r', hr'⟩ := key.mpr ⟨strip r, by rw [hr]; rfl⟩
    cases h : retain c cs with
    | error e => rw [h] at hr'; cases hr'
    | ok x => exact ⟨x, rfl⟩

/-- OBSERVATION under permutation, up to addresses: the retained counted VALUE (with its count),
    callable availability and callable identity agree; the retained ADDRESS need not. -/
theorem retain_perm_up_to_address (c d : Contribution) (cs ds : List Contribution)
    (hp : ((c :: cs).map strip).Perm ((d :: ds).map strip)) (hT : CallableTransOn (c :: cs))
    (r r' : Contribution) (hr : retain c cs = .ok r) (hr' : retain d ds = .ok r') :
    r.value = r'.value ∧ r.callable.isSome = r'.callable.isSome ∧
      (∀ a b, r.callable = some a → r'.callable = some b → sameRepeatedCallableIdentity a b = true) := by
  have h1 : retain (strip c) (cs.map strip) = .ok (strip r) := by rw [retain_strip, hr]; rfl
  have h2 : retain (strip d) (ds.map strip) = .ok (strip r') := by rw [retain_strip, hr']; rfl
  exact retain_perm_preserves_observation (strip c) (strip d) (cs.map strip) (ds.map strip) hp
    (callable_trans_on_strip _ hT) (strip r) (strip r') h1 h2

/-- PRODUCTION PERMUTATION COROLLARY: two successful head runs — possibly different heads, models,
    states and fresh addresses — in which one repeated name's completed contributions carry the
    same OBSERVATIONS in permuted order bind that name to representatives with the same counted
    VALUE, callable availability and callable identity (on the identity domain `CallableTransOn`).
    Addresses, heaps and every other check of the two runs are NOT related. -/
theorem head_perm_preserves_observation (M1 M2 : Model) (ps1 ps2 : List NeedPattern)
    (cells1 cells2 : List Nat) (family1 family2 : Bool) (env1 env2 : NeedEnv) (N1 N2 : Model)
    (log1 log2 : Log) (hw1 : M1.WF) (hw2 : M2.WF)
    (h1 : walkHead M1 ps1 cells1 family1 = some (.ok (some env1), N1, log1))
    (h2 : walkHead M2 ps2 cells2 family2 = some (.ok (some env2), N2, log2))
    (X : Ident) (hX1 : (needRepeatedNames ps1).contains X = true)
    (hX2 : (needRepeatedNames ps2).contains X = true)
    (a1 a2 : Nat) (as1 as2 : List Nat) (ho1 : occ X log1 = a1 :: as1) (ho2 : occ X log2 = a2 :: as2)
    (hp : ((a1 :: as1).map (fun a => strip (contrib N1.obs a))).Perm
      ((a2 :: as2).map (fun a => strip (contrib N2.obs a))))
    (hT : CallableTransOn ((a1 :: as1).map (contrib N1.obs))) :
    ∃ q1 q2, lookupAssoc X env1 = some q1 ∧ lookupAssoc X env2 = some q2 ∧
      (N1.obs q1).1 = (N2.obs q2).1 ∧ (N1.obs q1).2.isSome = (N2.obs q2).2.isSome ∧
      (∀ a b, (N1.obs q1).2 = some a → (N2.obs q2).2 = some b → sameRepeatedCallableIdentity a b = true) := by
  have b1 := head_binding_is_retain M1 ps1 cells1 family1 env1 N1 log1 hw1 h1 X hX1
  have b2 := head_binding_is_retain M2 ps2 cells2 family2 env2 N2 log2 hw2 h2 X hX2
  rw [ho1] at b1; rw [ho2] at b2
  obtain ⟨r1, hr1, hl1⟩ := b1
  obtain ⟨r2, hr2, hl2⟩ := b2
  have hp' : ((contrib N1.obs a1 :: as1.map (contrib N1.obs)).map strip).Perm
      ((contrib N2.obs a2 :: as2.map (contrib N2.obs)).map strip) := by
    simpa [List.map_map, Function.comp_def] using hp
  obtain ⟨v, c, i⟩ := retain_perm_up_to_address _ _ _ _ hp' (by simpa using hT) r1 r2 hr1 hr2
  have e1 := retain_contrib N1.obs a1 as1 r1 hr1
  have e2 := retain_contrib N2.obs a2 as2 r2 hr2
  refine ⟨r1.address, r2.address, hl1, hl2, ?_, ?_, ?_⟩
  · have := v; rw [e1, e2] at this; exact this
  · have := c; rw [e1, e2] at this; exact this
  · intro a b ha hb
    apply i a b
    · rw [e1]; exact ha
    · rw [e2]; exact hb

/-! ## Whole-head success is not repeated-name compatibility -/

/-- A three-cell model: two equal numbers and a number where a sequence is expected. -/
def witnessModel : Model :=
  ⟨fun a => if a = 0 ∨ a = 1 then some ((.atom 1, 1), none)
    else if a = 2 then some ((.atom 5, 1), none) else none, fun _ => false, 3⟩

/-- KERNEL WITNESS: the repeated name `x` is compatible (its fold over its contributions
    succeeds), yet the level `x, x, (y, z)` does not match in family mode — a later independent
    structural check refuses the third cell (a number where a sequence is expected). Compatibility
    alone never establishes whole-head success; the head's cardinality, literal, structural and
    META checks are independent. Stated on the level walk with the head's repeated set `["x"]`:
    the kernel does not reduce `needRepeatedNames` (`List.eraseDups` is well-founded); the
    head-level run is the executable guard `compatible_head_does_not_match`
    (`NestedRepeatedNameGuards.lean`). -/
theorem compatible_is_not_success :
    (∃ r, retain (contrib witnessModel.obs 0) [contrib witnessModel.obs 1] = .ok r) ∧
    walkSources witnessModel [.bind "x", .bind "x", .sequence [.bind "y", .bind "z"]]
      (needLevelSources [.bind "x", .bind "x", .sequence [.bind "y", .bind "z"]] [0, 1, 2]) ["x"] [] true =
      some (.ok none, witnessModel, [("x", 0), ("x", 1)]) :=
  ⟨⟨_, rfl⟩, rfl⟩

end KatLang.NestedRepeatedNames
