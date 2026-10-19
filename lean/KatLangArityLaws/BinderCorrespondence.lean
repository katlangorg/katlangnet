import KatLangArityLaws.BinderTrace

open KatLang KatLang.BinderTrace

/-!
# Two correspondences of the Model-C binder (R3, October 2026)

The FORMAL-07 roadmap's R3 item lists three proof obligations: (a) the order of the binder's
capability invocations, truncated at the first failure — `KatLangArityLaws.BinderTrace`; (b)
"results depend on the channels only through the inspecting positions"; (c) the family/ordinary
correspondence. This module proves (b) and (c) for the production core (`NeedBinder`, at any
capability record `k : NeedCapabilities EvalM`). Its theorems are PRODUCTION theorems over that
core's `EvalM` runs, not trace theorems; they read the schedule functions of `BinderTrace`
(`oneEvents` … `patternsEvents`), whose meaning as the binder's actual invocations is
`traced_patterns`.

* (b) CHANNEL SUBSTITUTION, per channel — two capability records with the same allocator whose
  VALUE demands agree outside a set of cells `V` and whose CALLABLE projections agree outside a
  set `C` give the IDENTICAL run (outcome, final state, schedule) whenever the first run's
  schedule demands no VALUE on a cell of `V` and projects no CALLABLE on a cell of `C`
  (`results_depend_only_on_invoked_cells`). Corollaries: a run that invokes nothing is
  channel-independent; a head that repeats no name is independent of the CALLABLE channel.
* (b′) THE STATIC FORM ("inspecting positions") — every VALUE or CALLABLE invocation of a whole
  head is on a supplied cell at an INSPECTING top-level position (a literal, a structural
  pattern, the unpacking receiver, or a name the head repeats) or on a cell the run itself
  allocated (`invoked_cells_are_inspected_or_allocated`). So the channels at supplied cells that
  occur only at plain, non-repeated positions — and that no allocation of the run reuses — are
  irrelevant (`plain_cells_are_channel_irrelevant`). Aliasing is respected: a cell supplied at a
  plain position AND an inspecting one is inspected. The freshness hypothesis is a schedule fact;
  with the production allocator every allocation returns the then-current heap size, so it holds
  whenever the cells lie below the initial heap size and the channels never shrink the heap —
  supported for the internal partial `demandNeedRecursive` channel by source inspection, not
  a whole-run theorem. R5 proves local/conditional heap laws and total public `demandNeed`
  specialization in `KatLangArityLaws/NeedControl.lean`; its callbacks still need the stated
  heap-preservation assumptions.
* (c) MODE CORRESPONDENCE, every head — a clause attempt (`family = true`) and an ordinary
  binding (`family = false`) perform the same invocations in the same order and reach the same
  final state; their outcomes differ ONLY where the ordinary binding raises one of four
  incompatibility errors, and there the attempt is a non-match (`family_attempt_is_the_ordinary_binding`,
  `modes_differ_only_at_an_incompatibility`). A literal mismatch is a non-match in BOTH modes.
  For a LITERAL-FREE head (every ordinary signature: `ordinary_heads_are_literal_free`) the
  ordinary binding is never a non-match. The relation classifies errors by VALUE, so an
  incompatibility-shaped error raised by a channel is a raised error in both modes, not a
  non-match: "the ordinary binding raised an incompatibility-shaped error" does NOT imply "the
  attempt was a non-match" — the converse that holds is the one above, for differing outcomes.

As everywhere in R3, helper outcomes that reach `partial` definitions stay symbolic, and nothing
here concerns the `partial` callers or C#.
-/

namespace KatLang.BinderCorrespondence

/-! ## (b) Channel substitution -/

/-- The cell an event is about. -/
def _root_.KatLang.BinderTrace.NeedEvent.address : NeedEvent → Nat
  | .value a => a
  | .callable a => a
  | .collector a _ => a
  | .ready a => a
  | .expression a => a
  | .reference a _ => a

/-- Whether an event is a VALUE or CALLABLE invocation. -/
def _root_.KatLang.BinderTrace.NeedEvent.isInvocation : NeedEvent → Bool
  | .value _ => true
  | .callable _ => true
  | _ => false

/-- Whether an event invokes a channel on a cell the sets name: VALUE on a cell of `V`, CALLABLE
    on a cell of `C`. Allocations invoke no channel. -/
def Hits (V C : Nat → Prop) : NeedEvent → Prop
  | .value a => V a
  | .callable a => C a
  | _ => False

/-- `k₁` and `k₂` have the same allocator, the same VALUE demand (as a complete `EvalM`
    computation) on every cell outside `V`, and the same CALLABLE projection on every cell
    outside `C`. -/
structure AgreeOutside (V C : Nat → Prop) (k₁ k₂ : NeedCapabilities EvalM) : Prop where
  allocate : k₁.allocate = k₂.allocate
  value : ∀ a, ¬ V a → k₁.value a = k₂.value a
  callable : ∀ a, ¬ C a → k₁.callable a = k₂.callable a
  /-- The same META capability (CallReference S1): production capabilities share
      `NeedPlan.reference`, which reads no channel. -/
  reference : k₁.reference = k₂.reference

/-- A schedule AVOIDS `V` and `C`: none of its VALUE demands is on a cell of `V`, none of its
    CALLABLE projections on a cell of `C`. -/
def Avoids (V C : Nat → Prop) (events : List NeedEvent) : Prop :=
  ∀ ev ∈ events, ¬ Hits V C ev

theorem avoids_append {V C : Nat → Prop} {l₁ l₂ : List NeedEvent} (h : Avoids V C (l₁ ++ l₂)) :
    Avoids V C l₁ ∧ Avoids V C l₂ :=
  ⟨fun ev hev => h ev (List.mem_append_left _ hev), fun ev hev => h ev (List.mem_append_right _ hev)⟩

theorem avoids_cons {V C : Nat → Prop} {ev : NeedEvent} {l : List NeedEvent} (h : Avoids V C (ev :: l)) :
    ¬ Hits V C ev ∧ Avoids V C l :=
  ⟨h ev List.mem_cons_self, fun e he => h e (List.mem_cons_of_mem _ he)⟩

theorem readyEvents_allocator {k₁ k₂ : NeedCapabilities EvalM} (h : k₁.allocate = k₂.allocate)
    (items : List Result) (s : EvalState) : readyEvents k₁ items s = readyEvents k₂ items s := by
  induction items generalizing s with
  | nil => rfl
  | cons item rest ih => simp only [readyEvents, h, ih]

theorem readyCells_allocator {k₁ k₂ : NeedCapabilities EvalM} (h : k₁.allocate = k₂.allocate)
    (items : List Result) : readyCells k₁ items = readyCells k₂ items := by
  simp only [readyCells, h]

theorem addressEvents_allocator {k₁ k₂ : NeedCapabilities EvalM} (h : k₁.allocate = k₂.allocate)
    (source : NeedSource Nat) (s : EvalState) : addressEvents k₁ source s = addressEvents k₂ source s := by
  cases source <;> simp only [addressEvents, h]

/-- The structural arms of the core (sequence, list, unpacking receiver) in one shape. -/
theorem bindOne_structural_shape (k : NeedCapabilities EvalM) (p : NeedPattern) (ps : List NeedPattern)
    (hp : p = .sequence ps ∨ p = .list ps ∨ p = .unpack ps) (address : Nat) (repeated : List Ident)
    (bound : NeedEnv) (family : Bool) :
    NeedBinder.bindOne k p address repeated bound family = (do
      let (value, _) <- k.value address
      match structuralItems p value with
      | none => if family then pure none else throw (structuralPatternKindMismatch p.toParameter value)
      | some items => do
          let cells <- readyCells k items
          NeedBinder.cardinalityGate ps cells.length family
            (NeedBinder.bindSources k ps (needLevelSources ps cells) repeated bound family)) := by
  rcases hp with rfl | rfl | rfl <;> rfl

/-- The structural arms of the schedule in one shape. -/
theorem oneEvents_structural_shape (k : NeedCapabilities EvalM) (p : NeedPattern) (ps : List NeedPattern)
    (hp : p = .sequence ps ∨ p = .list ps ∨ p = .unpack ps) (address : Nat) (repeated : List Ident)
    (bound : NeedEnv) (family : Bool) (s : EvalState) :
    oneEvents k p address repeated bound family s =
      .value address ::
        match runEval (k.value address) s with
        | (.error _, _) => []
        | (.ok (value, _), s1) =>
          match structuralItems p value with
          | none => []
          | some items =>
            readyEvents k items s1 ++
              match runEval (readyCells k items) s1 with
              | (.error _, _) => []
              | (.ok cells, s2) =>
                if needAcceptsCardinality ps cells.length = true then
                  sourcesEvents k ps (needLevelSources ps cells) repeated bound family s2
                else [] := by
  rcases hp with rfl | rfl | rfl <;> rfl

/-- The literal arm of the core: it demands its cell's VALUE and decides by the matcher, in
    either mode. -/
theorem bindOne_literal_shape (k : NeedCapabilities EvalM) (literal : Pattern) (address : Nat)
    (repeated : List Ident) (bound : NeedEnv) (family : Bool) :
    NeedBinder.bindOne k (.literal literal) address repeated bound family = (do
      let (value, _) <- k.value address
      pure (if (matchPattern literal value).isSome then some bound else none)) := rfl

/-- CHANNEL SUBSTITUTION, one name occurrence. -/
theorem name_substitution (V C : Nat → Prop) (k₁ k₂ : NeedCapabilities EvalM) (hk : AgreeOutside V C k₁ k₂)
    (name : Ident) (address : Nat) (repeated : List Ident) (bound : NeedEnv) (family : Bool) (s : EvalState)
    (havoid : Avoids V C (nameEvents k₁ name address repeated bound s)) :
    runEval (NeedBinder.bindName k₁ name address repeated bound family) s
      = runEval (NeedBinder.bindName k₂ name address repeated bound family) s
    ∧ nameEvents k₁ name address repeated bound s = nameEvents k₂ name address repeated bound s := by
  by_cases hr : repeated.contains name = true
  · rw [repeated_name_binding k₁ name address repeated bound family s hr,
      repeated_name_binding k₂ name address repeated bound family s hr]
    simp only [nameEvents, hr, ↓reduceIte] at havoid ⊢
    simp only [repeatedNameEvents] at havoid ⊢
    have hva := hk.value address (avoids_cons havoid).1
    rcases h1 : runEval (k₁.value address) s with ⟨e | value, s1⟩
    · have h1' : runEval (k₂.value address) s = (.error e, s1) := by rw [← hva, h1]
      simp [h1']
    · have h1' : runEval (k₂.value address) s = (.ok value, s1) := by rw [← hva, h1]
      simp only [h1] at havoid
      cases hl : lookupAssoc name bound with
      | none => simp [h1']
      | some previous =>
        simp only [hl] at havoid
        have hvp := hk.value previous (avoids_cons (avoids_cons havoid).2).1
        rcases h2 : runEval (k₁.value previous) s1 with ⟨e | before, s2⟩
        · have h2' : runEval (k₂.value previous) s1 = (.error e, s2) := by rw [← hvp, h2]
          simp [h1', h2, h2']
        · have h2' : runEval (k₂.value previous) s1 = (.ok before, s2) := by rw [← hvp, h2]
          cases hbv : (before == value)
          · simp [h1', h2, h2', hbv]
          · simp only [h2, hbv, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at havoid
            have hcp := hk.callable previous (avoids_cons (avoids_cons (avoids_cons havoid).2).2).1
            rcases h3 : runEval (k₁.callable previous) s2 with ⟨e | first, s3⟩
            · have h3' : runEval (k₂.callable previous) s2 = (.error e, s3) := by rw [← hcp, h3]
              simp [h1', h2, h2', hbv, h3, h3']
            · have h3' : runEval (k₂.callable previous) s2 = (.ok first, s3) := by rw [← hcp, h3]
              simp only [h3] at havoid
              have hca := hk.callable address
                (avoids_cons (avoids_cons (avoids_cons (avoids_cons havoid).2).2).2).1
              rcases h4 : runEval (k₁.callable address) s3 with ⟨e | second, s4⟩
              · have h4' : runEval (k₂.callable address) s3 = (.error e, s4) := by rw [← hca, h4]
                simp [h1', h2, h2', hbv, h3, h3', h4, h4']
              · have h4' : runEval (k₂.callable address) s3 = (.ok second, s4) := by rw [← hca, h4]
                simp [h1', h2, h2', hbv, h3, h3', h4, h4']
  · have hr' : repeated.contains name = false := by simpa using hr
    constructor
    · rw [BinderCore.core_plain_name_is_pure k₁ name address repeated bound family hr',
        BinderCore.core_plain_name_is_pure k₂ name address repeated bound family hr']
    · simp only [nameEvents, hr', Bool.false_eq_true, ↓reduceIte]

/-- CHANNEL SUBSTITUTION, one structural pattern, given the substitution law for its nested
    level. -/
theorem structural_substitution (V C : Nat → Prop) (k₁ k₂ : NeedCapabilities EvalM) (hk : AgreeOutside V C k₁ k₂)
    (p : NeedPattern) (ps : List NeedPattern) (hp : p = .sequence ps ∨ p = .list ps ∨ p = .unpack ps)
    (address : Nat) (repeated : List Ident) (bound : NeedEnv) (family : Bool) (s : EvalState)
    (ih : ∀ (cells : List Nat) (s2 : EvalState),
      Avoids V C (sourcesEvents k₁ ps (needLevelSources ps cells) repeated bound family s2) →
        runEval (NeedBinder.bindSources k₁ ps (needLevelSources ps cells) repeated bound family) s2
          = runEval (NeedBinder.bindSources k₂ ps (needLevelSources ps cells) repeated bound family) s2
        ∧ sourcesEvents k₁ ps (needLevelSources ps cells) repeated bound family s2
          = sourcesEvents k₂ ps (needLevelSources ps cells) repeated bound family s2)
    (havoid : Avoids V C (oneEvents k₁ p address repeated bound family s)) :
    runEval (NeedBinder.bindOne k₁ p address repeated bound family) s
      = runEval (NeedBinder.bindOne k₂ p address repeated bound family) s
    ∧ oneEvents k₁ p address repeated bound family s = oneEvents k₂ p address repeated bound family s := by
  rw [oneEvents_structural_shape k₁ p ps hp] at havoid
  rw [bindOne_structural_shape k₁ p ps hp, bindOne_structural_shape k₂ p ps hp,
    oneEvents_structural_shape k₁ p ps hp, oneEvents_structural_shape k₂ p ps hp]
  have hva := hk.value address (avoids_cons havoid).1
  have hrest := (avoids_cons havoid).2
  simp only [← hva, ← readyCells_allocator hk.allocate, ← readyEvents_allocator hk.allocate, runEval_bind]
  rcases h1 : runEval (k₁.value address) s with ⟨e | ⟨value, count⟩, s1⟩
  · simp
  · simp only [h1] at hrest
    simp only [thenRun_ok]
    cases hi : structuralItems p value with
    | none => simp
    | some items =>
      simp only [hi] at hrest
      simp only [runEval_bind]
      rcases h2 : runEval (readyCells k₁ items) s1 with ⟨e | cells, s2⟩
      · simp
      · simp only [h2] at hrest
        simp only [thenRun_ok, NeedBinder.cardinalityGate]
        cases hacc : needAcceptsCardinality ps cells.length
        · simp
        · simp only [hacc, ↓reduceIte] at hrest
          obtain ⟨hrun, hev⟩ := ih cells s2 (avoids_append hrest).2
          simp [hrun, hev]

mutual
  /-- CHANNEL SUBSTITUTION, one pattern: agreement outside `V`/`C` and a schedule that avoids
      them give the same run and the same schedule. -/
  theorem one_substitution (V C : Nat → Prop) (k₁ k₂ : NeedCapabilities EvalM) (hk : AgreeOutside V C k₁ k₂)
      (p : NeedPattern) (address : Nat) (repeated : List Ident) (bound : NeedEnv) (family : Bool)
      (s : EvalState) (havoid : Avoids V C (oneEvents k₁ p address repeated bound family s)) :
      runEval (NeedBinder.bindOne k₁ p address repeated bound family) s
        = runEval (NeedBinder.bindOne k₂ p address repeated bound family) s
      ∧ oneEvents k₁ p address repeated bound family s = oneEvents k₂ p address repeated bound family s := by
    cases p with
    | bind name collecting =>
      exact name_substitution V C k₁ k₂ hk name address repeated bound family s havoid
    | literal literal =>
      have hva := hk.value address (avoids_cons havoid).1
      constructor
      · simp only [NeedBinder.bindOne, hva]
      · rfl
    | metaRef name =>
      simp only [oneEvents] at havoid
      simp only [NeedBinder.bindOne, oneEvents, ← hk.reference, runEval_bind]
      rcases h1 : runEval (k₁.reference address) s with ⟨e | adapter, s1⟩
      · simp
      · simp only [h1] at havoid
        obtain ⟨hrun, hev⟩ := name_substitution V C k₁ k₂ hk name adapter repeated bound family s1
          (avoids_cons havoid).2
        simp [hrun, hev]
    | sequence ps =>
      exact structural_substitution V C k₁ k₂ hk _ ps (Or.inl rfl) address repeated bound family s
        (fun cells s2 h => sources_substitution V C k₁ k₂ hk ps (needLevelSources ps cells) repeated bound family s2 h)
        havoid
    | list ps =>
      exact structural_substitution V C k₁ k₂ hk _ ps (Or.inr (Or.inl rfl)) address repeated bound family s
        (fun cells s2 h => sources_substitution V C k₁ k₂ hk ps (needLevelSources ps cells) repeated bound family s2 h)
        havoid
    | unpack ps =>
      exact structural_substitution V C k₁ k₂ hk _ ps (Or.inr (Or.inr rfl)) address repeated bound family s
        (fun cells s2 h => sources_substitution V C k₁ k₂ hk ps (needLevelSources ps cells) repeated bound family s2 h)
        havoid

  /-- CHANNEL SUBSTITUTION, one level's patterns. -/
  theorem sources_substitution (V C : Nat → Prop) (k₁ k₂ : NeedCapabilities EvalM) (hk : AgreeOutside V C k₁ k₂)
      (ps : List NeedPattern) (sources : List (NeedSource Nat)) (repeated : List Ident) (bound : NeedEnv)
      (family : Bool) (s : EvalState) (havoid : Avoids V C (sourcesEvents k₁ ps sources repeated bound family s)) :
      runEval (NeedBinder.bindSources k₁ ps sources repeated bound family) s
        = runEval (NeedBinder.bindSources k₂ ps sources repeated bound family) s
      ∧ sourcesEvents k₁ ps sources repeated bound family s
        = sourcesEvents k₂ ps sources repeated bound family s := by
    cases ps with
    | nil => exact ⟨rfl, rfl⟩
    | cons p rest =>
      simp only [sourcesEvents] at havoid
      have hrest := (avoids_append havoid).2
      simp only [NeedBinder.bindSources, sourcesEvents, runEval_bind, ← hk.allocate,
        ← addressEvents_allocator hk.allocate]
      rcases h1 : runEval (NeedBinder.sourceAddress k₁.allocate (sources.headD .missing)) s
        with ⟨e | address, s1⟩
      · simp
      · simp only [h1] at hrest
        simp only [thenRun_ok]
        obtain ⟨hrun, hev⟩ := one_substitution V C k₁ k₂ hk p address repeated bound family s1
          (avoids_append hrest).1
        rw [← hrun, ← hev]
        rcases h2 : runEval (NeedBinder.bindOne k₁ p address repeated bound family) s1
          with ⟨e | (_ | next), s2⟩
        · simp
        · simp
        · simp only [h2] at hrest
          obtain ⟨hrun', hev'⟩ := sources_substitution V C k₁ k₂ hk rest sources.tail repeated next family s2
            (avoids_append hrest).2
          simp [hrun', hev']
end

/-- (b) RESULTS DEPEND ON THE CHANNELS ONLY THROUGH THE INVOKED CELLS (the roadmap's R3
    obligation (b) in its run-relative form, for a whole head, per channel): two capability
    records with the same allocator whose VALUE demands agree outside `V` and whose CALLABLE
    projections agree outside `C`, when the first run's schedule (`patternsEvents`, the binder's
    actual invocations by `traced_patterns`) demands no VALUE on a cell of `V` and projects no
    CALLABLE on a cell of `C`, produce the SAME outcome, final state and schedule. What a channel
    would answer at a cell the run never invokes on that channel is irrelevant. This says nothing
    about the cell's heap CONTENTS: both runs start from the same state, and another cell's
    channel (e.g. `demandNeed` of an expression cell) may still read them. -/
theorem results_depend_only_on_invoked_cells (V C : Nat → Prop) (k₁ k₂ : NeedCapabilities EvalM)
    (hk : AgreeOutside V C k₁ k₂) (ps : List NeedPattern) (cells : List Nat) (family : Bool) (s : EvalState)
    (havoid : Avoids V C (patternsEvents k₁ ps cells family s)) :
    runEval (NeedBinder.bindPatterns k₁ ps cells family) s = runEval (NeedBinder.bindPatterns k₂ ps cells family) s
    ∧ patternsEvents k₁ ps cells family s = patternsEvents k₂ ps cells family s := by
  simp only [NeedBinder.bindPatterns, NeedBinder.bindLevel, NeedBinder.cardinalityGate, patternsEvents,
    levelEvents] at havoid ⊢
  cases hacc : needAcceptsCardinality ps cells.length
  · exact ⟨rfl, rfl⟩
  · rw [hacc] at havoid
    simp only [↓reduceIte] at havoid
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    exact sources_substitution V C k₁ k₂ hk ps (needLevelSources ps cells) (needRepeatedNames ps) [] family s havoid

/-- The production instance: two pairs of production channels over the one allocator
    `allocateNeed` — the evaluator's `bindingChannels` against any other pair —
    bind every head the same way when they agree wherever the run invokes them. -/
theorem production_results_depend_only_on_invoked_cells (V C : Nat → Prop) (c₁ c₂ : NeedChannels)
    (hv : ∀ a, ¬ V a → c₁.value a = c₂.value a) (hc : ∀ a, ¬ C a → c₁.callable a = c₂.callable a)
    (ps : List NeedPattern) (cells : List Nat) (family : Bool) (s : EvalState)
    (havoid : Avoids V C (patternsEvents c₁.capabilities ps cells family s)) :
    (bindNeedPatterns c₁ ps cells family).runState s = (bindNeedPatterns c₂ ps cells family).runState s :=
  (results_depend_only_on_invoked_cells V C c₁.capabilities c₂.capabilities ⟨rfl, hv, hc, rfl⟩ ps cells family s
    havoid).1

/-- The extreme case: a run whose schedule invokes NO channel (a head of plain, non-repeated
    names, a rejected count, …) binds identically under every pair of production channels. -/
theorem production_uninvoked_channels_are_irrelevant (c₁ c₂ : NeedChannels) (ps : List NeedPattern)
    (cells : List Nat) (family : Bool) (s : EvalState)
    (hnone : ∀ ev ∈ patternsEvents c₁.capabilities ps cells family s, ev.isInvocation = false) :
    (bindNeedPatterns c₁ ps cells family).runState s = (bindNeedPatterns c₂ ps cells family).runState s :=
  production_results_depend_only_on_invoked_cells (fun _ => True) (fun _ => True) c₁ c₂
    (fun _ h => absurd trivial h) (fun _ h => absurd trivial h) ps cells family s
    (fun ev hev => by
      have := hnone ev hev
      cases ev <;> simp_all [Hits, NeedEvent.isInvocation])

/-- THE CALLABLE CHANNEL IS IRRELEVANT TO A HEAD THAT REPEATS NO NAME (NEED-06's binder half):
    two pairs of production channels with the same VALUE demand bind such a head identically,
    whatever their CALLABLE projections. -/
theorem production_callable_channel_is_irrelevant_without_repeated_names (c₁ c₂ : NeedChannels)
    (hv : c₁.value = c₂.value) (ps : List NeedPattern) (cells : List Nat) (family : Bool) (s : EvalState)
    (h : needRepeatedNames ps = []) :
    (bindNeedPatterns c₁ ps cells family).runState s = (bindNeedPatterns c₂ ps cells family).runState s :=
  production_results_depend_only_on_invoked_cells (fun _ => False) (fun _ => True) c₁ c₂
    (fun a _ => congrFun hv a) (fun _ h => absurd trivial h) ps cells family s
    (fun ev hev => by
      have := head_without_repeated_names_projects_no_callable c₁.capabilities ps cells family s h ev hev
      cases ev <;> simp_all [Hits, NeedEvent.isCallable])

/-! ## (b′) The static form: invocations are at inspecting positions or on allocated cells -/

/-- Whether an occurrence INSPECTS its own cell: a literal, a structural pattern, the unpacking
    receiver, or a name the head repeats. A plain, non-repeated name (collecting or not) does
    not. -/
def _root_.KatLang.NeedPattern.inspects (repeated : List Ident) : NeedPattern → Bool
  | .bind name _ => repeated.contains name
  | .metaRef _ => false
  | _ => true

/-- The supplied cells a level's patterns inspect at their own positions (each pattern's source
    cell, when the pattern inspects). -/
def inspectedCells (repeated : List Ident) : List NeedPattern → List (NeedSource Nat) → List Nat
  | [], _ => []
  | p :: rest, sources =>
    (match sources.headD .missing with
      | .cell c => if p.inspects repeated then [c] else []
      | _ => []) ++ inspectedCells repeated rest sources.tail

/-- The cell an allocation event created. -/
def _root_.KatLang.BinderTrace.NeedEvent.allocated? : NeedEvent → Option Nat
  | .ready a => some a
  | .collector a _ => some a
  | .reference _ adapter => some adapter
  | _ => none

/-- Some allocation event of the schedule created cell `a`. -/
def Allocated (events : List NeedEvent) (a : Nat) : Prop :=
  ∃ ev ∈ events, ev.allocated? = some a

/-- The binding so far holds cell `a` for one of the head's repeated names. -/
def RepeatedAt (repeated : List Ident) (bound : NeedEnv) (a : Nat) : Prop :=
  ∃ name, repeated.contains name = true ∧ lookupAssoc name bound = some a

theorem allocated_append_left {l₁ l₂ : List NeedEvent} {a : Nat} (h : Allocated l₁ a) :
    Allocated (l₁ ++ l₂) a := by
  obtain ⟨ev, hev, ha⟩ := h
  exact ⟨ev, List.mem_append_left _ hev, ha⟩

theorem allocated_append_right {l₁ l₂ : List NeedEvent} {a : Nat} (h : Allocated l₂ a) :
    Allocated (l₁ ++ l₂) a := by
  obtain ⟨ev, hev, ha⟩ := h
  exact ⟨ev, List.mem_append_right _ hev, ha⟩

theorem allocated_cons {ev : NeedEvent} {l : List NeedEvent} {a : Nat} (h : Allocated l a) :
    Allocated (ev :: l) a := by
  obtain ⟨ev', hev, ha⟩ := h
  exact ⟨ev', List.mem_cons_of_mem _ hev, ha⟩

/-- Re-binding a name: the name reads its new cell, every other name its old one. -/
theorem lookupAssoc_rebind (n name : Ident) (address : Nat) (bound : NeedEnv) :
    lookupAssoc n (bound.filter (fun entry => entry.fst != name) ++ [(name, address)])
      = if n = name then some address else lookupAssoc n bound := by
  induction bound with
  | nil => simp [lookupAssoc]
  | cons e rest ih =>
    obtain ⟨key, v⟩ := e
    by_cases hk : key = name
    · subst hk
      simp only [List.filter_cons, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, ih, lookupAssoc]
      by_cases hn : n = key <;> simp [hn]
    · have hkb : (key != name) = true := by simpa using hk
      simp only [List.filter_cons, hkb, ↓reduceIte, List.cons_append, lookupAssoc, ih]
      by_cases hn : n = key
      · subst hn; simp [hk]
      · simp [hn]

/-- The repeated cells after a re-binding: the re-bound name's new cell, or an old one. -/
theorem repeatedAt_rebind {repeated : List Ident} {name : Ident} {address a : Nat} {bound : NeedEnv}
    (h : RepeatedAt repeated (bound.filter (fun entry => entry.fst != name) ++ [(name, address)]) a) :
    RepeatedAt repeated bound a ∨ (repeated.contains name = true ∧ a = address) := by
  obtain ⟨n, hn, hl⟩ := h
  rw [lookupAssoc_rebind] at hl
  by_cases he : n = name
  · subst he
    simp only [↓reduceIte, Option.some.injEq] at hl
    exact Or.inr ⟨hn, hl.symm⟩
  · simp only [he, ↓reduceIte] at hl
    exact Or.inl ⟨n, hn, hl⟩

theorem repeatedAt_nil {repeated : List Ident} {a : Nat} : ¬ RepeatedAt repeated [] a := by
  rintro ⟨n, -, hl⟩
  simp [lookupAssoc] at hl

/-- Every event of a repeated occurrence is on the occurrence's own cell or on its
    representative's. -/
theorem repeatedNameEvents_addresses (k : NeedCapabilities EvalM) (address : Nat) (previous? : Option Nat)
    (s : EvalState) : ∀ ev ∈ repeatedNameEvents k address previous? s,
      ev.address = address ∨ previous? = some ev.address := by
  intro ev hev
  simp only [repeatedNameEvents] at hev
  rcases List.mem_cons.mp hev with rfl | hev
  · exact Or.inl rfl
  · rcases h1 : runEval (k.value address) s with ⟨_ | value, s1⟩
    · simp [h1] at hev
    · simp only [h1] at hev
      cases previous? with
      | none => simp at hev
      | some previous =>
        simp only at hev
        rcases List.mem_cons.mp hev with rfl | hev
        · exact Or.inr rfl
        · rcases h2 : runEval (k.value previous) s1 with ⟨_ | before, s2⟩
          · simp [h2] at hev
          · simp only [h2] at hev
            split at hev
            · simp at hev
            · rcases List.mem_cons.mp hev with rfl | hev
              · exact Or.inr rfl
              · rcases h3 : runEval (k.callable previous) s2 with ⟨_ | _, s3⟩
                · simp [h3] at hev
                · simp only [h3, List.mem_singleton] at hev
                  subst hev
                  exact Or.inl rfl

/-- A name occurrence's result: the binding so far, or that binding with the name re-bound to the
    occurrence's cell. -/
theorem bindName_result (k : NeedCapabilities EvalM) (name : Ident) (address : Nat) (repeated : List Ident)
    (bound : NeedEnv) (family : Bool) (s : EvalState) (next : NeedEnv) (s' : EvalState)
    (h : runEval (NeedBinder.bindName k name address repeated bound family) s = (.ok (some next), s')) :
    next = bound ∨ next = bound.filter (fun entry => entry.fst != name) ++ [(name, address)] := by
  by_cases hr : repeated.contains name = true
  · rw [repeated_name_binding k name address repeated bound family s hr] at h
    rcases h1 : runEval (k.value address) s with ⟨e | value, s1⟩
    · simp [h1] at h
    · cases hl : lookupAssoc name bound with
      | none =>
        simp only [h1, hl, Prod.mk.injEq, Except.ok.injEq, Option.some.injEq] at h
        exact Or.inr h.1.symm
      | some previous =>
        rcases h2 : runEval (k.value previous) s1 with ⟨e | before, s2⟩
        · simp [h1, hl, h2] at h
        · cases hbv : (before == value)
          · cases family <;> simp [h1, hl, h2, hbv] at h
          · rcases h3 : runEval (k.callable previous) s2 with ⟨e | first, s3⟩
            · simp [h1, hl, h2, hbv, h3] at h
            · rcases h4 : runEval (k.callable address) s3 with ⟨e | second, s4⟩
              · simp [h1, hl, h2, hbv, h3, h4] at h
              · simp only [h1, hl, h2, hbv, h3, h4, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
                  Prod.mk.injEq] at h
                obtain ⟨hv, -⟩ := h
                unfold repeatedVerdict at hv
                cases first with
                | none =>
                  cases second <;> simp at hv
                  · exact Or.inl hv.symm
                  · exact Or.inr hv.symm
                | some a =>
                  cases second with
                  | none => simp at hv; exact Or.inl hv.symm
                  | some b =>
                    cases hid : sameRepeatedCallableIdentity a b
                    · cases family <;> simp [hid] at hv
                    · simp [hid] at hv; exact Or.inl hv.symm
  · have hr' : repeated.contains name = false := by simpa using hr
    rw [BinderCore.core_plain_name_is_pure k name address repeated bound family hr'] at h
    simp only [runEval_pure, Prod.mk.injEq, Except.ok.injEq, Option.some.injEq] at h
    exact Or.inr h.1.symm

/-- A ready allocation event exists for every cell a structural pattern's items received. -/
theorem ready_loop_cells (k : NeedCapabilities EvalM) (items : List Result) (acc : List Nat)
    (s : EvalState) (cells : List Nat) (s' : EvalState)
    (h : runEval (List.mapM.loop (fun item => k.allocate (.ready (item, Result.valueCount item))) items acc) s
      = (.ok cells, s')) :
    ∀ c ∈ cells, c ∈ acc ∨ NeedEvent.ready c ∈ readyEvents k items s := by
  induction items generalizing acc s with
  | nil =>
    simp only [List.mapM.loop, runEval_pure, Prod.mk.injEq, Except.ok.injEq] at h
    intro c hc
    rw [← h.1] at hc
    exact Or.inl (List.mem_reverse.mp hc)
  | cons item rest ih =>
    simp only [List.mapM.loop, runEval_bind] at h
    simp only [readyEvents]
    rcases h1 : runEval (k.allocate (.ready (item, Result.valueCount item))) s with ⟨e | b, s1⟩
    · simp [h1] at h
    · simp only [h1, thenRun_ok] at h
      intro c hc
      rcases ih (b :: acc) s1 h c hc with hc' | hc'
      · rcases List.mem_cons.mp hc' with rfl | hc'
        · exact Or.inr List.mem_cons_self
        · exact Or.inl hc'
      · exact Or.inr (List.mem_cons_of_mem _ hc')

theorem ready_cells_are_allocated (k : NeedCapabilities EvalM) (items : List Result) (s : EvalState)
    (cells : List Nat) (s' : EvalState) (h : runEval (readyCells k items) s = (.ok cells, s')) :
    ∀ c ∈ cells, Allocated (readyEvents k items s) c := by
  intro c hc
  rcases ready_loop_cells k items [] s cells s' h c hc with hc' | hc'
  · simp at hc'
  · exact ⟨.ready c, hc', rfl⟩

/-- A ready allocation emits only `ready` events. -/
theorem readyEvents_are_allocations (k : NeedCapabilities EvalM) (items : List Result) (s : EvalState) :
    ∀ ev ∈ readyEvents k items s, ev.isInvocation = false := by
  induction items generalizing s with
  | nil => simp [readyEvents]
  | cons item rest ih =>
    simp only [readyEvents]
    rcases runEval (k.allocate (.ready (item, Result.valueCount item))) s with ⟨_ | address, s'⟩
    · simp
    · intro ev hev
      rcases List.mem_cons.mp hev with rfl | hev
      · rfl
      · exact ih s' ev hev

theorem addressEvents_are_allocations (k : NeedCapabilities EvalM) (source : NeedSource Nat) (s : EvalState) :
    ∀ ev ∈ addressEvents k source s, ev.isInvocation = false := by
  cases source with
  | collector slice =>
    simp only [addressEvents]
    rcases runEval (k.allocate (.collector slice)) s with ⟨_ | address, s'⟩ <;>
      simp [NeedEvent.isInvocation]
  | _ => simp [addressEvents]

/-- A cell source of a level's allocation is one of the level's cells. -/
theorem cell_source_mem {ps : List NeedPattern} {cells : List Nat} {c : Nat}
    (h : NeedSource.cell c ∈ needLevelSources ps cells) : c ∈ cells := by
  simp only [needLevelSources, List.mem_map, List.mem_range] at h
  obtain ⟨i, -, hi⟩ := h
  simp only [needSourceAt] at hi
  split at hi
  · cases hi
  · split at hi
    · rename_i cell hcell
      cases hi
      exact List.mem_of_getElem? hcell
    · cases hi

/-- A level with no sources inspects no cell. -/
theorem inspectedCells_nil_sources (repeated : List Ident) (ps : List NeedPattern) :
    inspectedCells repeated ps [] = [] := by
  induction ps with
  | nil => rfl
  | cons q qs ih => simp [inspectedCells, ih]

/-- The cells a level inspects are among its cell sources. -/
theorem inspectedCells_are_cell_sources (repeated : List Ident) (ps : List NeedPattern)
    (sources : List (NeedSource Nat)) : ∀ c ∈ inspectedCells repeated ps sources, NeedSource.cell c ∈ sources := by
  induction ps generalizing sources with
  | nil => simp [inspectedCells]
  | cons p rest ih =>
    intro c hc
    simp only [inspectedCells, List.mem_append] at hc
    rcases hc with hc | hc
    · cases sources with
      | nil => simp at hc
      | cons src tail =>
        cases src with
        | cell c' =>
          by_cases hp : p.inspects repeated = true
          · simp only [List.headD_cons, hp, ↓reduceIte, List.mem_singleton] at hc
            subst hc
            exact List.mem_cons_self
          · simp [hp] at hc
        | collector slice => simp at hc
        | missing => simp at hc
    · cases sources with
      | nil => simp [inspectedCells_nil_sources] at hc
      | cons src tail => exact List.mem_cons_of_mem _ (ih tail c hc)

/-- The cells a nested level inspects were allocated by its parent's ready allocation. -/
theorem nested_inspected_cells_are_allocated (k : NeedCapabilities EvalM) (repeated : List Ident)
    (ps : List NeedPattern) (items : List Result) (s1 : EvalState) (cells : List Nat) (s2 : EvalState)
    (h : runEval (readyCells k items) s1 = (.ok cells, s2)) :
    ∀ c ∈ inspectedCells repeated ps (needLevelSources ps cells), Allocated (readyEvents k items s1) c :=
  fun c hc => ready_cells_are_allocated k items s1 cells s2 h c
    (cell_source_mem (inspectedCells_are_cell_sources repeated ps _ c hc))

/-- The name arm of the core is `bindName`. -/
theorem bindOne_bind_shape (k : NeedCapabilities EvalM) (name : Ident) (collecting : Bool) (address : Nat)
    (repeated : List Ident) (bound : NeedEnv) (family : Bool) :
    NeedBinder.bindOne k (.bind name collecting) address repeated bound family
      = NeedBinder.bindName k name address repeated bound family := rfl

/-- The literal arm's result is the binding so far, unchanged. -/
theorem bindOne_literal_result (k : NeedCapabilities EvalM) (literal : Pattern) (address : Nat)
    (repeated : List Ident) (bound : NeedEnv) (family : Bool) (s : EvalState) (next : NeedEnv) (s' : EvalState)
    (h : runEval (NeedBinder.bindOne k (.literal literal) address repeated bound family) s = (.ok (some next), s')) :
    next = bound := by
  rw [bindOne_literal_shape] at h
  simp only [runEval_bind] at h
  rcases h1 : runEval (k.value address) s with ⟨e | ⟨value, count⟩, s1⟩
  · simp [h1] at h
  · simp only [h1, thenRun_ok, runEval_pure] at h
    by_cases hm : (matchPattern literal value).isSome = true
    · simp only [hm, ↓reduceIte, Prod.mk.injEq, Except.ok.injEq, Option.some.injEq] at h
      exact h.1.symm
    · simp [hm] at h

theorem mem_inspected_tail {repeated : List Ident} {p : NeedPattern} {rest : List NeedPattern}
    {sources : List (NeedSource Nat)} {a : Nat} (h : a ∈ inspectedCells repeated rest sources.tail) :
    a ∈ inspectedCells repeated (p :: rest) sources := by
  simp only [inspectedCells]
  exact List.mem_append_right _ h

/-- THE ORIGIN OF AN INVOCATION, one structural pattern, given the law for its nested level. -/
theorem structural_origin (k : NeedCapabilities EvalM) (p : NeedPattern) (ps : List NeedPattern)
    (hp : p = .sequence ps ∨ p = .list ps ∨ p = .unpack ps) (address : Nat) (repeated : List Ident)
    (bound : NeedEnv) (family : Bool) (s : EvalState)
    (ih : ∀ (cells : List Nat) (s2 : EvalState),
      (∀ ev ∈ sourcesEvents k ps (needLevelSources ps cells) repeated bound family s2, ev.isInvocation = true →
          ev.address ∈ inspectedCells repeated ps (needLevelSources ps cells)
          ∨ Allocated (sourcesEvents k ps (needLevelSources ps cells) repeated bound family s2) ev.address
          ∨ RepeatedAt repeated bound ev.address)
      ∧ (∀ next s', runEval (NeedBinder.bindSources k ps (needLevelSources ps cells) repeated bound family) s2
            = (.ok (some next), s') →
          ∀ a, RepeatedAt repeated next a →
            RepeatedAt repeated bound a ∨ a ∈ inspectedCells repeated ps (needLevelSources ps cells)
            ∨ Allocated (sourcesEvents k ps (needLevelSources ps cells) repeated bound family s2) a)) :
    (∀ ev ∈ oneEvents k p address repeated bound family s, ev.isInvocation = true →
        (p.inspects repeated = true ∧ ev.address = address)
        ∨ Allocated (oneEvents k p address repeated bound family s) ev.address
        ∨ RepeatedAt repeated bound ev.address)
    ∧ (∀ next s', runEval (NeedBinder.bindOne k p address repeated bound family) s = (.ok (some next), s') →
        ∀ a, RepeatedAt repeated next a →
          RepeatedAt repeated bound a ∨ (p.inspects repeated = true ∧ a = address)
          ∨ Allocated (oneEvents k p address repeated bound family s) a) := by
  have hins : p.inspects repeated = true := by rcases hp with rfl | rfl | rfl <;> rfl
  rw [oneEvents_structural_shape k p ps hp]
  constructor
  · intro ev hev hinv
    rcases List.mem_cons.mp hev with rfl | hev'
    · exact Or.inl ⟨hins, rfl⟩
    · refine Or.inr ?_
      rcases h1 : runEval (k.value address) s with ⟨e | ⟨value, count⟩, s1⟩
      · simp [h1] at hev'
      · simp only [h1] at hev' ⊢
        cases hi : structuralItems p value with
        | none => simp [hi] at hev'
        | some items =>
          simp only [hi] at hev' ⊢
          rcases List.mem_append.mp hev' with hr | hs
          · simp [readyEvents_are_allocations k items s1 ev hr] at hinv
          · rcases h2 : runEval (readyCells k items) s1 with ⟨e | cells, s2⟩
            · simp [h2] at hs
            · simp only [h2] at hs ⊢
              by_cases hacc : needAcceptsCardinality ps cells.length = true
              · simp only [hacc, ↓reduceIte] at hs ⊢
                rcases (ih cells s2).1 ev hs hinv with hc | hc | hc
                · exact Or.inl (allocated_cons (allocated_append_left
                    (nested_inspected_cells_are_allocated k repeated ps items s1 cells s2 h2 _ hc)))
                · exact Or.inl (allocated_cons (allocated_append_right hc))
                · exact Or.inr hc
              · simp [hacc] at hs
  · intro next s' h a ha
    rw [bindOne_structural_shape k p ps hp] at h
    simp only [runEval_bind] at h
    rcases h1 : runEval (k.value address) s with ⟨e | ⟨value, count⟩, s1⟩
    · simp [h1] at h
    · simp only [h1, thenRun_ok] at h ⊢
      cases hi : structuralItems p value with
      | none => cases family <;> simp [hi] at h
      | some items =>
        simp only [hi, runEval_bind] at h ⊢
        rcases h2 : runEval (readyCells k items) s1 with ⟨e | cells, s2⟩
        · simp [h2] at h
        · simp only [h2, thenRun_ok, NeedBinder.cardinalityGate] at h ⊢
          by_cases hacc : needAcceptsCardinality ps cells.length = true
          · simp only [hacc, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
            rcases (ih cells s2).2 next s' h a ha with hb | hc | hc
            · exact Or.inl hb
            · exact Or.inr (Or.inr (allocated_cons (allocated_append_left
                (nested_inspected_cells_are_allocated k repeated ps items s1 cells s2 h2 _ hc))))
            · exact Or.inr (Or.inr (allocated_cons (allocated_append_right hc)))
          · have hf : needAcceptsCardinality ps cells.length = false := by simpa using hacc
            cases family <;> simp [hf] at h

mutual
  /-- THE ORIGIN OF AN INVOCATION, one pattern: every VALUE or CALLABLE invocation is on the
      pattern's own cell (when it inspects it), on a cell its run allocated, or on a cell the
      binding so far holds for a repeated name; and its result binds a repeated name only to such
      a cell. -/
  theorem one_origin (k : NeedCapabilities EvalM) (p : NeedPattern) (address : Nat) (repeated : List Ident)
      (bound : NeedEnv) (family : Bool) (s : EvalState) :
      (∀ ev ∈ oneEvents k p address repeated bound family s, ev.isInvocation = true →
          (p.inspects repeated = true ∧ ev.address = address)
          ∨ Allocated (oneEvents k p address repeated bound family s) ev.address
          ∨ RepeatedAt repeated bound ev.address)
      ∧ (∀ next s', runEval (NeedBinder.bindOne k p address repeated bound family) s = (.ok (some next), s') →
          ∀ a, RepeatedAt repeated next a →
            RepeatedAt repeated bound a ∨ (p.inspects repeated = true ∧ a = address)
            ∨ Allocated (oneEvents k p address repeated bound family s) a) := by
    cases p with
    | bind name collecting =>
      constructor
      · intro ev hev _
        simp only [oneEvents, nameEvents] at hev
        split at hev
        · rename_i hr
          rcases repeatedNameEvents_addresses k address _ s ev hev with ha | ha
          · exact Or.inl ⟨hr, ha⟩
          · exact Or.inr (Or.inr ⟨name, hr, ha⟩)
        · simp at hev
      · intro next s' h a ha
        rw [bindOne_bind_shape] at h
        rcases bindName_result k name address repeated bound family s next s' h with rfl | rfl
        · exact Or.inl ha
        · rcases repeatedAt_rebind ha with ha | ⟨hr, rfl⟩
          · exact Or.inl ha
          · exact Or.inr (Or.inl ⟨hr, rfl⟩)
    | literal literal =>
      constructor
      · intro ev hev _
        simp only [oneEvents, List.mem_singleton] at hev
        subst hev
        exact Or.inl ⟨rfl, rfl⟩
      · intro next s' h a ha
        rw [bindOne_literal_result k literal address repeated bound family s next s' h] at ha
        exact Or.inl ha
    | metaRef name =>
      constructor
      · intro ev hev hinv
        simp only [oneEvents] at hev ⊢
        rcases h1 : runEval (k.reference address) s with ⟨e | adapter, s1⟩
        · simp [h1] at hev
        · simp only [h1] at hev ⊢
          rcases List.mem_cons.mp hev with rfl | hev
          · simp [NeedEvent.isInvocation] at hinv
          · simp only [nameEvents] at hev
            split at hev
            · rename_i hr
              rcases repeatedNameEvents_addresses k adapter _ s1 ev hev with ha | ha
              · exact Or.inr (Or.inl ⟨.reference address adapter, List.mem_cons_self,
                  by simp [ha, NeedEvent.allocated?]⟩)
              · exact Or.inr (Or.inr ⟨name, hr, ha⟩)
            · simp at hev
      · intro next s' h a ha
        simp only [NeedBinder.bindOne, runEval_bind] at h
        simp only [oneEvents]
        rcases h1 : runEval (k.reference address) s with ⟨e | adapter, s1⟩
        · simp [h1] at h
        · simp only [h1, thenRun_ok] at h ⊢
          rcases bindName_result k name adapter repeated bound family s1 next s' h with rfl | rfl
          · exact Or.inl ha
          · rcases repeatedAt_rebind ha with ha | ⟨hr, rfl⟩
            · exact Or.inl ha
            · exact Or.inr (Or.inr ⟨.reference address a, List.mem_cons_self, rfl⟩)
    | sequence ps =>
      exact structural_origin k _ ps (Or.inl rfl) address repeated bound family s
        (fun cells s2 => sources_origin k ps (needLevelSources ps cells) repeated bound family s2)
    | list ps =>
      exact structural_origin k _ ps (Or.inr (Or.inl rfl)) address repeated bound family s
        (fun cells s2 => sources_origin k ps (needLevelSources ps cells) repeated bound family s2)
    | unpack ps =>
      exact structural_origin k _ ps (Or.inr (Or.inr rfl)) address repeated bound family s
        (fun cells s2 => sources_origin k ps (needLevelSources ps cells) repeated bound family s2)

  /-- THE ORIGIN OF AN INVOCATION, one level's patterns over their sources. -/
  theorem sources_origin (k : NeedCapabilities EvalM) (ps : List NeedPattern) (sources : List (NeedSource Nat))
      (repeated : List Ident) (bound : NeedEnv) (family : Bool) (s : EvalState) :
      (∀ ev ∈ sourcesEvents k ps sources repeated bound family s, ev.isInvocation = true →
          ev.address ∈ inspectedCells repeated ps sources
          ∨ Allocated (sourcesEvents k ps sources repeated bound family s) ev.address
          ∨ RepeatedAt repeated bound ev.address)
      ∧ (∀ next s', runEval (NeedBinder.bindSources k ps sources repeated bound family) s = (.ok (some next), s') →
          ∀ a, RepeatedAt repeated next a →
            RepeatedAt repeated bound a ∨ a ∈ inspectedCells repeated ps sources
            ∨ Allocated (sourcesEvents k ps sources repeated bound family s) a) := by
    cases ps with
    | nil =>
      constructor
      · intro ev hev
        simp [sourcesEvents] at hev
      · intro next s' h a ha
        simp only [NeedBinder.bindSources, runEval_pure, Prod.mk.injEq, Except.ok.injEq,
          Option.some.injEq] at h
        rw [← h.1] at ha
        exact Or.inl ha
    | cons p rest =>
      have haddr : ∀ address s1,
          runEval (NeedBinder.sourceAddress k.allocate (sources.headD .missing)) s = (.ok address, s1) →
          (p.inspects repeated = true → address ∈ inspectedCells repeated (p :: rest) sources)
          ∨ Allocated (addressEvents k (sources.headD .missing) s) address := by
        intro address s1 h
        cases hsrc : sources.headD .missing with
        | cell c =>
          rw [hsrc] at h
          simp only [NeedBinder.sourceAddress, runEval_pure, Prod.mk.injEq, Except.ok.injEq] at h
          refine Or.inl (fun hp => ?_)
          simp only [inspectedCells, hsrc, hp, ↓reduceIte, List.mem_append, List.mem_singleton]
          exact Or.inl h.1.symm
        | collector slice =>
          rw [hsrc] at h
          simp only [NeedBinder.sourceAddress] at h
          refine Or.inr ⟨.collector address slice, ?_, rfl⟩
          simp [addressEvents, h]
        | missing =>
          rw [hsrc] at h
          simp [NeedBinder.sourceAddress] at h
      constructor
      · intro ev hev hinv
        simp only [sourcesEvents] at hev ⊢
        rcases List.mem_append.mp hev with hev | hev
        · simp [addressEvents_are_allocations k _ s ev hev] at hinv
        · rcases h1 : runEval (NeedBinder.sourceAddress k.allocate (sources.headD .missing)) s
            with ⟨e | address, s1⟩
          · simp only [h1, List.not_mem_nil] at hev
          · simp only [h1] at hev ⊢
            have hA := haddr address s1 h1
            rcases List.mem_append.mp hev with hev | hev
            · rcases (one_origin k p address repeated bound family s1).1 ev hev hinv with ⟨hp, hea⟩ | hc | hc
              · rw [hea]
                rcases hA with hA | hA
                · exact Or.inl (hA hp)
                · exact Or.inr (Or.inl (allocated_append_left hA))
              · exact Or.inr (Or.inl (allocated_append_right (allocated_append_left hc)))
              · exact Or.inr (Or.inr hc)
            · rcases h2 : runEval (NeedBinder.bindOne k p address repeated bound family) s1
                with ⟨e | (_ | mid), s2⟩
              · simp [h2] at hev
              · simp [h2] at hev
              · simp only [h2] at hev ⊢
                rcases (sources_origin k rest sources.tail repeated mid family s2).1 ev hev hinv with hc | hc | hc
                · exact Or.inl (mem_inspected_tail hc)
                · exact Or.inr (Or.inl (allocated_append_right (allocated_append_right hc)))
                · rcases (one_origin k p address repeated bound family s1).2 mid s2 h2 _ hc
                    with hb | ⟨hp, hea⟩ | hc'
                  · exact Or.inr (Or.inr hb)
                  · rw [hea]
                    rcases hA with hA | hA
                    · exact Or.inl (hA hp)
                    · exact Or.inr (Or.inl (allocated_append_left hA))
                  · exact Or.inr (Or.inl (allocated_append_right (allocated_append_left hc')))
      · intro next s' h a ha
        simp only [NeedBinder.bindSources, runEval_bind] at h
        simp only [sourcesEvents]
        rcases h1 : runEval (NeedBinder.sourceAddress k.allocate (sources.headD .missing)) s
          with ⟨e | address, s1⟩
        · simp only [h1, thenRun_error] at h <;> simp at h
        · simp only [h1, thenRun_ok] at h ⊢
          have hA := haddr address s1 h1
          rcases h2 : runEval (NeedBinder.bindOne k p address repeated bound family) s1
            with ⟨e | (_ | mid), s2⟩
          · simp [h2] at h
          · simp [h2] at h
          · simp only [h2, thenRun_ok] at h ⊢
            rcases (sources_origin k rest sources.tail repeated mid family s2).2 next s' h a ha with hb | hc | hc
            · rcases (one_origin k p address repeated bound family s1).2 mid s2 h2 a hb with hb' | ⟨hp, hea⟩ | hc'
              · exact Or.inl hb'
              · subst hea
                rcases hA with hA | hA
                · exact Or.inr (Or.inl (hA hp))
                · exact Or.inr (Or.inr (allocated_append_left hA))
              · exact Or.inr (Or.inr (allocated_append_right (allocated_append_left hc')))
            · exact Or.inr (Or.inl (mem_inspected_tail hc))
            · exact Or.inr (Or.inr (allocated_append_right (allocated_append_right hc)))
end

/-- (b′) THE STATIC FORM — WHERE A HEAD INVOKES ITS CHANNELS: every VALUE demand and CALLABLE
    projection of a whole head is on a supplied cell at an INSPECTING top-level position (a
    literal, a structural pattern, the unpacking receiver, or a repeated name — aliasing
    included: a cell supplied at an inspecting position is inspected whatever else it is bound
    to) or on a cell the run itself allocated (a collector or a ready item cell). -/
theorem invoked_cells_are_inspected_or_allocated (k : NeedCapabilities EvalM) (ps : List NeedPattern)
    (cells : List Nat) (family : Bool) (s : EvalState) :
    ∀ ev ∈ patternsEvents k ps cells family s, ev.isInvocation = true →
      ev.address ∈ inspectedCells (needRepeatedNames ps) ps (needLevelSources ps cells)
      ∨ Allocated (patternsEvents k ps cells family s) ev.address := by
  intro ev hev hinv
  simp only [patternsEvents, levelEvents] at hev ⊢
  by_cases hacc : needAcceptsCardinality ps cells.length = true
  · simp only [hacc, ↓reduceIte] at hev ⊢
    rcases (sources_origin k ps (needLevelSources ps cells) (needRepeatedNames ps) [] family s).1 ev hev hinv
      with hc | hc | hc
    · exact Or.inl hc
    · exact Or.inr hc
    · exact absurd hc repeatedAt_nil
  · simp [hacc] at hev

/-- (b′) MIXED-HEAD NONINTERFERENCE, static form: the VALUE and CALLABLE channels at a set of
    supplied cells `P` that occur only at plain, non-repeated positions of the head (plain or
    collecting names; aliasing with an inspecting position excluded by `hplain`) and that no
    allocation of the run reuses (`hfresh`) are irrelevant to the binding — outcome, final state
    and schedule. -/
theorem plain_cells_are_channel_irrelevant (P : Nat → Prop) (k₁ k₂ : NeedCapabilities EvalM)
    (hk : AgreeOutside P P k₁ k₂) (ps : List NeedPattern) (cells : List Nat) (family : Bool) (s : EvalState)
    (hplain : ∀ c, P c → c ∉ inspectedCells (needRepeatedNames ps) ps (needLevelSources ps cells))
    (hfresh : ∀ c, P c → ¬ Allocated (patternsEvents k₁ ps cells family s) c) :
    runEval (NeedBinder.bindPatterns k₁ ps cells family) s = runEval (NeedBinder.bindPatterns k₂ ps cells family) s
    ∧ patternsEvents k₁ ps cells family s = patternsEvents k₂ ps cells family s :=
  results_depend_only_on_invoked_cells P P k₁ k₂ hk ps cells family s (fun ev hev hhit => by
    obtain ⟨hinv, hP⟩ : ev.isInvocation = true ∧ P ev.address := by
      cases ev with
      | value a => exact ⟨rfl, hhit⟩
      | callable a => exact ⟨rfl, hhit⟩
      | collector a slice => simp [Hits] at hhit
      | ready a => simp [Hits] at hhit
      | expression a => simp [Hits] at hhit
      | reference a adapter => simp [Hits] at hhit
    rcases invoked_cells_are_inspected_or_allocated k₁ ps cells family s ev hev hinv with hc | hc
    · exact hplain _ hP hc
    · exact hfresh _ hP hc)

/-- The production instance of the static form: production channels that differ only at supplied
    cells occurring at plain, non-repeated positions, and never reused by an allocation of the
    run, bind the head identically. -/
theorem production_plain_cells_are_channel_irrelevant (P : Nat → Prop) (c₁ c₂ : NeedChannels)
    (hv : ∀ a, ¬ P a → c₁.value a = c₂.value a) (hc : ∀ a, ¬ P a → c₁.callable a = c₂.callable a)
    (ps : List NeedPattern) (cells : List Nat) (family : Bool) (s : EvalState)
    (hplain : ∀ c, P c → c ∉ inspectedCells (needRepeatedNames ps) ps (needLevelSources ps cells))
    (hfresh : ∀ c, P c → ¬ Allocated (patternsEvents c₁.capabilities ps cells family s) c) :
    (bindNeedPatterns c₁ ps cells family).runState s = (bindNeedPatterns c₂ ps cells family).runState s :=
  (plain_cells_are_channel_irrelevant P c₁.capabilities c₂.capabilities ⟨rfl, hv, hc, rfl⟩ ps cells family s
    hplain hfresh).1

/-! ## (c) Mode correspondence: a clause attempt is the ordinary binding up to its first incompatibility -/

mutual
  /-- No literal pattern anywhere in the pattern (every ordinary signature). -/
  def _root_.KatLang.NeedPattern.literalFree : NeedPattern → Bool
    | .literal _ => false
    | .bind _ _ => true
    | .metaRef _ => true
    | .sequence ps => literalFreeList ps
    | .list ps => literalFreeList ps
    | .unpack ps => literalFreeList ps

  /-- No literal pattern anywhere in the list. -/
  def literalFreeList : List NeedPattern → Bool
    | [] => true
    | p :: ps => p.literalFree && literalFreeList ps
end

/-- The four incompatibility errors of an ordinary binding, classified by VALUE: unequal repeated
    values, incompatible repeated callable identities, a structural value of the wrong kind, and
    a level's unaccepted count (top-level or nested). A channel may raise an error of the same
    value; the relation `ModeAgree` then records it as a raised error, the same in both modes. -/
inductive Incompatibility : Error → Prop
  | repeatedValue (name : Ident) : Incompatibility (Error.withContext (repeatedParameterContext name) Error.badArity)
  | repeatedIdentity : Incompatibility (Error.typeMismatch "Repeated bind equality requires the same callable identity")
  | kind (pattern : ParameterPattern) (value : Result) : Incompatibility (structuralPatternKindMismatch pattern value)
  | count (minimum supplied : Nat) : Incompatibility (Error.arityMismatch minimum supplied)

/-- How a clause attempt's outcome relates to the ordinary binding's: the same binding, the same
    raised error, the same non-match (a literal mismatch), or a non-match where the ordinary
    binding raises an incompatibility. -/
inductive ModeAgree : Except Error (Option NeedEnv) → Except Error (Option NeedEnv) → Prop
  | bound (env : NeedEnv) : ModeAgree (.ok (some env)) (.ok (some env))
  | raised (e : Error) : ModeAgree (.error e) (.error e)
  | incompatible (e : Error) (h : Incompatibility e) : ModeAgree (.ok none) (.error e)
  | nonMatch : ModeAgree (.ok none) (.ok none)

/-- Equal outcomes always agree. -/
theorem ModeAgree.refl : ∀ r : Except Error (Option NeedEnv), ModeAgree r r
  | .ok (some env) => .bound env
  | .ok none => .nonMatch
  | .error e => .raised e

/-- The repeated-name verdict in the two modes. -/
theorem verdict_modes (name : Ident) (address : Nat) (bound : NeedEnv) (first second : Option Algorithm) :
    ModeAgree (repeatedVerdict name address bound true first second)
      (repeatedVerdict name address bound false first second) := by
  unfold repeatedVerdict
  cases first with
  | none => cases second <;> exact .bound _
  | some a =>
    cases second with
    | none => exact .bound _
    | some b =>
      cases hid : sameRepeatedCallableIdentity a b
      · simp only [hid, Bool.not_false, Bool.false_eq_true, ↓reduceIte]
        exact .incompatible _ .repeatedIdentity
      · simp only [hid, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Option.isSome_some, Bool.true_or]
        exact .bound _

/-- The two modes of one name occurrence. -/
theorem name_modes (k : NeedCapabilities EvalM) (name : Ident) (address : Nat) (repeated : List Ident)
    (bound : NeedEnv) (s : EvalState) :
    (runEval (NeedBinder.bindName k name address repeated bound true) s).2
      = (runEval (NeedBinder.bindName k name address repeated bound false) s).2
    ∧ ModeAgree (runEval (NeedBinder.bindName k name address repeated bound true) s).1
        (runEval (NeedBinder.bindName k name address repeated bound false) s).1 := by
  by_cases hr : repeated.contains name = true
  · rw [repeated_name_binding k name address repeated bound true s hr,
      repeated_name_binding k name address repeated bound false s hr]
    rcases h1 : runEval (k.value address) s with ⟨e | value, s1⟩
    · simp only
      exact ⟨by trivial, .raised e⟩
    · cases hl : lookupAssoc name bound with
      | none =>
        simp only
        exact ⟨by trivial, .bound _⟩
      | some previous =>
        rcases h2 : runEval (k.value previous) s1 with ⟨e | before, s2⟩
        · simp only [h2]
          exact ⟨by trivial, .raised e⟩
        · cases hbv : (before == value)
          · simp only [h2, hbv, Bool.not_false, Bool.false_eq_true, ↓reduceIte]
            exact ⟨by trivial, .incompatible _ (.repeatedValue name)⟩
          · rcases h3 : runEval (k.callable previous) s2 with ⟨e | first, s3⟩
            · simp only [h2, hbv, h3, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
              exact ⟨by trivial, .raised e⟩
            · rcases h4 : runEval (k.callable address) s3 with ⟨e | second, s4⟩
              · simp only [h2, hbv, h3, h4, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
                exact ⟨by trivial, .raised e⟩
              · simp only [h2, hbv, h3, h4, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
                exact ⟨by trivial, verdict_modes name address bound first second⟩
  · have hr' : repeated.contains name = false := by simpa using hr
    rw [BinderCore.core_plain_name_is_pure k name address repeated bound true hr',
      BinderCore.core_plain_name_is_pure k name address repeated bound false hr']
    exact ⟨rfl, .bound _⟩

/-- The two modes of one structural pattern, given the law for its nested level. -/
theorem structural_modes (k : NeedCapabilities EvalM) (p : NeedPattern) (ps : List NeedPattern)
    (hp : p = .sequence ps ∨ p = .list ps ∨ p = .unpack ps) (address : Nat) (repeated : List Ident)
    (bound : NeedEnv) (s : EvalState)
    (ih : ∀ (cells : List Nat) (s2 : EvalState),
      (runEval (NeedBinder.bindSources k ps (needLevelSources ps cells) repeated bound true) s2).2
        = (runEval (NeedBinder.bindSources k ps (needLevelSources ps cells) repeated bound false) s2).2
      ∧ ModeAgree (runEval (NeedBinder.bindSources k ps (needLevelSources ps cells) repeated bound true) s2).1
          (runEval (NeedBinder.bindSources k ps (needLevelSources ps cells) repeated bound false) s2).1
      ∧ sourcesEvents k ps (needLevelSources ps cells) repeated bound true s2
        = sourcesEvents k ps (needLevelSources ps cells) repeated bound false s2) :
    (runEval (NeedBinder.bindOne k p address repeated bound true) s).2
      = (runEval (NeedBinder.bindOne k p address repeated bound false) s).2
    ∧ ModeAgree (runEval (NeedBinder.bindOne k p address repeated bound true) s).1
        (runEval (NeedBinder.bindOne k p address repeated bound false) s).1
    ∧ oneEvents k p address repeated bound true s = oneEvents k p address repeated bound false s := by
  rw [bindOne_structural_shape k p ps hp _ _ _ true, bindOne_structural_shape k p ps hp _ _ _ false,
    oneEvents_structural_shape k p ps hp _ _ _ true, oneEvents_structural_shape k p ps hp _ _ _ false]
  simp only [runEval_bind]
  rcases h1 : runEval (k.value address) s with ⟨e | ⟨value, count⟩, s1⟩
  · simp only [thenRun_error]
    exact ⟨by trivial, .raised e, by trivial⟩
  · simp only [thenRun_ok]
    cases hi : structuralItems p value with
    | none =>
      simp only [↓reduceIte, runEval_pure, runEval_throw, Bool.false_eq_true]
      exact ⟨by trivial, .incompatible _ (.kind _ _), by trivial⟩
    | some items =>
      simp only [runEval_bind]
      rcases h2 : runEval (readyCells k items) s1 with ⟨e | cells, s2⟩
      · simp only [thenRun_error]
        exact ⟨by trivial, .raised e, by trivial⟩
      · simp only [thenRun_ok, NeedBinder.cardinalityGate]
        cases hacc : needAcceptsCardinality ps cells.length
        · simp only [Bool.not_false, ↓reduceIte, runEval_pure, runEval_throw, Bool.false_eq_true]
          exact ⟨by trivial, .incompatible _ (.count _ _), by trivial⟩
        · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          obtain ⟨hs, hm, he⟩ := ih cells s2
          exact ⟨hs, hm, by rw [he]⟩


mutual
  /-- The two modes of one pattern: same final state, related outcomes, same schedule. -/
  theorem one_modes (k : NeedCapabilities EvalM) (p : NeedPattern) (address : Nat)
      (repeated : List Ident) (bound : NeedEnv) (s : EvalState) :
      (runEval (NeedBinder.bindOne k p address repeated bound true) s).2
        = (runEval (NeedBinder.bindOne k p address repeated bound false) s).2
      ∧ ModeAgree (runEval (NeedBinder.bindOne k p address repeated bound true) s).1
          (runEval (NeedBinder.bindOne k p address repeated bound false) s).1
      ∧ oneEvents k p address repeated bound true s = oneEvents k p address repeated bound false s := by
    cases p with
    | bind name collecting =>
      obtain ⟨h1, h2⟩ := name_modes k name address repeated bound s
      exact ⟨h1, h2, rfl⟩
    | literal literal =>
      rw [bindOne_literal_shape k literal address repeated bound true,
        bindOne_literal_shape k literal address repeated bound false]
      exact ⟨rfl, ModeAgree.refl _, rfl⟩
    | metaRef name =>
      simp only [NeedBinder.bindOne, oneEvents, runEval_bind]
      rcases h1 : runEval (k.reference address) s with ⟨e | adapter, s1⟩
      · simp only [thenRun_error]
        exact ⟨by trivial, .raised e, by trivial⟩
      · simp only [thenRun_ok]
        obtain ⟨hs, hm⟩ := name_modes k name adapter repeated bound s1
        exact ⟨hs, hm, by trivial⟩
    | sequence ps =>
      exact structural_modes k _ ps (Or.inl rfl) address repeated bound s
        (fun cells s2 => sources_modes k ps (needLevelSources ps cells) repeated bound s2)
    | list ps =>
      exact structural_modes k _ ps (Or.inr (Or.inl rfl)) address repeated bound s
        (fun cells s2 => sources_modes k ps (needLevelSources ps cells) repeated bound s2)
    | unpack ps =>
      exact structural_modes k _ ps (Or.inr (Or.inr rfl)) address repeated bound s
        (fun cells s2 => sources_modes k ps (needLevelSources ps cells) repeated bound s2)

  /-- The two modes of one level's patterns. -/
  theorem sources_modes (k : NeedCapabilities EvalM) (ps : List NeedPattern) (sources : List (NeedSource Nat))
      (repeated : List Ident) (bound : NeedEnv) (s : EvalState) :
      (runEval (NeedBinder.bindSources k ps sources repeated bound true) s).2
        = (runEval (NeedBinder.bindSources k ps sources repeated bound false) s).2
      ∧ ModeAgree (runEval (NeedBinder.bindSources k ps sources repeated bound true) s).1
          (runEval (NeedBinder.bindSources k ps sources repeated bound false) s).1
      ∧ sourcesEvents k ps sources repeated bound true s = sourcesEvents k ps sources repeated bound false s := by
    cases ps with
    | nil => exact ⟨rfl, .bound _, rfl⟩
    | cons p rest =>
      simp only [NeedBinder.bindSources, sourcesEvents, runEval_bind]
      rcases h1 : runEval (NeedBinder.sourceAddress k.allocate (sources.headD .missing)) s with ⟨e | address, s1⟩
      · simp only [thenRun_error]
        exact ⟨by trivial, .raised e, by trivial⟩
      · simp only [thenRun_ok]
        obtain ⟨hs, hm, he⟩ := one_modes k p address repeated bound s1
        rw [he]
        rcases hT : runEval (NeedBinder.bindOne k p address repeated bound true) s1 with ⟨rT, sT⟩
        rcases hF : runEval (NeedBinder.bindOne k p address repeated bound false) s1 with ⟨rF, sF⟩
        rw [hT, hF] at hs hm
        simp only at hs hm
        subst hs
        cases hm with
        | bound env =>
          obtain ⟨hs', hm', he'⟩ := sources_modes k rest sources.tail repeated env sT
          simp only [thenRun_ok]
          exact ⟨hs', hm', by rw [he']⟩
        | raised e =>
          simp only [thenRun_error]
          exact ⟨by trivial, .raised e, by trivial⟩
        | incompatible e hinc =>
          simp only [thenRun_ok, thenRun_error]
          exact ⟨by trivial, .incompatible e hinc, by trivial⟩
        | nonMatch =>
          simp only [thenRun_ok]
          exact ⟨by trivial, .nonMatch, by trivial⟩
end

/-- A non-match on the attempt side is an incompatibility error or the same non-match (a literal
    mismatch) on the ordinary side. -/
theorem ModeAgree.of_non_match {a b : Except Error (Option NeedEnv)} (h : ModeAgree a b)
    (ha : a = .ok none) : (∃ e, Incompatibility e ∧ b = .error e) ∨ b = .ok none := by
  cases h with
  | bound env => cases ha
  | raised e => cases ha
  | incompatible e hinc => exact Or.inl ⟨e, hinc, rfl⟩
  | nonMatch => exact Or.inr rfl

/-- WHERE THE MODES DIFFER: differing outcomes are a non-match against an incompatibility error. -/
theorem ModeAgree.of_differing {a b : Except Error (Option NeedEnv)} (h : ModeAgree a b) (hne : a ≠ b) :
    a = .ok none ∧ ∃ e, Incompatibility e ∧ b = .error e := by
  cases h with
  | bound env => exact absurd rfl hne
  | raised e => exact absurd rfl hne
  | incompatible e hinc => exact ⟨rfl, e, hinc, rfl⟩
  | nonMatch => exact absurd rfl hne

/-- (c) A CLAUSE ATTEMPT IS THE ORDINARY BINDING UP TO ITS FIRST INCOMPATIBILITY (the roadmap's R3
    obligation (c), whole head, EVERY head): binding in family mode and in ordinary mode performs
    the same invocations in the same order (equal schedules), reaches the same final state, and
    gives related outcomes — the same binding, the same raised error, the same non-match (a
    literal mismatch), or a non-match where the ordinary binding raises one of the four
    incompatibility errors. The outcomes differ ONLY in that last case
    (`production_modes_differ_only_at_an_incompatibility`). -/
theorem family_attempt_is_the_ordinary_binding (k : NeedCapabilities EvalM) (ps : List NeedPattern)
    (cells : List Nat) (s : EvalState) :
    (runEval (NeedBinder.bindPatterns k ps cells true) s).2 = (runEval (NeedBinder.bindPatterns k ps cells false) s).2
    ∧ ModeAgree (runEval (NeedBinder.bindPatterns k ps cells true) s).1
        (runEval (NeedBinder.bindPatterns k ps cells false) s).1
    ∧ patternsEvents k ps cells true s = patternsEvents k ps cells false s := by
  simp only [NeedBinder.bindPatterns, NeedBinder.bindLevel, NeedBinder.cardinalityGate, patternsEvents,
    levelEvents]
  cases hacc : needAcceptsCardinality ps cells.length
  · simp only [Bool.not_false, ↓reduceIte, runEval_pure, runEval_throw, Bool.false_eq_true]
    exact ⟨by trivial, .incompatible _ (.count _ _), by trivial⟩
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    exact sources_modes k ps (needLevelSources ps cells) (needRepeatedNames ps) [] s

/-- At the production binder, for EVERY head: when a clause attempt and the ordinary binding
    disagree, the attempt is a non-match and the ordinary binding raised one of the four
    incompatibility errors, in the same final state. -/
theorem production_modes_differ_only_at_an_incompatibility (c : NeedChannels) (ps : List NeedPattern)
    (cells : List Nat) (s : EvalState)
    (hne : ((bindNeedPatterns c ps cells true).runState s).1 ≠ ((bindNeedPatterns c ps cells false).runState s).1) :
    ((bindNeedPatterns c ps cells true).runState s).1 = .ok none
    ∧ (∃ e, Incompatibility e ∧ ((bindNeedPatterns c ps cells false).runState s).1 = .error e)
    ∧ ((bindNeedPatterns c ps cells true).runState s).2 = ((bindNeedPatterns c ps cells false).runState s).2 := by
  obtain ⟨hs, hm, -⟩ := family_attempt_is_the_ordinary_binding c.capabilities ps cells s
  obtain ⟨ht, e, hinc, hf⟩ := hm.of_differing hne
  exact ⟨ht, ⟨e, hinc, hf⟩, hs⟩

/-! ### Literal-free heads: the ordinary binding is never a non-match -/

theorem verdict_ordinary_is_never_a_non_match (name : Ident) (address : Nat) (bound : NeedEnv)
    (first second : Option Algorithm) : repeatedVerdict name address bound false first second ≠ .ok none := by
  unfold repeatedVerdict
  cases first with
  | none => cases second <;> simp
  | some a =>
    cases second with
    | none => simp
    | some b => cases hid : sameRepeatedCallableIdentity a b <;> simp [hid]

theorem name_ordinary_is_never_a_non_match (k : NeedCapabilities EvalM) (name : Ident) (address : Nat)
    (repeated : List Ident) (bound : NeedEnv) (s : EvalState) :
    (runEval (NeedBinder.bindName k name address repeated bound false) s).1 ≠ .ok none := by
  by_cases hr : repeated.contains name = true
  · rw [repeated_name_binding k name address repeated bound false s hr]
    rcases h1 : runEval (k.value address) s with ⟨e | value, s1⟩
    · simp
    · cases hl : lookupAssoc name bound with
      | none => simp
      | some previous =>
        rcases h2 : runEval (k.value previous) s1 with ⟨e | before, s2⟩
        · simp [h2]
        · cases hbv : (before == value)
          · simp [h2, hbv]
          · rcases h3 : runEval (k.callable previous) s2 with ⟨e | first, s3⟩
            · simp [h2, hbv, h3]
            · rcases h4 : runEval (k.callable address) s3 with ⟨e | second, s4⟩
              · simp [h2, hbv, h3, h4]
              · simp only [h2, hbv, h3, h4, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
                exact verdict_ordinary_is_never_a_non_match name address bound first second
  · have hr' : repeated.contains name = false := by simpa using hr
    rw [BinderCore.core_plain_name_is_pure k name address repeated bound false hr']
    simp

theorem structural_ordinary_is_never_a_non_match (k : NeedCapabilities EvalM) (p : NeedPattern)
    (ps : List NeedPattern) (hp : p = .sequence ps ∨ p = .list ps ∨ p = .unpack ps) (address : Nat)
    (repeated : List Ident) (bound : NeedEnv) (s : EvalState)
    (ih : ∀ (cells : List Nat) (s2 : EvalState),
      (runEval (NeedBinder.bindSources k ps (needLevelSources ps cells) repeated bound false) s2).1 ≠ .ok none) :
    (runEval (NeedBinder.bindOne k p address repeated bound false) s).1 ≠ .ok none := by
  rw [bindOne_structural_shape k p ps hp]
  simp only [runEval_bind]
  rcases h1 : runEval (k.value address) s with ⟨e | ⟨value, count⟩, s1⟩
  · simp
  · simp only [thenRun_ok]
    cases hi : structuralItems p value with
    | none => simp
    | some items =>
      simp only [runEval_bind]
      rcases h2 : runEval (readyCells k items) s1 with ⟨e | cells, s2⟩
      · simp
      · simp only [thenRun_ok, NeedBinder.cardinalityGate]
        cases hacc : needAcceptsCardinality ps cells.length
        · simp
        · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          exact ih cells s2

mutual
  theorem one_ordinary_is_never_a_non_match (k : NeedCapabilities EvalM) (p : NeedPattern) (address : Nat)
      (repeated : List Ident) (bound : NeedEnv) (s : EvalState) (hlf : p.literalFree = true) :
      (runEval (NeedBinder.bindOne k p address repeated bound false) s).1 ≠ .ok none := by
    cases p with
    | bind name collecting =>
      rw [bindOne_bind_shape]
      exact name_ordinary_is_never_a_non_match k name address repeated bound s
    | literal literal => simp [NeedPattern.literalFree] at hlf
    | metaRef name =>
      simp only [NeedBinder.bindOne, runEval_bind]
      rcases h1 : runEval (k.reference address) s with ⟨e | adapter, s1⟩
      · simp
      · simp only [thenRun_ok]
        exact name_ordinary_is_never_a_non_match k name adapter repeated bound s1
    | sequence ps =>
      simp only [NeedPattern.literalFree] at hlf
      exact structural_ordinary_is_never_a_non_match k _ ps (Or.inl rfl) address repeated bound s
        (fun cells s2 => sources_ordinary_is_never_a_non_match k ps (needLevelSources ps cells) repeated bound s2 hlf)
    | list ps =>
      simp only [NeedPattern.literalFree] at hlf
      exact structural_ordinary_is_never_a_non_match k _ ps (Or.inr (Or.inl rfl)) address repeated bound s
        (fun cells s2 => sources_ordinary_is_never_a_non_match k ps (needLevelSources ps cells) repeated bound s2 hlf)
    | unpack ps =>
      simp only [NeedPattern.literalFree] at hlf
      exact structural_ordinary_is_never_a_non_match k _ ps (Or.inr (Or.inr rfl)) address repeated bound s
        (fun cells s2 => sources_ordinary_is_never_a_non_match k ps (needLevelSources ps cells) repeated bound s2 hlf)

  theorem sources_ordinary_is_never_a_non_match (k : NeedCapabilities EvalM) (ps : List NeedPattern)
      (sources : List (NeedSource Nat)) (repeated : List Ident) (bound : NeedEnv) (s : EvalState)
      (hlf : literalFreeList ps = true) :
      (runEval (NeedBinder.bindSources k ps sources repeated bound false) s).1 ≠ .ok none := by
    cases ps with
    | nil => simp [NeedBinder.bindSources]
    | cons p rest =>
      simp only [literalFreeList, Bool.and_eq_true] at hlf
      simp only [NeedBinder.bindSources, runEval_bind]
      rcases h1 : runEval (NeedBinder.sourceAddress k.allocate (sources.headD .missing)) s with ⟨e | address, s1⟩
      · simp
      · simp only [thenRun_ok]
        have hone := one_ordinary_is_never_a_non_match k p address repeated bound s1 hlf.1
        rcases h2 : runEval (NeedBinder.bindOne k p address repeated bound false) s1 with ⟨e | (_ | next), s2⟩
        · simp
        · rw [h2] at hone
          exact absurd rfl hone
        · simp only [thenRun_ok]
          exact sources_ordinary_is_never_a_non_match k rest sources.tail repeated next s2 hlf.2
end

/-- For a literal-free head the ordinary binding is never a non-match. -/
theorem ordinary_binding_is_never_a_non_match (k : NeedCapabilities EvalM) (ps : List NeedPattern)
    (cells : List Nat) (s : EvalState) (hlf : literalFreeList ps = true) :
    (runEval (NeedBinder.bindPatterns k ps cells false) s).1 ≠ .ok none := by
  simp only [NeedBinder.bindPatterns, NeedBinder.bindLevel, NeedBinder.cardinalityGate]
  cases hacc : needAcceptsCardinality ps cells.length
  · simp
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    exact sources_ordinary_is_never_a_non_match k ps _ _ [] s hlf

mutual
  theorem ofParameter_literalFree : (p : ParameterPattern) → (NeedPattern.ofParameter p).literalFree = true
    | .capture _ => by
      simp only [NeedPattern.ofParameter]
      split <;> simp [NeedPattern.literalFree]
    | .sequenceValue ps => by
      simp only [NeedPattern.ofParameter, NeedPattern.literalFree]
      exact ofParameter_list_literalFree ps
    | .listValue ps => by
      simp only [NeedPattern.ofParameter, NeedPattern.literalFree]
      exact ofParameter_list_literalFree ps
    | .unpacking ps => by
      simp only [NeedPattern.ofParameter, NeedPattern.literalFree]
      exact ofParameter_list_literalFree ps

  theorem ofParameter_list_literalFree : (ps : List ParameterPattern) →
      literalFreeList (ps.map NeedPattern.ofParameter) = true
    | [] => rfl
    | p :: ps => by
      simp only [List.map_cons, literalFreeList, ofParameter_literalFree p, ofParameter_list_literalFree ps,
        Bool.and_self]
end

/-- EVERY ORDINARY SIGNATURE IS LITERAL-FREE: the head the ordinary drivers bind
    (`(Algorithm.parameterPatterns a).map NeedPattern.ofParameter` — `evalNeedUserSupply`,
    `runNeedStepSlots`, `evalZeroArgumentDemandOutputCounted`) has no literal pattern. -/
theorem ordinary_heads_are_literal_free (a : Algorithm) :
    literalFreeList ((Algorithm.parameterPatterns a).map NeedPattern.ofParameter) = true :=
  ofParameter_list_literalFree _

/-- At the production binder, a literal-free head never yields a non-match in ordinary mode. -/
theorem production_ordinary_binding_is_never_a_non_match (c : NeedChannels) (ps : List NeedPattern)
    (cells : List Nat) (s : EvalState) (hlf : literalFreeList ps = true) :
    ((bindNeedPatterns c ps cells false).runState s).1 ≠ .ok none :=
  ordinary_binding_is_never_a_non_match c.capabilities ps cells s hlf

/-- The head of every ordinary signature never yields a non-match at the production binder, so the
    `badArity` that the three ordinary drivers (`evalNeedUserSupply`, `runNeedStepSlots`,
    `evalZeroArgumentDemandOutputCounted`, all `partial`) raise for an unexpected `none` is
    unreachable — given that they pass these heads, a fact of their source. -/
theorem production_signature_binding_is_never_a_non_match (c : NeedChannels) (a : Algorithm)
    (cells : List Nat) (s : EvalState) :
    ((bindNeedPatterns c ((Algorithm.parameterPatterns a).map NeedPattern.ofParameter) cells false).runState s).1
      ≠ .ok none :=
  production_ordinary_binding_is_never_a_non_match c _ cells s (ordinary_heads_are_literal_free a)

/-- At the production binder, a clause attempt's non-match over a literal-free head is an ordinary
    incompatibility error, reached in the same state. -/
theorem production_non_match_is_an_ordinary_incompatibility (c : NeedChannels) (ps : List NeedPattern)
    (cells : List Nat) (s : EvalState) (hlf : literalFreeList ps = true)
    (hnone : ((bindNeedPatterns c ps cells true).runState s).1 = .ok none) :
    ∃ e, Incompatibility e ∧ ((bindNeedPatterns c ps cells false).runState s).1 = .error e
      ∧ ((bindNeedPatterns c ps cells false).runState s).2 = ((bindNeedPatterns c ps cells true).runState s).2 := by
  obtain ⟨hs, hm, -⟩ := family_attempt_is_the_ordinary_binding c.capabilities ps cells s
  rcases hm.of_non_match hnone with ⟨e, hinc, he⟩ | hn
  · exact ⟨e, hinc, he, hs.symm⟩
  · exact absurd hn (production_ordinary_binding_is_never_a_non_match c ps cells s hlf)

/-! ## Instances: the hypotheses are met by ordinary heads (executable) -/

namespace Instances

def channels : NeedChannels := ⟨demandNeed, projectNeedCallable⟩

def heap (values : List Result) : EvalState :=
  { needs := (values.map fun v => ({ suspension := .ready (v, Result.valueCount v) } : NeedCell)).toArray }

/-- A plain name beside a literal. -/
def mixed : List NeedPattern := [.bind "x", .literal (.litInt 7)]

-- (b′) cell 0 sits only at the plain position: it is not inspected, never invoked, never allocated.
#guard !(inspectedCells (needRepeatedNames mixed) mixed (needLevelSources mixed [0, 1])).contains 0
#guard (patternsEvents channels.capabilities mixed [0, 1] false (heap [.atom 1, .atom 7])).all
  (fun ev => !(ev.isInvocation && ev.address == 0) && ev.allocated? != some 0)
-- …while the literal's cell 1 is inspected and demanded.
#guard (patternsEvents channels.capabilities mixed [0, 1] false (heap [.atom 1, .atom 7])).any
  (fun ev => ev.isInvocation && ev.address == 1)
-- Aliasing: the same cell at the plain AND the literal position is inspected and demanded.
#guard (inspectedCells (needRepeatedNames mixed) mixed (needLevelSources mixed [0, 0])).contains 0
#guard (patternsEvents channels.capabilities mixed [0, 0] false (heap [.atom 7])).any
  (fun ev => ev.isInvocation && ev.address == 0)

/-- A repeated name. -/
def twice : List NeedPattern := [.bind "x", .bind "x"]

-- (c) unequal repeated values: a non-match against the ordinary incompatibility (`ModeAgree.incompatible`).
#guard match ((bindNeedPatterns channels twice [0, 1] true).runState (heap [.atom 1, .atom 2])).1,
             ((bindNeedPatterns channels twice [0, 1] false).runState (heap [.atom 1, .atom 2])).1 with
  | .ok none, .error (.withContext _ .badArity) => true
  | _, _ => false
-- (c) a literal mismatch: a non-match in both modes (`ModeAgree.nonMatch`).
#guard match ((bindNeedPatterns channels [.literal (.litInt 0)] [0] true).runState (heap [.atom 7])).1,
             ((bindNeedPatterns channels [.literal (.litInt 0)] [0] false).runState (heap [.atom 7])).1 with
  | .ok none, .ok none => true
  | _, _ => false

end Instances

end KatLang.BinderCorrespondence
