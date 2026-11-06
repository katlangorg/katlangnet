import KatLangArityLaws.SignatureCompletionLaws

open KatLang

/-!
# SC-1: the reading of a classification, and what a selected answer satisfies

Over the reference kernel only (`SignatureCompletion.lean`): reachability is saturated and transitive, components are
equivalence classes, the layers leave no pending cell, and every reading's facts are a fixed point of the ONE composition
law over the settled reads. `Completed` is the publication interface: a completed selection carries its obligations.
-/

namespace KatLang.SignatureCompletion

/-! ## Reachability -/

private theorem filter_sublist_of_imp {p q : Nat → Bool} {l : List Nat}
    (h : ∀ x ∈ l, p x = true → q x = true) : (l.filter p).Sublist (l.filter q) := by
  induction l with
  | nil => exact List.Sublist.refl _
  | cons x xs ih =>
    have hx := h x List.mem_cons_self
    have hrest := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    simp only [List.filter_cons]
    by_cases hpx : p x = true
    · simp only [hpx, hx hpx, if_true]
      exact hrest.cons_cons x
    · simp only [hpx, if_false]
      by_cases hqx : q x = true
      · simp only [hqx, if_true]
        exact hrest.cons x
      · simp only [hqx, if_false]
        exact hrest

section Reach

variable (sys : System) (opened : Nat → Bool)

theorem mem_grow {S : List Nat} {j : Nat} :
    j ∈ grow sys opened S ↔ j ∈ sys.keys ∧ (j ∈ S ∨ ∃ i ∈ S, j ∈ activeTargets (sys.equation i) opened) := by
  simp [grow, List.mem_filter]

theorem growN_succ' : ∀ (n : Nat) (S : List Nat),
    growN sys opened (Nat.succ n) S = grow sys opened (growN sys opened n S) := by
  intro n
  induction n with
  | zero => intro S; rfl
  | succ n ih =>
    intro S
    have h : growN sys opened (Nat.succ (Nat.succ n)) S = growN sys opened (Nat.succ n) (grow sys opened S) := rfl
    rw [h, ih]
    rfl

/-- The saturation sequence of a start. -/
private def chain (a : Nat) (i : Nat) : List Nat := growN sys opened i (grow sys opened [a])

private theorem chain_succ (a i : Nat) : chain sys opened a (i + 1) = grow sys opened (chain sys opened a i) :=
  growN_succ' sys opened i _

private theorem chain_filter (a i : Nat) :
    ∃ p, chain sys opened a i = sys.keys.filter p := by
  cases i with
  | zero => exact ⟨_, rfl⟩
  | succ i => rw [chain_succ]; exact ⟨_, rfl⟩

private theorem chain_sub_keys (a i : Nat) : chain sys opened a i ⊆ sys.keys := by
  obtain ⟨p, h⟩ := chain_filter sys opened a i
  rw [h]
  exact fun x hx => (List.mem_filter.1 hx).1

private theorem chain_mono (a i : Nat) {x : Nat} (h : x ∈ chain sys opened a i) :
    x ∈ chain sys opened a (i + 1) := by
  rw [chain_succ, mem_grow]
  exact ⟨chain_sub_keys sys opened a i h, .inl h⟩

private theorem chain_sublist (a i : Nat) :
    (chain sys opened a i).Sublist (chain sys opened a (i + 1)) := by
  obtain ⟨p, hp⟩ := chain_filter sys opened a i
  obtain ⟨q, hq⟩ := chain_filter sys opened a (i + 1)
  have hsub : ∀ x ∈ sys.keys, p x = true → q x = true := by
    intro x hx hpx
    have h1 : x ∈ chain sys opened a i := by rw [hp]; exact List.mem_filter.2 ⟨hx, hpx⟩
    have h2 := chain_mono sys opened a i h1
    rw [hq] at h2
    exact (List.mem_filter.1 h2).2
  rw [hp, hq]
  exact filter_sublist_of_imp hsub

private theorem chain_length_le (a i : Nat) (hn : sys.keys.Nodup) :
    (chain sys opened a i).length ≤ sys.keys.length := by
  obtain ⟨p, h⟩ := chain_filter sys opened a i
  rw [h]
  exact List.length_filter_le _ _

private theorem chain_progress (a : Nat) (ha : a ∈ sys.keys) : ∀ i,
    chain sys opened a (i + 1) = chain sys opened a i ∨ i + 1 ≤ (chain sys opened a i).length := by
  intro i
  induction i with
  | zero =>
    right
    have : a ∈ chain sys opened a 0 := by
      show a ∈ grow sys opened [a]
      rw [mem_grow]
      exact ⟨ha, .inl (by simp)⟩
    exact List.length_pos_of_mem this
  | succ i ih =>
    by_cases he : chain sys opened a (i + 1 + 1) = chain sys opened a (i + 1)
    · exact .inl he
    · right
      have hne : chain sys opened a (i + 1) ≠ chain sys opened a i := by
        intro e
        apply he
        rw [chain_succ, e, ← chain_succ, e]
      have hle := (chain_sublist sys opened a i).length_le
      have hlt : (chain sys opened a i).length < (chain sys opened a (i + 1)).length := by
        apply Nat.lt_of_le_of_ne hle
        intro e
        exact hne ((chain_sublist sys opened a i).eq_of_length e).symm
      rcases ih with h | h
      · exact absurd h hne
      · omega

/-- Saturation: `keys.length` growth rounds reach a closed set. -/
theorem grow_reachOf (hn : sys.keys.Nodup) {a : Nat} (ha : a ∈ sys.keys) :
    grow sys opened (reachOf sys opened a) = reachOf sys opened a := by
  have e : reachOf sys opened a = chain sys opened a sys.keys.length := rfl
  rw [e, ← chain_succ]
  rcases chain_progress sys opened a ha sys.keys.length with h | h
  · exact h
  · have := chain_length_le sys opened a sys.keys.length hn
    omega

theorem self_mem_reachOf {a : Nat} (ha : a ∈ sys.keys) : a ∈ reachOf sys opened a := by
  have base : a ∈ chain sys opened a 0 := by
    show a ∈ grow sys opened [a]
    rw [mem_grow]
    exact ⟨ha, .inl (by simp)⟩
  have : ∀ i, a ∈ chain sys opened a i := by
    intro i
    induction i with
    | zero => exact base
    | succ i ih => exact chain_mono sys opened a i ih
  exact this _

theorem reachOf_closed (hn : sys.keys.Nodup) {a j t : Nat} (ha : a ∈ sys.keys)
    (hj : j ∈ reachOf sys opened a) (ht : t ∈ activeTargets (sys.equation j) opened) (hk : t ∈ sys.keys) :
    t ∈ reachOf sys opened a := by
  rw [← grow_reachOf sys opened hn ha, mem_grow]
  exact ⟨hk, .inr ⟨j, hj, ht⟩⟩

/-- Everything a reached key reaches is reached: reachability is transitive. -/
theorem reachOf_trans (hn : sys.keys.Nodup) {a j x : Nat} (ha : a ∈ sys.keys)
    (hj : j ∈ reachOf sys opened a) (hx : x ∈ reachOf sys opened j) : x ∈ reachOf sys opened a := by
  have step : ∀ S : List Nat, (∀ y ∈ S, y ∈ reachOf sys opened a) → ∀ y ∈ grow sys opened S,
      y ∈ reachOf sys opened a := by
    intro S hS y hy
    rcases (mem_grow sys opened).1 hy with ⟨hk, hy | ⟨i, hi, ht⟩⟩
    · exact hS y hy
    · exact reachOf_closed sys opened hn ha (hS i hi) ht hk
  have : ∀ i, ∀ y ∈ chain sys opened j i, y ∈ reachOf sys opened a := by
    intro i
    induction i with
    | zero =>
      apply step
      intro y hy
      simp only [List.mem_singleton] at hy
      exact hy ▸ hj
    | succ i ih =>
      rw [chain_succ]
      exact step _ ih
  exact this _ x hx

theorem reachOf_sub_keys {a x : Nat} (ha : a ∈ sys.keys) (hx : x ∈ reachOf sys opened a) : x ∈ sys.keys :=
  chain_sub_keys sys opened a _ hx

end Reach

/-! ## Components -/

section Components

variable (sys : System) (opened : Nat → Bool)

/-- The reach table the evaluation uses. -/
abbrev reachTable : Nat → List Nat := (tabulate sys.keys [] (reachOf sys opened)).get

theorem reachTable_of_mem {a : Nat} (h : a ∈ sys.keys) : reachTable sys opened a = reachOf sys opened a :=
  tabulate_of_mem _ _ _ h

theorem sameComponent_refl {a : Nat} (h : a ∈ sys.keys) : sameComponent (reachTable sys opened) a a = true := by
  simp [sameComponent, reachTable_of_mem sys opened h, self_mem_reachOf sys opened h]

theorem sameComponent_symm {a b : Nat} :
    sameComponent (reachTable sys opened) a b = sameComponent (reachTable sys opened) b a := by
  simp [sameComponent, Bool.and_comm]

theorem sameComponent_iff {a b : Nat} (ha : a ∈ sys.keys) (hb : b ∈ sys.keys) :
    sameComponent (reachTable sys opened) a b = true
      ↔ b ∈ reachOf sys opened a ∧ a ∈ reachOf sys opened b := by
  simp [sameComponent, reachTable_of_mem sys opened ha, reachTable_of_mem sys opened hb]

theorem sameComponent_trans (hn : sys.keys.Nodup) {a b c : Nat} (ha : a ∈ sys.keys) (hb : b ∈ sys.keys)
    (hc : c ∈ sys.keys) (h1 : sameComponent (reachTable sys opened) a b = true)
    (h2 : sameComponent (reachTable sys opened) b c = true) :
    sameComponent (reachTable sys opened) a c = true := by
  rw [sameComponent_iff sys opened ha hb] at h1
  rw [sameComponent_iff sys opened hb hc] at h2
  rw [sameComponent_iff sys opened ha hc]
  exact ⟨reachOf_trans sys opened hn ha h1.1 h2.1, reachOf_trans sys opened hn hc h2.2 h1.2⟩

theorem mem_componentOf {reach : Nat → List Nat} {a x : Nat} :
    x ∈ componentOf sys reach a ↔ x ∈ sys.keys ∧ sameComponent reach a x = true := by
  simp [componentOf, List.mem_filter]

/-- Every member of a component names the same component, in the same storage order. -/
theorem componentOf_eq (hn : sys.keys.Nodup) {a b : Nat} (ha : a ∈ sys.keys) (hb : b ∈ sys.keys)
    (h : sameComponent (reachTable sys opened) a b = true) :
    componentOf sys (reachTable sys opened) b = componentOf sys (reachTable sys opened) a := by
  unfold componentOf
  apply List.filter_congr
  intro x hx
  cases h1 : sameComponent (reachTable sys opened) a x with
  | true =>
    have hba : sameComponent (reachTable sys opened) b a = true := by
      rw [sameComponent_symm]; exact h
    exact sameComponent_trans sys opened hn hb ha hx hba h1
  | false =>
    cases h2 : sameComponent (reachTable sys opened) b x with
    | false => rfl
    | true =>
      have := sameComponent_trans sys opened hn ha hb hx h h2
      rw [this] at h1
      cases h1

end Components

/-! ## The layers -/

section Layers

variable (sys : System) (opened : Nat → Bool) (fuel : Nat)

theorem Cell.patterns_factOf (c : Cell) : c.patterns = (factOf c).patterns := by
  cases c <;> rfl

/-- `evalComponent` never leaves a cell pending. -/
theorem evalComponent_not_pending (members : List Nat) (cells : Nat → Cell) (k : Nat) :
    evalComponent sys opened fuel members cells k ≠ .pending := by
  unfold evalComponent
  simp only
  split
  · simp
  · split
    · simp
    · split
      · simp
      · generalize completeLoop _ _ _ _ _ _ _ = outcome
        cases outcome <;> simp

/-- What a layer does to one key. -/
theorem layer_apply (reach : Nat → List Nat) (cells : Memo Cell) {k : Nat} (h : k ∈ sys.keys) :
    (layer sys opened fuel reach cells).get k =
      match cells.get k with
      | .pending =>
          let members := componentOf sys reach k
          if layerReady sys opened members cells.get then evalComponent sys opened fuel members cells.get k
          else .pending
      | settled => settled :=
  tabulate_of_mem _ _ _ h

theorem layer_keep (reach : Nat → List Nat) (cells : Memo Cell) {k : Nat} (h : k ∈ sys.keys)
    (hp : cells.get k ≠ .pending) : (layer sys opened fuel reach cells).get k = cells.get k := by
  rw [layer_apply sys opened fuel reach cells h]
  cases hc : cells.get k with
  | pending => exact absurd hc hp
  | fact f => rfl
  | meaningless => rfl
  | exhausted => rfl

theorem mem_outsideReads {members : List Nat} {t : Nat} :
    t ∈ outsideReads sys opened members ↔
      ∃ k ∈ members, t ∈ activeTargets (sys.equation k) opened ∧ t ∉ members := by
  simp [outsideReads, List.mem_flatMap, List.mem_filter]

/-- The invariant of the layers: a settled cell's component is settled with it, and a FACT is the composition of its
    equation over cells that are facts. Nothing here says how the fact was found: gate or rounds. -/
structure GoodCells (cells : Nat → Cell) : Prop where
  outside : ∀ k, k ∉ sys.keys → cells k = .pending
  together : ∀ a ∈ sys.keys, ∀ b ∈ sys.keys, sameComponent (reachTable sys opened) a b = true →
    cells a = .pending → cells b = .pending
  closed : ∀ k ∈ sys.keys, ∀ f, cells k = .fact f →
    (∀ t ∈ activeTargets (sys.equation k) opened, ∃ g, cells t = .fact g)
      ∧ f = composeWith (sys.equation k) opened (fun t => (cells t).patterns)

theorem goodCells_start : GoodCells sys opened fun _ => .pending :=
  ⟨fun _ _ => rfl, fun _ _ _ _ _ _ => rfl, fun _ _ f h => by cases h⟩

private theorem acceptsZero_nil : acceptsZero [] = true := rfl


theorem lowerReads_outside {members : List Nat} {cells : Nat → Cell} {m t : Nat} (hm : m ∈ members)
    (ht : t ∈ activeTargets (sys.equation m) opened) (tm : t ∉ members) :
    lowerReads sys opened members cells t = (cells t).patterns := by
  have : t ∈ outsideReads sys opened members := (mem_outsideReads sys opened).2 ⟨m, hm, ht, tm⟩
  simp [lowerReads, this]

/-- The value of `evalComponent` when it gives a fact: no read leaving the component failed, and the facts of the
    members are a FIXED POINT of the one composition law over the settled reads, whichever branch found them: the
    closed gate, when no read inside the cycle lifts (Lemma B1), or the rounds. -/
theorem evalComponent_fact_cases {members : List Nat} {cells : Nat → Cell} {k : Nat} {f : Fact}
    (h : evalComponent sys opened fuel members cells k = .fact f) :
    (∀ t ∈ outsideReads sys opened members, cells t ≠ .exhausted ∧ cells t ≠ .meaningless)
    ∧ ∃ state : Nat → Fact,
      evalComponent sys opened fuel members cells = (fun x => .fact (state x))
      ∧ ∀ m ∈ members, state m = composeWith (sys.equation m) opened
          (fun t => if t ∈ members then (state t).patterns else (cells t).patterns) := by
  unfold evalComponent at h ⊢
  simp only at h ⊢
  by_cases h1 : (outsideReads sys opened members).any (fun t => cells t == .exhausted) = true
  · rw [if_pos h1] at h; simp at h
  by_cases h2 : (outsideReads sys opened members).any (fun t => cells t == .meaningless) = true
  · rw [if_neg h1, if_pos h2] at h; simp at h
  have hout : ∀ t ∈ outsideReads sys opened members, cells t ≠ .exhausted ∧ cells t ≠ .meaningless := by
    intro t ht
    constructor
    · intro e
      apply h1
      simp only [List.any_eq_true]
      exact ⟨t, ht, by simp [e]⟩
    · intro e
      apply h2
      simp only [List.any_eq_true]
      exact ⟨t, ht, by simp [e]⟩
  refine ⟨hout, ?_⟩
  rw [if_neg h1, if_neg h2] at h ⊢
  by_cases h3 : (!gateLifts sys opened members (lowerReads sys opened members cells)) = true
  · rw [if_pos h3]
    refine ⟨_, rfl, ?_⟩
    intro m hm
    have hgate := roundStep_of_mem sys opened members (lowerReads sys opened members cells) ⟨fun _ => closedFact⟩ hm
    show (gateState sys opened members _).get m = _
    unfold gateState
    rw [hgate]
    unfold nextFact
    apply composeWith_congr
    intro t ht
    by_cases tm : t ∈ members
    · right
      refine ⟨by simp [readThrough, tm, closedFact, acceptsZero_nil], ?_⟩
      simp only [tm, if_true]
      have hno : gateLifts sys opened members (lowerReads sys opened members cells) = false := by simpa using h3
      unfold gateLifts at hno
      have hno2 := List.any_eq_false.1 hno m hm
      have hno3 : ∀ x, x ∈ activeTargets (sys.equation m) opened → x ∈ members →
          acceptsZero (gateState sys opened members (lowerReads sys opened members cells) x).patterns = true := by
        simpa using hno2
      exact hno3 t ht tm
    · left
      simp only [readThrough, List.contains_iff_mem, tm, decide_false, Bool.false_eq_true, if_false]
      exact lowerReads_outside sys opened hm ht tm
  · rw [if_neg h3] at h ⊢
    cases hc : completeLoop (roundStep sys opened members (lowerReads sys opened members cells)) (sameState members) fuel
        (gateState sys opened members (lowerReads sys opened members cells))
        (gateState sys opened members (lowerReads sys opened members cells)) 0 1 with
    | settled state =>
      refine ⟨state.get, rfl, ?_⟩
      intro m hm
      have := settled_fixed_point sys opened members (lowerReads sys opened members cells) hc hm
      rw [this]
      apply composeWith_congr
      intro t ht
      left
      by_cases tm : t ∈ members
      · simp [readThrough, tm]
      · simp only [readThrough, List.contains_iff_mem, tm, decide_false, Bool.false_eq_true, if_false]
        exact lowerReads_outside sys opened hm ht tm
    | nonSettling => simp [hc] at h
    | exhausted => simp [hc] at h

variable (wf : sys.WellFormed)
include wf

private theorem target_mem {k t : Nat} (hk : k ∈ sys.keys) (ht : t ∈ activeTargets (sys.equation k) opened) :
    t ∈ sys.keys := by
  obtain ⟨r, hr, e, _⟩ := mem_activeTargets.1 ht
  exact (wf.targets k hk r hr).1 t e

/-- The layers keep the invariant. -/
theorem goodCells_layer {cells : Memo Cell} (good : GoodCells sys opened cells.get) :
    GoodCells sys opened (layer sys opened fuel (reachTable sys opened) cells).get := by
  have keep := fun {k} hk hp => layer_keep sys opened fuel (reachTable sys opened) cells (k := k) hk hp
  have comp_eq : ∀ {a b}, a ∈ sys.keys → b ∈ sys.keys → sameComponent (reachTable sys opened) a b = true →
      componentOf sys (reachTable sys opened) b = componentOf sys (reachTable sys opened) a :=
    fun ha hb h => componentOf_eq sys opened wf.nodup ha hb h
  have apply_pending : ∀ {k}, k ∈ sys.keys → cells.get k = .pending →
      (layer sys opened fuel (reachTable sys opened) cells).get k =
        if layerReady sys opened (componentOf sys (reachTable sys opened) k) cells.get
        then evalComponent sys opened fuel (componentOf sys (reachTable sys opened) k) cells.get k else .pending := by
    intro k hk hp
    rw [layer_apply sys opened fuel _ cells hk, hp]
  refine ⟨fun k hk => tabulate_of_not_mem _ _ _ hk, ?_, ?_⟩
  · intro a ha b hb hab hl
    have hpa : cells.get a = .pending := by
      by_cases hne : cells.get a = .pending
      · exact hne
      · rw [keep ha hne] at hl
        exact absurd hl hne
    have hpb := good.together a ha b hb hab hpa
    rw [apply_pending ha hpa] at hl
    rw [apply_pending hb hpb, comp_eq ha hb hab]
    by_cases hr : layerReady sys opened (componentOf sys (reachTable sys opened) a) cells.get = true
    · simp only [hr, if_true] at hl
      exact absurd hl (evalComponent_not_pending sys opened fuel _ _ _)
    · simp [hr]
  · intro k hk f hf
    by_cases hp : cells.get k = .pending
    · rw [apply_pending hk hp] at hf
      by_cases hr : layerReady sys opened (componentOf sys (reachTable sys opened) k) cells.get = true
      · simp only [hr, if_true] at hf
        obtain ⟨hout, state, hE, hfix⟩ := evalComponent_fact_cases sys opened fuel hf
        have hsame : k ∈ componentOf sys (reachTable sys opened) k :=
          (mem_componentOf sys).2 ⟨hk, sameComponent_refl sys opened hk⟩
        have hval : ∀ t ∈ activeTargets (sys.equation k) opened,
            ((layer sys opened fuel (reachTable sys opened) cells).get t).patterns
                = (if t ∈ componentOf sys (reachTable sys opened) k then (state t).patterns else (cells.get t).patterns)
            ∧ ∃ g, (layer sys opened fuel (reachTable sys opened) cells).get t = .fact g := by
          intro t ht
          have tk := target_mem sys opened wf hk ht
          by_cases tm : t ∈ componentOf sys (reachTable sys opened) k
          · have hst := ((mem_componentOf sys).1 tm).2
            have hpt := good.together k hk t tk hst hp
            have e : (layer sys opened fuel (reachTable sys opened) cells).get t = .fact (state t) := by
              rw [apply_pending tk hpt, comp_eq hk tk hst]
              simp only [hr, if_true, hE]
            rw [e]
            exact ⟨by simp [tm, Cell.patterns], _, rfl⟩
          · have hor : t ∈ outsideReads sys opened (componentOf sys (reachTable sys opened) k) :=
              (mem_outsideReads sys opened).2 ⟨k, hsame, ht, tm⟩
            have hne : cells.get t ≠ .pending := by
              have := List.all_eq_true.1 hr t hor
              simpa using this
            rw [keep tk hne]
            obtain ⟨he, hm⟩ := hout t hor
            cases hc : cells.get t with
            | pending => exact absurd hc hne
            | exhausted => exact absurd hc he
            | meaningless => exact absurd hc hm
            | fact g => exact ⟨by simp [tm], g, rfl⟩
        refine ⟨fun t ht => (hval t ht).2, ?_⟩
        have hfk : f = state k := by
          rw [hE] at hf
          cases hf
          rfl
        rw [hfk, hfix k hsame]
        apply composeWith_congr
        intro t ht
        left
        exact (hval t ht).1.symm
      · simp [hr] at hf
    · have hc : cells.get k = .fact f := by rw [keep hk hp] at hf; exact hf
      obtain ⟨hall, hcomp⟩ := good.closed k hk f hc
      refine ⟨?_, ?_⟩
      · intro t ht
        obtain ⟨g, hg⟩ := hall t ht
        have tk := target_mem sys opened wf hk ht
        exact ⟨g, by rw [keep tk (by simp [hg]), hg]⟩
      · rw [hcomp]
        apply composeWith_congr
        intro t ht
        obtain ⟨g, hg⟩ := hall t ht
        have tk := target_mem sys opened wf hk ht
        left
        rw [keep tk (by simp [hg])]

theorem goodCells_layers (n : Nat) : ∀ {cells : Memo Cell}, GoodCells sys opened cells.get →
    GoodCells sys opened (layers sys opened fuel (reachTable sys opened) n cells).get := by
  induction n with
  | zero => exact fun good => good
  | succ n ih => exact fun good => ih (goodCells_layer sys opened fuel wf good)

theorem goodCells_evalVector : GoodCells sys opened (evalVector sys opened fuel).get :=
  goodCells_layers sys opened fuel wf _ (cells := ⟨fun _ => .pending⟩) (goodCells_start sys opened)

end Layers

/-! ## No cell stays pending -/

section Progress

variable (sys : System) (opened : Nat → Bool) (fuel : Nat) (wf : sys.WellFormed)
include wf

private theorem countP_strict {S T l : List Nat} {k : Nat} (hnodup : l.Nodup) (hsub : ∀ x, x ∈ S → x ∈ T)
    (hnot : k ∉ S) (hself : k ∈ T) (hk : k ∈ l) :
    l.countP (fun x => S.contains x) < l.countP (fun x => T.contains x) := by
  induction l with
  | nil => cases hk
  | cons x xs ih =>
    have hxs : xs.Nodup := (List.nodup_cons.1 hnodup).2
    simp only [List.countP_cons]
    have mono : xs.countP (fun x => S.contains x) ≤ xs.countP (fun x => T.contains x) := by
      apply List.countP_mono_left
      intro y _ hy
      simp only [List.contains_iff_mem, decide_eq_true_eq] at hy ⊢
      exact hsub y hy
    by_cases e : k = x
    · subst e
      have h1 : S.contains k = false := by simpa using hnot
      have h2 : T.contains k = true := by simpa using hself
      simp only [h1, h2, if_true, if_false, Bool.false_eq_true]
      omega
    · have hk' : k ∈ xs := by simpa [e] using hk
      have := ih hxs hk'
      by_cases hsx : S.contains x = true
      · have htx : T.contains x = true := by
          simp only [List.contains_iff_mem, decide_eq_true_eq] at hsx ⊢
          exact hsub x hsx
        simp only [hsx, htx, if_true]
        omega
      · rw [if_neg hsx]
        split <;> omega

private theorem reachTable_measure_drop {k t m : Nat} (hk : k ∈ sys.keys) (hm : m ∈ sys.keys) (ht : t ∈ sys.keys)
    (hkm : sameComponent (reachTable sys opened) k m = true)
    (hread : t ∈ activeTargets (sys.equation m) opened)
    (hout : sameComponent (reachTable sys opened) k t = false) :
    sys.keys.countP (fun x => (reachOf sys opened t).contains x)
      < sys.keys.countP (fun x => (reachOf sys opened k).contains x) := by
  have hn := wf.nodup
  have hmr : m ∈ reachOf sys opened k := ((sameComponent_iff sys opened hk hm).1 hkm).1
  have htr : t ∈ reachOf sys opened k := reachOf_closed sys opened hn hk hmr hread ht
  have hsub : ∀ x, x ∈ reachOf sys opened t → x ∈ reachOf sys opened k :=
    fun x hx => reachOf_trans sys opened hn hk htr hx
  have hnot : k ∉ reachOf sys opened t := by
    intro hkt
    have := (sameComponent_iff sys opened hk ht).2 ⟨htr, hkt⟩
    rw [hout] at this
    cases this
  exact countP_strict sys wf wf.nodup hsub hnot (self_mem_reachOf sys opened hk) hk

/-- Some pending key's component is ready: take a pending key reaching the fewest keys; everything its component reads
    outside reaches strictly fewer, so it is not pending. -/
private theorem exists_ready {cells : Memo Cell} (good : GoodCells sys opened cells.get) {p : Nat} (hp : p ∈ sys.keys)
    (hpend : cells.get p = .pending) :
    ∃ k ∈ sys.keys, cells.get k = .pending
      ∧ layerReady sys opened (componentOf sys (reachTable sys opened) k) cells.get = true := by
  let measure := fun x => sys.keys.countP (fun y => (reachOf sys opened x).contains y)
  have hmin : ∀ n, ∀ q ∈ sys.keys, cells.get q = .pending → measure q ≤ n →
      ∃ k ∈ sys.keys, cells.get k = .pending ∧ ∀ t ∈ sys.keys, cells.get t = .pending → measure k ≤ measure t := by
    intro n
    induction n with
    | zero =>
      intro q hq hqp hm
      exact ⟨q, hq, hqp, fun t _ _ => by omega⟩
    | succ n ih =>
      intro q hq hqp hm
      by_cases h : ∃ t ∈ sys.keys, cells.get t = .pending ∧ measure t < measure q
      · obtain ⟨t, ht, htp, hlt⟩ := h
        exact ih t ht htp (by omega)
      · refine ⟨q, hq, hqp, fun t ht htp => ?_⟩
        by_cases hlt : measure t < measure q
        · exact absurd ⟨t, ht, htp, hlt⟩ h
        · omega
  obtain ⟨k, hk, hkp, hk_min⟩ := hmin _ p hp hpend (Nat.le_refl _)
  refine ⟨k, hk, hkp, ?_⟩
  unfold layerReady
  apply List.all_eq_true.2
  intro t ht
  obtain ⟨m, hm, hread, hnot⟩ := (mem_outsideReads sys opened).1 ht
  obtain ⟨mk, hkm⟩ := (mem_componentOf sys).1 hm
  have tk : t ∈ sys.keys := target_mem sys opened wf mk hread
  have hout : sameComponent (reachTable sys opened) k t = false := by
    cases h : sameComponent (reachTable sys opened) k t with
    | false => rfl
    | true => exact absurd ((mem_componentOf sys).2 ⟨tk, h⟩) hnot
  have hdrop := reachTable_measure_drop sys opened wf hk mk tk hkm hread hout
  by_cases htp : cells.get t = .pending
  · have := hk_min t tk htp
    simp only [measure] at this
    omega
  · simpa using htp

/-- A layer removes a pending key while one remains: the layers finish. -/
private theorem layer_count (cells : Memo Cell) (good : GoodCells sys opened cells.get) :
    sys.keys.countP (fun k => (layer sys opened fuel (reachTable sys opened) cells).get k == .pending)
      ≤ sys.keys.countP (fun k => cells.get k == .pending) - 1
    ∨ sys.keys.countP (fun k => cells.get k == .pending) = 0 := by
  have hmono : ∀ k ∈ sys.keys, (layer sys opened fuel (reachTable sys opened) cells).get k = .pending →
      cells.get k = .pending := by
    intro k hk hl
    by_cases h : cells.get k = .pending
    · exact h
    · rw [layer_keep sys opened fuel _ cells hk h] at hl
      exact absurd hl h
  by_cases hz : sys.keys.countP (fun k => cells.get k == .pending) = 0
  · exact .inr hz
  left
  obtain ⟨p, hp, hpp⟩ := List.countP_pos_iff.1 (Nat.pos_of_ne_zero hz)
  have hpp' : cells.get p = .pending := by simpa using hpp
  obtain ⟨k, hk, hkp, hready⟩ := exists_ready sys opened wf (cells := cells) good hp hpp'
  have hgone : (layer sys opened fuel (reachTable sys opened) cells).get k ≠ .pending := by
    rw [layer_apply sys opened fuel _ cells hk, hkp]
    simp only [hready, if_true]
    exact evalComponent_not_pending sys opened fuel _ _ _
  have key : ∀ l : List Nat, k ∈ l → l.Nodup → (∀ x ∈ l, x ∈ sys.keys) →
      l.countP (fun x => (layer sys opened fuel (reachTable sys opened) cells).get x == .pending) + 1
        ≤ l.countP (fun x => cells.get x == .pending) := by
    intro l
    induction l with
    | nil => intro h; cases h
    | cons x xs ih =>
      intro hm hnd hsub
      have hx := (List.nodup_cons.1 hnd).1
      have hxs := (List.nodup_cons.1 hnd).2
      have hmono' : xs.countP (fun x => (layer sys opened fuel (reachTable sys opened) cells).get x == .pending)
          ≤ xs.countP (fun x => cells.get x == .pending) := by
        apply List.countP_mono_left
        intro y hy hyl
        have := hmono y (hsub y (List.mem_cons_of_mem _ hy)) (by simpa using hyl)
        simpa using this
      simp only [List.countP_cons]
      by_cases e : k = x
      · subst e
        have h1 : ((layer sys opened fuel (reachTable sys opened) cells).get k == .pending) = false := by
          simpa using hgone
        have h2 : (cells.get k == .pending) = true := by simpa using hkp
        simp only [h1, h2, if_true, if_false, Bool.false_eq_true]
        omega
      · have hk' : k ∈ xs := by simpa [e] using hm
        have := ih hk' hxs (fun y hy => hsub y (List.mem_cons_of_mem _ hy))
        by_cases hlx : ((layer sys opened fuel (reachTable sys opened) cells).get x == .pending) = true
        · have hcx : (cells.get x == .pending) = true := by
            have := hmono x (hsub x List.mem_cons_self) (by simpa using hlx)
            simpa using this
          simp only [hlx, hcx, if_true]
          omega
        · rw [if_neg hlx]
          split <;> omega
  have := key sys.keys hk wf.nodup (fun _ h => h)
  omega

private theorem layers_count (n : Nat) : ∀ (cells : Memo Cell), GoodCells sys opened cells.get →
    sys.keys.countP (fun k => (layers sys opened fuel (reachTable sys opened) n cells).get k == .pending)
      ≤ sys.keys.countP (fun k => cells.get k == .pending) - n := by
  induction n with
  | zero => intro cells _; exact Nat.le_refl _
  | succ n ih =>
    intro cells good
    have h1 := ih _ (goodCells_layer sys opened fuel wf good)
    have h2 := layer_count sys opened fuel wf cells good
    show sys.keys.countP (fun k => (layers sys opened fuel (reachTable sys opened) n
      (layer sys opened fuel (reachTable sys opened) cells)).get k == .pending) ≤ _
    rcases h2 with h2 | h2
    · omega
    · rw [h2]
      have hmono : sys.keys.countP (fun k => (layer sys opened fuel (reachTable sys opened) cells).get k == .pending) = 0 := by
        rw [List.countP_eq_zero] at h2 ⊢
        intro k hk hl
        have hkp := h2 k hk
        by_cases h : cells.get k = .pending
        · simp [h] at hkp
        · rw [layer_keep sys opened fuel _ cells hk h] at hl
          exact hkp hl
      rw [hmono] at h1
      omega

/-- THE LAYERS FINISH: after `keys.length` layers no key is pending, for every well-formed system, classification and
    bound, so components are evaluated dependency-first without a stuck state. -/
theorem no_pending_cell {k : Nat} (hk : k ∈ sys.keys) : (evalVector sys opened fuel).get k ≠ .pending := by
  intro hp
  have h := layers_count sys opened fuel wf sys.keys.length ⟨fun _ => .pending⟩ (goodCells_start sys opened)
  have hle : sys.keys.countP (fun k => ((⟨fun _ => .pending⟩ : Memo Cell)).get k == .pending) ≤ sys.keys.length :=
    List.countP_le_length
  have hzero : sys.keys.countP (fun k => (layers sys opened fuel (reachTable sys opened) sys.keys.length
      ⟨fun _ => .pending⟩).get k == .pending) = 0 := by omega
  rw [List.countP_eq_zero] at hzero
  exact hzero k hk (by simp only [beq_iff_eq]; exact hp)

end Progress

/-! ## Selection: what a row and a selected answer satisfy -/

section Selection

variable (sys : System) (fuel : Nat) (linkSet : List Nat)

theorem rowOf_consistent {assigned : Nat → Bool} {v : Groundedness} {facts : Nat → Fact}
    (h : rowOf sys fuel linkSet assigned = .consistent v facts) :
    (∀ k ∈ sys.keys, (evalVector sys assigned fuel).get k = .fact (facts k))
    ∧ (∀ l ∈ linkSet, l ∈ sys.keys → assigned l = !(facts l).patterns.isEmpty)
    ∧ v = groundednessOf sys fuel linkSet assigned := by
  unfold rowOf at h
  simp only at h
  by_cases h1 : noVerdict sys (evalVector sys assigned fuel).get = true
  · rw [if_pos h1] at h; cases h
  by_cases h2 : linkSet.any (refutesClass (evalVector sys assigned fuel).get assigned) = true
  · rw [if_neg h1, if_pos h2] at h; cases h
  by_cases h3 : sys.keys.any (fun k => (evalVector sys assigned fuel).get k == .meaningless) = true
  · rw [if_neg h1, if_neg h2, if_pos h3] at h; cases h
  rw [if_neg h1, if_neg h2, if_neg h3] at h
  split at h
  · cases h
  · rename_i hv _
    cases h
    have hcell : ∀ k ∈ sys.keys, ∃ f, (evalVector sys assigned fuel).get k = .fact f := by
      intro k hk
      have n1 : ¬ ((evalVector sys assigned fuel).get k = .exhausted ∨ (evalVector sys assigned fuel).get k = .pending) := by
        intro e
        apply h1
        unfold noVerdict
        simp only [List.any_eq_true]
        refine ⟨k, hk, ?_⟩
        rcases e with e | e <;> simp [e]
      have n2 : (evalVector sys assigned fuel).get k ≠ .meaningless := by
        intro e
        apply h3
        simp only [List.any_eq_true]
        exact ⟨k, hk, by simp [e]⟩
      cases hc : (evalVector sys assigned fuel).get k with
      | fact f => exact ⟨f, rfl⟩
      | pending => exact absurd (.inr hc) n1
      | exhausted => exact absurd (.inl hc) n1
      | meaningless => exact absurd hc n2
    refine ⟨?_, ?_, rfl⟩
    · intro k hk
      obtain ⟨f, hf⟩ := hcell k hk
      simp [hf, factOf]
    · intro l hl hk
      obtain ⟨f, hf⟩ := hcell l hk
      have : ¬ ((!f.patterns.isEmpty) != assigned l) = true := by
        intro e
        apply h2
        simp only [List.any_eq_true]
        exact ⟨l, hl, by simp [refutesClass, hf, e]⟩
      simp only [hf, factOf]
      simp only [bne_iff_ne, ne_eq, Decidable.not_not] at this
      exact this.symm

/-- EVERY READING'S FACTS ARE A FIXED POINT OF THE ONE COMPOSITION LAW: each equation's fact IS its composition over
    the facts of the reads active under this classification. -/
theorem rowOf_composed (wf : sys.WellFormed) {assigned : Nat → Bool} {v : Groundedness} {facts : Nat → Fact}
    (h : rowOf sys fuel linkSet assigned = .consistent v facts) {k : Nat} (hk : k ∈ sys.keys) :
    facts k = composeWith (sys.equation k) assigned (fun t => (facts t).patterns) := by
  obtain ⟨hcells, _, _⟩ := rowOf_consistent sys fuel linkSet h
  have good := goodCells_evalVector sys assigned fuel wf
  have hclosed := (good.closed k hk _ (hcells k hk)).2
  rw [hclosed]
  apply composeWith_congr
  intro t ht
  left
  obtain ⟨r, hr, e, _⟩ := mem_activeTargets.1 ht
  rw [hcells t ((wf.targets k hk r hr).1 t e)]
  rfl

theorem mem_subsetsOf_sub : ∀ {l s : List Nat}, s ∈ subsetsOf l → s ⊆ l := by
  intro l
  induction l with
  | nil => intro s h; simp [subsetsOf] at h; subst h; exact List.nil_subset _
  | cons x xs ih =>
    intro s h
    simp only [subsetsOf, List.mem_append, List.mem_map] at h
    rcases h with h | ⟨t, ht, rfl⟩
    · exact fun y hy => List.mem_cons_of_mem _ (ih h hy)
    · intro y hy
      rcases List.mem_cons.1 hy with rfl | hy
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih ht hy)

theorem rule_selected {rows : List Row} {facts : Nat → Fact} (h : rule rows = .selected facts) :
    rows.any Row.isExhausted = false
    ∧ rows.filter Row.isGrounded = [.consistent .grounded facts]
    ∧ rows.any Row.isUndetermined = false := by
  unfold rule at h
  by_cases h1 : rows.any Row.isExhausted = true
  · simp [h1] at h
  simp only [h1, if_false] at h
  cases hf : rows.filter Row.isGrounded with
  | nil =>
    rw [hf] at h
    simp only at h
    repeat' (split at h)
    all_goals cases h
  | cons x xs =>
    rw [hf] at h
    cases xs with
    | cons y ys => simp at h
    | nil =>
      have hx : x ∈ rows.filter Row.isGrounded := by rw [hf]; simp
      have hg := (List.mem_filter.1 hx).2
      cases x with
      | consistent v fs =>
        cases v with
        | grounded =>
          simp only at h
          by_cases hu : rows.any Row.isUndetermined = true
          · rw [if_pos hu] at h; cases h
          · rw [if_neg hu] at h
            cases h
            exact ⟨by simpa using h1, rfl, by simpa using hu⟩
        | undetermined => simp [Row.isGrounded] at hg
        | ungrounded => simp [Row.isGrounded] at hg
        | noVerdict => simp [Row.isGrounded] at hg
      | exhausted => simp [Row.isGrounded] at hg
      | refuted => simp [Row.isGrounded] at hg
      | meaningless => simp [Row.isGrounded] at hg

/-- THE OBLIGATIONS OF A COMPLETED SELECTION, none of which mentions the selection's own control:

* `composed`: every equation's fact is the one composition law over the selected facts of its active reads;
* `classified`: a link is a calculation exactly when its selected signature is nonempty (META-S3-2);
* `refutes`: every nonempty set of calculation links is REFUTED by the reading without it (groundedness);
* `only`: no other classification has a grounded reading, and none is undetermined (rule G6). -/
structure Obligations (gamma : List Nat) (facts : Nat → Fact) : Prop where
  subset : gamma ⊆ links sys
  composed : ∀ k ∈ sys.keys, facts k = composeWith (sys.equation k) (classOf gamma) (fun t => (facts t).patterns)
  classified : ∀ l ∈ links sys, classOf gamma l = !(facts l).patterns.isEmpty
  refutes : ∀ support ∈ subsetsOf ((links sys).filter (classOf gamma)), support ≠ [] →
    refutedWithout (evalVector sys (fun k => classOf gamma k && !classOf support k) fuel).get support = some true
  only : ∀ other ∈ subsetsOf (links sys), (rowOf sys fuel (links sys) (classOf other)).isGrounded = true →
    rowOf sys fuel (links sys) (classOf other) = .consistent .grounded facts
  decided : ∀ other ∈ subsetsOf (links sys), (rowOf sys fuel (links sys) (classOf other)).isUndetermined = false

private theorem groundedness_refutes {assigned : Nat → Bool}
    (h : groundednessOf sys fuel linkSet assigned = .grounded) :
    ∀ support ∈ subsetsOf (linkSet.filter assigned), support ≠ [] →
      refutedWithout (evalVector sys (fun k => assigned k && !classOf support k) fuel).get support = some true := by
  intro support hs hne
  unfold groundednessOf at h
  simp only at h
  generalize hr : ((subsetsOf (linkSet.filter assigned)).filter (fun s => !s.isEmpty)).map (fun support =>
    (support, evalVector sys (fun k => assigned k && !classOf support k) fuel)) = readings at h
  have hm : (support, evalVector sys (fun k => assigned k && !classOf support k) fuel) ∈ readings := by
    rw [← hr]
    refine List.mem_map.2 ⟨support, List.mem_filter.2 ⟨hs, ?_⟩, rfl⟩
    cases support with
    | nil => exact absurd rfl hne
    | cons _ _ => rfl
  by_cases h0 : readings.any (fun reading => noVerdict sys reading.2.get) = true
  · rw [if_pos h0] at h; cases h
  rw [if_neg h0] at h
  generalize hv : readings.map (fun reading => refutedWithout reading.2.get reading.1) = verdicts at h
  have hmv : refutedWithout (evalVector sys (fun k => assigned k && !classOf support k) fuel).get support ∈ verdicts := by
    rw [← hv]
    exact List.mem_map.2 ⟨_, hm, rfl⟩
  by_cases h1 : verdicts.contains (some false) = true
  · rw [if_pos h1] at h; cases h
  by_cases h2 : verdicts.contains none = true
  · rw [if_neg h1, if_pos h2] at h; cases h
  cases hr' : refutedWithout (evalVector sys (fun k => assigned k && !classOf support k) fuel).get support with
  | none =>
    rw [hr'] at hmv
    exact absurd (by simpa using hmv) h2
  | some b =>
    cases b with
    | true => rfl
    | false =>
      rw [hr'] at hmv
      exact absurd (by simpa using hmv) h1

/-- A SELECTED ANSWER DISCHARGES ITS OBLIGATIONS. No obligation assumes the selection: this is soundness of `select`
    against the composition law and rule G6, for every well-formed system and every bound. -/
theorem select_obligations (wf : sys.WellFormed) {facts : Nat → Fact} (h : select sys fuel = .selected facts) :
    ∃ gamma, gamma ∈ subsetsOf (links sys) ∧ Obligations sys fuel gamma facts := by
  obtain ⟨_, hfilter, hund⟩ := rule_selected h
  have hmem : Row.consistent .grounded facts ∈ ((subsetsOf (links sys)).map fun gamma =>
      rowOf sys fuel (links sys) (classOf gamma)).filter Row.isGrounded := by
    rw [hfilter]; simp
  obtain ⟨gamma, hg, hrow⟩ := List.mem_map.1 (List.mem_filter.1 hmem).1
  obtain ⟨hcells, hclass, hv⟩ := rowOf_consistent sys fuel (links sys) hrow
  refine ⟨gamma, hg, ⟨mem_subsetsOf_sub hg, fun k hk => rowOf_composed sys fuel (links sys) wf hrow hk, ?_, ?_, ?_, ?_⟩⟩
  · intro l hl
    exact hclass l hl (List.mem_filter.1 hl).1
  · exact groundedness_refutes sys fuel (links sys) hv.symm
  · intro other ho hgo
    have : rowOf sys fuel (links sys) (classOf other) ∈ ((subsetsOf (links sys)).map fun gamma =>
        rowOf sys fuel (links sys) (classOf gamma)).filter Row.isGrounded :=
      List.mem_filter.2 ⟨List.mem_map.2 ⟨other, ho, rfl⟩, hgo⟩
    rw [hfilter] at this
    simpa using this
  · intro other ho
    have := List.any_eq_false.1 hund (rowOf sys fuel (links sys) (classOf other)) (List.mem_map.2 ⟨other, ho, rfl⟩)
    simpa using this

/-- THE PUBLICATION INTERFACE: a completed result exists only together with its obligations, so nothing can be
    exposed from a refused, non-settling or exhausted selection. -/
def Completed : Type := { facts : Nat → Fact // ∃ gamma, gamma ∈ subsetsOf (links sys) ∧ Obligations sys fuel gamma facts }

/-- Publication of the reference kernel: the selected facts with their proof, and nothing else. -/
def publish (wf : sys.WellFormed) : Option (Completed sys fuel) :=
  match h : select sys fuel with
  | .selected facts => some ⟨facts, select_obligations sys fuel wf h⟩
  | .refused _ => none
  | .exhausted => none

theorem publish_refused (wf : sys.WellFormed) {c : Refusal} (h : select sys fuel = .refused c) :
    publish sys fuel wf = none := by
  unfold publish
  split <;> simp_all

theorem publish_exhausted (wf : sys.WellFormed) (h : select sys fuel = .exhausted) :
    publish sys fuel wf = none := by
  unfold publish
  split <;> simp_all

end Selection

end KatLang.SignatureCompletion
