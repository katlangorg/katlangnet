import KatLangArityLaws.SignatureCompletionEvaluation

open KatLang

/-!
# SC-1: nothing internal selects an answer

Over the reference kernel only. A relabeling renames equation keys and callee identities by bijections, and `storage` is
ANY enumeration of the renamed keys; written reference order inside each equation is untouched. `select_relabel`: the
outcome of the relabeled system is the outcome of the original, read through the renaming. So neither declaration
storage, nor equation numbering, nor callee identity allocation, nor any enumeration the kernel does can select an
answer, while written reference order stays meaningful (`SignatureCompletionGuards`: reversing it changes outcomes).
-/

namespace KatLang.SignatureCompletion

/-- A renaming of equation keys (a bijection) and of callee identities (an injection). -/
structure Relabeling where
  key : Nat → Nat
  inv : Nat → Nat
  left : ∀ k, inv (key k) = k
  right : ∀ k, key (inv k) = k
  identity : Nat → Nat
  identity_injective : ∀ {a b}, identity a = identity b → a = b

variable (ρ : Relabeling)

def Reference.relabel (r : Reference) : Reference where
  target := match r.target with
    | .member k => .member (ρ.key k)
    | .external patterns => .external patterns
  identity := ρ.identity r.identity
  guard := r.guard.map ρ.key

/-- Written reference order is kept: only names change. -/
def Equation.relabel (eq : Equation) : Equation :=
  { eq with references := eq.references.map (Reference.relabel ρ) }

/-- The renamed system over any storage order of its keys. -/
def System.relabel (sys : System) (storage : List Nat) : System where
  keys := storage
  equation k := (sys.equation (ρ.inv k)).relabel ρ

def Row.relabel : Row → Row
  | .consistent verdict facts => .consistent verdict fun k => facts (ρ.inv k)
  | row => row

def Outcome.relabel : Outcome → Outcome
  | .selected facts => .selected fun k => facts (ρ.inv k)
  | outcome => outcome

/-- Two lists hold corresponding keys. -/
def SameKeys (S S' : List Nat) : Prop := ∀ k, k ∈ S ↔ ρ.key k ∈ S'

variable {ρ}

theorem SameKeys.back {S S' : List Nat} (h : SameKeys ρ S S') {x : Nat} (hx : x ∈ S') : ρ.inv x ∈ S :=
  (h _).2 (by rw [ρ.right]; exact hx)

theorem any_relabel {S S' : List Nat} (h : SameKeys ρ S S') {p p' : Nat → Bool} (hp : ∀ k, p' (ρ.key k) = p k) :
    S'.any p' = S.any p := by
  apply Bool.eq_iff_iff.2
  simp only [List.any_eq_true]
  constructor
  · rintro ⟨x, hx, hpx⟩
    refine ⟨ρ.inv x, h.back hx, ?_⟩
    rw [← hp, ρ.right]
    exact hpx
  · rintro ⟨k, hk, hpk⟩
    exact ⟨ρ.key k, (h k).1 hk, by rw [hp]; exact hpk⟩

theorem all_relabel {S S' : List Nat} (h : SameKeys ρ S S') {p p' : Nat → Bool} (hp : ∀ k, p' (ρ.key k) = p k) :
    S'.all p' = S.all p := by
  apply Bool.eq_iff_iff.2
  simp only [List.all_eq_true]
  constructor
  · intro hall k hk
    rw [← hp]
    exact hall _ ((h k).1 hk)
  · intro hall x hx
    have := hall _ (h.back hx)
    rw [← hp, ρ.right] at this
    exact this

theorem contains_relabel {S S' : List Nat} (h : SameKeys ρ S S') (k : Nat) :
    S'.contains (ρ.key k) = S.contains k := by
  apply Bool.eq_iff_iff.2
  simp only [List.contains_iff_mem]
  exact (h k).symm

private theorem any_congr_map {α} {l : List α} {p q : α → Bool} (h : ∀ x, p x = q x) : l.any p = l.any q := by
  rw [funext h]

section Lifting

variable {opened opened' : Nat → Bool} (ho : ∀ k, opened' (ρ.key k) = opened k)
include ho

theorem active_relabel (r : Reference) : (Reference.relabel ρ r).active opened' = r.active opened := by
  unfold Reference.active Reference.relabel
  cases r.guard with
  | none => rfl
  | some g => exact ho g

theorem liftedFrom_relabel {look : Nat → Patterns} {look' : Nat → Patterns} (hl : ∀ k, look' (ρ.key k) = look k) :
    ∀ (refs : List Reference) (seen : List Nat),
    liftedFrom opened' look' (refs.map (Reference.relabel ρ)) (seen.map ρ.identity) = liftedFrom opened look refs seen := by
  intro refs
  induction refs with
  | nil => intro seen; rfl
  | cons r rest ih =>
    intro seen
    simp only [List.map_cons, liftedFrom, active_relabel ho]
    have hmem : (seen.map ρ.identity).contains (ρ.identity r.identity) = seen.contains r.identity := by
      apply Bool.eq_iff_iff.2
      simp only [List.contains_iff_mem, List.mem_map]
      constructor
      · rintro ⟨x, hx, e⟩
        rw [← ρ.identity_injective e]
        exact hx
      · exact fun h => ⟨_, h, rfl⟩
    have hsig : signatureOf look' (Reference.relabel ρ r).target = signatureOf look r.target := by
      unfold Reference.relabel
      cases r.target with
      | member k => exact hl k
      | external p => rfl
    have hid : (Reference.relabel ρ r).identity = ρ.identity r.identity := rfl
    rw [hsig, hid, hmem]
    split
    · split
      · exact ih seen
      · split
        · exact ih seen
        · rw [← ih (r.identity :: seen)]
          rfl
    · exact ih seen

theorem composeWith_relabel {look look' : Nat → Patterns} (hl : ∀ k, look' (ρ.key k) = look k) (eq : Equation) :
    composeWith (Equation.relabel ρ eq) opened' look' = composeWith eq opened look := by
  unfold composeWith Equation.relabel
  simp only
  have := liftedFrom_relabel ho hl eq.references []
  rw [List.map_nil] at this
  rw [this]

theorem activeTargets_relabel (eq : Equation) :
    activeTargets (Equation.relabel ρ eq) opened' = (activeTargets eq opened).map ρ.key := by
  unfold activeTargets Equation.relabel
  simp only [List.filterMap_map, List.map_filterMap]
  congr 1
  funext r
  simp only [Function.comp_apply]
  rw [active_relabel ho r]
  unfold Reference.relabel
  cases r.target with
  | member k => by_cases h : r.active opened = true <;> simp [h]
  | external p => rfl

end Lifting

section System

variable {sys : System} {storage : List Nat} (hs : storage.Perm (sys.keys.map ρ.key))
variable {opened opened' : Nat → Bool} (ho : ∀ k, opened' (ρ.key k) = opened k)

include hs in
theorem keys_relabel : SameKeys ρ sys.keys (sys.relabel ρ storage).keys := by
  intro k
  show k ∈ sys.keys ↔ ρ.key k ∈ storage
  rw [hs.mem_iff]
  simp only [List.mem_map]
  constructor
  · exact fun h => ⟨k, h, rfl⟩
  · rintro ⟨x, hx, e⟩
    have : x = k := by rw [← ρ.left x, e, ρ.left]
    rwa [← this]

theorem equation_relabel (k : Nat) : (sys.relabel ρ storage).equation (ρ.key k) = Equation.relabel ρ (sys.equation k) := by
  show (sys.equation (ρ.inv (ρ.key k))).relabel ρ = _
  rw [ρ.left]

include ho in
theorem active_key (k : Nat) :
    activeTargets ((sys.relabel ρ storage).equation (ρ.key k)) opened' = (activeTargets (sys.equation k) opened).map ρ.key := by
  rw [equation_relabel]
  exact activeTargets_relabel ho _

theorem map_key_mem {l : List Nat} {k : Nat} : ρ.key k ∈ l.map ρ.key ↔ k ∈ l := by
  simp only [List.mem_map]
  constructor
  · rintro ⟨x, hx, e⟩
    have : x = k := by rw [← ρ.left x, e, ρ.left]
    rwa [← this]
  · exact fun h => ⟨k, h, rfl⟩

include hs ho in
theorem grow_relabel {S S' : List Nat} (h : SameKeys ρ S S') :
    SameKeys ρ (grow sys opened S) (grow (sys.relabel ρ storage) opened' S') := by
  intro j
  rw [mem_grow, mem_grow]
  have hk := keys_relabel (ρ := ρ) (sys := sys) hs j
  constructor
  · rintro ⟨hj, hin | ⟨i, hi, ht⟩⟩
    · exact ⟨hk.1 hj, .inl ((h j).1 hin)⟩
    · refine ⟨hk.1 hj, .inr ⟨ρ.key i, (h i).1 hi, ?_⟩⟩
      rw [active_key ho]
      exact map_key_mem.2 ht
  · rintro ⟨hj, hin | ⟨i, hi, ht⟩⟩
    · exact ⟨hk.2 hj, .inl ((h j).2 hin)⟩
    · have hb := h.back hi
      refine ⟨hk.2 hj, .inr ⟨ρ.inv i, hb, ?_⟩⟩
      have e : i = ρ.key (ρ.inv i) := (ρ.right i).symm
      rw [e, active_key ho] at ht
      exact map_key_mem.1 ht

include hs ho in
theorem growN_relabel (n : Nat) : ∀ {S S' : List Nat}, SameKeys ρ S S' →
    SameKeys ρ (growN sys opened n S) (growN (sys.relabel ρ storage) opened' n S') := by
  induction n with
  | zero => exact fun h => h
  | succ n ih => exact fun h => ih (grow_relabel hs ho h)

include hs ho in
theorem reachOf_relabel (a : Nat) :
    SameKeys ρ (reachOf sys opened a) (reachOf (sys.relabel ρ storage) opened' (ρ.key a)) := by
  unfold reachOf
  have hlen : (sys.relabel ρ storage).keys.length = sys.keys.length := by
    show storage.length = _
    rw [hs.length_eq, List.length_map]
  rw [hlen]
  apply growN_relabel hs ho
  apply grow_relabel hs ho
  intro k
  simp only [List.mem_singleton]
  constructor
  · exact fun e => by rw [e]
  · intro e
    rw [← ρ.left k, e, ρ.left]

include hs ho in
theorem reachTable_relabel (a : Nat) :
    SameKeys ρ (reachTable sys opened a) (reachTable (sys.relabel ρ storage) opened' (ρ.key a)) := by
  by_cases ha : a ∈ sys.keys
  · rw [reachTable_of_mem sys opened ha,
      reachTable_of_mem _ opened' ((keys_relabel (ρ := ρ) (sys := sys) hs a).1 ha)]
    exact reachOf_relabel hs ho a
  · have h1 : reachTable sys opened a = [] := tabulate_of_not_mem _ _ _ ha
    have h2 : reachTable (sys.relabel ρ storage) opened' (ρ.key a) = [] :=
      tabulate_of_not_mem _ _ _ (fun h => ha ((keys_relabel (ρ := ρ) (sys := sys) hs a).2 h))
    rw [h1, h2]
    intro k
    simp

include hs ho in
theorem sameComponent_relabel (a b : Nat) :
    sameComponent (reachTable (sys.relabel ρ storage) opened') (ρ.key a) (ρ.key b)
      = sameComponent (reachTable sys opened) a b := by
  unfold sameComponent
  rw [contains_relabel (reachTable_relabel hs ho a), contains_relabel (reachTable_relabel hs ho b)]

include hs ho in
theorem componentOf_relabel (a : Nat) :
    SameKeys ρ (componentOf sys (reachTable sys opened) a)
      (componentOf (sys.relabel ρ storage) (reachTable (sys.relabel ρ storage) opened') (ρ.key a)) := by
  intro k
  rw [mem_componentOf, mem_componentOf, sameComponent_relabel hs ho]
  have := keys_relabel (ρ := ρ) (sys := sys) hs k
  constructor
  · exact fun ⟨h1, h2⟩ => ⟨this.1 h1, h2⟩
  · exact fun ⟨h1, h2⟩ => ⟨this.2 h1, h2⟩

variable {members members' : List Nat} (hm : SameKeys ρ members members')
variable {lower lower' : Nat → Patterns} (hl : ∀ k, lower' (ρ.key k) = lower k)

include hm hl in
theorem readThrough_relabel {state state' : Nat → Fact} (hst : ∀ k, state' (ρ.key k) = state k) (t : Nat) :
    readThrough members' lower' state' (ρ.key t) = readThrough members lower state t := by
  unfold readThrough
  rw [contains_relabel hm, hst, hl]

include ho hm hl in
theorem roundStep_relabel {state : Memo Fact} {state' : Memo Fact} (hst : ∀ k, state'.get (ρ.key k) = state.get k) (k : Nat) :
    (roundStep (sys.relabel ρ storage) opened' members' lower' state').get (ρ.key k)
      = (roundStep sys opened members lower state).get k := by
  by_cases hk : k ∈ members
  · rw [roundStep_of_mem _ _ _ _ _ hk, roundStep_of_mem _ _ _ _ _ ((hm k).1 hk)]
    unfold nextFact
    rw [equation_relabel]
    exact composeWith_relabel ho (readThrough_relabel hm hl hst) _
  · have h1 : (roundStep sys opened members lower state).get k = closedFact := tabulate_of_not_mem _ _ _ hk
    have h2 : (roundStep (sys.relabel ρ storage) opened' members' lower' state').get (ρ.key k) = closedFact :=
      tabulate_of_not_mem _ _ _ (fun h => hk ((hm k).2 h))
    rw [h1, h2]

include hm in
theorem sameState_relabel {a a' b b' : Memo Fact} (ha : ∀ k, a'.get (ρ.key k) = a.get k)
    (hb : ∀ k, b'.get (ρ.key k) = b.get k) : sameState members' a' b' = sameState members a b := by
  unfold sameState
  apply all_relabel hm
  intro k
  rw [ha, hb]

/-- The rounds run alike: same verdict, corresponding states. -/
def RoundRelated : RoundOutcome (Memo Fact) → RoundOutcome (Memo Fact) → Prop
  | .settled a, .settled a' => ∀ k, a'.get (ρ.key k) = a.get k
  | .nonSettling, .nonSettling => True
  | .exhausted, .exhausted => True
  | _, _ => False

include ho hm hl in
theorem completeLoop_relabel : ∀ (fuel : Nat) {previous previous' saved saved' : Memo Fact} (age window : Nat),
    (∀ k, previous'.get (ρ.key k) = previous.get k) → (∀ k, saved'.get (ρ.key k) = saved.get k) →
    RoundRelated (ρ := ρ)
      (completeLoop (roundStep sys opened members lower) (sameState members) fuel previous saved age window)
      (completeLoop (roundStep (sys.relabel ρ storage) opened' members' lower') (sameState members') fuel previous' saved' age window) := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ _ _ _ _; exact trivial
  | succ fuel ih =>
    intro previous previous' saved saved' age window hp hs'
    have hc := roundStep_relabel (storage := storage) (sys := sys) ho hm hl hp
    simp only [completeLoop]
    rw [sameState_relabel hm hp hc, sameState_relabel hm hs' hc]
    split
    · exact hc
    · split
      · exact trivial
      · split
        · exact ih _ _ hc hc
        · exact ih _ _ hc hs'

end System

section Evaluation

variable {sys : System} {storage : List Nat} (hs : storage.Perm (sys.keys.map ρ.key))
variable {opened opened' : Nat → Bool} (ho : ∀ k, opened' (ρ.key k) = opened k)

/-- Two readings correspond. -/
abbrev CellsRelated (cells cells' : Nat → Cell) : Prop := ∀ k, cells' (ρ.key k) = cells k

include ho in
theorem outsideReads_relabel {members members' : List Nat} (hm : SameKeys ρ members members') :
    SameKeys ρ (outsideReads sys opened members) (outsideReads (sys.relabel ρ storage) opened' members') := by
  intro t
  rw [mem_outsideReads, mem_outsideReads]
  constructor
  · rintro ⟨k, hk, ht, hn⟩
    refine ⟨ρ.key k, (hm k).1 hk, ?_, fun h => hn ((hm t).2 h)⟩
    rw [active_key ho]
    exact map_key_mem.2 ht
  · rintro ⟨x, hx, ht, hn⟩
    have hb := hm.back hx
    refine ⟨ρ.inv x, hb, ?_, fun h => hn ((hm t).1 h)⟩
    have e : x = ρ.key (ρ.inv x) := (ρ.right x).symm
    rw [e, active_key ho] at ht
    exact map_key_mem.1 ht

theorem lowerReads_relabel_aux {members members' : List Nat} (hm : SameKeys ρ members members')
    (ho : ∀ k, opened' (ρ.key k) = opened k) {cells cells' : Nat → Cell} (hc : CellsRelated (ρ := ρ) cells cells') (t : Nat) :
    lowerReads (sys.relabel ρ storage) opened' members' cells' (ρ.key t) = lowerReads sys opened members cells t := by
  unfold lowerReads
  rw [contains_relabel (outsideReads_relabel ho hm), hc]

include ho in
theorem gateState_relabel {members members' : List Nat} (hm : SameKeys ρ members members')
    {lower lower' : Nat → Patterns} (hl : ∀ k, lower' (ρ.key k) = lower k) (k : Nat) :
    (gateState (sys.relabel ρ storage) opened' members' lower').get (ρ.key k)
      = (gateState sys opened members lower).get k :=
  roundStep_relabel (storage := storage) (sys := sys) ho hm hl (state := ⟨fun _ => closedFact⟩)
    (state' := ⟨fun _ => closedFact⟩) (fun _ => rfl) k

include ho in
theorem gateLifts_relabel {members members' : List Nat} (hm : SameKeys ρ members members')
    {lower lower' : Nat → Patterns} (hl : ∀ k, lower' (ρ.key k) = lower k) :
    gateLifts (sys.relabel ρ storage) opened' members' lower' = gateLifts sys opened members lower := by
  unfold gateLifts
  simp only
  apply any_relabel hm
  intro k
  rw [active_key ho, List.any_map]
  apply any_congr_map
  intro t
  simp only [Function.comp_apply]
  rw [contains_relabel hm, gateState_relabel ho hm hl]

include ho in
theorem evalComponent_relabel {members members' : List Nat} (hm : SameKeys ρ members members') (fuel : Nat)
    {cells cells' : Nat → Cell} (hc : CellsRelated (ρ := ρ) cells cells') (k : Nat) :
    evalComponent (sys.relabel ρ storage) opened' fuel members' cells' (ρ.key k)
      = evalComponent sys opened fuel members cells k := by
  have hout := outsideReads_relabel (sys := sys) (storage := storage) ho hm
  have hl := lowerReads_relabel_aux (sys := sys) (storage := storage) hm ho hc
  have h1 : (outsideReads (sys.relabel ρ storage) opened' members').any (fun t => cells' t == .exhausted)
      = (outsideReads sys opened members).any (fun t => cells t == .exhausted) :=
    any_relabel hout fun t => by rw [hc]
  have h2 : (outsideReads (sys.relabel ρ storage) opened' members').any (fun t => cells' t == .meaningless)
      = (outsideReads sys opened members).any (fun t => cells t == .meaningless) :=
    any_relabel hout fun t => by rw [hc]
  have h3 := gateLifts_relabel (sys := sys) (storage := storage) ho hm hl
  have h4 := gateState_relabel (sys := sys) (storage := storage) ho hm hl
  have h5 := completeLoop_relabel (sys := sys) (storage := storage) ho hm hl fuel 0 1 h4 h4
  unfold evalComponent
  simp only
  rw [h1, h2, h3]
  split
  · rfl
  · split
    · rfl
    · split
      · exact congrArg Cell.fact (h4 k)
      · revert h5
        generalize completeLoop (roundStep sys opened members (lowerReads sys opened members cells)) (sameState members) fuel
          (gateState sys opened members (lowerReads sys opened members cells))
          (gateState sys opened members (lowerReads sys opened members cells)) 0 1 = outcome
        generalize completeLoop (roundStep (sys.relabel ρ storage) opened' members'
          (lowerReads (sys.relabel ρ storage) opened' members' cells')) (sameState members') fuel
          (gateState (sys.relabel ρ storage) opened' members' (lowerReads (sys.relabel ρ storage) opened' members' cells'))
          (gateState (sys.relabel ρ storage) opened' members' (lowerReads (sys.relabel ρ storage) opened' members' cells')) 0 1 = outcome'
        intro h5
        cases outcome <;> cases outcome' <;> first | rfl | exact congrArg Cell.fact (h5 k) | exact False.elim h5

include hs ho in
theorem layer_relabel (fuel : Nat) {cells cells' : Memo Cell} (hc : CellsRelated (ρ := ρ) cells.get cells'.get) (k : Nat) :
    (layer (sys.relabel ρ storage) opened' fuel (reachTable (sys.relabel ρ storage) opened') cells').get (ρ.key k)
      = (layer sys opened fuel (reachTable sys opened) cells).get k := by
  have hkeys := keys_relabel (ρ := ρ) (sys := sys) hs
  by_cases hk : k ∈ sys.keys
  · rw [layer_apply _ _ _ _ _ ((hkeys k).1 hk), layer_apply _ _ _ _ _ hk, hc k]
    cases hcell : cells.get k with
    | fact f => rfl
    | meaningless => rfl
    | exhausted => rfl
    | pending =>
      simp only
      have hcomp := componentOf_relabel hs ho k
      have hready : layerReady (sys.relabel ρ storage) opened'
            (componentOf (sys.relabel ρ storage) (reachTable (sys.relabel ρ storage) opened') (ρ.key k)) cells'.get
          = layerReady sys opened (componentOf sys (reachTable sys opened) k) cells.get :=
        all_relabel (outsideReads_relabel ho hcomp) fun t => by rw [hc t]
      rw [hready]
      split
      · exact evalComponent_relabel ho hcomp fuel hc k
      · rfl
  · have h1 : (layer sys opened fuel (reachTable sys opened) cells).get k = .pending := tabulate_of_not_mem _ _ _ hk
    have h2 : (layer (sys.relabel ρ storage) opened' fuel (reachTable (sys.relabel ρ storage) opened') cells').get (ρ.key k) = .pending :=
      tabulate_of_not_mem _ _ _ (fun h => hk ((hkeys k).2 h))
    rw [h1, h2]

include hs ho in
theorem layers_relabel (fuel n : Nat) : ∀ {cells cells' : Memo Cell}, CellsRelated (ρ := ρ) cells.get cells'.get →
    CellsRelated (ρ := ρ) (layers sys opened fuel (reachTable sys opened) n cells).get
      (layers (sys.relabel ρ storage) opened' fuel (reachTable (sys.relabel ρ storage) opened') n cells').get := by
  induction n with
  | zero => exact fun h => h
  | succ n ih => exact fun h => ih (fun k => layer_relabel hs ho fuel h k)

include hs ho in
theorem evalVector_relabel (fuel : Nat) :
    CellsRelated (ρ := ρ) (evalVector sys opened fuel).get (evalVector (sys.relabel ρ storage) opened' fuel).get := by
  have hlen : (sys.relabel ρ storage).keys.length = sys.keys.length := by
    show storage.length = _
    rw [hs.length_eq, List.length_map]
  unfold evalVector
  rw [hlen]
  exact layers_relabel hs ho fuel _ (cells := ⟨fun _ => .pending⟩) (cells' := ⟨fun _ => .pending⟩) fun _ => rfl

include hs in
theorem noVerdict_relabel {cells cells' : Nat → Cell} (hc : CellsRelated (ρ := ρ) cells cells') :
    noVerdict (sys.relabel ρ storage) cells' = noVerdict sys cells := by
  unfold noVerdict
  exact any_relabel (keys_relabel hs) fun k => by rw [hc]

theorem refutedWithout_relabel {cells cells' : Nat → Cell} (hc : CellsRelated (ρ := ρ) cells cells') {s s' : List Nat}
    (hss : SameKeys ρ s s') : refutedWithout cells' s' = refutedWithout cells s := by
  unfold refutedWithout
  have h1 := any_relabel hss (p := stillCalculation cells) (p' := stillCalculation cells') fun k => by
    unfold stillCalculation; rw [hc]
  have h2 := any_relabel hss (p := undecidedLink cells) (p' := undecidedLink cells') fun k => by
    unfold undecidedLink; rw [hc]
  rw [h1, h2]

end Evaluation

/-! ### Subsets under renaming and reordering -/

private theorem subsets_map_key (key : Nat → Nat) : ∀ l : List Nat,
    subsetsOf (l.map key) = (subsetsOf l).map (·.map key) := by
  intro l
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, subsetsOf, ih, List.map_append, List.map_map]
    rfl

/-- Reordering a list reorders its subsets, each up to the order of its own elements. -/
private theorem subsets_perm {β} (F : List Nat → β) (hF : ∀ a b : List Nat, (∀ x, x ∈ a ↔ x ∈ b) → F a = F b)
    {l l' : List Nat} (h : l.Perm l') : ((subsetsOf l).map F).Perm ((subsetsOf l').map F) := by
  induction h generalizing F with
  | nil => exact List.Perm.refl _
  | cons x _ ih =>
    simp only [subsetsOf, List.map_append, List.map_map]
    exact (ih F hF).append (ih (F ∘ (x :: ·)) (fun a b hab => hF _ _ fun y => by simp [hab y]))
  | swap x y l =>
    simp only [subsetsOf, List.map_append, List.map_map]
    have e : (F ∘ (x :: ·)) ∘ (y :: ·) = (F ∘ (y :: ·)) ∘ (x :: ·) := by
      funext s
      apply hF
      intro z
      simp only [List.mem_cons]
      constructor
      · rintro (h | h | h)
        · exact .inr (.inl h)
        · exact .inl h
        · exact .inr (.inr h)
      · rintro (h | h | h)
        · exact .inr (.inl h)
        · exact .inl h
        · exact .inr (.inr h)
    have e' : (F ∘ fun t => y :: x :: t) = (F ∘ fun t => x :: y :: t) := by
      funext s
      apply hF
      intro z
      simp only [List.mem_cons]
      constructor
      · rintro (h | h | h)
        · exact .inr (.inl h)
        · exact .inl h
        · exact .inr (.inr h)
      · rintro (h | h | h)
        · exact .inr (.inl h)
        · exact .inl h
        · exact .inr (.inr h)
    simp only [Function.comp_def] at e' ⊢
    rw [e']
    simp only [List.append_assoc]
    apply List.Perm.append_left
    rw [← List.append_assoc, ← List.append_assoc]
    exact List.Perm.append_right _ List.perm_append_comm
  | trans _ _ ih1 ih2 => exact (ih1 F hF).trans (ih2 F hF)

section Selection

variable {sys : System} {storage : List Nat} (hs : storage.Perm (sys.keys.map ρ.key))

include hs in
private theorem links_relabel : (links (sys.relabel ρ storage)).Perm ((links sys).map ρ.key) := by
  unfold links
  have h1 := hs.filter (fun k => ((sys.relabel ρ storage).equation k).isLink)
  refine h1.trans ?_
  rw [List.filter_map]
  have : ((fun k => ((sys.relabel ρ storage).equation k).isLink) ∘ ρ.key) = fun k => (sys.equation k).isLink := by
    funext k
    simp only [Function.comp_apply]
    rw [equation_relabel]
    rfl
  rw [this]

/-- The class of a renamed subset. -/
private theorem classOf_map (s : List Nat) (k : Nat) : classOf (s.map ρ.key) (ρ.key k) = classOf s k := by
  unfold classOf
  apply Bool.eq_iff_iff.2
  simp only [List.contains_iff_mem]
  exact map_key_mem

private theorem classOf_iff {s : List Nat} {k : Nat} : classOf s k = true ↔ k ∈ s := by
  simp [classOf]

private theorem classOf_same {a b : List Nat} (h : ∀ x, x ∈ a ↔ x ∈ b) : classOf a = classOf b := by
  funext k
  apply Bool.eq_iff_iff.2
  rw [classOf_iff, classOf_iff]
  exact h k

private theorem any_filter_eq {α} (l : List α) (q p : α → Bool) :
    (l.filter q).any p = l.any fun x => q x && p x := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.filter_cons, List.any_cons]
    by_cases h : q x = true
    · simp [h, ih]
    · simp [h, ih]

private theorem contains_map_any {α} (l : List α) (f : α → Option Bool) (v : Option Bool) :
    (l.map f).contains v = l.any fun x => f x == v := by
  apply Bool.eq_iff_iff.2
  simp [List.mem_map, List.any_eq_true]

/-- Every subset of a reordered list has a subset with the same elements. -/
private theorem subsets_sim {l l' s : List Nat} (h : l.Perm l') (hs : s ∈ subsetsOf l) :
    ∃ s' ∈ subsetsOf l', ∀ x, x ∈ s ↔ x ∈ s' := by
  have hperm := subsets_perm classOf (fun _ _ hab => classOf_same hab) h
  have : classOf s ∈ (subsetsOf l').map classOf := hperm.mem_iff.1 (List.mem_map_of_mem hs)
  obtain ⟨s', hs', e⟩ := List.mem_map.1 this
  refine ⟨s', hs', fun x => ?_⟩
  rw [← classOf_iff, ← classOf_iff (s := s'), e]

/-- A question about subsets is the same question after renaming and reordering. -/
private theorem any_subsets {c c' : List Nat} (h : c'.Perm (c.map ρ.key)) {P P' : List Nat → Bool}
    (hP : ∀ s s', SameKeys ρ s s' → P' s' = P s) : (subsetsOf c').any P' = (subsetsOf c).any P := by
  apply Bool.eq_iff_iff.2
  simp only [List.any_eq_true]
  constructor
  · rintro ⟨s', hs', hp⟩
    obtain ⟨s'', hs'', e⟩ := subsets_sim h hs'
    rw [subsets_map_key] at hs''
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hs''
    refine ⟨s, hs, ?_⟩
    rw [← hP s s' (fun k => by rw [e]; exact map_key_mem.symm)]
    exact hp
  · rintro ⟨s, hs, hp⟩
    have hmapped : s.map ρ.key ∈ subsetsOf (c.map ρ.key) := by
      rw [subsets_map_key]
      exact List.mem_map_of_mem hs
    obtain ⟨s', hs', e⟩ := subsets_sim h.symm hmapped
    refine ⟨s', hs', ?_⟩
    rw [hP s s' (fun k => by rw [← e]; exact map_key_mem.symm)]
    exact hp

private theorem isEmpty_relabel {s s' : List Nat} (h : SameKeys ρ s s') : s'.isEmpty = s.isEmpty := by
  cases s with
  | cons x xs =>
    have : ρ.key x ∈ s' := (h x).1 List.mem_cons_self
    cases s' with
    | nil => cases this
    | cons _ _ => rfl
  | nil =>
    cases s' with
    | nil => rfl
    | cons y ys =>
      have : ρ.inv y ∈ ([] : List Nat) := h.back List.mem_cons_self
      cases this

variable {linkSet linkSet' : List Nat} (hlinks : linkSet'.Perm (linkSet.map ρ.key))
variable {assigned assigned' : Nat → Bool} (ho : ∀ k, assigned' (ρ.key k) = assigned k)

private theorem sameKeys_of_perm (hlinks : linkSet'.Perm (linkSet.map ρ.key)) : SameKeys ρ linkSet linkSet' := by
  intro k
  rw [hlinks.mem_iff]
  exact map_key_mem.symm

include hlinks ho in
private theorem calculations_relabel :
    (linkSet'.filter assigned').Perm ((linkSet.filter assigned).map ρ.key) := by
  refine (hlinks.filter assigned').trans ?_
  rw [List.filter_map]
  have : assigned' ∘ ρ.key = assigned := funext ho
  rw [this]

/-- The counterfactual classifications correspond. -/
private theorem counterfactual_key (ho : ∀ k, assigned' (ρ.key k) = assigned k) {s s' : List Nat} (h : SameKeys ρ s s') (k : Nat) :
    (fun x => assigned' x && !classOf s' x) (ρ.key k) = (fun x => assigned x && !classOf s x) k := by
  simp only [ho]
  have : classOf s' (ρ.key k) = classOf s k := contains_relabel h k
  rw [this]

include hs hlinks ho in
theorem groundednessOf_relabel (fuel : Nat) :
    groundednessOf (sys.relabel ρ storage) fuel linkSet' assigned' = groundednessOf sys fuel linkSet assigned := by
  have hcalc := calculations_relabel hlinks ho
  have hQ1 : (subsetsOf (linkSet'.filter assigned')).any
        (fun s => !s.isEmpty && noVerdict (sys.relabel ρ storage)
          (evalVector (sys.relabel ρ storage) (fun k => assigned' k && !classOf s k) fuel).get)
      = (subsetsOf (linkSet.filter assigned)).any
        (fun s => !s.isEmpty && noVerdict sys (evalVector sys (fun k => assigned k && !classOf s k) fuel).get) :=
    any_subsets hcalc fun s s' hss => by
      rw [isEmpty_relabel hss, noVerdict_relabel hs (evalVector_relabel hs (counterfactual_key ho hss) fuel)]
  have hQ2 : ∀ v : Option Bool, (subsetsOf (linkSet'.filter assigned')).any
        (fun s => !s.isEmpty && refutedWithout
          (evalVector (sys.relabel ρ storage) (fun k => assigned' k && !classOf s k) fuel).get s == v)
      = (subsetsOf (linkSet.filter assigned)).any
        (fun s => !s.isEmpty && refutedWithout (evalVector sys (fun k => assigned k && !classOf s k) fuel).get s == v) :=
    fun v => any_subsets hcalc fun s s' hss => by
      rw [isEmpty_relabel hss, refutedWithout_relabel (evalVector_relabel hs (counterfactual_key ho hss) fuel) hss]
  unfold groundednessOf
  simp only [List.any_map, List.map_map, Function.comp_def, contains_map_any, any_filter_eq]
  rw [hQ1, hQ2 (some false), hQ2 none]

include hs hlinks ho in
theorem rowOf_relabel (fuel : Nat) :
    rowOf (sys.relabel ρ storage) fuel linkSet' assigned' = Row.relabel ρ (rowOf sys fuel linkSet assigned) := by
  have hc := evalVector_relabel hs ho fuel
  have h1 := noVerdict_relabel hs hc
  have h2 : linkSet'.any (refutesClass (evalVector (sys.relabel ρ storage) assigned' fuel).get assigned')
      = linkSet.any (refutesClass (evalVector sys assigned fuel).get assigned) :=
    any_relabel (sameKeys_of_perm hlinks) fun l => by
      unfold refutesClass
      rw [hc, ho]
  have h3 : (sys.relabel ρ storage).keys.any (fun k => (evalVector (sys.relabel ρ storage) assigned' fuel).get k == .meaningless)
      = sys.keys.any (fun k => (evalVector sys assigned fuel).get k == .meaningless) :=
    any_relabel (keys_relabel hs) fun k => by rw [hc]
  unfold rowOf
  simp only
  rw [h1, h2, h3, groundednessOf_relabel hs hlinks ho fuel]
  have hfacts : (fun k => factOf ((evalVector (sys.relabel ρ storage) assigned' fuel).get k))
      = fun k => factOf ((evalVector sys assigned fuel).get (ρ.inv k)) := by
    funext x
    have := hc (ρ.inv x)
    rw [ρ.right] at this
    rw [this]
  rw [hfacts]
  split
  · rfl
  · split
    · rfl
    · split
      · rfl
      · generalize groundednessOf sys fuel linkSet assigned = v
        cases v <;> rfl

private theorem any_of_perm {α} {l l' : List α} (h : l.Perm l') (p : α → Bool) : l.any p = l'.any p := by
  apply Bool.eq_iff_iff.2
  simp only [List.any_eq_true]
  constructor
  · rintro ⟨x, hx, hp⟩
    exact ⟨x, h.mem_iff.1 hx, hp⟩
  · rintro ⟨x, hx, hp⟩
    exact ⟨x, h.mem_iff.2 hx, hp⟩

/-- Rule G6 reads its rows as a multiset: no enumeration of the classifications matters. -/
theorem rule_perm {rows rows' : List Row} (h : rows.Perm rows') : rule rows = rule rows' := by
  unfold rule
  rw [any_of_perm h, any_of_perm h Row.isUndetermined, any_of_perm h Row.isUngrounded, any_of_perm h Row.isMeaningless]
  have hf := h.filter Row.isGrounded
  split
  · rfl
  · generalize rows.filter Row.isGrounded = a at hf
    generalize rows'.filter Row.isGrounded = b at hf
    cases a with
    | nil => rw [hf.symm.eq_nil]
    | cons x xs =>
      cases xs with
      | nil => rw [List.perm_singleton.1 hf.symm]
      | cons y ys =>
        have hlen := hf.length_eq
        cases b with
        | nil => simp at hlen
        | cons u us =>
          cases us with
          | nil => simp at hlen
          | cons v vs => rfl

private theorem relabel_isExhausted (r : Row) : (Row.relabel ρ r).isExhausted = r.isExhausted := by cases r <;> rfl
private theorem relabel_isGrounded (r : Row) : (Row.relabel ρ r).isGrounded = r.isGrounded := by
  cases r with
  | consistent v f => cases v <;> rfl
  | _ => rfl
private theorem relabel_isUndetermined (r : Row) : (Row.relabel ρ r).isUndetermined = r.isUndetermined := by
  cases r with
  | consistent v f => cases v <;> rfl
  | _ => rfl
private theorem relabel_isUngrounded (r : Row) : (Row.relabel ρ r).isUngrounded = r.isUngrounded := by
  cases r with
  | consistent v f => cases v <;> rfl
  | _ => rfl
private theorem relabel_isMeaningless (r : Row) : (Row.relabel ρ r).isMeaningless = r.isMeaningless := by cases r <;> rfl

/-- Rule G6 commutes with the renaming. -/
theorem rule_relabel (rows : List Row) : rule (rows.map (Row.relabel ρ)) = Outcome.relabel ρ (rule rows) := by
  have e1 : ∀ p q : Row → Bool, (∀ r, p (Row.relabel ρ r) = q r) → (rows.map (Row.relabel ρ)).any p = rows.any q := by
    intro p q h
    rw [List.any_map]
    congr 1
    funext r
    exact h r
  have hfilter : (rows.map (Row.relabel ρ)).filter Row.isGrounded = (rows.filter Row.isGrounded).map (Row.relabel ρ) := by
    rw [List.filter_map]
    congr 1
    congr 1
    funext r
    exact relabel_isGrounded r
  unfold rule
  rw [e1 _ _ relabel_isExhausted, e1 _ _ relabel_isUndetermined, e1 _ _ relabel_isUngrounded,
    e1 _ _ relabel_isMeaningless, hfilter]
  split
  · rfl
  · cases hg : rows.filter Row.isGrounded with
    | nil =>
      simp only [List.map_nil]
      split
      · rfl
      · split
        · rfl
        · split <;> rfl
    | cons x xs =>
      cases xs with
      | cons y ys => rfl
      | nil =>
        cases x with
        | consistent v fs =>
          simp only [List.map_cons, List.map_nil, Row.relabel]
          split <;> rfl
        | exhausted => rfl
        | refuted => rfl
        | meaningless => rfl

include hs in
/-- NO ENUMERATION SELECTS AN ANSWER. Renaming equation keys and callee identities and storing the keys in ANY order gives
    the same outcome read through the renaming, for every bound. Written reference order is kept by the relabeling, and
    it is the one order that stays meaningful. No well-formedness premise is needed. -/
theorem select_relabel (fuel : Nat) :
    select (sys.relabel ρ storage) fuel = Outcome.relabel ρ (select sys fuel) := by
  have hl := links_relabel (ρ := ρ) (sys := sys) hs
  unfold select
  simp only
  rw [← rule_relabel, List.map_map]
  have step1 : ((subsetsOf (links (sys.relabel ρ storage))).map fun gamma =>
        rowOf (sys.relabel ρ storage) fuel (links (sys.relabel ρ storage)) (classOf gamma)).Perm
      ((subsetsOf ((links sys).map ρ.key)).map fun gamma =>
        rowOf (sys.relabel ρ storage) fuel (links (sys.relabel ρ storage)) (classOf gamma)) :=
    subsets_perm _ (fun a b hab => by rw [classOf_same hab]) hl
  rw [rule_perm step1, subsets_map_key, List.map_map]
  congr 1
  apply List.map_congr_left
  intro gamma _
  simp only [Function.comp_apply]
  exact rowOf_relabel hs hl (classOf_map gamma) fuel

end Selection

/-- The renaming that renames nothing. -/
def Relabeling.refl : Relabeling where
  key := id
  inv := id
  left _ := rfl
  right _ := rfl
  identity := id
  identity_injective h := h

private theorem relabel_refl_reference (r : Reference) : Reference.relabel Relabeling.refl r = r := by
  obtain ⟨target, identity, guard⟩ := r
  unfold Reference.relabel
  cases target <;> cases guard <;> rfl

/-- DECLARATION STORAGE SELECTS NOTHING: permuting the keys of a system changes no outcome, under any bound. -/
theorem select_storage_independent {sys : System} {storage : List Nat} (h : storage.Perm sys.keys) (fuel : Nat) :
    select { keys := storage, equation := sys.equation } fuel = select sys fuel := by
  have hs : storage.Perm (sys.keys.map Relabeling.refl.key) := by
    have : sys.keys.map Relabeling.refl.key = sys.keys := List.map_id _
    rw [this]
    exact h
  have hsys : sys.relabel Relabeling.refl storage = { keys := storage, equation := sys.equation } := by
    unfold System.relabel
    congr 1
    funext k
    show (sys.equation k).relabel Relabeling.refl = sys.equation k
    unfold Equation.relabel
    have : (sys.equation k).references.map (Reference.relabel Relabeling.refl) = (sys.equation k).references := by
      conv => rhs; rw [← List.map_id (sys.equation k).references]
      exact List.map_congr_left fun r _ => relabel_refl_reference r
    rw [this]
  rw [← hsys, select_relabel hs fuel]
  cases select sys fuel <;> rfl

end KatLang.SignatureCompletion
