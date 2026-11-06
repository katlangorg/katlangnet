import KatLangArityLaws.SignatureCompletion

open KatLang

/-!
# SC-1: the laws of simultaneous completion

Over the reference kernel only (`SignatureCompletion.lean`), never about C#. `completeLoop` is generic: a settled state is a
state its round reproduces, a non-settling verdict is an exact repetition at distance at least two on one deterministic
orbit (`completeLoop_nonSettling_spec`), and such an orbit never settles (`repetition_never_settles`). Monotonicity, convergence,
and uniqueness of fixed points are not assumed and not true: `SignatureCompletionGuards.otherFixedPoint`.
-/

namespace KatLang.SignatureCompletion

/-! ## Rounds: the generic loop -/

section Loop

variable {σ : Type} (step : σ → σ) (same : σ → σ → Bool)

/-- The orbit of a transition. -/
def orbit (start : σ) : Nat → σ
  | 0 => start
  | .succ n => step (orbit start n)

/-- What the state comparison must satisfy for a repetition to mean anything: it is an equivalence and the
    transition respects it. -/
structure LawfulRound : Prop where
  refl : ∀ a, same a a = true
  symm : ∀ {a b}, same a b = true → same b a = true
  trans : ∀ {a b c}, same a b = true → same b c = true → same a c = true
  congr : ∀ {a b}, same a b = true → same (step a) (step b) = true

/-- ONLY `.exhausted` DEPENDS ON THE BOUND: a verdict is the same under every larger bound. -/
theorem completeLoop_verdict_stable : ∀ (fuel more : Nat) (previous saved : σ) (age window : Nat),
    (∀ s, completeLoop step same fuel previous saved age window = .settled s →
      completeLoop step same (fuel + more) previous saved age window = .settled s)
    ∧ (completeLoop step same fuel previous saved age window = .nonSettling →
      completeLoop step same (fuel + more) previous saved age window = .nonSettling) := by
  intro fuel
  induction fuel with
  | zero =>
    intro more previous saved age window
    exact ⟨fun s h => by simp [completeLoop] at h, fun h => by simp [completeLoop] at h⟩
  | succ fuel ih =>
    intro more previous saved age window
    have : fuel + 1 + more = (fuel + more) + 1 := by omega
    rw [this]
    simp only [completeLoop]
    split
    · exact ⟨fun _ h => h, fun h => h⟩
    · split
      · exact ⟨fun _ h => h, fun h => h⟩
      · split
        · exact ih more _ _ _ _
        · exact ih more _ _ _ _

/-- A SETTLED answer is a state equal to the state it was computed from. -/
theorem completeLoop_settled_spec : ∀ (fuel : Nat) (previous saved : σ) (age window : Nat) (state : σ),
    completeLoop step same fuel previous saved age window = .settled state →
    ∃ n, state = step (orbit step previous n) ∧ same (orbit step previous n) state = true := by
  intro fuel
  induction fuel with
  | zero => intro previous saved age window state h; simp [completeLoop] at h
  | succ fuel ih =>
    intro previous saved age window state h
    simp only [completeLoop] at h
    have shift : ∀ n, orbit step (step previous) n = orbit step previous (n + 1) := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih => exact congrArg step ih
    split at h
    · rename_i hs
      cases h
      exact ⟨0, rfl, hs⟩
    · split at h
      · cases h
      · split at h
        all_goals
          obtain ⟨n, h1, h2⟩ := ih _ _ _ _ _ h
          rw [shift] at h1 h2
          exact ⟨n + 1, h1, h2⟩

/-- A NON-SETTLING verdict is an EXACT repetition at distance at least two, and every earlier pair of successive
    states differed: this is what Brent's detector establishes, on the deterministic orbit. -/
theorem completeLoop_nonSettling_spec (start : σ) : ∀ (fuel i j age window : Nat),
    i = j + age →
    (∀ m, m < i → same (orbit step start m) (orbit step start (m + 1)) = false) →
    completeLoop step same fuel (orbit step start i) (orbit step start j) age window = .nonSettling →
    ∃ a b, a + 2 ≤ b ∧ same (orbit step start a) (orbit step start b) = true
      ∧ ∀ m, m < b → same (orbit step start m) (orbit step start (m + 1)) = false := by
  intro fuel
  induction fuel with
  | zero => intro i j age window _ _ h; simp [completeLoop] at h
  | succ fuel ih =>
    intro i j age window hi hm h
    simp only [completeLoop] at h
    have hstep : step (orbit step start i) = orbit step start (i + 1) := rfl
    rw [hstep] at h
    split at h
    · cases h
    · rename_i hne
      have hne' : same (orbit step start i) (orbit step start (i + 1)) = false := by
        simpa using hne
      have hextend : ∀ m, m < i + 1 → same (orbit step start m) (orbit step start (m + 1)) = false := by
        intro m hlt
        by_cases hm' : m < i
        · exact hm m hm'
        · have : m = i := by omega
          subst this
          exact hne'
      split at h
      · rename_i hsaved
        refine ⟨j, i + 1, ?_, hsaved, hextend⟩
        cases age with
        | zero =>
          have : i = j := by omega
          subst this
          exact absurd hsaved (by simp [hne'])
        | succ age => omega
      · split at h
        · exact ih (i + 1) (i + 1) 0 _ (by omega) hextend h
        · exact ih (i + 1) j (age + 1) _ (by omega) hextend h

/-- PROVEN OSCILLATION NEVER SETTLES. For the FIXED deterministic transition, an exact repetition at distance at
    least two, with no successive equal pair before it, leaves no later settling. Nothing is claimed across another
    transition: `step` is one function here, so changed equations or external facts are a different orbit. -/
theorem repetition_never_settles (lawful : LawfulRound step same) (start : σ) {a b : Nat} (hab : a + 2 ≤ b)
    (hrepeat : same (orbit step start a) (orbit step start b) = true)
    (hbefore : ∀ m, m < b → same (orbit step start m) (orbit step start (m + 1)) = false) :
    ∀ m, same (orbit step start m) (orbit step start (m + 1)) = false := by
  have shift : ∀ q, same (orbit step start (a + q)) (orbit step start (b + q)) = true := by
    intro q
    induction q with
    | zero => exact hrepeat
    | succ q ih => exact lawful.congr ih
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    by_cases hm : m < b
    · exact hbefore m hm
    · have hle : b ≤ m := by omega
      have hm1 : m = b + (m - b) := by omega
      have h1 := shift (m - b)
      have h2 := shift (m - b + 1)
      have hlt : a + (m - b) < m := by omega
      have hfalse := ih (a + (m - b)) hlt
      cases hc : same (orbit step start m) (orbit step start (m + 1)) with
      | false => rfl
      | true =>
        exfalso
        have e1 : b + (m - b) = m := by omega
        have e2 : b + (m - b + 1) = m + 1 := by omega
        rw [e1] at h1
        rw [e2] at h2
        have h3 := lawful.trans h1 hc
        have h4 := lawful.trans h3 (lawful.symm h2)
        have e : a + (m - b) + 1 = a + (m - b + 1) := by omega
        rw [e] at hfalse
        rw [hfalse] at h4
        cases h4

/-- The stable state a SETTLED round reaches: one more round stays in its class. -/
theorem settled_is_stable (lawful : LawfulRound step same) {p state : σ} (h1 : state = step p)
    (h2 : same p state = true) : same state (step state) = true := by
  subst h1
  exact lawful.congr h2

end Loop

/-! ## Tabulation and composition congruence -/

private theorem tabulate_get {α} (keys : List Nat) (d : α) (f : Nat → α) (k : Nat) :
    (tabulate keys d f).get k = ((keys.map fun k => (k, f k)).lookup k).getD d := rfl

theorem tabulate_of_mem {α} (keys : List Nat) (d : α) (f : Nat → α) {k : Nat} (h : k ∈ keys) :
    (tabulate keys d f).get k = f k := by
  rw [tabulate_get]
  induction keys with
  | nil => cases h
  | cons x xs ih =>
    simp only [List.map_cons, List.lookup_cons]
    by_cases e : k = x
    · subst e; simp
    · have hk : k ∈ xs := by simpa [e] using h
      have hb : (k == x) = false := by simpa using e
      simp only [hb]
      exact ih hk

theorem tabulate_of_not_mem {α} (keys : List Nat) (d : α) (f : Nat → α) {k : Nat} (h : k ∉ keys) :
    (tabulate keys d f).get k = d := by
  rw [tabulate_get]
  induction keys with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.lookup_cons]
    have e : k ≠ x := fun e => h (by simp [e])
    have hk : k ∉ xs := fun m => h (by simp [m])
    have hb : (k == x) = false := by simpa using e
    simp only [hb]
    exact ih hk

theorem mem_activeTargets {eq : Equation} {opened : Nat → Bool} {t : Nat} :
    t ∈ activeTargets eq opened ↔ ∃ r ∈ eq.references, r.target = .member t ∧ r.active opened = true := by
  unfold activeTargets
  simp only [List.mem_filterMap]
  constructor
  · rintro ⟨r, hr, h⟩
    refine ⟨r, hr, ?_⟩
    cases ht : r.target with
    | member k =>
      rw [ht] at h
      by_cases ha : r.active opened = true
      · simp [ha] at h; simp [h, ha]
      · simp [ha] at h
    | external p => rw [ht] at h; cases h
  · rintro ⟨r, hr, ht, ha⟩
    exact ⟨r, hr, by simp [ht, ha]⟩

/-- Two reads that agree on every active member read, except where both accept zero arguments, lift alike. -/
theorem liftedFrom_congr {opened : Nat → Bool} {look look' : Nat → Patterns} :
    ∀ (refs : List Reference) (seen : List Nat),
    (∀ r ∈ refs, ∀ t, r.target = .member t → r.active opened = true →
      look t = look' t ∨ (acceptsZero (look t) = true ∧ acceptsZero (look' t) = true)) →
    liftedFrom opened look refs seen = liftedFrom opened look' refs seen := by
  intro refs
  induction refs with
  | nil => intro seen _; rfl
  | cons r rest ih =>
    intro seen h
    have hrest : ∀ r ∈ rest, ∀ t, r.target = .member t → r.active opened = true →
        look t = look' t ∨ (acceptsZero (look t) = true ∧ acceptsZero (look' t) = true) :=
      fun x hx => h x (List.mem_cons_of_mem _ hx)
    simp only [liftedFrom]
    by_cases ha : r.active opened = true
    · simp only [ha, if_true]
      have hsame : signatureOf look r.target = signatureOf look' r.target
          ∨ (acceptsZero (signatureOf look r.target) = true ∧ acceptsZero (signatureOf look' r.target) = true) := by
        cases ht : r.target with
        | external p => exact .inl rfl
        | member t => exact h r List.mem_cons_self t ht ha
      rcases hsame with e | ⟨z1, z2⟩
      · rw [e]
        split
        · exact ih _ hrest
        · split
          · exact ih _ hrest
          · rw [ih _ hrest]
      · rw [if_pos z1, if_pos z2]
        exact ih _ hrest
    · simp only [ha, if_false]
      exact ih _ hrest

/-- The composition of an equation reads its signatures only through its active member reads. -/
theorem composeWith_congr {eq : Equation} {opened : Nat → Bool} {look look' : Nat → Patterns}
    (h : ∀ t ∈ activeTargets eq opened,
      look t = look' t ∨ (acceptsZero (look t) = true ∧ acceptsZero (look' t) = true)) :
    composeWith eq opened look = composeWith eq opened look' := by
  unfold composeWith
  rw [liftedFrom_congr eq.references [] (fun r hr t ht ha => h t (mem_activeTargets.2 ⟨r, hr, ht, ha⟩))]

/-! ## The concrete rounds -/

section Rounds

variable (sys : System) (opened : Nat → Bool) (members : List Nat) (lower : Nat → Patterns)

theorem roundStep_of_mem (state : Memo Fact) {k : Nat} (h : k ∈ members) :
    (roundStep sys opened members lower state).get k = nextFact sys opened members lower state.get k :=
  tabulate_of_mem _ _ _ h

theorem sameState_iff {left right : Memo Fact} :
    sameState members left right = true ↔ ∀ k ∈ members, left.get k = right.get k := by
  simp [sameState]

theorem readThrough_congr {left right : Nat → Fact} (h : ∀ k ∈ members, left k = right k) :
    readThrough members lower left = readThrough members lower right := by
  funext t
  unfold readThrough
  by_cases m : t ∈ members
  · simp [m, h t m]
  · simp [m]

/-- The concrete rounds are lawful: their comparison is the full ordered member state, and a round reads no other
    part of the preceding state. -/
theorem roundStep_lawful : LawfulRound (roundStep sys opened members lower) (sameState members) where
  refl a := by simp [sameState]
  symm := by
    intro a b h
    rw [sameState_iff] at h ⊢
    exact fun k m => (h k m).symm
  trans := by
    intro a b c h1 h2
    rw [sameState_iff] at h1 h2 ⊢
    exact fun k m => (h1 k m).trans (h2 k m)
  congr := by
    intro a b h
    rw [sameState_iff] at h ⊢
    intro k m
    rw [roundStep_of_mem _ _ _ _ _ m, roundStep_of_mem _ _ _ _ _ m]
    unfold nextFact
    rw [readThrough_congr members lower h]

/-- A settled component is a fixed point of the composition over its own state. -/
theorem settled_fixed_point {fuel : Nat} {gate state : Memo Fact} {age window : Nat}
    (h : completeLoop (roundStep sys opened members lower) (sameState members) fuel gate gate age window
      = .settled state) {k : Nat} (hk : k ∈ members) :
    state.get k = composeWith (sys.equation k) opened (readThrough members lower state.get) := by
  obtain ⟨n, h1, h2⟩ := completeLoop_settled_spec _ _ _ _ _ _ _ _ h
  have hsame := (sameState_iff members).1 h2
  rw [h1] at hsame ⊢
  rw [roundStep_of_mem _ _ _ _ _ hk]
  unfold nextFact
  rw [readThrough_congr members lower hsame]

/-- PROVEN OSCILLATION, concretely: a `nonSettling` verdict of the rounds of a fixed component under a fixed
    classification and fixed lower facts is an exact repeated member state at distance at least two, and no two
    successive rounds of that orbit ever agree. -/
theorem nonSettling_never_settles {fuel : Nat} {gate : Memo Fact}
    (h : completeLoop (roundStep sys opened members lower) (sameState members) fuel gate gate 0 1 = .nonSettling) :
    ∃ a b, a + 2 ≤ b
      ∧ (∀ k ∈ members, (orbit (roundStep sys opened members lower) gate a).get k
          = (orbit (roundStep sys opened members lower) gate b).get k)
      ∧ ∀ m, sameState members (orbit (roundStep sys opened members lower) gate m)
          (orbit (roundStep sys opened members lower) gate (m + 1)) = false := by
  obtain ⟨a, b, hab, hrep, hbefore⟩ :=
    completeLoop_nonSettling_spec (roundStep sys opened members lower) (sameState members) gate fuel 0 0 0 1
      rfl (fun m hm => absurd hm (Nat.not_lt_zero m)) h
  exact ⟨a, b, hab, (sameState_iff members).1 hrep,
    repetition_never_settles _ _ (roundStep_lawful sys opened members lower) gate hab hrep hbefore⟩

end Rounds

end KatLang.SignatureCompletion
