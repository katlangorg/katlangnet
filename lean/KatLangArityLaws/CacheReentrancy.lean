import Lean
import KatLangArityLaws.PropertyInvocationLaws
import KatLangArityLaws.WhileRoundProduction

open KatLang KatLang.EvaluatorCore KatLang.EvaluatorCacheLaws KatLang.PropertyInvocationLaws

/-!
# FG-K1: an active key cannot be published by its own recursive evaluation

`EvaluatorCacheLaws` proves that entries survive and that completed runs restore the owner set, and
`PropertyInvocationLaws` proves one step of the writer at ANY answer `rec`. Neither says that the
evaluation running below an owner leaves that owner's empty key empty: an arbitrary `rec` could
publish it. This module proves it of the production evaluator.

* **Lawful equality** (§1): `LawfulBEq` of the EXISTING derived comparison of
  `ZeroArgPropertyAccessKind` and `ZeroArgPropertyCacheKey`, over every key field
  (`key_beq_fields`); `insert`/`lookup` laws for arbitrary cache lists, duplicates included
  (`lookup_insert_missing`, `lookup_insert_other`), and `contains` as membership.
* **The whole-evaluator invariant** (§2): `ActiveProtected s t`: every key active at `s` is active
  at `t` with the lookup it had at `s`, absent or present. It composes because it keeps the
  protection available to the next computation. `protected_property_step` is the writer, the one
  body with work to do: an inactive owner's key differs from every protected key because it is not
  active (`contains` to `≠` is where lawful equality is used), and its own mark is exactly what
  protects it during the calculation. `evalStep_preserves` discharges every other `EvalCall`
  constructor. `active_protected` covers every production outcome: a run with no completing fuel
  returns its entry state. `active_protected_core` needs `Completes`, since an incomplete core run
  forgets its state; `incomplete_core_is_unprotected` shows the premise is necessary.
* **The publication contract** (§3): production corollaries with no premise on recursive calls.
  `active_miss_stays_absent`, `reentrant_request_stays_absent`,
  `owner_calculation_keeps_key_absent`, `owner_success_establishes`,
  `owner_failure_leaves_no_entry`, `established_entry_stays`, `established_entry_read_after`.
  Every key is the ONE key computed at the request's entry state; nothing recomputes an owner
  context at the exit.
* **The incomplete boundary** (§4): `owner_incomplete_keeps_mark`. A raw body whose calculation is
  incomplete publishes nothing and does NOT release its mark, so no ordinary-failure cleanup may be
  inferred from it. `fuelExhausted` is the model's incomplete outcome, neither a language failure
  nor C# cancellation.

NOT claimed: key injectivity (lawful equality of `String` fields says nothing of `reprStr`, scope
rendering or AST serialization, so two different bindings rendering alike would share one key);
that a later read computes the same key (a premise of `established_entry_read_after`; the local
case is `OwnerContextStability`); that an active key's entry is absent in an arbitrary state (the
invariant keeps whatever lookup it found, and the corollaries take absence as their premise);
termination; anything about C#.
-/

namespace KatLang.CacheReentrancy

/-! ## 1. Lawful equality of the production key -/

instance : LawfulBEq ZeroArgPropertyAccessKind where
  rfl := by intro a; cases a <;> rfl
  eq_of_beq := by
    intro a b h
    cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

/-- The derived comparison IS the conjunction of all the key's fields, in declaration order. A new
    field breaks this proof by name, not silently. -/
theorem key_beq_fields (a b : ZeroArgPropertyCacheKey) :
    (a == b) =
      (a.accessKind == b.accessKind && (a.owner == b.owner && (a.hostOwners == b.hostOwners &&
        (a.componentOwners == b.componentOwners && (a.propertyName == b.propertyName &&
        (a.propertyAlgorithm == b.propertyAlgorithm && (a.valEnv == b.valEnv &&
        a.bindingContext == b.bindingContext))))))) := by
  cases a; cases b; rfl

instance : LawfulBEq ZeroArgPropertyCacheKey where
  rfl := by intro a; simp [key_beq_fields]
  eq_of_beq := by
    intro a b h
    rw [key_beq_fields] at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈⟩ := h
    cases a; cases b; simp_all

/-- The owner-set test is membership. -/
theorem contains_iff_mem (l : List ZeroArgPropertyCacheKey) (key : ZeroArgPropertyCacheKey) :
    l.contains key = true ↔ key ∈ l := by
  simp

/-- A key that is not in the list differs from every key that is. -/
theorem ne_of_mem_of_not_contains {l : List ZeroArgPropertyCacheKey} {key p : ZeroArgPropertyCacheKey}
    (hnot : l.contains key = false) (hp : p ∈ l) : p ≠ key := by
  rintro rfl
  have := (contains_iff_mem l p).2 hp
  rw [hnot] at this
  cases this

/-- **Publication under a missing key is found**: for an arbitrary cache list, under first-match
    lookup, inserting into a missing key makes lookup return the inserted counted result. -/
theorem lookup_insert_missing (c : ZeroArgPropertyCache) (key : ZeroArgPropertyCacheKey)
    (val : CountedResult) (hmiss : ZeroArgPropertyCache.lookup c key = none) :
    ZeroArgPropertyCache.lookup (ZeroArgPropertyCache.insert c key val) key = some val := by
  induction c with
  | nil => simp [ZeroArgPropertyCache.insert, ZeroArgPropertyCache.lookup]
  | cons e rest ih =>
    obtain ⟨ek, ev⟩ := e
    simp only [ZeroArgPropertyCache.lookup] at hmiss
    split at hmiss
    · cases hmiss
    · rename_i hk
      simp only [ZeroArgPropertyCache.insert, ite_eq_right hk, ZeroArgPropertyCache.lookup]
      exact ih hmiss

/-- **Publication under a distinct key changes no lookup**, absent or present, on an arbitrary cache
    list. -/
theorem lookup_insert_other (c : ZeroArgPropertyCache) (key p : ZeroArgPropertyCacheKey)
    (val : CountedResult) (hne : p ≠ key) :
    ZeroArgPropertyCache.lookup (ZeroArgPropertyCache.insert c key val) p =
      ZeroArgPropertyCache.lookup c p := by
  induction c with
  | nil =>
    have : (key == p) = false := beq_eq_false_iff_ne.2 (Ne.symm hne)
    simp [ZeroArgPropertyCache.insert, ZeroArgPropertyCache.lookup, this]
  | cons e rest ih =>
    obtain ⟨ek, ev⟩ := e
    simp only [ZeroArgPropertyCache.insert]
    split
    · rfl
    · simp only [ZeroArgPropertyCache.lookup, ih]

/-! ## 2. Active keys are protected throughout recursive evaluation -/

/-- Every key active at `s` is still active at `t`, with the lookup it had at `s`: absent stays
    absent and present keeps its value. -/
def ActiveProtected (s t : EvalState) : Prop :=
  ∀ key, key ∈ s.activeZeroArgProperties →
    key ∈ t.activeZeroArgProperties ∧
    ZeroArgPropertyCache.lookup t.zeroArgPropertyCache key =
      ZeroArgPropertyCache.lookup s.zeroArgPropertyCache key

theorem ActiveProtected.refl (s : EvalState) : ActiveProtected s s := fun _ h => ⟨h, rfl⟩

theorem ActiveProtected.trans {s t u : EvalState} (h₁ : ActiveProtected s t)
    (h₂ : ActiveProtected t u) : ActiveProtected s u := fun key hk =>
  let ⟨ht, le⟩ := h₁ key hk
  let ⟨hu, le'⟩ := h₂ key ht
  ⟨hu, le'.trans le⟩

instance : StateRel ActiveProtected := ⟨ActiveProtected.refl, ActiveProtected.trans⟩
instance : FieldFrame ActiveProtected :=
  ⟨fun s t hc ha key hk => ⟨by rw [ha]; exact hk, by rw [hc]⟩⟩

/-- Marking a key protects it and everything already protected. -/
theorem protected_mark (key : ZeroArgPropertyCacheKey) (s : EvalState) :
    ActiveProtected s (markedAt key s) :=
  fun _ hk => ⟨List.mem_cons_of_mem _ hk, rfl⟩

/-- The writer preserves protection at any answer that does, in every branch:
    * not cacheable, an invocation of an established entry, and an active miss are the calculation;
    * a cache hit of a read returns with the state unchanged;
    * an inactive miss marks its key and runs the calculation. An incomplete calculation propagates
      its exit state. A completed one restores the entry owner set, on success after publishing
      under a key that differs from every protected key (`ne_of_mem_of_not_contains`), on ordinary
      failure publishing nothing. -/
theorem protected_property_step (rec : EvalRec) (hrec : ∀ c, Preserves ActiveProtected (rec c))
    (accessKind : ZeroArgPropertyAccessKind) (owner : Algorithm) (binding : PropDef)
    (resolvedAlgorithm : Algorithm) (ctx : EvalCtx) (env : ValEnv) (request : ZeroArgPropertyRequest) :
    Preserves ActiveProtected
      (EvalBody.evalZeroArgPropertyAccessCounted rec accessKind owner binding resolvedAlgorithm ctx env request) := by
  have hcalc := EvalBody.zeroArgPropertyCalculation_pres (R := ActiveProtected) rec hrec request resolvedAlgorithm ctx env
  intro s
  unfold EvalBody.evalZeroArgPropertyAccessCounted
  split
  · simp only [EvalM.bind_runState, get_runState]
    split
    · cases request with
      | read => exact ActiveProtected.refl s
      | invoke _ => exact hcalc s
    · split
      · exact hcalc s
      · rename_i hnot
        simp only [EvalM.bind_runState, set_runState]
        have hnot' := Bool.eq_false_iff.2 hnot
        generalize hkey : zeroArgPropertyCacheKey accessKind owner binding ctx env
          (propertyOwnerBindingContext resolvedAlgorithm.parent s) = key at hnot' ⊢
        obtain ⟨o, t, hm, hc⟩ := evalAttempt_cases
          (EvalBody.zeroArgPropertyCalculation rec request resolvedAlgorithm ctx env) (markedAt key s)
        have hk := (protected_mark key s).trans (by simpa only [hm] using hcalc (markedAt key s))
        rcases hc with ⟨hrun, _⟩ | ⟨hrun, _⟩
        · rw [show (evalAttempt (EvalBody.zeroArgPropertyCalculation rec request resolvedAlgorithm ctx env)).runState
              { s with activeZeroArgProperties := key :: s.activeZeroArgProperties } = _ from hrun]
          exact hk
        · rw [show (evalAttempt (EvalBody.zeroArgPropertyCalculation rec request resolvedAlgorithm ctx env)).runState
              { s with activeZeroArgProperties := key :: s.activeZeroArgProperties } = _ from hrun]
          simp only [get_runState]
          cases o with
          | ok counted =>
            simp only [EvalM.bind_runState, set_runState, pure_runState]
            intro p hp
            refine ⟨hp, ?_⟩
            rw [lookup_insert_other _ _ _ _ (ne_of_mem_of_not_contains hnot' hp)]
            exact (hk p hp).2
          | error err =>
            simp only [EvalM.bind_runState, set_runState, throw_runState]
            exact fun p hp => ⟨hp, (hk p hp).2⟩
  · exact hcalc s

/-- One evaluator step over a preserving answer, for every `EvalCall` constructor. -/
theorem protected_step (rec : EvalRec) (hrec : ∀ c, Preserves ActiveProtected (rec c)) :
    ∀ c, Preserves ActiveProtected (evalStep rec c) :=
  evalStep_preserves protected_property_step rec hrec

/-- **Whole run (core):** every COMPLETED run of the total core, at every fuel, from every state,
    success and ordinary failure alike. An incomplete core run forgets its state
    (`incomplete_core_is_unprotected`). -/
theorem active_protected_core (n : Nat) (c : EvalCall) (s : EvalState)
    (hc : Completes (evalFuel n c) s) : ActiveProtected s ((evalFuel n c).runState s).2 :=
  invariant_transfer ActiveProtected ActiveProtected.refl protected_step n c s hc

/-- **Whole run (production):** every production operation, from every state, on every outcome. A
    run with no completing fuel returns its entry state (`production_preserves`), so the statement
    has no completion premise and says nothing of termination. -/
theorem active_protected (c : EvalCall) : Preserves ActiveProtected (evalUnbounded c) :=
  production_preserves ActiveProtected ActiveProtected.refl protected_step c

/-- The production calculation of a request, through which every recursive call runs, preserves
    protection: the writer's calculation is not an unrestricted callback. -/
theorem production_calculation_protected (request : ZeroArgPropertyRequest) (a : Algorithm)
    (ctx : EvalCtx) (env : ValEnv) :
    Preserves ActiveProtected (EvalBody.zeroArgPropertyCalculation evalUnbounded request a ctx env) :=
  EvalBody.zeroArgPropertyCalculation_pres evalUnbounded active_protected request a ctx env

/-! ## 3. The publication contract of the production evaluator -/

/-- **An active miss stays absent**: any production evaluation entered with `key` active and absent
    leaves it absent, on every outcome, through every nested evaluation, ordinary failure included. -/
theorem active_miss_stays_absent (c : EvalCall) (s : EvalState) (key : ZeroArgPropertyCacheKey)
    (hact : key ∈ s.activeZeroArgProperties)
    (hmiss : ZeroArgPropertyCache.lookup s.zeroArgPropertyCache key = none) :
    ZeroArgPropertyCache.lookup ((evalUnbounded c).runState s).2.zeroArgPropertyCache key = none :=
  ((active_protected c s key hact).2).trans hmiss

/-- The same for every completed core run. -/
theorem active_miss_stays_absent_core (n : Nat) (c : EvalCall) (s : EvalState)
    (key : ZeroArgPropertyCacheKey) (hc : Completes (evalFuel n c) s)
    (hact : key ∈ s.activeZeroArgProperties)
    (hmiss : ZeroArgPropertyCache.lookup s.zeroArgPropertyCache key = none) :
    ZeroArgPropertyCache.lookup ((evalFuel n c).runState s).2.zeroArgPropertyCache key = none :=
  ((active_protected_core n c s hc key hact).2).trans hmiss

section Requests
variable (k : ZeroArgPropertyAccessKind) (owner : Algorithm) (binding : PropDef)
  (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) (s : EvalState) (request : ZeroArgPropertyRequest)

/-- The production request at one call. -/
abbrev requestCall : EvalCall := .evalZeroArgPropertyAccessCounted k owner binding a ctx env request

/-- A completed production request is its body over production. -/
theorem request_unfolds (hc : ProductionCompletes (evalUnbounded (requestCall k owner binding a ctx env request)) s) :
    (EvalBody.evalZeroArgPropertyAccessCounted evalUnbounded k owner binding a ctx env request).runState s =
      (evalUnbounded (requestCall k owner binding a ctx env request)).runState s :=
  production_unfolds _ s hc

/-- **Reentrant requests keep the key absent**: a read or an invocation of an active, absent key
    leaves that key absent. It says nothing of the rest of the state: other keys may publish. -/
theorem reentrant_request_stays_absent
    (hact : s.activeZeroArgProperties.contains (keyAt k owner binding a ctx env s) = true)
    (hmiss : ZeroArgPropertyCache.lookup s.zeroArgPropertyCache (keyAt k owner binding a ctx env s) = none) :
    ZeroArgPropertyCache.lookup
        ((evalUnbounded (requestCall k owner binding a ctx env request)).runState s).2.zeroArgPropertyCache
        (keyAt k owner binding a ctx env s) = none :=
  active_miss_stays_absent _ s _ ((contains_iff_mem _ _).1 hact) hmiss

/-- A completed reentrant request's outcome is its own calculation's, over production. -/
theorem reentrant_request_returns_its_calculation
    (hc : isCacheableZeroArgPropertyAlgorithm a = true)
    (hact : s.activeZeroArgProperties.contains (keyAt k owner binding a ctx env s) = true)
    (hmiss : ZeroArgPropertyCache.lookup s.zeroArgPropertyCache (keyAt k owner binding a ctx env s) = none)
    (hdone : ProductionCompletes (evalUnbounded (requestCall k owner binding a ctx env request)) s) :
    (evalUnbounded (requestCall k owner binding a ctx env request)).runState s =
      (EvalBody.zeroArgPropertyCalculation evalUnbounded request a ctx env).runState s := by
  rw [← request_unfolds k owner binding a ctx env s request hdone]
  exact reentrant_request_is_its_calculation evalUnbounded k owner binding a ctx env s request hc hmiss hact

/-- **The owner's calculation keeps its key absent, and active**: from an absent, inactive key, the
    production calculation run under the owner's mark exits with the key still marked and still
    absent, whatever it did to other keys and on every outcome. -/
theorem owner_calculation_keeps_key_absent
    (hmiss : ZeroArgPropertyCache.lookup s.zeroArgPropertyCache (keyAt k owner binding a ctx env s) = none) :
    let key := keyAt k owner binding a ctx env s
    let t := ((EvalBody.zeroArgPropertyCalculation evalUnbounded request a ctx env).runState (markedAt key s)).2
    key ∈ t.activeZeroArgProperties ∧ ZeroArgPropertyCache.lookup t.zeroArgPropertyCache key = none := by
  intro key t
  have h := production_calculation_protected request a ctx env (markedAt key s) key List.mem_cons_self
  exact ⟨h.1, h.2.trans hmiss⟩

/-- The two completed exits of an owning request, read off the calculation over production. -/
private theorem owner_cases
    (hc : isCacheableZeroArgPropertyAlgorithm a = true)
    (hmiss : ZeroArgPropertyCache.lookup s.zeroArgPropertyCache (keyAt k owner binding a ctx env s) = none)
    (hnot : s.activeZeroArgProperties.contains (keyAt k owner binding a ctx env s) = false)
    (o : Except Error CountedResult) (t : EvalState)
    (hrun : (evalUnbounded (requestCall k owner binding a ctx env request)).runState s = (o, t))
    (hdone : o.isIncomplete = false) :
    ∃ t', (EvalBody.zeroArgPropertyCalculation evalUnbounded request a ctx env).runState
        (markedAt (keyAt k owner binding a ctx env s) s) = (o, t') ∧
      ((∃ counted, o = .ok counted ∧ t = { t' with
          activeZeroArgProperties := s.activeZeroArgProperties,
          zeroArgPropertyCache :=
            ZeroArgPropertyCache.insert t'.zeroArgPropertyCache (keyAt k owner binding a ctx env s) counted }) ∨
       (∃ e, o = .error e ∧ t = { t' with activeZeroArgProperties := s.activeZeroArgProperties })) := by
  have hprod : ProductionCompletes (evalUnbounded (requestCall k owner binding a ctx env request)) s := by
    unfold ProductionCompletes
    rw [hrun]
    intro h
    cases h
    simp [Except.isIncomplete] at hdone
  have hbody := request_unfolds k owner binding a ctx env s request hprod
  rw [hrun] at hbody
  rcases hcalc : (EvalBody.zeroArgPropertyCalculation evalUnbounded request a ctx env).runState
    (markedAt (keyAt k owner binding a ctx env s) s) with ⟨o', t'⟩
  cases o' with
  | ok counted =>
    rw [owner_success_publishes evalUnbounded k owner binding a ctx env s request counted t' hc hmiss hnot hcalc] at hbody
    cases hbody
    exact ⟨t', rfl, .inl ⟨counted, rfl, rfl⟩⟩
  | error e =>
    by_cases hinc : (Except.error e : Except Error CountedResult).isIncomplete = true
    · have he := Except.isIncomplete_eq_true hinc
      cases he
      have hraw := evalAttempt_runState_of_incomplete _ _ t' hcalc
      simp only [EvalBody.evalZeroArgPropertyAccessCounted, hc, ite_true, EvalM.bind_runState, get_runState] at hbody
      rw [hmiss] at hbody
      simp only [hnot, Bool.false_eq_true, ite_false, EvalM.bind_runState, set_runState] at hbody
      rw [show (evalAttempt (EvalBody.zeroArgPropertyCalculation evalUnbounded request a ctx env)).runState _ = _ from hraw] at hbody
      cases hbody
      simp [Except.isIncomplete] at hdone
    · rw [owner_failure_publishes_nothing evalUnbounded k owner binding a ctx env s request e t' hc hmiss hnot
        (Bool.eq_false_iff.2 hinc) hcalc] at hbody
      cases hbody
      exact ⟨t', rfl, .inr ⟨e, rfl, rfl⟩⟩

/-- **A successful owner establishes exactly its own counted result**: a production request on an
    absent, inactive key that succeeds with `counted` got `counted` from the calculation it ran
    under its mark, during which the key stayed absent; after it the owner set is restored and
    lookup of the entry-state key returns that full counted result, not merely an `insert` call.
    An inner success cannot win: it would have needed the key not to stay absent. -/
theorem owner_success_establishes (counted : CountedResult) (t : EvalState)
    (hc : isCacheableZeroArgPropertyAlgorithm a = true)
    (hmiss : ZeroArgPropertyCache.lookup s.zeroArgPropertyCache (keyAt k owner binding a ctx env s) = none)
    (hnot : s.activeZeroArgProperties.contains (keyAt k owner binding a ctx env s) = false)
    (hrun : (evalUnbounded (requestCall k owner binding a ctx env request)).runState s = (.ok counted, t)) :
    ZeroArgPropertyCache.lookup t.zeroArgPropertyCache (keyAt k owner binding a ctx env s) = some counted ∧
    t.activeZeroArgProperties = s.activeZeroArgProperties ∧
    ∃ t', (EvalBody.zeroArgPropertyCalculation evalUnbounded request a ctx env).runState
        (markedAt (keyAt k owner binding a ctx env s) s) = (.ok counted, t') ∧
      ZeroArgPropertyCache.lookup t'.zeroArgPropertyCache (keyAt k owner binding a ctx env s) = none := by
  obtain ⟨t', hcalc, hexit⟩ := owner_cases k owner binding a ctx env s request hc hmiss hnot _ t hrun rfl
  have habsent := (owner_calculation_keeps_key_absent k owner binding a ctx env s request hmiss).2
  simp only [hcalc] at habsent
  rcases hexit with ⟨counted', heq, rfl⟩ | ⟨_, heq, _⟩
  · cases heq
    exact ⟨lookup_insert_missing _ _ _ habsent, rfl, t', hcalc, habsent⟩
  · cases heq

/-- **A failing owner leaves no entry**: a production request on an absent, inactive key that
    completes with an ordinary failure leaves the key absent and restores the owner set. Nothing is
    rolled back: the exit cache is the failed calculation's, so other keys' nested publications
    stay, and every entry the request found survives (`cache_entries_survive`). -/
theorem owner_failure_leaves_no_entry (e : Error) (t : EvalState)
    (hc : isCacheableZeroArgPropertyAlgorithm a = true)
    (hmiss : ZeroArgPropertyCache.lookup s.zeroArgPropertyCache (keyAt k owner binding a ctx env s) = none)
    (hnot : s.activeZeroArgProperties.contains (keyAt k owner binding a ctx env s) = false)
    (hcomplete : (Except.error e : Except Error CountedResult).isIncomplete = false)
    (hrun : (evalUnbounded (requestCall k owner binding a ctx env request)).runState s = (.error e, t)) :
    ZeroArgPropertyCache.lookup t.zeroArgPropertyCache (keyAt k owner binding a ctx env s) = none ∧
    t.activeZeroArgProperties = s.activeZeroArgProperties ∧
    t.zeroArgPropertyCache =
      ((EvalBody.zeroArgPropertyCalculation evalUnbounded request a ctx env).runState
        (markedAt (keyAt k owner binding a ctx env s) s)).2.zeroArgPropertyCache ∧
    CacheKept s t := by
  obtain ⟨t', hcalc, hexit⟩ := owner_cases k owner binding a ctx env s request hc hmiss hnot _ t hrun hcomplete
  have habsent := (owner_calculation_keeps_key_absent k owner binding a ctx env s request hmiss).2
  simp only [hcalc] at habsent ⊢
  have hkept : CacheKept s t := by
    have := cache_entries_survive (requestCall k owner binding a ctx env request) s
    rwa [hrun] at this
  rcases hexit with ⟨_, heq, _⟩ | ⟨_, _, rfl⟩
  · cases heq
  · exact ⟨habsent, rfl, rfl, hkept⟩

/-- **An established entry stays established**: an explicit invocation of it is its own fresh
    calculation when it completes, and on every outcome the entry keeps its value. -/
theorem established_entry_stays (calleeName : String) (v : CountedResult)
    (hc : isCacheableZeroArgPropertyAlgorithm a = true)
    (hhit : ZeroArgPropertyCache.lookup s.zeroArgPropertyCache (keyAt k owner binding a ctx env s) = some v) :
    ZeroArgPropertyCache.lookup
        ((evalUnbounded (requestCall k owner binding a ctx env (.invoke calleeName))).runState s).2.zeroArgPropertyCache
        (keyAt k owner binding a ctx env s) = some v ∧
    (ProductionCompletes (evalUnbounded (requestCall k owner binding a ctx env (.invoke calleeName))) s →
      (evalUnbounded (requestCall k owner binding a ctx env (.invoke calleeName))).runState s =
        (EvalBody.zeroArgPropertyCalculation evalUnbounded (.invoke calleeName) a ctx env).runState s) :=
  ⟨cache_entries_survive _ s _ _ hhit, fun hdone => by
    rw [← request_unfolds k owner binding a ctx env s _ hdone]
    exact invocation_with_entry_is_fresh evalUnbounded k owner binding a ctx env s calleeName v hc hhit⟩

/-- **…and later bare reads reuse it**: after ANY production operation, a read whose computed key
    is the established key returns the entry and changes nothing. That the read computes that key
    is its premise (`hsame`): owner-context stability is `OwnerContextStability`, not this module. -/
theorem established_entry_read_after (c : EvalCall) (key : ZeroArgPropertyCacheKey) (v : CountedResult)
    (hc : isCacheableZeroArgPropertyAlgorithm a = true)
    (hhit : ZeroArgPropertyCache.lookup s.zeroArgPropertyCache key = some v)
    (hsame : keyAt k owner binding a ctx env ((evalUnbounded c).runState s).2 = key) :
    (evalZeroArgPropertyAccessCounted k owner binding a ctx env).runState ((evalUnbounded c).runState s).2 =
      (.ok v, ((evalUnbounded c).runState s).2) := by
  apply WhileRoundProduction.property_cache_hit_production k owner binding a ctx env _ v hc
  rw [show zeroArgPropertyCacheKey k owner binding ctx env
      (propertyOwnerBindingContext a.parent ((evalUnbounded c).runState s).2) = key from hsame]
  exact cache_entries_survive c s key v hhit

/-! ## 4. The incomplete boundary -/

/-- **An incomplete owner keeps its mark and publishes nothing**: a raw body whose calculation is
    incomplete exits with the calculation's own state. Over a protection-preserving answer, the key
    stays absent and STILL MARKED. There is no cleanup to infer: that belongs to completed runs. -/
theorem owner_incomplete_keeps_mark (rec : EvalRec) (hrec : ∀ c, Preserves ActiveProtected (rec c))
    (t : EvalState)
    (hc : isCacheableZeroArgPropertyAlgorithm a = true)
    (hmiss : ZeroArgPropertyCache.lookup s.zeroArgPropertyCache (keyAt k owner binding a ctx env s) = none)
    (hnot : s.activeZeroArgProperties.contains (keyAt k owner binding a ctx env s) = false)
    (hrun : (EvalBody.zeroArgPropertyCalculation rec request a ctx env).runState
      (markedAt (keyAt k owner binding a ctx env s) s) = (.error .fuelExhausted, t)) :
    (EvalBody.evalZeroArgPropertyAccessCounted rec k owner binding a ctx env request).runState s =
      (.error .fuelExhausted, t) ∧
    keyAt k owner binding a ctx env s ∈ t.activeZeroArgProperties ∧
    ZeroArgPropertyCache.lookup t.zeroArgPropertyCache (keyAt k owner binding a ctx env s) = none := by
  have hp := EvalBody.zeroArgPropertyCalculation_pres (R := ActiveProtected) rec hrec request a ctx env
    (markedAt (keyAt k owner binding a ctx env s) s) (keyAt k owner binding a ctx env s) List.mem_cons_self
  rw [hrun] at hp
  refine ⟨?_, hp.1, hp.2.trans hmiss⟩
  simp only [EvalBody.evalZeroArgPropertyAccessCounted, hc, ite_true, EvalM.bind_runState, get_runState]
  rw [hmiss]
  simp only [hnot, Bool.false_eq_true, ite_false, EvalM.bind_runState, set_runState]
  rw [show (evalAttempt (EvalBody.zeroArgPropertyCalculation rec request a ctx env)).runState _ = _ from
    evalAttempt_runState_of_incomplete _ _ t hrun]

end Requests

/-- `Completes` of `active_protected_core` is necessary: an incomplete core run forgets its state,
    so a key that was active is not protected by the exit state. -/
theorem incomplete_core_is_unprotected (c : EvalCall) (s : EvalState)
    (hs : s.activeZeroArgProperties ≠ []) : ¬ ActiveProtected s ((evalFuel 0 c).runState s).2 := by
  intro h
  obtain ⟨key, hk⟩ := List.exists_mem_of_ne_nil _ hs
  exact List.not_mem_nil (h key hk).1

end KatLang.CacheReentrancy
