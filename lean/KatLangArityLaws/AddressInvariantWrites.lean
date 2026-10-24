import KatLangArityLaws.AddressInvariant

open KatLang KatLang.NeedControl.Allocation KatLang.HeapAddressValidity KatLang.AddressInvariant
open KatLang.CallPlan (bind_run get_run pure_run modify_run throw_run lift_run evalAttempt_run
  captured_readonly captured_state modify_get)

/-!
# FG-H1-FU-01 (M2): the write points of `Inv` and the helper contracts

Every production write of an address-bearing location keeps `Inv`, each because the value it
writes is valid in the CURRENT heap (heap growth makes every earlier address valid there too):

| write point | lemma |
| --- | --- |
| `allocateNeed` (every push, every Ready site) | `inv_push`, `allocate_spec`, `ready_spec` |
| `NeedDemand.step` (`.evaluating`, `.completed`) | `inv_modify`, `demandStep_spec` |
| `NeedProjection.step` (`callable` only) | `inv_modify`, `projStep_spec` |
| `NeedPlan.prepare`'s `setSupply` | `inv_modify`, `prepare_spec` |
| `NeedPlan.routeOf`'s `setRoute` | `inv_modify`, `routeOf_spec` |
| `NeedPlan.calleeCell`'s `setCallee` | `inv_modify`, `calleeCell_spec` |
| `NeedLink.receiverCell`'s `setReceiver` | `inv_modify`, `receiverCell_spec` |
| `aliasBareCell` (whole-cell `set!` of a STALE snapshot) | `inv_set`, `aliasBareCell_spec` |
| `takeTerminalAliasInvocation` (whole-cell `set!`) | `inv_set`, `takeTerminal_spec` |
| `aliasBindingCellRecorded` (`aliasCells`) | `aliasBindingCellRecorded_spec` |
| `recordParameterActivation` | `inv_activation`, `record_spec` |
| property-cache publication | `inv_cache_insert`, used by `AddressInvariantBodies` |

`aliasBareCell` writes back the cell it read BEFORE `bindParameters`, `enterAlgorithmBody` and
`supplyNeed`: the snapshot was valid in the earlier heap, hence in the current one, and its new
`aliasBare` is the address `supplyNeed` just returned. FG-M1's in-flight callee overwrite
(`calleeCell` recording `c` after a re-entrant route classification recorded another) keeps `Inv`
for the same reason: `c` is valid now. Neither argument appeals to FG-M1.

The callback-parameterized helpers (supply formation, plan preparation / viewing / execution,
callee and receiver cells, the binder and the family dispatcher, the demand and projection
shells) are proved here once, for EVERY callback satisfying the named callback contract
(`SpreadSpec`, `RouteSpec`, `CapsSpec`, …); `AddressInvariantBodies` discharges those contracts
from the induction hypothesis on the recursive answer.
-/

namespace KatLang.AddressInvariant

/-! ## Invariant preservation at the primitive writes -/

theorem push_size (h : Array NeedCell) (c : NeedCell) : h.size ≤ (h.push c).size := by
  simp [Array.size_push]

/-- Pushing a cell whose suspension is valid in the OLD heap. -/
theorem inv_push {s : EvalState} (vs : Inv s) (susp : NeedSuspension) (hs : SuspV s.needs susp) :
    Inv { s with needs := s.needs.push { suspension := susp } } := by
  have g := push_size s.needs { suspension := susp }
  refine ⟨?_, ?_, fun i act e => ActV.mono g (vs.activations i act e),
    fun p m => CRV.mono g (vs.cache p m), fun p m => Nat.lt_of_lt_of_le (vs.aliasCells p m) g⟩
  · by_cases hc : ∃ slice, susp = .collector slice
    · obtain ⟨slice, rfl⟩ := hc
      simpa only [allocate_run] using append_valid_collector s slice vs.collectors hs
    · intro a cell hcell sub hsub b hb
      simp only [Array.getElem?_push] at hcell
      split at hcell
      · cases hcell
        exact (hc ⟨sub, hsub⟩).elim
      · exact vs.collectors a cell hcell sub hsub b hb
  · intro a cell hcell
    simp only [Array.getElem?_push] at hcell
    split at hcell
    · cases hcell
      exact ⟨SuspV.mono g hs, trivial, trivial, OptAddr.nil, OptAddr.nil, OptAddr.nil⟩
    · exact CellV.mono g (vs.cells a cell hcell)

/-- A same-size cell write at `a` keeping the suspension, whose result is valid in the heap. -/
theorem inv_modify {s : EvalState} (vs : Inv s) (a : Nat) (f : NeedCell → NeedCell)
    (hf : ∀ c, s.needs[a]? = some c → (f c).suspension = c.suspension ∧ CellV s.needs (f c)) :
    Inv { s with needs := s.needs.modify a f } := by
  have hsz : (s.needs.modify a f).size = s.needs.size := Array.size_modify ..
  have g : s.needs.size ≤ (s.needs.modify a f).size := by rw [hsz]; exact Nat.le_refl _
  refine ⟨?_, ?_, fun i act e => ActV.mono g (vs.activations i act e),
    fun p m => CRV.mono g (vs.cache p m), fun p m => Nat.lt_of_lt_of_le (vs.aliasCells p m) g⟩
  · intro b cell hcell sub hsub x hx
    rw [modify_get] at hcell
    split at hcell
    · rename_i hab; subst hab
      cases hc : s.needs[a]? with
      | none => rw [hc] at hcell; cases hcell
      | some c0 =>
        rw [hc] at hcell; cases hcell
        have := (hf c0 hc).1
        rw [this] at hsub
        exact vs.collectors a c0 hc sub hsub x hx
    · exact vs.collectors b cell hcell sub hsub x hx
  · intro b cell hcell
    rw [modify_get] at hcell
    split at hcell
    · rename_i hab; subst hab
      cases hc : s.needs[a]? with
      | none => rw [hc] at hcell; cases hcell
      | some c0 =>
        rw [hc] at hcell; cases hcell
        exact CellV.mono g (hf c0 hc).2
    · exact CellV.mono g (vs.cells b cell hcell)

/-- A whole-cell `set!` at an in-heap address whose new cell is valid in the heap and whose
    collector slice (if any) lies below `a` — the snapshot write of `aliasBareCell` and
    `takeTerminalAliasInvocation`. -/
theorem inv_set {s : EvalState} (vs : Inv s) (a : Nat) (c' : NeedCell)
    (hcol : ∀ slice, c'.suspension = .collector slice → ∀ b ∈ slice, b < a)
    (hv : CellV s.needs c') : Inv { s with needs := s.needs.set! a c' } := by
  have hsz : (s.needs.set! a c').size = s.needs.size := by simp [Array.set!]
  have g : s.needs.size ≤ (s.needs.set! a c').size := by rw [hsz]; exact Nat.le_refl _
  have hget : ∀ b, (s.needs.set! a c')[b]? = if a = b ∧ a < s.needs.size then some c' else s.needs[b]? := by
    intro b
    simp only [Array.set!, Array.setIfInBounds]
    split
    · rename_i ha
      rw [Array.getElem?_set]
      by_cases hab : a = b
      · subst hab; simp [ha]
      · simp [hab]
    · rename_i ha
      by_cases hab : a = b
      · subst hab
        simp [ha, Array.getElem?_eq_none (Nat.le_of_not_lt ha)]
      · simp [hab]
  refine ⟨?_, ?_, fun i act e => ActV.mono g (vs.activations i act e),
    fun p m => CRV.mono g (vs.cache p m), fun p m => Nat.lt_of_lt_of_le (vs.aliasCells p m) g⟩
  · intro b cell hcell sub hsub x hx
    rw [hget] at hcell
    split at hcell
    · rename_i hab; obtain ⟨rfl, _⟩ := hab
      cases hcell
      exact hcol sub hsub x hx
    · exact vs.collectors b cell hcell sub hsub x hx
  · intro b cell hcell
    rw [hget] at hcell
    split at hcell
    · cases hcell; exact CellV.mono g hv
    · exact CellV.mono g (vs.cells b cell hcell)

/-- Saving a valid activation. -/
theorem inv_activation {s : EvalState} (vs : Inv s) (act : ParameterActivation) (ha : ActV s.needs act) :
    Inv { s with lexicalActivations := s.lexicalActivations.push act } := by
  refine ⟨vs.collectors, vs.cells, ?_, vs.cache, vs.aliasCells⟩
  intro i x e
  simp only [Array.getElem?_push] at e
  split at e
  · cases e; exact ha
  · exact vs.activations i x e

/-- A write of fields `Inv` does not read. -/
theorem inv_of_fields {s t : EvalState} (vs : Inv s) (hn : t.needs = s.needs)
    (ha : t.lexicalActivations = s.lexicalActivations) (hc : t.zeroArgPropertyCache = s.zeroArgPropertyCache)
    (hl : t.aliasCells = s.aliasCells) : Inv t := by
  obtain ⟨c1, c2, c3, c4, c5⟩ := vs
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hn]; exact c1
  · rw [hn]; exact c2
  · rw [hn, ha]; exact c3
  · rw [hn, hc]; exact c4
  · rw [hn, hl]; exact c5

/-- Recording an alias binding cell. -/
theorem inv_aliasCell {s : EvalState} (vs : Inv s) (key : String) (a : Nat) (ha : a < s.needs.size) :
    Inv { s with aliasCells := (key, a) :: s.aliasCells } := by
  refine ⟨vs.collectors, vs.cells, vs.activations, vs.cache, ?_⟩
  intro p m
  rcases List.mem_cons.mp m with rfl | m
  · exact ha
  · exact vs.aliasCells p m

/-- The property cache after `insert`: every entry is an old entry or the inserted one. -/
theorem cache_insert_mem (cache : ZeroArgPropertyCache) (key : ZeroArgPropertyCacheKey)
    (v : CountedResult) : ∀ p ∈ ZeroArgPropertyCache.insert cache key v, p ∈ cache ∨ p = (key, v) := by
  induction cache with
  | nil => intro p m; simp [ZeroArgPropertyCache.insert] at m; exact .inr m
  | cons e rest ih =>
    intro p m
    obtain ⟨k, w⟩ := e
    simp only [ZeroArgPropertyCache.insert] at m
    split at m
    · exact .inl m
    · rcases List.mem_cons.mp m with rfl | m
      · exact .inl List.mem_cons_self
      · rcases ih p m with h | h
        · exact .inl (List.mem_cons_of_mem _ h)
        · exact .inr h

/-- Publishing a valid counted result into the property cache. -/
theorem inv_cache_insert {s : EvalState} (vs : Inv s) (key : ZeroArgPropertyCacheKey) (v : CountedResult)
    (hv : CRV s.needs v) :
    Inv { s with zeroArgPropertyCache := ZeroArgPropertyCache.insert s.zeroArgPropertyCache key v } := by
  refine ⟨vs.collectors, vs.cells, vs.activations, ?_, vs.aliasCells⟩
  intro p m
  rcases cache_insert_mem _ key v p m with h | h
  · exact vs.cache p h
  · subst h; exact hv

/-! ## Reading the invariant -/

theorem Inv.cell {s : EvalState} (vs : Inv s) {a : Nat} {c : NeedCell} (hc : s.needs[a]? = some c) :
    CellV s.needs c := vs.cells a c hc

theorem Inv.activation {s : EvalState} (vs : Inv s) {i : Nat} {act : ParameterActivation}
    (e : s.lexicalActivations[i]? = some act) : ActV s.needs act := vs.activations i act e

/-- The `get` contract: the state read satisfies `Inv` and its heap is a prefix-sized heap. -/
def GotV (st : EvalState) (h : Array NeedCell) : Prop := Inv st ∧ st.needs.size ≤ h.size

theorem get_spec {P : Array NeedCell → Prop} :
    SoundI P (get : EvalM EvalState) GotV :=
  fun _ s vs _ => ⟨vs, Nat.le_refl _, fun x hx => by cases hx; exact ⟨vs, Nat.le_refl _⟩⟩

theorem GotV.mono : PMono GotV := fun _ _ _ g v => ⟨v.1, Nat.le_trans v.2 g⟩

theorem GotV.cell {st : EvalState} {h : Array NeedCell} (v : GotV st h) {a : Nat} {c : NeedCell}
    (hc : st.needs[a]? = some c) : CellV h c := CellV.mono v.2 (v.1.cells a c hc)

theorem GotV.activation {st : EvalState} {h : Array NeedCell} (v : GotV st h) {i : Nat}
    {act : ParameterActivation} (e : st.lexicalActivations[i]? = some act) : ActV h act :=
  ActV.mono v.2 (v.1.activations i act e)

theorem GotV.lt {st : EvalState} {h : Array NeedCell} (v : GotV st h) {a : Nat} {c : NeedCell}
    (hc : st.needs[a]? = some c) : a < h.size := Nat.lt_of_lt_of_le (lt_of_getElem? hc) v.2

/-! ## The primitive operations -/

theorem allocate_spec {P : Array NeedCell → Prop} {susp : NeedSuspension}
    (hreq : ∀ h, P h → SuspV h susp) : SoundI P (allocateNeed susp) (fun a h => a < h.size) := by
  intro _ s vs ps
  rw [allocate_run]
  refine ⟨inv_push vs susp (hreq _ ps), push_size _ _, fun a ha => ?_⟩
  cases ha
  simp [Array.size_push]

theorem ready_spec {P : Array NeedCell → Prop} {v : CountedResult}
    (hreq : ∀ h, P h → CRV h v) : SoundI P (readyNeed v) (fun a h => a < h.size) :=
  allocate_spec (susp := .ready v) hreq

/-- `capturedParameterActivation?` reads only; a selected activation is a saved one. -/
theorem captured_spec {P : Array NeedCell → Prop} {name : Ident} {ctx : EvalCtx} :
    SoundI P (capturedParameterActivation? name ctx)
      (fun act? h => OptActV h act?) := by
  refine SoundI.of_readonly (fun s vs _ => ?_)
  obtain ⟨act?, hc, hact⟩ := captured_run name ctx s
  rw [hc]
  refine ⟨rfl, fun x hx act he => ?_⟩
  cases hx
  obtain ⟨i, hi⟩ := hact act he
  exact vs.activations i act hi

theorem tier_valid {h : Array NeedCell} {ctx : EvalCtx} (vc : ValidCtx h ctx)
    {act? : Option ParameterActivation} (hact : OptActV h act?) :
    ValidNeedEnv h (act?.map ParameterActivation.needs |>.getD ctx.needEnv) := by
  cases act? with
  | none => exact vc
  | some act => exact (hact act rfl).1

theorem supply_spec {P : Array NeedCell → Prop} {source : Expr} {caller : EvalCtx} {values : ValEnv}
    (hreq : ∀ h, P h → ValidCtx h caller ∧ VEV h values) :
    SoundI P (supplyNeed source caller values) (fun a h => a < h.size) := by
  intro hp s vs ps
  by_cases hpar : ∃ name, source = .param name
  · obtain ⟨name, rfl⟩ := hpar
    obtain ⟨act?, hc, hact⟩ := captured_run name caller s
    have venv : ValidNeedEnv s.needs (act?.map ParameterActivation.needs |>.getD caller.needEnv) :=
      tier_valid (hreq _ ps).1 (fun act e => by
        obtain ⟨i, hi⟩ := hact act e
        exact vs.activations i act hi)
    cases hl : lookupAssoc name (act?.map ParameterActivation.needs |>.getD caller.needEnv) with
    | some a =>
      rw [supply_param_transports name caller values s act? a hc hl]
      exact ⟨vs, Nat.le_refl _, fun x hx => by cases hx; exact venv.lookup hl⟩
    | none =>
      rw [supply_unbound_param name caller values s act? hc hl, ← allocate_run]
      exact allocate_spec (susp := .expression (.param name) caller values) (fun h ph => hreq h ph) hp s vs ps
  · rw [supply_nonparameter source caller values s (fun n h => hpar ⟨n, h⟩), ← allocate_run]
    exact allocate_spec (susp := .expression source caller values) (fun h ph => hreq h ph) hp s vs ps

theorem record_spec {P : Array NeedCell → Prop} {names : List Ident} {ctx : EvalCtx} {env : ValEnv}
    (hreq : ∀ h, P h → ValidCtx h ctx ∧ VEV h env) :
    SoundI P (recordParameterActivation names ctx env) (fun _ _ => True) := by
  intro _ s vs ps
  rw [recordParameterActivation_run]
  refine ⟨inv_activation vs _ ⟨ValidNeedEnv.filter (hreq _ ps).1 _, VEV.filter (hreq _ ps).2 _⟩,
    Nat.le_refl _, fun _ _ => trivial⟩

theorem bindParameters_spec {P : Array NeedCell → Prop} {names : List Ident} {ctx : EvalCtx}
    (hreq : ∀ h, P h → ValidCtx h ctx) :
    SoundI P (EvalCtx.bindParameters names ctx) (fun c h => ValidCtx h c) := by
  intro _ s vs ps
  refine ⟨inv_of_fields vs rfl rfl rfl rfl, Nat.le_refl _, fun x hx => ?_⟩
  cases hx
  exact ValidNeedEnv.filter (hreq _ ps) _

theorem enterAlgorithmBody_spec {P : Array NeedCell → Prop} {a : Algorithm} {ctx : EvalCtx} {env : ValEnv}
    (hreq : ∀ h, P h → ValidCtx h ctx ∧ VEV h env) :
    SoundI P (enterAlgorithmBody a ctx env) (fun c h => ValidCtx h c) := by
  intro hp
  unfold enterAlgorithmBody
  split
  · exact SoundI.pure _ (fun h ph => (hreq h ph).1) hp
  · refine SoundI.bind (record_spec hreq) (fun _ _ _ _ _ => trivial) ?_ hp
    intro id
    exact SoundI.pure _ (fun h ph => (hreq h ph.1).1)

theorem enterPropertyOwnerBody_spec {P : Array NeedCell → Prop} {a : Algorithm} {ctx : EvalCtx}
    {env : ValEnv} {bc : Nat} (hreq : ∀ h, P h → ValidCtx h ctx ∧ VEV h env) :
    SoundI P (enterPropertyOwnerBody a ctx env bc) (fun c h => ValidCtx h c) := by
  intro hp
  unfold enterPropertyOwnerBody
  refine SoundI.bind (enterAlgorithmBody_spec (ctx := { ctx with bindingContext := bc }) hreq)
    (fun _ _ _ g v => ValidCtx.mono g v) ?_ hp
  intro entered
  exact SoundI.pure _ (fun h ph => ph.2)

theorem needBindingContext_spec {P : Array NeedCell → Prop} {ctx : EvalCtx} {bindings : NeedEnv}
    (hreq : ∀ h, P h → ValidCtx h ctx ∧ ValidNeedEnv h bindings) :
    SoundI P (needBindingContext ctx bindings) (fun c h => ValidCtx h c) := by
  intro hp
  unfold needBindingContext
  refine SoundI.bind (bindParameters_spec (fun h ph => (hreq h ph).1))
    (fun _ _ _ g v => ValidCtx.mono g v) ?_ hp
  intro next
  exact SoundI.pure _ (fun h ph => ValidNeedEnv.append (hreq h ph.1).2 ph.2)

theorem parameterContext_spec {P : Array NeedCell → Prop} {name : Ident} {ctx : EvalCtx} {env : ValEnv}
    (hreq : ∀ h, P h → ValidCtx h ctx ∧ VEV h env) :
    SoundI P (parameterContext name ctx env) (fun r h => ValidCtx h r.1 ∧ VEV h r.2) := by
  intro hp
  unfold parameterContext
  refine SoundI.bind captured_spec (fun _ _ _ g v act e => ActV.mono g (v act e)) ?_ hp
  intro act?
  cases act? with
  | none => exact SoundI.pure _ (fun h ph => hreq h ph.1)
  | some act => exact SoundI.pure _ (fun h ph => ph.2 act rfl)

theorem wireSelectedBranchBody_spec {P : Array NeedCell → Prop} {callee body : Algorithm}
    {names : List Ident} {ctx : EvalCtx} {env : ValEnv} (hreq : ∀ h, P h → ValidCtx h ctx ∧ VEV h env) :
    SoundI P (wireSelectedBranchBody callee body names ctx env) (fun _ _ => True) := by
  intro hp
  unfold wireSelectedBranchBody
  refine SoundI.bind (record_spec hreq) (fun _ _ _ _ _ => trivial) ?_ hp
  intro id
  exact SoundI.pure _ (fun _ _ => trivial)

theorem needActivateBranch_spec {P : Array NeedCell → Prop} {callee : Algorithm} {ctx : EvalCtx}
    {env : ValEnv} {branch : CondBranch} {bindings : NeedEnv}
    (hreq : ∀ h, P h → ValidCtx h ctx ∧ VEV h env ∧ ValidNeedEnv h bindings) :
    SoundI P (needActivateBranch callee ctx env branch bindings)
      (fun r h => ValidCtx h r.2.1 ∧ VEV h r.2.2) := by
  intro hp
  unfold needActivateBranch
  refine SoundI.bind (needBindingContext_spec (ctx := ctx.push callee)
      (fun h ph => ⟨(hreq h ph).1, (hreq h ph).2.2⟩))
    (fun _ _ _ g v => ValidCtx.mono g v) ?_ hp
  intro next
  refine SoundI.bind (wireSelectedBranchBody_spec (fun h ph => ⟨ph.2, VEV.shadow (hreq h ph.1).2.1 _⟩))
    (fun _ _ _ _ _ => trivial) ?_
  intro body
  exact SoundI.pure _ (fun h ph => ⟨ph.1.2, VEV.shadow (hreq h ph.1.1).2.1 _⟩)

theorem identifyRuntimeAlgorithm_spec {P : Array NeedCell → Prop} {a : Algorithm} :
    SoundI P (identifyRuntimeAlgorithm a) (fun _ _ => True) := by
  intro _ s vs _
  exact ⟨inv_of_fields vs rfl rfl rfl rfl, Nat.le_refl _, fun _ _ => trivial⟩

end KatLang.AddressInvariant
