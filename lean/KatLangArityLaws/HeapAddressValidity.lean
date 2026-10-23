import KatLangArityLaws.NeedControl

open KatLang KatLang.NeedControl.Allocation

/-!
# FG-H1: need-heap address validity through allocation and supply formation

`EvaluatorDiscipline` proves that existing cells keep their suspension, completed VALUE and
prepared supply; it says nothing about the references a NEW cell or a returned supply carries.
This module proves, over the actual total production helpers of `KatLang.lean`, that:

* `allocateNeed` / `readyNeed` return a fresh valid address and keep the heap invariant when the
  stored suspension's own references are valid (`allocate_sound`, `ready_sound`);
* a collector allocated over a valid slice references only EARLIER cells
  (`allocate_collector_members_below`, empty and repeated slices included), and the collector
  order forbids self and forward collector edges (`collector_no_self_edge`,
  `collector_no_forward_edge`);
* parameter transport (`supplyNeed`) returns a valid address through BOTH lookup routes — the
  caller's `needEnv` and a captured `ParameterActivation.needs` — and a fresh expression cell
  stores a valid caller environment (`supply_sound`); known-slice reopening
  (`spreadCollectorSlice?`) supplies valid addresses from the collector order alone
  (`collector_slice_sound`);
* the one supply former `NeedSupply.slot` / `form` / `addresses` preserves all of this for every
  output bundle, composing left to right across intervening allocations and callback effects,
  for success AND every failure outcome — the retained heap after an ordinary error included
  (`slot_sound`, `form_sound`, `addresses_sound`, `form_failure_retains_prefix`) — under ONE
  explicit callback contract `SpreadSound` for the computed-spread evaluator;
* the production wrappers `formNeedSupplySourced` / `formNeedSupply` inherit it under exactly
  the named premise `SpreadSound evalSupplySpread ctx env` (`formNeedSupplySourced_runState_valid`,
  `formNeedSupply_runState_valid`), which remains an open evaluator obligation;
* the activation facts actual parameter lookup uses (`recordParameterActivation_sound`,
  `parameterContext_sound`, `bindParameters_sound`, `enterAlgorithmBody_sound`) and the binder's
  collector allocation boundary (`needSourceAddress_sound`, `needLevelSources_valid`);
* the whole Model-C binder returns a valid callee need environment from valid supplied cells
  (`binder_sound`, production `bindNeedPatterns_sound`), its allocation and META adapter
  discharged (`reference_sound`), under exactly the named channel premise `ChannelsSound`
  (VALUE / CALLABLE demand keep the invariant), which remains an open evaluator obligation.

Every address here is a NEED-HEAP address (an index of `EvalState.needs`), never a binding
context, a lexical-activation index, a declaration identity or a source position.

Coverage of the invariant `StateValid` (precisely these fields, nothing else):
* `NeedSuspension.collector slice` stored at `a`: every member is `< a` (the existing
  `ValidCollectorHeap`, reused, not redefined);
* `NeedSuspension.expression _ caller _`: every entry of `caller.needEnv` is `< needs.size`;
* `EvalState.lexicalActivations`: every entry of every `ParameterActivation.needs` is `< needs.size`.

NOT covered (they can hold addresses even in a Ready cell): addresses inside a `Result`
(`callRef`, `argView`, completed VALUE outcomes), the `.ready` payload, prepared plan supplies,
`NeedCell.callee` / `receiver` / `aliasBare`, `EvalState.aliasCells`, the value environment
`ValEnv`, and `EvalCtx.headScope` activation indices. No acyclicity of VALUE/CALLABLE
dependencies is claimed: backward collector edges are one edge kind only. `Error.fuelExhausted`
(the R7 incomplete outcome) is treated like every other outcome by the STATE guarantees (they hold
for every run), and the RESULT guarantees speak only of `.ok`; nothing here claims completion.
-/

namespace KatLang.HeapAddressValidity
open KatLang.NeedControl.Schedule (mapM_schedule schedule formation_step)

/-! ## Address predicates -/

/-- A list of need addresses, every one inside `heap`. -/
def ValidAddresses (heap : Array NeedCell) (xs : List Nat) : Prop := ∀ a ∈ xs, a < heap.size

/-- A sourced supply (`NeedSupply.Sourced`), every address inside `heap` (sources unconstrained). -/
def ValidSourced (heap : Array NeedCell) (xs : List NeedSupply.Sourced) : Prop :=
  ∀ p ∈ xs, p.1 < heap.size

/-- Every entry of a need environment (shadowed entries included) is inside `heap`. -/
def ValidNeedEnv (heap : Array NeedCell) (env : NeedEnv) : Prop := ∀ p ∈ env, p.2 < heap.size

/-- A context's need tier is valid. Only `EvalCtx.needEnv` is constrained. -/
def ValidCtx (heap : Array NeedCell) (ctx : EvalCtx) : Prop := ValidNeedEnv heap ctx.needEnv

/-- Every saved activation's `needs` is valid (`values` / `bindingContext` unconstrained). -/
def ValidActivations (heap : Array NeedCell) (acts : Array ParameterActivation) : Prop :=
  ∀ (i : Nat) (act : ParameterActivation), acts[i]? = some act → ValidNeedEnv heap act.needs

/-- Every stored EXPRESSION suspension's captured caller need tier is valid. -/
def ValidSuspensionEnvs (heap : Array NeedCell) : Prop :=
  ∀ (a : Nat) (cell : NeedCell), heap[a]? = some cell →
    ∀ source caller values, cell.suspension = .expression source caller values → ValidCtx heap caller

/-- The FG-H1 state invariant: exactly the three fields listed in the module header. -/
structure StateValid (s : EvalState) : Prop where
  collectors : ValidCollectorHeap s.needs
  suspensionEnvs : ValidSuspensionEnvs s.needs
  activations : ValidActivations s.needs s.lexicalActivations

/-- The references a suspension about to be STORED carries: an expression's caller tier, a
    collector's members (inside the heap BEFORE the push). A Ready payload is not inspected. -/
def SuspensionValid (heap : Array NeedCell) : NeedSuspension → Prop
  | .expression _ caller _ => ValidCtx heap caller
  | .collector slice => ValidAddresses heap slice
  | .ready _ => True

/-- What a binder source contributes, inside `heap`. -/
def ValidSource (heap : Array NeedCell) : NeedSource Nat → Prop
  | .cell a => a < heap.size
  | .collector slice => ValidAddresses heap slice
  | .missing => True

/-- A computed spread's contribution: transported cell addresses must be valid. Item payloads
    are outside this predicate's coverage (they may contain addresses); `NeedSupply.slot`
    allocates the fresh Ready cell addresses. -/
def SpreadSupplyValid (heap : Array NeedCell) : SpreadSupply → Prop
  | .items _ => True
  | .cells cells => ValidSourced heap cells

theorem empty_valid : StateValid EvalState.empty :=
  ⟨fun _ _ h => by simp [EvalState.empty] at h, fun _ _ h => by simp [EvalState.empty] at h,
   fun _ _ h => by simp [EvalState.empty] at h⟩

/-! ## Growth, lookup, filtering, slicing, concatenation, projection -/

section Mono
variable {h h' : Array NeedCell}

theorem ValidAddresses.mono (g : h.size ≤ h'.size) {xs} (v : ValidAddresses h xs) :
    ValidAddresses h' xs := fun a m => Nat.lt_of_lt_of_le (v a m) g
theorem ValidSourced.mono (g : h.size ≤ h'.size) {xs} (v : ValidSourced h xs) :
    ValidSourced h' xs := fun p m => Nat.lt_of_lt_of_le (v p m) g
theorem ValidNeedEnv.mono (g : h.size ≤ h'.size) {env} (v : ValidNeedEnv h env) :
    ValidNeedEnv h' env := fun p m => Nat.lt_of_lt_of_le (v p m) g
theorem ValidCtx.mono (g : h.size ≤ h'.size) {ctx} (v : ValidCtx h ctx) : ValidCtx h' ctx :=
  ValidNeedEnv.mono g v
theorem ValidActivations.mono (g : h.size ≤ h'.size) {acts} (v : ValidActivations h acts) :
    ValidActivations h' acts := fun i act m => ValidNeedEnv.mono g (v i act m)
theorem SpreadSupplyValid.mono (g : h.size ≤ h'.size) {x} (v : SpreadSupplyValid h x) :
    SpreadSupplyValid h' x := by
  cases x with
  | items _ => trivial
  | cells _ => exact ValidSourced.mono g v
end Mono

theorem lookup_mem {α : Type} (name : Ident) : ∀ (env : Assoc Ident α) (a : α),
    lookupAssoc name env = some a → ∃ k, (k, a) ∈ env
  | [], _, h => by simp [lookupAssoc] at h
  | (k, v) :: rest, a, h => by
    simp only [lookupAssoc] at h
    split at h
    · cases h; exact ⟨k, List.mem_cons_self⟩
    · obtain ⟨k', m⟩ := lookup_mem name rest a h
      exact ⟨k', List.mem_cons_of_mem _ m⟩

/-- Lookup in a valid environment returns a valid address. -/
theorem ValidNeedEnv.lookup {h : Array NeedCell} {env : NeedEnv} (v : ValidNeedEnv h env)
    {name : Ident} {a : Nat} (hl : lookupAssoc name env = some a) : a < h.size := by
  obtain ⟨k, m⟩ := lookup_mem name env a hl
  exact v (k, a) m

theorem ValidNeedEnv.filter {h : Array NeedCell} {env : NeedEnv} (v : ValidNeedEnv h env)
    (f : Ident × Nat → Bool) : ValidNeedEnv h (env.filter f) :=
  fun p m => v p (List.mem_filter.mp m).1

theorem ValidNeedEnv.append {h : Array NeedCell} {e1 e2 : NeedEnv}
    (v1 : ValidNeedEnv h e1) (v2 : ValidNeedEnv h e2) : ValidNeedEnv h (e1 ++ e2) := by
  intro p m
  rcases List.mem_append.mp m with m | m
  · exact v1 p m
  · exact v2 p m

theorem ValidAddresses.append {h : Array NeedCell} {xs ys : List Nat}
    (v1 : ValidAddresses h xs) (v2 : ValidAddresses h ys) : ValidAddresses h (xs ++ ys) := by
  intro a m
  rcases List.mem_append.mp m with m | m
  · exact v1 a m
  · exact v2 a m

theorem ValidSourced.append {h : Array NeedCell} {xs ys : List NeedSupply.Sourced}
    (v1 : ValidSourced h xs) (v2 : ValidSourced h ys) : ValidSourced h (xs ++ ys) := by
  intro p m
  rcases List.mem_append.mp m with m | m
  · exact v1 p m
  · exact v2 p m

theorem ValidAddresses.take {h : Array NeedCell} {xs : List Nat} (v : ValidAddresses h xs)
    (n : Nat) : ValidAddresses h (xs.take n) := fun a m => v a (List.mem_of_mem_take m)

theorem ValidAddresses.drop {h : Array NeedCell} {xs : List Nat} (v : ValidAddresses h xs)
    (n : Nat) : ValidAddresses h (xs.drop n) := fun a m => v a (List.mem_of_mem_drop m)

/-- Address projection of a sourced supply (`NeedSupply.addresses`, `formNeedSupply`). -/
theorem ValidSourced.addresses {h : Array NeedCell} {xs : List NeedSupply.Sourced}
    (v : ValidSourced h xs) : ValidAddresses h (xs.map Prod.fst) := by
  intro a m
  obtain ⟨p, mp, rfl⟩ := List.mem_map.mp m
  exact v p mp

/-- Re-sourcing a valid address list (the known-slice reopening shape). -/
theorem ValidAddresses.sourced {h : Array NeedCell} {xs : List Nat} (v : ValidAddresses h xs)
    (src : Nat → Option Expr) : ValidSourced h (xs.map (fun a => (a, src a))) := by
  intro p m
  obtain ⟨a, ma, rfl⟩ := List.mem_map.mp m
  exact v a ma

/-! ## Collector order -/

/-- A heap with the collector order has no collector self-edge. -/
theorem collector_no_self_edge {heap : Array NeedCell} (v : ValidCollectorHeap heap)
    {a : Nat} {cell : NeedCell} {slice : List Nat} (hc : heap[a]? = some cell)
    (hs : cell.suspension = .collector slice) : a ∉ slice :=
  fun m => Nat.lt_irrefl a (v a cell hc slice hs a m)

/-- ... nor a forward collector edge: no member is at or after its collector. -/
theorem collector_no_forward_edge {heap : Array NeedCell} (v : ValidCollectorHeap heap)
    {a b : Nat} {cell : NeedCell} {slice : List Nat} (hc : heap[a]? = some cell)
    (hs : cell.suspension = .collector slice) (hb : b ∈ slice) : ¬ a ≤ b :=
  fun le => Nat.lt_irrefl b (Nat.lt_of_lt_of_le (v a cell hc slice hs b hb) le)

/-- Every member of a stored collector is a valid address: `b < a < heap.size`. -/
theorem collector_members_valid {heap : Array NeedCell} (v : ValidCollectorHeap heap)
    {a : Nat} {cell : NeedCell} {slice : List Nat} (hc : heap[a]? = some cell)
    (hs : cell.suspension = .collector slice) : ValidAddresses heap slice := by
  have ha : a < heap.size := by
    rcases Nat.lt_or_ge a heap.size with lt | ge
    · exact lt
    · simp [Array.getElem?_eq_none ge] at hc
  exact fun b hb => Nat.lt_trans (v a cell hc slice hs b hb) ha

/-! ## The run contract -/

/-- `Sound pre m post`: from EVERY state satisfying `StateValid` and `pre` (a heap predicate on
    the run's inputs), the run — whatever its outcome: success, an ordinary error, or the R7
    incomplete outcome — ends in a `StateValid` state whose heap is no smaller (so every
    previously valid address stays valid), and a SUCCESSFUL result satisfies `post` in the FINAL
    heap. The final state is `runState`'s, i.e. the heap retained after a failure too. -/
def Sound {α : Type} (pre : Array NeedCell → Prop) (m : EvalM α)
    (post : α → Array NeedCell → Prop) : Prop :=
  ∀ s, StateValid s → pre s.needs →
    StateValid (m.runState s).2 ∧ s.needs.size ≤ (m.runState s).2.needs.size ∧
      ∀ x, (m.runState s).1 = .ok x → post x (m.runState s).2.needs

/-- A heap predicate preserved by size growth, as used for input and result address bounds. -/
def Mono {β : Type} (p : β → Array NeedCell → Prop) : Prop :=
  ∀ x (h h' : Array NeedCell), h.size ≤ h'.size → p x h → p x h'

theorem Sound.bind {α β : Type} {pre : Array NeedCell → Prop} {m : EvalM α} {f : α → EvalM β}
    {mid : α → Array NeedCell → Prop} {post : β → Array NeedCell → Prop}
    (hpre : Mono (fun (_ : Unit) => pre)) (hm : Sound pre m mid)
    (hf : ∀ a, Sound (fun h => pre h ∧ mid a h) (f a) post) : Sound pre (m >>= f) post := by
  intro s vs ps
  rw [bind_run]
  obtain ⟨vt, gt, rt⟩ := hm s vs ps
  cases hr : m.runState s with
  | mk out t =>
    rw [hr] at vt gt rt
    cases out with
    | error e => exact ⟨vt, gt, fun _ h => by cases h⟩
    | ok a =>
      obtain ⟨vu, gu, ru⟩ := hf a t vt ⟨hpre () _ _ gt ps, rt a rfl⟩
      exact ⟨vu, Nat.le_trans gt gu, ru⟩

theorem Sound.pure {α : Type} {pre : Array NeedCell → Prop} {post : α → Array NeedCell → Prop}
    (x : α) (h : ∀ heap, pre heap → post x heap) : Sound pre (pure x : EvalM α) post :=
  fun s vs ps => ⟨vs, Nat.le_refl _, fun y hy => by cases hy; exact h _ ps⟩

theorem Sound.weaken {α : Type} {pre pre' : Array NeedCell → Prop} {m : EvalM α}
    {post post' : α → Array NeedCell → Prop} (hm : Sound pre m post)
    (hp : ∀ h, pre' h → pre h) (hq : ∀ x h, post x h → post' x h) : Sound pre' m post' :=
  fun s vs ps =>
    let ⟨v, g, r⟩ := hm s vs (hp _ ps)
    ⟨v, g, fun x hx => hq _ _ (r x hx)⟩

/-- A computation that reads the state and never writes it. -/
theorem Sound.of_readonly {α : Type} {pre : Array NeedCell → Prop} {m : EvalM α}
    {post : α → Array NeedCell → Prop}
    (h : ∀ s, StateValid s → pre s.needs → (m.runState s).2 = s ∧
      ∀ x, (m.runState s).1 = .ok x → post x s.needs) : Sound pre m post := by
  intro s vs ps
  obtain ⟨hs, hr⟩ := h s vs ps
  rw [hs]
  exact ⟨vs, Nat.le_refl _, hr⟩

/-- `mapM` composes, each element run from the state the previous one left. -/
theorem Sound.mapM {α β : Type} {pre : Array NeedCell → Prop} {f : α → EvalM β}
    {q : β → Array NeedCell → Prop} (hpre : Mono (fun (_ : Unit) => pre)) (hq : Mono q)
    (xs : List α) (hf : ∀ x ∈ xs, Sound pre (f x) q) :
    Sound pre (xs.mapM f) (fun ys h => ∀ y ∈ ys, q y h) := by
  intro s vs ps
  rw [mapM_schedule]
  induction xs generalizing s with
  | nil => exact ⟨vs, Nat.le_refl _, fun ys h => by cases h; simp⟩
  | cons x rest ih =>
    simp only [schedule]
    obtain ⟨vt, gt, rt⟩ := hf x List.mem_cons_self s vs ps
    cases hr : (f x).runState s with
    | mk out t =>
      rw [hr] at vt gt rt
      cases out with
      | error e => exact ⟨vt, gt, fun _ h => by cases h⟩
      | ok y =>
        dsimp only
        obtain ⟨vu, gu, ru⟩ := ih (fun z m => hf z (List.mem_cons_of_mem _ m)) t vt
          (hpre () _ _ gt ps)
        cases hs : schedule f rest t with
        | mk out2 u =>
          rw [hs] at vu gu ru
          cases out2 with
          | error e => exact ⟨vu, Nat.le_trans gt gu, fun _ h => by cases h⟩
          | ok ys =>
            refine ⟨vu, Nat.le_trans gt gu, fun zs hz => ?_⟩
            cases hz
            intro z mz
            rcases List.mem_cons.mp mz with rfl | mz
            · exact hq _ _ _ gu (rt _ rfl)
            · exact ru ys rfl z mz

/-! ## Allocation -/

/-- Pushing a suspension whose references are valid in the OLD heap keeps `StateValid`. -/
theorem push_valid (s : EvalState) (suspension : NeedSuspension) (vs : StateValid s)
    (hs : SuspensionValid s.needs suspension) :
    StateValid { s with needs := s.needs.push { suspension := suspension } } := by
  have grow : s.needs.size ≤ (s.needs.push { suspension := suspension }).size := by
    simp [Array.size_push]
  refine ⟨?_, ?_, ValidActivations.mono grow vs.activations⟩
  · by_cases hc : ∃ slice, suspension = .collector slice
    · obtain ⟨slice, rfl⟩ := hc
      simpa only [allocate_run] using append_valid_collector s slice vs.collectors hs
    · intro a cell hcell sub hsub b hb
      simp only [Array.getElem?_push] at hcell
      split at hcell
      · cases hcell
        exact (hc ⟨sub, hsub⟩).elim
      · exact vs.collectors a cell hcell sub hsub b hb
  · intro a cell hcell source caller values hsub
    simp only [Array.getElem?_push] at hcell
    split at hcell
    · cases hcell
      cases suspension with
      | expression _ c _ => cases hsub; exact ValidCtx.mono grow hs
      | collector _ => cases hsub
      | ready _ => cases hsub
    · exact ValidCtx.mono grow (vs.suspensionEnvs a cell hcell source caller values hsub)

/-- `allocateNeed` over a valid suspension: the returned address is the previous heap size,
    valid in the new heap, and the invariant holds. -/
theorem allocate_sound (suspension : NeedSuspension) :
    Sound (fun h => SuspensionValid h suspension) (allocateNeed suspension)
      (fun a h => a < h.size) := by
  intro s vs ps
  rw [allocate_run]
  refine ⟨push_valid s suspension vs ps, by simp [Array.size_push], fun a ha => ?_⟩
  cases ha
  simp [Array.size_push]

/-- **Collector allocation order.** A collector allocated over a slice valid in the entry heap
    references only cells strictly before its own address — for the empty slice (vacuous) and
    for repeated members alike, and the resulting heap keeps the collector order. -/
theorem allocate_collector_members_below (slice : List Nat) (s : EvalState)
    (hs : ValidAddresses s.needs slice) :
    (allocateNeed (.collector slice)).runState s =
        (.ok s.needs.size, { s with needs := s.needs.push { suspension := .collector slice } }) ∧
      ∀ b ∈ slice, b < s.needs.size := ⟨allocate_run _ s, hs⟩

/-- `readyNeed` returns a valid fresh address and keeps the invariant. No premise is placed on
    (and nothing is concluded about) addresses inside the stored value. -/
theorem ready_sound (value : CountedResult) :
    Sound (fun _ => True) (readyNeed value) (fun a h => a < h.size) :=
  (allocate_sound (.ready value)).weaken (fun _ _ => trivial) (fun _ _ h => h)

/-! ## Parameter transport: caller and captured need tiers -/

/-- `capturedParameterActivation?` reads the state only, and an activation it selects is one
    SAVED in `lexicalActivations`. (It may select none — an invalid activation identifier is an
    absence here, not a dangling need address.) -/
theorem captured_run (name : Ident) (ctx : EvalCtx) (s : EvalState) :
    ∃ act?, (capturedParameterActivation? name ctx).runState s = (.ok act?, s) ∧
      ∀ act, act? = some act → ∃ i : Nat, s.lexicalActivations[i]? = some act := by
  unfold capturedParameterActivation?
  split
  · split
    · exact ⟨none, rfl, by simp⟩
    · dsimp only
      split
      · exact ⟨none, rfl, by simp⟩
      · rename_i id _
        exact ⟨s.lexicalActivations[id]?, rfl, fun act h => ⟨id, h⟩⟩
  · exact ⟨none, rfl, by simp⟩

/-- The need tier `supplyNeed` / `spreadCollectorSlice?` look a parameter up in — the selected
    captured activation's `needs`, else the caller's `needEnv` — is valid. -/
theorem lookup_tier_valid {s : EvalState} {ctx : EvalCtx} (vs : StateValid s)
    (vc : ValidCtx s.needs ctx) (act? : Option ParameterActivation)
    (hact : ∀ act, act? = some act → ∃ i : Nat, s.lexicalActivations[i]? = some act) :
    ValidNeedEnv s.needs (act?.map ParameterActivation.needs |>.getD ctx.needEnv) := by
  cases act? with
  | none => exact vc
  | some act =>
    obtain ⟨i, hi⟩ := hact act rfl
    exact vs.activations i act hi

/-- **Ordinary supply.** `supplyNeed` returns a valid address: a bound parameter TRANSPORTS its
    cell found through the caller's or the captured tier (no allocation, no state change); any
    other source (an unbound parameter included) allocates one expression cell whose stored
    caller tier is the (valid) caller's. -/
theorem supply_sound (source : Expr) (caller : EvalCtx) (values : ValEnv) :
    Sound (fun h => ValidCtx h caller) (supplyNeed source caller values)
      (fun a h => a < h.size) := by
  intro s vs ps
  by_cases hp : ∃ name, source = .param name
  · obtain ⟨name, rfl⟩ := hp
    obtain ⟨act?, hc, hact⟩ := captured_run name caller s
    have venv := lookup_tier_valid vs ps act? hact
    cases hl : lookupAssoc name (act?.map ParameterActivation.needs |>.getD caller.needEnv) with
    | some a =>
      rw [supply_param_transports name caller values s act? a hc hl]
      exact ⟨vs, Nat.le_refl _, fun x hx => by cases hx; exact venv.lookup hl⟩
    | none =>
      rw [supply_unbound_param name caller values s act? hc hl, ← allocate_run]
      exact allocate_sound (.expression (.param name) caller values) s vs ps
  · rw [supply_nonparameter source caller values s (fun n h => hp ⟨n, h⟩), ← allocate_run]
    exact allocate_sound (.expression source caller values) s vs ps

/-- `spreadCollectorSlice?` never writes the state, and a slice it returns is the slice of a
    collector cell PRESENT in the heap. -/
theorem slice_run (operand : Expr) (caller : EvalCtx) (s : EvalState) :
    ∃ r, (spreadCollectorSlice? operand caller).runState s = (r, s) ∧
      ∀ slice, r = .ok (some slice) →
        ∃ (a : Nat) (cell : NeedCell), s.needs[a]? = some cell ∧ cell.suspension = .collector slice := by
  cases operand
  case param name =>
    obtain ⟨act?, hc, _⟩ := captured_run name caller s
    cases hl : lookupAssoc name (act?.map ParameterActivation.needs |>.getD caller.needEnv) with
    | none =>
      refine ⟨.ok none, ?_, fun _ h => by cases h⟩
      simp only [spreadCollectorSlice?, bind_run, hc, hl]
      rfl
    | some a =>
      cases hcell : s.needs[a]? with
      | none =>
        refine ⟨.error .badArity, ?_, fun _ h => by cases h⟩
        simp only [spreadCollectorSlice?, bind_run, hc, hl, KatLang.NeedControl.Provenance.get_run, hcell]
        rfl
      | some cell =>
        cases hs : cell.suspension with
        | collector slice =>
          refine ⟨.ok (some slice), ?_, fun sl h => ?_⟩
          · simp only [spreadCollectorSlice?, bind_run, hc, hl, KatLang.NeedControl.Provenance.get_run, hcell, hs]
            rfl
          · cases h; exact ⟨a, cell, hcell, hs⟩
        | expression e c v =>
          refine ⟨.ok none, ?_, fun _ h => by cases h⟩
          simp only [spreadCollectorSlice?, bind_run, hc, hl, KatLang.NeedControl.Provenance.get_run, hcell, hs]
          rfl
        | ready v =>
          refine ⟨.ok none, ?_, fun _ h => by cases h⟩
          simp only [spreadCollectorSlice?, bind_run, hc, hl, KatLang.NeedControl.Provenance.get_run, hcell, hs]
          rfl
  all_goals exact ⟨.ok none, rfl, fun _ h => by cases h⟩

/-- **Known-slice validity.** A slice `spreadCollectorSlice?` finds is valid in the current heap
    by the collector order alone: its members are `b < a < heap.size` for the collector's own
    address `a`. No premise on the caller's environment is needed (a dangling candidate fails). -/
theorem collector_slice_sound (operand : Expr) (caller : EvalCtx) :
    Sound (fun _ => True) (spreadCollectorSlice? operand caller)
      (fun r h => ∀ slice, r = some slice → ValidAddresses h slice) := by
  refine Sound.of_readonly (fun s vs _ => ?_)
  obtain ⟨r, hr, hfound⟩ := slice_run operand caller s
  rw [hr]
  refine ⟨rfl, fun x hx slice hslice => ?_⟩
  subst hx hslice
  obtain ⟨a, cell, hc, hs⟩ := hfound slice rfl
  exact collector_members_valid vs.collectors hc hs

/-! ## Supply formation -/

/-- **The computed-spread callback contract** for the `ctx` / `env` one formation uses: from a
    valid state with a valid caller tier, every run of the callback on a spread slot keeps the
    invariant and does not shrink the heap — on success AND on every failure — and a successful
    `.cells` result holds addresses valid in the callback's POST-state. This is a premise about
    the callback's own effects and outputs only, not the formation's conclusion: the ordinary,
    known-slice and Ready-item arms are discharged below from the production definitions. -/
def SpreadSound (spread : NeedSupply.SpreadEval) (ctx : EvalCtx) (env : ValEnv) : Prop :=
  ∀ operand, Sound (fun h => ValidCtx h ctx) (spread (.sequenceSpread operand) ctx env)
    (fun x h => SpreadSupplyValid h x)

private theorem ctx_mono (ctx : EvalCtx) : Mono (fun (_ : Unit) h => ValidCtx h ctx) :=
  fun _ _ _ g v => ValidCtx.mono g v

/-- One Ready item of a computed `.items` spread (the `slot` arm, verbatim). -/
private theorem ready_item_sound (v : Result) :
    Sound (fun _ => True)
      (do pure (← readyNeed (v, Result.valueCount v), (none : Option Expr)) : EvalM NeedSupply.Sourced)
      (fun p h => p.1 < h.size) := by
  refine Sound.bind (mid := fun a h => a < h.size) (fun _ _ _ _ _ => trivial) (ready_sound _) ?_
  intro a
  exact Sound.pure _ (fun _ h => h.2)

/-- **One slot.** Every production branch of `NeedSupply.slot` returns a valid sourced list in
    its final heap and keeps the invariant: ordinary expression (one cell, `supply_sound`),
    bound parameter (transport), known collector spread (the original slice, unchanged, in order,
    no allocation or demand — `known_slot_exact`), computed `.items` (fresh valid Ready cells) and
    computed `.cells` (the callback's post-state-valid cells, transported unchanged). -/
theorem slot_sound (spread : NeedSupply.SpreadEval) (ctx : EvalCtx) (env : ValEnv)
    (hspread : SpreadSound spread ctx env) (e : Expr) :
    Sound (fun h => ValidCtx h ctx) (NeedSupply.slot spread ctx env e)
      (fun xs h => ValidSourced h xs) := by
  cases e
  case sequenceSpread operand =>
    simp only [NeedSupply.slot]
    refine Sound.bind (ctx_mono ctx)
      ((collector_slice_sound operand ctx).weaken (fun _ _ => trivial) (fun _ _ h => h)) ?_
    intro r
    cases r with
    | some slice =>
      refine Sound.of_readonly (fun s _ ps => ?_)
      rw [KatLang.NeedControl.Provenance.reopen_run]
      exact ⟨rfl, fun x hx => by cases hx; exact (ps.2 slice rfl).sourced _⟩
    | none =>
      refine Sound.bind (fun _ _ _ g v => ⟨ValidCtx.mono g v.1, fun _ h => by cases h⟩)
        ((hspread operand).weaken (fun _ h => h.1) (fun _ _ h => h)) ?_
      intro x
      cases x with
      | items values =>
        refine (Sound.mapM (q := fun p h => p.1 < h.size) (fun _ _ _ _ _ => trivial) (fun _ _ _ g v => Nat.lt_of_lt_of_le v g)
          values (fun v _ => ready_item_sound v)).weaken (fun _ _ => trivial) (fun _ _ h p m => h p m)
      | cells cells => exact Sound.pure _ (fun _ h => h.2)
  all_goals
    simp only [NeedSupply.slot]
    refine Sound.bind (mid := fun a h => a < h.size) (ctx_mono ctx) (supply_sound _ ctx env) ?_
    intro a
    exact Sound.pure _ (fun _ h p hp => by simp at hp; subst hp; exact h.2)

/-- **Formation.** `NeedSupply.form` composes the slots left to right: each slot runs from the
    state its predecessors (and their callbacks) left, the caller tier stays valid across those
    effects, and the already formed prefix stays valid while the tail is formed. For every output
    bundle and every outcome. -/
theorem form_sound (spread : NeedSupply.SpreadEval) (ctx : EvalCtx) (env : ValEnv)
    (hspread : SpreadSound spread ctx env) (args : OutputBundle) :
    Sound (fun h => ValidCtx h ctx) (NeedSupply.form spread ctx env args)
      (fun xs h => ValidSourced h xs) := by
  induction args with
  | nil => exact Sound.pure _ (fun _ _ p hp => by simp at hp)
  | cons e rest ih =>
    simp only [NeedSupply.form]
    refine Sound.bind (ctx_mono ctx) (slot_sound spread ctx env hspread e) ?_
    intro head
    refine Sound.bind (fun _ _ _ g v => ⟨ValidCtx.mono g v.1, ValidSourced.mono g v.2⟩)
      (ih.weaken (fun _ h => h.1) (fun _ _ h => h)) ?_
    intro tail
    exact Sound.pure _ (fun _ h => ValidSourced.append h.1.2 h.2)

/-- The address projection (`NeedSupply.addresses`). -/
theorem addresses_sound (spread : NeedSupply.SpreadEval) (ctx : EvalCtx) (env : ValEnv)
    (hspread : SpreadSound spread ctx env) (args : OutputBundle) :
    Sound (fun h => ValidCtx h ctx) (NeedSupply.addresses spread ctx env args)
      (fun xs h => ValidAddresses h xs) := by
  simp only [NeedSupply.addresses]
  refine Sound.bind (ctx_mono ctx) (form_sound spread ctx env hspread args) ?_
  intro xs
  exact Sound.pure _ (fun _ h => h.2.addresses)

/-- The run of `form (leading ++ tail)` when `leading` succeeds and `tail` then fails. -/
theorem form_append_failure (spread : NeedSupply.SpreadEval) (ctx : EvalCtx) (env : ValEnv)
    (leading tail : OutputBundle) (s t u : EvalState) (xs : List NeedSupply.Sourced) (e : Error)
    (hl : (NeedSupply.form spread ctx env leading).runState s = (.ok xs, t))
    (ht : (NeedSupply.form spread ctx env tail).runState t = (.error e, u)) :
    (NeedSupply.form spread ctx env (leading ++ tail)).runState s = (.error e, u) := by
  induction leading generalizing s xs with
  | nil =>
    cases hl
    exact ht
  | cons a rest ih =>
    rw [formation_step] at hl
    rw [List.cons_append, formation_step]
    cases ha : (NeedSupply.slot spread ctx env a).runState s with
    | mk out1 t1 =>
      rw [ha] at hl
      cases out1 with
      | error err => cases hl
      | ok head =>
        dsimp only at hl ⊢
        cases hr : (NeedSupply.form spread ctx env rest).runState t1 with
        | mk out2 t2 =>
          rw [hr] at hl
          cases out2 with
          | error err => cases hl
          | ok tl =>
            cases hl
            rw [ih t1 tl hr]

/-- **Retained heap after an ordinary failure.** When an earlier part of the bundle formed
    `xs` (possibly allocating cells) and a later slot fails, the whole formation fails with that
    error and the RETAINED final heap — no rollback — still satisfies the invariant, has not
    shrunk, and keeps every prefix address valid. -/
theorem form_failure_retains_prefix (spread : NeedSupply.SpreadEval) (ctx : EvalCtx)
    (env : ValEnv) (hspread : SpreadSound spread ctx env) (leading tail : OutputBundle)
    (s t u : EvalState) (xs : List NeedSupply.Sourced) (e : Error)
    (vs : StateValid s) (vc : ValidCtx s.needs ctx)
    (hl : (NeedSupply.form spread ctx env leading).runState s = (.ok xs, t))
    (ht : (NeedSupply.form spread ctx env tail).runState t = (.error e, u)) :
    (NeedSupply.form spread ctx env (leading ++ tail)).runState s = (.error e, u) ∧
      StateValid u ∧ s.needs.size ≤ u.needs.size ∧ ValidSourced u.needs xs := by
  have whole := form_append_failure spread ctx env leading tail s t u xs e hl ht
  obtain ⟨vt, gt, rt⟩ := form_sound spread ctx env hspread leading s vs vc
  rw [hl] at vt gt rt
  obtain ⟨vu, gu, _⟩ := form_sound spread ctx env hspread tail t vt (ValidCtx.mono gt vc)
  rw [ht] at vu gu
  exact ⟨whole, vu, Nat.le_trans gt gu, ValidSourced.mono gu (rt xs rfl)⟩

/-! ## Production wrappers -/

/-- **Production sourced supply**, in `runState` form: from a valid state and caller tier, the
    final state of `formNeedSupplySourced` — after success or any failure — satisfies the
    invariant, keeps every previously valid address valid, and a successful supply is valid in
    it. Remaining premise: `SpreadSound evalSupplySpread ctx env` (the evaluator's computed
    spread keeps the invariant and returns post-state-valid `.cells`), NOT discharged here. -/
theorem formNeedSupplySourced_runState_valid (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv)
    (hspread : SpreadSound evalSupplySpread ctx env) (s : EvalState) (vs : StateValid s)
    (vc : ValidCtx s.needs ctx) {o : Except Error (List NeedSupply.Sourced)} {t : EvalState}
    (hr : (formNeedSupplySourced args ctx env).runState s = (o, t)) :
    StateValid t ∧ (∀ a, a < s.needs.size → a < t.needs.size) ∧
      ∀ xs, o = .ok xs → ValidSourced t.needs xs := by
  obtain ⟨v, g, r⟩ := form_sound evalSupplySpread ctx env hspread args s vs vc
  simp only [formNeedSupplySourced] at hr
  rw [hr] at v g r
  exact ⟨v, fun a ha => Nat.lt_of_lt_of_le ha g, r⟩

/-- **Production address supply** (`formNeedSupply`), same premise. -/
theorem formNeedSupply_runState_valid (args : OutputBundle) (ctx : EvalCtx) (env : ValEnv)
    (hspread : SpreadSound evalSupplySpread ctx env) (s : EvalState) (vs : StateValid s)
    (vc : ValidCtx s.needs ctx) {o : Except Error (List Nat)} {t : EvalState}
    (hr : (formNeedSupply args ctx env).runState s = (o, t)) :
    StateValid t ∧ (∀ a, a < s.needs.size → a < t.needs.size) ∧
      ∀ xs, o = .ok xs → ValidAddresses t.needs xs := by
  have hs : Sound (fun h => ValidCtx h ctx) (formNeedSupply args ctx env)
      (fun xs h => ValidAddresses h xs) := by
    simp only [formNeedSupply, formNeedSupplySourced]
    refine Sound.bind (ctx_mono ctx) (form_sound evalSupplySpread ctx env hspread args) ?_
    intro xs
    exact Sound.pure _ (fun _ h => h.2.addresses)
  obtain ⟨v, g, r⟩ := hs s vs vc
  rw [hr] at v g r
  exact ⟨v, fun a ha => Nat.lt_of_lt_of_le ha g, r⟩

/-! ## Activations and parameter contexts -/

/-- The activation `recordParameterActivation` saves (its definition's record, verbatim). -/
def savedActivation (names : List Ident) (ctx : EvalCtx) (env : ValEnv) : ParameterActivation :=
  { values := env.filter (fun b => names.contains b.fst)
    needs := ctx.needEnv.filter (fun b => names.contains b.fst)
    bindingContext := ctx.bindingContext }

/-- `recordParameterActivation` saves exactly the caller's need tier filtered to the owner's
    parameter names, and returns the previous activation count. -/
theorem recordParameterActivation_run (names : List Ident) (ctx : EvalCtx) (env : ValEnv)
    (s : EvalState) :
    (recordParameterActivation names ctx env).runState s =
      (.ok s.lexicalActivations.size,
        { s with lexicalActivations := s.lexicalActivations.push (savedActivation names ctx env) }) :=
  rfl

/-- Recording from a valid caller tier keeps every saved activation valid. -/
theorem recordParameterActivation_sound (names : List Ident) (ctx : EvalCtx) (env : ValEnv) :
    Sound (fun h => ValidCtx h ctx) (recordParameterActivation names ctx env)
      (fun _ _ => True) := by
  intro s vs ps
  rw [recordParameterActivation_run]
  refine ⟨⟨vs.collectors, vs.suspensionEnvs, ?_⟩, Nat.le_refl _, fun _ _ => trivial⟩
  intro i act hi
  simp only [Array.getElem?_push] at hi
  split at hi
  · cases hi; exact ValidNeedEnv.filter ps _
  · exact vs.activations i act hi

/-- The context a parameter read evaluates in (`parameterContext`) has a valid need tier: the
    caller's, or the selected captured activation's. Read-only. -/
theorem parameterContext_sound (name : Ident) (ctx : EvalCtx) (env : ValEnv) :
    Sound (fun h => ValidCtx h ctx) (parameterContext name ctx env)
      (fun r h => ValidCtx h r.1) := by
  refine Sound.of_readonly (fun s vs ps => ?_)
  obtain ⟨act?, hc, hact⟩ := captured_run name ctx s
  have hrun : (parameterContext name ctx env).runState s =
      (.ok (match act? with
        | none => (ctx, env)
        | some activation => ({ ctx with needEnv := activation.needs }, activation.values)), s) := by
    simp only [parameterContext, bind_run, hc]
    cases act? <;> rfl
  rw [hrun]
  refine ⟨rfl, fun x hx => ?_⟩
  cases hx
  cases act? with
  | none => exact ps
  | some act =>
    obtain ⟨i, hi⟩ := hact act rfl
    exact vs.activations i act hi

/-- A binding boundary (`EvalCtx.bindParameters`) only filters the inherited need tier. -/
theorem bindParameters_sound (names : List Ident) (ctx : EvalCtx) :
    Sound (fun h => ValidCtx h ctx) (EvalCtx.bindParameters names ctx)
      (fun c h => ValidCtx h c) := by
  intro s vs ps
  exact ⟨⟨vs.collectors, vs.suspensionEnvs, vs.activations⟩, Nat.le_refl _,
    fun x hx => by cases hx; exact ValidNeedEnv.filter ps _⟩

/-- Body entry keeps the caller's need tier and records only valid activations. -/
theorem enterAlgorithmBody_sound (a : Algorithm) (ctx : EvalCtx) (env : ValEnv) :
    Sound (fun h => ValidCtx h ctx) (enterAlgorithmBody a ctx env)
      (fun c h => ValidCtx h c) := by
  unfold enterAlgorithmBody
  split
  · exact Sound.pure _ (fun _ h => h)
  · refine Sound.bind (ctx_mono ctx) (recordParameterActivation_sound a.params ctx env) ?_
    intro id
    exact Sound.pure _ (fun _ h => h.1)

/-! ## The binder's collector allocation boundary -/

/-- `needSourceAddress` (= `NeedBinder.sourceAddress allocateNeed`): a transported cell stays the
    valid supplied address; a collecting binding allocates ONE collector over its valid slice
    (members below the new address, `allocate_collector_members_below`); `.missing` fails with
    the state unchanged. -/
theorem needSourceAddress_sound (source : NeedSource Nat) :
    Sound (fun h => ValidSource h source) (needSourceAddress source) (fun a h => a < h.size) := by
  cases source with
  | cell a => exact Sound.pure _ (fun _ h => h)
  | collector slice => exact allocate_sound (.collector slice)
  | missing => exact fun s vs _ => ⟨vs, Nat.le_refl _, fun _ h => by cases h⟩

/-- The production binder instantiates the generic allocation with `allocateNeed`. -/
theorem capabilities_sourceAddress (channels : NeedChannels) (source : NeedSource Nat) :
    NeedBinder.sourceAddress (NeedChannels.capabilities channels).allocate source =
      needSourceAddress source := rfl

theorem needSourceAt_valid {h : Array NeedCell} {cells : List Nat} (v : ValidAddresses h cells)
    (collector? : Option Nat) (extra index : Nat) :
    ValidSource h (needSourceAt collector? extra cells index) := by
  unfold needSourceAt
  split
  · exact (v.drop _).take _
  · split
    · rename_i cell hcell
      exact v cell (List.mem_of_getElem? hcell)
    · trivial

/-- Positional allocation of a level's supply (`needLevelSources`) hands every pattern a source
    whose addresses come from the valid supplied cells (a collector's exact `drop`/`take` slice). -/
theorem needLevelSources_valid {h : Array NeedCell} {cells : List Nat}
    (v : ValidAddresses h cells) (patterns : List NeedPattern) :
    ∀ source ∈ needLevelSources patterns cells, ValidSource h source := by
  intro source m
  unfold needLevelSources at m
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp m
  exact needSourceAt_valid v _ _ _

/-- The binder's per-pattern use (`bindSources`: `sourceAddress … (sources.headD .missing)`). -/
theorem headD_valid {h : Array NeedCell} {sources : List (NeedSource Nat)}
    (v : ∀ source ∈ sources, ValidSource h source) : ValidSource h (sources.headD .missing) := by
  cases sources with
  | nil => trivial
  | cons x _ => exact v x List.mem_cons_self

/-! ## The binder under explicit channel premises

The binder's own effects — collector allocation, one Ready cell per opened structural item, the
META adapter — are discharged concretely below. Its VALUE and CALLABLE channels re-enter the
evaluator, so they enter as the premise `ChannelsSound` (keep the invariant, never shrink the
heap, for every outcome, when asked about a valid address); the production binding channels
satisfying it is NOT proved here. Results of a channel are not inspected for addresses. -/

/-- The production binder's channel premise. -/
structure ChannelsSound (channels : NeedChannels) : Prop where
  value : ∀ a, Sound (fun h => a < h.size) (channels.value a) (fun _ _ => True)
  callable : ∀ a, Sound (fun h => a < h.size) (channels.callable a) (fun _ _ => True)

/-- The four generic capabilities, each keeping the invariant; allocation and META reference
    return valid addresses. -/
structure CapsSound (caps : NeedCapabilities EvalM) : Prop where
  value : ∀ a, Sound (fun h => a < h.size) (caps.value a) (fun _ _ => True)
  callable : ∀ a, Sound (fun h => a < h.size) (caps.callable a) (fun _ _ => True)
  allocate : ∀ suspension, Sound (fun h => SuspensionValid h suspension) (caps.allocate suspension)
    (fun a h => a < h.size)
  reference : ∀ a, Sound (fun _ => True) (caps.reference a) (fun r h => r < h.size)

/-- An optional binding environment, valid when present. -/
def OptEnvValid (r : Option NeedEnv) (h : Array NeedCell) : Prop :=
  ∀ env, r = some env → ValidNeedEnv h env

theorem Sound.throw_ {α : Type} {pre : Array NeedCell → Prop} {post : α → Array NeedCell → Prop}
    (e : Error) : Sound pre (throw e : EvalM α) post :=
  fun _ vs _ => ⟨vs, Nat.le_refl _, fun _ h => by cases h⟩

theorem Sound.throw_bind {α β : Type} {pre : Array NeedCell → Prop}
    {post : β → Array NeedCell → Prop} (e : Error) (f : α → EvalM β) :
    Sound pre ((throw e : EvalM α) >>= f) post := by
  intro s vs _
  rw [bind_run]
  exact ⟨vs, Nat.le_refl _, fun _ h => by cases h⟩

/-- Bind through an effect whose result carries no fact: the continuation keeps `pre`. -/
theorem Sound.bind_t {α β : Type} {pre pm : Array NeedCell → Prop} {m : EvalM α}
    {f : α → EvalM β} {post : β → Array NeedCell → Prop}
    (hpre : Mono (fun (_ : Unit) => pre)) (hm : Sound pm m (fun _ _ => True))
    (himp : ∀ h, pre h → pm h) (hf : ∀ a, Sound pre (f a) post) : Sound pre (m >>= f) post :=
  Sound.bind hpre (hm.weaken himp (fun _ _ h => h)) (fun a => (hf a).weaken (fun _ h => h.1) (fun _ _ h => h))

/-- A rethrowing handler (`tryCatchThe`, as `NeedBinder.captureMeta` uses it) keeps soundness. -/
theorem Sound.tryCatch {α : Type} {pre : Array NeedCell → Prop} {m : EvalM α}
    {handler : Error → EvalM α} {post : α → Array NeedCell → Prop}
    (hpre : Mono (fun (_ : Unit) => pre)) (hm : Sound pre m post)
    (hh : ∀ e, Sound pre (handler e) post) : Sound pre (tryCatchThe Error m handler) post := by
  intro s vs ps
  obtain ⟨vt, gt, rt⟩ := hm s vs ps
  have hrun : (tryCatchThe Error m handler).runState s =
      (match m.runState s with
        | (.error err, next) =>
            if (Except.error err : Except Error Unit).isIncomplete then (.error err, next)
            else (handler err).runState next
        | (.ok a, next) => (.ok a, next)) := rfl
  rw [hrun]
  cases hr : m.runState s with
  | mk out t =>
    rw [hr] at vt gt rt
    cases out with
    | ok a => exact ⟨vt, gt, rt⟩
    | error err =>
      dsimp only
      split
      · exact ⟨vt, gt, fun _ h => by cases h⟩
      · obtain ⟨vu, gu, ru⟩ := hh err t vt (hpre () _ _ gt ps)
        exact ⟨vu, Nat.le_trans gt gu, ru⟩

/-- `NeedPlan.reify` is a pure read. -/
theorem reify_readonly (a : Nat) (s : EvalState) :
    ((NeedPlan.reify a).runState s).2 = s := by
  simp only [NeedPlan.reify, bind_run, KatLang.NeedControl.Provenance.get_run]
  cases NeedPlan.reifyResult s.needs a <;> rfl

/-- **META adapter.** `NeedPlan.reference` reads, then allocates ONE fresh Ready cell: a valid
    address. (Its `callRef` payload is not covered.) -/
theorem reference_sound (a : Nat) :
    Sound (fun _ => True) (NeedPlan.reference a) (fun r h => r < h.size) := by
  unfold NeedPlan.reference
  refine Sound.bind_t (fun _ _ _ _ _ => trivial)
    (Sound.of_readonly (fun s _ _ => ⟨reify_readonly a s, fun _ _ => trivial⟩))
    (fun _ _ => trivial) (fun r => ready_sound _)

theorem capabilities_sound (channels : NeedChannels) (hc : ChannelsSound channels) :
    CapsSound (NeedChannels.capabilities channels) :=
  ⟨hc.value, hc.callable, allocate_sound, reference_sound⟩

private theorem pre_mono (address : Nat) (bound : NeedEnv) :
    Mono (fun (_ : Unit) h => address < h.size ∧ ValidNeedEnv h bound) :=
  fun _ _ _ g v => ⟨Nat.lt_of_lt_of_le v.1 g, ValidNeedEnv.mono g v.2⟩

private theorem none_leaf {pre : Array NeedCell → Prop} :
    Sound pre (pure none : EvalM (Option NeedEnv)) OptEnvValid :=
  Sound.pure _ (fun _ _ _ h => by cases h)

/-- One name occurrence: the binding becomes `bound`, or `bound` without `name` plus
    `(name, address)` — valid from a valid `bound` and `address`; the channels touch only `address`
    and an earlier binding of the same name. -/
theorem bindName_sound (caps : NeedCapabilities EvalM) (hc : CapsSound caps) (name : Ident)
    (address : Nat) (repeated : List Ident) (bound : NeedEnv) (family : Bool) :
    Sound (fun h => address < h.size ∧ ValidNeedEnv h bound)
      (NeedBinder.bindName caps name address repeated bound family) OptEnvValid := by
  have hP := pre_mono address bound
  have leaf : Sound (fun h => address < h.size ∧ ValidNeedEnv h bound)
      (pure (some (bound.filter (fun entry => entry.fst != name) ++ [(name, address)])) :
        EvalM (Option NeedEnv)) OptEnvValid :=
    Sound.pure _ (fun _ hp env he => by
      cases he
      refine ValidNeedEnv.append (hp.2.filter _) ?_
      intro p m
      simp only [List.mem_singleton] at m
      subst m
      exact hp.1)
  have same : Sound (fun h => address < h.size ∧ ValidNeedEnv h bound)
      (pure (some bound) : EvalM (Option NeedEnv)) OptEnvValid :=
    Sound.pure _ (fun _ hp env he => by cases he; exact hp.2)
  unfold NeedBinder.bindName
  dsimp only
  split
  · refine Sound.bind_t hP (hc.value address) (fun _ h => h.1) (fun value => ?_)
    split
    · rename_i previous hprev
      refine Sound.bind_t hP (hc.value previous) (fun _ h => h.2.lookup hprev) (fun before => ?_)
      try dsimp only
      split
      · split
        · exact none_leaf
        · exact Sound.throw_bind _ _
      · refine Sound.bind_t hP (hc.callable previous) (fun _ h => h.2.lookup hprev) (fun first => ?_)
        refine Sound.bind_t hP (hc.callable address) (fun _ h => h.1) (fun second => ?_)
        try dsimp only
        split
        · split
          · split
            · split
              · exact none_leaf
              · exact Sound.throw_bind _ _
            · split
              · exact same
              · exact leaf
          · split
            · exact same
            · exact leaf
        · split
          · exact same
          · exact leaf
    · exact leaf
  · exact leaf

/-- The generic source allocation at sound capabilities. -/
theorem sourceAddress_sound (caps : NeedCapabilities EvalM) (hc : CapsSound caps)
    (source : NeedSource Nat) :
    Sound (fun h => ValidSource h source) (NeedBinder.sourceAddress caps.allocate source)
      (fun a h => a < h.size) := by
  cases source with
  | cell a => exact Sound.pure _ (fun _ h => h)
  | collector slice => exact hc.allocate (.collector slice)
  | missing => exact Sound.throw_ _

private theorem sources_mono (sources : List (NeedSource Nat)) (current : NeedEnv) :
    Mono (fun (_ : Unit) h => (∀ source ∈ sources, ValidSource h source) ∧ ValidNeedEnv h current) := by
  intro _ _ _ g v
  refine ⟨fun source m => ?_, ValidNeedEnv.mono g v.2⟩
  have hs := v.1 source m
  cases source with
  | cell a => exact Nat.lt_of_lt_of_le hs g
  | collector slice => exact ValidAddresses.mono g hs
  | missing => trivial

/-- **The binder.** At sound capabilities every pattern and every pattern level returns, when
    it binds, a need environment whose every entry is a valid address in the FINAL heap, from a
    valid supplied address / valid sources and a valid binding so far; every run (failures and
    non-matches included) keeps the invariant. -/
theorem binder_sound (caps : NeedCapabilities EvalM) (hc : CapsSound caps) (repeated : List Ident)
    (family : Bool) :
    (∀ pattern address bound,
      Sound (fun h => address < h.size ∧ ValidNeedEnv h bound)
        (NeedBinder.bindOne caps pattern address repeated bound family) OptEnvValid) ∧
    (∀ patterns sources current,
      Sound (fun h => (∀ source ∈ sources, ValidSource h source) ∧ ValidNeedEnv h current)
        (NeedBinder.bindSources caps patterns sources repeated current family) OptEnvValid) := by
  have structural : ∀ (pattern : NeedPattern) (ps : List NeedPattern) (address : Nat) (bound : NeedEnv),
      (pattern = .sequence ps ∨ pattern = .list ps ∨ pattern = .unpack ps) →
      (∀ cells, Sound (fun h => (∀ source ∈ needLevelSources ps cells, ValidSource h source) ∧
          ValidNeedEnv h bound)
        (NeedBinder.bindSources caps ps (needLevelSources ps cells) repeated bound family) OptEnvValid) →
      Sound (fun h => address < h.size ∧ ValidNeedEnv h bound)
        (NeedBinder.bindOne caps pattern address repeated bound family) OptEnvValid := by
    intro pattern ps address bound hshape ih
    have hP := pre_mono address bound
    have body : ∀ items : List Result, Sound (fun h => address < h.size ∧ ValidNeedEnv h bound)
        (do
          let cells ← items.mapM (fun item => caps.allocate (.ready (item, Result.valueCount item)))
          NeedBinder.cardinalityGate ps cells.length family
            (NeedBinder.bindSources caps ps (needLevelSources ps cells) repeated bound family))
        OptEnvValid := by
      intro items
      refine Sound.bind (mid := fun cells h => ∀ c ∈ cells, c < h.size) hP
        ((Sound.mapM (q := fun c h => c < h.size) (fun _ _ _ _ _ => trivial)
          (fun _ _ _ g v => Nat.lt_of_lt_of_le v g) items
          (fun item _ => (hc.allocate (.ready (item, Result.valueCount item))).weaken (fun _ _ => True.intro) (fun _ _ h => h))).weaken (fun _ _ => trivial) (fun _ _ h => h)) ?_
      intro cells
      unfold NeedBinder.cardinalityGate
      split
      · split
        · exact none_leaf
        · exact Sound.throw_ _
      · exact (ih cells).weaken
          (fun _ h => ⟨needLevelSources_valid h.2 ps, h.1.2⟩) (fun _ _ h => h)
    rcases hshape with rfl | rfl | rfl
    all_goals
      simp only [NeedBinder.bindOne]
      refine Sound.bind_t hP (hc.value address) (fun _ h => h.1) (fun pair => ?_)
      try dsimp only
      first
        | exact body _
        | (split
           · split
             · exact none_leaf
             · exact Sound.throw_ _
           · exact body _)
  refine NeedBinder.bindOne.mutual_induct
    (motive_1 := fun pattern address bound =>
      Sound (fun h => address < h.size ∧ ValidNeedEnv h bound)
        (NeedBinder.bindOne caps pattern address repeated bound family) OptEnvValid)
    (motive_2 := fun patterns sources current =>
      Sound (fun h => (∀ source ∈ sources, ValidSource h source) ∧ ValidNeedEnv h current)
        (NeedBinder.bindSources caps patterns sources repeated current family) OptEnvValid)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro address bound name collecting
    simp only [NeedBinder.bindOne]
    exact bindName_sound caps hc name address repeated bound family
  · intro address bound name
    simp only [NeedBinder.bindOne]
    refine Sound.bind (mid := fun r h => r < h.size) (pre_mono address bound)
      (Sound.tryCatch (pre_mono address bound)
        ((hc.reference address).weaken (fun _ _ => trivial) (fun _ _ h => h))
        (fun _ => Sound.throw_ _)) ?_
    intro adapter
    exact (bindName_sound caps hc name adapter repeated bound family).weaken
      (fun _ h => ⟨h.2, h.1.2⟩) (fun _ _ h => h)
  · intro address bound literal
    simp only [NeedBinder.bindOne]
    refine Sound.bind_t (pre_mono address bound) (hc.value address) (fun _ h => h.1) (fun pair => ?_)
    exact Sound.pure _ (fun _ hp env he => by
      split at he
      · cases he; exact hp.2
      · cases he)
  · intro address bound ps ih
    exact structural _ ps address bound (Or.inl rfl) ih
  · intro address bound ps ih
    exact structural _ ps address bound (Or.inr (Or.inl rfl)) ih
  · intro address bound ps ih
    exact structural _ ps address bound (Or.inr (Or.inr rfl)) ih
  · intro sources current
    simp only [NeedBinder.bindSources]
    exact Sound.pure _ (fun _ hp env he => by cases he; exact hp.2)
  · intro sources current pattern rest ih1 ih2
    simp only [NeedBinder.bindSources]
    have hP := sources_mono sources current
    refine Sound.bind (mid := fun a h => a < h.size) hP
      ((sourceAddress_sound caps hc _).weaken (fun _ h => headD_valid h.1) (fun _ _ h => h)) ?_
    intro address
    refine Sound.bind (mid := fun r h => OptEnvValid r h) (fun _ _ _ g v => ⟨hP () _ _ g v.1, Nat.lt_of_lt_of_le v.2 g⟩)
      ((ih1 address).weaken (fun _ h => ⟨h.2, h.1.2⟩) (fun _ _ h => h)) ?_
    intro r
    cases r with
    | none => exact none_leaf
    | some next =>
      exact (ih2 next).weaken
        (fun _ h => ⟨fun source m => h.1.1.1 source (List.mem_of_mem_tail m), h.2 next rfl⟩)
        (fun _ _ h => h)

/-- **Production binder.** `bindNeedPatterns` over valid supplied cells returns, when it binds, a
    valid callee need environment, and every run keeps the invariant — under the named premise
    `ChannelsSound channels` only (allocation and META reference are discharged). -/
theorem bindNeedPatterns_sound (channels : NeedChannels) (hc : ChannelsSound channels)
    (patterns : List NeedPattern) (cells : List Nat) (family : Bool) :
    Sound (fun h => ValidAddresses h cells) (bindNeedPatterns channels patterns cells family)
      OptEnvValid := by
  unfold bindNeedPatterns NeedBinder.bindPatterns NeedBinder.bindLevel NeedBinder.cardinalityGate
  split
  · split
    · exact none_leaf
    · exact Sound.throw_ _
  · exact ((binder_sound _ (capabilities_sound channels hc) _ family).2 _ _ _).weaken
      (fun _ h => ⟨needLevelSources_valid h patterns, fun _ m => by cases m⟩) (fun _ _ h => h)

end KatLang.HeapAddressValidity
