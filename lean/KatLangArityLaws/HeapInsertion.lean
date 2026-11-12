import KatLangArityLaws.AddressInvariantProduction

open KatLang KatLang.CallPlan KatLang.EvaluatorCore

/-!
# The heap insertion relation (ledger E-18, step 1, M2 § 6.1)

At the flight of a planned `.Algorithm` invocation (cell `a` `evaluating`, route recorded, callee
unrecorded) the plan side first appends its callee LINK cell and — unless the receiver is a
parameter — the link's retained RECEIVER cell, and records the link in `a`
(`NeedPlan.calleeCell`, `NeedLink.receiverCell`). Ordinary production evaluation of the same
written call does neither. From then on the two heaps differ by exactly that: the plan heap is the
production heap with those one or two cells INSERTED at the comparison state's heap size, every
later address shifted past them, and `a`'s callee record set.

This module defines that relation STRUCTURALLY, as a computable function of the production state:

* `Site` — where the cells go (`base`, the insertion address) and how many (`count`);
  `Site.addr` is the address shift: an address below `base` is kept, one at or above it moves up by
  `count`.
* The shift of every address-bearing component of the evaluator state, by `Site.addr`:
  - `shiftResult` — `callRef` / `argView` payloads, at any depth of sequence and list values;
  - `shiftCtx` / `shiftNeedEnv` / `shiftValEnv` — a captured caller context's need tier and a
    captured value environment;
  - `shiftSuspension` — an expression's caller context and values, a collector's slice, a Ready
    payload;
  - `shiftNeedState` — a completed VALUE (a completed FAILURE is kept: no `Error` carries a need
    address); `shiftPlan` — a prepared supply's cells;
  - `shiftCell` — the above, and the recorded `callee` and `receiver` cells;
  - `shiftActivation` — a recorded parameter activation's need tier and values;
  - the property cache's VALUES and the recorded alias binding cells (`embed`).
* `Insertion` — a site's `base`, the inserted cells with their CURRENT plan-side content, and the
  plan cell whose callee record is the first inserted cell; `embed ι s` is the plan-side state of
  the production-side state `s`.
* `Inserted ι sp so` — the relation: `sp = embed ι so`, the plan cell below the insertion, the
  production heap at least `base` long, and production's own record of the plan cell's callee
  ABSENT. `insertedB` decides it on concrete states (by printed form).

Nothing else differs: the tick counter, the binding-context and runtime-declaration counters, the
active owner set, every route, every invocation role and every CALLABLE outcome are EQUAL on the two
sides (an `Algorithm`, an `Expr`, a `ScopeCtx` and an `Error` carry no need address —
`AddressInvariant`'s domain statement).

## Boundary: text that renders an address

Two components hold TEXT, which a structural shift cannot rename: the property-cache KEY of a
local-only binding without a retained activation renders its value environment
(`zeroArgPropertyCacheKey`: `valEnv := some (reprStr env)`), and that environment can hold a call
reference. `embed` keeps every cache key and every active owner key as it is. So the relation holds
only while no such key renders an address at or above `base`; a run that publishes one is outside
it (its two sides would print two different addresses in the key). No error message renders an
address (`operandDescription` names a value's kind).

## What a state valid at the insertion address looks like

`embed_of_valid`: a production state satisfying the whole-evaluator address invariant
(`AddressInvariant.Inv`, which every production run preserves — `production_sound`) holds no
address at or above its own heap size, so inserting AT its heap size shifts nothing: the embedding
is the state with the cells appended and the callee record set. That is the plan side's state right
after it establishes its link and receiver cells.
-/

namespace KatLang.HeapInsertion

/-! ## The address shift -/

/-- Where cells are inserted (`base`) and how many (`count`). -/
structure Site where
  base : Nat
  count : Nat
  deriving Repr, DecidableEq

/-- The address shift of an insertion: addresses below `base` are kept, addresses at or above it
    move past the inserted cells. -/
def Site.addr (σ : Site) (i : Nat) : Nat := if i < σ.base then i else i + σ.count

theorem Site.addr_lt (σ : Site) {i : Nat} (h : i < σ.base) : σ.addr i = i := by
  simp [Site.addr, h]

theorem Site.addr_ge (σ : Site) {i : Nat} (h : σ.base ≤ i) : σ.addr i = i + σ.count := by
  simp [Site.addr, Nat.not_lt.mpr h]

theorem Site.addr_injective (σ : Site) {i j : Nat} (h : σ.addr i = σ.addr j) : i = j := by
  unfold Site.addr at h
  split at h <;> split at h <;> omega

mutual
  /-- A result with every need address it carries shifted. -/
  def shiftResult (σ : Site) : Result → Result
    | .callRef a => .callRef (σ.addr a)
    | .argView a => .argView (σ.addr a)
    | .sequenceValue rs => .sequenceValue (shiftResults σ rs)
    | .listValue rs => .listValue (shiftResults σ rs)
    | r => r

  def shiftResults (σ : Site) : List Result → List Result
    | [] => []
    | r :: rs => shiftResult σ r :: shiftResults σ rs
end

theorem shiftResults_eq_map (σ : Site) (rs : List Result) : shiftResults σ rs = rs.map (shiftResult σ) := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp [shiftResults, ih]

def shiftCounted (σ : Site) (p : CountedResult) : CountedResult := (shiftResult σ p.1, p.2)

def shiftValEnv (σ : Site) (env : ValEnv) : ValEnv := env.map (fun p => (p.1, shiftResult σ p.2))

def shiftNeedEnv (σ : Site) (env : NeedEnv) : NeedEnv := env.map (fun p => (p.1, σ.addr p.2))

/-- A caller context: its need tier. (The call stack and head scope hold algorithms and scope
    levels, which carry no need address.) -/
def shiftCtx (σ : Site) (c : EvalCtx) : EvalCtx := { c with needEnv := shiftNeedEnv σ c.needEnv }

def shiftSuspension (σ : Site) : NeedSuspension → NeedSuspension
  | .expression e c v => .expression e (shiftCtx σ c) (shiftValEnv σ v)
  | .collector slice => .collector (slice.map σ.addr)
  | .ready v => .ready (shiftCounted σ v)

/-- An outcome with its value shifted; an error carries no need address. -/
def shiftExcept {α : Type} (f : α → α) : Except Error α → Except Error α
  | .ok v => .ok (f v)
  | .error e => .error e

def shiftNeedState (σ : Site) : NeedState → NeedState
  | .completed o => .completed (shiftExcept (shiftCounted σ) o)
  | s => s

def shiftSourced (σ : Site) (cells : List NeedSupply.Sourced) : List NeedSupply.Sourced :=
  cells.map (fun p => (σ.addr p.1, p.2))

def shiftPlan (σ : Site) : NeedPlanSupply → NeedPlanSupply
  | .prepared (.ok cells) => .prepared (.ok (shiftSourced σ cells))
  | p => p

/-- A cell with every address it holds shifted: its suspension, completed VALUE, prepared supply
    and recorded callee and receiver cells. Its CALLABLE outcome, route and invocation role carry
    no need address. -/
def shiftCell (σ : Site) (c : NeedCell) : NeedCell :=
  { c with
    suspension := shiftSuspension σ c.suspension
    state := shiftNeedState σ c.state
    plan := shiftPlan σ c.plan
    callee := c.callee.map σ.addr
    receiver := c.receiver.map σ.addr }

def shiftActivation (σ : Site) (act : ParameterActivation) : ParameterActivation :=
  { act with values := shiftValEnv σ act.values, needs := shiftNeedEnv σ act.needs }

/-! ## The insertion -/

/-- An insertion: the address the cells go to, the inserted cells with their CURRENT plan-side
    content (taken as they are: their own addresses are plan-side addresses), and the plan cell
    whose callee record is the first inserted cell. -/
structure Insertion where
  base : Nat
  cells : List NeedCell
  plan : Nat
  deriving Repr

def Insertion.site (ι : Insertion) : Site := ⟨ι.base, ι.cells.length⟩

/-- The plan-side heap of a production-side heap: every cell shifted, the plan cell's callee record
    set to the first inserted cell, and the inserted cells at `base`. -/
def embedNeeds (ι : Insertion) (h : Array NeedCell) : Array NeedCell :=
  let renamed := (h.toList.map (shiftCell ι.site)).modify ι.plan (fun c => { c with callee := some ι.base })
  (renamed.take ι.base ++ ι.cells ++ renamed.drop ι.base).toArray

/-- **The plan-side state of a production-side state**: the heap with the cells inserted
    (`embedNeeds`), and every other address-bearing component shifted — the property cache's values,
    the recorded parameter activations and the recorded alias binding cells. Cache keys, the active
    owner set and the three counters are kept. -/
def embed (ι : Insertion) (s : EvalState) : EvalState :=
  { s with
    needs := embedNeeds ι s.needs
    zeroArgPropertyCache := s.zeroArgPropertyCache.map (fun p => (p.1, shiftCounted ι.site p.2))
    lexicalActivations := s.lexicalActivations.map (shiftActivation ι.site)
    aliasCells := s.aliasCells.map (fun p => (p.1, ι.site.addr p.2)) }

/-- What the relation asks of the production side: the plan cell lies below the insertion, the heap
    reaches the insertion address, and production holds NO callee record for the plan cell — the
    record is the plan side's alone. -/
def Frame (base plan : Nat) (s : EvalState) : Prop :=
  plan < base ∧ base ≤ s.needs.size ∧ (s.needs[plan]?).bind NeedCell.callee = none

instance (base plan : Nat) (s : EvalState) : Decidable (Frame base plan s) := by
  unfold Frame; infer_instance

/-- **THE RELATION.** The plan-side state `sp` is the production-side state `so` with the cells of
    `ι` inserted: structurally, as an equation. -/
def Inserted (ι : Insertion) (sp so : EvalState) : Prop :=
  Frame ι.base ι.plan so ∧ sp = embed ι so

/-- The relation decided on concrete states (states are compared by their printed form). -/
def insertedB (ι : Insertion) (sp so : EvalState) : Bool :=
  decide (Frame ι.base ι.plan so) && reprStr sp == reprStr (embed ι so)

/-! ## A value valid below the insertion address is unshifted -/

open KatLang.AddressInvariant KatLang.HeapAddressValidity

mutual
  theorem shiftResult_fix (σ : Site) : ∀ r : Result, (∀ a, Mentions r a → a < σ.base) → shiftResult σ r = r
    | .callRef a, h => by simp [shiftResult, σ.addr_lt (h a (.callRef a))]
    | .argView a, h => by simp [shiftResult, σ.addr_lt (h a (.argView a))]
    | .sequenceValue rs, h => by
      rw [shiftResult, shiftResults_fix σ rs (fun x hx a m => h a (.seq hx m))]
    | .listValue rs, h => by
      rw [shiftResult, shiftResults_fix σ rs (fun x hx a m => h a (.list hx m))]
    | .atom _, _ => rfl
    | .str _, _ => rfl
    | .bool _, _ => rfl

  theorem shiftResults_fix (σ : Site) :
      ∀ rs : List Result, (∀ x ∈ rs, ∀ a, Mentions x a → a < σ.base) → shiftResults σ rs = rs
    | [], _ => rfl
    | r :: rs, h => by
      rw [shiftResults, shiftResult_fix σ r (h r List.mem_cons_self),
        shiftResults_fix σ rs (fun x hx => h x (List.mem_cons_of_mem _ hx))]
end

section Fix
variable {heap : Array NeedCell} {σ : Site} (hσ : σ.base = heap.size)
include hσ

theorem shiftResult_valid {r : Result} (v : RV heap r) : shiftResult σ r = r :=
  shiftResult_fix σ r (fun a m => hσ ▸ v a m)

theorem shiftCounted_valid {p : CountedResult} (v : CRV heap p) : shiftCounted σ p = p := by
  unfold shiftCounted
  rw [shiftResult_valid hσ v]

theorem shiftValEnv_valid {env : ValEnv} (v : VEV heap env) : shiftValEnv σ env = env := by
  unfold shiftValEnv
  conv => rhs; rw [← List.map_id env]
  apply List.map_congr_left
  intro p hp
  show (p.1, shiftResult σ p.2) = p
  rw [shiftResult_valid hσ (v p hp)]

theorem shiftNeedEnv_valid {env : NeedEnv} (v : ValidNeedEnv heap env) : shiftNeedEnv σ env = env := by
  unfold shiftNeedEnv
  conv => rhs; rw [← List.map_id env]
  apply List.map_congr_left
  intro p hp
  show (p.1, σ.addr p.2) = p
  rw [σ.addr_lt (hσ ▸ v p hp)]

theorem shiftCtx_valid {c : EvalCtx} (v : ValidCtx heap c) : shiftCtx σ c = c := by
  unfold shiftCtx
  rw [shiftNeedEnv_valid hσ v]

theorem shiftAddresses_valid {xs : List Nat} (v : ValidAddresses heap xs) : xs.map σ.addr = xs := by
  conv => rhs; rw [← List.map_id xs]
  apply List.map_congr_left
  intro a ha
  exact σ.addr_lt (hσ ▸ v a ha)

theorem shiftSourced_valid {xs : List NeedSupply.Sourced} (v : ValidSourced heap xs) : shiftSourced σ xs = xs := by
  unfold shiftSourced
  conv => rhs; rw [← List.map_id xs]
  apply List.map_congr_left
  intro p hp
  show (σ.addr p.1, p.2) = p
  rw [σ.addr_lt (hσ ▸ v p hp)]

theorem shiftSuspension_valid {s : NeedSuspension} (v : SuspV heap s) : shiftSuspension σ s = s := by
  cases s with
  | expression e c vals =>
    show NeedSuspension.expression e (shiftCtx σ c) (shiftValEnv σ vals) = _
    rw [shiftCtx_valid hσ v.1, shiftValEnv_valid hσ v.2]
  | collector slice =>
    show NeedSuspension.collector (slice.map σ.addr) = _
    rw [shiftAddresses_valid hσ v]
  | ready value =>
    show NeedSuspension.ready (shiftCounted σ value) = _
    rw [shiftCounted_valid hσ v]

theorem shiftNeedState_valid {s : NeedState} (v : StateV heap s) : shiftNeedState σ s = s := by
  cases s with
  | completed o =>
    cases o with
    | ok r =>
      show NeedState.completed (.ok (shiftCounted σ r)) = _
      rw [shiftCounted_valid hσ v]
    | error _ => rfl
  | suspended => rfl
  | evaluating => rfl

theorem shiftPlan_valid {p : NeedPlanSupply} (v : PlanV heap p) : shiftPlan σ p = p := by
  cases p with
  | prepared o =>
    cases o with
    | ok cells =>
      show NeedPlanSupply.prepared (.ok (shiftSourced σ cells)) = _
      rw [shiftSourced_valid hσ v]
    | error _ => rfl
  | unprepared => rfl
  | preparing => rfl

theorem shiftOptAddr_valid {o : Option Nat} (v : OptAddr heap o) : o.map σ.addr = o := by
  cases o with
  | none => rfl
  | some a => simp [σ.addr_lt (hσ ▸ v a rfl)]

/-- **A valid cell is unshifted**: every address it holds lies below the insertion. -/
theorem shiftCell_valid {c : NeedCell} (v : CellV heap c) : shiftCell σ c = c := by
  unfold shiftCell
  rw [shiftSuspension_valid hσ v.susp, shiftNeedState_valid hσ v.state, shiftPlan_valid hσ v.plan,
    shiftOptAddr_valid hσ v.callee, shiftOptAddr_valid hσ v.receiver]

theorem shiftActivation_valid {act : ParameterActivation} (v : ActV heap act) : shiftActivation σ act = act := by
  unfold shiftActivation
  rw [shiftValEnv_valid hσ v.2, shiftNeedEnv_valid hσ v.1]

end Fix

/-! ## Reading and writing the plan-side heap -/

/-- The plan-side cell of the production-side cell at address `i`. -/
def embedCell (ι : Insertion) (i : Nat) (c : NeedCell) : NeedCell :=
  if ι.plan = i then { shiftCell ι.site c with callee := some ι.base } else shiftCell ι.site c

/-- **Every cell of the plan-side heap**: below the insertion the production cell, shifted (and the
    plan cell with its callee record); then the inserted cells; then the later production cells. -/
theorem embedNeeds_getElem? (ι : Insertion) (h : Array NeedCell) (hb : ι.base ≤ h.size) (i : Nat) :
    (embedNeeds ι h)[i]? =
      if i < ι.base then (h[i]?).map (embedCell ι i)
      else if i < ι.base + ι.cells.length then ι.cells[i - ι.base]?
      else (h[i - ι.cells.length]?).map (embedCell ι (i - ι.cells.length)) := by
  have hlen : ((h.toList.map (shiftCell ι.site)).modify ι.plan (fun c => { c with callee := some ι.base })).length = h.size := by
    simp
  have hget : ∀ j, ((h.toList.map (shiftCell ι.site)).modify ι.plan (fun c => { c with callee := some ι.base }))[j]? =
      (h[j]?).map (embedCell ι j) := by
    intro j
    rw [List.getElem?_modify, List.getElem?_map, Array.getElem?_toList]
    cases h[j]? with
    | none => rfl
    | some c =>
      simp only [Option.map_some, embedCell]
      split <;> rfl
  unfold embedNeeds
  rw [List.getElem?_toArray, List.append_assoc, List.getElem?_append]
  have htake : (List.take ι.base ((h.toList.map (shiftCell ι.site)).modify ι.plan
      (fun c => { c with callee := some ι.base }))).length = ι.base := by
    rw [List.length_take, hlen]; omega
  rw [htake]
  by_cases h1 : i < ι.base
  · rw [ite_eq_left h1, ite_eq_left h1, List.getElem?_take, ite_eq_left h1, hget]
  · rw [ite_eq_right h1, ite_eq_right h1, List.getElem?_append]
    by_cases h2 : i < ι.base + ι.cells.length
    · rw [ite_eq_left (by omega), ite_eq_left h2]
    · rw [ite_eq_right (by omega), ite_eq_right h2, List.getElem?_drop, hget]
      have he : ι.base + (i - ι.base - ι.cells.length) = i - ι.cells.length := by omega
      rw [he]

theorem embedNeeds_size (ι : Insertion) (h : Array NeedCell) (hb : ι.base ≤ h.size) :
    (embedNeeds ι h).size = h.size + ι.cells.length := by
  unfold embedNeeds
  simp only [List.size_toArray, List.length_append, List.length_take, List.length_drop, List.length_modify,
    List.length_map, Array.length_toList]
  omega

/-- A production cell below the insertion, on the plan side. -/
theorem embedNeeds_below (ι : Insertion) (h : Array NeedCell) (hb : ι.base ≤ h.size) (i : Nat)
    (hi : i < ι.base) (c : NeedCell) (hc : h[i]? = some c) :
    (embedNeeds ι h)[i]? = some (embedCell ι i c) := by
  rw [embedNeeds_getElem? ι h hb, ite_eq_left hi, hc]
  rfl

/-- An inserted cell, on the plan side. -/
theorem embedNeeds_inserted (ι : Insertion) (h : Array NeedCell) (hb : ι.base ≤ h.size) (j : Nat)
    (hj : j < ι.cells.length) : (embedNeeds ι h)[ι.base + j]? = ι.cells[j]? := by
  rw [embedNeeds_getElem? ι h hb, ite_eq_right (by omega), ite_eq_left (by omega)]
  congr 1
  omega

/-- **Writing an inserted cell** is the insertion of the written cell: the production-side heap is
    untouched. -/
theorem embedNeeds_modify_inserted (ι : Insertion) (h : Array NeedCell) (hb : ι.base ≤ h.size) (j : Nat)
    (hj : j < ι.cells.length) (f : NeedCell → NeedCell) :
    (embedNeeds ι h).modify (ι.base + j) f = embedNeeds { ι with cells := ι.cells.modify j f } h := by
  have hsite : ({ ι with cells := ι.cells.modify j f } : Insertion).site = ι.site := by
    simp [Insertion.site]
  apply Array.ext_getElem?
  intro i
  rw [Array.getElem?_modify, embedNeeds_getElem? ι h hb,
    embedNeeds_getElem? { ι with cells := ι.cells.modify j f } h hb]
  have hcell : ∀ k, embedCell { ι with cells := ι.cells.modify j f } k = embedCell ι k := by
    intro k
    funext c
    unfold embedCell
    rw [hsite]
  simp only [List.length_modify, hcell]
  by_cases h1 : i < ι.base
  · rw [ite_eq_left h1, ite_eq_left h1, ite_eq_right (by omega)]
  · rw [ite_eq_right h1, ite_eq_right h1]
    by_cases h2 : i < ι.base + ι.cells.length
    · rw [ite_eq_left h2, ite_eq_left h2, List.getElem?_modify]
      by_cases h3 : ι.base + j = i
      · rw [ite_eq_left h3]
        have : j = i - ι.base := by omega
        subst this
        cases ι.cells[i - ι.base]? <;> simp
      · rw [ite_eq_right h3]
        have : ¬ j = i - ι.base := by omega
        cases ι.cells[i - ι.base]? <;> simp [this]
    · rw [ite_eq_right h2, ite_eq_right h2, ite_eq_right (by omega)]

/-- Writing an inserted cell of a plan-side state. -/
theorem embed_modify_inserted (ι : Insertion) (s : EvalState) (hb : ι.base ≤ s.needs.size) (j : Nat)
    (hj : j < ι.cells.length) (f : NeedCell → NeedCell) :
    { embed ι s with needs := (embed ι s).needs.modify (ι.base + j) f } =
      embed { ι with cells := ι.cells.modify j f } s := by
  have hsite : ({ ι with cells := ι.cells.modify j f } : Insertion).site = ι.site := by
    simp [Insertion.site]
  unfold embed
  rw [hsite]
  simp only [embedNeeds_modify_inserted ι s.needs hb j hj f]

/-- **A production cell at its shifted address**, on the plan side — below and above the insertion
    alike. -/
theorem embedNeeds_shifted (ι : Insertion) (h : Array NeedCell) (hb : ι.base ≤ h.size) (i : Nat) :
    (embedNeeds ι h)[ι.site.addr i]? = (h[i]?).map (embedCell ι i) := by
  rw [embedNeeds_getElem? ι h hb]
  by_cases hi : i < ι.base
  · rw [show ι.site.addr i = i from ι.site.addr_lt hi, ite_eq_left hi]
  · have hge : ι.site.base ≤ i := Nat.le_of_not_lt hi
    rw [ι.site.addr_ge hge]
    have hcount : ι.site.count = ι.cells.length := rfl
    rw [hcount, ite_eq_right (by omega), ite_eq_right (by omega)]
    have he : i + ι.cells.length - ι.cells.length = i := by omega
    rw [he]

/-! ## Small facts about shifted values -/

/-- A shifted value is a call reference only as the shift of one. -/
theorem shiftResult_callRef_inv (σ : Site) (v : Result) (p : Nat) (h : shiftResult σ v = .callRef p) :
    ∃ p₀, v = .callRef p₀ ∧ p = σ.addr p₀ := by
  cases v with
  | callRef a =>
    simp only [shiftResult, Result.callRef.injEq] at h
    exact ⟨a, rfl, h.symm⟩
  | argView a => simp [shiftResult] at h
  | sequenceValue rs => simp [shiftResult] at h
  | listValue rs => simp [shiftResult] at h
  | atom n => simp [shiftResult] at h
  | str s => simp [shiftResult] at h
  | bool b => simp [shiftResult] at h

/-- The emitted count of a value does not depend on the addresses it carries. -/
theorem valueCount_shift (σ : Site) (r : Result) : Result.valueCount (shiftResult σ r) = Result.valueCount r := by
  cases r with
  | sequenceValue rs => cases rs <;> simp [shiftResult, shiftResults, Result.valueCount]
  | listValue rs => simp [shiftResult, Result.valueCount]
  | callRef a => simp [shiftResult, Result.valueCount]
  | argView a => simp [shiftResult, Result.valueCount]
  | atom n => rfl
  | str s => rfl
  | bool b => rfl

theorem reCount_shift (σ : Site) (r : CountedResult) :
    reCountValueBoundary (shiftCounted σ r) = shiftCounted σ (reCountValueBoundary r) := by
  unfold reCountValueBoundary shiftCounted
  simp only [valueCount_shift]

/-- A value that carries no need address is unshifted, wherever the insertion is. -/
theorem shiftResult_addressFree (σ : Site) (r : Result) (h : ∀ a, ¬ Mentions r a) : shiftResult σ r = r :=
  shiftResult_fix σ r (fun a m => absurd m (h a))

/-- Whether a suspension is a written invocation does not depend on the addresses it carries. -/
theorem ofSuspension_shift_isSome (σ : Site) (susp : NeedSuspension) :
    (NeedPlan.ofSuspension? (shiftSuspension σ susp)).isSome = (NeedPlan.ofSuspension? susp).isSome := by
  cases susp with
  | expression e c v =>
    show (NeedPlan.callShape? e (shiftCtx σ c) (shiftValEnv σ v)).isSome = (NeedPlan.callShape? e c v).isSome
    unfold NeedPlan.callShape?
    cases e with
    | call f args => cases f <;> first | rfl | (rename_i r n fb argsOpt; cases argsOpt <;> rfl)
    | dotMember r n fb argsOpt => cases argsOpt <;> rfl
    | _ => rfl
  | collector slice => rfl
  | ready value => rfl

/-! ## Inserting at a valid state's heap size appends -/

/-- **A valid state is unshifted at its own heap size.** A production state satisfying the
    whole-evaluator address invariant holds no address at or above its heap size, so the plan-side
    state of an insertion AT its heap size is the state itself with the plan cell's callee record
    set and the cells appended. -/
theorem embed_of_valid (ι : Insertion) (s : EvalState) (v : Inv s) (hb : ι.base = s.needs.size) :
    embed ι s =
      { s with needs := ((s.needs.toList.modify ι.plan (fun c => { c with callee := some ι.base })) ++ ι.cells).toArray } := by
  have hσ : ι.site.base = s.needs.size := hb
  have hcells : s.needs.toList.map (shiftCell ι.site) = s.needs.toList := by
    conv => rhs; rw [← List.map_id s.needs.toList]
    apply List.map_congr_left
    intro c hc
    obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hc
    have hsome : s.needs[i]? = some c := by
      rw [← Array.getElem?_toList, List.getElem?_eq_getElem hi, hget]
    exact shiftCell_valid hσ (v.cells i c hsome)
  have hneeds : embedNeeds ι s.needs =
      ((s.needs.toList.modify ι.plan (fun c => { c with callee := some ι.base })) ++ ι.cells).toArray := by
    unfold embedNeeds
    rw [hcells]
    dsimp only
    have hlen : (s.needs.toList.modify ι.plan (fun c => { c with callee := some ι.base })).length ≤ ι.base := by
      simp [hb]
    rw [List.take_of_length_le hlen, List.drop_of_length_le hlen, List.append_nil]
  have hcache : s.zeroArgPropertyCache.map (fun p => (p.1, shiftCounted ι.site p.2)) = s.zeroArgPropertyCache := by
    conv => rhs; rw [← List.map_id s.zeroArgPropertyCache]
    apply List.map_congr_left
    intro p hp
    show (p.1, shiftCounted ι.site p.2) = p
    rw [shiftCounted_valid hσ (v.cache p hp)]
  have hacts : s.lexicalActivations.map (shiftActivation ι.site) = s.lexicalActivations := by
    apply Array.ext_getElem?
    intro i
    rw [Array.getElem?_map]
    cases hi : s.lexicalActivations[i]? with
    | none => rfl
    | some act =>
      simp only [Option.map_some]
      rw [shiftActivation_valid hσ (v.activations i act hi)]
  have halias : s.aliasCells.map (fun p => (p.1, ι.site.addr p.2)) = s.aliasCells := by
    conv => rhs; rw [← List.map_id s.aliasCells]
    apply List.map_congr_left
    intro p hp
    show (p.1, ι.site.addr p.2) = p
    rw [ι.site.addr_lt (hσ ▸ v.aliasCells p hp)]
  unfold embed
  rw [hneeds, hcache, hacts, halias]

end KatLang.HeapInsertion
