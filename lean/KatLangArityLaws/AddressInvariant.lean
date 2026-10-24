import KatLangArityLaws.HeapAddressValidity
import KatLangArityLaws.EvaluatorMemoLinks

open KatLang KatLang.NeedControl.Allocation KatLang.HeapAddressValidity KatLang.EvaluatorCore

/-!
# FG-H1-FU-01: the whole-evaluator need-address invariant

FG-H1 (`HeapAddressValidity.lean`) proved address validity through allocation, parameter
transport, supply formation and the binder under two callback premises (`SpreadSound`,
`ChannelsSound`) that are FALSE for the compiled evaluator over its invariant `StateValid`:
`StateValid` constrains neither prepared plan supplies nor Ready payloads nor completed VALUE
outcomes, so a `StateValid` heap can make `evalSupplySpread` return a dangling `.cells` address
(`AddressInvariantGuards`, contract counterexamples). This module replaces those premises by a
STRONGER invariant `Inv` that covers every place a need address is stored, and an
invariant-indexed Hoare triple `SoundI`:

* `Mentions r a` / `RV h r`: the need addresses a `Result` carries (`callRef`, `argView`, at any
  depth of `sequenceValue` / `listValue`), all inside the heap; lifted to counted results, lists,
  value environments and every address-bearing auxiliary type of the evaluator.
* `Inv s`: the collector order; for every stored cell its suspension's references (an expression's
  caller need tier and values, a collector's slice, a Ready payload), a completed VALUE, a prepared
  plan supply and the recorded `callee` / `receiver` / `aliasBare` addresses; every saved
  activation's needs and values; every stored property-cache value; every recorded alias cell.
  `Inv.toStateValid`, `empty_inv`.
* `SoundI P m Q`: from every `Inv` state satisfying the (monotone) heap predicate `P`, every
  outcome — success, ordinary error, `fuelExhausted` — ends in an `Inv` state with a heap no
  smaller, and a success satisfies `Q` in the final heap; combinators (`bind`, `pure`, `mapM`,
  `attempt`, `withCtx`, loops) and the write-point lemmas of every production writer.
* `CallPre c` / `CallPost c`: the structural call contract of every `EvalCall`, defined by cases
  from `ValidCtx`, `VEV`, `RV` and the address bounds of the call's arguments and result only.
* `sound_transfer`: a contract every body keeps (given its recursive answer keeps it) holds for
  every completed `evalFuel` run, and (`production_sound`) for every production operation.

Every address here is a NEED-HEAP address. Out of domain (never bounded by the heap size):
`PlanRoute`, the `aliasUse` claim flag, CALLABLE outcomes, every `Algorithm` / `ScopeCtx` / `Expr`
/ `PropDef` / `Error` (none carries a `Result`), `ScopeCtx.activation` (a lexical-activation
index), binding contexts, declaration identities, cache keys and their `reprStr` text,
`Expr.emptySequence` depth and arity counts. No acyclicity, termination or first-writer law is
claimed. The incomplete outcome `Error.fuelExhausted` is treated like every other outcome; the
fuel core's normalized incomplete state is handled only through `Completes` / `completedPart` /
`production_incomplete_state` (`sound_transfer`, `production_sound`).
-/

/-- The validity lemmas of the `ht_tac` leaf solver (`ht_sbe`, a head-indexed backward prover). -/
register_label_attr ht_lemmas

/-- The forward lemmas of the `ht_tac` leaf solver (`ht_fwd`): each derives a fact from facts. -/
register_label_attr ht_fwd

/-- The registered operation contracts of `ht_tac`: `SoundI P (op …) Post` with every requirement
    an explicit premise; indexed by the head of `op`. -/
register_label_attr ht_spec

namespace KatLang.AddressInvariant

/-! ## Addresses inside results -/

/-- `Mentions r a`: the result `r` carries the need address `a` (a call reference or an argument
    view, at any depth of sequence and list values). -/
inductive Mentions : Result → Nat → Prop
  | callRef (a : Nat) : Mentions (.callRef a) a
  | argView (a : Nat) : Mentions (.argView a) a
  | seq {xs : List Result} {x : Result} {a : Nat} : x ∈ xs → Mentions x a → Mentions (.sequenceValue xs) a
  | list {xs : List Result} {x : Result} {a : Nat} : x ∈ xs → Mentions x a → Mentions (.listValue xs) a

/-- Every need address a result carries is inside `h`. -/
def RV (h : Array NeedCell) (r : Result) : Prop := ∀ a, Mentions r a → a < h.size

/-- A counted result: its value (the count is no address). -/
def CRV (h : Array NeedCell) (p : CountedResult) : Prop := RV h p.1

/-- A list of results. -/
def RLV (h : Array NeedCell) (xs : List Result) : Prop := ∀ x ∈ xs, RV h x

/-- A list of counted results. -/
def CRLV (h : Array NeedCell) (xs : List CountedResult) : Prop := ∀ x ∈ xs, CRV h x

/-- A value environment: every bound value (shadowed entries included). -/
def VEV (h : Array NeedCell) (env : ValEnv) : Prop := ∀ p ∈ env, RV h p.2

/-- An optional need address. -/
def OptAddr (h : Array NeedCell) (o : Option Nat) : Prop := ∀ a, o = some a → a < h.size

/-- A resolved builtin argument: its supplied cell. -/
def RAV (h : Array NeedCell) (arg : ResolvedArgumentAlgorithm) : Prop := OptAddr h arg.need?

def RALV (h : Array NeedCell) (args : List ResolvedArgumentAlgorithm) : Prop := ∀ x ∈ args, RAV h x

/-- A callee origin: a written callee's caller tier, a callee cell. -/
def OriginV (h : Array NeedCell) : CalleeOrigin → Prop
  | .written _ caller => ValidCtx h caller
  | .cell a => a < h.size
  | _ => True

/-- A collection-builtin call item: its supplied cell and its demanded value. -/
def ItemV (h : Array NeedCell) (item : CallableCallItem) : Prop :=
  OptAddr h item.need? ∧ ∀ v, item.value? = some v → RV h v

def ItemLV (h : Array NeedCell) (items : List CallableCallItem) : Prop := ∀ x ∈ items, ItemV h x

/-- A prepared control argument of a collection builtin. -/
def SuffixV (h : Array NeedCell) : PreparedSequenceBuiltinSuffixArg → Prop
  | .needAlgorithm a => a < h.size
  | .value r => RV h r
  | _ => True

def SuffixLV (h : Array NeedCell) (xs : List PreparedSequenceBuiltinSuffixArg) : Prop :=
  ∀ x ∈ xs, SuffixV h x

/-- Bound collection-builtin arguments. -/
def BoundV (h : Array NeedCell) (b : BoundSequenceBuiltinArguments) : Prop :=
  RLV h b.preparedInput.items ∧ CRLV h b.iterationItems ∧ SuffixLV h b.suffixArgs ∧ OptAddr h b.view?

/-- A computed spread's supply contribution: Ready items' payloads, transported cells. -/
def SupplyV (h : Array NeedCell) : SpreadSupply → Prop
  | .items values => RLV h values
  | .cells cells => ValidSourced h cells

/-- A prepared algorithm output. -/
def PreparedV (h : Array NeedCell) (p : PreparedAlgorithmOutput) : Prop :=
  CRV h p.counted ∧ RLV h p.outputSlots

/-- An optional list of results (a `while` round's verdict). -/
def OptRLV (h : Array NeedCell) (o : Option (List Result)) : Prop :=
  ∀ xs, o = some xs → RLV h xs

/-! ## The heap invariant -/

/-- What a STORED suspension references, inside the heap. -/
def SuspV (h : Array NeedCell) : NeedSuspension → Prop
  | .expression _ caller values => ValidCtx h caller ∧ VEV h values
  | .collector slice => ValidAddresses h slice
  | .ready value => CRV h value

/-- A completed VALUE outcome. -/
def StateV (h : Array NeedCell) : NeedState → Prop
  | .completed (.ok r) => CRV h r
  | _ => True

/-- A prepared plan supply. -/
def PlanV (h : Array NeedCell) : NeedPlanSupply → Prop
  | .prepared (.ok cells) => ValidSourced h cells
  | _ => True

/-- Every address a stored cell holds. Not constrained (out of domain): `callable` (no
    `Result`), `route` (no payload), `aliasUse` (a claim flag). -/
structure CellV (h : Array NeedCell) (c : NeedCell) : Prop where
  susp : SuspV h c.suspension
  state : StateV h c.state
  plan : PlanV h c.plan
  callee : OptAddr h c.callee
  receiver : OptAddr h c.receiver
  aliasBare : OptAddr h c.aliasBare

/-- A saved parameter activation: its need tier and its values. -/
def ActV (h : Array NeedCell) (act : ParameterActivation) : Prop :=
  ValidNeedEnv h act.needs ∧ VEV h act.values

/-- **THE WHOLE-EVALUATOR INVARIANT.** Each clause is required by a write point:
    * `collectors` — collector allocation (`allocateNeed`, the binder's collecting source);
    * `cells` — every push (`allocateNeed`, every Ready site), `NeedDemand.step` (`.completed`),
      `NeedPlan.prepare` (`setSupply`), `calleeCell` (`setCallee`), `NeedLink.receiverCell`
      (`setReceiver`), `aliasBareCell` (`aliasBare`), and the field-preserving writers
      (`NeedProjection.step`, `routeOf`, `takeTerminalAliasInvocation`, `aliasBareCell`'s claim);
    * `activations` — `recordParameterActivation` (and `wireSelectedBranchBody` through it);
    * `cache` — property-cache publication (`evalZeroArgPropertyAccessCounted`);
    * `aliasCells` — `aliasBindingCellRecorded`. -/
structure Inv (s : EvalState) : Prop where
  collectors : ValidCollectorHeap s.needs
  cells : ∀ (a : Nat) (c : NeedCell), s.needs[a]? = some c → CellV s.needs c
  activations : ∀ (i : Nat) (act : ParameterActivation), s.lexicalActivations[i]? = some act →
    ActV s.needs act
  cache : ∀ p ∈ s.zeroArgPropertyCache, CRV s.needs p.2
  aliasCells : ∀ p ∈ s.aliasCells, p.2 < s.needs.size

/-! ## Monotonicity -/

/-- A heap predicate preserved by growth. -/
def HMono (P : Array NeedCell → Prop) : Prop := ∀ (h h' : Array NeedCell), h.size ≤ h'.size → P h → P h'

/-- A result predicate preserved by growth. -/
def PMono {α : Type} (Q : α → Array NeedCell → Prop) : Prop := ∀ x, HMono (Q x)

section Mono
variable {h h' : Array NeedCell} (g : h.size ≤ h'.size)
include g

theorem RV.mono {r : Result} (v : RV h r) : RV h' r := fun a m => Nat.lt_of_lt_of_le (v a m) g
theorem CRV.mono {r : CountedResult} (v : CRV h r) : CRV h' r := RV.mono g v
theorem RLV.mono {xs : List Result} (v : RLV h xs) : RLV h' xs := fun x m => RV.mono g (v x m)
theorem CRLV.mono {xs : List CountedResult} (v : CRLV h xs) : CRLV h' xs := fun x m => CRV.mono g (v x m)
theorem VEV.mono {env : ValEnv} (v : VEV h env) : VEV h' env := fun p m => RV.mono g (v p m)
theorem OptAddr.mono {o : Option Nat} (v : OptAddr h o) : OptAddr h' o :=
  fun a e => Nat.lt_of_lt_of_le (v a e) g
theorem RAV.mono {x : ResolvedArgumentAlgorithm} (v : RAV h x) : RAV h' x := OptAddr.mono g v
theorem RALV.mono {xs : List ResolvedArgumentAlgorithm} (v : RALV h xs) : RALV h' xs :=
  fun x m => RAV.mono g (v x m)
theorem OriginV.mono {o : CalleeOrigin} (v : OriginV h o) : OriginV h' o := by
  cases o with
  | written _ c => exact ValidCtx.mono g v
  | cell a => exact Nat.lt_of_lt_of_le v g
  | none => trivial
  | bound _ _ => trivial
theorem ItemV.mono {x : CallableCallItem} (v : ItemV h x) : ItemV h' x :=
  ⟨OptAddr.mono g v.1, fun r e => RV.mono g (v.2 r e)⟩
theorem ItemLV.mono {xs : List CallableCallItem} (v : ItemLV h xs) : ItemLV h' xs :=
  fun x m => ItemV.mono g (v x m)
theorem SuffixV.mono {x : PreparedSequenceBuiltinSuffixArg} (v : SuffixV h x) : SuffixV h' x := by
  cases x with
  | needAlgorithm a => exact Nat.lt_of_lt_of_le v g
  | value r => exact RV.mono g v
  | algorithm _ => trivial
  | wholeNumber _ => trivial
theorem SuffixLV.mono {xs : List PreparedSequenceBuiltinSuffixArg} (v : SuffixLV h xs) : SuffixLV h' xs :=
  fun x m => SuffixV.mono g (v x m)
theorem BoundV.mono {b : BoundSequenceBuiltinArguments} (v : BoundV h b) : BoundV h' b :=
  ⟨RLV.mono g v.1, CRLV.mono g v.2.1, SuffixLV.mono g v.2.2.1, OptAddr.mono g v.2.2.2⟩
theorem SupplyV.mono {x : SpreadSupply} (v : SupplyV h x) : SupplyV h' x := by
  cases x with
  | items _ => exact RLV.mono g v
  | cells _ => exact ValidSourced.mono g v
theorem PreparedV.mono {p : PreparedAlgorithmOutput} (v : PreparedV h p) : PreparedV h' p :=
  ⟨CRV.mono g v.1, RLV.mono g v.2⟩
theorem OptRLV.mono {o : Option (List Result)} (v : OptRLV h o) : OptRLV h' o :=
  fun xs e => RLV.mono g (v xs e)
theorem SuspV.mono {s : NeedSuspension} (v : SuspV h s) : SuspV h' s := by
  cases s with
  | expression _ c vals => exact ⟨ValidCtx.mono g v.1, VEV.mono g v.2⟩
  | collector _ => exact ValidAddresses.mono g v
  | ready _ => exact CRV.mono g v
theorem StateV.mono {s : NeedState} (v : StateV h s) : StateV h' s := by
  cases s with
  | completed o => cases o with
    | ok r => exact CRV.mono g v
    | error _ => trivial
  | suspended => trivial
  | evaluating => trivial
theorem PlanV.mono {s : NeedPlanSupply} (v : PlanV h s) : PlanV h' s := by
  cases s with
  | prepared o => cases o with
    | ok cs => exact ValidSourced.mono g v
    | error _ => trivial
  | unprepared => trivial
  | preparing => trivial
theorem CellV.mono {c : NeedCell} (v : CellV h c) : CellV h' c :=
  ⟨SuspV.mono g v.susp, StateV.mono g v.state, PlanV.mono g v.plan, OptAddr.mono g v.callee,
   OptAddr.mono g v.receiver, OptAddr.mono g v.aliasBare⟩
theorem ActV.mono {act : ParameterActivation} (v : ActV h act) : ActV h' act :=
  ⟨ValidNeedEnv.mono g v.1, VEV.mono g v.2⟩
end Mono

/-! ## Structure of result validity -/

section Structure
variable {h : Array NeedCell}

theorem RV.atom (n : Int) : RV h (.atom n) := fun _ m => by cases m
theorem RV.str (s : String) : RV h (.str s) := fun _ m => by cases m
theorem RV.bool (b : Bool) : RV h (.bool b) := fun _ m => by cases m

theorem RV.seq_iff {xs : List Result} : RV h (.sequenceValue xs) ↔ RLV h xs := by
  constructor
  · intro v x mx a ma; exact v a (.seq mx ma)
  · intro v a m; cases m with
    | seq mx ma => exact v _ mx a ma

theorem RV.list_iff {xs : List Result} : RV h (.listValue xs) ↔ RLV h xs := by
  constructor
  · intro v x mx a ma; exact v a (.list mx ma)
  · intro v a m; cases m with
    | list mx ma => exact v _ mx a ma

theorem RV.callRef_iff {a : Nat} : RV h (.callRef a) ↔ a < h.size :=
  ⟨fun v => v a (.callRef a), fun v b m => by cases m; exact v⟩

theorem RV.argView_iff {a : Nat} : RV h (.argView a) ↔ a < h.size :=
  ⟨fun v => v a (.argView a), fun v b m => by cases m; exact v⟩

theorem RV.seq {xs : List Result} (v : RLV h xs) : RV h (.sequenceValue xs) := RV.seq_iff.2 v
theorem RV.list {xs : List Result} (v : RLV h xs) : RV h (.listValue xs) := RV.list_iff.2 v
theorem RV.callRef {a : Nat} (v : a < h.size) : RV h (.callRef a) := RV.callRef_iff.2 v
theorem RV.argView {a : Nat} (v : a < h.size) : RV h (.argView a) := RV.argView_iff.2 v

theorem RLV.nil : RLV h [] := fun _ m => by cases m
theorem RLV.cons {x : Result} {xs : List Result} (v : RV h x) (vs : RLV h xs) : RLV h (x :: xs) := by
  intro y m
  rcases List.mem_cons.mp m with rfl | m
  · exact v
  · exact vs y m
theorem RLV.head {x : Result} {xs : List Result} (v : RLV h (x :: xs)) : RV h x := v x List.mem_cons_self
theorem RLV.tail {x : Result} {xs : List Result} (v : RLV h (x :: xs)) : RLV h xs :=
  fun y m => v y (List.mem_cons_of_mem _ m)
theorem RLV.append {xs ys : List Result} (v1 : RLV h xs) (v2 : RLV h ys) : RLV h (xs ++ ys) := by
  intro y m
  rcases List.mem_append.mp m with m | m
  · exact v1 y m
  · exact v2 y m
theorem RLV.sub {xs ys : List Result} (v : RLV h xs) (hs : ∀ y ∈ ys, y ∈ xs) : RLV h ys :=
  fun y m => v y (hs y m)
theorem RLV.reverse {xs : List Result} (v : RLV h xs) : RLV h xs.reverse :=
  v.sub (fun _ m => List.mem_reverse.mp m)
theorem RLV.take {xs : List Result} (v : RLV h xs) (n : Nat) : RLV h (xs.take n) :=
  v.sub (fun _ m => List.mem_of_mem_take m)
theorem RLV.drop {xs : List Result} (v : RLV h xs) (n : Nat) : RLV h (xs.drop n) :=
  v.sub (fun _ m => List.mem_of_mem_drop m)
theorem RLV.singleton {x : Result} (v : RV h x) : RLV h [x] := RLV.cons v RLV.nil
theorem RLV.getElem? {xs : List Result} (v : RLV h xs) {i : Nat} {x : Result} (e : xs[i]? = some x) :
    RV h x := v x (List.mem_of_getElem? e)
theorem RLV.head? {xs : List Result} (v : RLV h xs) {x : Result} (e : xs.head? = some x) : RV h x :=
  v x (List.mem_of_mem_head? e)
theorem RLV.getLast? {xs : List Result} (v : RLV h xs) {x : Result} (e : xs.getLast? = some x) : RV h x :=
  v x (List.mem_of_getLast? e)
theorem RLV.map_atom (ns : List Int) : RLV h (ns.map Result.atom) := by
  intro x m
  obtain ⟨n, _, rfl⟩ := List.mem_map.mp m
  exact RV.atom n

theorem CRV.mk {r : Result} {n : Nat} (v : RV h r) : CRV h (r, n) := v
theorem CRLV.nil : CRLV h [] := fun _ m => by cases m
theorem CRLV.cons {x : CountedResult} {xs : List CountedResult} (v : CRV h x) (vs : CRLV h xs) :
    CRLV h (x :: xs) := by
  intro y m
  rcases List.mem_cons.mp m with rfl | m
  · exact v
  · exact vs y m
theorem CRLV.head {x : CountedResult} {xs : List CountedResult} (v : CRLV h (x :: xs)) : CRV h x :=
  v x List.mem_cons_self
theorem CRLV.tail {x : CountedResult} {xs : List CountedResult} (v : CRLV h (x :: xs)) : CRLV h xs :=
  fun y m => v y (List.mem_cons_of_mem _ m)
theorem CRLV.fst {xs : List CountedResult} (v : CRLV h xs) : RLV h (xs.map Prod.fst) := by
  intro x m
  obtain ⟨p, mp, rfl⟩ := List.mem_map.mp m
  exact v p mp
theorem CRLV.ones {xs : List Result} (v : RLV h xs) : CRLV h (xs.map (fun x => (x, 1))) := by
  intro p m
  obtain ⟨x, mx, rfl⟩ := List.mem_map.mp m
  exact v x mx

theorem VEV.nil : VEV h [] := fun _ m => by cases m
theorem VEV.filter {env : ValEnv} (v : VEV h env) (f : Ident × Result → Bool) : VEV h (env.filter f) :=
  fun p m => v p (List.mem_filter.mp m).1
theorem VEV.shadow {env : ValEnv} (v : VEV h env) (names : List Ident) : VEV h (ValEnv.shadow env names) :=
  VEV.filter v _
theorem VEV.lookup {env : ValEnv} (v : VEV h env) {x : Ident} {r : Result}
    (e : lookupAssoc x env = some r) : RV h r := by
  obtain ⟨k, m⟩ := lookup_mem x env r e
  exact v (k, r) m

theorem OptAddr.nil : OptAddr h none := fun _ e => by cases e
theorem OptAddr.mk {a : Nat} (v : a < h.size) : OptAddr h (some a) := fun _ e => by cases e; exact v
theorem OptAddr.get {o : Option Nat} {a : Nat} (v : OptAddr h o) (e : o = some a) : a < h.size := v a e

theorem ValidAddresses.nil : ValidAddresses h [] := fun _ m => by cases m
theorem ValidAddresses.cons {a : Nat} {xs : List Nat} (v : a < h.size) (vs : ValidAddresses h xs) :
    ValidAddresses h (a :: xs) := by
  intro b m
  rcases List.mem_cons.mp m with rfl | m
  · exact v
  · exact vs b m
theorem ValidSourced.nil : ValidSourced h [] := fun _ m => by cases m
theorem ValidSourced.fst_iff {xs : List NeedSupply.Sourced} :
    ValidSourced h xs ↔ ValidAddresses h (xs.map Prod.fst) := by
  constructor
  · exact ValidSourced.addresses
  · intro v p m; exact v p.1 (List.mem_map_of_mem m)

end Structure

/-! ## The invariant at the empty state and its FG-H1 projection -/

theorem empty_inv : Inv EvalState.empty :=
  ⟨fun _ _ h => by simp [EvalState.empty] at h, fun _ _ h => by simp [EvalState.empty] at h,
   fun _ _ h => by simp [EvalState.empty] at h, fun _ m => by simp [EvalState.empty] at m,
   fun _ m => by simp [EvalState.empty] at m⟩

/-- `Inv` is stronger than FG-H1's `StateValid`. -/
theorem Inv.toStateValid {s : EvalState} (v : Inv s) : StateValid s := by
  refine ⟨v.collectors, ?_, fun i act e => (v.activations i act e).1⟩
  intro a cell hc source caller values hs
  have := (v.cells a cell hc).susp
  rw [hs] at this
  exact this.1

theorem lt_of_getElem? {h : Array NeedCell} {a : Nat} {c : NeedCell} (hc : h[a]? = some c) : a < h.size := by
  rcases Nat.lt_or_ge a h.size with hl | hl
  · exact hl
  · rw [Array.getElem?_eq_none hl] at hc; cases hc

/-! ## The invariant-indexed run contract -/

/-- `SoundOver I pre m post`: FG-H1's `Sound` over an arbitrary state invariant `I`. -/
def SoundOver {α : Type} (I : EvalState → Prop) (pre : Array NeedCell → Prop) (m : EvalM α)
    (post : α → Array NeedCell → Prop) : Prop :=
  ∀ s, I s → pre s.needs →
    I (m.runState s).2 ∧ s.needs.size ≤ (m.runState s).2.needs.size ∧
      ∀ x, (m.runState s).1 = .ok x → post x (m.runState s).2.needs

/-- FG-H1's contract is `SoundOver StateValid`, definitionally. -/
theorem sound_is_soundOver {α : Type} (pre : Array NeedCell → Prop) (m : EvalM α)
    (post : α → Array NeedCell → Prop) : Sound pre m post ↔ SoundOver StateValid pre m post := Iff.rfl

/-- An `Inv` contract implies the FG-H1 one for `StateValid`-preserving purposes only when the
    entry state satisfies `Inv`; this is the projection the production corollaries use. -/
theorem SoundOver.toStateValid {α : Type} {pre : Array NeedCell → Prop} {m : EvalM α}
    {post : α → Array NeedCell → Prop} (hm : SoundOver Inv pre m post) (s : EvalState) (vs : Inv s)
    (ps : pre s.needs) :
    StateValid (m.runState s).2 ∧ s.needs.size ≤ (m.runState s).2.needs.size ∧
      ∀ x, (m.runState s).1 = .ok x → post x (m.runState s).2.needs :=
  let ⟨v, g, r⟩ := hm s vs ps
  ⟨v.toStateValid, g, r⟩

/-- **THE WORKING TRIPLE.** `SoundI P m Q`: for a monotone precondition `P`, `m` is sound over
    `Inv` (the monotonicity of `P` is what lets a continuation keep its facts across `m`). -/
def SoundI {α : Type} (P : Array NeedCell → Prop) (m : EvalM α) (Q : α → Array NeedCell → Prop) : Prop :=
  HMono P → SoundOver Inv P m Q

theorem SoundI.toSoundOver {α : Type} {P : Array NeedCell → Prop} {m : EvalM α}
    {Q : α → Array NeedCell → Prop} (hm : SoundI P m Q) (hp : HMono P) : SoundOver Inv P m Q := hm hp

theorem HMono.and {P R : Array NeedCell → Prop} (hp : HMono P) (hr : HMono R) :
    HMono (fun h => P h ∧ R h) := fun _ _ g v => ⟨hp _ _ g v.1, hr _ _ g v.2⟩

theorem SoundI.bind {α β : Type} {P : Array NeedCell → Prop} {m : EvalM α} {f : α → EvalM β}
    {Q : α → Array NeedCell → Prop} {R : β → Array NeedCell → Prop}
    (hm : SoundI P m Q) (hq : PMono Q) (hf : ∀ a, SoundI (fun h => P h ∧ Q a h) (f a) R) :
    SoundI P (m >>= f) R := by
  intro hp s vs ps
  rw [EvalM.bind_runState]
  obtain ⟨vt, gt, rt⟩ := hm hp s vs ps
  cases hr : m.runState s with
  | mk out t =>
    rw [hr] at vt gt rt
    cases out with
    | error e => exact ⟨vt, gt, fun _ h => by cases h⟩
    | ok a =>
      obtain ⟨vu, gu, ru⟩ := hf a (HMono.and hp (hq a)) t vt ⟨hp _ _ gt ps, rt a rfl⟩
      exact ⟨vu, Nat.le_trans gt gu, ru⟩

theorem SoundI.pure {α : Type} {P : Array NeedCell → Prop} {Q : α → Array NeedCell → Prop}
    (x : α) (h : ∀ heap, P heap → Q x heap) : SoundI P (pure x : EvalM α) Q :=
  fun _ s vs ps => ⟨vs, Nat.le_refl _, fun y hy => by cases hy; exact h _ ps⟩

theorem SoundI.weaken {α : Type} {P P' : Array NeedCell → Prop} {m : EvalM α}
    {Q Q' : α → Array NeedCell → Prop} (hm : SoundI P m Q)
    (hpp : ∀ h, P' h → P h) (hP : HMono P) (hq : ∀ x h, Q x h → Q' x h) : SoundI P' m Q' :=
  fun _ s vs ps =>
    let ⟨v, g, r⟩ := hm hP s vs (hpp _ ps)
    ⟨v, g, fun x hx => hq _ _ (r x hx)⟩

/-- Weakening of the postcondition only (no monotonicity needed). -/
theorem SoundI.post {α : Type} {P : Array NeedCell → Prop} {m : EvalM α}
    {Q Q' : α → Array NeedCell → Prop} (hm : SoundI P m Q) (hq : ∀ x h, P h → Q x h → Q' x h)
    (hpm : HMono P) : SoundI P m Q' := by
  intro hp s vs ps
  obtain ⟨v, g, r⟩ := hm hp s vs ps
  exact ⟨v, g, fun x hx => hq _ _ (hpm _ _ g ps) (r x hx)⟩

theorem SoundI.throw {α : Type} {P : Array NeedCell → Prop} {Q : α → Array NeedCell → Prop}
    (e : Error) : SoundI P (throw e : EvalM α) Q :=
  fun _ _ vs _ => ⟨vs, Nat.le_refl _, fun _ h => by cases h⟩

theorem SoundI.error {α : Type} {P : Array NeedCell → Prop} {Q : α → Array NeedCell → Prop}
    (e : Error) : SoundI P (EvalM.error e : EvalM α) Q :=
  fun _ _ vs _ => ⟨vs, Nat.le_refl _, fun _ h => by cases h⟩

/-- A computation that reads the state and never writes it. -/
theorem SoundI.of_readonly {α : Type} {P : Array NeedCell → Prop} {m : EvalM α}
    {Q : α → Array NeedCell → Prop}
    (h : ∀ s, Inv s → P s.needs → (m.runState s).2 = s ∧
      ∀ x, (m.runState s).1 = .ok x → Q x s.needs) : SoundI P m Q := by
  intro _ s vs ps
  obtain ⟨hs, hr⟩ := h s vs ps
  rw [hs]
  exact ⟨vs, Nat.le_refl _, hr⟩

/-- A computation from a fixed entry state (the continuation of a `get`). -/
def SoundAt {α : Type} (st : EvalState) (m : EvalM α) (Q : α → Array NeedCell → Prop) : Prop :=
  Inv (m.runState st).2 ∧ st.needs.size ≤ (m.runState st).2.needs.size ∧
    ∀ x, (m.runState st).1 = .ok x → Q x (m.runState st).2.needs

theorem SoundI.get_bind {β : Type} {P : Array NeedCell → Prop} {f : EvalState → EvalM β}
    {R : β → Array NeedCell → Prop}
    (h : HMono P → ∀ st, Inv st → P st.needs → SoundAt st (f st) R) : SoundI P (get >>= f) R := by
  intro hp s vs ps
  rw [EvalM.bind_runState]
  exact h hp s vs ps

theorem SoundAt.of_soundI {α : Type} {P : Array NeedCell → Prop} {m : EvalM α}
    {Q : α → Array NeedCell → Prop} {st : EvalState} (hm : SoundI P m Q) (hp : HMono P)
    (vs : Inv st) (ps : P st.needs) : SoundAt st m Q := hm hp st vs ps

theorem SoundAt.bind {α β : Type} {st : EvalState} {m : EvalM α} {f : α → EvalM β}
    {Q : α → Array NeedCell → Prop} {R : β → Array NeedCell → Prop} {P : Array NeedCell → Prop}
    (hm : SoundAt st m Q) (hq : PMono Q) (hp : HMono P) (ps : P st.needs)
    (hf : ∀ a, SoundI (fun h => P h ∧ Q a h) (f a) R) : SoundAt st (m >>= f) R := by
  unfold SoundAt at *
  rw [EvalM.bind_runState]
  obtain ⟨vt, gt, rt⟩ := hm
  cases hr : m.runState st with
  | mk out t =>
    rw [hr] at vt gt rt
    cases out with
    | error e => exact ⟨vt, gt, fun _ h => by cases h⟩
    | ok a =>
      obtain ⟨vu, gu, ru⟩ := hf a (HMono.and hp (hq a)) t vt ⟨hp _ _ gt ps, rt a rfl⟩
      exact ⟨vu, Nat.le_trans gt gu, ru⟩

theorem SoundAt.setState {st t : EvalState} (vt : Inv t) (g : st.needs.size ≤ t.needs.size) :
    SoundAt st (MonadState.set t : EvalM PUnit) (fun _ _ => True) := ⟨vt, g, fun _ _ => trivial⟩

theorem SoundAt.set_bind {β : Type} {st t : EvalState} {f : PUnit → EvalM β} {R : β → Array NeedCell → Prop}
    {P : Array NeedCell → Prop} (hp : HMono P) (pt : P t.needs) (vt : Inv t)
    (g : st.needs.size ≤ t.needs.size) (hf : SoundI P (f ⟨⟩) R) : SoundAt st (MonadState.set t >>= f) R := by
  unfold SoundAt
  rw [EvalM.bind_runState]
  show Inv ((f ⟨⟩).runState t).2 ∧ _ ∧ _
  obtain ⟨vu, gu, ru⟩ := hf hp t vt pt
  exact ⟨vu, Nat.le_trans g gu, ru⟩

theorem SoundAt.pure {α : Type} {st : EvalState} {Q : α → Array NeedCell → Prop} (x : α)
    (vs : Inv st) (h : Q x st.needs) : SoundAt st (pure x : EvalM α) Q :=
  ⟨vs, Nat.le_refl _, fun y hy => by cases hy; exact h⟩

theorem SoundAt.throw {α : Type} {st : EvalState} {Q : α → Array NeedCell → Prop} (e : Error)
    (vs : Inv st) : SoundAt st (throw e : EvalM α) Q :=
  ⟨vs, Nat.le_refl _, fun _ h => by cases h⟩

/-- `mapM` composes, each element run from the state the previous one left. -/
theorem SoundI.mapM {α β : Type} {P : Array NeedCell → Prop} {f : α → EvalM β}
    {q : β → Array NeedCell → Prop} (hq : PMono q)
    (xs : List α) (hf : ∀ x ∈ xs, SoundI P (f x) q) :
    SoundI P (xs.mapM f) (fun ys h => ∀ y ∈ ys, q y h) := by
  intro hp s vs ps
  rw [KatLang.NeedControl.Schedule.mapM_schedule]
  induction xs generalizing s with
  | nil => exact ⟨vs, Nat.le_refl _, fun ys h => by cases h; simp⟩
  | cons x rest ih =>
    simp only [KatLang.NeedControl.Schedule.schedule]
    obtain ⟨vt, gt, rt⟩ := hf x List.mem_cons_self hp s vs ps
    cases hr : (f x).runState s with
    | mk out t =>
      rw [hr] at vt gt rt
      cases out with
      | error e => exact ⟨vt, gt, fun _ h => by cases h⟩
      | ok y =>
        dsimp only
        obtain ⟨vu, gu, ru⟩ := ih (fun z m => hf z (List.mem_cons_of_mem _ m)) t vt (hp _ _ gt ps)
        cases hs : KatLang.NeedControl.Schedule.schedule f rest t with
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

/-- The postcondition of a captured outcome: a success satisfies `Q`. -/
def ExcV {α : Type} (Q : α → Array NeedCell → Prop) (r : Except Error α) (h : Array NeedCell) : Prop :=
  ∀ x, r = .ok x → Q x h

theorem ExcV.mono {α : Type} {Q : α → Array NeedCell → Prop} (hq : PMono Q) : PMono (ExcV Q) :=
  fun _ _ _ g v x e => hq x _ _ g (v x e)

theorem ExcV.ok {α : Type} {Q : α → Array NeedCell → Prop} {x : α} {h : Array NeedCell}
    (v : ExcV Q (.ok x) h) : Q x h := v x rfl

/-- An optional collector slice, valid when present. -/
def OptSliceV (h : Array NeedCell) (r : Option (List Nat)) : Prop :=
  ∀ slice, r = some slice → ValidAddresses h slice

/-- An optional saved activation, valid when present. -/
def OptActV (h : Array NeedCell) (r : Option ParameterActivation) : Prop :=
  ∀ act, r = some act → ActV h act

theorem OptSliceV.mono {h h' : Array NeedCell} (g : h.size ≤ h'.size) {r : Option (List Nat)}
    (v : OptSliceV h r) : OptSliceV h' r := fun s e => ValidAddresses.mono g (v s e)
theorem OptActV.mono {h h' : Array NeedCell} (g : h.size ≤ h'.size) {r : Option ParameterActivation}
    (v : OptActV h r) : OptActV h' r := fun s e => ActV.mono g (v s e)
theorem OptSliceV.get {h : Array NeedCell} {r : Option (List Nat)} {slice : List Nat}
    (v : OptSliceV h r) (e : r = some slice) : ValidAddresses h slice := v slice e
theorem OptSliceV.some {h : Array NeedCell} {slice : List Nat} (v : OptSliceV h (some slice)) :
    ValidAddresses h slice := v slice rfl
theorem OptActV.some {h : Array NeedCell} {act : ParameterActivation} (v : OptActV h (some act)) :
    ActV h act := v act rfl

/-- `evalAttempt` turns every ordinary failure into a successful `.error` result, keeping the
    state it reached; the incomplete outcome passes unchanged. -/
theorem SoundI.attempt {α : Type} {P : Array NeedCell → Prop} {m : EvalM α}
    {Q : α → Array NeedCell → Prop} (hm : SoundI P m Q) :
    SoundI P (evalAttempt m) (ExcV Q) := by
  intro hp s vs ps
  obtain ⟨vt, gt, rt⟩ := hm hp s vs ps
  have hrun : (evalAttempt m).runState s =
      (if (m.runState s).1.isIncomplete then (.error .fuelExhausted, (m.runState s).2)
       else (.ok (m.runState s).1, (m.runState s).2)) := rfl
  rw [hrun]
  revert vt gt rt
  rcases m.runState s with ⟨o, t⟩
  intro vt gt rt
  dsimp only at vt gt rt ⊢
  split
  · exact ⟨vt, gt, fun r hr => by cases hr⟩
  · refine ⟨vt, gt, fun r hr => ?_⟩
    cases hr
    intro y hy
    cases hy
    exact rt y rfl

theorem SoundI.withCtx {α : Type} {P : Array NeedCell → Prop} {m : EvalM α}
    {Q : α → Array NeedCell → Prop} (c : String) (hm : SoundI P m Q) (hq : PMono Q) :
    SoundI P (withCtx c m) Q := by
  unfold KatLang.withCtx
  refine SoundI.bind (SoundI.attempt hm) (fun r _ _ g v x e => hq x _ _ g (v x e)) ?_
  intro r
  cases r with
  | ok x => exact SoundI.pure _ (fun _ h => h.2 x rfl)
  | error e => exact SoundI.error _

theorem SoundI.withMissingOutputCtx {α : Type} {P : Array NeedCell → Prop} {m : EvalM α}
    {Q : α → Array NeedCell → Prop} (c : String) (hm : SoundI P m Q) (hq : PMono Q) :
    SoundI P (withMissingOutputCtx c m) Q := by
  unfold KatLang.withMissingOutputCtx
  refine SoundI.bind (SoundI.attempt hm) (fun r _ _ g v x e => hq x _ _ g (v x e)) ?_
  intro r
  cases r with
  | ok x => exact SoundI.pure _ (fun _ h => h.2 x rfl)
  | error e =>
    cases e
    all_goals first | exact SoundI.error _ | exact SoundI.throw _

theorem SoundI.map {α β : Type} {P : Array NeedCell → Prop} {m : EvalM α} (f : α → β)
    {Q : α → Array NeedCell → Prop} {R : β → Array NeedCell → Prop} (hm : SoundI P m Q)
    (hq : ∀ x h, Q x h → R (f x) h) : SoundI P (f <$> m) R := by
  intro hp s vs ps
  have hrun : (f <$> m).runState s = (match m.runState s with
      | (.ok a, next) => (.ok (f a), next)
      | (.error e, next) => (.error e, next)) := by
    show (m >>= (fun a => Pure.pure (f a))).runState s = _
    rw [EvalM.bind_runState]
    rcases m.runState s with ⟨o, t⟩
    cases o <;> rfl
  rw [hrun]
  obtain ⟨vt, gt, rt⟩ := hm hp s vs ps
  revert vt gt rt
  rcases m.runState s with ⟨o, t⟩
  intro vt gt rt
  cases o with
  | ok x => exact ⟨vt, gt, fun y hy => by cases hy; exact hq _ _ (rt x rfl)⟩
  | error e => exact ⟨vt, gt, fun _ h => by cases h⟩

/-- A rethrowing handler (`tryCatchThe`, `NeedBinder.captureMeta`) keeps soundness. -/
theorem SoundI.tryCatch {α : Type} {P : Array NeedCell → Prop} {m : EvalM α}
    {handler : Error → EvalM α} {Q : α → Array NeedCell → Prop}
    (hm : SoundI P m Q) (hh : ∀ e, SoundI P (handler e) Q) : SoundI P (tryCatchThe Error m handler) Q := by
  intro hp s vs ps
  obtain ⟨vt, gt, rt⟩ := hm hp s vs ps
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
      · obtain ⟨vu, gu, ru⟩ := hh err hp t vt (hp _ _ gt ps)
        exact ⟨vu, Nat.le_trans gt gu, ru⟩

/-- `monadLift` of a pure `Except`: its success is the lifted value. -/
theorem SoundI.lift {α : Type} {P : Array NeedCell → Prop} (e : Except Error α) :
    SoundI P (monadLift e : EvalM α) (fun x _ => e = .ok x) := by
  intro _ s vs _
  cases e with
  | ok x => exact ⟨vs, Nat.le_refl _, fun y hy => by cases hy; rfl⟩
  | error err => exact ⟨vs, Nat.le_refl _, fun _ hy => by cases hy⟩

/-! ## The call contracts

`CallPre c` constrains exactly the need addresses `c`'s inputs carry; `CallPost c` exactly those
of its result. Both are built from `ValidCtx`, `VEV`, `RV` (and their lifts) and the address
bounds of the arguments only — never from the evaluator, reachability or the evaluation's own
conclusion. -/

/-- The input contract of an evaluator call. An operation that only READS a cell at an address it
    is given (VALUE demand, CALLABLE projection, link channels, argument views) refuses an
    out-of-range address itself, so its contract places no bound on that address. -/
def CallPre : EvalCall → Array NeedCell → Prop
  | .whileLoop step ctx env _ cells => fun h => RAV h step ∧ ValidCtx h ctx ∧ VEV h env ∧ ValidAddresses h cells
  | .aliasStepIsRuntime _ _ ctx => fun h => ValidCtx h ctx
  | .aliasValue _ ctx env => fun h => ValidCtx h ctx ∧ VEV h env
  | .resolveAliasChase _ _ ctx _ _ => fun h => ValidCtx h ctx
  | .resolveAliasTarget _ ctx => fun h => ValidCtx h ctx
  | .resolveAliasValueTarget _ ctx => fun h => ValidCtx h ctx
  | .lookupLexicalProperty _ _ ctx => fun h => ValidCtx h ctx
  | .lookupLexicalValueProperty _ _ ctx => fun h => ValidCtx h ctx
  | .lookupLexical _ _ ctx => fun h => ValidCtx h ctx
  | .needPlanNormalizeCallee _ ctx => fun h => ValidCtx h ctx
  | .resolveAlg _ ctx => fun h => ValidCtx h ctx
  | .projectNeedCallable _ => fun _ => True
  | .projectNeedWrittenAt _ _ caller => fun h => ValidCtx h caller
  | .linkCallable _ => fun _ => True
  | .projectParameterCallable _ ctx => fun h => ValidCtx h ctx
  | .projectNeedWritten _ caller => fun h => ValidCtx h caller
  | .projectNeedStructuralMember _ ctx => fun h => ValidCtx h ctx
  | .resolveCalleeAlg _ ctx => fun h => ValidCtx h ctx
  | .expectPreparedSequenceBuiltinAlgorithmSuffixArg _ _ args _ => fun h => SuffixLV h args
  | .resolveDotReceiver? _ ctx => fun h => ValidCtx h ctx
  | .resolveDotReceiver _ ctx => fun h => ValidCtx h ctx
  | .algorithmIntrinsicRoute _ ctx => fun h => ValidCtx h ctx
  | .demandNeedRecursive _ => fun _ => True
  | .evalSuppliedAt _ _ ctx env => fun h => ValidCtx h ctx ∧ VEV h env
  | .linkValue _ => fun _ => True
  | .algorithmOfValue val _ ctx env => fun h => RV h val ∧ ValidCtx h ctx ∧ VEV h env
  | .capturedCallee _ => fun _ => True
  | .referenceReceiverValue _ _ ctx env => fun h => ValidCtx h ctx ∧ VEV h env
  | .algorithmCalleeOf _ ctx env => fun h => ValidCtx h ctx ∧ VEV h env
  | .evalSuppliedCallCounted origin _ cells ctx env _ => fun h =>
      OriginV h origin ∧ ValidSourced h cells ∧ ValidCtx h ctx ∧ VEV h env
  | .evalNeedUserSupply _ cells ctx env => fun h => ValidAddresses h cells ∧ ValidCtx h ctx ∧ VEV h env
  | .evalNeedFamilySupply _ cells ctx env _ => fun h => ValidAddresses h cells ∧ ValidCtx h ctx ∧ VEV h env
  | .invokeNeed arg => fun h => RAV h arg
  | .argumentNeed arg ctx env => fun h => RAV h arg ∧ ValidCtx h ctx ∧ VEV h env
  | .runNeedStepSlots _ ctx env cells _ => fun h => ValidCtx h ctx ∧ VEV h env ∧ ValidAddresses h cells
  | .runNeedWhileRound _ ctx env cells _ => fun h => ValidCtx h ctx ∧ VEV h env ∧ ValidAddresses h cells
  | .evalAlgOutputCore _ ctx env => fun h => ValidCtx h ctx ∧ VEV h env
  | .evalAlgOutput _ ctx env => fun h => ValidCtx h ctx ∧ VEV h env
  | .evalProgramOutput _ ctx env => fun h => ValidCtx h ctx ∧ VEV h env
  | .evalAlgOutputSlots _ ctx env => fun h => ValidCtx h ctx ∧ VEV h env
  | .formOutputRow ctx env _ => fun h => ValidCtx h ctx ∧ VEV h env
  | .whileVerdictSlots _ ctx env => fun h => ValidCtx h ctx ∧ VEV h env
  | .evalSequenceCallbackCall _ item ctx env _ => fun h => CRV h item ∧ ValidCtx h ctx ∧ VEV h env
  | .evalSequenceCallbackCallCounted _ item ctx env _ => fun h => CRV h item ∧ ValidCtx h ctx ∧ VEV h env
  | .evalAlgOutputPreparedCore _ ctx env => fun h => ValidCtx h ctx ∧ VEV h env
  | .evalOutputRowsPreparedCore _ rowCtx env => fun h => ValidCtx h rowCtx ∧ VEV h env
  | .evalCapturePreparedCore _ ctx env => fun h => ValidCtx h ctx ∧ VEV h env
  | .evalCaptureCountedCore _ ctx env => fun h => ValidCtx h ctx ∧ VEV h env
  | .evalCaptureValue _ ctx env => fun h => ValidCtx h ctx ∧ VEV h env
  | .evalAlgOutputCountedCore _ ctx env => fun h => ValidCtx h ctx ∧ VEV h env
  | .evalAlgOutputCounted _ ctx env => fun h => ValidCtx h ctx ∧ VEV h env
  | .evalZeroArgumentDemandOutputCounted _ ctx env => fun h => ValidCtx h ctx ∧ VEV h env
  | .evalZeroArgumentDemandOutput _ ctx env => fun h => ValidCtx h ctx ∧ VEV h env
  | .evalArgumentValueCounted arg ctx env => fun h => RAV h arg ∧ ValidCtx h ctx ∧ VEV h env
  | .evalArgumentValue arg ctx env => fun h => RAV h arg ∧ ValidCtx h ctx ∧ VEV h env
  | .evalZeroArgPropertyAccessCounted _ _ _ _ ctx env _ => fun h => ValidCtx h ctx ∧ VEV h env
  | .evalZeroArgPropertyAccess _ _ _ _ ctx env => fun h => ValidCtx h ctx ∧ VEV h env
  | .evalConditionalCallbackCallCounted _ args ctx env _ => fun h => CRLV h args ∧ ValidCtx h ctx ∧ VEV h env
  | .evalUserCallbackCallCounted _ args ctx env => fun h => CRLV h args ∧ ValidCtx h ctx ∧ VEV h env
  | .evalResolvedCallbackCallCounted _ args ctx env _ => fun h => CRLV h args ∧ ValidCtx h ctx ∧ VEV h env
  | .evalResolvedCallbackCall _ args ctx env _ => fun h => CRLV h args ∧ ValidCtx h ctx ∧ VEV h env
  | .evalSequenceReduceStepCounted _ element accumulator ctx env _ => fun h =>
      CRV h element ∧ RV h accumulator ∧ ValidCtx h ctx ∧ VEV h env
  | .demandSequenceBuiltinCallItemValue item ctx env => fun h => ItemV h item ∧ ValidCtx h ctx ∧ VEV h env
  | .bindSequenceBuiltinArguments _ _ args ctx env => fun h => RALV h args ∧ ValidCtx h ctx ∧ VEV h env
  | .evalReduceCounted collection _ initial ctx env => fun h =>
      CRLV h collection ∧ RV h initial ∧ ValidCtx h ctx ∧ VEV h env
  | .evalFilterCounted items _ ctx env => fun h => CRLV h items ∧ ValidCtx h ctx ∧ VEV h env
  | .evalMapCounted collection _ ctx env => fun h => CRLV h collection ∧ ValidCtx h ctx ∧ VEV h env
  | .applyBuiltinCountedSequence _ _ args ctx env => fun h => RALV h args ∧ ValidCtx h ctx ∧ VEV h env
  | .applyBuiltinCounted _ args ctx env => fun h => RALV h args ∧ ValidCtx h ctx ∧ VEV h env
  | .applyBuiltin _ args ctx env => fun h => RALV h args ∧ ValidCtx h ctx ∧ VEV h env
  | .applyBuiltinCountedResolved _ args ctx env => fun h => RALV h args ∧ ValidCtx h ctx ∧ VEV h env
  | .evalExplicitSequenceValueItems _ ctx env => fun h => ValidCtx h ctx ∧ VEV h env
  | .evalExplicitSequenceValueRowSlots _ rowCtx env => fun h => ValidCtx h rowCtx ∧ VEV h env
  | .evalExplicitSequenceValueExprSlots _ ctx env => fun h => ValidCtx h ctx ∧ VEV h env
  | .evalUserCallCounted _ _ ctx env => fun h => ValidCtx h ctx ∧ VEV h env
  | .evalConditionalCallCounted _ _ ctx env _ => fun h => ValidCtx h ctx ∧ VEV h env
  | .evalResolvedCall _ _ ctx env _ => fun h => ValidCtx h ctx ∧ VEV h env
  | .evalResolvedCallCounted _ _ ctx env _ origin => fun h => OriginV h origin ∧ ValidCtx h ctx ∧ VEV h env
  | .evalCallCountedExpr _ _ ctx env => fun h => ValidCtx h ctx ∧ VEV h env
  | .callLexicalWithReceiverCounted _ _ _ _ ctx env => fun h => ValidCtx h ctx ∧ VEV h env
  | .rejectDotStringIntrinsicArguments _ ctx env => fun h => ValidCtx h ctx ∧ VEV h env
  | .evalDotStringReceiverValue _ _ ctx env => fun h => ValidCtx h ctx ∧ VEV h env
  | .evalDotCallCounted _ _ _ _ ctx env => fun h => ValidCtx h ctx ∧ VEV h env
  | .rejectInvokeIntrinsicArguments _ ctx env => fun h => ValidCtx h ctx ∧ VEV h env
  | .invokeCallReferenceValue val => fun h => RV h val
  | .argumentViewCells _ => fun _ => True
  | .evalArgumentViewBuiltin _ _ => fun _ => True
  | .evalSequenceSpreadOperandValue _ ctx env => fun h => ValidCtx h ctx ∧ VEV h env
  | .evalSequenceSpreadCounted _ ctx env => fun h => ValidCtx h ctx ∧ VEV h env
  | .evalSupplySpread _ ctx env => fun h => ValidCtx h ctx ∧ VEV h env
  | .evalListLiteralCounted _ ctx env => fun h => ValidCtx h ctx ∧ VEV h env
  | .evalSequenceConstructCounted _ ctx env => fun h => ValidCtx h ctx ∧ VEV h env
  | .evalUnaryCounted _ _ ctx env => fun h => ValidCtx h ctx ∧ VEV h env
  | .evalBinaryCounted _ _ _ ctx env => fun h => ValidCtx h ctx ∧ VEV h env
  | .evalComparisonCounted _ _ ctx env => fun h => ValidCtx h ctx ∧ VEV h env
  | .evalComparisonLinksCounted _ previous _ _ ctx env => fun h => RV h previous ∧ ValidCtx h ctx ∧ VEV h env
  | .evalCounted _ ctx env => fun h => ValidCtx h ctx ∧ VEV h env
  | .evalUserCall _ _ ctx env => fun h => ValidCtx h ctx ∧ VEV h env
  | .evalConditionalCall _ _ ctx env _ => fun h => ValidCtx h ctx ∧ VEV h env
  | .evalCallExpr _ _ ctx env => fun h => ValidCtx h ctx ∧ VEV h env
  | .evalDotCall _ _ _ _ ctx env => fun h => ValidCtx h ctx ∧ VEV h env
  | .eval _ ctx env => fun h => ValidCtx h ctx ∧ VEV h env

/-- The result contract of an evaluator call. -/
def CallPost : (c : EvalCall) → c.Ret → Array NeedCell → Prop
  | .whileLoop .., cells, h => ValidAddresses h cells
  | .aliasStepIsRuntime .., _, _ => True
  | .aliasValue .., r, h => CRV h r
  | .resolveAliasChase .., _, _ => True
  | .resolveAliasTarget .., _, _ => True
  | .resolveAliasValueTarget .., _, _ => True
  | .lookupLexicalProperty .., _, _ => True
  | .lookupLexicalValueProperty .., _, _ => True
  | .lookupLexical .., _, _ => True
  | .needPlanNormalizeCallee .., _, _ => True
  | .resolveAlg .., _, _ => True
  | .projectNeedCallable .., _, _ => True
  | .projectNeedWrittenAt .., _, _ => True
  | .linkCallable .., _, _ => True
  | .projectParameterCallable .., _, _ => True
  | .projectNeedWritten .., _, _ => True
  | .projectNeedStructuralMember .., _, _ => True
  | .resolveCalleeAlg .., _, _ => True
  | .expectPreparedSequenceBuiltinAlgorithmSuffixArg .., _, _ => True
  | .resolveDotReceiver? .., _, _ => True
  | .resolveDotReceiver .., _, _ => True
  | .algorithmIntrinsicRoute .., _, _ => True
  | .demandNeedRecursive .., r, h => CRV h r
  | .evalSuppliedAt .., r, h => CRV h r
  | .linkValue .., r, h => CRV h r
  | .algorithmOfValue .., r, h => CRV h r
  | .capturedCallee .., _, _ => True
  | .referenceReceiverValue .., r, h => RV h r
  | .algorithmCalleeOf .., r, h => r.2.2 < h.size
  | .evalSuppliedCallCounted .., r, h => CRV h r
  | .evalNeedUserSupply .., r, h => CRV h r
  | .evalNeedFamilySupply .., r, h => CRV h r
  | .invokeNeed .., _, _ => True
  | .argumentNeed .., a, h => a < h.size
  | .runNeedStepSlots .., rs, h => RLV h rs
  | .runNeedWhileRound .., o, h => OptRLV h o
  | .evalAlgOutputCore .., r, h => RV h r
  | .evalAlgOutput .., r, h => RV h r
  | .evalProgramOutput .., r, h => RV h r
  | .evalAlgOutputSlots .., rs, h => RLV h rs
  | .formOutputRow .., rs, h => RLV h rs
  | .whileVerdictSlots .., o, h => OptRLV h o
  | .evalSequenceCallbackCall .., r, h => RV h r
  | .evalSequenceCallbackCallCounted .., r, h => CRV h r
  | .evalAlgOutputPreparedCore .., p, h => PreparedV h p
  | .evalOutputRowsPreparedCore .., p, h => PreparedV h p
  | .evalCapturePreparedCore .., p, h => PreparedV h p
  | .evalCaptureCountedCore .., r, h => CRV h r
  | .evalCaptureValue .., r, h => RV h r
  | .evalAlgOutputCountedCore .., r, h => CRV h r
  | .evalAlgOutputCounted .., r, h => CRV h r
  | .evalZeroArgumentDemandOutputCounted .., r, h => CRV h r
  | .evalZeroArgumentDemandOutput .., r, h => RV h r
  | .evalArgumentValueCounted .., r, h => CRV h r
  | .evalArgumentValue .., r, h => RV h r
  | .evalZeroArgPropertyAccessCounted .., r, h => CRV h r
  | .evalZeroArgPropertyAccess .., r, h => RV h r
  | .evalConditionalCallbackCallCounted .., r, h => CRV h r
  | .evalUserCallbackCallCounted .., r, h => CRV h r
  | .evalResolvedCallbackCallCounted .., r, h => CRV h r
  | .evalResolvedCallbackCall .., r, h => RV h r
  | .evalSequenceReduceStepCounted .., r, h => CRV h r
  | .demandSequenceBuiltinCallItemValue .., item, h => ItemV h item
  | .bindSequenceBuiltinArguments .., b, h => BoundV h b
  | .evalReduceCounted .., r, h => CRV h r
  | .evalFilterCounted .., r, h => CRV h r
  | .evalMapCounted .., r, h => CRV h r
  | .applyBuiltinCountedSequence .., r, h => CRV h r
  | .applyBuiltinCounted .., r, h => CRV h r
  | .applyBuiltin .., r, h => RV h r
  | .applyBuiltinCountedResolved .., r, h => CRV h r
  | .evalExplicitSequenceValueItems .., rs, h => RLV h rs
  | .evalExplicitSequenceValueRowSlots .., rs, h => RLV h rs
  | .evalExplicitSequenceValueExprSlots .., rs, h => RLV h rs
  | .evalUserCallCounted .., r, h => CRV h r
  | .evalConditionalCallCounted .., r, h => CRV h r
  | .evalResolvedCall .., r, h => RV h r
  | .evalResolvedCallCounted .., r, h => CRV h r
  | .evalCallCountedExpr .., r, h => CRV h r
  | .callLexicalWithReceiverCounted .., r, h => CRV h r
  | .rejectDotStringIntrinsicArguments .., _, _ => True
  | .evalDotStringReceiverValue .., r, h => RV h r
  | .evalDotCallCounted .., r, h => CRV h r
  | .rejectInvokeIntrinsicArguments .., _, _ => True
  | .invokeCallReferenceValue .., r, h => CRV h r
  | .argumentViewCells .., cells, h => ValidSourced h cells
  | .evalArgumentViewBuiltin .., r, h => CRV h r
  | .evalSequenceSpreadOperandValue .., r, h => RV h r
  | .evalSequenceSpreadCounted .., r, h => CRV h r
  | .evalSupplySpread .., x, h => SupplyV h x
  | .evalListLiteralCounted .., r, h => CRV h r
  | .evalSequenceConstructCounted .., r, h => CRV h r
  | .evalUnaryCounted .., r, h => CRV h r
  | .evalBinaryCounted .., r, h => CRV h r
  | .evalComparisonCounted .., r, h => CRV h r
  | .evalComparisonLinksCounted .., r, h => CRV h r
  | .evalCounted .., r, h => CRV h r
  | .evalUserCall .., r, h => RV h r
  | .evalConditionalCall .., r, h => RV h r
  | .evalCallExpr .., r, h => RV h r
  | .evalDotCall .., r, h => RV h r
  | .eval .., r, h => RV h r

open Lean Meta Elab Tactic in
/-- Destructs every conjunction hypothesis (recursively), clearing it. -/
elab "split_ands" : tactic => do
  let rec loop (fuel : Nat) : TacticM Unit := do
    match fuel with
    | 0 => pure ()
    | Nat.succ fuel =>
      let goal ← getMainGoal
      let found ← goal.withContext do
        for d in (← getLCtx) do
          unless d.isImplementationDetail do
            let t ← whnfR (← instantiateMVars d.type)
            if t.isAppOfArity ``And 2 then return some d.fvarId
        return none
      match found with
      | none => pure ()
      | some fv =>
        let gs ← goal.cases fv
        replaceMainGoal (gs.toList.map (·.mvarId))
        loop fuel
  loop 200

/-- One atomic monotonicity step (the leaf of `mono_conj`). -/
macro "mono_atom" g:term : tactic => `(tactic| with_reducible first
  | exact ValidCtx.mono $g ‹_›
  | exact VEV.mono $g ‹_›
  | exact RV.mono $g ‹_›
  | exact CRV.mono $g ‹_›
  | exact RLV.mono $g ‹_›
  | exact CRLV.mono $g ‹_›
  | exact RAV.mono $g ‹_›
  | exact RALV.mono $g ‹_›
  | exact ItemV.mono $g ‹_›
  | exact ItemLV.mono $g ‹_›
  | exact OriginV.mono $g ‹_›
  | exact SuffixV.mono $g ‹_›
  | exact SuffixLV.mono $g ‹_›
  | exact BoundV.mono $g ‹_›
  | exact SupplyV.mono $g ‹_›
  | exact PreparedV.mono $g ‹_›
  | exact OptRLV.mono $g ‹_›
  | exact OptAddr.mono $g ‹_›
  | exact ValidSourced.mono $g ‹_›
  | exact ValidAddresses.mono $g ‹_›
  | exact ValidNeedEnv.mono $g ‹_›
  | exact Nat.lt_of_lt_of_le ‹_› $g
  | exact OptSliceV.mono $g ‹_›
  | exact OptActV.mono $g ‹_›
  | exact ActV.mono $g ‹_›
  | exact CellV.mono $g ‹_›
  | exact True.intro)

theorem callPre_mono (c : EvalCall) : HMono (CallPre c) := by
  intro h h' g
  cases c <;> simp only [CallPre] <;> intro v
  all_goals split_ands
  all_goals (repeat' (first | mono_atom g | (refine ⟨?_, ?_⟩)))

theorem callPost_mono (c : EvalCall) : PMono (CallPost c) := by
  intro x h h' g
  cases c <;> simp only [CallPost] <;> intro v <;> mono_atom g

/-! ## Hoare transfer through the fuel core and to production -/

/-- The contract every call of an answer `rec` keeps. -/
def RecSound (rec : EvalRec) : Prop := ∀ c, SoundI (CallPre c) (rec c) (CallPost c)

/-- **THE PER-BODY OBLIGATION**: every evaluator body keeps the call contract whenever its
    recursive answer does. (`AddressInvariantBodies.evalStep_sound` proves it.) -/
def BodySound : Prop := ∀ rec : EvalRec, RecSound rec → RecSound (evalStep rec)

/-- The completed part of fuel `n` keeps the contract: where `evalFuel n` completes, by the
    induction hypothesis; elsewhere it stops at once with the entry state and an error. -/
theorem completedPart_sound (n : Nat)
    (ih : ∀ c s, Completes (evalFuel n c) s → Inv s → CallPre c s.needs →
      Inv ((evalFuel n c).runState s).2 ∧ s.needs.size ≤ ((evalFuel n c).runState s).2.needs.size ∧
        ∀ x, ((evalFuel n c).runState s).1 = .ok x → CallPost c x ((evalFuel n c).runState s).2.needs) :
    RecSound (completedPart n) := by
  intro c _ s vs ps
  by_cases hc : Completes (evalFuel n c) s
  · simp only [completedPart, if_pos hc]
    exact ih c s hc vs ps
  · simp only [completedPart, if_neg hc]
    exact ⟨vs, Nat.le_refl _, fun _ h => by cases h⟩

/-- **HOARE TRANSFER (completed fuel runs).** Under the per-body obligation, every completed
    run of the total core at every fuel, from an `Inv` state satisfying the call's input
    contract, ends in an `Inv` state with a heap no smaller and a result satisfying the call's
    output contract. (An INCOMPLETE core run is not covered: its normalized state is
    `EvalState.empty`; see `incomplete_core_state`.) -/
theorem sound_transfer (hbody : BodySound) :
    ∀ n c s, Completes (evalFuel n c) s → Inv s → CallPre c s.needs →
      Inv ((evalFuel n c).runState s).2 ∧ s.needs.size ≤ ((evalFuel n c).runState s).2.needs.size ∧
        ∀ x, ((evalFuel n c).runState s).1 = .ok x → CallPost c x ((evalFuel n c).runState s).2.needs := by
  intro n
  induction n with
  | zero => intro c s hc; exact absurd rfl hc
  | succ n ih =>
    intro c s hc vs ps
    have hpart := completedPart_sound n ih
    have hstep := evalStep_monotone _ _ (evalFuel_approx_completedPart n) c s
    have hne := (evalFuel_completes_iff (n + 1) c s).1 hc
    rw [evalFuel_succ] at hne ⊢
    by_cases hraw : ((evalStep (evalFuel n) c).runState s).1 = .error .fuelExhausted
    · rw [normalize_of_incomplete _ s hraw] at hne; exact absurd rfl hne
    · rw [normalize_of_complete _ s hraw]
      rcases hstep with hi | he
      · exfalso; apply hraw; unfold EvalM.IsIncompleteAt at hi; rw [hi]
      · rw [he]; exact hbody _ hpart c (callPre_mono c) s vs ps

/-- The incomplete outcome of the fuel core retains nothing: its state is `EvalState.empty`
    (which satisfies `Inv`, `empty_inv`), so heap growth and the validity of earlier addresses
    are NOT claimed for it. Stated through `Completes` only. -/
theorem incomplete_core_state (n : Nat) (c : EvalCall) (s : EvalState)
    (hc : ¬ Completes (evalFuel n c) s) :
    (evalFuel n c).runState s = (.error .fuelExhausted, {}) ∧ Inv ((evalFuel n c).runState s).2 := by
  have hi : (evalFuel n c).IsIncompleteAt s := Classical.not_not.mp hc
  unfold EvalM.IsIncompleteAt at hi
  rw [hi]
  exact ⟨rfl, empty_inv⟩

/-- **PRODUCTION (unconditional in the per-body obligation).** Every production operation
    `evalUnbounded c` keeps the contract on EVERY outcome: a completed run is a completed core
    run at some fuel (`production_completes_iff`); a non-completing one returns its entry state
    (`production_incomplete_state`). -/
theorem production_sound (hbody : BodySound) (c : EvalCall) :
    SoundOver Inv (CallPre c) (evalUnbounded c) (CallPost c) := by
  intro s vs ps
  by_cases hc : ProductionCompletes (evalUnbounded c) s
  · obtain ⟨m, hr, hm⟩ := (production_completes_iff c s _).1 ⟨rfl, hc⟩
    rw [← hr]
    exact sound_transfer hbody m c s hm vs ps
  · rw [production_incomplete_state c s hc]
    exact ⟨vs, Nat.le_refl _, fun _ h => by cases h⟩

/-- The production answer keeps the contract (the `RecSound` form). -/
theorem production_recSound (hbody : BodySound) : RecSound evalUnbounded :=
  fun c _ => production_sound hbody c

/-- Raw fuel iterates, premised on completion. -/
theorem evalFuel_sound (hbody : BodySound) (n : Nat) (c : EvalCall) (s : EvalState)
    (hc : Completes (evalFuel n c) s) (vs : Inv s) (ps : CallPre c s.needs) :
    Inv ((evalFuel n c).runState s).2 ∧ s.needs.size ≤ ((evalFuel n c).runState s).2.needs.size ∧
      ∀ x, ((evalFuel n c).runState s).1 = .ok x → CallPost c x ((evalFuel n c).runState s).2.needs :=
  sound_transfer hbody n c s hc vs ps

end KatLang.AddressInvariant
