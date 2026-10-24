import KatLangArityLaws.AddressInvariantProduction
import KatLangArityLaws.HeapAddressValidityGuards
import KatLangArityLaws.InvocationPlanGuards
import KatLangArityLaws.ArgumentViewGuards
import KatLangArityLaws.RuntimeAliasGuards
import KatLangArityLaws.MetaLoopGuards

open KatLang KatLang.NeedControl.Allocation KatLang.HeapAddressValidity KatLang.AddressInvariant
open KatLang.EvaluatorCore

/-!
# FG-H1-FU-01 guards: the whole-evaluator invariant `Inv`

Two kinds of evidence, complementing (never replacing) the universal theorems of
`AddressInvariant*.lean`:

* **Total-layer contract counterexamples** (kernel theorems). A `StateValid` state may hold a
  prepared plan supply naming a cell outside the heap (`badPlan`): `StateValid` constrains only
  collectors, expression tiers and activation tiers. On that state the plan readers
  (`NeedPlan.prepare`, `viewCells`, `viewSupply`) return the dangling address, so their contracts
  are FALSE over `StateValid` and need `Inv` (whose `CellV.plan` clause rules the state out);
  and allocating the collector a binder forms from that supply (`.collector [5]`) breaks
  `StateValid` itself. Each call-contract premise is shown necessary by a labelled
  counterexample.
* **Production guards** (`#guard`, executed). The production evaluator `evalUnbounded` runs
  through the kernel-opaque fuel search, so whole runs are evidence by execution: on the
  malformed state the production spread and VALUE channel reproduce the two legacy-premise
  counterexamples (FG-H1's `SpreadSound evalSupplySpread` and `ChannelsSound bindingChannels`
  are FALSE over `StateValid`); on whole programs every final state passes `invOk`, the
  clause-by-clause executable reading of `Inv` (every address a cell, activation, cache entry or
  alias cell holds is below the heap size; collector members precede their collector).
-/

namespace KatLang.AddressInvariantGuards

/-! ## The executable reading of `Inv` -/

/-- `RV`: every call reference / argument view inside the result is below `n`. -/
def resultOk (n : Nat) : Result → Bool
  | .callRef a => decide (a < n)
  | .argView a => decide (a < n)
  | .sequenceValue xs => xs.attach.all fun ⟨x, _⟩ => resultOk n x
  | .listValue xs => xs.attach.all fun ⟨x, _⟩ => resultOk n x
  | _ => true

def optOk (n : Nat) : Option Nat → Bool
  | some a => decide (a < n)
  | none => true

/-- `CellV` at address `a` (plus the collector order of `ValidCollectorHeap`). -/
def cellOk (n a : Nat) (c : NeedCell) : Bool :=
  (match c.suspension with
    | .expression _ caller values =>
      caller.needEnv.all (fun p => decide (p.2 < n)) && values.all (fun p => resultOk n p.2)
    | .collector slice => slice.all (fun b => decide (b < a))
    | .ready v => resultOk n v.1) &&
  (match c.state with
    | .completed (.ok r) => resultOk n r.1
    | _ => true) &&
  (match c.plan with
    | .prepared (.ok cells) => cells.all (fun p => decide (p.1 < n))
    | _ => true) &&
  optOk n c.callee && optOk n c.receiver && optOk n c.aliasBare

/-- Every clause of `Inv`. -/
def invOk (s : EvalState) : Bool :=
  let n := s.needs.size
  (List.range n).all (fun a => match s.needs[a]? with | some c => cellOk n a c | none => true) &&
  s.lexicalActivations.toList.all (fun act =>
    act.needs.all (fun p => decide (p.2 < n)) && act.values.all (fun p => resultOk n p.2)) &&
  s.zeroArgPropertyCache.all (fun p => resultOk n p.2.1) &&
  s.aliasCells.all (fun p => decide (p.2 < n))

/-! ## The malformed `StateValid` state -/

def emptyCtx : EvalCtx := { callStack := [] }

/-- A call-shaped cell whose route is recorded and whose prepared supply names cell 5 in a
    one-cell heap. -/
def planCell : NeedCell :=
  { suspension := .expression (.call (.resolve "F") []) emptyCtx [],
    route := some .call, plan := .prepared (.ok [(5, none)]) }

def badPlan : EvalState := { needs := #[planCell] }

theorem badPlan_stateValid : StateValid badPlan := by
  refine ⟨?_, ?_, ?_⟩
  · intro a c h slice hs
    match a, h with
    | 0, h => simp [badPlan] at h; subst h; simp [planCell] at hs
  · intro a c h source caller values hs p m
    match a, h with
    | 0, h =>
      simp [badPlan] at h; subst h; simp [planCell] at hs
      obtain ⟨_, rfl, _⟩ := hs
      simp [emptyCtx] at m
  · intro i act h
    simp [badPlan] at h

/-- `Inv` rules the state out: its `CellV.plan` clause is exactly the missing constraint. -/
theorem badPlan_not_inv : ¬ Inv badPlan := by
  intro h
  have := (h.cells 0 planCell rfl).plan (5, none) (by simp [planCell])
  simp [badPlan] at this

/-- The shape `viewCells` / `prepare` see at cell 0. -/
def planShape : NeedPlan.CallShape := ⟨.resolve "F", [], emptyCtx, [], .call⟩

/-- No spread callback, no classification: the readers never consult them on `badPlan`. -/
def refuse : NeedSupply.SpreadEval := fun _ _ _ => throw Error.divByZero
def noClassify : NeedPlan.CallShape → EvalM PlanRoute := fun _ => throw Error.divByZero

theorem badPlan_prepare :
    (NeedPlan.prepare refuse 0 planShape).runState badPlan = (.ok [(5, none)], badPlan) := rfl

theorem badPlan_viewCells :
    (NeedPlan.viewCells refuse noClassify 0).runState badPlan = (.ok [(5, none)], badPlan) := rfl

theorem badPlan_viewSupply :
    (NeedPlan.viewSupply refuse noClassify 0).runState badPlan = (.ok (.cells [(5, none)]), badPlan) := rfl

/-- **Total-layer counterexample (prepare)**: over `StateValid`, a plan reread is not valid. -/
theorem prepare_contract_false_over_stateValid :
    ¬ Sound (fun _ => True) (NeedPlan.prepare refuse 0 planShape) (fun xs h => ValidSourced h xs) := by
  intro h
  have r := (h badPlan badPlan_stateValid trivial).2.2 [(5, none)] (by rw [badPlan_prepare])
  rw [badPlan_prepare] at r
  have := r (5, none) (by simp)
  simp [badPlan] at this

/-- **Total-layer counterexample (viewSupply)**: an argument view's transported cells may dangle. -/
theorem viewSupply_contract_false_over_stateValid :
    ¬ Sound (fun _ => True) (NeedPlan.viewSupply refuse noClassify 0) (fun x h => SpreadSupplyValid h x) := by
  intro h
  have r := (h badPlan badPlan_stateValid trivial).2.2 (.cells [(5, none)]) (by rw [badPlan_viewSupply])
  rw [badPlan_viewSupply] at r
  have := r (5, none) (by simp)
  simp [badPlan] at this

/-- ... while over `Inv` the same readers are valid (`viewSupply_spec`), whatever the callbacks
    return: `badPlan` is simply not an `Inv` state. -/
theorem viewSupply_contract_over_inv (spread : NeedSupply.SpreadEval) (classify : NeedPlan.CallShape → EvalM PlanRoute)
    (hs : SpreadSpec spread) (hc : ClassifySpec classify) (a : Nat) :
    SoundOver Inv (fun _ => True) (NeedPlan.viewSupply spread classify a) (fun x h => SupplyV h x) :=
  viewSupply_spec hs hc (fun _ _ _ _ => trivial)

/-- The collector a binder forms from that supply. -/
def badCollector : EvalState := { needs := #[planCell, { suspension := .collector [5] }] }

theorem badPlan_allocate :
    (allocateNeed (.collector [5])).runState badPlan = (.ok 1, badCollector) := rfl

/-- **Total-layer counterexample (allocation)**: after `allocateNeed (.collector [5])` the state
    is neither `StateValid` nor `Inv`. -/
theorem badCollector_not_stateValid : ¬ StateValid badCollector := by
  intro h
  have := h.collectors 1 _ rfl [5] rfl 5 (by simp)
  omega

theorem badCollector_not_inv : ¬ Inv badCollector := fun h => badCollector_not_stateValid h.toStateValid

theorem allocate_collector_contract_false :
    ¬ Sound (fun _ => True) (allocateNeed (.collector [5])) (fun a h => a < h.size) := by
  intro h
  have v := (h badPlan badPlan_stateValid trivial).1
  rw [badPlan_allocate] at v
  exact badCollector_not_stateValid v

/-! ## Labelled call-contract counterexamples: each precondition is needed -/

def ctxWith (env : NeedEnv) : EvalCtx := { callStack := [], needEnv := env }

/-- `supply` (`CallPre`'s valid caller tier): a dangling tier forwards a dangling address. -/
theorem contract_supply_needs_tier :
    ¬ SoundOver Inv (fun _ => True) (supplyNeed (.param "x") (ctxWith [("x", 9)]) []) (fun a h => a < h.size) := by
  intro h
  have r := (h EvalState.empty empty_inv trivial).2.2 9 rfl
  exact absurd r (by decide)

/-- `ready` (a valid Ready payload): a Ready payload naming cell 9 breaks `CellV.susp`. -/
theorem contract_ready_needs_payload :
    ¬ SoundOver Inv (fun _ => True) (readyNeed (.callRef 9, 1)) (fun a h => a < h.size) := by
  intro h
  have v := (h EvalState.empty empty_inv trivial).1
  have := (v.cells 0 { suspension := .ready (.callRef 9, 1) } rfl).susp 9 (.callRef 9)
  exact absurd this (by decide)

/-- `allocate` (a valid collector slice): `.collector [0]` in the empty heap breaks the order. -/
theorem contract_collector_needs_slice :
    ¬ SoundOver Inv (fun _ => True) (allocateNeed (.collector [0])) (fun a h => a < h.size) := by
  intro h
  have v := (h EvalState.empty empty_inv trivial).1
  have := v.collectors 0 _ rfl [0] rfl 0 (by simp)
  omega

/-- `spread` callbacks: a callback transporting a dangling cell fails `SpreadSpec`. -/
theorem contract_spread_callback :
    ¬ SpreadSpec HeapAddressValidityGuards.danglingSpread := by
  intro h
  have ps : ValidCtx EvalState.empty.needs (ctxWith []) ∧ VEV EvalState.empty.needs [] :=
    ⟨fun _ m => by simp [ctxWith] at m, fun _ m => by simp at m⟩
  have r := (h (.num 0) (ctxWith []) [] (hmono_ctx_env _ _)) EvalState.empty empty_inv ps
  have := r.2.2 (.cells [(9, none)]) rfl (9, none) (by simp)
  exact absurd this (by decide)

/-! ## Production: the legacy premises are FALSE over `StateValid` (executed) -/

-- FG-H1 `SpreadSound evalSupplySpread emptyCtx [("V", .argView 0)]` fails at `badPlan`: the
-- production spread of an argument view returns cell 5 in a one-cell heap.
#guard match (evalSupplySpread (.sequenceSpread (.param "V")) emptyCtx [("V", .argView 0)]).runState badPlan with
  | (.ok (.cells [(5, none)]), s) => s.needs.size == 1 && !invOk s
  | _ => false

/-- `Fxs(*xs) = 7` declared in the caller tier of cell 1, which spreads the view of cell 0.
    The collector is deliberately unused, so VALUE succeeds with the malformed collector stored. -/
def fxsCtx : EvalCtx :=
  { callStack := [algPrivate [] []
      [("Fxs", algWithParameters [{ name := "xs", kind := .collecting }] [] [] [.num 7])] []] }

def channelState : EvalState :=
  { needs := #[planCell,
      { suspension := .expression (.call (.resolve "Fxs") [.sequenceSpread (.param "V")]) fxsCtx
          [("V", .argView 0)] }] }

theorem channelState_stateValid : StateValid channelState := by
  refine ⟨?_, ?_, ?_⟩
  · intro a c h slice hs
    match a, h with
    | 0, h => simp [channelState] at h; subst h; simp [planCell] at hs
    | 1, h => simp [channelState] at h; subst h; simp at hs
  · intro a c h source caller values hs p m
    match a, h with
    | 0, h =>
      simp [channelState] at h; subst h; simp [planCell] at hs
      obtain ⟨_, rfl, _⟩ := hs
      simp [emptyCtx] at m
    | 1, h =>
      simp [channelState] at h; subst h; simp at hs
      obtain ⟨_, rfl, _⟩ := hs
      simp [fxsCtx] at m
  · intro i act h
    simp [channelState] at h

-- FG-H1 `ChannelsSound bindingChannels` fails at `channelState`: the production VALUE channel
-- binds `xs` to a collector `[5]` at address 2 in a 3-cell heap (neither `StateValid` nor `Inv`).
#guard match (bindingChannels.value 1).runState channelState with
  | (.ok (.atom 7, 1), s) => s.needs.size == 3 && !invOk s &&
      (match s.needs[2]? with | some c => (match c.suspension with | .collector [5] => true | _ => false) | none => false)
  | _ => false

/-! ## Production: whole programs keep `Inv` (executed) -/

open KatLang.CallReferenceGuards in
/-- The fixtures of `CallReferenceGuards` / `ArgumentViewGuards` / `AlgorithmProjectionGuards` /
    `RuntimeAliasGuards`, plus `L = [R, R.Arguments]` (a cached zero-argument property holding a
    call reference and an argument view) and `Outer2(k) = { In = k ⏎ In + 1 }` (a captured
    parameter tier). -/
def fixtures : List (Ident × Algorithm) :=
  ArgumentViewGuards.extra ++ AlgorithmProjectionGuards.extra.filter (fun p => p.1 != "Pick") ++
  RuntimeAliasGuards.extraRA ++ refR ++
  [("L", alg [] [] [] [.listLiteral [.resolve "R", ArgumentViewGuards.args (.resolve "R")]]),
   ("Outer2", algPrivate ["k"] [] [("In", alg [] [] [] [.param "k"])]
      [CallReferenceGuards.add (.resolve "In") (.num 1)]),
   ("AR", RuntimeAliasGuards.alias (AlgorithmProjectionGuards.algorithm (.resolve "R")))]

def stateOf (e : Expr) : Option (Result × EvalState) :=
  match runResultWithState e with
  | .ok p => some p
  | .error _ => none

/-- The run succeeds with `v`, its final heap is nonempty, and its final state passes `invOk`. -/
def keeps (rows : List Expr) (v : Result) : Bool :=
  match stateOf (CallReferenceGuards.program fixtures rows) with
  | some (r, s) => r == v && s.needs.size > 0 && invOk s
  | none => false

open KatLang.CallReferenceGuards KatLang.ArgumentViewGuards

-- Computed `.items` spread (Ready items of `Pair()*`), and `.cells` transport of an argument view.
#guard keeps [callF "Add" [.sequenceSpread (callF "Pair" [])]] (.atom 3)
#guard keeps [callF "Sq" [.sequenceSpread (args R)]] (.atom 25)
-- The plan supply re-read twice (one prepared supply, `CellV.plan`).
#guard keeps [add (.index (args R) [.num 0]) (.index (args R) [.num 0])] (.atom 10)
#guard keeps [dot (args R) "count"] (.atom 1)
-- Ready / nested payloads: a cached zero-argument property holding a call reference and a view.
#guard keeps [dot (.resolve "L") "count"] (.atom 2)
#guard keeps [invoke (.index (.resolve "L") [.num 0])] (.atom 25)
-- Callee / receiver / runtime-alias paths.
#guard keeps [invoke R] (.atom 25)
#guard keeps [.call (AlgorithmProjectionGuards.algorithm R) [.num 3]] (.atom 9)
#guard keeps [callF "AR" [.num 4]] (.atom 16)
#guard keeps [callF "UseA" [.resolve "Sq"]] (.atom 81)
-- Direct and captured parameter tiers.
#guard keeps [invoke (callF "Fwd2" [callF "Sq" [.num 2]])] (.atom 4)
#guard keeps [callF "Outer2" [.num 6]] (.atom 7)
-- Binder: deconstruction, clause family, META capture.
#guard keeps [callF "Mix" [.listLiteral [.num 4], callF "Sq" [.num 1]]] (.atom 4)
#guard keeps [callF "Sign" [.num 0], callF "Sign" [.num 5]] (.sequenceValue [.atom 100, .atom 5])
#guard keeps [callF "Both" [.num 1, callF "Sq" [.num 3]]] (.atom 10)

/-! ### The stored payloads, supplies and links those runs leave (observed, then `invOk`) -/

/-- The result carries a call reference or an argument view. -/
def mentionsAny : Result → Bool
  | .callRef _ => true
  | .argView _ => true
  | .sequenceValue xs => xs.attach.any fun ⟨x, _⟩ => mentionsAny x
  | .listValue xs => xs.attach.any fun ⟨x, _⟩ => mentionsAny x
  | _ => false

def count (s : EvalState) (p : NeedCell → Bool) : Nat := (s.needs.toList.filter p).length

def isReady (c : NeedCell) : Bool := match c.suspension with | .ready _ => true | _ => false
def readyRef (c : NeedCell) : Bool := match c.suspension with | .ready v => mentionsAny v.1 | _ => false
def isCollector (c : NeedCell) : Bool := match c.suspension with | .collector _ => true | _ => false
def prepared (c : NeedCell) : Bool := match c.plan with | .prepared (.ok (_ :: _)) => true | _ => false
def completedRef (c : NeedCell) : Bool := match c.state with | .completed (.ok v) => mentionsAny v.1 | _ => false
def cacheRefs (s : EvalState) : Nat := (s.zeroArgPropertyCache.filter fun p => mentionsAny p.2.1).length
def tiers (s : EvalState) : Nat := (s.lexicalActivations.toList.filter fun a => !a.needs.isEmpty).length

/-- The run succeeds with `v`, its final state shows `obs` and passes `invOk`. -/
def observes (rows : List Expr) (v : Result) (obs : EvalState → Bool) : Bool :=
  match stateOf (CallReferenceGuards.program fixtures rows) with
  | some (r, s) => r == v && obs s && invOk s
  | none => false

-- `Pair()*`: two fresh Ready item cells (heap 2).
#guard observes [callF "Add" [.sequenceSpread (callF "Pair" [])]] (.atom 3)
  fun s => s.needs.size == 2 && count s isReady == 2
-- `Sq(*R.Arguments)`: ONE prepared plan supply, transported; a Ready reference, a completed VALUE
-- holding a reference and a cached reference are all stored.
#guard observes [callF "Sq" [.sequenceSpread (args R)]] (.atom 25)
  fun s => count s prepared == 1 && count s readyRef == 1 && count s completedRef == 1 && cacheRefs s == 1
-- The plan supply re-read across an intervening evaluation: still ONE prepared supply.
#guard observes [add (.index (args R) [.num 0]) (.index (args R) [.num 0])] (.atom 10)
  fun s => count s prepared == 1
-- `L = [R, R.Arguments]`: the cache stores the reference and the view.
#guard observes [dot (.resolve "L") "count"] (.atom 2) fun s => cacheRefs s == 2 && count s completedRef == 2
-- `R.Algorithm(3)`: a recorded callee cell; `AR(4)`: a recorded callee, receiver and alias cell.
#guard observes [.call (AlgorithmProjectionGuards.algorithm R) [.num 3]] (.atom 9)
  fun s => count s (fun c => c.callee.isSome) == 1
#guard observes [callF "AR" [.num 4]] (.atom 16)
  fun s => count s (fun c => c.callee.isSome) == 1 && count s (fun c => c.receiver.isSome) == 1 &&
    s.aliasCells.length == 1
-- Captured / forwarded tiers: saved activations with nonempty need tiers.
#guard observes [invoke (callF "Fwd2" [callF "Sq" [.num 2]])] (.atom 4) fun s => tiers s == 5
#guard observes [callF "Outer2" [.num 6]] (.atom 7) fun s => tiers s == 1
-- Deconstruction: structural Ready items; a collecting parameter: one collector cell.
#guard observes [callF "Mix" [.listLiteral [.num 4], callF "Sq" [.num 1]]] (.atom 4)
  fun s => count s isReady == 2 && count s readyRef == 1
#guard observes [callF "Coll" [.num 1, .num 2]] (.listValue [.atom 1, .atom 2])
  fun s => count s isCollector == 1

/-- META builtins (`while(meta step)`, `repeat(meta step, count)`) over the `MetaLoopGuards`
    fixtures. -/
def loopKeeps (rows : List Expr) (v : Result) : Bool :=
  match stateOf (MetaLoopGuards.program [] rows) with
  | some (r, s) => r == v && s.needs.size > 0 && invOk s
  | none => false

#guard loopKeeps [MetaLoopGuards.callN "while" [MetaLoopGuards.callN "Step" [.num 0]]] (.atom 3)
#guard loopKeeps [MetaLoopGuards.callN "repeat" [MetaLoopGuards.callN "Inc" [.num 0], .num 5]] (.atom 5)
#guard loopKeeps [MetaLoopGuards.dot (MetaLoopGuards.callN "Fib" [.sequenceSpread (.resolve "P")]) "repeat"
    (some [.num 10])] (.sequenceValue [.atom 55, .atom 89])

/-! ## Production: an ordinary error retains a valid prefix; the incomplete core retains nothing -/

def rootCtx : EvalCtx := { callStack := [preludeAlg] }

-- Ready payloads retain addresses through both list and sequence nesting. The first cell
-- provides a valid address; the second allocation stores, and VALUE returns, that exact payload.
def nestedPayload : Result := .listValue [.sequenceValue [.callRef 0, .argView 0]]

#guard match (do
    let a ← readyNeed (nestedPayload, 1)
    let r ← bindingChannels.value a
    pure r : EvalM CountedResult).runState HeapAddressValidityGuards.oneReady with
  | (.ok (r, 1), s) => r == nestedPayload && s.needs.size == 2 && invOk s &&
      (match s.needs[1]? with
       | some c => match c.suspension with
         | .ready (stored, 1) => stored == nestedPayload
         | _ => false
       | _ => false)
  | _ => false

-- Supply formation itself fails in the computed spread, after storing the first suspended
-- argument. Pin the ordinary error and the exact retained prefix, rather than a later binder error.
#guard match (formNeedSupplySourced [.num 5, .sequenceSpread (.binary .div (.num 1) (.num 0))]
    rootCtx []).runState EvalState.empty with
  | (.error .divByZero, s) => s.needs.size == 1 && invOk s &&
      (match s.needs[0]? with
       | some c => match c.suspension with
         | .expression (.num 5) _ [] => true
         | _ => false
       | _ => false)
  | _ => false

-- An ordinary failure after a valid prefix: the error is returned from a NONEMPTY retained heap
-- that keeps `Inv` (`production_sound_all` claims every outcome).
#guard match (eval (CallReferenceGuards.program [] [callF "Add" [.num 5, .binary .div (.num 1) (.num 0)]]) rootCtx []).runState
    EvalState.empty with
  | (.error e, s) => CallPlanGuards.failsAs (Except.error e : Except Error Result) .divByZero &&
      s.needs.size > 0 && invOk s
  | _ => false

-- The completed error from a nonempty `Inv` state keeps the entry cells.
#guard match (eval (.binary .div (.num 1) (.num 0)) rootCtx []).runState HeapAddressValidityGuards.oneReady with
  | (.error .divByZero, s) => s.needs.size == 1 && invOk s
  | _ => false

/-- The incomplete outcome of the fuel core returns `EvalState.empty` (it retains nothing, and
    `Inv` holds of it: `incomplete_core_state`), whatever the entry state. -/
theorem incomplete_core_empty :
    (evalFuel 0 (.eval (.num 1) rootCtx [])).runState HeapAddressValidityGuards.oneReady =
      (.error .fuelExhausted, {}) := rfl

#guard invOk {}
#guard invOk HeapAddressValidityGuards.oneReady
#guard !invOk badPlan

end KatLang.AddressInvariantGuards
