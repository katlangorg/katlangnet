import KatLangArityLaws.PlanAlgorithmBridge
import KatLangArityLaws.PlanRouteBridgeGuards
import KatLangArityLaws.AddressInvariantGuards

open KatLang KatLang.CallPlan KatLang.PlanRouteBridge KatLang.HeapInsertion KatLang.PlanAlgorithmBridge
open KatLang.InvocationRouteGuards (dot algoCall grouped inId valueIs)
open KatLang.PlanConservativityGuards (flight)
open KatLang.PlanRouteBridgeGuards (supplied ctx same receiverParam)
open KatLang.AddressInvariantGuards (invOk)

/-!
# `.Algorithm` conditional-bridge guards (ledger E-18, step 1, M2)

Every guard runs the authoritative evaluator from `EvalState.empty`, over the `PlanRouteBridgeGuards`
declarations, at the plan's own flight (cell `evaluating`, route `.algorithm` recorded by `routeOf`,
callee unrecorded). `coreAt` DECIDES, by the compiled evaluator, exactly the premises and the
conclusion of the bridges' finite-domain forms `PlanAlgorithmBridge.algorithm_bridge_dot_at` /
`algorithm_bridge_grouped_at` (and `coreParamAt` those of the `_param_at` forms) on a concrete
reached state:

* **the decidable premises** — the plan cell's suspension, route and unrecorded callee; the
  executable reading of the address invariant (`invOk`); production's own route selection (the
  receiver probe and `selectDotEdge` for the dot form, `algorithmIntrinsicRoute` for the grouped
  form, with `settled`); `Frame` and `PlanCallees` at the comparison state, after production's
  receiver read (the tail entry) and at production's final state;
* **the contract's two instances** — the invocation receiver read from the plan-side state with the
  receiver cell `evaluating`, and `algorithmOfValue` over the receiver read's ACTUAL result from
  the plan-side state with the receiver cell completed, each against production's run;
* **the conclusion** — the plan's outcome is production's with its value shifted, and the plan's
  final state is production's under `finalInsertion`: `HeapInsertion.Inserted`, decided.

## What is a theorem and what is a guard

These are EXECUTABLE checks: a state is compared by its printed form and the evaluator runs
compiled. The kernel-checked applications of the same theorems — every premise proved, the
conclusion by the theorem — are in `PlanAlgorithmBridgeInstances`, for the scenarios whose whole run
the kernel can evaluate (a value receiver with a failing tail, a failing receiver, both written
forms; the tail's obligations over a call reference). A scenario whose receiver read returns a
call reference now also has kernel-checked whole-bridge applications in
`PlanAlgorithmBridgeParameterInstances` for an own-parameter supply context, in both forms.
The full `R.Algorithm(0)` control, an alias receiver, a captured-reference receiver, a
captured-ancestor parameter, effectful memo sharing, an address-bearing whole-bridge result and a
structured failure have THEOREM applications in `PlanAlgorithmBridgeSourceInstances` and its
companion modules (on genuine source programs of their own, the run equations proved by
proof-producing evaluation). The guards here stay as the wider executable corpus over the
`PlanRouteBridgeGuards` declarations: they decide the finite-domain premises and conclusion on
more scenarios, and prove nothing in the kernel.

`tailContractSelfReferenceDiffers` is the witness that REFUTED the first version's universal tail
premise (every receiver value, every `P` state): at the flight of the non-self-observing control it
instantiates the value with the plan cell's own reference. It stays as the reason the tail contract
is now asked only from the admissible tail entries (`PlanAlgorithmBridge.After`);
`selfReferenceNotAdmissible` checks, on the same state, that the control's ACTUAL receiver result is
another reference and that production's tail over the plan cell's own reference records that cell's
callee — the fact `PlanAlgorithmBridge.self_reference_records_callee` proves in general.

`relatedAt` is the relation alone, on the final states of `PlanRouteBridgeGuards.algorithmHeapDiffers`
and of the M0 controls. `SelfObservation.witnessViolatesBridge` shows the contract is NECESSARY: on
the M0 witness the conclusion fails in both written forms — outcome and relation — and the premise
that fails is the preservation one (production records the plan cell's callee: `Frame` is false at
its final state; the receiver is read twice).

A PARAMETER receiver inserts ONE cell (the link; its receiver is the parameter's own cell):
`paramBridgeAt` decides the premises and the conclusion of `algorithm_bridge_dot_param_at` /
`algorithm_bridge_grouped_param_at`, including the parameter's cell and its completed VALUE after
production's receiver read.
-/

namespace KatLang.PlanAlgorithmBridgeGuards

def planCalleesOk (s : EvalState) : Bool :=
  s.needs.toList.all fun cell => cell.callee.isNone || (NeedPlan.ofSuspension? cell.suspension).isSome

def frameOk (base plan : Nat) (s : EvalState) : Bool := decide (Frame base plan s)

def sameOutcome (σ : Site) (planned produced : Except Error CountedResult × EvalState) : Bool :=
  reprStr planned.1 == reprStr (shiftExcept (shiftCounted σ) produced.1)

/-- The premises and the conclusion of the bridge at the comparison state `x`, for the plan cell `a`
    with shape `shape` over the receiver `receiver`, against the production run `produced` (whose
    entry is the caller's business: `x` for the dot form, the route decision's entry for the grouped
    form). -/
def coreAt (a : Nat) (shape : NeedPlan.CallShape) (receiver : Expr) (x : EvalState)
    (produced : Except Error CountedResult × EvalState) : Bool :=
  let k := x.needs.size
  let σ : Site := ⟨k, 2⟩
  let read := (invocationReceiverValue receiver shape.caller shape.values).runState x
  let planned := (ordinaryCall productionPlanRoute a shape .algorithm).runState x
  -- structural premises and the invariant's two facts
  (match x.needs[a]? with
   | some cell =>
     reprStr (NeedPlan.ofSuspension? cell.suspension) == reprStr (some shape) &&
       cell.route == some .algorithm && cell.callee.isNone
   | none => false) &&
  invOk x && frameOk k a x && planCalleesOk x && frameOk k a read.2 && planCalleesOk read.2 &&
  frameOk k a produced.2 &&
  -- the contract instance for the receiver read: from the plan-side state with the cell `evaluating`
  (let ι₃ := planInsertion k a shape.callee shape.caller shape.values .evaluating
   same ((invocationReceiverValue receiver shape.caller shape.values).runState (embed ι₃ x))
     (shiftExcept (shiftResult σ) read.1, embed ι₃ read.2)) &&
  -- the contract instance for the tail: from the plan-side state with the cell completed
  (match read.1 with
   | .ok v =>
     let ι₅ := planInsertion k a shape.callee shape.caller shape.values (.completed (receiverMemo σ (.ok v)))
     let tail := (algorithmOfValue v (some shape.args) shape.caller shape.values).runState read.2
     same ((algorithmOfValue (shiftResult σ v) (some shape.args) shape.caller shape.values).runState (embed ι₅ read.2))
       (shiftExcept (shiftCounted σ) tail.1, embed ι₅ tail.2)
   | .error _ => true) &&
  -- THE CONCLUSION: related outcomes, and the final states in the insertion relation
  sameOutcome σ planned produced &&
  insertedB (finalInsertion x a shape receiver) planned.2 produced.2

/-- `algorithm_bridge_dot` for `target.Algorithm(args)` supplied as a fresh plan cell: its premises,
    the two contract instances and its conclusion, both sides run from the flight state. -/
def dotBridgeAt (target : Expr) (args : List Expr) : Bool :=
  let src := algoCall target args
  let fallback : Expr := .resolve "Algorithm"
  match supplied src with
  | none => false
  | some (a, s) =>
    match flight s a with
    | some (shape, .algorithm, x) =>
      reprStr shape == reprStr (dotShape target fallback args ctx []) &&
      (match (resolveDotReceiver? target ctx).runState x with
       | (.ok alg?, _) =>
         (match selectDotEdge ctx target "Algorithm" alg? with
          | .ok (.miss .algorithm) => true
          | _ => false)
       | _ => false) &&
      coreAt a shape target x ((reCountValueBoundary <$> evalCounted src ctx []).runState x)
    | _ => false

/-- `algorithm_bridge_grouped` for `(receiver.Algorithm)(args)`: production's route decision from
    the flight state answers `true`; the plan runs from the decision's exit state, production from
    its entry. `settled` records whether the two coincide. -/
def groupedBridgeAt (receiver : Expr) (args : List Expr) (settled : Bool := true) : Bool :=
  let f : Expr := .dotMember receiver "Algorithm" (.resolve "Algorithm") none
  let src : Expr := .call f args
  match supplied src with
  | none => false
  | some (a, s) =>
    match flight s a with
    | some (shape, .algorithm, x) =>
      reprStr shape == reprStr (groupedShape receiver (.resolve "Algorithm") args ctx []) &&
      (match (withCtx (CtxMsg.call f) (algorithmIntrinsicRoute receiver ctx)).runState x with
       | (.ok true, x₁) =>
         (reprStr x₁ == reprStr x) == settled &&
         coreAt a shape receiver x₁ ((reCountValueBoundary <$> evalCallCountedExpr f args ctx []).runState x)
       | _ => false)
    | _ => false

def R : Expr := .resolve "R"
def capture (e : Expr) : Expr := .call (.resolve "Capture") [e]
def callN (f : Ident) (args : List Expr) : Expr := .call (.resolve f) args

-- Successes and dispatch failures, both written forms.
#guard dotBridgeAt R [.num 0]                             -- `R.Algorithm(0)` = (0, 1): `algorithmHeapDiffers`' pair
#guard dotBridgeAt R [.num 1]                             -- the captured callee's `noMatchingBranch "F"`
#guard groupedBridgeAt R [.num 0]
#guard groupedBridgeAt R [.num 1]

/-- **The witness that refuted the FIRST version's universal tail premise** (`∀ v, InsertedOn P …`
    over every receiver value and every `P` state). At the reached flight of the non-self-observing
    control `R.Algorithm(0)`, instantiate the value with `callRef a`, where `a` is the OUTER plan
    cell (the actual receiver returns another reference). Production establishes that cell's callee
    and returns 0; the inserted link's evaluating receiver instead reports `demandCycle`. Both runs
    complete. So no premise quantified over every value can hold for a domain containing this
    flight; the repaired bridges ask the tail contract only from the admissible tail entries.
    A contract-design counterexample, not a language discrepancy. -/
def tailContractSelfReferenceDiffers : Bool :=
  match supplied (algoCall R [.num 0]) with
  | some (a, s) =>
    match flight s a with
    | some (shape, .algorithm, x) =>
      let σ : Site := ⟨x.needs.size, 2⟩
      let ι := planInsertion x.needs.size a shape.callee shape.caller shape.values .evaluating
      let v := Result.callRef a
      let produced := (algorithmOfValue v (some shape.args) shape.caller shape.values).runState x
      let planned := (algorithmOfValue (shiftResult σ v) (some shape.args)
        shape.caller shape.values).runState (embed ι x)
      frameOk x.needs.size a x &&
      (match produced.1, planned.1 with
       | .ok (.atom 0, 1), .error .demandCycle => true
       | _, _ => false) &&
      !same planned (shiftExcept (shiftCounted σ) produced.1, embed ι produced.2)
    | _ => false
  | none => false

#guard tailContractSelfReferenceDiffers

/-- **The self-reference is not an admissible tail input of the control — and the control's own
    tail is.** At the same flight: the receiver read's ACTUAL result is a call reference to ANOTHER
    cell, so `callRef a` has no tail entry (`PlanAlgorithmBridge.After` over the flight is empty for
    it); production's tail over the actual result keeps the plan cell's callee unrecorded (the
    preservation obligation `ktail` holds); and production's tail over `callRef a` RECORDS it — the
    fact `PlanAlgorithmBridge.self_reference_records_callee` proves — so the obligation would fail
    there. -/
def selfReferenceNotAdmissible : Bool :=
  match supplied (algoCall R [.num 0]) with
  | some (a, s) =>
    match flight s a with
    | some (shape, .algorithm, x) =>
      let read := (invocationReceiverValue R shape.caller shape.values).runState x
      (match read.1 with
       | .ok (.callRef p) =>
         p != a &&
         decide (Unrecorded a ((algorithmOfValue (.callRef p) (some shape.args) shape.caller shape.values).runState read.2).2) &&
         !decide (Unrecorded a ((algorithmOfValue (.callRef a) (some shape.args) shape.caller shape.values).runState x).2)
       | _ => false)
    | _ => false
  | none => false

#guard selfReferenceNotAdmissible
#guard dotBridgeAt (.resolve "S") [.num 3]                -- `Sq(3)` through the captured callee
#guard dotBridgeAt (.resolve "S") [.num 1, .num 2]        -- an arity failure of the fresh call
#guard dotBridgeAt (.resolve "Q") [.num 0]                -- a qualified captured callee `Pack.F`
#guard dotBridgeAt (.resolve "Q") [.num 1]
#guard groupedBridgeAt (.resolve "Q") [.num 1]
-- A failing callee projection (`X = Mk2(5)` captures `f(1)` with `f = 5`): the tail's failure.
#guard dotBridgeAt (.resolve "X") [.num 1]
-- Receiver failures: without output (a name, a member path, an inline block), nested, values.
#guard dotBridgeAt (.resolve "Empty") [.num 0]
#guard groupedBridgeAt (.resolve "Empty") [.num 0]
#guard dotBridgeAt (dot (.resolve "Lib") "Sub" none) [.num 0]
#guard dotBridgeAt (.resolve "Inner") [.num 0]
#guard dotBridgeAt (.resolve "Seven") [.num 0]            -- `5`-like: no call reference
#guard dotBridgeAt (.num 5) [.num 0]
#guard dotBridgeAt (dot R "Algorithm" none) [.num 0]      -- a nested `.Algorithm` receiver
-- Captured references and aliases: a written call receiver, a transparent reference to a reference.
#guard dotBridgeAt (capture (callN "F" [.num 0])) [.num 0]
#guard dotBridgeAt (capture (callN "F" [.num 0])) [.num 1]
#guard groupedBridgeAt (capture (callN "F" [.num 0])) [.num 0]
#guard dotBridgeAt (callN "Mk" [.num 1]) [.num 5]
#guard dotBridgeAt (.resolve "RA") [.num 0]
#guard groupedBridgeAt (.resolve "RA") [.num 1]
-- Laziness, repeated receiver demand and memo sharing: an effectful receiver is read ONCE on each
-- side (the `tick()` counter is part of the related states).
#guard dotBridgeAt (callN "Forced" [.call (.resolve "tick") [], R]) [.num 0]
#guard groupedBridgeAt (callN "Forced" [.call (.resolve "tick") [], R]) [.num 0]
-- Shifted allocations and an ADDRESS-BEARING result: the fresh call returns a call reference
-- allocated after the comparison state; the plan side's is production's, shifted by two.
#guard dotBridgeAt (capture (callN "Mk" [.num 1])) [.num 2]
#guard groupedBridgeAt (capture (callN "Mk" [.num 1])) [.num 2]

/-- The address-bearing instance, spelled out: production returns `callRef p`, the plan side
    `callRef (p + 2)`, with `p` at or above the comparison state's heap size. -/
def addressBearingResult : Bool :=
  let src := algoCall (capture (callN "Mk" [.num 1])) [.num 2]
  match supplied src with
  | none => false
  | some (a, s) =>
    match flight s a with
    | some (shape, .algorithm, x) =>
      (match ((ordinaryCall productionPlanRoute a shape .algorithm).runState x).1,
          ((reCountValueBoundary <$> evalCounted src ctx []).runState x).1 with
       | .ok (.callRef pp, 1), .ok (.callRef po, 1) => x.needs.size ≤ po && pp == po + 2
       | _, _ => false)
    | _ => false
#guard addressBearingResult

/-- The corollaries on an address-free result and on a failure: the outcomes are EQUAL, unshifted. -/
def exactOutcomeAt (src : Expr) : Bool :=
  match supplied src with
  | none => false
  | some (a, s) =>
    match flight s a with
    | some (shape, .algorithm, x) =>
      reprStr ((ordinaryCall productionPlanRoute a shape .algorithm).runState x).1 ==
        reprStr ((reCountValueBoundary <$> evalCounted src ctx []).runState x).1
    | _ => false

#guard exactOutcomeAt (algoCall R [.num 0])
#guard exactOutcomeAt (algoCall R [.num 1])
#guard exactOutcomeAt (algoCall (.resolve "Empty") [.num 0])
#guard !exactOutcomeAt (algoCall (capture (callN "Mk" [.num 1])) [.num 2])   -- an address-bearing result is shifted

/-! ## The relation alone, on the control pairs -/

/-- The insertion relation between the final states of the two runs from one flight state, with the
    inserted cells read off the plan side. -/
def relatedAt (a : Nat) (x : EvalState) (count : Nat)
    (planned produced : Except Error CountedResult × EvalState) : Bool :=
  let k := x.needs.size
  let cells := (List.range count).filterMap (fun i => planned.2.needs[k + i]?)
  let ι : Insertion := ⟨k, cells, a⟩
  cells.length == count && sameOutcome ι.site planned produced && insertedB ι planned.2 produced.2

/-- `PlanRouteBridgeGuards.algorithmHeapDiffers`' two runs — equal outcomes, unequal states — are in
    the relation: the states differ by exactly the two inserted cells and the callee record. -/
def algorithmHeapDiffersRelated : Bool :=
  let src := algoCall R [.num 0]
  match supplied src with
  | none => false
  | some (a, s) =>
    match flight s a with
    | some (shape, .algorithm, x) =>
      let planned := (ordinaryCall productionPlanRoute a shape .algorithm).runState x
      let produced := (reCountValueBoundary <$> evalCounted src ctx []).runState x
      reprStr planned.2 != reprStr produced.2 && relatedAt a x 2 planned produced
    | _ => false
#guard algorithmHeapDiffersRelated

namespace SelfObservation

open KatLang.PlanRouteBridgeGuards.SelfObservation

/-- The M0 controls WITHOUT self-observation satisfy the relation, in both written forms. -/
def controlRelated (plan : Expr) : Bool :=
  match sides plan with
  | some t => relatedAt t.a t.entry 2 t.planned t.produced && frameOk t.entry.needs.size t.a t.produced.2
  | none => false

#guard controlRelated controlPlain
#guard controlRelated controlPlainGrouped

/-- **The contract is necessary.** On the M0 witness the bridge's conclusion FAILS — the outcome
    is not production's (9 against 10) and the final states are not in the relation — and the
    premise that fails is non-observation: production itself records the plan cell's callee, so
    `Frame` is false at its final state (and it is true at the comparison state). -/
def witnessViolatesBridge (plan : Expr) : Bool :=
  match sides plan with
  | some t =>
    frameOk t.entry.needs.size t.a t.entry && !frameOk t.entry.needs.size t.a t.produced.2 &&
    !sameOutcome ⟨t.entry.needs.size, 2⟩ t.planned t.produced &&
    !relatedAt t.a t.entry 2 t.planned t.produced
  | none => false

#guard witnessViolatesBridge witnessDot
#guard witnessViolatesBridge witnessGrouped

/-- The pure self-observing control: the outcomes agree, but production records the plan cell's
    callee too (at another address), so the states are NOT in the relation — the contract excludes
    it whatever the receiver's effects. -/
def pureControlOutsideRelation : Bool :=
  match sides controlPure with
  | some t =>
    reprStr t.planned.1 == reprStr t.produced.1 && !frameOk t.entry.needs.size t.a t.produced.2 &&
    !relatedAt t.a t.entry 2 t.planned t.produced
  | none => false

#guard pureControlOutsideRelation

end SelfObservation

/-! ## A parameter receiver: one inserted cell (`algorithm_bridge_dot_param`, `_grouped_param`) -/

open KatLang.MemberStability (parameterAddressIn)

/-- The premises and the conclusion of the parameter-receiver bridge at the comparison state `x`: the
    parameter `name` is bound to a cell `b` of the comparison state; the structural premises and the
    invariant's two facts; `hmemo` — after production's receiver read the parameter's cell holds the
    read VALUE; the two contract instances, with ONE inserted cell; and the conclusion under
    `paramInsertion`. -/
def coreParamAt (a : Nat) (shape : NeedPlan.CallShape) (name : Ident) (x : EvalState)
    (produced : Except Error CountedResult × EvalState) : Bool :=
  let k := x.needs.size
  let σ : Site := ⟨k, 1⟩
  let read := (invocationReceiverValue (.param name) shape.caller shape.values).runState x
  let planned := (ordinaryCall productionPlanRoute a shape .algorithm).runState x
  match parameterAddressIn x.lexicalActivations name shape.caller with
  | none => false
  | some b =>
    let ι := paramInsertion k a shape.callee shape.caller shape.values b
    decide (b < k) &&
    (match x.needs[a]? with
     | some cell =>
       reprStr (NeedPlan.ofSuspension? cell.suspension) == reprStr (some shape) &&
         cell.route == some .algorithm && cell.callee.isNone
     | none => false) &&
    invOk x && frameOk k a x && planCalleesOk x && frameOk k a read.2 && planCalleesOk read.2 &&
    frameOk k a produced.2 &&
    (match read.1 with
     | .ok v =>
       (match read.2.needs[b]? with
        | some cell =>
          (match cell.state with
           | .completed (.ok (v', _)) => reprStr v' == reprStr v
           | _ => false)
        | none => false)
     | .error _ => true) &&
    same ((invocationReceiverValue (.param name) shape.caller shape.values).runState (embed ι x))
      (shiftExcept (shiftResult σ) read.1, embed ι read.2) &&
    (match read.1 with
     | .ok v =>
       let tail := (algorithmOfValue v (some shape.args) shape.caller shape.values).runState read.2
       same ((algorithmOfValue (shiftResult σ v) (some shape.args) shape.caller shape.values).runState (embed ι read.2))
         (shiftExcept (shiftCounted σ) tail.1, embed ι tail.2)
     | .error _ => true) &&
    sameOutcome σ planned produced && insertedB ι planned.2 produced.2

/-- `r.Algorithm(0)` / `(r.Algorithm)(0)` over a PARAMETER receiver bound to the written `arg`: the
    plan side allocates ONE cell — its callee link, whose receiver is the parameter's own cell — and
    the bridge's premises and conclusion hold. -/
def paramBridgeAt (arg : Expr) (groupedForm : Bool := false) : Bool :=
  match receiverParam arg with
  | none => false
  | some (c, s₀) =>
    let f : Expr := .dotMember (.param "r") "Algorithm" (.resolve "Algorithm") none
    let src := if groupedForm then Expr.call f [.num 0] else algoCall (.param "r") [.num 0]
    match (supplyNeed src c []).runState s₀ with
    | (.ok a, s) =>
      (match flight s a with
       | some (shape, .algorithm, x) =>
         if groupedForm then
           (match (withCtx (CtxMsg.call f) (algorithmIntrinsicRoute (.param "r") c)).runState x with
            | (.ok true, x₁) =>
              coreParamAt a shape "r" x₁ ((reCountValueBoundary <$> evalCallCountedExpr f [.num 0] c []).runState x)
            | _ => false)
         else
           (match (resolveDotReceiver? (.param "r") c).runState x with
            | (.ok alg?, _) =>
              (match selectDotEdge c (.param "r") "Algorithm" alg? with
               | .ok (.miss .algorithm) => true
               | _ => false)
            | _ => false) &&
           coreParamAt a shape "r" x ((reCountValueBoundary <$> evalCounted src c []).runState x)
       | _ => false)
    | _ => false

#guard paramBridgeAt R                                    -- a forwarded call reference: (0, 1)
#guard paramBridgeAt R true
#guard paramBridgeAt (.resolve "RA")
#guard paramBridgeAt (.resolve "RA") true
#guard paramBridgeAt (.resolve "Empty")                   -- the receiver's failure
#guard paramBridgeAt (.resolve "Empty") true
#guard paramBridgeAt (.num 5)                             -- a value that is no call reference
#guard paramBridgeAt (capture (callN "Mk" [.num 1]))      -- an address-bearing result
#guard paramBridgeAt (callN "Forced" [.call (.resolve "tick") [], R])   -- an effectful argument, read once

/-- The plan side allocates exactly one cell more than production over a parameter receiver. -/
def paramInsertsOne (arg : Expr) : Bool :=
  match receiverParam arg with
  | none => false
  | some (c, s₀) =>
    let src := algoCall (.param "r") [.num 0]
    match (supplyNeed src c []).runState s₀ with
    | (.ok a, s) =>
      (match flight s a with
       | some (shape, .algorithm, x) =>
         ((ordinaryCall productionPlanRoute a shape .algorithm).runState x).2.needs.size ==
           ((reCountValueBoundary <$> evalCounted src c []).runState x).2.needs.size + 1
       | _ => false)
    | _ => false

#guard paramInsertsOne R
#guard paramInsertsOne (.resolve "Empty")

end KatLang.PlanAlgorithmBridgeGuards
