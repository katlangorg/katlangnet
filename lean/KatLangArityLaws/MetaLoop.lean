import KatLangArityLaws.AlgorithmProjection
import KatLangArityLaws.ArgumentView

open KatLang KatLang.CallPlan

/-!
# META-S3-3: `while(meta step)` and `repeat(meta step, count)` (October 2026)

The loop builtins are ordinary fixed-arity callables whose step is a genuine META parameter. The
authoritative definitions are in `lean/KatLang.lean`:

* `builtinSignature` — THE ONE builtin signature (`while(meta step)`, `repeat(meta step, count)`),
  read by the arity contract (`builtinAcceptsArity`, `builtinMinimumArity`), the builtin META
  binding, formula lifting (`builtinLiftingSignature`) and the lifting roles
  (`builtinLiftingSlotRole` via `builtinMetaAt`);
* the META binding step of `applyBuiltinCounted` (`builtinDeclaresMeta`): the arity gate, then
  THE ONE binder `bindNeedPatterns` over the signature, whose `.metaRef` arm is
  `NeedPlan.reference` (the user META capture);
* `metaLoopCapture` — the captured step's setup: the adapter's reference decoded into its plan,
  the plan's ONE sticky supply (`argumentViewCells` = `NeedPlan.viewCells`) as the initial state,
  the plan's canonical callee cell (`NeedPlan.calleeCell`) as the step;
* `metaRepeatSetup` — RP-1: the captured setup BEFORE the count.

Proved here, over those total definitions:

* the signature facts: exact arity (`while_arity`, `repeat_arity`), the binding patterns
  (`while_binding_patterns`, `repeat_binding_patterns`), the META builtins are exactly the loops
  (`declares_meta_iff`), lifting reads the one signature (`lifting_is_the_signature`) and the META
  step position transports its cell while `count` is a value (`loop_lifting_roles`);
* INERT CAPTURE — the binder's `meta step` occurrence on a plan cell allocates ONE Ready adapter and
  changes nothing else (`step_capture_inert`, from `production_meta_binding`);
* the capture's state and step (`metaLoopCapture_run`): the initial state is EXACTLY the plan's view
  cells (`state_is_view_cells`; for a prepared plan, its recorded supply with nothing run,
  `state_of_prepared_plan` — the cells `Invoke` and `Arguments` share), and the step is the
  plan's canonical callee cell (`step_is_recorded_callee_cell`), established inertly
  (`step_establishment_inert`);
* RP-1 — `repeat` runs the captured setup before the count (`repeat_setup_order`), and a failing
  setup never demands the count (`repeat_setup_failure_skips_count`);
* OD-1 — an empty captured supply is the ordinary zero-slot state (`zero_state_capture`), whose
  completed loop is `()` with emitted count 0 (`zero_state_result`);
* plain/dot preparation — `X.while` / `X.repeat(n)` prepare the bundles of `while(X)` /
  `repeat(X, n)` (`dot_while_preparation`, `dot_repeat_preparation`).

NOT claimed (source facts pinned by `MetaLoopGuards.lean` and the regenerated corpora): that the
evaluator's `applyBuiltinCounted` installs these definitions with `read := demandNeedRecursive` and
`view := argumentViewCells` (an installation of the total core, R7), that the dot route then reaches
the ordinary call funnel (Q-66), whole-loop refinement, and anything about C# async resolution,
cancellation, J7 plan retention or diagnostics (C#-only, `MetaLoopInterfaceTests`).
-/

namespace KatLang.MetaLoopLaws

/-! ## The one builtin signature -/

theorem while_signature :
    builtinSignature .whileBuiltin = [.capture { name := "step", kind := .metaRef }] := rfl

theorem repeat_signature :
    builtinSignature .repeatBuiltin =
      [.capture { name := "step", kind := .metaRef }, .capture { name := "count" }] := rfl

/-- The binder patterns of `while(meta step)`: one META capture. -/
theorem while_binding_patterns :
    (builtinSignature .whileBuiltin).map NeedPattern.ofParameter = [.metaRef "step"] := by
  simp [builtinSignature, sequenceBuiltinMetadata?, NeedPattern.ofParameter]

/-- The binder patterns of `repeat(meta step, count)`: a META capture and an ordinary binding. -/
theorem repeat_binding_patterns :
    (builtinSignature .repeatBuiltin).map NeedPattern.ofParameter = [.metaRef "step", .bind "count"] := by
  simp [builtinSignature, sequenceBuiltinMetadata?, NeedPattern.ofParameter]

/-- `while` accepts exactly one supplied argument (D2: no variadic `*init`). -/
theorem while_arity (n : Nat) : builtinAcceptsArity .whileBuiltin n = (n == 1) := by
  rcases n with _ | _ | n <;> rfl

/-- `repeat` accepts exactly two supplied arguments. -/
theorem repeat_arity (n : Nat) : builtinAcceptsArity .repeatBuiltin n = (n == 2) := by
  rcases n with _ | _ | _ | n <;> rfl

/-- The arity payload is the exact arity. -/
theorem loop_arity_payload :
    builtinMinimumArity .whileBuiltin = 1 ∧ builtinMinimumArity .repeatBuiltin = 2 := ⟨rfl, rfl⟩

/-- The builtins that bind through the META binder are exactly the two loops. -/
theorem declares_meta_iff (b : Builtin) :
    builtinDeclaresMeta b = true ↔ b = .whileBuiltin ∨ b = .repeatBuiltin := by
  cases b <;> decide

/-- Formula lifting and forwarding read THE builtin signature. -/
theorem lifting_is_the_signature (b : Builtin) : builtinLiftingSignature b = builtinSignature b := rfl

/-- Runtime arity and its error payload read the same signature the META binder uses. -/
theorem arity_is_the_signature (b : Builtin) (n : Nat) :
    builtinAcceptsArity b n = (n == (builtinSignature b).length) ∧
    builtinMinimumArity b = (builtinSignature b).length := ⟨rfl, rfl⟩

/-- The META step position transports its cell (the CALLABLE role); `count` is a value. -/
theorem loop_lifting_roles :
    builtinLiftingSlotRole .whileBuiltin 0 = .callable ∧
    builtinLiftingSlotRole .repeatBuiltin 0 = .callable ∧
    builtinLiftingSlotRole .repeatBuiltin 1 = .value := ⟨rfl, rfl, rfl⟩

/-! ## Inert capture: the binder's `meta step` occurrence -/

/-- **Inert META capture.** On a supplied plan cell, the production binder's `meta step` occurrence
    (the loop builtins' first pattern) binds `step` to ONE fresh Ready adapter cell holding the plan's
    reference and changes nothing else: no VALUE demand, no target, no supply preparation. -/
theorem step_capture_inert (channels : NeedChannels) (address : Nat) (s : EvalState)
    (shape : NeedPlan.CallShape) (h : NeedPlan.shapeAt? s.needs address = some shape) :
    (bindNeedOne channels (.metaRef "step") address [] [] false).runState s =
      (.ok (some [("step", s.needs.size)]),
        { s with needs := s.needs.push (CallReferenceLaws.adapterCell address) }) := by
  rw [CallReferenceLaws.production_meta_binding channels "step" address [] [] false s shape h rfl]
  rfl

/-! ## The captured step's setup -/

/-- The run of `metaLoopCapture` once the adapter reads as plan `a`'s reference and the plan's
    view yields `cells`: the state is `cells` and the step is `NeedPlan.calleeCell a`. -/
theorem metaLoopCapture_run (read : Nat → EvalM CountedResult)
    (view : Nat → EvalM (List NeedSupply.Sourced)) (adapter a k : Nat)
    (cells : List NeedSupply.Sourced) (s s1 s2 : EvalState)
    (hread : (read adapter).runState s = (.ok (.callRef a, k), s1))
    (hview : (view a).runState s1 = (.ok cells, s2)) :
    (metaLoopCapture read view adapter).runState s =
      (match (NeedPlan.calleeCell a).runState s2 with
       | (.ok c, t) => (.ok (c, cells.map Prod.fst), t)
       | (.error e, t) => (.error e, t)) := by
  simp only [metaLoopCapture, bind_run, hread, decodeCallRef, pure_run, hview]
  rcases (NeedPlan.calleeCell a).runState s2 with ⟨_ | c, t⟩ <;> rfl

/-- **CR-9: the initial state IS the plan's view cells** — the original argument cells, never
    re-formed or copied. -/
theorem state_is_view_cells (read : Nat → EvalM CountedResult)
    (view : Nat → EvalM (List NeedSupply.Sourced)) (adapter a k : Nat)
    (cells : List NeedSupply.Sourced) (s s1 s2 t : EvalState) (step : Nat) (state : List Nat)
    (hread : (read adapter).runState s = (.ok (.callRef a, k), s1))
    (hview : (view a).runState s1 = (.ok cells, s2))
    (h : (metaLoopCapture read view adapter).runState s = (.ok (step, state), t)) :
    state = cells.map Prod.fst := by
  rw [metaLoopCapture_run read view adapter a k cells s s1 s2 hread hview] at h
  rcases hc : (NeedPlan.calleeCell a).runState s2 with ⟨_ | c, u⟩ <;> rw [hc] at h <;> cases h
  rfl

/-- **The production view of a prepared plan**: the initial state is the plan's RECORDED supply —
    the cells the captured call's own VALUE, `Invoke()` and `Arguments` share — and nothing runs. -/
theorem state_of_prepared_plan (sp : NeedSupply.SpreadEval) (a : Nat) (s : EvalState)
    (shape : NeedPlan.CallShape) (cell : NeedCell) (cells : List NeedSupply.Sourced)
    (hs : NeedPlan.shapeAt? s.needs a = some shape) (hc : s.needs[a]? = some cell)
    (hp : cell.plan = .prepared (.ok cells)) :
    (NeedPlan.viewCells sp a).runState s = (.ok cells, s) :=
  ArgumentViewLaws.viewCells_prepared sp a s shape cell (.ok cells) hs hc hp

/-- **CR-13: the step IS the plan's canonical callee cell.** Once recorded, the capture's step is
    that cell and establishing it changes nothing. -/
theorem step_is_recorded_callee_cell (read : Nat → EvalM CountedResult)
    (view : Nat → EvalM (List NeedSupply.Sourced)) (adapter a k c : Nat)
    (cells : List NeedSupply.Sourced) (s s1 s2 : EvalState) (cell : NeedCell)
    (hread : (read adapter).runState s = (.ok (.callRef a, k), s1))
    (hview : (view a).runState s1 = (.ok cells, s2))
    (hc : s2.needs[a]? = some cell) (hcallee : cell.callee = some c) :
    (metaLoopCapture read view adapter).runState s = (.ok (c, cells.map Prod.fst), s2) := by
  rw [metaLoopCapture_run read view adapter a k cells s s1 s2 hread hview,
    AlgorithmProjectionLaws.calleeCell_recorded a c s2 cell hc hcallee]

/-- Establishing the step is inert: every cell existing after the view keeps its suspension, VALUE
    state, CALLABLE state and plan supply. -/
theorem step_establishment_inert (a : Nat) (s2 : EvalState) :
    AlgorithmProjectionLaws.HeapCore s2.needs ((NeedPlan.calleeCell a).runState s2).2.needs :=
  AlgorithmProjectionLaws.calleeCell_inert a s2

/-! ## RP-1: the captured supply before the count -/

/-- **RP-1.** `repeat` runs the captured setup (which prepares the captured supply) first and
    demands and validates the count only from the state the setup left. -/
theorem repeat_setup_order {α : Type} (setup : EvalM α) (count : EvalM Int) (s : EvalState) :
    (metaRepeatSetup setup count).runState s =
      (match setup.runState s with
       | (.ok c, s1) =>
         match count.runState s1 with
         | (.ok n, s2) => (.ok (c, n), s2)
         | (.error e, s2) => (.error e, s2)
       | (.error e, s1) => (.error e, s1)) := by
  simp only [metaRepeatSetup, bind_run]
  rcases setup.runState s with ⟨_ | c, s1⟩
  · rfl
  · simp only [pure_run]
    rcases count.runState s1 with ⟨_ | n, s2⟩ <;> rfl

/-- A failing setup (a captured spread's failure) is the loop's failure: the count is never
    demanded. -/
theorem repeat_setup_failure_skips_count {α : Type} (setup : EvalM α) (count : EvalM Int)
    (s s1 : EvalState) (e : Error) (h : setup.runState s = (.error e, s1)) :
    (metaRepeatSetup setup count).runState s = (.error e, s1) := by
  rw [repeat_setup_order, h]

/-! ## OD-1: zero effective initial state -/

/-- An empty captured supply is the ordinary zero-slot state. -/
theorem zero_state_capture (read : Nat → EvalM CountedResult)
    (view : Nat → EvalM (List NeedSupply.Sourced)) (adapter a k : Nat) (s s1 s2 t : EvalState)
    (step : Nat) (state : List Nat)
    (hread : (read adapter).runState s = (.ok (.callRef a, k), s1))
    (hview : (view a).runState s1 = (.ok [], s2))
    (h : (metaLoopCapture read view adapter).runState s = (.ok (step, state), t)) :
    state = [] :=
  state_is_view_cells read view adapter a k [] s s1 s2 t step state hread hview h

/-- A completed zero-slot loop is `()`, emitted count 0 (LOOP-07). -/
theorem zero_state_result : loopResultCounted [] = (.sequenceValue [], 0) := by
  simp [loopResultCounted, loopStateResult, Result.normalize, reCountValueBoundary, Result.valueCount]

/-! ## Plain and dot preparation -/

/-- `X.while` prepares the argument bundle of `while(X)`. -/
theorem dot_while_preparation (receiver : Expr) :
    prepareLexicalDotCallArgs receiver none = [receiver] := rfl

/-- `X.repeat(n)` prepares the argument bundle of `repeat(X, n)`. -/
theorem dot_repeat_preparation (receiver count : Expr) :
    prepareLexicalDotCallArgs receiver (some [count]) = [receiver, count] := rfl

end KatLang.MetaLoopLaws
