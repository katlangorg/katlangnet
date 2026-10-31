import KatLang

open KatLang

/-!
# The `tick()` primitive: laws of the run-local counter

`tick()` is the zero-argument diagnostic builtin. Its ONE piece of language state is
`EvalState.tickCounter` (zero in `EvalState.empty`, the state every run starts from), advanced only
by `runTick`, the `.tickBuiltin` arm of `EvalBody.applyBuiltinCounted`. These laws state, over the
actual definitions:

* a successful execution returns the INCREMENTED counter as one number and advances it by exactly
  one, touching nothing else (`runTick_advances`);
* at the checked limit `tickCounterLimit` (2^63 - 1, C#'s `long.MaxValue`) the execution is the
  deterministic `illegalInEval` refusal and the state is unchanged (`runTick_exhausted`), so no two
  executions of one run ever return the same value (`runTick_strictly_increases`);
* a bare VALUE demand of the builtin is the invocation-required refusal and changes no state
  (`tick_value_demand_is_refused_without_effect`);
* the dispatch: the accepted zero-argument application IS `runTick`, and every supplied argument is
  the ordinary arity rejection, raised before any argument is demanded and without advancing the
  counter (`apply_tick_without_arguments_runs_the_primitive`,
  `apply_tick_with_arguments_is_the_arity_rejection`).

The laws are about the SERIAL Lean evaluator. That C# advances the counter at the same logical points
on every route (sync, async twin, planned loops, the fused pipeline), keeps it per run, observes
cancellation and terminal resource failures first, and stays exactly-once under shared demands and
async retries is C# evidence (`TickBuiltinTests`), not a consequence of these theorems. Whole-program
behavior is executed by `KatLangArityLaws/TickGuards.lean` and the `tick-*` language-spec cases.
-/

namespace KatLang.TickLaws

/-- A successful execution: the new counter value, as one number (emitted count 1), and the counter
    advanced by exactly one — every other state field unchanged. -/
theorem runTick_advances (s : EvalState) (h : s.tickCounter < tickCounterLimit) :
    runTick.runState s
      = (.ok (Result.atom (Int.ofNat (s.tickCounter + 1)), 1),
         { s with tickCounter := s.tickCounter + 1 }) := by
  have hnot : ¬ s.tickCounter ≥ tickCounterLimit := Nat.not_le.mpr h
  show (if s.tickCounter ≥ tickCounterLimit then
      (throw (Error.illegalInEval tickExhaustedMessage) : EvalM Unit) >>= fun _ =>
        modify (fun s => { s with tickCounter := s.tickCounter + 1 }) >>= fun _ =>
          (pure (Result.atom (Int.ofNat (s.tickCounter + 1)), 1) : EvalM CountedResult)
    else
      modify (fun s => { s with tickCounter := s.tickCounter + 1 }) >>= fun _ =>
        (pure (Result.atom (Int.ofNat (s.tickCounter + 1)), 1) : EvalM CountedResult)).runState s = _
  rw [if_neg hnot]
  rfl

/-- At the checked limit the primitive is the deterministic domain refusal and the state is
    unchanged: the counter never wraps, rounds or saturates into a duplicate value. -/
theorem runTick_exhausted (s : EvalState) (h : tickCounterLimit ≤ s.tickCounter) :
    runTick.runState s = (.error (Error.illegalInEval tickExhaustedMessage), s) := by
  show (if s.tickCounter ≥ tickCounterLimit then
      (throw (Error.illegalInEval tickExhaustedMessage) : EvalM Unit) >>= fun _ =>
        modify (fun s => { s with tickCounter := s.tickCounter + 1 }) >>= fun _ =>
          (pure (Result.atom (Int.ofNat (s.tickCounter + 1)), 1) : EvalM CountedResult)
    else
      modify (fun s => { s with tickCounter := s.tickCounter + 1 }) >>= fun _ =>
        (pure (Result.atom (Int.ofNat (s.tickCounter + 1)), 1) : EvalM CountedResult)).runState s = _
  rw [if_pos h]
  rfl

/-- Successive successful executions return strictly increasing values: the value returned is the
    counter after the execution, which only ever grows. -/
theorem runTick_strictly_increases (s : EvalState) (h : s.tickCounter < tickCounterLimit) :
    ((runTick.runState s).2).tickCounter = s.tickCounter + 1 := by
  rw [runTick_advances s h]

/-- Every run starts with the counter at zero. -/
theorem tick_counter_starts_at_zero : EvalState.empty.tickCounter = 0 := rfl

/-- A bare VALUE demand of `tick` is refused as invocation-required and changes no state. -/
theorem tick_value_demand_is_refused_without_effect (s : EvalState) :
    (evalBuiltinValueCounted .tickBuiltin).runState s
      = (.error (Error.illegalInEval (builtinInvocationRequiredMessage .tickBuiltin)), s) := rfl

/-- Every other builtin keeps the very arity rejection its empty call reports. -/
theorem nonzero_arity_builtin_value_demand_is_its_arity_error (b : Builtin) (h : b ≠ .tickBuiltin)
    (s : EvalState) :
    (evalBuiltinValueCounted b).runState s = (.error (builtinArityError b 0), s) := by
  cases b <;> first | exact absurd rfl h | rfl

/-- The accepted zero-argument application of `tick` IS one execution of the primitive. -/
theorem apply_tick_without_arguments_runs_the_primitive (rec : EvalRec) (ctx : EvalCtx) (env : ValEnv) :
    EvalBody.applyBuiltinCounted rec .tickBuiltin [] ctx env = withNestedMissingOutput runTick := rfl

/-- Any supplied argument is the ordinary arity rejection, before anything is demanded: the state —
    the counter included — is unchanged. -/
theorem apply_tick_with_arguments_is_the_arity_rejection (rec : EvalRec) (arg : ResolvedArgumentAlgorithm)
    (rest : List ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) :
    EvalBody.applyBuiltinCounted rec .tickBuiltin (arg :: rest) ctx env
      = withNestedMissingOutput (.error (builtinArityError .tickBuiltin (rest.length + 1))) := rfl

end KatLang.TickLaws
