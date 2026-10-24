import KatLangArityLaws.PublicRunBridge

open KatLang KatLang.EvaluatorCore

/-!
# R7 executable guards: the fuel index in action

Bounded runs of the TOTAL evaluator core at explicit fuel (`evalFuel`), beside the production
operation (`evalUnbounded`, which every public run uses): the least completing fuel of a
terminating program, the incomplete outcome just below it, the identical outcome AND final state
above it and in production (law 1), a fuel bound that is not divergence (law 5), bounded probes of
a genuinely divergent program, and the incomplete outcome's passage through the memo shell
without completing the cell. These are executable evidence; the laws themselves are the kernel
theorems of `KatLangArityLaws/EvaluatorCore.lean`.
-/

namespace KatLang.EvaluatorCoreGuards

/-- The root run of `runResultM`, with the evaluator core at fuel `n` in place of production:
    the SAME public composition (`PublicRunBridge.runResultWith`, pinned to `runResultM` by
    `rfl`), so this guard copy cannot drift. -/
def runAtFuel (n : Nat) (e : Expr) : Except Error Result × EvalState :=
  (PublicRunBridge.runResultWith (evalFuel n) e).runState EvalState.empty

/-- The production root run with its final state. -/
def runProduction (e : Expr) : Except Error Result × EvalState :=
  (runResultM e).runState EvalState.empty

def incomplete (r : Except Error Result × EvalState) : Bool :=
  r.1.isIncomplete

def same (a b : Except Error Result × EvalState) : Bool :=
  reprStr a == reprStr b

/-- The least fuel ≤ `bound` at which the run completes. -/
def leastFuel (e : Expr) (bound : Nat) : Option Nat :=
  (List.range (bound + 1)).find? (fun n => !incomplete (runAtFuel n e))

/-- `Fact(n)`: a recursive clause family. -/
def factProgram (n : Int) : Expr :=
  .algorithmExpr (algPrivate [] []
    [("Fact", .conditional none [] [⟨.litInt 0, alg [] [] [] [.num 1]⟩,
      ⟨.bind "n", alg [] [] [] [.binary .mul (.param "n") (.call (.resolve "Fact") [.binary .sub (.param "n") (.num 1)])]⟩])]
    [.call (.resolve "Fact") [.num n]])

/-- `Loop(n) = Loop(n)`: a genuinely divergent program (every round re-enters the same call). -/
def loopProgram : Expr :=
  .algorithmExpr (algPrivate [] []
    [("Loop", .conditional none [] [⟨.bind "n", alg [] [] [] [.call (.resolve "Loop") [.param "n"]]⟩])]
    [.call (.resolve "Loop") [.num 1]])

-- Fuel 0 is the everywhere-incomplete answer.
#guard incomplete (runAtFuel 0 (factProgram 3))

-- The incomplete outcome is THE incomplete outcome: `fuelExhausted` with no retained state (no
-- probe wrapped it in a context, no memo kept it).
#guard (runAtFuel 5 (factProgram 6)).1 matches .error .fuelExhausted
#guard reprStr (runAtFuel 5 (factProgram 6)).2 == reprStr EvalState.empty

-- Law 1 and the production bridge: completion at the least fuel, the same outcome AND final
-- state at every larger fuel tried and in production.
def factCompletion : Bool :=
  match leastFuel (factProgram 6) 2000 with
  | none => false
  | some m =>
      m > 0 && incomplete (runAtFuel (m - 1) (factProgram 6)) &&
      ((runAtFuel m (factProgram 6)).1 matches .ok (.atom 720)) &&
      same (runAtFuel m (factProgram 6)) (runAtFuel (m + 1) (factProgram 6)) &&
      same (runAtFuel m (factProgram 6)) (runAtFuel (m + 1000) (factProgram 6)) &&
      same (runAtFuel m (factProgram 6)) (runProduction (factProgram 6))

#guard factCompletion

-- A completed ordinary FAILURE keeps its state and stays that failure under more fuel.
def failureProgram : Expr :=
  .algorithmExpr (algPrivate [] [] [("F", alg ["x"] [] [] [.binary .div (.param "x") (.num 0)])]
    [.call (.resolve "F") [.num 1]])

def failureCompletion : Bool :=
  match leastFuel failureProgram 2000 with
  | none => false
  | some m =>
      (match (runAtFuel m failureProgram).1 with | .error e => !(Except.error e : Except Error Unit).isIncomplete | _ => false) &&
      same (runAtFuel m failureProgram) (runAtFuel (m + 500) failureProgram) &&
      same (runAtFuel m failureProgram) (runProduction failureProgram)

#guard failureCompletion

-- Law 5: exhausting a bound is not divergence — `Fact(12)` is incomplete at a fuel that would
-- complete `Fact(6)` and completes with more.
def boundIsNotDivergence : Bool :=
  match leastFuel (factProgram 6) 2000, leastFuel (factProgram 12) 4000 with
  | some m6, some m12 => m6 < m12 && incomplete (runAtFuel m6 (factProgram 12)) &&
      ((runAtFuel m12 (factProgram 12)).1 matches .ok (.atom 479001600))
  | _, _ => false

#guard boundIsNotDivergence

-- Bounded probes of a divergent program: incomplete at every fuel tried (production would search
-- forever; it is never run here).
#guard incomplete (runAtFuel 100 loopProgram)
#guard incomplete (runAtFuel 1000 loopProgram)
#guard incomplete (runAtFuel 4000 loopProgram)

-- The memo shell never completes a cell on an incomplete computation: the cell stays
-- `evaluating` (here the computation keeps its state, so the cell is visible).
def incompleteNotMemoized : Bool :=
  let s : EvalState := { needs := #[{ suspension := .expression (.num 1) EvalCtx.empty [] }] }
  let keepState : EvalM CountedResult := ⟨fun st => (.error .fuelExhausted, st)⟩
  let r := (NeedDemand.step (fun _ _ _ => keepState) productionPlanRoute (fun _ => keepState) 0).runState s
  (match r.1 with | .error .fuelExhausted => true | _ => false) &&
  (match r.2.needs[0]? with | some c => (match c.state with | .evaluating => true | _ => false) | none => false)

#guard incompleteNotMemoized

/-- The fueled root keeps the public result boundary: a captured call cannot leave the run. -/
def referenceExportProgram : Expr :=
  .algorithmExpr (algPrivate [] []
    [("Id", alg ["x"] [] [] [.param "x"]),
     ("Capture", algWithParameters [{ name := "r", kind := .metaRef }] [] [] [.param "r"])]
    [.call (.resolve "Capture") [.call (.resolve "Id") [.num 7]]])

#guard match (runAtFuel 1000 referenceExportProgram).1 with
  | .error (.typeMismatch message) => message == callReferenceLeavesRunMessage
  | _ => false
#guard same (runAtFuel 1000 referenceExportProgram) (runProduction referenceExportProgram)

/-- CALLABLE incompletion keeps the active marker without publishing a completed failure.
    This is a shell prefix, not a resumable `evalFuel` outcome. -/
def incompleteCallableNotMemoized : Bool :=
  let s : EvalState := { needs := #[{ suspension := .expression (.resolve "F") EvalCtx.empty [] }] }
  let project : NeedSuspension -> EvalM (Option Algorithm) := fun _ =>
    ⟨fun st => (.error .fuelExhausted, st)⟩
  let r := (NeedProjection.step project 0).runState s
  r.1.isIncomplete && (match r.2.needs[0]? with
    | some c => (match c.callable with | .projecting => true | _ => false) &&
        (match c.state with | .suspended => true | _ => false)
    | none => false)

#guard incompleteCallableNotMemoized

/-- Incomplete computed-spread formation publishes no sticky plan supply, even after allocation. -/
def incompletePlanNotMemoized : Bool :=
  let source := Expr.call (.resolve "F") [.sequenceSpread (.num 1)]
  let s : EvalState := { needs := #[{ suspension := .expression source EvalCtx.empty [] }] }
  match NeedPlan.callShape? source EvalCtx.empty [] with
  | none => false
  | some shape =>
      let spread : NeedSupply.SpreadEval := fun _ _ _ => do
        let _ <- readyNeed (.atom 9, 1)
        throw Error.fuelExhausted
      let r := (NeedPlan.prepare spread 0 shape).runState s
      r.1.isIncomplete && r.2.needs.size == 2 &&
        (match r.2.needs[0]? with
        | some c => (match c.plan with | .preparing => true | _ => false)
        | none => false)

#guard incompletePlanNotMemoized

/-- Ordinary failure retains mutations made before failure and memoizes that exact failure.
    Incomplete outcomes pass through both ordinary error-handling interfaces instead. -/
def failureAndIncompleteHandlers : Bool :=
  let failing : EvalM CountedResult := do
    let _ <- readyNeed (.atom 9, 1)
    throw Error.divByZero
  let s : EvalState := { needs := #[{ suspension := .expression (.num 1) EvalCtx.empty [] }] }
  let r := (NeedDemand.step (fun _ _ _ => failing) productionPlanRoute (fun _ => failing) 0).runState s
  (r.1 matches .error .divByZero) && r.2.needs.size == 2 &&
    (match r.2.needs[0]? with
    | some c => (match c.state with | .completed (.error .divByZero) => true | _ => false)
    | none => false) &&
    ((evalAttempt (throw Error.fuelExhausted : EvalM Unit)).runState s).1.isIncomplete &&
    ((tryCatch (throw Error.fuelExhausted : EvalM Unit) (fun _ => pure ())).runState s).1.isIncomplete

#guard failureAndIncompleteHandlers

end KatLang.EvaluatorCoreGuards
