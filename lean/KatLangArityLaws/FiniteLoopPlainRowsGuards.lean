import KatLangArityLaws.FiniteLoopSurface
import KatLangArityLaws.EvaluatorInstallation

open KatLang KatLang.EvaluatorCore KatLang.WhileRoundProduction KatLang.FiniteLoop KatLang.FiniteLoopSurface

/-!
# `PlainRows`: where FG-L1 needs it, where it holds, and a state where it fails (issue #204)

FG-L1's one-round theorems (`FiniteLoop.repeat_one_round`, and through it `count_one_user`,
`count_one_family`, `repeat_builtin_count_one` and the value theorems of `FiniteLoopSurface.lean`)
assume `PlainRows`: the slots a step round emitted are not BARE deferred list items. The premise is
consumed at ONE place, the loop's final read of the Ready cells that hold those slots
(`materialize_ready` through `demand_ready`): a Ready cell holding a plain slot completes with that
slot, while a Ready cell holding a deferred item is an ALIAS of the item's position and completes
with the POSITION's outcome (`demand_ready_alias`). Without the premise the round is still the real
composition (`repeat_one_round_materialized`, no premise on the slots).

## Kernel-checked results here

* `host_round`, `host_round_not_plain`: over a HOST-BUILT heap containing a completed cell whose
  VALUE is a bare deferred item, the `if` step round emits that item,
  so `PlainRows` is not a property of every round from every state. Reachability of this heap from
  a closed program is not assumed.
* `host_repeat`, `one_round_needs_plainRows`, `one_round_without_plainRows_is_false`: from that state
  every other premise of `repeat_one_round` holds and its conclusion is FALSE: the loop's state cell
  is an alias, its final read is the position's value `5`, not the item. The premise is necessary.

Discharges (`FiniteLoopSurface.lean` § 5): `PlainRows` holds from every state for every user step
or clause family whose rows are PLAIN ROWS (scalar rows and list literals: `user_plainRows`,
`family_plainRows`); for a builtin step it IS the premise that the ordinary application's result is
not a bare position (`plainRows_builtin`). Plainness of every slot emitted in a closed run from
`EvalState.empty` remains open.

## Executable evidence on production terms (`#guard`, not theorems)

A step whose LIST PATTERN binds deferred positions, over the first-round supply the production
supply formation allocates (`supplyNeed`), run by the production `runNeedStepSlots`,
`repeatAfterSetup` and `whileAfterSetup`. The binder allocates ONE Ready alias cell per bound
position (`.ready (.deferred position, _)`); a row reading a bound name reads the position through
it, so the emitted slots are VALUES, never bare items — directly (`P([x, y]) = x, y`), through a
callee's value-only parameter cell (`Q([x]) = Id(x)`) and through alias chains built by earlier
rounds (`Sw([x, y]) = [y, x]` under `repeat(_, 2)`, `Wh` under `while`). Controls: written constants
are stored as values, so the same step allocates no alias (`P([1, 2])`); a nested list keeps its
inner positions deferred, and its slot is a LIST holding a deferred item — plain, though not
concrete (`N([x]) = x` over `[[1 + 0]]`). C#: a loop's row value is a `Result`, which has no position
variant (`Evaluator.InvokeLoopStepSupply`), and the binder's positional arm binds a fresh
`StoredPosition` cell, the alias (`Evaluator.PositionCell`): the C# reading of `PlainRows` holds by
typing.
-/

namespace KatLang.FiniteLoopPlainRowsGuards

/-! ## 1. The host-built heap: a completed bare deferred item -/

/-- Position 0 holds the completed value `5`, cell 1 the completed condition `true`, and cell 2 a
    completed VALUE that is the BARE deferred item over position 0. -/
def hostState : EvalState :=
  { needs := #[completedCell (.atom 5), completedCell (.bool true), completedCell (.deferred 0)] }

/-- `if(cell 1, cell 2, cell 0)` as a loop state. -/
def hostCells : List NeedSupply.Sourced := [(1, none), (2, none), (0, none)]

/-- The retained step: the builtin `if`, with no cell of its own. -/
def hostStep : ResolvedArgumentAlgorithm := { algorithm := .builtin .ifBuiltin }

theorem host_demand (a : Nat) (v : Result) (h : hostState.needs[a]? = some (completedCell v)) :
    (demandNeedRecursive a).runState hostState = (.ok (v, Result.valueCount v), hostState) :=
  demand_completed a hostState _ _ h rfl nofun

theorem host_argument (a : Nat) (v : Result) (h : hostState.needs[a]? = some (completedCell v)) :
    (evalUnbounded (.evalArgumentValueCounted (stepCellArgument (a, none)) EvalCtx.empty [])).runState hostState =
      (.ok (v, Result.valueCount v), hostState) := by
  have hstep : ∀ rec : EvalRec,
      evalStep rec (.evalArgumentValueCounted (stepCellArgument (a, none)) EvalCtx.empty []) =
        (fun rec : EvalRec => rec (.demandNeedRecursive a)) rec :=
    fun rec => by
      show EvalBody.evalArgumentValueCounted rec (stepCellArgument (a, none)) EvalCtx.empty [] = rec (.demandNeedRecursive a)
      exact EvaluatorInstallation.argument_value_of_a_cell rec _ _ _ a rfl
  have hc : ProductionCompletes ((fun rec : EvalRec => rec (.demandNeedRecursive a)) evalUnbounded) hostState := by
    show ((demandNeedRecursive a).runState hostState).1 ≠ _
    rw [host_demand a v h]; nofun
  rw [production_eq_of_finite _ _ hstep (finite_call _) hostState hc]
  exact host_demand a v h

theorem host_condition :
    (evalArgumentValue (stepCellArgument (1, none)) EvalCtx.empty []).runState hostState =
      (.ok (.bool true), hostState) := by
  show (evalArgumentValueCounted (stepCellArgument (1, none)) EvalCtx.empty [] >>= fun out =>
    pure out.fst).runState hostState = _
  rw [EvalM.bind_runState]
  rw [show evalArgumentValueCounted (stepCellArgument (1, none)) EvalCtx.empty [] =
    evalUnbounded (.evalArgumentValueCounted (stepCellArgument (1, none)) EvalCtx.empty []) from rfl,
    host_argument 1 (.bool true) rfl]
  rfl

/-- The `if` application selects cell 2 and returns its completed VALUE: the bare item. -/
theorem host_application :
    (applyBuiltinCountedResolved .ifBuiltin (stepArguments hostCells) EvalCtx.empty []).runState hostState =
      (.ok (.deferred 0, 1), hostState) :=
  if_application_value (stepCellArgument (1, none)) (stepCellArgument (2, none)) (stepCellArgument (0, none))
    EvalCtx.empty [] hostState hostState hostState true (.deferred 0, 1) host_condition
    (host_argument 2 (.deferred 0) rfl)

/-- **The step round emits a bare deferred item.** -/
theorem host_round :
    (runNeedStepSlots (.builtin .ifBuiltin) EvalCtx.empty [] hostCells "S").runState hostState =
      (.ok [.deferred 0], hostState) := by
  rw [builtin_step_value .ifBuiltin EvalCtx.empty [] hostCells "S" hostState (.ok (.deferred 0, 1)) hostState nofun
    host_application]
  rfl

/-- **`PlainRows` is not a property of every round from every state.** -/
theorem host_round_not_plain :
    ¬ PlainRows ((runNeedStepSlots (.builtin .ifBuiltin) EvalCtx.empty [] hostCells "S").runState hostState) := by
  rw [host_round]
  intro h
  exact h [.deferred 0] hostState rfl (.deferred 0) (List.mem_singleton_self _) 0 rfl

/-! ## 2. Without the premise the one-round equation is false -/

theorem host_invoke : (invokeNeed hostStep).runState hostState = (.ok (some (.builtin .ifBuiltin)), hostState) :=
  production_of_answer_free (.invokeNeed hostStep) hostState _ (fun _ => rfl) nofun

/-- The loop's state after the round: one Ready cell, at address 3, holding the bare item. -/
abbrev hostPushed : EvalState := pushReady hostState [.deferred 0]

/-- The final heap: that cell completed with the POSITION's value. -/
abbrev hostFinal : EvalState := { hostPushed with needs := evaluatedAt hostPushed.needs 3 (.atom 5, 1) }

/-- The loop's final read of its state cell: the cell is an ALIAS of position 0, so it reads `5`. -/
theorem host_materialize :
    (materialize (readyAddrs hostState.needs.size [.deferred 0])).runState hostPushed =
      (.ok [.atom 5], hostFinal) := by
  have halias := demand_ready_alias_completed 3 0 1 hostPushed (readyCell (.deferred 0))
    (completedCell (.atom 5)) (.atom 5, 1) rfl rfl rfl (by decide) rfl rfl
  show ([3].mapM (fun address => Prod.fst <$> demandNeedRecursive address)).runState hostPushed = _
  rw [KatLang.NeedControl.Schedule.mapM_schedule]
  simp only [KatLang.NeedControl.Schedule.schedule]
  have hm : (Prod.fst <$> demandNeedRecursive 3).runState hostPushed = _ :=
    KatLang.NeedControl.Collector.map_run _ _ _
  rw [hm, halias]

/-- **The real one-round `repeat` from the host-built heap**: `5`, read through the alias. -/
theorem host_repeat :
    (repeatAfterSetup evalUnbounded hostStep EvalCtx.empty [] "S" 1 hostCells).runState hostState =
      (.ok (loopResultCounted [.atom 5]), hostFinal) := by
  rw [repeat_one_round_materialized hostStep EvalCtx.empty [] "S" hostCells hostState hostState _ host_invoke,
    host_round]
  dsimp only
  rw [host_materialize]

/-- **`repeat_one_round` WITHOUT `PlainRows` IS FALSE**: from the host-built heap every other
    premise holds (`host_invoke`), and the equation states the slot where the loop reads the
    position. -/
theorem one_round_needs_plainRows :
    (repeatAfterSetup evalUnbounded hostStep EvalCtx.empty [] "S" 1 hostCells).runState hostState ≠
      oneRoundOutcome ((runNeedStepSlots (.builtin .ifBuiltin) EvalCtx.empty [] hostCells "S").runState hostState) := by
  rw [host_repeat, host_round]
  intro h
  injection h with h1
  injection h1 with h2
  injection h2 with h3
  simp [loopStateResult, Result.normalize] at h3

/-- The universal form: the premise-free one-round equation is not a theorem. -/
theorem one_round_without_plainRows_is_false :
    ¬ ∀ (step : ResolvedArgumentAlgorithm) (ctx : EvalCtx) (env : ValEnv) (name : String)
      (cells : List NeedSupply.Sourced) (s s₁ : EvalState) (alg : Algorithm),
      (invokeNeed step).runState s = (.ok (some alg), s₁) →
      (repeatAfterSetup evalUnbounded step ctx env name 1 cells).runState s =
        oneRoundOutcome ((runNeedStepSlots alg ctx env cells name).runState s₁) :=
  fun h => one_round_needs_plainRows (h hostStep EvalCtx.empty [] "S" hostCells hostState hostState _ host_invoke)

-- The two cells the distinction is about, executed: the item as a completed VALUE (cell 2, which the
-- step returned as its row) and the Ready ALIAS the loop allocated for that row (cell 3, which the
-- loop read back as the position's value).
#guard reprStr (hostState.needs[2]?.map (·.state)) ==
  reprStr (some (NeedState.completed (.ok (Result.deferred 0, 1))))
#guard reprStr (hostFinal.needs[3]?.map (fun c => (c.suspension, c.state))) ==
  reprStr (some (NeedSuspension.ready (Result.deferred 0, 1), NeedState.completed (.ok (Result.atom 5, 1))))
#guard reprStr ((repeatAfterSetup evalUnbounded hostStep EvalCtx.empty [] "S" 1 hostCells).runState hostState).1 ==
  reprStr (Except.ok (loopResultCounted [.atom 5]) : Except Error CountedResult)

-- Both receivers dispatch through runNeedStepWith. A builtin contributes one atomic slot:
-- repeat exposes it (host_round), but while must use that same slot as its Boolean flag.
#guard match (runNeedWhileRound (.builtin .ifBuiltin) EvalCtx.empty [] hostCells "S").runState hostState with
  | (.error (.withContext "while evaluating call to S" (.typeMismatch _)), _) => true
  | _ => false

-- A user body, also the reader of a selected family clause, can have a separate transition
-- row. On the same host heap the true flag admits that row unchanged in a while round.
#guard match (runNeedWhileRound (alg ["v"] [] [] [.param "v", .boolLiteral true])
    EvalCtx.empty [] [(2, none)] "S").runState hostState with
  | (.ok (some [.deferred 0]), _) => true
  | _ => false

/-! ## 3. Production routes over deferred positions: the slots are values -/

def cap (n : Ident) : ParameterPattern := .capture { name := n }
def callN (f : Ident) (args : List Expr) : Expr := .call (.resolve f) args
/-- `n + 0`: an element that is not a written constant, so a list literal defers it. -/
def lazyNum (n : Int) : Expr := .binary .add (.num n) (.num 0)

/-- `P([x, y]) = x, y`. -/
def pStep : Algorithm := algWithParameterPatterns [.listValue [cap "x", cap "y"]] [] [] [.param "x", .param "y"]
/-- `Id(v) = v`. -/
def idAlg : Algorithm := alg ["v"] [] [] [.param "v"]
/-- `Q([x]) = Id(x)`, with `Id` its own property: the position travels into `Id`'s parameter cell. -/
def qStep : Algorithm :=
  .mk none [.listValue [cap "x"]] [] (propsPrivate [("Id", idAlg)]) [callN "Id" [.param "x"]]
/-- `N([x]) = x`. -/
def nStep : Algorithm := algWithParameterPatterns [.listValue [cap "x"]] [] [] [.param "x"]
/-- `Sw([x, y]) = [y, x]`: its next state is a list whose positions are the bound names' cells. -/
def swStep : Algorithm :=
  algWithParameterPatterns [.listValue [cap "x", cap "y"]] [] [] [.listLiteral [.param "y", .param "x"]]
/-- `Wh([x, y], n) = [y, x], n - 1, n > 0`. -/
def whStep : Algorithm :=
  algWithParameterPatterns [.listValue [cap "x", cap "y"], cap "n"] [] []
    [.listLiteral [.param "y", .param "x"], .binary .sub (.param "n") (.num 1),
     .comparison (.param "n") [⟨.gt, .num 0⟩]]

def stepCtx : EvalCtx := { callStack := [preludeAlg] }
def stepArg (a : Algorithm) : ResolvedArgumentAlgorithm := { algorithm := a }

/-- The first round's state: one supplied cell per written argument, allocated by the production
    supply formation (`supplyNeed`), each with its written slot. -/
def firstState (args : List Expr) : List NeedSupply.Sourced × EvalState :=
  match (args.mapM (fun e => do let c ← supplyNeed e stepCtx []; pure (c, some e))).runState EvalState.empty with
  | (.ok cells, s) => (cells, s)
  | (.error _, s) => ([], s)

def viaStep (a : Algorithm) (args : List Expr) : Except Error (List Result) × EvalState :=
  let (cells, s) := firstState args
  (runNeedStepSlots a stepCtx [] cells "S").runState s

def viaRepeat (a : Algorithm) (args : List Expr) (n : Nat) : Except Error CountedResult × EvalState :=
  let (cells, s) := firstState args
  (repeatAfterSetup evalUnbounded (stepArg a) stepCtx [] "S" n cells).runState s

def viaWhile (a : Algorithm) (args : List Expr) : Except Error CountedResult × EvalState :=
  let (cells, s) := firstState args
  (whileAfterSetup evalUnbounded (stepArg a) stepCtx [] "S" cells).runState s

def isBare : Result → Bool
  | .deferred _ => true
  | _ => false

/-- The emitted slots: none is a bare deferred item. -/
def plainSlots : Except Error (List Result) → Bool
  | .ok ys => !ys.any isBare
  | .error _ => false

/-- The Ready ALIAS cells of a heap: Ready cells holding a deferred item, with their state. -/
def aliases (s : EvalState) : List (Nat × Nat × NeedState) :=
  s.needs.toList.zipIdx.filterMap fun (c, i) =>
    match c.suspension with
    | .ready (.deferred position, _) => some (i, position, c.state)
    | _ => none

/-- Every alias cell of the heap points at a position, never at itself. -/
def aliasesBelow (s : EvalState) : Bool := (aliases s).all fun (i, position, _) => position < i

/-- At least one Ready alias points to another Ready alias. -/
def hasAliasChain (s : EvalState) : Bool :=
  let links := aliases s
  links.any fun (_, target, _) => links.any fun (address, _, _) => address == target

-- Deferred positions bound by a list pattern: the slots are the positions' VALUES; the binder's two
-- aliases (cells 3 and 4, over positions 1 and 2) completed with those values.
#guard reprStr (viaStep pStep [.listLiteral [lazyNum 1, lazyNum 2]]).1 == reprStr (Except.ok [Result.atom 1, .atom 2] : Except Error (List Result))
#guard reprStr (aliases (viaStep pStep [.listLiteral [lazyNum 1, lazyNum 2]]).2) ==
  reprStr [(3, 1, NeedState.completed (.ok (Result.atom 1, 1))), (4, 2, NeedState.completed (.ok (Result.atom 2, 1)))]
-- Control: written constants are stored as values, so the same step allocates no alias.
#guard reprStr (viaStep pStep [.listLiteral [.num 1, .num 2]]).1 == reprStr (Except.ok [Result.atom 1, .atom 2] : Except Error (List Result))
#guard (aliases (viaStep pStep [.listLiteral [.num 1, .num 2]]).2).isEmpty
-- Through a value-only parameter cell: `Id`'s parameter is the alias itself, read for its value.
#guard reprStr (viaStep qStep [.listLiteral [lazyNum 1]]).1 == reprStr (Except.ok [Result.atom 1] : Except Error (List Result))
#guard (aliases (viaStep qStep [.listLiteral [lazyNum 1]]).2).length == 1
-- Nested list: the slot is a LIST still holding a deferred position — plain, though not concrete.
#guard match (viaStep nStep [.listLiteral [.listLiteral [lazyNum 1]]]).1 with
  | .ok [.listValue [.deferred _]] => true
  | _ => false
#guard plainSlots (viaStep nStep [.listLiteral [.listLiteral [lazyNum 1]]]).1
-- Every production slot above is plain.
#guard plainSlots (viaStep pStep [.listLiteral [lazyNum 1, lazyNum 2]]).1
#guard plainSlots (viaStep qStep [.listLiteral [lazyNum 1]]).1
#guard plainSlots (viaStep swStep [.listLiteral [lazyNum 1, lazyNum 2]]).1

-- Alias CHAINS across rounds: round 2 binds the positions of the list round 1 built, which are the
-- round-1 aliases; nothing is read, the loop value is a lazy list, and every alias points below
-- itself (an alias of an alias of a position).
#guard match (viaRepeat swStep [.listLiteral [lazyNum 1, lazyNum 2]] 2).1 with
  | .ok (.listValue [.deferred _, .deferred _], 1) => true
  | _ => false
#guard (aliases (viaRepeat swStep [.listLiteral [lazyNum 1, lazyNum 2]] 2).2).length == 4
#guard aliasesBelow (viaRepeat swStep [.listLiteral [lazyNum 1, lazyNum 2]] 2).2
#guard hasAliasChain (viaRepeat swStep [.listLiteral [lazyNum 1, lazyNum 2]] 2).2
#guard (aliases (viaRepeat swStep [.listLiteral [lazyNum 1, lazyNum 2]] 2).2).all fun (_, _, st) =>
  match st with
  | .suspended => true
  | _ => false
-- One round of `P`: the loop value is the row supply, read through the state cells.
#guard reprStr (viaRepeat pStep [.listLiteral [lazyNum 1, lazyNum 2]] 1).1 ==
  reprStr (Except.ok (Result.sequenceValue [.atom 1, .atom 2], 1) : Except Error CountedResult)
-- `while` reads its flag first: two accepted swaps, then a false round; aliases only below themselves.
#guard match (viaWhile whStep [.listLiteral [lazyNum 1, lazyNum 2], .num 2]).1 with
  | .ok (.sequenceValue [.listValue [.deferred _, .deferred _], .atom 0], 1) => true
  | _ => false
#guard aliasesBelow (viaWhile whStep [.listLiteral [lazyNum 1, lazyNum 2], .num 2]).2
#guard hasAliasChain (viaWhile whStep [.listLiteral [lazyNum 1, lazyNum 2], .num 2]).2

/-! ## 4. Whole programs: the loop against the ordinary call, read whole by the run -/

def decls : List (Ident × Algorithm) :=
  [("P", pStep), ("Q", qStep), ("N", nStep), ("Sw", swStep), ("Wh", whStep)]

def run (rows : List Expr) : Except Error Result := runResult (.algorithmExpr (algPrivate [] [] decls rows))

def obs (r : Except Error Result) : String :=
  match r with
  | .ok v => reprStr v
  | .error _ => "error"

def sameAsCall (step : Expr) : Bool :=
  match run [callN "repeat" [step, .num 1]], run [step] with
  | .ok a, .ok b => reprStr a == reprStr b
  | _, _ => false

#guard sameAsCall (callN "P" [.listLiteral [lazyNum 1, lazyNum 2]])
#guard sameAsCall (callN "P" [.listLiteral [.num 1, .num 2]])
#guard sameAsCall (callN "Q" [.listLiteral [lazyNum 1]])
#guard sameAsCall (callN "N" [.listLiteral [.listLiteral [lazyNum 1]]])
#guard sameAsCall (callN "Sw" [.listLiteral [lazyNum 1, lazyNum 2]])
#guard obs (run [callN "repeat" [callN "Sw" [.listLiteral [lazyNum 1, lazyNum 2]], .num 3]]) ==
  reprStr (Result.listValue [.atom 2, .atom 1])
#guard obs (run [callN "while" [callN "Wh" [.listLiteral [lazyNum 1, lazyNum 2], .num 3]]]) ==
  reprStr (Result.sequenceValue [.listValue [.atom 2, .atom 1], .atom 0])
-- A position that is never read is never evaluated, however many rounds forward it.
#guard obs (run [.dotCall (callN "repeat" [callN "Sw" [.listLiteral [.binary .div (.num 1) (.num 0), lazyNum 2]], .num 2])
    "count" none]) == reprStr (Result.atom 2)

/-! ## Axiom audit -/

/-- info: 'KatLang.FiniteLoopPlainRowsGuards.one_round_without_plainRows_is_false' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KatLang.FiniteLoopPlainRowsGuards.one_round_without_plainRows_is_false

/-- info: 'KatLang.FiniteLoopPlainRowsGuards.host_round_not_plain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KatLang.FiniteLoopPlainRowsGuards.host_round_not_plain

end KatLang.FiniteLoopPlainRowsGuards
