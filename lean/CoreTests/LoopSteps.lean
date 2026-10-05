import KatLang
import CoreTests.Common

namespace KatLangTests
open KatLang (alg algWithParameterPatterns algPrivate runResult Algorithm Error Result)
open KatLang (resolve param num)
open KatLang (Pattern CondBranch)

--------------------------------------------------------------------------------
-- A LOOP STEP IS AN ORDINARY CALLABLE (Q-23, decided October 2026; LOOP-08)
--------------------------------------------------------------------------------
-- Any callable is eligible as a `while`/`repeat` step. When an iteration runs,
-- the current state cells are supplied to it through its ORDINARY invocation
-- (`runNeedStepSlots`): a user algorithm through the one inspecting binder, a
-- clause family through the ordinary family dispatcher
-- (`selectNeedFamilyBranch`: clause order, inspecting patterns, non-match versus
-- failure), a builtin through its ordinary argument roles
-- (`applyBuiltinCountedResolved`), an alias as its target. Only the RECEIVER is
-- the loop's (Q-24): a user body's or the selected clause's ROWS are the next
-- state, and a builtin — which has no written rows — supplies its ONE result
-- value as ONE non-spread row (`()` included). A value with no callable identity
-- is still no step (NEED-06), and a zero-iteration `repeat` never projects its
-- step (LOOP-05).
--
-- C#: `LoopStepCallableDispatchTests` (six routes), the spec cases
-- `loop-step-*`. Law: `loop_step_builtin_result_is_one_row` in
-- `KatLangArityLaws.lean`.

-- Step(0) = 0
-- Step(n) = n - 1
def lsStepAlg : Algorithm :=
  .conditional none [] [
    ⟨ .litInt 0, alg [] [] [] [.num 0] ⟩,
    ⟨ .bind "n", alg [] [] [] [.binary .sub (.param "n") (.num 1)] ⟩
  ]

-- Countdown(0) = 0, false
-- Countdown(n) = n - 1, true
def lsCountdownAlg : Algorithm :=
  .conditional none [] [
    ⟨ .litInt 0, alg [] [] [] [.num 0, .boolLiteral false] ⟩,
    ⟨ .bind "n", alg [] [] [] [.binary .sub (.param "n") (.num 1), .boolLiteral true] ⟩
  ]

-- Gcd(a, 0) = a, 0, false
-- Gcd(a, b) = b, a mod b, true
def lsGcdAlg : Algorithm :=
  .conditional none [] [
    ⟨ .sequenceValue [.bind "a", .litInt 0], alg [] [] [] [.param "a", .num 0, .boolLiteral false] ⟩,
    ⟨ .sequenceValue [.bind "a", .bind "b"],
      alg [] [] [] [.param "b", .binary .mod (.param "a") (.param "b"), .boolLiteral true] ⟩
  ]

-- F(0) = 1
-- F(1) = 2
def lsPartialAlg : Algorithm :=
  .conditional none [] [
    ⟨ .litInt 0, alg [] [] [] [.num 1] ⟩,
    ⟨ .litInt 1, alg [] [] [] [.num 2] ⟩
  ]

-- E(x, x) = 0, 0
-- E(a, b) = a + 1, b
def lsRepeatedAlg : Algorithm :=
  .conditional none [] [
    ⟨ .sequenceValue [.bind "x", .bind "x"], alg [] [] [] [.num 0, .num 0] ⟩,
    ⟨ .sequenceValue [.bind "a", .bind "b"], alg [] [] [] [.binary .add (.param "a") (.num 1), .param "b"] ⟩
  ]

-- Sw((a, b)) = (b, a)
-- Sw([a, b]) = [b, a]
def lsSwapAlg : Algorithm :=
  .conditional none [] [
    ⟨ .sequenceValue [.sequenceValue [.bind "a", .bind "b"]], alg [] [] [] [.capture [.param "b", .param "a"]] ⟩,
    ⟨ .sequenceValue [.listValue [.bind "a", .bind "b"]], alg [] [] [] [.listLiteral [.param "b", .param "a"]] ⟩
  ]

-- Two(0) = 9, 9
-- Two(n) = n, n
def lsTwoRowsAlg : Algorithm :=
  .conditional none [] [
    ⟨ .litInt 0, alg [] [] [] [.num 9, .num 9] ⟩,
    ⟨ .bind "n", alg [] [] [] [.param "n", .param "n"] ⟩
  ]

-- First(x) = 1
-- First(0) = 2       (clause order: the first matching clause wins)
def lsClauseOrderAlg : Algorithm :=
  .conditional none [] [
    ⟨ .bind "x", alg [] [] [] [.num 1] ⟩,
    ⟨ .litInt 0, alg [] [] [] [.num 2] ⟩
  ]

-- C(c) = count(c)
def lsCountWrapperAlg : Algorithm :=
  alg ["c"] [] [] [.call (resolve "count") [.param "c"]]

-- Fi(c) = first(c)
def lsFirstWrapperAlg : Algorithm :=
  alg ["c"] [] [] [.call (resolve "first") [.param "c"]]

private def lsProgram (rows : List KatLang.Expr) : KatLang.Expr :=
  .algorithmExpr (algPrivate [] [] [
    ("Step", lsStepAlg), ("Countdown", lsCountdownAlg), ("Gcd", lsGcdAlg), ("F", lsPartialAlg),
    ("E", lsRepeatedAlg), ("Sw", lsSwapAlg), ("Two", lsTwoRowsAlg), ("Ord", lsClauseOrderAlg),
    ("C", lsCountWrapperAlg), ("Fi", lsFirstWrapperAlg),
    ("A", .alias none [] [] (resolve "Step")), ("B", .alias none [] [] (resolve "A")),
    ("Cnt", .alias none [] [] (resolve "count")), ("Cnt2", .alias none [] [] (resolve "Cnt")),
    -- Run1(f, s) = repeat(f, 1, s)
    ("Run1", alg ["f", "s"] [] [] [.call (resolve "repeat") [.param "f", .num 1, .param "s"]])
  ] rows)

private def lsCall (callee : String) (args : List KatLang.Expr) : KatLang.Expr :=
  .call (resolve callee) args

private def lsRepeat (step : KatLang.Expr) (count : Int) (state : List KatLang.Expr) : KatLang.Expr :=
  .call (resolve "repeat") ([step, .num count] ++ state)

private def lsWhile (step : KatLang.Expr) (state : List KatLang.Expr) : KatLang.Expr :=
  .call (resolve "while") (step :: state)

private def lsOk (rows : List KatLang.Expr) (expected : Result) : Bool :=
  match runResult (lsProgram rows) with
  | .ok value => value == expected
  | _ => false

private def lsFails (rows : List KatLang.Expr) (check : Error -> Bool) : Bool :=
  match runResult (lsProgram rows) with
  | .error e => check e
  | _ => false

-- The canonical family witness: repeat(Step, 2, 3) = Step(Step(3)) = 1, and the
-- base clause is a fixed point (Step.repeat(5, 3) = 0).
#guard lsOk [lsRepeat (resolve "Step") 2 [.num 3], lsCall "Step" [lsCall "Step" [.num 3]],
    .dotMember (resolve "Step") "repeat" (resolve "repeat") (some [.num 5, .num 3])]
  (.sequenceValue [.atom 1, .atom 1, .atom 0])

-- A family `while` step: the selected clause's LAST row is the flag.
#guard lsOk [lsWhile (resolve "Countdown") [.num 3]] (.atom 0)

-- A multi-slot family `while` step: literal matching in the second slot, the
-- selected clause's rows as the next state, the flag last (Gcd(48, 18) = 6).
#guard lsOk [lsWhile (resolve "Gcd") [.num 48, .num 18]] (.sequenceValue [.atom 6, .atom 0])

-- A family non-match is the ordinary NoMatchingBranch, never loop termination,
-- naming the WRITTEN step under its own call frame, exactly as the call `F(5)`.
#guard lsFails [lsRepeat (resolve "F") 1 [.num 5]] (innermostIsNoMatchingBranch "F")
#guard lsFails [lsRepeat (resolve "F") 1 [.num 5]] (hasContext "while evaluating call to F")
#guard lsFails [lsCall "F" [.num 5]] (innermostIsNoMatchingBranch "F")
-- The name is the expression the step's SUPPLY CELL retains (`loopStepName`):
-- transported through the parameter `f`, the cell is still the `F` written at the
-- outer call, so a forwarded step reports exactly as the direct one.
#guard lsFails [lsCall "Run1" [resolve "F", .num 5]] (innermostIsNoMatchingBranch "F")
#guard lsFails [lsCall "Run1" [resolve "F", .num 5]] (hasContext "while evaluating call to F")
#guard lsOk [lsCall "Run1" [resolve "Step", .num 3]] (.atom 2)

-- A wrong state arity is the family's ordinary arity failure.
#guard lsFails [lsRepeat (resolve "Step") 1 [.num 1, .num 2]] (innermostIsArityMismatch 1 2)

-- Clause order is the family's own: the first matching clause wins.
#guard lsOk [lsRepeat (resolve "Ord") 1 [.num 0], lsCall "Ord" [.num 0]] (.sequenceValue [.atom 1, .atom 1])

-- Repeated names bind the INCOMING state only (Q-24): E(0, 2) -> (1, 2) -> (2, 2) -> E(2, 2) = (0, 0).
#guard lsOk [lsRepeat (resolve "E") 3 [.num 0, .num 2]] (.sequenceValue [.atom 0, .atom 0])

-- Structural clauses select by kind through the ordinary dispatcher.
#guard lsOk [lsRepeat (resolve "Sw") 1 [.capture [.num 1, .num 2]], lsRepeat (resolve "Sw") 1 [.listLiteral [.num 1, .num 2]]]
  (.sequenceValue [.sequenceValue [.atom 2, .atom 1], .listValue [.atom 2, .atom 1]])

-- The selected clause's ROWS are the next state, not the call's one value: two
-- rows are two slots, so a second iteration of the one-parameter family is its
-- ordinary arity failure (reading the clause as one value would re-bind the pair).
#guard lsFails [lsRepeat (resolve "Two") 2 [.num 1]] (innermostIsArityMismatch 1 2)

-- A builtin step is its one-row user wrapper: one result value, one slot.
#guard lsOk [lsRepeat (resolve "count") 1 [.listLiteral [.num 1, .num 2]],
    lsRepeat (resolve "C") 1 [.listLiteral [.num 1, .num 2]],
    .dotMember (resolve "count") "repeat" (resolve "repeat") (some [.num 1, .listLiteral [.num 1, .num 2]])]
  (.sequenceValue [.atom 2, .atom 2, .atom 2])

-- A builtin's collection result is ONE state slot (never its element count):
-- take([1, 2, 3], 2) is one slot, so the next `take` call has one argument.
#guard lsOk [lsRepeat (resolve "take") 1 [.listLiteral [.num 1, .num 2, .num 3], .num 2]]
  (.listValue [.atom 1, .atom 2])
#guard lsFails [lsRepeat (resolve "take") 2 [.listLiteral [.num 1, .num 2, .num 3], .num 2]] innermostIsAnyArityMismatch

-- A builtin `()` result is ONE `()` slot: as a `while` step it is the flag and a
-- Boolean is required (a zero-slot reading would be "Bad arity" instead), exactly
-- like its one-row wrapper.
#guard lsFails [lsWhile (resolve "first") [.listLiteral [.emptySequence 0]]] innermostIsAnyTypeMismatch
#guard lsFails [lsWhile (resolve "Fi") [.listLiteral [.emptySequence 0]]] innermostIsAnyTypeMismatch

-- `if` keeps its lazy roles as a step: the unselected branch is never demanded.
#guard lsOk [lsRepeat (resolve "if") 1 [.boolLiteral false, .binary .div (.num 1) (.num 0), .num 2]] (.atom 2)

-- Aliases (and alias chains) are their targets' callables.
#guard lsOk [lsRepeat (resolve "A") 2 [.num 3], lsRepeat (resolve "B") 2 [.num 3],
    lsRepeat (resolve "Cnt") 1 [.listLiteral [.num 1, .num 2]], lsRepeat (resolve "Cnt2") 1 [.listLiteral [.num 1, .num 2]]]
  (.sequenceValue [.atom 1, .atom 1, .atom 2, .atom 2])

-- A value has no callable identity: still no step, and the iteration that needs
-- it reports `notAnAlgorithm` (Q-06), never by demanding the value.
#guard lsFails [lsRepeat (.num 5) 1 [.num 0]] (innermostIsNotAnAlgorithm "repeat step")
#guard lsFails [lsRepeat (.binary .div (.num 1) (.num 0)) 1 [.num 0]] (innermostIsNotAnAlgorithm "repeat step")

-- Zero iterations never project the step: a value and a failing expression alike.
#guard lsOk [lsRepeat (.num 5) 0 [.num 1], lsRepeat (.binary .div (.num 1) (.num 0)) 0 [.num 5],
    lsRepeat (resolve "F") 0 [.num 5]]
  (.sequenceValue [.atom 1, .atom 5, .atom 5])

/-- THE ONE-ITERATION LAW: one iteration over any callable equals the ordinary
    call with the same supply — value for value, and failure for failure down to
    the innermost error's whole payload (a family's no-match names the written
    callee on both routes; only the enclosing frames differ, the loop adding its
    own) (LOOP-07: a one-iteration `repeat` equals the direct call in value and
    emitted count). Families, builtins, aliases and user wrappers alike. -/
def lsOneIterationEqualsTheCall : Bool :=
  let cases : List (String × List KatLang.Expr) := [
    ("Step", [.num 3]), ("Step", [.num 0]), ("Countdown", [.num 2]), ("Gcd", [.num 48, .num 18]),
    ("F", [.num 1]), ("F", [.num 5]), ("E", [.num 2, .num 2]), ("E", [.num 0, .num 2]),
    ("Sw", [.capture [.num 1, .num 2]]), ("Sw", [.num 7]), ("Two", [.num 4]), ("Ord", [.num 0]),
    ("count", [.listLiteral [.num 1, .num 2]]), ("first", [.listLiteral [.emptySequence 0]]),
    ("take", [.listLiteral [.num 1, .num 2, .num 3], .num 2]), ("take", [.num 1]),
    ("if", [.boolLiteral true, .num 1, .num 2]), ("if", [.num 5, .num 1, .num 2]),
    ("A", [.num 3]), ("Cnt", [.listLiteral [.num 4]]), ("C", [.listLiteral [.num 1]]),
    ("Fi", [.listLiteral [.num 7, .num 8]])
  ]
  cases.all fun (callee, supply) =>
    match runResult (lsProgram [lsRepeat (resolve callee) 1 supply]),
          runResult (lsProgram [lsCall callee supply]) with
    | .ok a, .ok b => a == b
    | .error a, .error b => (repr (innermost a)).pretty == (repr (innermost b)).pretty
    | _, _ => false
where
  innermost : Error -> Error
    | .withContext _ inner => innermost inner
    | e => e

#guard lsOneIterationEqualsTheCall

end KatLangTests
