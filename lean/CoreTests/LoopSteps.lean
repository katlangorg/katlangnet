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
    -- Run1(f, s) = repeat(f(s), 1); Run0(f, s) = repeat(f(s), 0)
    ("Run1", alg ["f", "s"] [] [] [.call (resolve "repeat") [.call (.param "f") [.param "s"], .num 1]]),
    ("Run0", alg ["f", "s"] [] [] [.call (resolve "repeat") [.call (.param "f") [.param "s"], .num 0]]),
    -- Inc(x) = x + 1; RunCount(v) = repeat(count(v), 1)
    ("Inc", alg ["x"] [] [] [.binary .add (.param "x") (.num 1)]),
    ("RunCount", alg ["v"] [] [] [.call (resolve "repeat") [.call (resolve "count") [.param "v"], .num 1]])
  ] rows)

private def lsCall (callee : String) (args : List KatLang.Expr) : KatLang.Expr :=
  .call (resolve callee) args

/-- `repeat(step(state…), count)` (META-S3-3): the loop captures the written step call. -/
private def lsRepeat (step : KatLang.Expr) (count : Int) (state : List KatLang.Expr) : KatLang.Expr :=
  .call (resolve "repeat") [.call step state, .num count]

/-- `while(step(state…))` (META-S3-3). -/
private def lsWhile (step : KatLang.Expr) (state : List KatLang.Expr) : KatLang.Expr :=
  .call (resolve "while") [.call step state]

private def lsOk (rows : List KatLang.Expr) (expected : Result) : Bool :=
  match runResult (lsProgram rows) with
  | .ok value => value == expected
  | _ => false

private def lsFails (rows : List KatLang.Expr) (check : Error -> Bool) : Bool :=
  match runResult (lsProgram rows) with
  | .error e => check e
  | _ => false

-- The canonical family witness: repeat(Step(3), 2) = Step(Step(3)) = 1, and the
-- base clause is a fixed point (Step(3).repeat(5) = 0).
#guard lsOk [lsRepeat (resolve "Step") 2 [.num 3], lsCall "Step" [lsCall "Step" [.num 3]],
    .dotMember (.call (resolve "Step") [.num 3]) "repeat" (resolve "repeat") (some [.num 5])]
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
    .dotMember (.call (resolve "count") [.listLiteral [.num 1, .num 2]]) "repeat" (resolve "repeat") (some [.num 1])]
  (.sequenceValue [.atom 2, .atom 2, .atom 2])

-- A builtin's collection result is ONE state slot (never its element count):
-- take([1, 2, 3], 2) is one slot, so the next `take` call has one argument.
#guard lsOk [lsRepeat (resolve "take") 1 [.listLiteral [.num 1, .num 2, .num 3], .num 2]]
  (.listValue [.atom 1, .atom 2])
#guard lsFails [lsRepeat (resolve "take") 2 [.listLiteral [.num 1, .num 2, .num 3], .num 2]] (innermostIsArityMismatch 2 1)

-- A builtin `()` result is ONE `()` slot: as a `while` step it is the flag and a
-- Boolean is required (a zero-slot reading would be "Bad arity" instead), exactly
-- like its one-row wrapper.
private def lsEmptyFlagRequired : Error -> Bool :=
  innermostIsBooleanRequired "while continuation flag (the step's last output)"
    "a sequence value with 0 sequence elements: ()"
#guard lsFails [lsWhile (resolve "first") [.listLiteral [.emptySequence 0]]] lsEmptyFlagRequired
#guard lsFails [lsWhile (resolve "Fi") [.listLiteral [.emptySequence 0]]] lsEmptyFlagRequired

-- `if` keeps its lazy roles as a step: the unselected branch is never demanded.
#guard lsOk [lsRepeat (resolve "if") 1 [.boolLiteral false, .binary .div (.num 1) (.num 0), .num 2]] (.atom 2)

-- Aliases (and alias chains) are their targets' callables.
#guard lsOk [lsRepeat (resolve "A") 2 [.num 3], lsRepeat (resolve "B") 2 [.num 3],
    lsRepeat (resolve "Cnt") 1 [.listLiteral [.num 1, .num 2]], lsRepeat (resolve "Cnt2") 1 [.listLiteral [.num 1, .num 2]]]
  (.sequenceValue [.atom 1, .atom 1, .atom 2, .atom 2])

-- A value has no callable identity: supplied as the captured call's callee (through `f`),
-- still no step, and the iteration that needs it reports `notAnAlgorithm` (Q-06), never by
-- demanding the value. Written as the META argument's callee itself, the call is no plan,
-- so META refuses it first (META-S3-3).
#guard lsFails [lsCall "Run1" [.num 5, .num 0]] (innermostIsNotAnAlgorithm "repeat step")
#guard lsFails [lsCall "Run1" [.binary .div (.num 1) (.num 0), .num 0]] (innermostIsNotAnAlgorithm "repeat step")
#guard lsFails [lsRepeat (.num 5) 1 [.num 0]] (innermostIsNotAnAlgorithm "meta: not a supplied call computation")

-- Zero iterations never project the step: a value and a failing expression alike.
#guard lsOk [lsCall "Run0" [.num 5, .num 1], lsCall "Run0" [.binary .div (.num 1) (.num 0), .num 5],
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

--------------------------------------------------------------------------------
-- ROUND 1 KEEPS THE CAPTURED CALL'S WRITTEN ARGUMENT SLOTS (November 2026)
--------------------------------------------------------------------------------
-- The loop's initial state is the captured call's SOURCED supply
-- (`metaLoopCaptureSourced`: each original argument cell with the slot written
-- for it), and the first round hands it to the step as the ordinary dispatch
-- does (`runNeedStepWith`, `evalSuppliedCallCounted`). A builtin step's VALUE
-- demand of a callable-bearing argument is therefore judged by the slot the
-- direct call judges (`zeroArgumentDemandError?`): a written block reports its
-- OWN unresolved implicit parameters, a clause family is named by its reference,
-- a parameterized property keeps its property context. Before this, round 1
-- passed bare cells: a block and a property were a bare `arityMismatch 1 0`
-- under the builtin's frame, and a family was `noMatchingBranch "conditional"`.
-- Only the failure of round 1 changes; no value, effect or later round does.
--
-- C#: `LoopStepCallableDispatchTests.BuiltinStepRoundOne_*`, spec
-- `loop-step-builtin-argument-blame`. Laws: `ordinary_builtin_is_step_application`,
-- `count_one_builtin` (`KatLangArityLaws/FiniteLoop*.lean`).

-- { q + 1 }: a written block whose one implicit parameter is `q`.
private def lsBlock : KatLang.Expr :=
  .algorithmExpr (alg ["q"] [] [] [.binary .add (.param "q") (.num 1)])

private def lsInnermostIsUnresolvedImplicitParams (names : List String) : Error -> Bool
  | .withContext _ inner => lsInnermostIsUnresolvedImplicitParams names inner
  | .unresolvedImplicitParams actual => actual == names
  | _ => false

-- A builtin `count` step over a BLOCK cell captured through `metaLoopCaptureSourced`:
-- the block's own `unresolvedImplicitParams`, under `count`'s frame, as `count({ q + 1 })`.
#guard lsFails [lsRepeat (resolve "count") 1 [lsBlock]] (lsInnermostIsUnresolvedImplicitParams ["q"])
#guard lsFails [lsRepeat (resolve "count") 1 [lsBlock]] (hasContext "while evaluating call to count")
#guard lsFails [lsCall "count" [lsBlock]] (lsInnermostIsUnresolvedImplicitParams ["q"])
#guard lsFails [lsWhile (resolve "count") [lsBlock]] (lsInnermostIsUnresolvedImplicitParams ["q"])

-- Over a FAMILY cell: `noMatchingBranch` naming the family, never the anonymous "conditional".
#guard lsFails [lsRepeat (resolve "count") 1 [resolve "F"]] (innermostIsNoMatchingBranch "F")
#guard lsFails [lsWhile (resolve "count") [resolve "F"]] (innermostIsNoMatchingBranch "F")
#guard lsFails [lsCall "count" [resolve "F"]] (innermostIsNoMatchingBranch "F")
#guard !lsFails [lsRepeat (resolve "count") 1 [resolve "F"]] (innermostIsNoMatchingBranch "conditional")

-- Over a parameterized PROPERTY: its property-context arity mismatch — `Inc`'s contract, which
-- no frame can present as the builtin's (`take` received its two arguments).
#guard lsFails [lsRepeat (resolve "count") 1 [resolve "Inc"]]
  (fun e => innermostIsArityMismatch 1 0 e && hasContext (KatLang.CtxMsg.property "Inc") e)
#guard lsFails [lsRepeat (resolve "take") 1 [resolve "Inc", .num 1]]
  (fun e => innermostIsArityMismatch 1 0 e && hasContext (KatLang.CtxMsg.property "Inc") e)

/-- An error with its first frame `frame` removed. -/
private def lsWithoutFrame (frame : String) : Error -> Error
  | .withContext msg inner => if msg == frame then inner else .withContext msg (lsWithoutFrame frame inner)
  | e => e

/-- ROUND 1'S FAILURE IS THE DIRECT CALL'S, WHOLE: the loop's error with its own frame removed is
    the direct call's error — every frame and the innermost payload, not only the innermost kind
    (`lsOneIterationEqualsTheCall` compares the innermost error, which a missing property context
    does not change). Blocks, families, properties, a two-parameter builtin, `first`, aliases of a
    builtin, and the value-only control `(1 / 0)`, through `repeat`, `while` and the dot form. -/
def lsRoundOneFailureIsTheDirectCalls : Bool :=
  let cases : List (String × List KatLang.Expr) := [
    ("count", [lsBlock]), ("count", [resolve "F"]), ("count", [resolve "Inc"]),
    ("take", [resolve "Inc", .num 1]), ("first", [resolve "Inc"]), ("last", [lsBlock]),
    -- an alias (chain) of a builtin is the builtin step over the same sourced supply
    ("Cnt", [resolve "Inc"]), ("Cnt2", [lsBlock]),
    ("count", [.binary .div (.num 1) (.num 0)])
  ]
  cases.all fun (callee, supply) =>
    let direct := runResult (lsProgram [lsCall callee supply])
    let same (loop : KatLang.Expr) (frame : String) : Bool :=
      match runResult (lsProgram [loop]), direct with
      | .error a, .error b => (repr (lsWithoutFrame frame a)).pretty == (repr b).pretty
      | _, _ => false
    same (lsRepeat (resolve callee) 1 supply) "while evaluating call to repeat"
      && same (lsWhile (resolve callee) supply) "while evaluating call to while"
      && same (.dotMember (.call (resolve callee) supply) "repeat" (resolve "repeat") (some [.num 1]))
          "while evaluating dotCall .repeat of (call)"

#guard lsRoundOneFailureIsTheDirectCalls

-- The PARAMETER route: `RunCount(v) = repeat(count(v), 1)` against `C(c) = count(c)`. The slot
-- written in the captured call is the parameter read `v`, whose cell transports `Inc`; both
-- report `Inc`'s property-context mismatch under `count`'s frame.
#guard match runResult (lsProgram [lsCall "RunCount" [resolve "Inc"]]), runResult (lsProgram [lsCall "C" [resolve "Inc"]]) with
  | .error a, .error b =>
      (repr (lsWithoutFrame "while evaluating call to repeat" (lsWithoutFrame "while evaluating call to RunCount" a))).pretty
        == (repr (lsWithoutFrame "while evaluating call to C" b)).pretty
  | _, _ => false

-- Controls: values and later rounds are unchanged. Two rounds of `count` over a closed list
-- (round 2 reads a Ready cell, which has no written slot), and a successful first round.
#guard lsOk [lsRepeat (resolve "count") 2 [.listLiteral [.num 1, .num 2]]] (.atom 1)
#guard lsOk [lsRepeat (resolve "count") 1 [.listLiteral [.num 1, .num 2]]] (.atom 2)
#guard lsFails [lsRepeat (resolve "count") 1 [.binary .div (.num 1) (.num 0)]] innermostIsDivByZero

end KatLangTests
