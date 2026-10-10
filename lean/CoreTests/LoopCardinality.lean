import KatLang
import CoreTests.Common

namespace KatLangTests
open KatLang (alg algWithParameters algWithParameterPatterns algPrivate privateProp publicProp privateLocalProp publicLocalProp runFlat runResult Algorithm Error Result PropExposure)
open KatLang (resolve param num)

--------------------------------------------------------------------------------
-- THE LOOP CARDINALITY LAW (Q-24 + Q-26, decided October 2026)
--------------------------------------------------------------------------------
-- Patterns bind. Rows produce. `*` opens. None of the three changes the others.
--
-- * Q-24: a step's parameter patterns bind the INCOMING state only
--   (`runNeedStepSlots` -> `bindNeedPatterns`). The step's emitted ROW SUPPLY
--   (`evalAlgOutputSlots`, which takes no pattern-derived argument) IS the next
--   state: a non-spread row is one slot, a spread row supplies its items. No
--   pattern category — plain, repeated, collecting, structural — repacks it
--   (the former LOOP-04 packing of a pattern-bound step's spread row is gone).
-- * Q-26: a completed `while`/`repeat` is ONE value — the canonical capture of
--   its final slots — with emitted count `Result.valueCount`
--   (`loopResultCounted`), exactly like every builtin and call result. The slot
--   count is the loop's own protocol; only an explicit spread `L*` opens the
--   result into items.
--
-- C#: `LoopCardinalityLawTests` (six routes), the ArityDifferential laws
-- `LOOP_STEP_ROWS_ARE_THE_NEXT_STATE`, `LOOP_STEP_PATTERNS_ONLY_BIND_THE_INCOMING_STATE`
-- and `LOOP_RESULT_IS_A_VALUE_BOUNDARY`. Laws: `loop_result_*` in
-- `KatLangArityLaws.lean`.

-- Fib(x, y) = y, x + y
def lcFibAlg : Algorithm :=
  alg ["x", "y"] [] [] [.param "y", .binary .add (.param "x") (.param "y")]

-- Inc(x) = x + 1
def lcIncAlg : Algorithm :=
  alg ["x"] [] [] [.binary .add (.param "x") (.num 1)]

private def lcCap (name : String) : KatLang.ParameterPattern := .capture { name := name }
private def lcColl (name : String) : KatLang.ParameterPattern := .capture { name := name, kind := .collecting }

private def lcPair (a b : Int) : KatLang.Expr := .capture [.num a, .num b]

/-- One step-head category: its parameter patterns, the initial state binding
    `a = 1`, `b = 2` through that head, and the expressions the rows use for `a`
    and `b` under that head. -/
structure LcHead where
  name : String
  patterns : List KatLang.ParameterPattern
  init : List KatLang.Expr
  a : KatLang.Expr
  b : KatLang.Expr

def lcHeads : List LcHead := [
  { name := "flat", patterns := [lcCap "a", lcCap "b"],
    init := [.num 1, .num 2], a := .param "a", b := .param "b" },
  { name := "repeated names", patterns := [lcCap "a", lcCap "a", lcCap "b"],
    init := [.num 1, .num 1, .num 2], a := .param "a", b := .param "b" },
  { name := "collector", patterns := [lcCap "a", lcColl "rest"],
    init := [.num 1, .num 2], a := .param "a", b := .index (.param "rest") (.num 0) },
  { name := "collector only", patterns := [lcColl "xs"],
    init := [.num 1, .num 2], a := .index (.param "xs") (.num 0), b := .index (.param "xs") (.num 1) },
  { name := "sequence pattern", patterns := [.sequenceValue [lcCap "a", lcCap "b"]],
    init := [lcPair 1 2], a := .param "a", b := .param "b" },
  { name := "list pattern", patterns := [.listValue [lcCap "a", lcCap "b"]],
    init := [.listLiteral [.num 1, .num 2]], a := .param "a", b := .param "b" },
  { name := "nested pattern", patterns := [.sequenceValue [.sequenceValue [lcCap "a", lcCap "b"], lcCap "c"]],
    init := [.capture [lcPair 1 2, .num 3]], a := .param "a", b := .param "b" },
  { name := "sequence pattern with collector", patterns := [.sequenceValue [lcCap "a", lcColl "rest"]],
    init := [lcPair 1 2], a := .param "a", b := .index (.param "rest") (.num 0) },
  { name := "repeated structural leaf",
    patterns := [.sequenceValue [lcCap "a", lcCap "b"], .sequenceValue [lcCap "a", lcCap "c"]],
    init := [lcPair 1 2, lcPair 1 3], a := .param "a", b := .param "b" }
]

/-- Output forms over `a = 1`, `b = 2`, each followed by the sentinel row `0`,
    with the value the step's row supply captures: the sentinel makes the
    captured value reveal the exact slot list (two or more slots form one
    sequence of them; a lone `0` means the form supplied no slot). -/
def lcForms (a b : KatLang.Expr) : List (List KatLang.Expr × Result) := [
  ([a, b], .sequenceValue [.atom 1, .atom 2, .atom 0]),
  ([.capture [a, b]], .sequenceValue [.sequenceValue [.atom 1, .atom 2], .atom 0]),
  ([sequenceSpread (.capture [a, b])], .sequenceValue [.atom 1, .atom 2, .atom 0]),
  ([.listLiteral [a, b]], .sequenceValue [.listValue [.atom 1, .atom 2], .atom 0]),
  ([sequenceSpread (.listLiteral [a, b])], .sequenceValue [.atom 1, .atom 2, .atom 0]),
  ([.emptySequence 0], .sequenceValue [.sequenceValue [], .atom 0]),
  ([sequenceSpread (.emptySequence 0)], .atom 0),
  ([.capture [sequenceSpread (.emptySequence 0)]], .sequenceValue [.sequenceValue [], .atom 0]),
  ([sequenceSpread (.capture [a, .capture [a, b]])],
    .sequenceValue [.atom 1, .sequenceValue [.atom 1, .atom 2], .atom 0]),
  ([.call (resolve "repeat") [resolve "Fib", .num 1, a, b]],
    .sequenceValue [.sequenceValue [.atom 2, .atom 3], .atom 0]),
  ([sequenceSpread (.call (resolve "repeat") [resolve "Fib", .num 1, a, b])],
    .sequenceValue [.atom 2, .atom 3, .atom 0])
]

/-- Q-24: equal rows form an equal next state whatever the step's head. For
    every head category and every output form, one iteration
    `repeat(S, 1, init)` captures exactly the row supply the form defines, and
    equals the direct call `S(init)` in value. A packed spread row (the retired
    LOOP-04) would turn `(a, b)*, 0` into the two-slot state `((1, 2), 0)`
    under the pattern-bound heads only. -/
def stepRowsIgnorePatternCategory : Bool :=
  lcHeads.all fun head =>
    (lcForms head.a head.b).all fun (rows, expected) =>
      let step := algWithParameterPatterns head.patterns [] [] (rows ++ [.num 0])
      match runResult (.algorithmExpr (algPrivate [] [] [("Fib", lcFibAlg), ("S", step)]
          [.call (resolve "repeat") ([resolve "S", .num 1] ++ head.init),
           .call (resolve "S") head.init])) with
      | .ok value => value == .sequenceValue [expected, expected]
      | _ => false

#guard stepRowsIgnorePatternCategory

/-- Q-24, the η-wrapper: a flat step that spreads a structural step's result,
    `W(p) = P(p)*`, forms the same next state as the structural step itself. -/
def stepRowsIgnorePatternCategoryThroughAWrapper : Bool :=
  (lcForms (.param "a") (.param "b")).all fun (rows, expected) =>
    let inner := algWithParameterPatterns [.sequenceValue [lcCap "a", lcCap "b"]] [] [] (rows ++ [.num 0])
    let wrapper := alg ["p"] [] [] [sequenceSpread (.call (resolve "P") [.param "p"])]
    match runResult (.algorithmExpr (algPrivate [] [] [("Fib", lcFibAlg), ("P", inner), ("W", wrapper)]
        [.call (resolve "repeat") [resolve "W", .num 1, lcPair 1 2],
         .call (resolve "repeat") [resolve "P", .num 1, lcPair 1 2]])) with
    | .ok value => value == .sequenceValue [expected, expected]
    | _ => false

#guard stepRowsIgnorePatternCategoryThroughAWrapper

-- `Dup(x, x) = { x + 1, x + 1 }` and `Dup(x, x) = { (x + 1, x + 1)* }` form the
-- same two-slot state, so both iterate (formerly the spread row was packed into
-- one slot and the second binding failed). Diverging rows `x + 1, x + 2` iterate
-- once (`(2, 3)`), and the NEXT binding of the repeated name is the ordinary
-- binder's own failure (NEED-04), exactly the direct call `Dup(2, 3)`'s.
def repeatedNameStepRowsAreTheNextState : Bool :=
  let rows (spread : Bool) (second : KatLang.Expr) : List KatLang.Expr :=
    let one := KatLang.Expr.binary .add (.param "x") (.num 1)
    if spread then [sequenceSpread (.capture [one, second])] else [one, second]
  let dup (spread : Bool) (second : KatLang.Expr) : Algorithm :=
    alg ["x", "x"] [] [] (rows spread second)
  let run (step : Algorithm) (out : List KatLang.Expr) : Except Error Result :=
    runResult (.algorithmExpr (algPrivate [] [] [("Dup", step)] out))
  let twice := [KatLang.Expr.call (resolve "repeat") [resolve "Dup", .num 2, .num 1, .num 1]]
  let same := KatLang.Expr.binary .add (.param "x") (.num 1)
  let diverging := KatLang.Expr.binary .add (.param "x") (.num 2)
  (match run (dup false same) twice, run (dup true same) twice with
   | .ok left, .ok right => left == .sequenceValue [.atom 3, .atom 3] && right == left
   | _, _ => false) &&
  [false, true].all fun spread =>
    (match run (dup spread diverging) [.call (resolve "repeat") [resolve "Dup", .num 1, .num 1, .num 1]] with
     | .ok value => value == .sequenceValue [.atom 2, .atom 3]
     | _ => false) &&
    (match run (dup spread diverging) twice, run (dup spread diverging) [.call (resolve "Dup") [.num 2, .num 3]] with
     | .error loopError, .error callError => innermostIsBadArity loopError && innermostIsBadArity callError
     | _, _ => false)

#guard repeatedNameStepRowsAreTheNextState

-- A structural step's one-value row `(b, a + b)` is ONE slot that `(a, b)`
-- re-binds every iteration; its spread `(b, a + b)*` supplies TWO items — the
-- ordinary spread — so the one-pattern head cannot bind the next state.
-- Explicit capture keeps structure: `P((*h), n) = (h*), n + 1` and the list
-- history `Grow([*h], n) = [h*, n], n + 1`.
def structuralStepRowsAreOrdinaryRows : Bool :=
  let ab := [lcCap "a", lcCap "b"]
  let next := [KatLang.Expr.param "b", .binary .add (.param "a") (.param "b")]
  let oneSlot := algWithParameterPatterns [.sequenceValue ab] [] [] [.capture next]
  let twoItems := algWithParameterPatterns [.sequenceValue ab] [] [] [sequenceSpread (.capture next)]
  let history := algWithParameterPatterns [.sequenceValue [lcColl "h"], lcCap "n"] [] []
    [.capture [sequenceSpread (.param "h")], .binary .add (.param "n") (.num 1)]
  let flatHistory := algWithParameterPatterns [.sequenceValue [lcColl "h"], lcCap "n"] [] []
    [sequenceSpread (.param "h"), .binary .add (.param "n") (.num 1)]
  let grow := algWithParameterPatterns [.listValue [lcColl "h"], lcCap "n"] [] []
    [.listLiteral [sequenceSpread (.param "h"), .param "n"], .binary .add (.param "n") (.num 1)]
  let run (props : List (Prod String Algorithm)) (out : KatLang.Expr) : Except Error Result :=
    runResult (.algorithmExpr (algPrivate [] [] props [out]))
  (match run [("Step", oneSlot)] (.call (resolve "repeat") [resolve "Step", .num 3, lcPair 0 1]) with
   | .ok value => value == .sequenceValue [.atom 2, .atom 3]
   | _ => false) &&
  (match run [("Step2", twoItems)] (.call (resolve "repeat") [resolve "Step2", .num 1, lcPair 0 1]) with
   | .ok value => value == .sequenceValue [.atom 1, .atom 1]
   | _ => false) &&
  (match run [("Step2", twoItems)] (.call (resolve "repeat") [resolve "Step2", .num 3, lcPair 0 1]) with
   | .error err => innermostIsArityMismatch 1 2 err
   | _ => false) &&
  (match run [("P", history)] (.call (resolve "repeat") [resolve "P", .num 2, lcPair 1 2, .num 0]) with
   | .ok value => value == .sequenceValue [.sequenceValue [.atom 1, .atom 2], .atom 2]
   | _ => false) &&
  -- Without the capture the history's items become separate slots; the second
  -- binding of `((*h), n)` then sees three slots.
  (match run [("P", flatHistory)] (.call (resolve "repeat") [resolve "P", .num 2, lcPair 1 2, .num 0]) with
   | .error err => innermostIsArityMismatch 2 3 err
   | _ => false) &&
  (match run [("Grow", grow)]
      (.index (.call (resolve "repeat") [resolve "Grow", .num 3, .listLiteral [], .num 0]) (.num 0)) with
   | .ok value => value == .listValue [.atom 0, .atom 1, .atom 2]
   | _ => false)

#guard structuralStepRowsAreOrdinaryRows

/-- Q-26 with the LOOP-07 guard the investigation recommended: one iteration
    equals the direct step call in value AND emitted count, for flat, patterned,
    repeated-name, list-pattern and nested-loop steps (formerly the loop counted
    its slots, and a patterned step's packed spread row made the values differ). -/
def oneIterationEqualsTheDirectCall : Bool :=
  let step := alg ["a", "b"] [] [] [.param "b", .binary .add (.param "a") (.param "b")]
  let history := algWithParameterPatterns [.sequenceValue [lcColl "h"], lcCap "n"] [] []
    [sequenceSpread (.param "h"), .binary .add (.param "n") (.num 1)]
  let dup := alg ["x", "x"] [] []
    [sequenceSpread (.capture [.binary .add (.param "x") (.num 1), .binary .add (.param "x") (.num 1)])]
  let swapList := algWithParameterPatterns [.listValue [lcCap "a", lcCap "b"]] [] []
    [sequenceSpread (.listLiteral [.param "b", .param "a"]), .num 9]
  let nested := alg ["a", "b"] [] []
    [.call (resolve "repeat") [resolve "Step", .num 1, .param "a", .param "b"], .param "a"]
  let props := [("Step", step), ("P", history), ("Dup", dup), ("L", swapList), ("N", nested)]
  let cases : List (String × List KatLang.Expr × KatLang.CountedResult) := [
    ("Step", [.num 3, .num 4], (.sequenceValue [.atom 4, .atom 7], 1)),
    ("P", [lcPair 1 2, .num 0], (.sequenceValue [.atom 1, .atom 2, .atom 1], 1)),
    ("Dup", [.num 1, .num 1], (.sequenceValue [.atom 2, .atom 2], 1)),
    ("L", [.listLiteral [.num 1, .num 2]], (.sequenceValue [.atom 2, .atom 1, .atom 9], 1)),
    ("N", [.num 3, .num 4], (.sequenceValue [.sequenceValue [.atom 4, .atom 7], .atom 3], 1))
  ]
  cases.all fun (name, init, expected) =>
    match runCountedProgram (.algorithmExpr (algPrivate [] [] props
            [.call (resolve "repeat") ([resolve name, .num 1] ++ init)])),
          runCountedProgram (.algorithmExpr (algPrivate [] [] props [.call (resolve name) init])) with
    | .ok loop, .ok call => loop == expected && call == expected
    | _, _ => false

#guard oneIterationEqualsTheDirectCall

/-- Q-26: a completed loop is ONE value at the root, beside another row, under
    an explicit spread, with zero, one or several final slots, for `repeat`
    and `while` alike. -/
def loopResultIsAValueBoundary : Bool :=
  let countdown := alg ["n", "acc"] [] []
    [.binary .sub (.param "n") (.num 1), .binary .add (.param "acc") (.param "n"),
     .compare .gt (.param "n") (.num 1)]
  let drop := algWithParameters [{ name := "xs", kind := .collecting }] [] []
    [sequenceSpread (.emptySequence 0)]
  let props := [("Fib", lcFibAlg), ("Inc", lcIncAlg), ("Cd", countdown), ("Drop", drop)]
  let fib := KatLang.Expr.call (resolve "repeat") [resolve "Fib", .num 10, .num 0, .num 1]
  let pair5589 : Result := .sequenceValue [.atom 55, .atom 89]
  let counted (rows : List KatLang.Expr) (expected : KatLang.CountedResult) : Bool :=
    match runCountedProgram (.algorithmExpr (algPrivate [] [] props rows)) with
    | .ok observed => observed == expected
    | _ => false
  counted [fib] (pair5589, 1) &&
  counted [fib, .num 7] (.sequenceValue [pair5589, .atom 7], 2) &&
  counted [sequenceSpread fib] (pair5589, 2) &&
  counted [.call (resolve "while") [resolve "Cd", .num 3, .num 0]] (.sequenceValue [.atom 1, .atom 5], 1) &&
  counted [.call (resolve "repeat") [resolve "Inc", .num 3, .num 0]] (.atom 3, 1) &&
  -- zero final slots: the result is `()`, emitted count 0 at the loop and one
  -- visible root row; its spread supplies nothing
  counted [.call (resolve "repeat") [resolve "Drop", .num 1, .num 1]] (.sequenceValue [], 1) &&
  counted [sequenceSpread (.call (resolve "repeat") [resolve "Drop", .num 1, .num 1])] (.sequenceValue [], 0) &&
  KatLang.loopResultCounted [] == (.sequenceValue [], 0) &&
  KatLang.loopResultCounted [.atom 3] == (.atom 3, 1) &&
  KatLang.loopResultCounted [.atom 55, .atom 89] == (pair5589, 1)

#guard loopResultIsAValueBoundary

/-- Q-26: the slot count is not observable outside the loop. A one-slot state
    holding `(20, 30)` and a two-slot state `20, 30` complete to the same
    counted result; their difference is only the loop's own next binding. -/
def completedLoopForgetsItsSlotCount : Bool :=
  let onePair := alg ["p"] [] []
    [.capture [.binary .add (.index (.param "p") (.num 0)) (.num 10),
               .binary .add (.index (.param "p") (.num 1)) (.num 10)]]
  let twoSlots := alg ["a", "b"] [] []
    [.binary .add (.param "a") (.num 10), .binary .add (.param "b") (.num 10)]
  let props := [("P1", onePair), ("P2", twoSlots)]
  let run (out : KatLang.Expr) := runCountedProgram (.algorithmExpr (algPrivate [] [] props [out]))
  KatLang.loopResultCounted [.sequenceValue [.atom 20, .atom 30]]
    == KatLang.loopResultCounted [.atom 20, .atom 30] &&
  match run (.call (resolve "repeat") [resolve "P1", .num 1, lcPair 10 20]),
        run (.call (resolve "repeat") [resolve "P2", .num 1, .num 10, .num 20]) with
  | .ok one, .ok two => one == (.sequenceValue [.atom 20, .atom 30], 1) && two == one
  | _, _ => false

#guard completedLoopForgetsItsSlotCount

/-- Q-26: a nested loop written as a step row is ONE next-state slot, exactly
    like a helper call returning it (η-parity); the explicit spread supplies
    its items. `Two(a, b) = repeat(Fib, 2, a, b)` leaves one slot for the
    two-parameter head (formerly SUP-01's nested-loop exception spliced two). -/
def nestedLoopRowIsOneSlot : Bool :=
  let inner := alg ["a", "b"] [] [] [.call (resolve "repeat") [resolve "Fib", .num 2, .param "a", .param "b"]]
  let direct := alg ["a", "b"] [] [] [.call (resolve "repeat") [resolve "Fib", .num 2, .param "a", .param "b"]]
  let wrapped := alg ["a", "b"] [] [] [.call (resolve "Inner") [.param "a", .param "b"]]
  let directSpread := alg ["a", "b"] [] []
    [sequenceSpread (.call (resolve "repeat") [resolve "Fib", .num 2, .param "a", .param "b"])]
  let wrappedSpread := alg ["a", "b"] [] [] [sequenceSpread (.call (resolve "Inner") [.param "a", .param "b"])]
  let props := [("Fib", lcFibAlg), ("Inner", inner), ("Two", direct), ("TwoW", wrapped),
    ("TwoS", directSpread), ("TwoWS", wrappedSpread)]
  let run (step : String) := runResult (.algorithmExpr (algPrivate [] [] props
    [.call (resolve "repeat") [resolve step, .num 3, .num 0, .num 1]]))
  ["Two", "TwoW"].all (fun step =>
    match run step with
    | .error err => innermostIsArityMismatch 2 1 err
    | _ => false) &&
  ["TwoS", "TwoWS"].all (fun step =>
    match run step with
    | .ok value => value == .sequenceValue [.atom 8, .atom 13]
    | _ => false)

#guard nestedLoopRowIsOneSlot

/-- Q-26: a callback body whose row is a multi-slot loop returns ONE value,
    exactly like a helper returning it. Since Q-25 (Option B, October 2026) an
    explicit spread of the loop result inside the body re-opens it into rows that
    the call boundary captures again: the callback's ordinary call result is the
    same one value (HO-03). -/
def callbackBodyLoopIsOneValue : Bool :=
  let loop := KatLang.Expr.call (resolve "repeat") [resolve "Fib", .num 2, .param "x", .num 1]
  let helper := alg ["x"] [] [] [loop]
  let viaHelper := alg ["x"] [] [] [.call (resolve "H") [.param "x"]]
  let spreadBody := alg ["x"] [] [] [sequenceSpread loop]
  let expected : Result := .listValue [.sequenceValue [.atom 1, .atom 2], .sequenceValue [.atom 2, .atom 3]]
  let run (callback : KatLang.Expr) := runResult (.algorithmExpr (algPrivate [] []
    [("Fib", lcFibAlg), ("H", helper), ("V", viaHelper)]
    [.call (resolve "map") [.listLiteral [.num 0, .num 1], callback]]))
  [resolve "H", resolve "V", .algorithmExpr helper, .algorithmExpr spreadBody].all (fun callback =>
    match run callback with
    | .ok value => value == expected
    | _ => false)

#guard callbackBodyLoopIsOneValue

end KatLangTests
