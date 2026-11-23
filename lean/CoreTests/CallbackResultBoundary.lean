import KatLang
import CoreTests.Common

namespace KatLangTests.CallbackResultBoundary
open KatLang (alg algPrivate runResult Algorithm Error Result resolve)
open KatLangTests (sequenceSpread runCountedProgram innermostIsMissingOutput innermostIsAnyTypeMismatch)

/-! # A callback returns its ordinary call result (HO-03; Q-25 resolved October 2026, Option B)

A `map` transform or `reduce` step returns the ordinary result of calling its
callback — the ONE value the call boundary delivers (VAL-06): several written
rows arrive as one sequence value, `()` and `[]` are ordinary values, `map`
stores the result whole as ONE list element and `reduce` passes it whole as the
next accumulator, and nothing is spread. For pure, deterministic, total computations,
`map(L, F)` has the result value `[F(L[0]), F(L[1]), …]`; `reduce([a, b], R, i)`
has the same result value as `R(b, R(a, i))`. Since November 2026 (issue #203) a
fold evaluates its ACCUMULATORS ON DEMAND (§ 10): it demands only its last step,
each step receives ONE deferred accumulator, and a reducer that ignores it skips
every earlier step and the initial expression. Failures
of the invocation propagate unchanged (an output-less algorithm is still
`missingOutput`), `filter` keeps its Boolean contract, and a loop step's ROWS
are still its next state. C#: `CallbackResultBoundaryTests`,
`ClauseFamilyCallbackCardinalityTests`; spec cases
`callback-result-is-the-ordinary-call-result`,
`map-identity-preserves-empty-elements`, `reduce-accumulator-may-be-empty`. -/

private def pair (a b : Int) : Result := .sequenceValue [.atom a, .atom b]

-- D(x) = x, x ; G(x) = D(x) ; H(x) = (x, x) ; S(x) = { D(x)* } ; E(x) = () ;
-- Z(x) = { []* } ; W(x) = [x] ; Id(x) = x ; F(0) = 1, 2 / F(n) = n, n ;
-- Fe(0) = () / Fe(n) = n ; A = D
private def callees : List (String × Algorithm) := [
  ("D", alg ["x"] [] [] [.param "x", .param "x"]),
  ("G", alg ["x"] [] [] [.call (resolve "D") [.param "x"]]),
  ("H", alg ["x"] [] [] [.capture [.param "x", .param "x"]]),
  ("S", alg ["x"] [] [] [sequenceSpread (.call (resolve "D") [.param "x"])]),
  ("E", alg ["x"] [] [] [.emptySequence 0]),
  ("Z", alg ["x"] [] [] [sequenceSpread (.listLiteral [])]),
  ("W", alg ["x"] [] [] [.listLiteral [.param "x"]]),
  ("Id", alg ["x"] [] [] [.param "x"]),
  ("F", .conditional none [] [
    ⟨ .litInt 0, alg [] [] [] [.num 1, .num 2] ⟩,
    ⟨ .bind "n", alg [] [] [] [.param "n", .param "n"] ⟩ ]),
  ("Fe", .conditional none [] [
    ⟨ .litInt 0, alg [] [] [] [.emptySequence 0] ⟩,
    ⟨ .bind "n", alg [] [] [] [.param "n"] ⟩ ]),
  ("A", .alias none [] [] (resolve "D"))
]

-- Pair2(x, acc) = x, acc ; Snoc(x, acc) = acc, x ; Cap(x, acc) = (acc, x) ;
-- Flat(x, acc) = acc*, x ; Keep(x, acc) = acc ; Empty(x, acc) = () ;
-- Lst(x, acc) = [acc, x] ; R(e, 0) = e, 0 / R(e, acc) = e, acc
private def reducers : List (String × Algorithm) := [
  ("Pair2", alg ["x", "acc"] [] [] [.param "x", .param "acc"]),
  ("Snoc", alg ["x", "acc"] [] [] [.param "acc", .param "x"]),
  ("Cap", alg ["x", "acc"] [] [] [.capture [.param "acc", .param "x"]]),
  ("Flat", alg ["x", "acc"] [] [] [sequenceSpread (.param "acc"), .param "x"]),
  ("Keep", alg ["x", "acc"] [] [] [.param "acc"]),
  ("Empty", alg ["x", "acc"] [] [] [.emptySequence 0]),
  ("Lst", alg ["x", "acc"] [] [] [.listLiteral [.param "acc", .param "x"]]),
  ("R", .conditional none [] [
    ⟨ .sequenceValue [.bind "e", .litInt 0], alg [] [] [] [.param "e", .num 0] ⟩,
    ⟨ .sequenceValue [.bind "e", .bind "acc"], alg [] [] [] [.param "e", .param "acc"] ⟩ ])
]

private def program (rows : List KatLang.Expr) : KatLang.Expr :=
  .algorithmExpr (algPrivate [] [] (callees ++ reducers) rows)

private def innermost : Error -> Error
  | .withContext _ inner => innermost inner
  | e => e

/-- The same value, or failures with the same innermost error. -/
private def sameOutcome (a b : Except Error Result) : Bool :=
  match a, b with
  | .ok x, .ok y => x == y
  | .error x, .error y => (repr (innermost x)).pretty == (repr (innermost y)).pretty
  | _, _ => false

private def run (row : KatLang.Expr) : Except Error Result := runResult (program [row])

private def okIs (row : KatLang.Expr) (expected : Result) : Bool :=
  match run row with
  | .ok value => value == expected
  | _ => false

private def mapCall (items : List KatLang.Expr) (f : String) : KatLang.Expr :=
  .call (resolve "map") [.listLiteral items, resolve f]

private def reduceCall (items : List KatLang.Expr) (r : String) (initial : KatLang.Expr) : KatLang.Expr :=
  .call (resolve "reduce") [.listLiteral items, resolve r, initial]

private def elementLists : List (List KatLang.Expr) := [
  [.num 1, .num 2],
  [.emptySequence 0, .num 1],
  [.listLiteral [], .capture [.num 1, .num 2]],
  [.listLiteral [.num 1, .num 2], .capture [.emptySequence 0, .num 3]]
]

-- 1. Wrapper invariance: two rows, an inner call, a capture, a spread wrapper and an
--    alias all map to the same pairs.
#guard ["D", "G", "H", "S", "A"].all fun f =>
  okIs (mapCall [.num 1, .num 2] f) (.listValue [pair 1 1, pair 2 2])

-- 2. Pure deterministic input matrix: map(L, F) matches ordinary-call result values for every callee
--    shape (user, family, alias; rows, capture, (), zero rows, list) and element kind.
def mapIsTheListOfOrdinaryCalls : Bool :=
  callees.all fun (f, _) => elementLists.all fun items =>
    sameOutcome (run (mapCall items f))
      (run (.listLiteral (items.map fun item => .call (resolve f) [item])))

#guard mapIsTheListOfOrdinaryCalls

-- 3. Pure, deterministic, total computations: reduce and nested calls have the same result value.
def reduceIsTheNestedOrdinaryCalls : Bool :=
  reducers.all fun (r, _) =>
    [.num 0, .emptySequence 0, .listLiteral [], .capture [.num 1, .num 2]].all fun initial =>
      [(KatLang.Expr.num 1, KatLang.Expr.num 2), (.emptySequence 0, .num 3)].all fun (a, b) =>
        sameOutcome (run (.listLiteral [reduceCall [a, b] r initial]))
          (run (.listLiteral [.call (resolve r) [b, .call (resolve r) [a, initial]]]))

#guard reduceIsTheNestedOrdinaryCalls

-- 4. The identity map reproduces every list, `()` and `[]` elements included.
#guard okIs (mapCall [.emptySequence 0, .num 1, .listLiteral [], .num 2] "Id")
  (.listValue [.sequenceValue [], .atom 1, .listValue [], .atom 2])
#guard okIs (mapCall [.capture [.num 1, .emptySequence 0], .listLiteral [.emptySequence 0]] "Id")
  (.listValue [.sequenceValue [.atom 1, .sequenceValue []], .listValue [.sequenceValue []]])

-- 5. Several rows are ONE element (nothing is spread); `()` is one element too.
#guard okIs (mapCall [.num 1, .num 2, .num 3] "D") (.listValue [pair 1 1, pair 2 2, pair 3 3])
#guard okIs (mapCall [.num 1, .num 2] "E") (.listValue [.sequenceValue [], .sequenceValue []])
#guard okIs (mapCall [.num 1] "Z") (.listValue [.sequenceValue []])

-- 6. Every value is a legitimate accumulator: `()` may start a fold, be produced by a
--    step and end it; several rows are one accumulator, so `x, acc` nests.
#guard okIs (reduceCall [.num 1] "Keep" (.emptySequence 0)) (.sequenceValue [])
#guard okIs (reduceCall [.num 1, .num 2] "Empty" (.num 0)) (.sequenceValue [])
#guard okIs (reduceCall [.num 1, .num 2] "Pair2" (.num 0)) (.sequenceValue [.atom 2, pair 1 0])
#guard okIs (reduceCall [.num 1, .num 2, .num 3] "Flat" (.emptySequence 0))
  (.sequenceValue [.atom 1, .atom 2, .atom 3])

-- 7. A reduce RESULT crosses the value boundary: evaluated as the top-level expression
--    itself (a root program re-counts its rows), its emitted count is `valueCount` of its
--    value — 0 exactly for `()`, whether steps ran or the initial value was returned.
private def countedReduce (items : List KatLang.Expr) (step : Algorithm) (initial : KatLang.Expr) :
    Except Error KatLang.CountedResult :=
  runCountedProgram (.call (resolve "reduce") [.listLiteral items, .algorithmExpr step, initial])

#guard match countedReduce [.num 1] (alg ["x", "acc"] [] [] [.param "acc"]) (.emptySequence 0) with
  | .ok (value, count) => value == .sequenceValue [] && count == 0
  | _ => false
#guard match countedReduce [.num 1, .num 2] (alg ["x", "acc"] [] [] [.emptySequence 0]) (.num 0) with
  | .ok (value, count) => value == .sequenceValue [] && count == 0
  | _ => false
#guard match countedReduce [] (alg ["x", "acc"] [] [] [.param "acc"]) (.emptySequence 0) with
  | .ok (value, count) => value == .sequenceValue [] && count == 0
  | _ => false
#guard match countedReduce [.num 1, .num 2] (alg ["x", "acc"] [] [] [.param "x", .param "acc"]) (.num 0) with
  | .ok (value, count) => value == .sequenceValue [.atom 2, pair 1 0] && count == 1
  | _ => false

-- 8. A family callback returns exactly its ordinary call result (PAT-11).
#guard sameOutcome (run (mapCall [.num 0, .num 3] "F"))
  (run (.listLiteral [.call (resolve "F") [.num 0], .call (resolve "F") [.num 3]]))
#guard okIs (mapCall [.num 0, .num 3] "F") (.listValue [pair 1 2, pair 3 3])
#guard okIs (mapCall [.num 0, .num 3] "Fe") (.listValue [.sequenceValue [], .atom 3])

-- 9. Unchanged contracts: an output-less algorithm is still `missingOutput` (VAL-05),
--    a two-row filter predicate is the Boolean-required type error, and a loop step's
--    two rows are two state slots while a `()` row is one.
#guard match runResult (.algorithmExpr (algPrivate [] []
    [("Lib", alg [] [] [] []), ("Get", alg ["x"] [] [] [resolve "Lib"])]
    [.call (resolve "map") [.listLiteral [.num 1], resolve "Get"]])) with
  | .error e => innermostIsMissingOutput e
  | _ => false
#guard match runResult (.algorithmExpr (algPrivate [] []
    [("Two", alg ["x"] [] [] [.boolLiteral true, .boolLiteral true])]
    [.call (resolve "filter") [.listLiteral [.num 1], resolve "Two"]])) with
  | .error e => KatLangTests.innermostIsBooleanRequired "filter predicate result"
      "a sequence value with 2 sequence elements: (true, true)" e
  | _ => false
#guard okIs (.call (resolve "repeat") [.call (resolve "D") [.num 5], .num 1]) (pair 5 5)
#guard okIs (.listLiteral [.call (resolve "repeat") [.call (resolve "E") [.num 5], .num 1]]) (.listValue [.sequenceValue []])

-- 10. ACCUMULATORS ARE EVALUATED ON DEMAND (lazy `reduce`, November 2026, issue #203;
--     `EvalBody.evalReduceCounted` over `NeedSuspension.applied`). The fold demands its
--     collection whole, then only its LAST step: each step is the ordinary invocation over
--     its already evaluated element and ONE deferred accumulator, whose demand runs the
--     preceding step or evaluates the start. C#: `LazyReduceAccumulatorTests`.
private def div0 : KatLang.Expr := .binary .div (.num 1) (.num 0)
private def tick : KatLang.Expr := .call (resolve "tick") []
private def metaParam (name : String) : KatLang.CallableParameter := { name := name, kind := .metaRef }

-- Pick(item, acc) = item ; Add(item, acc) = item + acc ; Digits(item, acc) = acc * 10 + item ;
-- Skip(item, acc) = if(item == 1, 1 / 0, item) ; T(item, acc) = tick() * item + acc ;
-- Twice(item, acc) = acc + acc ; TT(item, acc) = tick() + acc + acc ;
-- Late(item, acc) = if(item == 1, 1 / 0, item + acc) ; Call(item, acc) = acc(item) ;
-- Inc(x) = x + 1 ; Cap(meta c) = c.Invoke() ; ViaCap(item, acc) = Cap(acc) ;
-- Meta(item, meta acc) = item ; Unpack(item, (a, b)) = (item, b) ;
-- Lit(item, 0) = item / Lit(item, acc) = item + acc ; Head(0, acc) = 0 / Head(item, acc) = item ;
-- A = Pick
private def lazyProps : List (String × Algorithm) := [
  ("Pick", alg ["item", "acc"] [] [] [.param "item"]),
  ("Add", alg ["item", "acc"] [] [] [.binary .add (.param "item") (.param "acc")]),
  ("Digits", alg ["item", "acc"] [] [] [.binary .add (.binary .mul (.param "acc") (.num 10)) (.param "item")]),
  ("Skip", alg ["item", "acc"] [] []
    [.call (resolve "if") [.comparison (.param "item") [⟨.eq, .num 1⟩], div0, .param "item"]]),
  ("T", alg ["item", "acc"] [] [] [.binary .add (.binary .mul tick (.param "item")) (.param "acc")]),
  ("Twice", alg ["item", "acc"] [] [] [.binary .add (.param "acc") (.param "acc")]),
  ("TT", alg ["item", "acc"] [] [] [.binary .add (.binary .add tick (.param "acc")) (.param "acc")]),
  ("Late", alg ["item", "acc"] [] []
    [.call (resolve "if") [.comparison (.param "item") [⟨.eq, .num 1⟩], div0,
      .binary .add (.param "item") (.param "acc")]]),
  ("Call", alg ["item", "acc"] [] [] [.call (.param "acc") [.param "item"]]),
  ("Inc", alg ["x"] [] [] [.binary .add (.param "x") (.num 1)]),
  ("Cap", KatLang.algWithParameters [metaParam "c"] [] [] [.dotCall (.param "c") "Invoke" (some [])]),
  ("ViaCap", alg ["item", "acc"] [] [] [.call (resolve "Cap") [.param "acc"]]),
  ("Meta", KatLang.algWithParameters [{ name := "item" }, metaParam "acc"] [] [] [.param "item"]),
  ("Unpack", KatLang.algWithParameterPatterns
    [.capture { name := "item" }, .sequenceValue [.capture { name := "a" }, .capture { name := "b" }]]
    [] [] [.capture [.param "item", .param "b"]]),
  ("Lit", .conditional none [] [
    ⟨ .sequenceValue [.bind "item", .litInt 0], alg [] [] [] [.param "item"] ⟩,
    ⟨ .sequenceValue [.bind "item", .bind "acc"], alg [] [] [] [.binary .add (.param "item") (.param "acc")] ⟩ ]),
  ("Head", .conditional none [] [
    ⟨ .sequenceValue [.litInt 0, .bind "acc"], alg [] [] [] [.num 0] ⟩,
    ⟨ .sequenceValue [.bind "item", .bind "acc"], alg [] [] [] [.param "item"] ⟩ ]),
  ("A", .alias none [] [] (resolve "Pick"))
]

private def lazyRun (row : KatLang.Expr) : Except Error Result :=
  runResult (.algorithmExpr (algPrivate [] [] lazyProps [row]))

private def lazyIs (row : KatLang.Expr) (expected : Result) : Bool :=
  match lazyRun row with
  | .ok value => value == expected
  | .error _ => false

private def lazyFailsWith (row : KatLang.Expr) (check : Error → Bool) : Bool :=
  match lazyRun row with
  | .ok _ => false
  | .error e => check (innermost e)

private def isDivByZero : Error → Bool
  | .divByZero => true
  | _ => false

private def isNotAnAlgorithm : Error → Bool
  | .notAnAlgorithm _ => true
  | _ => false

-- The issue's table: an ignored accumulator leaves the initial expression and the earlier
-- step unforced; a demanded one fails where it is demanded; the association is the left fold.
#guard lazyIs (reduceCall [.num 1, .num 2] "Pick" div0) (.atom 2)
#guard lazyIs (reduceCall [.num 1, .num 2] "Skip" (.num 0)) (.atom 2)
#guard lazyFailsWith (reduceCall [.num 1, .num 2] "Add" div0) isDivByZero
#guard lazyIs (reduceCall [.num 1, .num 2, .num 3] "Digits" (.num 0)) (.atom 123)
-- An empty collection demands the start once and never uses the reducer.
#guard lazyIs (.listLiteral [reduceCall [] "Pick" tick, tick]) (.listValue [.atom 1, .atom 2])
#guard lazyFailsWith (reduceCall [] "Pick" div0) isDivByZero
#guard lazyIs (.call (resolve "reduce") [.listLiteral [], div0, .num 7]) (.atom 7)
-- The collection is demanded whole, before any step and before the start.
#guard lazyFailsWith (reduceCall [div0, .num 2] "Pick" (.num 0)) isDivByZero
#guard lazyIs (.listLiteral [reduceCall [tick, tick] "Pick" tick, tick]) (.listValue [.atom 2, .atom 3])

-- Effects follow actual demand: the step for 2 draws 1 first, so the fold is 1 * 2 + (2 * 1 + 0).
#guard lazyIs (reduceCall [.num 1, .num 2] "T" (.num 0)) (.atom 4)
-- ... exactly as the nested ordinary calls draw.
#guard sameOutcome (lazyRun (reduceCall [.num 1, .num 2] "T" (.num 0)))
  (lazyRun (.call (resolve "T") [.num 2, .call (resolve "T") [.num 1, .num 0]]))

-- A demanded accumulator is evaluated ONCE: the start draws once however often it is read
-- (`Twice`: (1 + 1) + (1 + 1)), and so does each earlier step (`TT`: 1 + 8 + 8, where the
-- step for 1 is 2 + 3 + 3).
#guard lazyIs (reduceCall [.num 1, .num 2] "Twice" tick) (.atom 4)
#guard lazyIs (reduceCall [.num 1, .num 2] "TT" tick) (.atom 17)
#guard lazyIs (.listLiteral [reduceCall [.num 1, .num 2] "TT" tick, tick]) (.listValue [.atom 17, .atom 4])

-- A demanded earlier step's failure is the fold's failure, under ONE reduce step frame.
#guard lazyFailsWith (reduceCall [.num 1, .num 2, .num 3] "Late" (.num 0)) isDivByZero
#guard match lazyRun (reduceCall [.num 1, .num 2, .num 3] "Late" (.num 0)) with
  | .error (.withContext _ (.withContext frame inner)) =>
      frame == KatLang.reduceStepContext && (match inner with | .withContext frame2 _ => frame2 != KatLang.reduceStepContext | _ => true)
  | _ => false

-- The accumulator slot is demanded through the ordinary binder: an inspecting pattern and a
-- literal clause head demand it, a plain binder does not.
#guard lazyFailsWith (reduceCall [.num 1, .num 2] "Unpack" div0) isDivByZero
#guard lazyIs (reduceCall [.num 1, .num 2] "Unpack" (.capture [.num 5, .num 6])) (pair 2 6)
#guard lazyFailsWith (reduceCall [.num 1, .num 2] "Lit" div0) isDivByZero
#guard lazyIs (reduceCall [.num 1, .num 2] "Lit" (.num 0)) (.atom 3)
#guard lazyIs (reduceCall [.num 1, .num 2] "Head" div0) (.atom 2)
-- A builtin reducer demands it through its argument roles: `take(element, accumulator)` demands
-- its count when it binds.
#guard lazyFailsWith (.call (resolve "reduce") [.listLiteral [.listLiteral [.num 1, .num 2, .num 3]], resolve "take", div0]) isDivByZero
#guard lazyIs (.call (resolve "reduce") [.listLiteral [.listLiteral [.num 1, .num 2, .num 3]], resolve "take", .num 2])
  (.listValue [.atom 1, .atom 2])
-- An alias of a reducer is its target.
#guard lazyIs (reduceCall [.num 1, .num 2] "A" div0) (.atom 2)

-- Synthetic accumulator slots are VALUE-only. The initial computation's callable identity is
-- not transferred (the ordinary call passes the callable itself) ...
#guard lazyIs (.call (resolve "Call") [.num 1, resolve "Inc"]) (.atom 2)
#guard lazyFailsWith (reduceCall [.num 1] "Call" (resolve "Inc")) isNotAnAlgorithm
-- ... nor its written-call plan: a META parameter captures the ordinary call's argument and
-- refuses the fold's slot, the start's and a step's alike.
#guard lazyIs (.call (resolve "ViaCap") [.num 1, .call (resolve "Inc") [.num 4]]) (.atom 5)
#guard lazyFailsWith (reduceCall [.num 1] "ViaCap" (.call (resolve "Inc") [.num 4])) isNotAnAlgorithm
#guard lazyFailsWith (reduceCall [.num 1] "Meta" (.call (resolve "Inc") [.num 4])) isNotAnAlgorithm
#guard lazyFailsWith (reduceCall [.num 1, .num 2] "Meta" (.num 0)) isNotAnAlgorithm

-- A long fold whose reducer uses every accumulator, and one that skips all but its last step.
#guard lazyIs (reduceCall ((List.range 300).map fun n => KatLang.Expr.num (Int.ofNat n)) "Add" (.num 0)) (.atom 44850)
#guard lazyIs (reduceCall ((List.range 300).map fun n => KatLang.Expr.num (Int.ofNat n)) "Pick" div0) (.atom 299)

end KatLangTests.CallbackResultBoundary
