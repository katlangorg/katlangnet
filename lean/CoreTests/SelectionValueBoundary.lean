import KatLang
import CoreTests.Common

namespace KatLangTests
open KatLang (alg algWithParameters algWithParameterPatterns algPrivate privateProp publicProp privateLocalProp publicLocalProp runFlat runResult Algorithm Error Result PropExposure)
open KatLang (resolve param num)

--------------------------------------------------------------------------------
-- SELECTION IS A VALUE BOUNDARY (September 2026)
--------------------------------------------------------------------------------
-- `A:i`, `first(A)`, and `last(A)` CHOOSE a value: the selected element is
-- returned exactly as stored and re-counted through the ordinary value
-- boundary (`Result.valueCount`) — `()` emits zero values, everything else
-- (a sequence value, an exact list, a scalar) emits ONE. The selected value's
-- origin is forgotten, so every count-sensitive consumer (a lone root row, a
-- collecting dotted receiver — the ordinary leading argument, since dot-call
-- passes a value — a loop-step output row, the map/reduce single-element
-- checks, a callback parameter) sees exactly what it would see for a property
-- holding the same value. Only the spread marker `*` OPENS a selected
-- sequence or list — one boundary, per the ordinary spread law.
--
-- Lean: `Result.select?` + the `.index` arm of `evalCounted`,
-- `evalFirstCounted`/`evalLastCounted`, `countedSequenceCallbackItem`; laws in
-- `KatLangArityLaws.lean`. C#: `SelectionValueBoundaryTests`.

-- Coll(*xs) = xs
def selectionCollAlg : Algorithm :=
  algWithParameters [{ name := "xs", kind := .collecting }] [] [] [.param "xs"]

-- Id(x) = x
def selectionIdAlg : Algorithm :=
  alg ["x"] [] [] [.param "x"]

-- Wrap(x) = (x)
def selectionWrapAlg : Algorithm :=
  alg ["x"] [] [] [.capture [.param "x"]]

-- F(x) = x.Coll
def selectionItemCollAlg : Algorithm :=
  alg ["x"] [] [] [.dotCall (.param "x") "Coll" none]

-- G(x) = (x)*.Coll  (the fluent spread receiver lowers to Coll((x)*))
def selectionItemSpreadCollAlg : Algorithm :=
  alg ["x"] [] [] [.call (resolve "Coll") [.sequenceSpread (.param "x")]]

-- R(x, acc) = x
def selectionReduceItemAlg : Algorithm :=
  alg ["x", "acc"] [] [] [.param "x"]

/-- The semantic table of the rule: (selected value, `selection.Coll`,
    `selection*.Coll`). `()` and `[]` are deliberately distinct rows: an
    empty SEQUENCE value emits zero values at a value boundary (so it spreads
    to nothing) while an empty LIST is one exact value; both are ONE collected
    item when passed unspread, because dot-call passes a value (`().Coll` is
    `[()]`, exactly like the written argument `Coll(())`) and only the spread
    marker opens a receiver. -/
def selectionTable : List (KatLang.Expr × Result × Result) :=
  [ (.emptySequence 0,
      .listValue [.sequenceValue []],
      .listValue []),
    (.num 1,
      .listValue [.atom 1],
      .listValue [.atom 1]),
    (.stringLiteral "s",
      .listValue [.str "s"],
      .listValue [.str "s"]),
    (.boolLiteral true,
      .listValue [.bool true],
      .listValue [.bool true]),
    (.capture [.num 1, .num 2],
      .listValue [.sequenceValue [.atom 1, .atom 2]],
      .listValue [.atom 1, .atom 2]),
    (.listLiteral [],
      .listValue [.listValue []],
      .listValue []),
    (.listLiteral [.num 1, .num 2],
      .listValue [.listValue [.atom 1, .atom 2]],
      .listValue [.atom 1, .atom 2]),
    (.listLiteral [.emptySequence 0],
      .listValue [.listValue [.sequenceValue []]],
      .listValue [.sequenceValue []]),
    (.listLiteral [.capture [.num 1, .num 2]],
      .listValue [.listValue [.sequenceValue [.atom 1, .atom 2]]],
      .listValue [.sequenceValue [.atom 1, .atom 2]]),
    (.capture [.capture [.num 1, .num 2], .num 3],
      .listValue [.sequenceValue [.sequenceValue [.atom 1, .atom 2], .atom 3]],
      .listValue [.sequenceValue [.atom 1, .atom 2], .atom 3]),
    (.capture [.listLiteral [.num 1, .num 2], .num 3],
      .listValue [.sequenceValue [.listValue [.atom 1, .atom 2], .atom 3]],
      .listValue [.listValue [.atom 1, .atom 2], .atom 3]),
    (.capture [.emptySequence 0, .num 3],
      .listValue [.sequenceValue [.sequenceValue [], .atom 3]],
      .listValue [.sequenceValue [], .atom 3]) ]

/-- Every selection spelling of the SAME element: the collection definition that
    places the element where the spelling selects it, and the selection. -/
def selectionForms (selected : KatLang.Expr) : List (Algorithm × KatLang.Expr) :=
  let front := alg [] [] [] [.capture [selected, .num 9]]          -- A = (V, 9)
  let back := alg [] [] [] [.capture [.num 9, selected]]           -- A = (9, V)
  let frontList := alg [] [] [] [.listLiteral [selected, .num 9]]  -- A = [V, 9]
  let backList := alg [] [] [] [.listLiteral [.num 9, selected]]   -- A = [9, V]
  [ (front, .index (resolve "A") (.num 0)),
    (front, .call (resolve "first") [resolve "A"]),
    (back, .index (resolve "A") (.num 1)),
    (back, .call (resolve "last") [resolve "A"]),
    (back, .index (resolve "A") (.binary .sub (.dotCall (resolve "A") "count" none) (.num 1))),
    (frontList, .index (resolve "A") (.num 0)),
    (frontList, .call (resolve "first") [resolve "A"]),
    (backList, .call (resolve "last") [resolve "A"]) ]

def runSelectionProgram (collection : Algorithm) (extraProps : List (Prod String Algorithm))
    (out : KatLang.Expr) : Except Error Result :=
  runResult (.algorithmExpr (algPrivate [] [] ([("Coll", selectionCollAlg), ("A", collection)] ++ extraProps) [out]))

def resultIs (expected : Result) : Except Error Result -> Bool
  | Except.ok value => value == expected
  | _ => false

/-- Two evaluation outcomes agree: equal values, or errors with the same
    structured shape (`Error` carries no `BEq`; its `Repr` is total). -/
def sameOutcome {A : Type} [BEq A] : Except Error A -> Except Error A -> Bool
  | Except.ok a, Except.ok b => a == b
  | Except.error e, Except.error f => reprStr e == reprStr f
  | _, _ => false

-- Through the collecting dotted receiver: `selection.Coll` keeps the selected
-- value whole (ONE collected item — a selected `()` and a selected `[]`
-- alike), and it is exactly the written call `Coll(selection)` (dot-call
-- passes a value), which passes the same one slot as `Coll(V)` on a property
-- holding the same value; `selection*.Coll` / `Coll(selection*)` open exactly
-- one boundary, while the CAPTURE of the spread `(selection*).Coll` is one
-- value again.
def everySelectionFormKeepsTheSelectedValueWholeAndSpreadOpensIt : Bool :=
  selectionTable.all fun (selected, expectedColl, expectedSpreadColl) =>
    (selectionForms selected).all fun (collection, selection) =>
      resultIs expectedColl
        (runSelectionProgram collection [] (.dotCall selection "Coll" none)) &&
      resultIs expectedColl
        (runSelectionProgram collection [] (.call (resolve "Coll") [selection])) &&
      resultIs expectedColl
        (runSelectionProgram collection [("V", alg [] [] [] [selected])] (.call (resolve "Coll") [resolve "V"])) &&
      resultIs expectedColl
        (runSelectionProgram collection [("V", alg [] [] [] [selected])] (.dotCall (resolve "V") "Coll" none)) &&
      resultIs expectedSpreadColl
        (runSelectionProgram collection [] (.dotCall (.sequenceSpread selection) "Coll" none)) &&
      resultIs expectedSpreadColl
        (runSelectionProgram collection [] (.call (resolve "Coll") [.sequenceSpread selection])) &&
      (match expectedSpreadColl with
       | .listValue items =>
           resultIs (.listValue [Result.normalize (Result.sequenceValue items)])
             (runSelectionProgram collection [] (.dotCall (.capture [.sequenceSpread selection]) "Coll" none))
       | _ => false)

#guard everySelectionFormKeepsTheSelectedValueWholeAndSpreadOpensIt

-- Origin independence: storing the selection (`X = selection`) or passing it
-- through another ordinary value boundary (a call) changes nothing.
def storedSelectionBehavesExactlyLikeTheBareSelection : Bool :=
  selectionTable.all fun (selected, expectedColl, expectedSpreadColl) =>
    (selectionForms selected).all fun (collection, selection) =>
      let stored := [("X", alg [] [] [] [selection]), ("Id", selectionIdAlg)]
      resultIs expectedColl
        (runSelectionProgram collection stored (.dotCall (resolve "X") "Coll" none)) &&
      resultIs expectedColl
        (runSelectionProgram collection stored (.call (resolve "Coll") [resolve "X"])) &&
      resultIs expectedSpreadColl
        (runSelectionProgram collection stored (.call (resolve "Coll") [.sequenceSpread (resolve "X")])) &&
      resultIs expectedSpreadColl
        (runSelectionProgram collection stored (.dotCall (.sequenceSpread (resolve "X")) "Coll" none)) &&
      resultIs expectedColl
        (runSelectionProgram collection stored (.dotCall (.call (resolve "Id") [selection]) "Coll" none))

#guard storedSelectionBehavesExactlyLikeTheBareSelection

-- A lone root row: the selected value is ONE row with the emitted count of the
-- literal root row `V` (a selected `()` keeps the documented root bump: one
-- visible empty slot), never opened into several rows.
def loneRootRowShowsTheSelectedValueAsOneRow : Bool :=
  selectionTable.all fun (selected, _, _) =>
    let literal := runCountedProgram (.algorithmExpr (alg [] [] [] [selected]))
    (selectionForms selected).all fun (collection, selection) =>
      sameOutcome
        (runCountedProgram (.algorithmExpr (algPrivate [] [] [("Coll", selectionCollAlg), ("A", collection)] [selection])))
        literal &&
      (match literal with
       | .ok (_, 1) => true
       | _ => false)

#guard loneRootRowShowsTheSelectedValueAsOneRow

-- Written slots reify the selection as one value: `[selection, 9]`,
-- `(selection, 9)`, and structural equality with the written literal.
def writtenSlotsReifyTheSelectionAsOneValue : Bool :=
  selectionTable.all fun (selected, _, _) =>
    let literalList := runResult (.algorithmExpr (alg [] [] [] [.listLiteral [selected, .num 9]]))
    let literalSeq := runResult (.algorithmExpr (alg [] [] [] [.capture [selected, .num 9]]))
    (selectionForms selected).all fun (collection, selection) =>
      sameOutcome (runSelectionProgram collection [] (.listLiteral [selection, .num 9])) literalList &&
      sameOutcome (runSelectionProgram collection [] (.capture [selection, .num 9])) literalSeq &&
      resultIs (.bool true)
        (runSelectionProgram collection [] (.compare .eq selection selected))

#guard writtenSlotsReifyTheSelectionAsOneValue

-- A loop-step output row keeps the selection as ONE state slot:
-- `S(x, y) = selection, y + 1` with `repeat(S, 1, 0, 0)` ends in the two-slot
-- state `(V, 1)`, whatever V is (a selected pair is never opened into two
-- slots, a selected `()` stays one visible slot).
def loopStepOutputRowKeepsTheSelectionAsOneStateSlot : Bool :=
  selectionTable.all fun (selected, _, _) =>
    let literalValue := runResult (.algorithmExpr (alg [] [] [] [selected]))
    (selectionForms selected).all fun (collection, selection) =>
      let step := alg ["x", "y"] [] [] [selection, .binary .add (.param "y") (.num 1)]
      match literalValue, runCountedProgram (.algorithmExpr (algPrivate [] []
          [("Coll", selectionCollAlg), ("A", collection)]
          [.call (resolve "repeat") [.algorithmExpr step, .num 1, .num 0, .num 0]])) with
      | .ok value, .ok (.sequenceValue [slot, .atom 1], 2) => slot == value
      | _, _ => false

#guard loopStepOutputRowKeepsTheSelectionAsOneStateSlot

-- The map transform and the reduce step see the selection as ONE value: a
-- transform returning `selection` behaves exactly like one returning the
-- written literal (a literal `()` is the documented empty-result rejection,
-- and so is a selected `()`).
def mapTransformAndReduceStepSeeTheSelectionAsOneValue : Bool :=
  selectionTable.all fun (selected, _, _) =>
    let literalMap := runResult (.algorithmExpr (algPrivate [] []
      [("H", alg ["x"] [] [] [selected])]
      [.call (resolve "map") [.capture [.num 1], resolve "H"]]))
    let literalReduce := runResult (.algorithmExpr (algPrivate [] []
      [("H", alg ["x", "acc"] [] [] [selected])]
      [.call (resolve "reduce") [.capture [.num 1], resolve "H", .num 0]]))
    (selectionForms selected).all fun (collection, selection) =>
      sameOutcome
        (runSelectionProgram collection [("F", alg ["x"] [] [] [selection])]
          (.call (resolve "map") [.capture [.num 1], resolve "F"]))
        literalMap &&
      sameOutcome
        (runSelectionProgram collection [("F", alg ["x", "acc"] [] [] [selection])]
          (.call (resolve "reduce") [.capture [.num 1], resolve "F", .num 0]))
        literalReduce

#guard mapTransformAndReduceStepSeeTheSelectionAsOneValue

-- A higher-order callback item is a selected value with the same boundary:
-- inside the callback it is ONE value on every count-sensitive path (the
-- collecting dotted receiver `x.Coll` — i.e. `Coll(x)` — a bare `x` output
-- row, the single-element checks), and only an explicit spread `(x)*` opens it.
def callbackItemIsASelectedValueWithTheSameBoundary : Bool :=
  selectionTable.all fun (selected, expectedColl, expectedSpreadColl) =>
    let collection := alg [] [] [] [.capture [selected, .num 9]]   -- A = (V, 9)
    let props := [("F", selectionItemCollAlg), ("G", selectionItemSpreadCollAlg),
                  ("Id", selectionIdAlg), ("Wrap", selectionWrapAlg), ("R", selectionReduceItemAlg)]
    resultIs (.listValue [expectedColl, .listValue [.atom 9]])
      (runSelectionProgram collection props (.call (resolve "map") [resolve "A", resolve "F"])) &&
    resultIs (.listValue [expectedSpreadColl, .listValue [.atom 9]])
      (runSelectionProgram collection props (.call (resolve "map") [resolve "A", resolve "G"])) &&
    -- `Id(x) = x` and `Wrap(x) = (x)` agree: the bare item row is one mapped
    -- element (a `()` item is the documented empty-result rejection for both).
    sameOutcome
      (runSelectionProgram collection props (.call (resolve "map") [resolve "A", resolve "Id"]))
      (runSelectionProgram collection props (.call (resolve "map") [resolve "A", resolve "Wrap"])) &&
    (match selected with
     | .emptySequence _ =>
         (match runSelectionProgram collection props (.call (resolve "map") [resolve "A", resolve "Id"]) with
          | Except.error err => hasContext "map transform must return a single element" err
          | _ => false)
     | _ =>
         sameOutcome
           (runSelectionProgram collection props (.call (resolve "map") [resolve "A", resolve "Id"]))
           (runResult (.algorithmExpr (alg [] [] [] [.listLiteral [selected, .num 9]]))) &&
         resultIs (.atom 9)
           (runSelectionProgram collection props (.call (resolve "reduce") [resolve "A", resolve "R", .num 0])))

#guard callbackItemIsASelectedValueWithTheSameBoundary

-- The motivating examples: `()` selected from a sequence, read from a
-- property, returned by a call, or chosen by `if` is simply `()` — ONE
-- collected item when passed (dot-call passes a value: `().Coll` is `[()]`
-- like the written `Coll(())`) and zero items when spread — and no route
-- preserves "one element was selected" or turns the value-boundary count 0
-- into a missing argument; `[]` selected through any route stays one exact
-- list item.
def emptySelectedThroughAnyRouteIsPlainEmpty : Bool :=
  let props := [("Coll", selectionCollAlg),
                ("A", alg [] [] [] [.capture [.emptySequence 0, .num 1]]),
                ("B", alg [] [] [] [.capture [.num 1, .emptySequence 0]]),
                ("E", alg [] [] [] [.emptySequence 0]),
                ("Fz", alg ["x"] [] [] [.emptySequence 0]),
                ("L", alg [] [] [] [.capture [.listLiteral [], .num 1]])]
  let run (out : KatLang.Expr) := runResult (.algorithmExpr (algPrivate [] [] props [out]))
  let coll (receiver : KatLang.Expr) := run (.dotCall receiver "Coll" none)
  let written (argument : KatLang.Expr) := run (.call (resolve "Coll") [argument])
  [ coll (.index (resolve "A") (.num 0)),
    coll (.call (resolve "first") [resolve "A"]),
    coll (.index (resolve "B") (.num 1)),
    coll (.call (resolve "last") [resolve "B"]),
    coll (resolve "E"),
    coll (.call (resolve "Fz") [.num 1]),
    coll (.call (resolve "if") [.boolLiteral true, .emptySequence 0, .num 1]),
    coll (.emptySequence 0),
    written (.index (resolve "A") (.num 0)),
    written (.call (resolve "first") [resolve "A"]),
    written (resolve "E"),
    written (.call (resolve "Fz") [.num 1]),
    written (.emptySequence 0) ].all (resultIs (.listValue [.sequenceValue []])) &&
  [ written (.sequenceSpread (.index (resolve "A") (.num 0))),
    written (.sequenceSpread (.call (resolve "first") [resolve "A"])),
    written (.sequenceSpread (resolve "E")),
    written (.sequenceSpread (.emptySequence 0)),
    coll (.sequenceSpread (.index (resolve "A") (.num 0))),
    coll (.sequenceSpread (resolve "E")),
    written (.sequenceSpread (.index (resolve "L") (.num 0))) ].all (resultIs (.listValue [])) &&
  [ coll (.index (resolve "L") (.num 0)),
    coll (.call (resolve "first") [resolve "L"]),
    written (.index (resolve "L") (.num 0)) ].all (resultIs (.listValue [.listValue []]))

#guard emptySelectedThroughAnyRouteIsPlainEmpty

-- first(A) ≡ A:0 and last(A) ≡ A:(A.count - 1), counted, for representative
-- non-empty collections including nested and empty structures.
def firstLastCollections : List KatLang.Expr :=
  [ .capture [.num 1, .num 2],
    .num 7,
    .stringLiteral "text",
    .boolLiteral true,
    .capture [.emptySequence 0, .num 1],
    .capture [.num 1, .emptySequence 0],
    .capture [.emptySequence 0, .emptySequence 0],
    .capture [.capture [.num 1, .num 2], .num 3],
    .capture [.num 3, .capture [.num 1, .num 2]],
    .capture [.listLiteral [], .num 1],
    .capture [.num 1, .listLiteral []],
    .capture [.listLiteral [.num 1, .num 2], .num 3],
    .capture [.listLiteral [.emptySequence 0], .listLiteral [.capture [.num 1, .num 2]]],
    .listLiteral [.num 1, .num 2],
    .listLiteral [.listLiteral []],
    .listLiteral [.capture [.num 1, .num 2], .capture [.num 3, .num 4]],
    .listLiteral [.emptySequence 0],
    .capture [.capture [.num 1, .num 2], .emptySequence 0, .listLiteral [.num 3]] ]

def firstIsSelectionAtZeroAndLastIsSelectionAtCountMinusOne : Bool :=
  firstLastCollections.all fun collection =>
    let props := [("Coll", selectionCollAlg), ("A", alg [] [] [] [collection])]
    let counted (out : KatLang.Expr) := runCountedProgram (.algorithmExpr (algPrivate [] [] props [out]))
    let firstCall := KatLang.Expr.call (resolve "first") [resolve "A"]
    let lastCall := KatLang.Expr.call (resolve "last") [resolve "A"]
    let indexZero := KatLang.Expr.index (resolve "A") (.num 0)
    let indexLast := KatLang.Expr.index (resolve "A")
      (.binary .sub (.dotCall (resolve "A") "count" none) (.num 1))
    let observers : List (KatLang.Expr -> KatLang.Expr) :=
      [ fun e => e,
        fun e => .dotCall e "Coll" none,
        fun e => .call (resolve "Coll") [.sequenceSpread e],
        fun e => .listLiteral [e, .num 9] ]
    observers.all fun observe =>
      sameOutcome (counted (observe firstCall)) (counted (observe indexZero)) &&
      sameOutcome (counted (observe lastCall)) (counted (observe indexLast)) &&
      (match counted (observe firstCall) with | .ok _ => true | _ => false)

#guard firstIsSelectionAtZeroAndLastIsSelectionAtCountMinusOne

-- An empty target has no valid selection: `first`/`last` report the collection
-- arity rejection and `:` the index rejection.
def selectionFromAnEmptyCollectionFailsInEveryForm : Bool :=
  [KatLang.Expr.emptySequence 0, .listLiteral []].all fun target =>
    let props := [("A", alg [] [] [] [target])]
    let run (out : KatLang.Expr) := runResult (.algorithmExpr (algPrivate [] [] props [out]))
    (match run (.call (resolve "first") [resolve "A"]) with
     | Except.error err => innermostIsBadArity err | _ => false) &&
    (match run (.call (resolve "last") [resolve "A"]) with
     | Except.error err => innermostIsBadArity err | _ => false) &&
    (match run (.index (resolve "A") (.num 0)) with
     | Except.error err => innermostIsBadIndex err | _ => false)

#guard selectionFromAnEmptyCollectionFailsInEveryForm

-- Explicit spread of a selection opens exactly ONE boundary, and selection-
-- then-spread differs from spread-then-selection.
def spreadOfASelectionOpensExactlyOneBoundary : Bool :=
  let props := [("Coll", selectionCollAlg),
                ("A", alg [] [] [] [.capture [.capture [.capture [.num 1, .num 2], .listLiteral [.num 3, .num 4]], .num 9]]),
                ("B", alg [] [] [] [.listLiteral [.listLiteral [.num 1, .num 2], .listLiteral [.num 3, .num 4]]])]
  let run (out : KatLang.Expr) := runResult (.algorithmExpr (algPrivate [] [] props [out]))
  let oneLevel : Result := .listValue [.sequenceValue [.atom 1, .atom 2], .listValue [.atom 3, .atom 4]]
  resultIs oneLevel (run (.call (resolve "Coll") [.sequenceSpread (.index (resolve "A") (.num 0))])) &&
  resultIs oneLevel (run (.call (resolve "Coll") [.sequenceSpread (.call (resolve "first") [resolve "A"])])) &&
  resultIs (.listValue [.atom 1, .atom 2])
    (run (.call (resolve "Coll") [.sequenceSpread (.index (resolve "B") (.num 0))])) &&
  resultIs (.listValue [.listValue [.atom 1, .atom 2]])
    (run (.dotCall (.index (.capture [.sequenceSpread (resolve "B")]) (.num 0)) "Coll" none)) &&
  (match runCountedProgram (.algorithmExpr (algPrivate [] [] props
      [.sequenceSpread (.index (resolve "A") (.num 0))])) with
   | .ok (.sequenceValue [.sequenceValue [.atom 1, .atom 2], .listValue [.atom 3, .atom 4]], 2) => true
   | _ => false)

#guard spreadOfASelectionOpensExactlyOneBoundary

-- Observe the expression before the root output row makes an empty result
-- visible. This distinguishes count 0 for selected `()` from count 1 for `[]`.
def selectionCountBeforeRootDecoration : Bool :=
  selectionTable.all fun (selected, _, _) =>
    let collection := KatLang.Expr.listLiteral [selected]
    let selectors := [KatLang.Expr.index collection (.num 0),
      .call (resolve "first") [collection], .call (resolve "last") [collection]]
    selectors.all fun selection =>
      sameOutcome (runCountedProgram selection) (runCountedProgram selected) &&
      (match runCountedProgram selection with
       | .ok (_, count) => count == (match selected with | .emptySequence _ => 0 | _ => 1)
       | _ => false)

#guard selectionCountBeforeRootDecoration

-- Filter must inspect the same value as a direct call, and keep the original
-- exact element even when the element is `()`. The collector makes the count
-- visible to the Boolean predicate instead of merely comparing display text.
def filterCallbackUsesTheOrdinaryValueBoundary : Bool :=
  selectionTable.all fun (selected, expectedColl, _) =>
    let collection := alg [] [] [] [.listLiteral [selected]]
    let keep := alg ["x"] [] []
      [.compare .eq (.dotCall (.param "x") "Coll" none) (KatLang.resultToExpr expectedColl)]
    let filtered := KatLang.Expr.call (resolve "filter") [resolve "A", resolve "Keep"]
    sameOutcome
      (runSelectionProgram collection [("Keep", keep)] filtered)
      (runResult (.algorithmExpr (alg [] [] [] [.listLiteral [selected]]))) &&
    resultIs (.atom 1)
      (runSelectionProgram collection [("Keep", keep)] (.dotCall filtered "count" none))

#guard filterCallbackUsesTheOrdinaryValueBoundary

end KatLangTests
