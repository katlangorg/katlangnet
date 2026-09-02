import KatLang
import CoreTests.Common
import CoreTests.SequenceCallbackBuiltins

namespace KatLangTests
open KatLang (alg algWithParameters algWithParameterPatterns algPrivate privateProp publicProp privateLocalProp publicLocalProp runFlat runResult Algorithm Error Result PropExposure)
open KatLang (resolve param num)
open KatLang (Pattern CondBranch)

--------------------------------------------------------------------------------
-- range builtin tests
--------------------------------------------------------------------------------

-- Test 59: ascending inclusive range
def test59 : Bool :=
  match runFlat (.call (resolve "range") [.num 1, .num 10]) with
  | Except.ok [1, 2, 3, 4, 5, 6, 7, 8, 9, 10] => true
  | _ => false

#guard test59

-- Test 60: descending inclusive range
def test60 : Bool :=
  match runFlat (.call (resolve "range") [.num 10, .num 1]) with
  | Except.ok [10, 9, 8, 7, 6, 5, 4, 3, 2, 1] => true
  | _ => false

#guard test60

-- Test 61: equal bounds produce a singleton
def test61 : Bool :=
  match runFlat (.call (resolve "range") [.num 5, .num 5]) with
  | Except.ok [5] => true
  | _ => false

#guard test61

-- Test 62: negative to positive bounds remain inclusive and ordered
def test62 : Bool :=
  match runFlat (.call (resolve "range") [.num (-2), .num 2]) with
  | Except.ok [-2, -1, 0, 1, 2] => true
  | _ => false

#guard test62

-- Test 32: Unary / binary composition with 2-arg if is rejected
def test32 : Bool :=
  match runResult (.binary .add (.num 10) (.unary .minus (.call (resolve "if") [.num 0, .num 5]))) with
  | Except.error _ => true
  | Except.ok _ => false

#guard test32

-- Test 33: if arity mismatch — 1 arg → error
def test33 : Bool :=
  match runResult (.call (resolve "if") [.num 1]) with
  | Except.error _ => true
  | Except.ok _ => false

#guard test33

--------------------------------------------------------------------------------
-- spread builtin-argument evaluation ORDER tests
-- `expandSequenceSpreadBuiltinArguments`: SPREAD-MARKED argument slots are forced
-- exactly once, in left-to-right written order, and expanding a spread slot is
-- part of evaluating that slot. Non-spread slots keep their written position but
-- remain builtin-lazy algorithms at this stage — the builtin decides whether and
-- when to evaluate them (an unselected `if` branch never runs). The helper
-- formerly recursed into the remaining slots BEFORE evaluating the current spread
-- slot, so two failing spread arguments reported the RIGHTMOST failure while C#
-- reported the leftmost. C# parity:
-- tests/KatLang.Tests/SpreadArgumentEvaluationOrderTests.cs and the generated
-- LanguageSpecCases guards `spread-arguments-fail-left-to-right` /
-- `spread-arguments-keep-written-order`.
--------------------------------------------------------------------------------

-- Two spread slots failing with DIFFERENT errors: the reported error identifies
-- which slot was evaluated first, so each shape is pinned in both spellings.
def spreadBuiltinArgumentFailingProps : List (Prod String Algorithm) :=
  [("P", alg [] [] [] [.binary .div (.num 1) (.num 0)]),
   ("Q", alg [] [] [] [.binary .add (.stringLiteral "x") (.num 1)])]

def spreadBuiltinArgumentProgram (callee : String) (args : List KatLang.Expr) : KatLang.Expr :=
  .algorithmExpr (algPrivate [] [] spreadBuiltinArgumentFailingProps [
    .call (resolve callee) args
  ])

def spreadP : KatLang.Expr := sequenceSpread (resolve "P")
def spreadQ : KatLang.Expr := sequenceSpread (resolve "Q")

-- range(P*, Q*) → the leftmost slot's division by zero.
def spreadBuiltinArgumentsRangeFailLeftToRight : Bool :=
  match runResult (spreadBuiltinArgumentProgram "range" [spreadP, spreadQ]) with
  | Except.error err => innermostIsDivByZero err
  | _ => false

#guard spreadBuiltinArgumentsRangeFailLeftToRight

-- range(Q*, P*) → the mirrored spelling reports the type mismatch instead, so this
-- is an ORDER rule, not an error-precedence rule.
def spreadBuiltinArgumentsRangeMirroredFailsFirstSlot : Bool :=
  match runResult (spreadBuiltinArgumentProgram "range" [spreadQ, spreadP]) with
  | Except.error err => innermostIsAnyTypeMismatch err
  | _ => false

#guard spreadBuiltinArgumentsRangeMirroredFailsFirstSlot

-- if(P*, Q*, 0) / if(Q*, P*, 0) — expansion runs before `if` selects a branch.
def spreadBuiltinArgumentsIfFailLeftToRight : Bool :=
  match runResult (spreadBuiltinArgumentProgram "if" [spreadP, spreadQ, .num 0]) with
  | Except.error err => innermostIsDivByZero err
  | _ => false

#guard spreadBuiltinArgumentsIfFailLeftToRight

def spreadBuiltinArgumentsIfMirroredFailsFirstSlot : Bool :=
  match runResult (spreadBuiltinArgumentProgram "if" [spreadQ, spreadP, .num 0]) with
  | Except.error err => innermostIsAnyTypeMismatch err
  | _ => false

#guard spreadBuiltinArgumentsIfMirroredFailsFirstSlot

-- repeat(P*, Q*, 1) / repeat(Q*, P*, 1) — expansion runs before the loop's own
-- step/count/state binding.
def spreadBuiltinArgumentsRepeatFailLeftToRight : Bool :=
  match runResult (spreadBuiltinArgumentProgram "repeat" [spreadP, spreadQ, .num 1]) with
  | Except.error err => innermostIsDivByZero err
  | _ => false

#guard spreadBuiltinArgumentsRepeatFailLeftToRight

def spreadBuiltinArgumentsRepeatMirroredFailsFirstSlot : Bool :=
  match runResult (spreadBuiltinArgumentProgram "repeat" [spreadQ, spreadP, .num 1]) with
  | Except.error err => innermostIsAnyTypeMismatch err
  | _ => false

#guard spreadBuiltinArgumentsRepeatMirroredFailsFirstSlot

-- Correcting the evaluation ORDER must not reorder the expanded argument VALUES:
-- each slot still contributes its items in place.
def spreadBuiltinArgumentBoundsProps : List (Prod String Algorithm) :=
  [("Lo", alg [] [] [] [.num 2]), ("Hi", alg [] [] [] [.num 4])]

def spreadBuiltinArgumentsKeepWrittenOrder : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] spreadBuiltinArgumentBoundsProps [
    .call (resolve "range") [sequenceSpread (resolve "Lo"), sequenceSpread (resolve "Hi")]
  ])) with
  | Except.ok [2, 3, 4] => true
  | _ => false

#guard spreadBuiltinArgumentsKeepWrittenOrder

def spreadBuiltinArgumentsMirroredOrderSwapsArguments : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] spreadBuiltinArgumentBoundsProps [
    .call (resolve "range") [sequenceSpread (resolve "Hi"), sequenceSpread (resolve "Lo")]
  ])) with
  | Except.ok [4, 3, 2] => true
  | _ => false

#guard spreadBuiltinArgumentsMirroredOrderSwapsArguments

-- One spread slot supplying BOTH arguments keeps its items in order too.
def spreadBuiltinArgumentsSingleSlotKeepsItemOrder : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("Bounds", alg [] [] [] [.num 2, .num 4])] [
    .call (resolve "range") [sequenceSpread (resolve "Bounds")]
  ])) with
  | Except.ok [2, 3, 4] => true
  | _ => false

#guard spreadBuiltinArgumentsSingleSlotKeepsItemOrder

--------------------------------------------------------------------------------
-- sum builtin tests
--------------------------------------------------------------------------------

def isEvenAlg93 : Algorithm :=
  alg ["x"] [] [] [
    .binary .eq (.binary .mod (.param "x") (.num 2)) (.num 0)
  ]

-- Test 93: plain-call sum adds expanded range items
def test93 : Bool :=
  match runFlat (.algorithmExpr (alg [] [] [] [
    .call (resolve "sum") [
      .call (resolve "range") [.num 1, .num 5]
    ]
  ])) with
  | Except.ok [15] => true
  | _ => false

#guard test93

-- Test 94: dot-call sum uses receiver injection with no explicit args
def test94 : Bool :=
  match runFlat (.algorithmExpr (alg [] [] [] [
    .dotCall
      (.call (resolve "range") [.num 1, .num 5])
      "sum"
      none
  ])) with
  | Except.ok [15] => true
  | _ => false

#guard test94

-- Test 95: descending ranges also expand for plain-call sum
def test95 : Bool :=
  match runFlat (.algorithmExpr (alg [] [] [] [
    .call (resolve "sum") [
      .call (resolve "range") [.num 5, .num 1]
    ]
  ])) with
  | Except.ok [15] => true
  | _ => false

#guard test95

-- Test 96: sum composes with filter and preserves strict top-level semantics
def test96 : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("IsEven", isEvenAlg93)] [
    .dotCall
      (.dotCall
        (.call (resolve "range") [.num 1, .num 10])
        "filter"
        (some [.resolve "IsEven"]))
      "sum"
      none
  ])) with
  | Except.ok [30] => true
  | _ => false

#guard test96

-- Test 97: sum composes with map and sums the mapped top-level elements
def test97 : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("Square", squareAlg86)] [
    .dotCall
      (.dotCall
        (.call (resolve "range") [.num 1, .num 4])
        "map"
        (some [.resolve "Square"]))
      "sum"
      none
  ])) with
  | Except.ok [30] => true
  | _ => false

#guard test97

-- Test 98: plain-call sum of an empty collection returns zero
def test98 : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("AlwaysFalse", alwaysFalseAlg66a)] [
    .call (resolve "sum") [
      .call (resolve "filter") [
        .call (resolve "range") [.num 1, .num 4],
        .resolve "AlwaysFalse"
      ]
    ]
  ])) with
  | Except.ok [0] => true
  | _ => false

#guard test98

-- Test 99: a single atomic value is treated as a one-element collection
def test99 : Bool :=
  match runFlat (.algorithmExpr (alg [] [] [] [
    .call (resolve "sum") [.num 5]
  ])) with
  | Except.ok [5] => true
  | _ => false

#guard test99

-- Test 100: sequenceValue top-level elements are rejected rather than flattened
def test100 : Bool :=
  let sequenceValuePairs := .capture [
    .capture [.num 1, .num 2],
    .capture [.num 3, .num 4]
  ]
  match runResult (.algorithmExpr (alg [] [] [] [
    .call (resolve "sum") [sequenceValuePairs]
  ])) with
  | Except.error err => hasContext "sum expects each collection element to be a single numeric value; item 0 was sequence value" err && innermostIsBadArity err
  | _ => false

#guard test100

-- Test 101: string elements are rejected by sum
def test101 : Bool :=
  match runResult (.algorithmExpr (alg [] [] [] [
    .call (resolve "sum") [.stringLiteral "hello"]
  ])) with
  | Except.error err => hasContext "sum expects each collection element to be a single numeric value; item 0 was string value \"hello\"" err && innermostIsBadArity err
  | _ => false

#guard test101

--------------------------------------------------------------------------------
-- count builtin tests
--------------------------------------------------------------------------------

-- Test 102: plain-call count counts expanded range items
def test102 : Bool :=
  match runFlat (.algorithmExpr (alg [] [] [] [
    .call (resolve "count") [
      .call (resolve "range") [.num 1, .num 5]
    ]
  ])) with
  | Except.ok [5] => true
  | _ => false

#guard test102

-- Test 103: dot-call count uses receiver injection with no explicit args
def test103 : Bool :=
  match runFlat (.algorithmExpr (alg [] [] [] [
    .dotCall
      (.call (resolve "range") [.num 1, .num 5])
      "count"
      none
  ])) with
  | Except.ok [5] => true
  | _ => false

#guard test103

-- Test 103a: dot-call count matches the shared sequence-value receiver examples
def countReceiverNormalizationRoot103a : Algorithm :=
  algPrivate [] [] [
    ("Data1", alg [] [] [] [.num 1, .num 7]),
    ("Data2", alg [] [] [] [.capture [.num 1, .num 7]])
  ] [
    .dotCall (.resolve "Data1") "count" none,
    .dotCall (.resolve "Data2") "count" none,
    .dotCall (.capture [.num 1, .num 7]) "count" none,
    .dotCall (.capture [
      .capture [.num 1, .num 7]
    ]) "count" none
  ]

def test103a : Bool :=
  match runFlat (.algorithmExpr countReceiverNormalizationRoot103a) with
  | Except.ok [2, 2, 2, 2] => true
  | _ => false

#guard test103a

-- Test 103b: nested sequence-value receiver boundaries are preserved after one strip
def test103b : Bool :=
  let sequenceValuePairs := .capture [
    .capture [.num 1, .num 2],
    .capture [.num 3, .num 4]
  ]
  match runFlat (.algorithmExpr (alg [] [] [] [
    .dotCall sequenceValuePairs "count" none,
    .dotCall (.capture [sequenceValuePairs]) "count" none
  ])) with
  | Except.ok [2, 2] => true
  | _ => false

#guard test103b

-- Test 104: descending ranges still count all expanded top-level items
def test104 : Bool :=
  match runFlat (.algorithmExpr (alg [] [] [] [
    .call (resolve "count") [
      .call (resolve "range") [.num 5, .num 1]
    ]
  ])) with
  | Except.ok [5] => true
  | _ => false

#guard test104

-- Test 105: count composes with filter over kept top-level elements
def test105 : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("IsEven", isEvenAlg93)] [
    .dotCall
      (.dotCall
        (.call (resolve "range") [.num 1, .num 10])
        "filter"
        (some [.resolve "IsEven"]))
      "count"
      none
  ])) with
  | Except.ok [5] => true
  | _ => false

#guard test105

-- Test 106: count composes with map and counts mapped top-level elements
def test106 : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("Square", squareAlg86)] [
    .dotCall
      (.dotCall
        (.call (resolve "range") [.num 1, .num 4])
        "map"
        (some [.resolve "Square"]))
      "count"
      none
  ])) with
  | Except.ok [4] => true
  | _ => false

#guard test106

-- Test 107: plain-call count of an empty collection is zero
def test107 : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("AlwaysFalse", alwaysFalseAlg66a)] [
    .call (resolve "count") [
      .call (resolve "filter") [
        .call (resolve "range") [.num 1, .num 4],
        .resolve "AlwaysFalse"
      ]
    ]
  ])) with
  | Except.ok [0] => true
  | _ => false

#guard test107

-- Test 107a: dot-call count of an empty filtered receiver is zero
def test107a : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("AlwaysFalse", alwaysFalseAlg66a)] [
    .dotCall
      (.dotCall
        (.capture [.num 1, .num 5, .num 3])
        "filter"
        (some [.resolve "AlwaysFalse"]))
      "count"
      none
  ])) with
  | Except.ok [0] => true
  | _ => false

#guard test107a

-- Test 107b: count(collection) is an ordinary fixed-arity callable, so an empty
-- call is an arity error — absence of an argument is never an empty collection
-- (the explicit empty-collection call `count(())` counts zero).
def test107b : Bool :=
  match runFlat (.algorithmExpr (alg [] [] [] [
    .call (resolve "count") []
  ])) with
  | Except.error err => innermostIsArityMismatch 1 0 err
  | _ => false

#guard test107b

--------------------------------------------------------------------------------
-- Fixed-arity collection builtin calls (mirrors the C# fixed collection-object
-- binding tests): a collection builtin is an ordinary fixed-arity callable
-- (`sum(collection)`, `contains(collection, item)`) whose ONE bound collection
-- value is read through the one-level collection view after binding.
--------------------------------------------------------------------------------

-- sum(collection): one grouped value is the collection argument; inline
-- multi-item calls and empty calls are ordinary arity errors.
def builtinSumTakesOneCollectionArgument : Bool :=
  let inlineErrs :=
    match runResult (.algorithmExpr (alg [] [] [] [
      .call (resolve "sum") [.num 3, .num 4, .num 2, .num 1, .num 3, .num 3]
    ])) with
    | Except.error err => innermostIsArityMismatch 1 6 err
    | _ => false
  let grouped :=
    match runFlat (.algorithmExpr (alg [] [] [] [
      .call (resolve "sum") [.capture [.num 3, .num 4, .num 2, .num 1, .num 3, .num 3]]
    ])) with
    | Except.ok [16] => true
    | _ => false
  let emptyErrs :=
    match runResult (.algorithmExpr (alg [] [] [] [.call (resolve "sum") []])) with
    | Except.error err => innermostIsArityMismatch 1 0 err
    | _ => false
  inlineErrs && grouped && emptyErrs

#guard builtinSumTakesOneCollectionArgument

-- Multiple sibling arguments are never flattened into one collection: sum(A, B) with
-- A = (1, 2) and B = (3, 4) is a two-argument arity error, and sum(A*, B*) opens the
-- spreads into FOUR ordinary argument slots (also an arity error). The concatenation
-- rewrite groups the spreads into ONE collection argument: sum((*A, *B)) = 10.
def builtinSumSiblingsNotFlattened : Bool :=
  let siblingsErr :=
    match runResult (.algorithmExpr (algPrivate [] [] [
      ("A", alg [] [] [] [.num 1, .num 2]),
      ("B", alg [] [] [] [.num 3, .num 4])
    ] [ .call (resolve "sum") [resolve "A", resolve "B"] ])) with
    | Except.error err => innermostIsArityMismatch 1 2 err
    | _ => false
  let spreadSiblingsErr :=
    match runResult (.algorithmExpr (algPrivate [] [] [
      ("A", alg [] [] [] [.num 1, .num 2]),
      ("B", alg [] [] [] [.num 3, .num 4])
    ] [ .call (resolve "sum") [sequenceSpread (resolve "A"), sequenceSpread (resolve "B")] ])) with
    | Except.error err => innermostIsArityMismatch 1 4 err
    | _ => false
  let groupedConcatenates :=
    match runFlat (.algorithmExpr (algPrivate [] [] [
      ("A", alg [] [] [] [.num 1, .num 2]),
      ("B", alg [] [] [] [.num 3, .num 4])
    ] [ .call (resolve "sum") [
          .capture [sequenceSpread (resolve "A"), sequenceSpread (resolve "B")]] ])) with
    | Except.ok [10] => true
    | _ => false
  siblingsErr && spreadSiblingsErr && groupedConcatenates

#guard builtinSumSiblingsNotFlattened

-- contains(collection, item): the first argument is the collection and the second is the
-- item. The inline multi-item call is an arity error; the grouped form binds.
def builtinContainsTakesCollectionAndItem : Bool :=
  let inlineErrs :=
    match runResult (.algorithmExpr (alg [] [] [] [
      .call (resolve "contains") [.num 1, .num 2, .num 3, .num 2]
    ])) with
    | Except.error err => innermostIsArityMismatch 2 4 err
    | _ => false
  let grouped :=
    match runFlat (.algorithmExpr (alg [] [] [] [
      .call (resolve "contains") [.capture [.num 1, .num 2, .num 3], .num 2]
    ])) with
    | Except.ok [1] => true
    | _ => false
  inlineErrs && grouped

#guard builtinContainsTakesCollectionAndItem

-- A collection builtin is NOT a user variadic: sum(3, 4, 2, 1, 3, 3) is an arity error
-- under `sum(collection)`, while a user variadic G(*values) = values.sum captures the
-- same inline items and sums them; the grouped call sum((3, 4, 2, 1, 3, 3)) is the
-- builtin twin.
def builtinFixedArityDiffersFromUserVariadic : Bool :=
  let builtinInlineErrs :=
    match runResult (.algorithmExpr (alg [] [] [] [
      .call (resolve "sum") [.num 3, .num 4, .num 2, .num 1, .num 3, .num 3]
    ])) with
    | Except.error err => innermostIsArityMismatch 1 6 err
    | _ => false
  let builtinGrouped :=
    match runFlat (.algorithmExpr (alg [] [] [] [
      .call (resolve "sum") [.capture [.num 3, .num 4, .num 2, .num 1, .num 3, .num 3]]
    ])) with
    | Except.ok [16] => true
    | _ => false
  let userSumAlg : Algorithm :=
    algWithParameters [{ name := "values", kind := .collecting }] [] [] [
      .dotCall (.param "values") "sum" none
    ]
  let viaUser :=
    match runFlat (.algorithmExpr (algPrivate [] [] [("G", userSumAlg)] [
      .call (resolve "G") [.num 3, .num 4, .num 2, .num 1, .num 3, .num 3]
    ])) with
    | Except.ok [16] => true
    | _ => false
  builtinInlineErrs && builtinGrouped && viaUser

#guard builtinFixedArityDiffersFromUserVariadic

-- Test 108: count's one bound sequence-valued argument is opened by the
-- one-level collection view — two nested pairs are two items.
def test108 : Bool :=
  let sequenceValuePairs := .capture [
    .capture [.num 1, .num 2],
    .capture [.num 3, .num 4]
  ]
  match runFlat (.algorithmExpr (alg [] [] [] [
    .call (resolve "count") [sequenceValuePairs]
  ])) with
  | Except.ok [2] => true
  | _ => false

#guard test108

-- Test 108a: plain-call `count(filter(X, pred))` destructures the one filtered
-- sequence argument and counts its kept items.
def test108aPlainCountFilterCountsOneSequenceValueResult : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("IsEven", isEvenAlg93)] [
    .call (resolve "count") [
      .call (resolve "filter") [
        .call (resolve "range") [.num 1, .num 4],
        .resolve "IsEven"
      ]
    ]
  ])) with
  | Except.ok [2] => true
  | _ => false

#guard test108aPlainCountFilterCountsOneSequenceValueResult

-- Test 109: a single atomic value is treated as a one-element collection
def test109 : Bool :=
  match runFlat (.algorithmExpr (alg [] [] [] [
    .call (resolve "count") [.num 5]
  ])) with
  | Except.ok [1] => true
  | _ => false

#guard test109

-- Test 110: string elements are valid top-level elements for count
def test110 : Bool :=
  match runFlat (.algorithmExpr (alg [] [] [] [
    .call (resolve "count") [.stringLiteral "hello"]
  ])) with
  | Except.ok [1] => true
  | _ => false

#guard test110

-- Test 110a: plain-call contains searches expanded range items
def test110a : Bool :=
  match runFlat (.algorithmExpr (alg [] [] [] [
    .call (resolve "contains") [
      .call (resolve "range") [.num 1, .num 5],
      .num 3
    ]
  ])) with
  | Except.ok [1] => true
  | _ => false

#guard test110a

-- Test 110b: contains returns zero when no top-level item matches
def test110b : Bool :=
  match runFlat (.algorithmExpr (alg [] [] [] [
    .call (resolve "contains") [
      .call (resolve "range") [.num 1, .num 5],
      .num 9
    ]
  ])) with
  | Except.ok [0] => true
  | _ => false

#guard test110b

-- Test 110c: dot-call contains matches plain-call receiver semantics
def test110c : Bool :=
  match runFlat (.algorithmExpr (alg [] [] [] [
    .dotCall
      (.call (resolve "range") [.num 1, .num 5])
      "contains"
      (some [.num 4])
  ])) with
  | Except.ok [1] => true
  | _ => false

#guard test110c

-- Test 110d: contains compares sequence-value top-level elements structurally
def test110d : Bool :=
  match runFlat (.algorithmExpr (alg [] [] [] [
    .call (resolve "contains") [
      sequenceItems [
        .capture [.num 1, .num 2],
        .capture [.num 3, .num 4]
      ],
      .capture [.num 1, .num 2]
    ]
  ])) with
  | Except.ok [1] => true
  | _ => false

#guard test110d

-- Test 110e: contains searches top-level items only, not nested sequence elements
def test110e : Bool :=
  let sequenceValuePairs := .capture [
    .capture [.num 1, .num 2],
    .capture [.num 3, .num 4]
  ]
  let nestedCollection := sequenceItems [sequenceValuePairs, .num 0]
  match runFlat (.algorithmExpr (alg [] [] [] [
    .call (resolve "contains") [
      nestedCollection,
      .capture [.num 1, .num 2]
    ]
  ])) with
  | Except.ok [0] => true
  | _ => false

#guard test110e

-- Test 110f: selection-projected content follows the same contains rules in both call styles
def containsProjectionRoot110f : Algorithm :=
  algPrivate [] [] [
    ("Data", alg [] [] [] [
      .capture [.num 7, .num 6, .num 4, .num 2, .num 1],
      .capture [.num 1, .num 2, .num 3, .num 4, .num 5]
    ])
  ] [
    .call (resolve "contains") [
      .index (.resolve "Data") (.num 0),
      .num 4
    ],
    .dotCall (.index (.resolve "Data") (.num 0)) "contains" (some [.num 4])
  ]

def test110f : Bool :=
  match runFlat (.algorithmExpr containsProjectionRoot110f) with
  | Except.ok [1, 1] => true
  | _ => false

#guard test110f

-- Test 110g: contains's item argument stays outside the collection — a
-- multi-output helper bound to `item` is compared as one grouped value.
def test110g : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("Item", alg [] [] [] [.num 1, .num 2])
  ] [
    .call (resolve "contains") [
      .capture [.num 1, .num 2],
      .resolve "Item"
    ]
  ])) with
  | Except.ok [0] => true
  | _ => false

#guard test110g

--------------------------------------------------------------------------------
-- min builtin tests
--------------------------------------------------------------------------------

def negateAlg111 : Algorithm :=
  alg ["x"] [] [] [
    .unary .minus (.param "x")
  ]

-- Test 111: plain-call min compares expanded range items
def test111 : Bool :=
  match runFlat (.algorithmExpr (alg [] [] [] [
    .call (resolve "min") [
      .call (resolve "range") [.num 1, .num 5]
    ]
  ])) with
  | Except.ok [1] => true
  | _ => false

#guard test111

-- Test 112: dot-call min uses receiver injection with no explicit args
def test112 : Bool :=
  match runFlat (.algorithmExpr (alg [] [] [] [
    .dotCall
      (.call (resolve "range") [.num 1, .num 5])
      "min"
      none
  ])) with
  | Except.ok [1] => true
  | _ => false

#guard test112

-- Test 113: descending ranges also expand for plain-call min
def test113 : Bool :=
  match runFlat (.algorithmExpr (alg [] [] [] [
    .call (resolve "min") [
      .call (resolve "range") [.num 5, .num 1]
    ]
  ])) with
  | Except.ok [1] => true
  | _ => false

#guard test113

-- Test 114: min composes with filter over kept top-level elements
def test114 : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("IsEven", isEvenAlg93)] [
    .dotCall
      (.dotCall
        (.call (resolve "range") [.num 1, .num 10])
        "filter"
        (some [.resolve "IsEven"]))
      "min"
      none
  ])) with
  | Except.ok [2] => true
  | _ => false

#guard test114

-- Test 115: min composes with map and compares mapped top-level elements
def test115 : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("Negate", negateAlg111)] [
    .dotCall
      (.dotCall
        (.call (resolve "range") [.num 1, .num 4])
        "map"
        (some [.resolve "Negate"]))
      "min"
      none
  ])) with
  | Except.ok [-4] => true
  | _ => false

#guard test115

-- Test 116: plain-call min requires a non-empty collection
def test116 : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("AlwaysFalse", alwaysFalseAlg66a)] [
    .call (resolve "min") [
      .call (resolve "filter") [
        .call (resolve "range") [.num 1, .num 4],
        .resolve "AlwaysFalse"
      ]
    ]
  ])) with
  | Except.error err => hasContext "min requires a non-empty collection" err && innermostIsBadArity err
  | _ => false

#guard test116

-- Test 117: a single atomic value is treated as a one-element collection
def test117 : Bool :=
  match runFlat (.algorithmExpr (alg [] [] [] [
    .call (resolve "min") [.num 5]
  ])) with
  | Except.ok [5] => true
  | _ => false

#guard test117

-- Test 118: sequenceValue top-level elements are rejected rather than flattened
def test118 : Bool :=
  let sequenceValuePairs := .capture [
    .capture [.num 1, .num 2],
    .capture [.num 3, .num 4]
  ]
  match runResult (.algorithmExpr (alg [] [] [] [
    .call (resolve "min") [sequenceValuePairs]
  ])) with
  | Except.error err => hasContext "min expects each collection element to be a single numeric value; item 0 was sequence value" err && innermostIsBadArity err
  | _ => false

#guard test118

-- Test 119: string elements are rejected by min
def test119 : Bool :=
  match runResult (.algorithmExpr (alg [] [] [] [
    .call (resolve "min") [.stringLiteral "hello"]
  ])) with
  | Except.error err => hasContext "min expects each collection element to be a single numeric value; item 0 was string value \"hello\"" err && innermostIsBadArity err
  | _ => false

#guard test119

--------------------------------------------------------------------------------
-- max builtin tests
--------------------------------------------------------------------------------

-- Test 120: plain-call max compares expanded range items
def test120 : Bool :=
  match runFlat (.algorithmExpr (alg [] [] [] [
    .call (resolve "max") [
      .call (resolve "range") [.num 1, .num 5]
    ]
  ])) with
  | Except.ok [5] => true
  | _ => false

#guard test120

-- Test 121: dot-call max uses receiver injection with no explicit args
def test121 : Bool :=
  match runFlat (.algorithmExpr (alg [] [] [] [
    .dotCall
      (.call (resolve "range") [.num 1, .num 5])
      "max"
      none
  ])) with
  | Except.ok [5] => true
  | _ => false

#guard test121

-- Test 122: descending ranges also expand for plain-call max
def test122 : Bool :=
  match runFlat (.algorithmExpr (alg [] [] [] [
    .call (resolve "max") [
      .call (resolve "range") [.num 5, .num 1]
    ]
  ])) with
  | Except.ok [5] => true
  | _ => false

#guard test122

-- Test 123: max composes with filter over kept top-level elements
def test123 : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("IsEven", isEvenAlg93)] [
    .dotCall
      (.dotCall
        (.call (resolve "range") [.num 1, .num 10])
        "filter"
        (some [.resolve "IsEven"]))
      "max"
      none
  ])) with
  | Except.ok [10] => true
  | _ => false

#guard test123

-- Test 124: max composes with map and compares mapped top-level elements
def test124 : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("Negate", negateAlg111)] [
    .dotCall
      (.dotCall
        (.call (resolve "range") [.num 1, .num 4])
        "map"
        (some [.resolve "Negate"]))
      "max"
      none
  ])) with
  | Except.ok [-1] => true
  | _ => false

#guard test124

-- Test 125: plain-call max requires a non-empty collection
def test125 : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("AlwaysFalse", alwaysFalseAlg66a)] [
    .call (resolve "max") [
      .call (resolve "filter") [
        .call (resolve "range") [.num 1, .num 4],
        .resolve "AlwaysFalse"
      ]
    ]
  ])) with
  | Except.error err => hasContext "max requires a non-empty collection" err && innermostIsBadArity err
  | _ => false

#guard test125

-- Test 126: a single atomic value is treated as a one-element collection
def test126 : Bool :=
  match runFlat (.algorithmExpr (alg [] [] [] [
    .call (resolve "max") [.num 5]
  ])) with
  | Except.ok [5] => true
  | _ => false

#guard test126

-- Test 127: sequenceValue top-level elements are rejected rather than flattened
def test127 : Bool :=
  let sequenceValuePairs := .capture [
    .capture [.num 1, .num 2],
    .capture [.num 3, .num 4]
  ]
  match runResult (.algorithmExpr (alg [] [] [] [
    .call (resolve "max") [sequenceValuePairs]
  ])) with
  | Except.error err => hasContext "max expects each collection element to be a single numeric value; item 0 was sequence value" err && innermostIsBadArity err
  | _ => false

#guard test127

-- Test 128: string elements are rejected by max
def test128 : Bool :=
  match runResult (.algorithmExpr (alg [] [] [] [
    .call (resolve "max") [.stringLiteral "hello"]
  ])) with
  | Except.error err => hasContext "max expects each collection element to be a single numeric value; item 0 was string value \"hello\"" err && innermostIsBadArity err
  | _ => false

#guard test128

-- Test 129: plain-call avg averages expanded range items
def test129 : Bool :=
  match runFlat (.algorithmExpr (alg [] [] [] [
    .call (resolve "avg") [
      .call (resolve "range") [.num 1, .num 5]
    ]
  ])) with
  | Except.ok [3] => true
  | _ => false

#guard test129

-- Test 130: dot-call avg uses receiver injection with no explicit args
def test130 : Bool :=
  match runFlat (.algorithmExpr (alg [] [] [] [
    .dotCall
      (.call (resolve "range") [.num 1, .num 5])
      "avg"
      none
  ])) with
  | Except.ok [3] => true
  | _ => false

#guard test130

-- Test 131: descending ranges also expand for plain-call avg
def test131 : Bool :=
  match runFlat (.algorithmExpr (alg [] [] [] [
    .call (resolve "avg") [
      .call (resolve "range") [.num 5, .num 1]
    ]
  ])) with
  | Except.ok [3] => true
  | _ => false

#guard test131

-- Test 132: avg composes with filter over kept top-level elements
def test132 : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("IsEven", isEvenAlg93)] [
    .dotCall
      (.dotCall
        (.call (resolve "range") [.num 1, .num 10])
        "filter"
        (some [.resolve "IsEven"]))
      "avg"
      none
  ])) with
  | Except.ok [6] => true
  | _ => false

#guard test132

-- Test 133: avg composes with map and averages mapped top-level elements
def test133 : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("Double", doubleAlg85)] [
    .dotCall
      (.dotCall
        (.call (resolve "range") [.num 1, .num 4])
        "map"
        (some [.resolve "Double"]))
      "avg"
      none
  ])) with
  | Except.ok [5] => true
  | _ => false

#guard test133

-- Test 134: plain-call avg requires a non-empty collection
def test134 : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("AlwaysFalse", alwaysFalseAlg66a)] [
    .call (resolve "avg") [
      .call (resolve "filter") [
        .call (resolve "range") [.num 1, .num 4],
        .resolve "AlwaysFalse"
      ]
    ]
  ])) with
  | Except.error err => hasContext "avg requires a non-empty collection" err && innermostIsBadArity err
  | _ => false

#guard test134

-- Test 135: a single atomic value is treated as a one-element collection
def test135 : Bool :=
  match runFlat (.algorithmExpr (alg [] [] [] [
    .call (resolve "avg") [.num 5]
  ])) with
  | Except.ok [5] => true
  | _ => false

#guard test135

-- Test 136: sequenceValue top-level elements are rejected rather than flattened
def test136 : Bool :=
  let sequenceValuePairs := .capture [
    .capture [.num 1, .num 2],
    .capture [.num 3, .num 4]
  ]
  match runResult (.algorithmExpr (alg [] [] [] [
    .call (resolve "avg") [sequenceValuePairs]
  ])) with
  | Except.error err => hasContext "avg expects each collection element to be a single numeric value; item 0 was sequence value" err && innermostIsBadArity err
  | _ => false

#guard test136

-- Test 137: string elements are rejected by avg
def test137 : Bool :=
  match runResult (.algorithmExpr (alg [] [] [] [
    .call (resolve "avg") [.stringLiteral "hello"]
  ])) with
  | Except.error err => hasContext "avg expects each collection element to be a single numeric value; item 0 was string value \"hello\"" err && innermostIsBadArity err
  | _ => false

#guard test137

--------------------------------------------------------------------------------
-- order builtins tests
--------------------------------------------------------------------------------

-- Test 138: ordinary builtin-call order sorts direct multi-argument inputs ascending and preserves duplicates
def test138 : Bool :=
  match runFlat (.algorithmExpr (alg [] [] [] [
    .call (resolve "order") [sequenceItems [
      .num 3,
      .num 4,
      .num 2,
      .num 1,
      .num 3,
      .num 3
    ]]
  ])) with
  | Except.ok [1, 2, 3, 3, 3, 4] => true
  | _ => false

#guard test138

-- Test 139: dot-call order sorts property output ascending
def test139 : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("Values", alg [] [] [] [.num 3, .num 4, .num 2, .num 1, .num 3, .num 3])] [
    .dotCall (.resolve "Values") "order" none
  ])) with
  | Except.ok [1, 2, 3, 3, 3, 4] => true
  | _ => false

#guard test139

-- Test 140: dot-call orderDesc sorts descending and preserves duplicates
def test140 : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("Values", alg [] [] [] [.num 3, .num 4, .num 2, .num 1, .num 3, .num 3])] [
    .dotCall (.resolve "Values") "orderDesc" none
  ])) with
  | Except.ok [4, 3, 3, 3, 2, 1] => true
  | _ => false

#guard test140

-- Test 141: sorting a descending range returns ascending output for order
def test141 : Bool :=
  match runFlat (.algorithmExpr (alg [] [] [] [
    .dotCall
      (.call (resolve "range") [.num 5, .num 1])
      "order"
      none
  ])) with
  | Except.ok [1, 2, 3, 4, 5] => true
  | _ => false

#guard test141

-- Test 142: dot-call order preserves empty receiver outputs
def test142 : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("AlwaysFalse", alwaysFalseAlg66a)] [
    .dotCall
      (.call (resolve "filter") [
        .call (resolve "range") [.num 1, .num 4],
        .resolve "AlwaysFalse"
      ])
      "order"
      none
  ])) with
  | Except.ok [] => true
  | _ => false

#guard test142

-- Test 143: unsupported sortable elements are rejected by order
def test143 : Bool :=
  match runResult (.algorithmExpr (alg [] [] [] [
    .call (resolve "order") [
      .capture [.num 1, .stringLiteral "hello"]
    ]
  ])) with
  | Except.error err => hasContext "order expects each collection element to be a single numeric value; item 1 was string value \"hello\"" err && innermostIsBadArity err
  | _ => false

#guard test143

--------------------------------------------------------------------------------
-- first/last builtin tests
--------------------------------------------------------------------------------

-- Test 144: plain-call first returns the first expanded range item
def test144 : Bool :=
  match runFlat (.algorithmExpr (alg [] [] [] [
    .call (resolve "first") [
      .call (resolve "range") [.num 1, .num 5]
    ]
  ])) with
  | Except.ok [1] => true
  | _ => false

#guard test144

-- Test 145: dot-call first uses receiver injection with no explicit args
def test145 : Bool :=
  match runFlat (.algorithmExpr (alg [] [] [] [
    .dotCall
      (.call (resolve "range") [.num 1, .num 5])
      "first"
      none
  ])) with
  | Except.ok [1] => true
  | _ => false

#guard test145

-- Test 146: plain-call last returns the last expanded range item
def test146 : Bool :=
  match runFlat (.algorithmExpr (alg [] [] [] [
    .call (resolve "last") [
      .call (resolve "range") [.num 1, .num 5]
    ]
  ])) with
  | Except.ok [5] => true
  | _ => false

#guard test146

-- Test 147: dot-call last uses receiver injection with no explicit args
def test147 : Bool :=
  match runFlat (.algorithmExpr (alg [] [] [] [
    .dotCall
      (.call (resolve "range") [.num 1, .num 5])
      "last"
      none
  ])) with
  | Except.ok [5] => true
  | _ => false

#guard test147

-- Test 148: first returns the first item of the grouped collection (opened by the one-level collection view)
def test148 : Bool :=
  let sequenceValuePairs := .capture [
    .capture [.num 1, .num 2],
    .capture [.num 3, .num 4]
  ]
  match runResult (.algorithmExpr (alg [] [] [] [
    .call (resolve "first") [sequenceValuePairs]
  ])) with
  | Except.ok (.sequenceValue [.atom 1, .atom 2]) => true
  | _ => false

#guard test148

-- Test 149: last returns the last item of the grouped collection (opened by the one-level collection view)
def test149 : Bool :=
  let sequenceValuePairs := .capture [
    .capture [.num 1, .num 2],
    .capture [.num 3, .num 4]
  ]
  match runResult (.algorithmExpr (alg [] [] [] [
    .call (resolve "last") [sequenceValuePairs]
  ])) with
  | Except.ok (.sequenceValue [.atom 3, .atom 4]) => true
  | _ => false

#guard test149

-- Test 150: plain-call first requires a non-empty collection
def test150 : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("AlwaysFalse", alwaysFalseAlg66a)] [
    .call (resolve "first") [
      .call (resolve "filter") [
        .call (resolve "range") [.num 1, .num 4],
        .resolve "AlwaysFalse"
      ]
    ]
  ])) with
  | Except.error err => hasContext "first requires a non-empty collection" err && innermostIsBadArity err
  | _ => false

#guard test150

-- Test 151: plain-call last requires a non-empty collection
def test151 : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("AlwaysFalse", alwaysFalseAlg66a)] [
    .call (resolve "last") [
      .call (resolve "filter") [
        .call (resolve "range") [.num 1, .num 4],
        .resolve "AlwaysFalse"
      ]
    ]
  ])) with
  | Except.error err => hasContext "last requires a non-empty collection" err && innermostIsBadArity err
  | _ => false

#guard test151

-- Additional sequence-input builtin regression tests

def test151a : Bool :=
  match runFlat (.algorithmExpr (alg [] [] [] [
    .call (resolve "order") [sequenceItems [.num 3, .num 4, .num 2, .num 1, .num 3, .num 3]]
  ])) with
  | Except.ok [1, 2, 3, 3, 3, 4] => true
  | _ => false

#guard test151a

def test151b : Bool :=
  match runFlat (.algorithmExpr (alg [] [] [] [
    .call (resolve "orderDesc") [sequenceItems [.num 3, .num 4, .num 2, .num 1, .num 3, .num 3]]
  ])) with
  | Except.ok [4, 3, 3, 3, 2, 1] => true
  | _ => false

#guard test151b

def test151c : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("Values", alg [] [] [] [.num 3, .num 4, .num 2])] [
    .call (resolve "order") [sequenceItems [sequenceSpread (.resolve "Values"), .num 1, .num 3]]
  ])) with
  | Except.ok [1, 2, 3, 3, 4] => true
  | _ => false

#guard test151c

def test151d : Bool :=
  match runResult (.algorithmExpr (alg [] [] [] [
    .call (resolve "order") [sequenceItems [
      .capture [.num 1, .num 2],
      .capture [.num 3, .num 4]
    ]]
  ])) with
  | Except.error err => hasContext "order expects each collection element to be a single numeric value; item 0 was sequence value" err && innermostIsBadArity err
  | _ => false

#guard test151d

def test151e : Bool :=
  match runResult (.algorithmExpr (alg [] [] [] [
    .call (resolve "orderDesc") [sequenceItems [
      .capture [.num 1, .num 2],
      .capture [.num 3, .num 4]
    ]]
  ])) with
  | Except.error err => hasContext "orderDesc expects each collection element to be a single numeric value; item 0 was sequence value" err && innermostIsBadArity err
  | _ => false

#guard test151e

def test151f : Bool :=
  match runResult (.algorithmExpr (alg [] [] [] [
    .call (resolve "first") [sequenceItems [
      .capture [.num 1, .num 2],
      .capture [.num 3, .num 4]
    ]]
  ])) with
  | Except.ok (.sequenceValue [.atom 1, .atom 2]) => true
  | _ => false

#guard test151f

def test151g : Bool :=
  match runResult (.algorithmExpr (alg [] [] [] [
    .call (resolve "last") [sequenceItems [
      .capture [.num 1, .num 2],
      .capture [.num 3, .num 4]
    ]]
  ])) with
  | Except.ok (.sequenceValue [.atom 3, .atom 4]) => true
  | _ => false

#guard test151g

def test151h : Bool :=
  match runFlat (.algorithmExpr (alg [] [] [] [
    .call (resolve "count") [sequenceItems [.num 10, .num 20, .num 30]]
  ])) with
  | Except.ok [3] => true
  | _ => false

#guard test151h

def test151i : Bool :=
  match runFlat (.algorithmExpr (alg [] [] [] [
    .call (resolve "count") [sequenceItems [
      .capture [.num 1, .num 2],
      .capture [.num 3, .num 4]
    ]]
  ])) with
  | Except.ok [2] => true
  | _ => false

#guard test151i

def test151j : Bool :=
  match runFlat (.algorithmExpr (alg [] [] [] [
    .call (resolve "sum") [sequenceItems [.num 10, .num 20, .num 30]]
  ])) with
  | Except.ok [60] => true
  | _ => false

#guard test151j

def test151k : Bool :=
  match runFlat (.algorithmExpr (alg [] [] [] [
    .call (resolve "min") [sequenceItems [.num 10, .num 4, .num 7]]
  ])) with
  | Except.ok [4] => true
  | _ => false

#guard test151k

def test151l : Bool :=
  match runFlat (.algorithmExpr (alg [] [] [] [
    .call (resolve "max") [sequenceItems [.num 10, .num 4, .num 7]]
  ])) with
  | Except.ok [10] => true
  | _ => false

#guard test151l

def test151m : Bool :=
  match runFlat (.algorithmExpr (alg [] [] [] [
    .call (resolve "avg") [sequenceItems [.num 10, .num 20, .num 30]]
  ])) with
  | Except.ok [20] => true
  | _ => false

#guard test151m

def test151n : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("KeepFourSequenceValue", keepFourSequenceValueAlg66c)] [
    .call (resolve "filter") [
      sequenceItems [.num 1, .num 2, sequenceSpread (.call (resolve "range") [.num 3, .num 6])],
      .resolve "KeepFourSequenceValue"
    ]
  ])) with
  | Except.ok [] => true
  | _ => false

#guard test151n

def test151o : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("MarkThreeSequenceValue", markThreeSequenceValueAlg66e)] [
    .call (resolve "map") [
      sequenceItems [.num 1, sequenceSpread (.call (resolve "range") [.num 2, .num 4])],
      .resolve "MarkThreeSequenceValue"
    ]
  ])) with
  | Except.ok [0, 0, 0, 0] => true
  | _ => false

#guard test151o

-- SequenceValue source `map((1, range(2, 4)*), MarkThreeSequenceValue)`: spread
-- contributes inside the single grouped value, opened by the collection view.
def test151ob : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("MarkThreeSequenceValue", markThreeSequenceValueAlg66e)] [
    .call (resolve "map") [
      sequenceItems [.num 1, sequenceSpread (.call (resolve "range") [.num 2, .num 4])],
      .resolve "MarkThreeSequenceValue"
    ]
  ])) with
  | Except.ok [0, 0, 0, 0] => true
  | _ => false

#guard test151ob

-- SequenceValue source `filter((1, range(2, 4)*), MarkThreeSequenceValue)`: spread
-- contributes inside the single grouped value, opened by the collection view.
def test151oc : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("MarkThreeSequenceValue", markThreeSequenceValueAlg66e)] [
    .call (resolve "filter") [
      sequenceItems [.num 1, sequenceSpread (.call (resolve "range") [.num 2, .num 4])],
      .resolve "MarkThreeSequenceValue"
    ]
  ])) with
  | Except.ok [] => true
  | _ => false

#guard test151oc

def markSequenceValueRangeDirectCallAlg151oa : Algorithm :=
  .conditional none [] [
    ⟨ .sequenceValue [.sequenceValue [.bind "a", .bind "b", .bind "c"]],
      alg [] [] [] [.num 1] ⟩,
    ⟨ .bind "x", alg [] [] [] [.num 0] ⟩
  ]

-- `range(1, 3)` is now an exact list value, and multi-clause conditional groups
-- match sequence values only (list patterns are deferred), so the list argument
-- takes the fallback clause.
def test151oa : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("MarkSequenceValueRange", markSequenceValueRangeDirectCallAlg151oa)] [
    .call (resolve "MarkSequenceValueRange") [
      .call (resolve "range") [.num 1, .num 3]
    ]
  ])) with
  | Except.ok [0] => true
  | _ => false

#guard test151oa

def test151p : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("AddItemCount", addItemCountAlg80c)] [
    .call (resolve "reduce") [
      sequenceItems [.num 1, .num 2, sequenceSpread (.call (resolve "range") [.num 3, .num 4])],
      .resolve "AddItemCount",
      .num 0
    ]
  ])) with
  | Except.ok [4] => true
  | _ => false

#guard test151p

def addSequenceValueRangeAlg151pb : Algorithm :=
  .conditional none [] [
    ⟨ .sequenceValue [.sequenceValue [.bind "a", .bind "b", .bind "c"], .bind "acc"],
      alg [] [] [] [.binary .add (.param "acc") (.num 100)] ⟩,
    ⟨ .sequenceValue [.bind "x", .bind "acc"],
      alg [] [] [] [.binary .add (.param "acc") (.param "x")] ⟩
  ]

def test151pb : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("AddSequenceValueRange", addSequenceValueRangeAlg151pb)] [
    .call (resolve "reduce") [
      sequenceItems [.num 1, sequenceSpread (.call (resolve "range") [.num 2, .num 4])],
      .resolve "AddSequenceValueRange",
      .num 0
    ]
  ])) with
  | Except.ok [10] => true
  | _ => false

#guard test151pb

-- SequenceValue source `reduce((1, range(2, 4)*), AddSequenceValueRange, 0)`:
-- the spread marker contributes inside the single grouped value, opened by the collection view.
def test151pc : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("AddSequenceValueRange", addSequenceValueRangeAlg151pb)] [
    .call (resolve "reduce") [
      sequenceItems [.num 1, sequenceSpread (.call (resolve "range") [.num 2, .num 4])],
      .resolve "AddSequenceValueRange",
      .num 0
    ]
  ])) with
  | Except.ok [10] => true
  | _ => false

#guard test151pc

def test151q : Bool :=
  match runResult (.algorithmExpr (alg [] [] [] [
    .call (resolve "order") [
      sequenceItems [.capture [.num 3, .num 4, .num 2, .num 1, .num 3, .num 3], .num 0]
    ]
  ])) with
  | Except.error err => hasContext "order expects each collection element to be a single numeric value; item 0 was sequence value" err && innermostIsBadArity err
  | _ => false

#guard test151q

def test151r : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("Values", alg [] [] [] [.num 3, .num 4, .num 2, .num 1, .num 3, .num 3])] [
    .call (resolve "order") [.resolve "Values"]
  ])) with
  | Except.ok [1, 2, 3, 3, 3, 4] => true
  | _ => false

#guard test151r

def test151s : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("Values", alg [] [] [] [.capture [.num 3, .num 4, .num 2]])] [
    .call (resolve "order") [.resolve "Values"]
  ])) with
  | Except.ok [2, 3, 4] => true
  | _ => false

#guard test151s

def test151t : Bool :=
  match runResult (.algorithmExpr (alg [] [] [] [
    .call (resolve "orderDesc") [
      sequenceItems [.capture [.num 3, .num 4, .num 2, .num 1, .num 3, .num 3], .num 0]
    ]
  ])) with
  | Except.error err => hasContext "orderDesc expects each collection element to be a single numeric value; item 0 was sequence value" err && innermostIsBadArity err
  | _ => false

#guard test151t

def test151u : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("Values", alg [] [] [] [.num 3, .num 4, .num 2, .num 1, .num 3, .num 3])] [
    .call (resolve "orderDesc") [.resolve "Values"]
  ])) with
  | Except.ok [4, 3, 3, 3, 2, 1] => true
  | _ => false

#guard test151u

def test151v : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("Values", alg [] [] [] [.capture [.num 3, .num 4, .num 2]])] [
    .call (resolve "orderDesc") [.resolve "Values"]
  ])) with
  | Except.ok [4, 3, 2] => true
  | _ => false

#guard test151v

def test151w : Bool :=
  match runFlat (.algorithmExpr (alg [] [] [] [
    .call (resolve "count") [
      .capture [.num 1, .num 2]
    ]
  ])) with
  | Except.ok [2] => true
  | _ => false

#guard test151w

def test151x : Bool :=
  match runResult (.algorithmExpr (alg [] [] [] [
    .call (resolve "first") [
      .capture [.num 1, .num 2]
    ]
  ])) with
  | Except.ok (.atom 1) => true
  | _ => false

#guard test151x

def test151y : Bool :=
  match runResult (.algorithmExpr (alg [] [] [] [
    .call (resolve "last") [
      .capture [.num 1, .num 2]
    ]
  ])) with
  | Except.ok (.atom 2) => true
  | _ => false

#guard test151y

-- Additional uniform sequence-extraction wrapper regressions

def test152 : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [
    ("KeepSecondEven", evenPredicateAlg19d),
    ("Values", alg [] [] [] [
      .capture [.num 1, .num 2],
      .capture [.num 1, .num 3]
    ])
  ] [
    .call (resolve "filter") [
      .resolve "Values",
      .resolve "KeepSecondEven"
    ]
  ])) with
  -- One sequence-valued item is kept; the exact-list materializer keeps it as one
  -- list element, so the result is `[(1, 2)]` (never erased to the item itself).
  | Except.ok (.listValue [.sequenceValue [.atom 1, .atom 2]]) => true
  | _ => false

#guard test152

def test153 : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("TakeValue", takePairValueAlg89),
    ("Values", alg [] [] [] [
      .capture [.num 1, .num 2],
      .capture [.num 3, .num 4]
    ])
  ] [
    .call (resolve "map") [
      .resolve "Values",
      .resolve "TakeValue"
    ]
  ])) with
  | Except.ok [2, 4] => true
  | _ => false

#guard test153

def test154 : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("AddValue", reduceSequenceValueItemAlg79),
    ("Values", alg [] [] [] [
      .capture [.num 1, .num 2],
      .capture [.num 3, .num 4]
    ])
  ] [
    .call (resolve "reduce") [
      .resolve "Values",
      .resolve "AddValue",
      .num 0
    ]
  ])) with
  | Except.ok [6] => true
  | _ => false

#guard test154

def test155 : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("Values", alg [] [] [] [
      .capture [.num 1, .num 2, .num 3]
    ])
  ] [
    .call (resolve "count") [.resolve "Values"]
  ])) with
  | Except.ok [3] => true
  | _ => false

#guard test155

def test156 : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("Values", alg [] [] [] [.num 1, .num 2, .num 3])
  ] [
    .call (resolve "count") [.resolve "Values"]
  ])) with
  | Except.ok [3] => true
  | _ => false

#guard test156

def test157 : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [
    ("Values", alg [] [] [] [
      .capture [.num 1, .num 2]
    ])
  ] [
    .call (resolve "first") [.resolve "Values"]
  ])) with
  | Except.ok (.atom 1) => true
  | _ => false

#guard test157

def test158 : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [
    ("Values", alg [] [] [] [
      .capture [.num 1, .num 2]
    ])
  ] [
    .call (resolve "last") [.resolve "Values"]
  ])) with
  | Except.ok (.atom 2) => true
  | _ => false

#guard test158

def test159 : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [
    ("Values", alg [] [] [] [
      .capture [.num 10, .num 20, .num 30]
    ])
  ] [
    .call (resolve "sum") [.resolve "Values"]
  ])) with
  | Except.ok (.atom 60) => true
  | _ => false

#guard test159

def test160 : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [
    ("Values", alg [] [] [] [
      .capture [.num 10, .num 20, .num 30]
    ])
  ] [
    .call (resolve "min") [.resolve "Values"]
  ])) with
  | Except.ok (.atom 10) => true
  | _ => false

#guard test160

def test161 : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [
    ("Values", alg [] [] [] [
      .capture [.num 10, .num 20, .num 30]
    ])
  ] [
    .call (resolve "max") [.resolve "Values"]
  ])) with
  | Except.ok (.atom 30) => true
  | _ => false

#guard test161

def test162 : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [
    ("Values", alg [] [] [] [
      .capture [.num 10, .num 20, .num 30]
    ])
  ] [
    .call (resolve "avg") [.resolve "Values"]
  ])) with
  | Except.ok (.atom 20) => true
  | _ => false

#guard test162

def test163 : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("Values", alg [] [] [] [.num 10, .num 20, .num 30])
  ] [
    .call (resolve "sum") [.resolve "Values"]
  ])) with
  | Except.ok [60] => true
  | _ => false

#guard test163

def test164 : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("Values", alg [] [] [] [.num 10, .num 4, .num 7])
  ] [
    .call (resolve "min") [.resolve "Values"]
  ])) with
  | Except.ok [4] => true
  | _ => false

#guard test164

def test165 : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("Values", alg [] [] [] [.num 10, .num 4, .num 7])
  ] [
    .call (resolve "max") [.resolve "Values"]
  ])) with
  | Except.ok [10] => true
  | _ => false

#guard test165

def test166 : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("Values", alg [] [] [] [.num 10, .num 20, .num 30])
  ] [
    .call (resolve "avg") [.resolve "Values"]
  ])) with
  | Except.ok [20] => true
  | _ => false

#guard test166

def test167 : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("AlwaysFalse", alwaysFalseAlg66a)] [
    .dotCall
      (.call (resolve "filter") [
        .call (resolve "range") [.num 1, .num 4],
        .resolve "AlwaysFalse"
      ])
      "orderDesc"
      none
  ])) with
  | Except.ok [] => true
  | _ => false

#guard test167

-- avg(1, 2) = 3.tdiv 2 = 1 in the Lean Int core. The decimal runtime returns the
-- exact fractional average (1.5) instead; the integer result is a Lean model
-- limitation, not the C# runtime contract.
def test168 : Bool :=
  match runFlat (.algorithmExpr (alg [] [] [] [
    .call (resolve "avg") [sequenceItems [.num 1, .num 2]]
  ])) with
  | Except.ok [1] => true
  | _ => false

#guard test168

-- avg truncates its quotient toward zero (Int.tdiv), matching the truncating
-- division convention of `div`/`mod`: avg(-1, -2) = (-3).tdiv 2 = -1.
-- The decimal runtime keeps the exact fractional average (-1.5) instead.
def test169 : Bool :=
  match runFlat (.algorithmExpr (alg [] [] [] [
    .call (resolve "avg") [sequenceItems [.num (-1), .num (-2)]]
  ])) with
  | Except.ok [-1] => true
  | _ => false

#guard test169

def test170 : Bool :=
  match runResult (.algorithmExpr (alg [] [] [] [
    .call (resolve "order") [sequenceItems [
      .num 1,
      .capture [.num 2, .num 3]
    ]]
  ])) with
  | Except.error err => hasContext "order expects each collection element to be a single numeric value; item 1 was sequence value" err && innermostIsBadArity err
  | _ => false

#guard test170

def test171 : Bool :=
  match runResult (.algorithmExpr (alg [] [] [] [
    .call (resolve "orderDesc") [sequenceItems [
      .num 1,
      .capture [.num 2, .num 3]
    ]]
  ])) with
  | Except.error err => hasContext "orderDesc expects each collection element to be a single numeric value; item 1 was sequence value" err && innermostIsBadArity err
  | _ => false

#guard test171

def test172 : Bool :=
  match runResult (.algorithmExpr (alg [] [] [] [
    .call (resolve "min") [sequenceItems [
      .num 1,
      .capture [.num 2, .num 3]
    ]]
  ])) with
  | Except.error err => hasContext "min expects each collection element to be a single numeric value; item 1 was sequence value" err && innermostIsBadArity err
  | _ => false

#guard test172

def test173 : Bool :=
  match runResult (.algorithmExpr (alg [] [] [] [
    .call (resolve "max") [sequenceItems [
      .num 1,
      .capture [.num 2, .num 3]
    ]]
  ])) with
  | Except.error err => hasContext "max expects each collection element to be a single numeric value; item 1 was sequence value" err && innermostIsBadArity err
  | _ => false

#guard test173

def test174 : Bool :=
  match runResult (.algorithmExpr (alg [] [] [] [
    .call (resolve "sum") [sequenceItems [
      .num 1,
      .capture [.num 2, .num 3]
    ]]
  ])) with
  | Except.error err => hasContext "sum expects each collection element to be a single numeric value; item 1 was sequence value" err && innermostIsBadArity err
  | _ => false

#guard test174

def test175 : Bool :=
  match runResult (.algorithmExpr (alg [] [] [] [
    .call (resolve "avg") [sequenceItems [
      .num 1,
      .capture [.num 2, .num 3]
    ]]
  ])) with
  | Except.error err => hasContext "avg expects each collection element to be a single numeric value; item 1 was sequence value" err && innermostIsBadArity err
  | _ => false

#guard test175

def test176 : Bool :=
  match runFlat (.algorithmExpr (alg [] [] [] [
    .call (resolve "take") [
      sequenceItems [.num 1, .num 2, .num 3, .num 4, .num 5],
      .num 3
    ]
  ])) with
  | Except.ok [1, 2, 3] => true
  | _ => false

#guard test176

def test177 : Bool :=
  match runFlat (.algorithmExpr (alg [] [] [] [
    .call (resolve "skip") [
      sequenceItems [.num 1, .num 2, .num 3, .num 4, .num 5],
      .num 3
    ]
  ])) with
  | Except.ok [4, 5] => true
  | _ => false

#guard test177

def test178 : Bool :=
  match runFlat (.algorithmExpr (alg [] [] [] [
    .call (resolve "take") [
      sequenceItems [.num 1, .num 2, .num 3],
      .num 0
    ]
  ])) with
  | Except.ok [] => true
  | _ => false

#guard test178

def test179 : Bool :=
  match runFlat (.algorithmExpr (alg [] [] [] [
    .call (resolve "skip") [
      sequenceItems [.num 1, .num 2, .num 3],
      .num 0
    ]
  ])) with
  | Except.ok [1, 2, 3] => true
  | _ => false

#guard test179

def test180 : Bool :=
  match runFlat (.algorithmExpr (alg [] [] [] [
    .call (resolve "take") [
      sequenceItems [.num 1, .num 2, .num 3],
      .num (-2)
    ]
  ])) with
  | Except.ok [] => true
  | _ => false

#guard test180

def test181 : Bool :=
  match runFlat (.algorithmExpr (alg [] [] [] [
    .call (resolve "skip") [
      sequenceItems [.num 1, .num 2, .num 3],
      .num (-2)
    ]
  ])) with
  | Except.ok [1, 2, 3] => true
  | _ => false

#guard test181

def test182 : Bool :=
  match runFlat (.algorithmExpr (alg [] [] [] [
    .call (resolve "take") [
      sequenceItems [.num 1, .num 2, .num 3],
      .num 10
    ]
  ])) with
  | Except.ok [1, 2, 3] => true
  | _ => false

#guard test182

def test183 : Bool :=
  match runFlat (.algorithmExpr (alg [] [] [] [
    .call (resolve "skip") [
      sequenceItems [.num 1, .num 2, .num 3],
      .num 10
    ]
  ])) with
  | Except.ok [] => true
  | _ => false

#guard test183

def test184 : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("AlwaysFalse", alwaysFalseAlg66a)] [
    .call (resolve "take") [
      .call (resolve "filter") [
        .call (resolve "range") [.num 1, .num 4],
        .resolve "AlwaysFalse"
      ],
      .num 3
    ]
  ])) with
  | Except.ok [] => true
  | _ => false

#guard test184

def test185 : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("AlwaysFalse", alwaysFalseAlg66a)] [
    .call (resolve "skip") [
      .call (resolve "filter") [
        .call (resolve "range") [.num 1, .num 4],
        .resolve "AlwaysFalse"
      ],
      .num 3
    ]
  ])) with
  | Except.ok [] => true
  | _ => false

#guard test185

def test186 : Bool :=
  match runResult (.algorithmExpr (alg [] [] [] [
    .call (resolve "take") [sequenceItems [
      .capture [.num 1, .num 2],
      .capture [.num 3, .num 4]],
      .num 1
    ]
  ])) with
  -- Taking one sequence-valued item keeps it as one exact list element:
  -- the result is `[(1, 2)]` (`first` still selects the item itself).
  | Except.ok (.listValue [.sequenceValue [.atom 1, .atom 2]]) => true
  | _ => false

#guard test186

def test187 : Bool :=
  match runResult (.algorithmExpr (alg [] [] [] [
    .call (resolve "skip") [sequenceItems [
      .capture [.num 1, .num 2],
      .capture [.num 3, .num 4]],
      .num 1
    ]
  ])) with
  -- Skipping to one remaining sequence-valued item keeps it as one exact list
  -- element: the result is `[(3, 4)]` (`last` still selects the item itself).
  | Except.ok (.listValue [.sequenceValue [.atom 3, .atom 4]]) => true
  | _ => false

#guard test187

-- Regression block for the exact-list builtin result boundary:
-- `T = take(((1, 2), (3, 4)), 1)` is the exact list `[(1, 2)]` — equal to the
-- list literal `[(1, 2)]`, NOT equal to the sequence `(1, 2)` (or its grouping
-- form `((1, 2))`), and counted as ONE kept item by `count(T)` and `T.count`
-- alike (count opens exactly the one list boundary).
def takeSingleKeptItemProgram (output : KatLang.Expr) : KatLang.Expr :=
  .algorithmExpr (algPrivate [] [] [
    ("T", alg [] [] [] [
      .call (resolve "take") [
        sequenceItems [
          .capture [.num 1, .num 2],
          .capture [.num 3, .num 4]
        ],
        .num 1
      ]
    ])
  ] [output])

def takeSingleKeptItemIsExactListValue : Bool :=
  match runResult (takeSingleKeptItemProgram (.resolve "T")) with
  | Except.ok (.listValue [.sequenceValue [.atom 1, .atom 2]]) => true
  | _ => false

#guard takeSingleKeptItemIsExactListValue

def takeSingleKeptItemCount : Bool :=
  match runResult (takeSingleKeptItemProgram
      (.call (resolve "count") [.resolve "T"])) with
  | Except.ok (.atom 1) => true
  | _ => false

#guard takeSingleKeptItemCount

def takeSingleKeptItemDotCount : Bool :=
  match runResult (takeSingleKeptItemProgram (.dotCall (.resolve "T") "count" none)) with
  | Except.ok (.atom 1) => true
  | _ => false

#guard takeSingleKeptItemDotCount

def takeSingleKeptItemEqualsListLiteral : Bool :=
  match runResult (takeSingleKeptItemProgram
      (.binary .eq (.resolve "T") (.listLiteral [sequenceItems [.num 1, .num 2]]))) with
  | Except.ok (.atom 1) => true
  | _ => false

#guard takeSingleKeptItemEqualsListLiteral

def takeSingleKeptItemNotEqualFlatLiteral : Bool :=
  match runResult (takeSingleKeptItemProgram
      (.binary .eq (.resolve "T") (sequenceItems [.num 1, .num 2]))) with
  | Except.ok (.atom 0) => true
  | _ => false

#guard takeSingleKeptItemNotEqualFlatLiteral

def takeSingleKeptItemNotEqualWrappedLiteral : Bool :=
  match runResult (takeSingleKeptItemProgram
      (.binary .eq (.resolve "T")
        (.capture [sequenceItems [.num 1, .num 2]]))) with
  | Except.ok (.atom 0) => true
  | _ => false

#guard takeSingleKeptItemNotEqualWrappedLiteral

-- A single kept empty-sequence item stays one exact list element:
-- `distinct(((), ()))` dedups the two equal `()` items of the one grouped
-- collection argument to one kept item and yields the exact list `[()]`
-- (count 1) — never erased to `()` itself. The ungrouped spelling
-- `distinct((), ())` is a two-argument arity error under `distinct(collection)`.
def distinctSingleKeptEmptyItemStaysExactElement : Bool :=
  match runResult (.call (resolve "distinct") [.capture [.emptySequence 0, .emptySequence 0]]) with
  | Except.ok (.listValue [.sequenceValue []]) => true
  | _ => false

#guard distinctSingleKeptEmptyItemStaysExactElement

def distinctTwoEmptyArgumentsIsArityError : Bool :=
  match runResult (.call (resolve "distinct") [.emptySequence 0, .emptySequence 0]) with
  | Except.error err => innermostIsArityMismatch 1 2 err
  | _ => false

#guard distinctTwoEmptyArgumentsIsArityError

def distinctSingleKeptEmptyItemCountsOne : Bool :=
  match runResult (.call (resolve "count") [
    .call (resolve "distinct") [.capture [.emptySequence 0, .emptySequence 0]]
  ]) with
  | Except.ok (.atom 1) => true
  | _ => false

#guard distinctSingleKeptEmptyItemCountsOne

def distinctSingleKeptEmptyItemNotEqualEmpty : Bool :=
  match runResult (.binary .eq
      (.call (resolve "distinct") [.capture [.emptySequence 0, .emptySequence 0]])
      (.emptySequence 0)) with
  | Except.ok (.atom 0) => true
  | _ => false

#guard distinctSingleKeptEmptyItemNotEqualEmpty

-- Multiple kept empty-sequence items keep their sibling boundaries as exact list
-- elements. `take(((), ()), 2)` is the two-element list `[(), ()]` with count 2 —
-- the materializer is exact and never collapses or drops meaningful sibling items.
def takeMultipleEmptyItemsPreservesSiblingBoundaries : Bool :=
  match runResult (.call (resolve "take") [.capture [.emptySequence 0, .emptySequence 0], .num 2]) with
  | Except.ok (.listValue [.sequenceValue [], .sequenceValue []]) => true
  | _ => false

#guard takeMultipleEmptyItemsPreservesSiblingBoundaries

def takeMultipleEmptyItemsCountsTwo : Bool :=
  match runResult (.call (resolve "count") [
    .call (resolve "take") [.capture [.emptySequence 0, .emptySequence 0], .num 2]
  ]) with
  | Except.ok (.atom 2) => true
  | _ => false

#guard takeMultipleEmptyItemsCountsTwo

-- The collection-result materializer is EXACT, unlike the canonical arity
-- combiners: zero items form `[]`, one item forms `[item]` (never erased),
-- nested structure is preserved raw, and the emitted count is always 1.
#guard KatLang.makeCollectionListResult [] == (Result.listValue [], 1)
#guard KatLang.makeCollectionListResult [.atom 7] == (Result.listValue [.atom 7], 1)
#guard KatLang.makeCollectionListResult [.str "a"] == (Result.listValue [.str "a"], 1)
#guard KatLang.makeCollectionListResult [.sequenceValue [.atom 1, .atom 2]]
  == (Result.listValue [.sequenceValue [.atom 1, .atom 2]], 1)
#guard KatLang.makeCollectionListResult [.sequenceValue []]
  == (Result.listValue [.sequenceValue []], 1)
#guard KatLang.makeCollectionListResult [.sequenceValue [], .sequenceValue []]
  == (Result.listValue [.sequenceValue [], .sequenceValue []], 1)
#guard KatLang.makeCollectionListResult [.listValue [.atom 1]]
  == (Result.listValue [.listValue [.atom 1]], 1)

def test188 : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [
    ("Values", alg [] [] [] [
      .capture [.num 1, .num 2, .num 3]
    ])
  ] [
    .call (resolve "take") [
      .resolve "Values",
      .num 1
    ]
  ])) with
  | Except.ok (.listValue [.atom 1]) => true
  | _ => false

#guard test188

def test189 : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("Values", alg [] [] [] [.num 1, .num 2, .num 3])
  ] [
    .call (resolve "take") [
      .resolve "Values",
      .num 1
    ]
  ])) with
  | Except.ok [1] => true
  | _ => false

#guard test189

def test190 : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("Values", alg [] [] [] [
      .capture [.num 1, .num 2, .num 3]
    ])
  ] [
    .call (resolve "skip") [
      .resolve "Values",
      .num 1
    ]
  ])) with
  | Except.ok [2, 3] => true
  | _ => false

#guard test190

def test191 : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("Values", alg [] [] [] [.num 1, .num 2, .num 3])
  ] [
    .call (resolve "skip") [
      .resolve "Values",
      .num 1
    ]
  ])) with
  | Except.ok [2, 3] => true
  | _ => false

#guard test191

def test192 : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("AlwaysFalse", alwaysFalseAlg66a)] [
    .call (resolve "take") [
      sequenceItems [.num 1, .num 2],
      .call (resolve "filter") [
        .call (resolve "range") [.num 1, .num 4],
        .resolve "AlwaysFalse"
      ]
    ]
  ])) with
  | Except.error err => hasContext "take count must be exactly one whole-number value" err && innermostIsBadArity err
  | _ => false

#guard test192

def test193 : Bool :=
  match runResult (.algorithmExpr (alg [] [] [] [
    .call (resolve "take") [
      sequenceItems [.num 3, .num 4],
      .capture [.num 1, .num 2]
    ]
  ])) with
  | Except.error err => hasContext "take count must be exactly one whole-number value" err && innermostIsBadArity err
  | _ => false

#guard test193

def test194 : Bool :=
  match runResult (.algorithmExpr (alg [] [] [] [
    .call (resolve "skip") [
      sequenceItems [.num 1, .num 2],
      .stringLiteral "hello"
    ]
  ])) with
  | Except.error err => hasContext "skip count must be exactly one whole-number value" err && innermostIsBadArity err
  | _ => false

#guard test194

def test195 : Bool :=
  match runFlat (.algorithmExpr (alg [] [] [] [
    .call (resolve "skip") [
      sequenceItems [.num 3, .num 4, .num 1],
      .num 2
    ]
  ])) with
  | Except.ok [1] => true
  | _ => false

#guard test195

def test196 : Bool :=
  match runFlat (.algorithmExpr (alg [] [] [] [
    .call (resolve "distinct") [sequenceItems [
      .num 3,
      .num 1,
      .num 3,
      .num 2,
      .num 1,
      .num 2]
    ]
  ])) with
  | Except.ok [3, 1, 2] => true
  | _ => false

#guard test196

def test197 : Bool :=
  match runFlat (.algorithmExpr (alg [] [] [] [
    .call (resolve "distinct") [sequenceItems [
      .num 4,
      .num 4,
      .num 4,
      .num 4]
    ]
  ])) with
  | Except.ok [4] => true
  | _ => false

#guard test197

def test198 : Bool :=
  match runFlat (.algorithmExpr (alg [] [] [] [
    .call (resolve "distinct") [sequenceItems [
      .num 1,
      .num 2,
      .num 3]
    ]
  ])) with
  | Except.ok [1, 2, 3] => true
  | _ => false

#guard test198

def test199 : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("AlwaysFalse", alwaysFalseAlg66a)] [
    .call (resolve "distinct") [
      .call (resolve "filter") [
        .call (resolve "range") [.num 1, .num 4],
        .resolve "AlwaysFalse"
      ]
    ]
  ])) with
  | Except.ok [] => true
  | _ => false

#guard test199

def test200 : Bool :=
  match runResult (.algorithmExpr (alg [] [] [] [
    .call (resolve "distinct") [sequenceItems [
      .capture [.num 1, .num 2],
      .capture [.num 1, .num 2],
      .capture [.num 3, .num 4]]
    ]
  ])) with
  | Except.ok (.listValue [
      .sequenceValue [.atom 1, .atom 2],
      .sequenceValue [.atom 3, .atom 4]
    ]) => true
  | _ => false

#guard test200

def test201 : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [
    ("Values", alg [] [] [] [
      .capture [
        .capture [.num 1, .num 2],
        .capture [.num 1, .num 2],
        .capture [.num 3, .num 4]
      ]
    ])
  ] [
    .call (resolve "distinct") [
      .resolve "Values"
    ]
  ])) with
  | Except.ok (.listValue [
      .sequenceValue [.atom 1, .atom 2],
      .sequenceValue [.atom 3, .atom 4]
    ]) => true
  | _ => false

#guard test201

def test202 : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [
    ("Values", alg [] [] [] [
      .capture [.num 1, .num 2],
      .capture [.num 1, .num 2],
      .capture [.num 3, .num 4]
    ])
  ] [
    .call (resolve "distinct") [
      .resolve "Values"
    ]
  ])) with
  | Except.ok (.listValue [
      .sequenceValue [.atom 1, .atom 2],
      .sequenceValue [.atom 3, .atom 4]
    ]) => true
  | _ => false

#guard test202

def test203 : Bool :=
  match runFlat (.dotCall (.capture [
    .num 3,
    .num 5,
    .num 3,
    .num 6,
    .num 3
  ]) "order" none) with
  | Except.ok [3, 3, 3, 5, 6] => true
  | _ => false

#guard test203

def test204 : Bool :=
  match runFlat (.dotCall (.capture [
    .num 3,
    .num 5,
    .num 3,
    .num 6,
    .num 3
  ]) "orderDesc" none) with
  | Except.ok [6, 5, 3, 3, 3] => true
  | _ => false

#guard test204

def test205 : Bool :=
  match runFlat (.dotCall (.capture [
    .num 3,
    .num 5,
    .num 3,
    .num 6,
    .num 3
  ]) "count" none) with
  | Except.ok [5] => true
  | _ => false

#guard test205

def test206 : Bool :=
  match runFlat (.dotCall (.capture [
    .num 3,
    .num 5,
    .num 3
  ]) "sum" none) with
  | Except.ok [11] => true
  | _ => false

#guard test206

def test207 : Bool :=
  match runFlat (.dotCall (.capture [
    .num 1,
    .num 2,
    .num 1,
    .num 3
  ]) "distinct" none) with
  | Except.ok [1, 2, 3] => true
  | _ => false

#guard test207

def test208 : Bool :=
  match runFlat (.dotCall (.capture [
    .num 1,
    .num 2,
    .num 3
  ]) "take" (some [.num 2])) with
  | Except.ok [1, 2] => true
  | _ => false

#guard test208

def test209 : Bool :=
  match runFlat (.dotCall (.capture [
    .num 1,
    .num 2,
    .num 3
  ]) "skip" (some [.num 1])) with
  | Except.ok [2, 3] => true
  | _ => false

#guard test209

def test210 : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("Double", doubleAlg85)] [
    .dotCall (.capture [
      .num 1,
      .num 2,
      .num 3
    ]) "map" (some [.resolve "Double"])
  ])) with
  | Except.ok [2, 4, 6] => true
  | _ => false

#guard test210

def test211 : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("IsEven", isEvenAlg93)] [
    .dotCall (.capture [
      .num 1,
      .num 2,
      .num 3,
      .num 4
    ]) "filter" (some [.resolve "IsEven"])
  ])) with
  | Except.ok [2, 4] => true
  | _ => false

#guard test211

def test212 : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("Add", addAlg76)] [
    .dotCall (.capture [
      .num 1,
      .num 2,
      .num 3
    ]) "reduce" (some [
      .resolve "Add",
      .num 0
    ])
  ])) with
  | Except.ok [6] => true
  | _ => false

#guard test212

def test213 : Bool :=
  match runFlat (.dotCall (.algorithmExpr (algPrivate [] [] [
    ("Values", alg [] [] [] [.num 3, .num 1, .num 2])
  ] [
    .resolve "Values"
  ])) "order" none) with
  | Except.ok [1, 2, 3] => true
  | _ => false

#guard test213

def test214 : Bool :=
  let inlineReceiver := .capture [
    .num 3,
    .num 5,
    .num 3,
    .num 6,
    .num 3
  ]
  let sequenceValueReceiver := .capture [inlineReceiver]
  let namedSequenceValueWorks :=
    match runFlat (.algorithmExpr (algPrivate [] [] [
      ("Data", alg [] [] [] [inlineReceiver])
    ] [
      .dotCall (.resolve "Data") "order" none
    ])) with
    | Except.ok [3, 3, 3, 5, 6] => true
    | _ => false
  let inlineReceiverWorks :=
    match runFlat (.dotCall inlineReceiver "order" none) with
    | Except.ok [3, 3, 3, 5, 6] => true
    | _ => false
  let doubleParenReceiverWorks :=
    match runFlat (.dotCall sequenceValueReceiver "order" none) with
    | Except.ok [3, 3, 3, 5, 6] => true
    | _ => false
  namedSequenceValueWorks && inlineReceiverWorks && doubleParenReceiverWorks

#guard test214

def test215 : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("Data", alg [] [] [] [
      .capture [.num 7, .num 6, .num 4, .num 2, .num 1],
      .capture [.num 1, .num 2, .num 3, .num 4, .num 5]
    ])
  ] [
    .call (resolve "count") [.index (.resolve "Data") (.num 0)],
    .dotCall (.index (.resolve "Data") (.num 0)) "count" none
    , .call (resolve "order") [.index (.resolve "Data") (.num 0)]
    , .dotCall (.index (.resolve "Data") (.num 0)) "order" none
  ])) with
  | Except.ok [5, 5, 1, 2, 4, 6, 7, 1, 2, 4, 6, 7] => true
  | _ => false

#guard test215

def test215a : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [
    ("A", alg [] [] [] [.num 7, .num 8])
  ] [
    .index (.resolve "A") (.num 0)
  ])) with
  | Except.ok (.atom 7) => true
  | _ => false

#guard test215a

def test215b : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [
    ("A", alg [] [] [] [
      .capture [.num 1, .num 2],
      .capture [.num 3, .num 4]
    ])
  ] [
    .index (.resolve "A") (.num 0)
  ])) with
  | Except.ok (.sequenceValue [.atom 1, .atom 2]) => true
  | _ => false

#guard test215b

def test215c : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("A", alg [] [] [] [
      .capture [.num 1, .num 2],
      .capture [.num 3, .num 4]
    ])
  ] [
    .call (resolve "count") [.index (.resolve "A") (.num 0)],
    .dotCall (.index (.resolve "A") (.num 0)) "count" none
  ])) with
  | Except.ok [2, 2] => true
  | _ => false

#guard test215c

def test215cWrappedProjectionBoundary : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("A", alg [] [] [] [
      .capture [.num 1, .num 2],
      .capture [.num 3, .num 4]
    ]),
    ("Projected", alg [] [] [] [
      .index (.resolve "A") (.num 0)
    ])
  ] [
    .call (resolve "count") [.index (.resolve "A") (.num 0)],
    .call (resolve "count") [.resolve "Projected"]
  ])) with
  | Except.ok [2, 2] => true
  | _ => false

#guard test215cWrappedProjectionBoundary

def test215d : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [
    ("A", alg [] [] [] [
      .capture [
        .capture [.num 1, .num 2],
        .capture [.num 3, .num 4]
      ],
      .capture [
        .capture [.num 5, .num 6],
        .capture [.num 7, .num 8]
      ]
    ])
  ] [
    .index (.resolve "A") (.num 0)
  ])) with
  | Except.ok (.sequenceValue [
      .sequenceValue [.atom 1, .atom 2],
      .sequenceValue [.atom 3, .atom 4]
    ]) => true
  | _ => false

#guard test215d

def test215e : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [
    ("A", alg [] [] [] [
      .capture [
        .capture [.num 1, .num 2],
        .capture [.num 3, .num 4]
      ],
      .capture [
        .capture [.num 5, .num 6],
        .capture [.num 7, .num 8]
      ]
    ])
  ] [
    .index (.index (.resolve "A") (.num 0)) (.num 1)
  ])) with
  | Except.ok (.sequenceValue [.atom 3, .atom 4]) => true
  | _ => false

#guard test215e

def test215f : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("A", alg [] [] [] [
      .capture [
        .capture [.num 1, .num 2],
        .capture [.num 3, .num 4]
      ],
      .capture [
        .capture [.num 5, .num 6],
        .capture [.num 7, .num 8]
      ]
    ])
  ] [
    .call (resolve "count") [.index (.resolve "A") (.num 0)],
    .call (resolve "count") [.index (.index (.resolve "A") (.num 0)) (.num 1)]
  ])) with
  | Except.ok [2, 2] => true
  | _ => false

#guard test215f

def test215g : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [
    ("A", alg [] [] [] [
      .capture [
        .capture [.num 1, .num 2],
        .capture [.num 3, .num 4]
      ],
      .capture [
        .capture [.num 5, .num 6],
        .capture [.num 7, .num 8]
      ]
    ])
  ] [
    .call (resolve "sum") [.index (.resolve "A") (.num 0)]
  ])) with
  | Except.error err =>
      hasContext "sum expects each collection element to be a single numeric value; item 0 was sequence value" err
        && innermostIsBadArity err
  | _ => false

#guard test215g

def test216 : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [
    ("Values", alg [] [] [] [
      .capture [.num 4, .num 5, .num 4, .num 6]
    ])
  ] [
    .dotCall (.resolve "Values") "first" none,
    .dotCall (.resolve "Values") "last" none,
    .dotCall (.resolve "Values") "distinct" none,
    .dotCall (.resolve "Values") "take" (some [.num 2]),
    .dotCall (.resolve "Values") "skip" (some [.num 1])
  ])) with
  | Except.ok (.sequenceValue [
      .atom 4,
      .atom 6,
      .listValue [.atom 4, .atom 5, .atom 6],
      .listValue [.atom 4, .atom 5],
      .listValue [.atom 5, .atom 4, .atom 6]
    ]) => true
  | _ => false

#guard test216

def test217 : Bool :=
  let runBuiltin := fun (name : String) =>
    runResult (.algorithmExpr (algPrivate [] [] [
      ("Values", alg [] [] [] [
        .capture [.num 10, .num 20, .num 30]
      ])
    ] [
      .dotCall (.resolve "Values") name none
    ]))
  let minWorks :=
    match runBuiltin "min" with
    | Except.ok (.atom 10) => true
    | _ => false
  let maxWorks :=
    match runBuiltin "max" with
    | Except.ok (.atom 30) => true
    | _ => false
  let sumWorks :=
    match runBuiltin "sum" with
    | Except.ok (.atom 60) => true
    | _ => false
  let avgWorks :=
    match runBuiltin "avg" with
    | Except.ok (.atom 20) => true
    | _ => false
  let orderWorks :=
    match runBuiltin "order" with
    | Except.ok (.listValue [.atom 10, .atom 20, .atom 30]) => true
    | _ => false
  let orderDescWorks :=
    match runBuiltin "orderDesc" with
    | Except.ok (.listValue [.atom 30, .atom 20, .atom 10]) => true
    | _ => false
  minWorks && maxWorks && sumWorks && avgWorks && orderWorks && orderDescWorks

#guard test217

def test218 : Bool :=
  let keepSecondEven : Algorithm :=
    alg ["pair"] [] [] [
      .binary .eq
        (.binary .mod (.index (.param "pair") (.num 1)) (.num 2))
        (.num 0)
    ]
  let takeFirstAlg : Algorithm :=
    alg ["x"] [] [] [
      .index (.param "x") (.num 0)
    ]
  let addItemCount : Algorithm :=
    alg ["item", "acc"] [] [] [
      .binary .add
        (.dotCall (.param "item") "count" none)
        (.param "acc")
    ]
  let filterResult :=
    runResult (.algorithmExpr (algPrivate [] [] [
      ("Values", alg [] [] [] [
        .capture [.num 1, .num 2],
        .capture [.num 1, .num 3]
      ]),
      ("KeepSecondEven", keepSecondEven)
    ] [
      .dotCall (.resolve "Values") "filter" (some [.resolve "KeepSecondEven"])
    ]))
  let mapResult :=
    runResult (.algorithmExpr (algPrivate [] [] [
      ("Values", alg [] [] [] [
        .capture [.num 1, .num 2, .num 3],
        .capture [.num 4, .num 5, .num 6]
      ]),
      ("TakeFirst", takeFirstAlg)
    ] [
      .dotCall (.resolve "Values") "map" (some [.resolve "TakeFirst"])
    ]))
  let reduceResult :=
    runFlat (.algorithmExpr (algPrivate [] [] [
      ("Values", alg [] [] [] [
        .capture [.num 1, .num 2, .num 3],
        .capture [.num 4, .num 5, .num 6]
      ]),
      ("AddItemCount", addItemCount)
    ] [
      .dotCall (.resolve "Values") "reduce" (some [.resolve "AddItemCount", .num 0])
    ]))
  let filterOk :=
    match filterResult with
    -- Filtering keeps one sequence-valued item; the exact-list result keeps it
    -- as one element, so the result is `[(1, 2)]`.
    | Except.ok (.listValue [.sequenceValue [.atom 1, .atom 2]]) => true
    | _ => false
  let mapOk :=
    match mapResult with
    | Except.ok (.listValue [.atom 1, .atom 4]) => true
    | _ => false
  let reduceOk :=
    match reduceResult with
    | Except.ok [6] => true
    | _ => false
  filterOk && mapOk && reduceOk

#guard test218

def test219 : Bool :=
  match runResult (.dotCall (.capture [
    .capture [.num 1, .num 2],
    .capture [.num 3, .num 4]
  ]) "sum" none) with
  | Except.error err =>
      hasContext "sum expects each collection element to be a single numeric value; item 0 was sequence value" err
        && innermostIsBadArity err
  | _ => false

#guard test219

end KatLangTests
