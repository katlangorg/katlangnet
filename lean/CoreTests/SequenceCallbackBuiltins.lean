import KatLang
import CoreTests.Common

namespace KatLangTests
open KatLang (alg algWithParameters algWithParameterPatterns algPrivate privateProp publicProp privateLocalProp publicLocalProp runFlat runResult Algorithm Error Result PropExposure)
open KatLang (resolve param num)
open KatLang (Pattern CondBranch)

--------------------------------------------------------------------------------
-- filter builtin tests
--------------------------------------------------------------------------------

def isEvenAlg63 : Algorithm :=
  alg ["x"] [] [] [.compare .eq (.binary .mod (.param "x") (.num 2)) (.num 0)]

def isPositiveAlg64 : Algorithm :=
  alg ["x"] [] [] [.compare .gt (.param "x") (.num 0)]

def isNegativeAlg65 : Algorithm :=
  alg ["x"] [] [] [.compare .lt (.param "x") (.num 0)]

def badTruthAlg66 : Algorithm :=
  alg ["x"] [] [] [.stringLiteral "not-a-number"]

def alwaysFalseAlg66a : Algorithm :=
  alg ["x"] [] [] [.boolLiteral false]

-- A predicate that returns a NUMBER is not a predicate: `filter{x}` over
-- numbers is the Boolean-requirement error, never a nonzero truth test.
def numericResultAlg66f : Algorithm :=
  alg ["x"] [] [] [.param "x"]

def keepTenSequenceValueAlg66b : Algorithm :=
  .conditional none [] [
    ⟨ .sequenceValue [
        .sequenceValue [
          .bind "a", .bind "b", .bind "c", .bind "d", .bind "e",
          .bind "f", .bind "g", .bind "h", .bind "i", .bind "j"
        ]
      ],
      alg [] [] [] [.boolLiteral true] ⟩,
    ⟨ .bind "x", alg [] [] [] [.boolLiteral false] ⟩
  ]

def keepFourSequenceValueAlg66c : Algorithm :=
  .conditional none [] [
    ⟨ .sequenceValue [.sequenceValue [.bind "a", .bind "b", .bind "c", .bind "d"]],
      alg [] [] [] [.boolLiteral true] ⟩,
    ⟨ .bind "x", alg [] [] [] [.boolLiteral false] ⟩
  ]

def rejectFourSequenceValueAlg66d : Algorithm :=
  .conditional none [] [
    ⟨ .sequenceValue [.sequenceValue [.bind "a", .bind "b", .bind "c", .bind "d"]],
      alg [] [] [] [.boolLiteral false] ⟩,
    ⟨ .bind "x", alg [] [] [] [.boolLiteral true] ⟩
  ]

def markThreeSequenceValueAlg66e : Algorithm :=
  .conditional none [] [
    ⟨ .sequenceValue [.sequenceValue [.bind "a", .bind "b", .bind "c"]],
      alg [] [] [] [.boolLiteral true] ⟩,
    ⟨ .bind "x", alg [] [] [] [.boolLiteral false] ⟩
  ]

def keepPairAlg67 : Algorithm :=
  .conditional none [] [
    ⟨ .sequenceValue [.bind "tag", .bind "value"],
      alg [] [] [] [.compare .eq (.binary .mod (.param "tag") (.num 2)) (.num 0)] ⟩
  ]

def badMultiFalseAlg68 : Algorithm :=
  alg ["x"] [] [] [.num 0, .num 999]

def badMultiTrueAlg69 : Algorithm :=
  alg ["x"] [] [] [.num 5, .num 0]

def badSequenceValueAlg70 : Algorithm :=
  alg ["x"] [] [] [.capture [.num 1, .num 0]]

-- `take(x, 0)` returns the exact list `[]`: one value, but a list has no truth
-- value, so a predicate built from a collection builtin is rejected.
def listTruthAlg71 : Algorithm :=
  alg ["x"] [] [] [
    .call (resolve "take") [
      .param "x",
      .num 0
    ]
  ]

-- Test 63: plain-call filter iterates emitted range items
def test63 : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("KeepTenSequenceValue", keepTenSequenceValueAlg66b)] [
    .call (resolve "filter") [
      .call (resolve "range") [.num 1, .num 10],
      .resolve "KeepTenSequenceValue"
    ]
  ])) with
  | Except.ok [] => true
  | _ => false

#guard test63

-- Test 64: descending ranges iterate emitted items in plain-call filter
def test64 : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("KeepTenSequenceValue", keepTenSequenceValueAlg66b)] [
    .call (resolve "filter") [
      .call (resolve "range") [.num 10, .num 1],
      .resolve "KeepTenSequenceValue"
    ]
  ])) with
  | Except.ok [] => true
  | _ => false

#guard test64

-- Test 65: a sequence-value-only predicate does not match scalar emitted range items
def test65 : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("KeepFourSequenceValue", keepFourSequenceValueAlg66c)] [
    .call (resolve "filter") [
      .call (resolve "range") [.num 1, .num 4],
      .resolve "KeepFourSequenceValue"
    ]
  ])) with
  | Except.ok [] => true
  | _ => false

#guard test65

-- Test 66: a sequence-value-only rejection predicate keeps scalar emitted range items
def test66 : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("RejectFourSequenceValue", rejectFourSequenceValueAlg66d)] [
    .call (resolve "filter") [
      .call (resolve "range") [.num 1, .num 4],
      .resolve "RejectFourSequenceValue"
    ]
  ])) with
  | Except.ok [1, 2, 3, 4] => true
  | _ => false

#guard test66

-- Fixed-arity collection builtin binding: the ONE bound collection argument is read
-- through the one-level collection view after binding, while sibling arguments are
-- never merged into one collection (extra siblings are ordinary arity errors).

-- Sibling arguments are never flattened into one collection: filter(range(3, 6), 8, IsEven)
-- supplies three arguments where `filter(collection, predicate)` expects two, so the call
-- reports an ordinary arity error (never a silently merged collection).
def sequenceBoundaryLawFilterCommaRangeSourcePreservesBoundary : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("IsEven", isEvenAlg63)] [
    .call (resolve "filter") [
      .call (resolve "range") [.num 3, .num 6],
      .num 8,
      .resolve "IsEven"
    ]
  ])) with
  | Except.error err => innermostIsArityMismatch 2 3 err
  | Except.ok _ => false

#guard sequenceBoundaryLawFilterCommaRangeSourcePreservesBoundary

-- A single grouped argument `(range(3, 6)*, 8)` is ONE collection value; the post-binding
-- one-level collection view opens it, so filter's collection is [3, 4, 5, 6, 8] and keeps
-- the even items [4, 6, 8].
def sequenceBoundaryLawFilterSequenceSpreadRangeSourceExpands : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("IsEven", isEvenAlg63)] [
    .call (resolve "filter") [
      sequenceItems [sequenceSpread (.call (resolve "range") [.num 3, .num 6]), .num 8],
      .resolve "IsEven"
    ]
  ])) with
  | Except.ok [4, 6, 8] => true
  | _ => false

#guard sequenceBoundaryLawFilterSequenceSpreadRangeSourceExpands

-- A named multi-output source `Data` is ONE collection argument; the post-binding one-level
-- collection view opens it, so filter's collection is [3, 4, 5, 6].
def sequenceBoundaryLawFilterNamedSingleSourcePreservesBoundary : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("IsEven", isEvenAlg63),
    ("Data", alg [] [] [] [.num 3, .num 4, .num 5, .num 6])
  ] [
    .call (resolve "filter") [
      .resolve "Data",
      .resolve "IsEven"
    ]
  ])) with
  | Except.ok [4, 6] => true
  | _ => false

#guard sequenceBoundaryLawFilterNamedSingleSourcePreservesBoundary

-- A dot-call receiver `Data` binds the fixed collection parameter; the post-binding
-- one-level collection view opens it, so filter iterates [3, 4, 5, 6].
def sequenceBoundaryLawFilterDotReceiverExpands : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("IsEven", isEvenAlg63),
    ("Data", alg [] [] [] [.num 3, .num 4, .num 5, .num 6])
  ] [
    .dotCall (.resolve "Data") "filter" (some [.resolve "IsEven"])
  ])) with
  | Except.ok [4, 6] => true
  | _ => false

#guard sequenceBoundaryLawFilterDotReceiverExpands

-- Named multi-output plus a comma-separated scalar are two sibling arguments ((3, 4, 5, 6)
-- and 8), so `filter(collection, predicate)` receives three arguments and reports an
-- ordinary arity error (sibling preservation, never silent flattening).
def sequenceBoundaryLawFilterCommaNamedSourcePreservesBoundary : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("IsEven", isEvenAlg63),
    ("Data", alg [] [] [] [.num 3, .num 4, .num 5, .num 6])
  ] [
    .call (resolve "filter") [
      .resolve "Data",
      .num 8,
      .resolve "IsEven"
    ]
  ])) with
  | Except.error err => innermostIsArityMismatch 2 3 err
  | Except.ok _ => false

#guard sequenceBoundaryLawFilterCommaNamedSourcePreservesBoundary

-- A single grouped argument `(Data*, 8)` is ONE collection value opened by the
-- post-binding one-level collection view, so filter's collection is [3, 4, 5, 6, 8]
-- and keeps the even items [4, 6, 8].
def sequenceBoundaryLawFilterSequenceSpreadNamedSourceExpands : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("IsEven", isEvenAlg63),
    ("Data", alg [] [] [] [.num 3, .num 4, .num 5, .num 6])
  ] [
    .call (resolve "filter") [
      sequenceItems [sequenceSpread (.resolve "Data"), .num 8],
      .resolve "IsEven"
    ]
  ])) with
  | Except.ok [4, 6, 8] => true
  | _ => false

#guard sequenceBoundaryLawFilterSequenceSpreadNamedSourceExpands

-- Test 67: filtering an already-empty sequence-value boundary stays empty
def test67 : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("KeepFourSequenceValue", keepFourSequenceValueAlg66c), ("RejectFourSequenceValue", rejectFourSequenceValueAlg66d)] [
    .call (resolve "filter") [
      .call (resolve "filter") [
        .call (resolve "range") [.num 1, .num 4],
        .resolve "RejectFourSequenceValue"
      ],
      .resolve "KeepFourSequenceValue"
    ]
  ])) with
  | Except.ok [] => true
  | _ => false

#guard test67

-- Test 68: a callback element is ONE argument (THE CALLBACK LAW): the flat
-- two-binder family `KeepPair(tag, value)` rejects each pair element with the
-- ordinary callback arity error, while the explicit structural pattern
-- `KeepPair((tag, value))` opens each pair — and the kept sequence values are
-- preserved whole and in order as exact list elements.
def keepPairPatternAlg68 : Algorithm :=
  .conditional none [] [
    ⟨ .sequenceValue [.sequenceValue [.bind "tag", .bind "value"]],
      alg [] [] [] [.compare .eq (.binary .mod (.param "tag") (.num 2)) (.num 0)] ⟩
  ]

def test68 : Bool :=
  let pairs := sequenceItems [
    .capture [.num 1, .num 10],
    .capture [.num 2, .num 20],
    .capture [.num 3, .num 30],
    .capture [.num 4, .num 40]]
  (match runResult (.algorithmExpr (algPrivate [] [] [("KeepPair", keepPairAlg67)] [
    .call (resolve "filter") [pairs, .resolve "KeepPair"]
  ])) with
  | Except.error err => innermostIsArityMismatch 2 1 err
  | _ => false) &&
  (match runResult (.algorithmExpr (algPrivate [] [] [("KeepPair", keepPairPatternAlg68)] [
    .call (resolve "filter") [pairs, .resolve "KeepPair"]
  ])) with
  | Except.ok (.listValue [
      .sequenceValue [.atom 2, .atom 20],
      .sequenceValue [.atom 4, .atom 40]
    ]) => true
  | _ => false)

#guard test68

-- Every non-Boolean predicate result is the ONE Boolean-requirement error
-- naming the result (`booleanRequiredMessage "filter predicate result"`),
-- raised inside the per-item filter context.
def filterPredicateRejected (predicate : Algorithm) (description : String) : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("Bad", predicate)] [
    .call (resolve "filter") [
      .call (resolve "range") [.num 1, .num 3],
      .resolve "Bad"
    ]
  ])) with
  | Except.error err =>
      hasContext "while evaluating call to filter" err &&
      innermostIsBooleanRequired "filter predicate result" description err
  | _ => false

-- Test 69: multi-output predicate starting with 0 is rejected
def test69 : Bool :=
  filterPredicateRejected badMultiFalseAlg68 "a sequence value with 2 sequence elements: (0, 999)"

#guard test69

-- Test 70: multi-output predicate starting with nonzero is also rejected
def test70 : Bool :=
  filterPredicateRejected badMultiTrueAlg69 "a sequence value with 2 sequence elements: (5, 0)"

#guard test70

-- Test 71: sequenceValue predicate result is rejected
def test71 : Bool :=
  filterPredicateRejected badSequenceValueAlg70 "a sequence value with 2 sequence elements: (1, 0)"

#guard test71

-- Test 72: exact-list predicate result is rejected (a collection builtin used
-- as a filter predicate returns a list, never a Boolean value)
def test72 : Bool :=
  filterPredicateRejected listTruthAlg71 "a list value with 0 elements: []"

#guard test72

-- Test 73: string predicate result is rejected
def test73 : Bool :=
  filterPredicateRejected badTruthAlg66 "a string: 'not-a-number'"

#guard test73

-- Test 73a: a NUMERIC predicate result is rejected too — `filter{x}` over
-- numbers has no nonzero-keeps reading; the first item `1` is reported.
def test73a : Bool :=
  filterPredicateRejected numericResultAlg66f "numeric value 1"

#guard test73a

-- Test 73b: a Boolean under a redundant singleton boundary is a valid
-- predicate result — `(x > 1)` keeps `2` and `3` exactly like `x > 1`.
def test73b : Bool :=
  match runResult (.algorithmExpr (algPrivate [] []
      [("Keep", alg ["x"] [] [] [.capture [.compare .gt (.param "x") (.num 1)]])] [
    .call (resolve "filter") [
      .call (resolve "range") [.num 1, .num 3],
      .resolve "Keep"
    ]
  ])) with
  | Except.ok (.listValue [.atom 2, .atom 3]) => true
  | _ => false

#guard test73b

-- Test 74: builtin arity mismatch still follows normal conventions
def test74 : Bool :=
  match runResult (.call (resolve "filter") []) with
  | Except.error _ => true
  | _ => false

#guard test74

-- Test 75: filter predicate arity mismatch explains the implicit item argument
def test75 : Bool :=
  match runResult (.dotCall
    (.call (resolve "range") [.num 1, .num 5])
    "filter"
    (some [.num 1])) with
  | Except.error err =>
      hasContext "while evaluating filter predicate for item 0: 1 (filter passes each iterated collection item as collected; a collecting parameter collects supplied values as one exact list and nested sequence and list values stay intact)" err &&
      innermostIsArityMismatch 0 1 err
  | _ => false

#guard test75

--------------------------------------------------------------------------------
-- reduce builtin tests
--------------------------------------------------------------------------------

def addAlg76 : Algorithm :=
  alg ["x", "total"] [] [] [.binary .add (.param "x") (.param "total")]

def mulAlg77 : Algorithm :=
  alg ["x", "total"] [] [] [
    .binary .add
      (.binary .mul (.param "total") (.num 10))
      (.dotCall (.param "x") "count" none)
  ]

def digitsAlg78 : Algorithm :=
  .conditional none [] [
    ⟨ .sequenceValue [
        .sequenceValue [.bind "a", .bind "b", .bind "c", .bind "d"],
        .bind "acc"
      ],
      alg [] [] [] [
        .binary .add
          (.binary .mul (.param "a") (.num 1000))
          (.binary .add
            (.binary .mul (.param "b") (.num 100))
            (.binary .add
              (.binary .mul (.param "c") (.num 10))
              (.param "d")))
      ] ⟩,
    ⟨ .sequenceValue [.bind "x", .bind "acc"],
      alg [] [] [] [.num 0] ⟩
  ]

def reduceSequenceValueItemAlg79 : Algorithm :=
  .conditional none [] [
    ⟨ .sequenceValue [.sequenceValue [.bind "tag", .bind "value"], .bind "acc"],
      alg [] [] [] [.binary .add (.param "acc") (.param "value")] ⟩
  ]

def reduceStatsAlg80 : Algorithm :=
  alg ["x", "acc"] [] [] [
    .capture [
      .binary .add (.dotCall (.param "x") "count" none) (.index (.param "acc") (.num 0)),
      .binary .add (.index (.param "acc") (.num 1)) (.num 1)
    ]
  ]

def reduceEmptyBoundaryAlg80a : Algorithm :=
  alg ["x", "acc"] [] [] [
    .binary .add
      (.binary .add (.param "acc") (.num 100))
      (.dotCall (.param "x") "count" none)
  ]

def reduceEmptyBoundarySequenceValueAccAlg80b : Algorithm :=
  alg ["x", "acc"] [] [] [
    .capture [
      .binary .add
        (.binary .add (.index (.param "acc") (.num 0)) (.num 100))
        (.dotCall (.param "x") "count" none),
      .binary .add (.index (.param "acc") (.num 1)) (.num 1)
    ]
  ]

def addItemCountAlg80c : Algorithm :=
  alg ["x", "acc"] [] [] [
    .binary .add
      (.dotCall (.param "x") "count" none)
      (.param "acc")
  ]

-- A literal `()` body keeps testing the empty-step failure: `take(x, 0)` now
-- returns the exact list `[]`, which is ONE valid accumulator value.
def reduceEmptyAlg81 : Algorithm :=
  alg ["x", "acc"] [] [] [.emptySequence 0]

def reduceMultiAlg82 : Algorithm :=
  alg ["x", "acc"] [] [] [.param "acc", .param "x"]

-- `T` reads the ancestor-owned step parameter `tt`, so it is local-only (the
-- front end classifies it so): the per-run zero-argument property cache keys a
-- local-only property by its binding context, one value per reduce step. An
-- exported declaration would cache the first step's `T` for every element.
def sequenceBoundaryLawAocCountMatchStepAlg : Algorithm :=
  alg ["element", "tt"] [] [
    privateLocalProp "T" (.localCapturedAncestorParams ["tt"]) (alg [] [] [] [
      .call (resolve "atoms") [.param "tt"]
    ])
  ] [
    .capture [
      .dotCall (resolve "T") "first" none,
      .binary .add
        (.index (resolve "T") (.num 1))
        (.call (resolve "if") [
          .compare .eq (.param "element") (.dotCall (resolve "T") "first" none),
          .num 1,
          .num 0
        ])
    ]
  ]

-- Exact AoC-style regression: Right is a named multi-output property bound as
-- reduce's collection argument, so the collection view must iterate its items.
def sequenceBoundaryLawAocNamedReduceSource : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("Left", alg [] [] [] [.num 3, .num 4, .num 2, .num 1, .num 3, .num 3]),
    ("Right", alg [] [] [] [.num 4, .num 3, .num 5, .num 3, .num 9, .num 3]),
    ("CountMatchStep", sequenceBoundaryLawAocCountMatchStepAlg),
    ("MatchCount", alg ["value"] [] [] [
      .index
        (.call (resolve "reduce") [
          resolve "Right",
          resolve "CountMatchStep",
          .capture [.param "value", .num 0]
        ])
        (.num 1)
    ]),
    ("SimilarityAt", alg ["value"] [] [] [
      .binary .mul
        (.param "value")
        (.call (resolve "MatchCount") [.param "value"])
    ]),
    ("Part2", alg [] [] [] [
      .dotCall
        (.dotCall (resolve "Left") "map" (some [resolve "SimilarityAt"]))
        "sum"
        none
    ])
  ] [
    resolve "Part2"
  ])) with
  | Except.ok [31] => true
  | _ => false

#guard sequenceBoundaryLawAocNamedReduceSource

-- Test 76: dot-call reduce over range with additive step
def test76 : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("Add", addAlg76)] [
    .dotCall
      (.call (resolve "range") [.num 1, .num 5])
      "reduce"
      (some [.resolve "Add", .num 0])
  ])) with
  | Except.ok [15] => true
  | _ => false

#guard test76

-- Test 77: plain-call reduce iterates emitted range items
def test77 : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("Mul", mulAlg77)] [
    .call (resolve "reduce") [
      .call (resolve "range") [.num 1, .num 4],
      .resolve "Mul",
      .num 1
    ]
  ])) with
  | Except.ok [11111] => true
  | _ => false

#guard test77

-- Test 77a: plain-call reduce can still observe sequence-value range content explicitly
def test77a : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("AddItemCount", addItemCountAlg80c)] [
    .call (resolve "reduce") [
      .call (resolve "range") [.num 3, .num 6],
      .resolve "AddItemCount",
      .num 0
    ]
  ])) with
  | Except.ok [4] => true
  | _ => false

#guard test77a

-- Test 78: sequence-value-only reduce branches do not match scalar emitted range items
def test78 : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("Digits", digitsAlg78)] [
    .call (resolve "reduce") [
      .call (resolve "range") [.num 1, .num 4],
      .resolve "Digits",
      .num 0
    ]
  ])) with
  | Except.ok [0] => true
  | _ => false

#guard test78

-- Test 79: reducing an empty plain-call collection returns the initial accumulator
def test79 : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("AlwaysFalse", alwaysFalseAlg66a), ("MarkEmptyBoundary", reduceEmptyBoundaryAlg80a)] [
    .call (resolve "reduce") [
      .call (resolve "filter") [
        .call (resolve "range") [.num 1, .num 4],
        .resolve "AlwaysFalse"
      ],
      .resolve "MarkEmptyBoundary",
      .num 0
    ]
  ])) with
  | Except.ok (.atom 0) => true
  | _ => false

#guard test79

-- Test 80: sequence-value accumulators also stay unchanged when reducing an empty collection
def test80 : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("AlwaysFalse", alwaysFalseAlg66a), ("MarkEmptyBoundary", reduceEmptyBoundarySequenceValueAccAlg80b)] [
    .call (resolve "reduce") [
      .call (resolve "filter") [
        .call (resolve "range") [.num 1, .num 4],
        .resolve "AlwaysFalse"
      ],
      .resolve "MarkEmptyBoundary",
      .capture [.num 7, .num 9]
    ]
  ])) with
  | Except.ok (.sequenceValue [.atom 7, .atom 9]) => true
  | _ => false

#guard test80

-- Test 81: sequenceValue collection elements are passed to the step as whole values
def test81 : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("TakeValue", reduceSequenceValueItemAlg79)] [
    .call (resolve "reduce") [sequenceItems [
      .capture [.num 1, .num 10],
      .capture [.num 2, .num 20],
      .capture [.num 3, .num 30]],
      .resolve "TakeValue",
      .num 0
    ]
  ])) with
  | Except.ok [60] => true
  | _ => false

#guard test81

-- Test 82: sequence-value accumulators keep their shape while emitted range items are reduced
def test82 : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("Stats", reduceStatsAlg80)] [
    .call (resolve "reduce") [
      .call (resolve "range") [.num 1, .num 4],
      .resolve "Stats",
      .capture [.num 0, .num 0]
    ]
  ])) with
  | Except.ok (.sequenceValue [.atom 4, .atom 4]) => true
  | _ => false

#guard test82

-- Test 83: reduce step must not return an empty result
def test83 : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("Bad", reduceEmptyAlg81)] [
    .call (resolve "reduce") [
      .call (resolve "range") [.num 1, .num 3],
      .resolve "Bad",
      .num 0
    ]
  ])) with
  | Except.error err => hasContext "reduce step must return a single accumulator value" err && innermostIsBadArity err
  | _ => false

#guard test83

-- Test 84: reduce step must not return multiple top-level outputs
def test84 : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("Bad", reduceMultiAlg82)] [
    .call (resolve "reduce") [
      .call (resolve "range") [.num 1, .num 3],
      .resolve "Bad",
      .num 0
    ]
  ])) with
  | Except.error err => hasContext "reduce step must return a single accumulator value" err && innermostIsBadArity err
  | _ => false

#guard test84

-- Test 84a: reduce is an ordinary fixed-arity callable — reduce(1) supplies one
-- argument where `reduce(collection, reducer, initial)` expects three.
def test84a : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("Add", addAlg76)] [
    .call (resolve "reduce") [
      .num 1
    ]
  ])) with
  | Except.error err => innermostIsArityMismatch 3 1 err
  | _ => false

#guard test84a

-- Test 84b: reduce((1, 2, 3), Add) supplies two of the three fixed arguments —
-- an ordinary arity error, with no suffix-binding reinterpretation of the
-- argument list.
def test84b : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("Add", addAlg76)] [
    .call (resolve "reduce") [
      sequenceItems [.num 1, .num 2, .num 3],
      .resolve "Add"
    ]
  ])) with
  | Except.error err => innermostIsArityMismatch 3 2 err
  | _ => false

#guard test84b

-- Test 84c: the dotted missing-initial hint is reserved for a visibly
-- parameterized reducer. An ordinary value in the sole control slot follows
-- the fixed signature and reports the ordinary three-versus-two arity error.
def test84c : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("Values", alg [] [] [] [
    sequenceItems [.num 1, .num 2, .num 3]
  ])] [
    .dotCall (resolve "Values") "reduce" (some [.num 0])
  ])) with
  | Except.error err => innermostIsArityMismatch 3 2 err
  | _ => false

#guard test84c

--------------------------------------------------------------------------------
-- map builtin tests
--------------------------------------------------------------------------------

def doubleAlg85 : Algorithm :=
  alg ["x"] [] [] [.binary .mul (.param "x") (.num 2)]

def takeMiddleSequenceValueAlg85a : Algorithm :=
  .conditional none [] [
    ⟨ .sequenceValue [.sequenceValue [.bind "a", .bind "b", .bind "c", .bind "d", .bind "e"]],
      alg [] [] [] [.param "c"] ⟩,
    ⟨ .bind "x", alg [] [] [] [.num 0] ⟩
  ]

def squareAlg86 : Algorithm :=
  alg ["x"] [] [] [.binary .mul (.param "x") (.param "x")]

def tagAlg87 : Algorithm :=
  .conditional none [] [
    ⟨ .sequenceValue [.sequenceValue [.bind "first", .bind "b", .bind "c", .bind "d", .bind "last"]],
      alg [] [] [] [
        .binary .add (.binary .mul (.param "first") (.num 10)) (.param "last")
      ] ⟩,
    ⟨ .bind "x", alg [] [] [] [.num 0] ⟩
  ]

def countMembersAlg88a : Algorithm :=
  alg ["x"] [] [] [
    .dotCall (.param "x") "count" none
  ]

def takePairValueAlg89 : Algorithm :=
  .conditional none [] [
    ⟨ .sequenceValue [.bind "tag", .bind "value"],
      alg [] [] [] [.param "value"] ⟩
  ]

def pairWithSquareAlg90 : Algorithm :=
  .conditional none [] [
    ⟨ .sequenceValue [.sequenceValue [.bind "first", .bind "middle", .bind "last"]],
      alg [] [] [] [
        .capture [
          .param "first",
          .param "last"
        ]
      ] ⟩,
    ⟨ .bind "x",
      alg [] [] [] [
        .capture [.num 0, .num 0]
      ] ⟩
  ]

-- A literal `()` body keeps testing the empty-transform failure: `take(x, 0)` now
-- returns the exact list `[]`, which is ONE valid element.
def mapEmptyAlg91 : Algorithm :=
  alg ["x"] [] [] [.emptySequence 0]

def mapMultiAlg92 : Algorithm :=
  alg ["x"] [] [] [
    .param "x",
    .num 0
  ]

-- Test 85: dot-call map doubles each range element left-to-right
def test85 : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("Double", doubleAlg85)] [
    .dotCall
      (.call (resolve "range") [.num 1, .num 5])
      "map"
      (some [.resolve "Double"])
  ])) with
  | Except.ok [2, 4, 6, 8, 10] => true
  | _ => false

#guard test85

def factorialMapAlg85a : Algorithm :=
  alg ["n"] [] [] [
    .call (resolve "if") [
      .compare .eq (.param "n") (.num 0),
      .num 1,
      .binary .mul
        (.call (resolve "Factorial") [
          .binary .sub (.param "n") (.num 1)
        ])
        (.param "n")
    ]
  ]

def test85a : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("Factorial", factorialMapAlg85a)] [
    .dotCall
      (.capture [.num 0, .num 1, .num 2, .num 3, .num 4])
      "map"
      (some [.resolve "Factorial"])
  ])) with
  | Except.ok [1, 1, 2, 6, 24] => true
  | _ => false

#guard test85a

-- Test 86: plain-call map iterates emitted range items
def test86 : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("TakeMiddle", takeMiddleSequenceValueAlg85a)] [
    .call (resolve "map") [
      .call (resolve "range") [.num 1, .num 5],
      .resolve "TakeMiddle"
    ]
  ])) with
  | Except.ok [0, 0, 0, 0, 0] => true
  | _ => false

#guard test86

-- Test 86a: plain-call map applies scalar transforms to emitted range items
def test86a : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("Double", doubleAlg85)] [
    .call (resolve "map") [
      .call (resolve "range") [.num 1, .num 5],
      .resolve "Double"
    ]
  ])) with
  | Except.ok [2, 4, 6, 8, 10] => true
  | _ => false

#guard test86a

-- Test 87: sequence-value-only map branches do not match scalar emitted range items
def test87 : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("Tag", tagAlg87)] [
    .call (resolve "map") [
      .call (resolve "range") [.num 5, .num 1],
      .resolve "Tag"
    ]
  ])) with
  | Except.ok [0, 0, 0, 0, 0] => true
  | _ => false

#guard test87

-- Test 88: mapping over an empty filter-result list yields the exact empty list `[]`
def test88 : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("AlwaysFalse", alwaysFalseAlg66a), ("CountMembers", countMembersAlg88a)] [
    .call (resolve "map") [
      .call (resolve "filter") [
        .call (resolve "range") [.num 1, .num 4],
        .resolve "AlwaysFalse"
      ],
      .resolve "CountMembers"
    ]
  ])) with
  | Except.ok (.listValue []) => true
  | _ => false

#guard test88

-- Test 89: sequenceValue collection elements are passed to the transform as
-- whole values — ONE argument each — so the flat two-binder family
-- `TakeValue(tag, value)` rejects them with the ordinary callback arity error,
-- while the explicit structural pattern `TakeValue((tag, value))` opens each.
def takePairValuePatternAlg89 : Algorithm :=
  .conditional none [] [
    ⟨ .sequenceValue [.sequenceValue [.bind "tag", .bind "value"]],
      alg [] [] [] [.param "value"] ⟩
  ]

def test89 : Bool :=
  let pairs := sequenceItems [
    .capture [.num 1, .num 10],
    .capture [.num 2, .num 20],
    .capture [.num 3, .num 30]]
  (match runFlat (.algorithmExpr (algPrivate [] [] [("TakeValue", takePairValueAlg89)] [
    .call (resolve "map") [pairs, .resolve "TakeValue"]
  ])) with
  | Except.error err => innermostIsArityMismatch 2 1 err
  | _ => false) &&
  (match runFlat (.algorithmExpr (algPrivate [] [] [("TakeValue", takePairValuePatternAlg89)] [
    .call (resolve "map") [pairs, .resolve "TakeValue"]
  ])) with
  | Except.ok [10, 20, 30] => true
  | _ => false)

#guard test89

-- Test 90: sequence-value mapped results are accepted for emitted range items
def test90 : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("PairWithSquare", pairWithSquareAlg90)] [
    .call (resolve "map") [
      .call (resolve "range") [.num 1, .num 3],
      .resolve "PairWithSquare"
    ]
  ])) with
  | Except.ok (.listValue [
      .sequenceValue [.atom 0, .atom 0],
      .sequenceValue [.atom 0, .atom 0],
      .sequenceValue [.atom 0, .atom 0]
    ]) => true
  | _ => false

#guard test90

-- Test 91: map transform must not return an empty result
def test91 : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("Bad", mapEmptyAlg91)] [
    .call (resolve "map") [
      .call (resolve "range") [.num 1, .num 3],
      .resolve "Bad"
    ]
  ])) with
  | Except.error err => hasContext "map transform must return a single element" err && innermostIsBadArity err
  | _ => false

#guard test91

-- Test 92: map transform must not return multiple top-level outputs
def test92 : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("Bad", mapMultiAlg92)] [
    .call (resolve "map") [
      .call (resolve "range") [.num 1, .num 3],
      .resolve "Bad"
    ]
  ])) with
  | Except.error err => hasContext "map transform must return a single element" err && innermostIsBadArity err
  | _ => false

#guard test92

-- K3-02: a zero-parameter wrapper retains its own callable identity even when
-- its only output names a parameterized algorithm. Eager value failure is not
-- permission to replace the wrapper by that output on the algorithm channel.
def filterZeroParameterWrapperRetainsArity : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("P", alg ["x"] [] [] [.num 1]),
    ("D", alg [] [] [] [.resolve "P"])
  ] [.call (.resolve "count") [.call (.resolve "filter") [
    .call (.resolve "range") [.num 1, .num 3], .resolve "D"
  ]]])) with
  | Except.error err => innermostIsArityMismatch 0 1 err
  | _ => false

#guard filterZeroParameterWrapperRetainsArity

--------------------------------------------------------------------------------
-- S3 (September 2026): callback binding of ONE supplied value uses the
-- ordinary call's nested-pattern rules. Both binders open a sequence-value
-- pattern's value through the ONE rule `Result.sequenceValuePatternItems`
-- (sequence/list opens one level; any other value is a one-item supply at
-- every group size), so for every pattern `P` and value `V`, `map([V], P)`
-- binds `V` exactly as `P(V)` does: same success, same bound values, and the
-- same innermost binding error. The callback operation still decides how many
-- values it supplies (map/filter one element, reduce element + accumulator).
-- Mirrors C# CallbackNestedPatternBindingTests.
--------------------------------------------------------------------------------

def innermostError : Error -> Error
  | .withContext _ inner => innermostError inner
  | error => error

/-- Pattern lists (with the names their one-value list body reports) covering
    every nested-group shape the one-item fallback distinguishes: one item,
    head plus collector, collector only, fixed pair, collector plus suffix,
    head/collector/suffix, a doubly nested collector, a nested group inside a
    group, and a repeated binder. -/
def s3CallbackPatterns : List (List KatLang.ParameterPattern × List String) := [
  ([.sequenceValue [.capture { name := "x" }]], ["x"]),
  ([.sequenceValue [.capture { name := "x" }, .capture { name := "rest", kind := .collecting }]], ["x", "rest"]),
  ([.sequenceValue [.capture { name := "xs", kind := .collecting }]], ["xs"]),
  ([.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]], ["x", "y"]),
  ([.sequenceValue [.capture { name := "init", kind := .collecting }, .capture { name := "z" }]], ["init", "z"]),
  ([.sequenceValue [.capture { name := "x" }, .capture { name := "r", kind := .collecting }, .capture { name := "z" }]],
    ["x", "r", "z"]),
  ([.sequenceValue [.sequenceValue [.capture { name := "x" }, .capture { name := "r", kind := .collecting }]]],
    ["x", "r"]),
  ([.sequenceValue [.capture { name := "a" },
      .sequenceValue [.capture { name := "b" }, .capture { name := "r", kind := .collecting }]]],
    ["a", "b", "r"]),
  ([.sequenceValue [.capture { name := "x" }, .capture { name := "x" }]], ["x"])
]

/-- Supplied values: scalars of every kind, the empty sequence value, sequence
    values (flat, nested, with an empty item, with a repeated item), and lists
    (empty, singleton, pair, singleton holding a pair). -/
def s3CallbackValues : List KatLang.Expr := [
  .num 7,
  .stringLiteral "s",
  .boolLiteral true,
  .emptySequence 0,
  .capture [.num 1, .num 2],
  .capture [.num 1, .num 2, .num 3],
  .capture [.capture [.num 1, .num 2], .num 3],
  .capture [.emptySequence 0, .num 1],
  .capture [.num 7, .num 7],
  .listLiteral [],
  .listLiteral [.num 5],
  .listLiteral [.num 1, .num 2],
  .listLiteral [.capture [.num 1, .num 2]]
]

def s3PatternAlg (patterns : List KatLang.ParameterPattern) (names : List String) : Algorithm :=
  algWithParameterPatterns patterns [] [] [.listLiteral (names.map KatLang.Expr.param)]

def s3Program (patterns : List KatLang.ParameterPattern) (names : List String)
    (output : KatLang.Expr) : KatLang.Expr :=
  .algorithmExpr (algPrivate [] [] [("P", s3PatternAlg patterns names)] [output])

/-- `P(V)` and `map([V], P)` bind the same value alike: equal bound results
    (the mapped list holds exactly the direct result), or the same innermost
    binding error (only the outer call/map context differs). -/
def s3DirectAndMapBindAlike (patterns : List KatLang.ParameterPattern) (names : List String)
    (value : KatLang.Expr) : Bool :=
  match runResult (s3Program patterns names (.call (resolve "P") [value])),
        runResult (s3Program patterns names (.call (resolve "map") [.listLiteral [value], .resolve "P"])) with
  | .ok direct, .ok (.listValue [mapped]) => direct == mapped
  | .error direct, .error mapped => reprStr (innermostError direct) == reprStr (innermostError mapped)
  | _, _ => false

#guard s3CallbackPatterns.all fun (patterns, names) =>
  s3CallbackValues.all fun value => s3DirectAndMapBindAlike patterns names value

/-- Two outcomes of the same supplied values agree: equal results, or the same
    innermost error. -/
def s3SameOutcome (expected actual : Except Error Result) : Bool :=
  match expected, actual with
  | .ok e, .ok a => e == a
  | .error e, .error a => reprStr (innermostError e) == reprStr (innermostError a)
  | _, _ => false

/-- filter binds its predicate like the call: `filter([V], K)` with an always-true
    `K(P)` keeps `[V]` exactly when `P(V)` binds, and otherwise fails with the
    direct call's innermost error. -/
def s3DirectAndFilterBindAlike (patterns : List KatLang.ParameterPattern) (value : KatLang.Expr) : Bool :=
  let keep := algWithParameterPatterns patterns [] [] [.boolLiteral true]
  let program (output : KatLang.Expr) := KatLang.Expr.algorithmExpr (algPrivate [] [] [("K", keep)] [output])
  match runResult (program (.call (resolve "K") [value])),
        runResult (program (.call (resolve "filter") [.listLiteral [value], .resolve "K"])) with
  | .ok _, filtered => s3SameOutcome (runResult (program (.listLiteral [value]))) filtered
  | .error direct, .error filtered => reprStr (innermostError direct) == reprStr (innermostError filtered)
  | _, _ => false

/-- reduce supplies the element AND the accumulator as two ordinary arguments:
    `reduce([V], R, 0)` agrees with the two-argument call `R(V, 0)`, and with a
    top-level collecting accumulator parameter the reducer still receives the
    accumulator as ONE value, so `reduce([V], R, (1, 2))` agrees with
    `R(V, (1, 2))` — the same supply. -/
def s3DirectAndReduceBindAlike (patterns : List KatLang.ParameterPattern) (names : List String)
    (value : KatLang.Expr) : Bool :=
  let fixedAcc := algWithParameterPatterns (patterns ++ [.capture { name := "acc" }]) [] []
    [.listLiteral ((names ++ ["acc"]).map KatLang.Expr.param)]
  let slotAcc := algWithParameterPatterns (patterns ++ [.capture { name := "acc", kind := .collecting }]) [] []
    [.listLiteral ((names ++ ["acc"]).map KatLang.Expr.param)]
  let run (reducer : Algorithm) (output : KatLang.Expr) :=
    runResult (.algorithmExpr (algPrivate [] [] [("R", reducer)] [output]))
  s3SameOutcome
      (run fixedAcc (.call (resolve "R") [value, .num 0]))
      (run fixedAcc (.call (resolve "reduce") [.listLiteral [value], .resolve "R", .num 0])) &&
  s3SameOutcome
      (run slotAcc (.call (resolve "R") [value, .capture [.num 1, .num 2]]))
      (run slotAcc (.call (resolve "reduce") [.listLiteral [value], .resolve "R", .capture [.num 1, .num 2]]))

#guard s3CallbackPatterns.all fun (patterns, _) =>
  s3CallbackValues.all fun value => s3DirectAndFilterBindAlike patterns value

#guard s3CallbackPatterns.all fun (patterns, names) =>
  s3CallbackValues.all fun value => s3DirectAndReduceBindAlike patterns names value

-- The agreement matrix alone would also pass if BOTH paths regressed the same
-- way, so the characteristic cells are pinned as well: a scalar is ONE item
-- for `(x, *rest)` (binds, rest empty), for `(*init, z)`, and inside a nested
-- group; it is one item too few for `(x, y)` — the nested group's ordinary
-- `arityMismatch 2 1`, never a bare `badArity` — in the direct call and the
-- callback alike.
def s3CallbackScalarCells : Bool :=
  let headRest : List KatLang.ParameterPattern := [.sequenceValue [.capture { name := "x" }, .capture { name := "rest", kind := .collecting }]]
  let pair : List KatLang.ParameterPattern := [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]]
  let initLast : List KatLang.ParameterPattern := [.sequenceValue [.capture { name := "init", kind := .collecting }, .capture { name := "z" }]]
  let nestedHead : List KatLang.ParameterPattern := [.sequenceValue [.sequenceValue [.capture { name := "x" }, .capture { name := "r", kind := .collecting }]]]
  let groupInGroup : List KatLang.ParameterPattern := [.sequenceValue [.capture { name := "a" },
      .sequenceValue [.capture { name := "b" }, .capture { name := "r", kind := .collecting }]]]
  let viaMap (patterns : List KatLang.ParameterPattern) (names : List String) (value : KatLang.Expr) :=
    runResult (s3Program patterns names (.call (resolve "map") [.listLiteral [value], .resolve "P"]))
  let direct (patterns : List KatLang.ParameterPattern) (names : List String) (value : KatLang.Expr) :=
    runResult (s3Program patterns names (.call (resolve "P") [value]))
  (match viaMap headRest ["x", "rest"] (.num 7) with
   | .ok (.listValue [.listValue [.atom 7, .listValue []]]) => true | _ => false) &&
  (match viaMap headRest ["x", "rest"] (.stringLiteral "s") with
   | .ok (.listValue [.listValue [.str "s", .listValue []]]) => true | _ => false) &&
  (match viaMap initLast ["init", "z"] (.boolLiteral true) with
   | .ok (.listValue [.listValue [.listValue [], .bool true]]) => true | _ => false) &&
  (match viaMap nestedHead ["x", "r"] (.num 7) with
   | .ok (.listValue [.listValue [.atom 7, .listValue []]]) => true | _ => false) &&
  (match viaMap groupInGroup ["a", "b", "r"] (.capture [.num 1, .num 2]) with
   | .ok (.listValue [.listValue [.atom 1, .atom 2, .listValue []]]) => true | _ => false) &&
  (match viaMap pair ["x", "y"] (.num 7) with
   | .error err => innermostIsArityMismatch 2 1 err | _ => false) &&
  (match direct pair ["x", "y"] (.num 7) with
   | .error err => innermostIsArityMismatch 2 1 err | _ => false)

#guard s3CallbackScalarCells

-- filter and reduce deliver their values through the same counted binder:
-- `filter([7, 1], P)` keeps 7 with `P((x, *rest)) = x > 1`; reduce binds the
-- scalar element (`R((x, *rest), acc)`) and the scalar accumulator
-- (`R(e, (a, *r))`) exactly as the two-argument ordinary call `R(7, 0)` does,
-- and the element beside a top-level collecting accumulator (`R((a, *r), *acc)`)
-- exactly as the ordinary call with the same supply — the accumulator is ONE
-- ordinary argument, so that call is again `R(7, 0)`.
def s3FilterAndReduceBindLikeCalls : Bool :=
  let headRest : List KatLang.ParameterPattern :=
    [.sequenceValue [.capture { name := "x" }, .capture { name := "rest", kind := .collecting }]]
  let keepAboveOne := algWithParameterPatterns headRest [] [] [.compare .gt (.param "x") (.num 1)]
  let elementReducer := algWithParameterPatterns
    (headRest ++ [.capture { name := "acc" }]) [] [] [.binary .add (.param "acc") (.param "x")]
  let accumulatorReducer := algWithParameterPatterns
    [.capture { name := "e" },
     .sequenceValue [.capture { name := "a" }, .capture { name := "r", kind := .collecting }]] [] []
    [.binary .add (.param "e") (.param "a")]
  let collectingReducer := algWithParameterPatterns
    [.sequenceValue [.capture { name := "a" }, .capture { name := "r", kind := .collecting }],
     .capture { name := "acc", kind := .collecting }] [] []
    [.listLiteral [.param "a", .param "r", .param "acc"]]
  let run (name : String) (callee : Algorithm) (output : KatLang.Expr) :=
    runResult (.algorithmExpr (algPrivate [] [] [(name, callee)] [output]))
  (match run "P" keepAboveOne (.call (resolve "filter") [.listLiteral [.num 7, .num 1], .resolve "P"]) with
   | .ok (.listValue [.atom 7]) => true | _ => false) &&
  (match run "R" elementReducer (.call (resolve "reduce") [.listLiteral [.num 7, .num 8], .resolve "R", .num 0]) with
   | .ok (.atom 15) => true | _ => false) &&
  (match run "R" elementReducer (.call (resolve "R") [.num 7, .num 0]) with
   | .ok (.atom 7) => true | _ => false) &&
  (match run "R" accumulatorReducer (.call (resolve "reduce") [.listLiteral [.num 7], .resolve "R", .num 0]) with
   | .ok (.atom 7) => true | _ => false) &&
  (match run "R" accumulatorReducer (.call (resolve "R") [.num 7, .num 0]) with
   | .ok (.atom 7) => true | _ => false) &&
  (match run "R" collectingReducer (.call (resolve "reduce") [.listLiteral [.num 7], .resolve "R", .num 0]) with
   | .ok (.listValue [.atom 7, .listValue [], .listValue [.atom 0]]) => true | _ => false) &&
  (match run "R" collectingReducer (.call (resolve "R") [.num 7, .num 0]) with
   | .ok (.listValue [.atom 7, .listValue [], .listValue [.atom 0]]) => true | _ => false)

#guard s3FilterAndReduceBindLikeCalls

-- Invocation count stays the collection operation's: an empty collection runs
-- the callback zero times even though its body would fail, while a selected
-- empty value `()` is ONE invocation with that value (it binds `(*xs)` to `[]`,
-- exactly like `P(())`).
def s3EmptyCollectionVersusEmptyItem : Bool :=
  let collector : List KatLang.ParameterPattern := [.sequenceValue [.capture { name := "xs", kind := .collecting }]]
  let failing := algWithParameterPatterns collector [] [] [.binary .div (.num 1) (.num 0)]
  let run (callee : Algorithm) (output : KatLang.Expr) :=
    runResult (.algorithmExpr (algPrivate [] [] [("P", callee)] [output]))
  (match run failing (.call (resolve "map") [.listLiteral [], .resolve "P"]) with
   | .ok (.listValue []) => true | _ => false) &&
  (match run (s3PatternAlg collector ["xs"]) (.call (resolve "map") [.listLiteral [.emptySequence 0], .resolve "P"]) with
   | .ok (.listValue [.listValue [.listValue []]]) => true | _ => false) &&
  (match run (s3PatternAlg collector ["xs"]) (.call (resolve "P") [.emptySequence 0]) with
   | .ok (.listValue [.listValue []]) => true | _ => false)

#guard s3EmptyCollectionVersusEmptyItem

end KatLangTests
