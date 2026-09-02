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
  alg ["x"] [] [] [.binary .eq (.binary .mod (.param "x") (.num 2)) (.num 0)]

def isPositiveAlg64 : Algorithm :=
  alg ["x"] [] [] [.binary .gt (.param "x") (.num 0)]

def isNegativeAlg65 : Algorithm :=
  alg ["x"] [] [] [.binary .lt (.param "x") (.num 0)]

def badTruthAlg66 : Algorithm :=
  alg ["x"] [] [] [.stringLiteral "not-a-number"]

def alwaysFalseAlg66a : Algorithm :=
  alg ["x"] [] [] [.num 0]

def keepTenSequenceValueAlg66b : Algorithm :=
  .conditional none [] [
    ⟨ .sequenceValue [
        .sequenceValue [
          .bind "a", .bind "b", .bind "c", .bind "d", .bind "e",
          .bind "f", .bind "g", .bind "h", .bind "i", .bind "j"
        ]
      ],
      alg [] [] [] [.num 1] ⟩,
    ⟨ .bind "x", alg [] [] [] [.num 0] ⟩
  ]

def keepFourSequenceValueAlg66c : Algorithm :=
  .conditional none [] [
    ⟨ .sequenceValue [.sequenceValue [.bind "a", .bind "b", .bind "c", .bind "d"]],
      alg [] [] [] [.num 1] ⟩,
    ⟨ .bind "x", alg [] [] [] [.num 0] ⟩
  ]

def rejectFourSequenceValueAlg66d : Algorithm :=
  .conditional none [] [
    ⟨ .sequenceValue [.sequenceValue [.bind "a", .bind "b", .bind "c", .bind "d"]],
      alg [] [] [] [.num 0] ⟩,
    ⟨ .bind "x", alg [] [] [] [.num 1] ⟩
  ]

def markThreeSequenceValueAlg66e : Algorithm :=
  .conditional none [] [
    ⟨ .sequenceValue [.sequenceValue [.bind "a", .bind "b", .bind "c"]],
      alg [] [] [] [.num 1] ⟩,
    ⟨ .bind "x", alg [] [] [] [.num 0] ⟩
  ]

def keepPairAlg67 : Algorithm :=
  .conditional none [] [
    ⟨ .sequenceValue [.bind "tag", .bind "value"],
      alg [] [] [] [.binary .eq (.binary .mod (.param "tag") (.num 2)) (.num 0)] ⟩
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

-- Test 68: kept sequence values are preserved whole and in order as exact list elements
def test68 : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("KeepPair", keepPairAlg67)] [
    .call (resolve "filter") [sequenceItems [
      .capture [.num 1, .num 10],
      .capture [.num 2, .num 20],
      .capture [.num 3, .num 30],
      .capture [.num 4, .num 40]],
      .resolve "KeepPair"
    ]
  ])) with
  | Except.ok (.listValue [
      .sequenceValue [.atom 2, .atom 20],
      .sequenceValue [.atom 4, .atom 40]
    ]) => true
  | _ => false

#guard test68

-- Test 69: multi-output predicate starting with 0 is rejected
def test69 : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("Bad", badMultiFalseAlg68)] [
    .call (resolve "filter") [
      .call (resolve "range") [.num 1, .num 3],
      .resolve "Bad"
    ]
  ])) with
  | Except.error err => hasContext "filter predicate must return exactly one atomic numeric value" err && innermostIsBadArity err
  | _ => false

#guard test69

-- Test 70: multi-output predicate starting with nonzero is also rejected
def test70 : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("Bad", badMultiTrueAlg69)] [
    .call (resolve "filter") [
      .call (resolve "range") [.num 1, .num 3],
      .resolve "Bad"
    ]
  ])) with
  | Except.error err => hasContext "filter predicate must return exactly one atomic numeric value" err && innermostIsBadArity err
  | _ => false

#guard test70

-- Test 71: sequenceValue predicate result is rejected
def test71 : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("Bad", badSequenceValueAlg70)] [
    .call (resolve "filter") [
      .call (resolve "range") [.num 1, .num 3],
      .resolve "Bad"
    ]
  ])) with
  | Except.error err => hasContext "filter predicate must return exactly one atomic numeric value" err && innermostIsBadArity err
  | _ => false

#guard test71

-- Test 72: exact-list predicate result is rejected (a collection builtin used
-- as a filter predicate returns a list, never an atomic numeric value)
def test72 : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("Bad", listTruthAlg71)] [
    .call (resolve "filter") [
      .call (resolve "range") [.num 1, .num 3],
      .resolve "Bad"
    ]
  ])) with
  | Except.error err => hasContext "filter predicate must return exactly one atomic numeric value" err && innermostIsBadArity err
  | _ => false

#guard test72

-- Test 73: string predicate result is rejected
def test73 : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("BadTruth", badTruthAlg66)] [
    .call (resolve "filter") [
      .call (resolve "range") [.num 1, .num 3],
      .resolve "BadTruth"
    ]
  ])) with
  | Except.error err => hasContext "filter predicate must return exactly one atomic numeric value" err && innermostIsBadArity err
  | _ => false

#guard test73

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

def sequenceBoundaryLawAocCountMatchStepAlg : Algorithm :=
  algPrivate ["element", "tt"] [] [
    ("T", alg [] [] [] [
      .call (resolve "atoms") [.param "tt"]
    ])
  ] [
    .capture [
      .dotCall (resolve "T") "first" none,
      .binary .add
        (.index (resolve "T") (.num 1))
        (.call (resolve "if") [
          .binary .eq (.param "element") (.dotCall (resolve "T") "first" none),
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
      .binary .eq (.param "n") (.num 0),
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

-- Test 89: sequenceValue collection elements are passed to the transform as whole values
def test89 : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("TakeValue", takePairValueAlg89)] [
    .call (resolve "map") [sequenceItems [
      .capture [.num 1, .num 10],
      .capture [.num 2, .num 20],
      .capture [.num 3, .num 30]],
      .resolve "TakeValue"
    ]
  ])) with
  | Except.ok [10, 20, 30] => true
  | _ => false

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

end KatLangTests
