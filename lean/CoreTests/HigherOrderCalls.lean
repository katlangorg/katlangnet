import KatLang
import CoreTests.Common

namespace KatLangTests
open KatLang (alg algWithParameters algWithParameterPatterns algPrivate privateProp publicProp privateLocalProp publicLocalProp runFlat runResult Algorithm Error Result PropExposure)

-- Test 6: Numbers.count as algorithm argument to Repeat
-- Repeat(step, Numbers.count, init) where Numbers = [10,20,30]
-- step(x) = x + 1, init = 0, count = Numbers.count = 3
-- Result: 0 → 1 → 2 → 3
open KatLang (resolve param num)

def numbersAlg : Algorithm :=
  alg [] [] [] [.num 10, .num 20, .num 30]

-- step: single-param algorithm that adds 1
def stepAlg : Algorithm :=
  alg ["x"] [] [] [.binary .add (.param "x") (.num 1)]

-- Root algorithm that calls Repeat(step, Numbers.count, init)
def repeatArityRoot : Algorithm :=
  algPrivate [] [] [("Numbers", numbersAlg), ("Step", stepAlg)] [
    .call (resolve "repeat") [
        resolve "Step",
        .dotCall (resolve "Numbers") "count" none,
        .num 0
      ]
  ]

def test6 : Bool :=
  match runFlat (.algorithmExpr repeatArityRoot) with
  | Except.ok [3] => true
  | _ => false

#guard test6
-- EXPECTED: Except.ok [3] (step applied 3 times: 0→1→2→3)
#eval runFlat (.algorithmExpr repeatArityRoot)

-- Test 7: Numbers.count as Repeat count (comprehensive)
-- Uses 6 output expressions to verify correct count
def numbersAlg7 : Algorithm :=
  alg [] [] [] [.num 3, .num 5, .num 9, .num 1, .num 0, .num 6]

def testAlg7 : Algorithm :=
  algPrivate [] [] [("Numbers", numbersAlg7)] [
    .call (resolve "repeat") [
        .algorithmExpr (alg ["x"] [] [] [.binary .add (.param "x") (.num 1)]),  -- step: increment
        .dotCall (resolve "Numbers") "count" none,                      -- count: 6
        .num 0                                   -- init: 0
      ]
  ]

def test7 : Bool :=
  match runFlat (.algorithmExpr testAlg7) with
  | Except.ok [6] => true
  | _ => false

#guard test7
-- EXPECTED: Except.ok [6] (step applied 6 times: 0→1→2→3→4→5→6)
#eval runFlat (.algorithmExpr testAlg7)

-- Test 8: 0-param structural property used as Algorithm argument
-- a.X in algorithm position where X has 0 params, returns 42
def xAlg : Algorithm :=
  alg [] [] [] [.num 42]

def receiver8 : Algorithm :=
  algPrivate [] [] [("X", xAlg)] []

-- Use Atoms to force evaluation of the arg algorithm
def test8 : Bool :=
  match runFlat (.call (.resolve "atoms") [.dotCall (.algorithmExpr receiver8) "X" none]) with
  | Except.ok [42] => true
  | _ => false

#guard test8
#eval runFlat (.call (.resolve "atoms") [.dotCall (.algorithmExpr receiver8) "X" none])

-- Test 9: Structural property with params, no args → arity mismatch (navigation-only)
-- a.Inc where Inc(x) = x + 1, no args → error
def incAlg9 : Algorithm :=
  alg ["x"] [] [] [.binary .add (.param "x") (.num 1)]

def receiver9 : Algorithm :=
  algPrivate [] [] [("Inc", incAlg9)] [.num 5]

def test9a : Bool :=
  match runResult (.dotCall (.algorithmExpr receiver9) "Inc" none) with
  | Except.error _ => true   -- arity mismatch: Inc expects 1 arg, got 0
  | Except.ok _ => false

#guard test9a
#eval runResult (.dotCall (.algorithmExpr receiver9) "Inc" none)

-- Test 9b: Structural property with explicit args → direct binding
-- a.Inc(5) where Inc(x) = x + 1 → 6
def test9b : Bool :=
  match runFlat (.dotCall (.algorithmExpr receiver9) "Inc" (some [.num 5])) with
  | Except.ok [6] => true
  | _ => false

#guard test9b
#eval runFlat (.dotCall (.algorithmExpr receiver9) "Inc" (some [.num 5]))

-- Test 10: dotCall with args (a.X(extra)) passed as builtin argument (navigation-only)
-- Repeat(step, a.Count(bias), init)
-- a has Count(b) = 2 + b, bias = 1 → count = 3
-- step(x) = x + 10, init = 0 → 0→10→20→30
-- Note: Count takes 1 param; no receiver injection in navigation-only semantics
def countAlg : Algorithm :=
  alg ["b"] [] [] [.binary .add (.num 2) (.param "b")]

def receiver10 : Algorithm :=
  algPrivate [] [] [("Count", countAlg)] [.num 99]

def test10 : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("R", receiver10)] [
    .call (resolve "repeat") [
        .algorithmExpr (alg ["x"] [] [] [.binary .add (.param "x") (.num 10)]),  -- step
        .dotCall (resolve "R") "Count" (some [.num 1]),   -- count: R.Count(1) = 3
        .num 0                                     -- init
      ]
  ])) with
  | Except.ok [30] => true
  | _ => false

#guard test10
#eval runFlat (.algorithmExpr (algPrivate [] [] [("R", receiver10)] [
  .call (resolve "repeat") [
      .algorithmExpr (alg ["x"] [] [] [.binary .add (.param "x") (.num 10)]),
      .dotCall (resolve "R") "Count" (some [.num 1]),
      .num 0
    ]
]))

-- Test 11: dotCall none syntax for count in Repeat argument position
-- Repeat(Add, Numbers.count, 0, 0) where Numbers.count is encoded as .dotCall
-- Numbers = [3,5,9,1,0,6] → count = 6
-- Add(a,sum) = (a+1, sum + Numbers[a])
-- Result: sum of all Numbers = 3+5+9+1+0+6 = 24, extracted via index 1
def numbersAlg11 : Algorithm :=
  alg [] [] [] [.num 3, .num 5, .num 9, .num 1, .num 0, .num 6]

def addAlg11 : Algorithm :=
  alg ["a", "sum"] [] [] [
    .binary .add (.param "a") (.num 1),
    .binary .add (.param "sum") (.index (resolve "Numbers") (.param "a"))
  ]

def testAlg11 : Algorithm :=
  algPrivate [] [] [("Numbers", numbersAlg11), ("Add", addAlg11)] [
    .index
      (.call (resolve "repeat") [
          resolve "Add",
          .dotCall (resolve "Numbers") "count" none,     -- ← no-arg dotCall
          .num 0,
          .num 0
        ])
      (.num 1)
  ]

def test11 : Bool :=
  match runFlat (.algorithmExpr testAlg11) with
  | Except.ok [24] => true
  | _ => false

#guard test11
-- EXPECTED: Except.ok [24]
#eval runFlat (.algorithmExpr testAlg11)

-- Test 12: dotCall count as Repeat count (simple increment)
-- Same as Test 7 but with dotCall none syntax
-- Numbers has 3 outputs → count = 3, step(x) = x + 1, init = 0 → 3
def numbersAlg12 : Algorithm :=
  alg [] [] [] [.num 10, .num 20, .num 30]

def testAlg12 : Algorithm :=
  algPrivate [] [] [("Numbers", numbersAlg12)] [
    .call (resolve "repeat") [
        .algorithmExpr (alg ["x"] [] [] [.binary .add (.param "x") (.num 1)]),  -- step
        .dotCall (resolve "Numbers") "count" none,                       -- ← no-arg dotCall
        .num 0                                   -- init
      ]
  ]

def test12 : Bool :=
  match runFlat (.algorithmExpr testAlg12) with
  | Except.ok [3] => true
  | _ => false

#guard test12
-- EXPECTED: Except.ok [3]
#eval runFlat (.algorithmExpr testAlg12)

-- Regression: recursive dot-call arguments bind both value and algorithm views,
-- but builtin argument preparation must use the current parameter value when it
-- exists. Otherwise atoms(values) re-enters list.skip(1) while list is computing.
-- `atoms` now traverses list values directly (issue #136); the explicit spread
-- (`rest = list.skip(1)*`) is kept because a sequence-shaped recursion
-- argument is what exercises the current-value binding — mirroring the C#
-- regression test.
def recursiveDotCallListAlg : Algorithm :=
  alg [] [] [] [
    .call (resolve "atoms") [.param "values"]
  ]

def recursiveDotCallRestAlg : Algorithm :=
  alg [] [] [] [
    .sequenceSpread (.dotCall (resolve "list") "skip" (some [.num 1]))
  ]

def recursiveDotCallReduceCollectionAlg : Algorithm :=
  algPrivate ["values"] [] [
    ("list", recursiveDotCallListAlg),
    ("rest", recursiveDotCallRestAlg)
  ] [
    .call (resolve "if") [
      .binary .le (.dotCall (resolve "list") "count" none) (.num 1),
      resolve "list",
      .dotCall (resolve "rest") "reduceCollection" none
    ]
  ]

def recursiveDotCallRoot : Algorithm :=
  algPrivate [] [] [("reduceCollection", recursiveDotCallReduceCollectionAlg)] [
    .call (resolve "reduceCollection") [
      .capture [.num 1, .num 2, .num 3, .num 4]
    ]
  ]

def test12a : Bool :=
  match runFlat (.algorithmExpr recursiveDotCallRoot) with
  | Except.ok [4] => true
  | _ => false

#guard test12a

-- Test 13: named multi-output receiver no longer exposes arity
def arityRemovedRoot13 : Algorithm :=
  algPrivate [] [] [("Data", alg [] [] [] [.num 1, .num 7])] [
    .dotCall (resolve "Data") "arity" none
  ]

def test13 : Bool :=
  match runResult (.algorithmExpr arityRemovedRoot13) with
  | Except.error err => innermostIsUnknownName "arity" err
  | Except.ok _ => false

#guard test13
#eval runResult (.algorithmExpr arityRemovedRoot13)

-- Test 14: inline sequence-value receiver no longer exposes arity
def test14 : Bool :=
  match runResult (.dotCall (.capture [.num 1, .num 7]) "arity" none) with
  | Except.error err => innermostIsUnknownName "arity" err
  | Except.ok _ => false

#guard test14
#eval runResult (.dotCall (.capture [.num 1, .num 7]) "arity" none)

-- Test 14a: extra sequence-value receiver layer no longer exposes arity
def test14a : Bool :=
  match runResult (.dotCall (.capture [.capture [.num 1, .num 7]]) "arity" none) with
  | Except.error err => innermostIsUnknownName "arity" err
  | Except.ok _ => false

#guard test14a
#eval runResult (.dotCall (.capture [.capture [.num 1, .num 7]]) "arity" none)

-- Test 14b: count still works for named, inline, and nested sequence-value receivers
def countReceiverRoot14b : Algorithm :=
  algPrivate [] [] [("Data", alg [] [] [] [.num 1, .num 7])] [
    .dotCall (resolve "Data") "count" none,
    .dotCall (.capture [.num 1, .num 7]) "count" none,
    .dotCall (.capture [.capture [.num 1, .num 7]]) "count" none
  ]

def test14b : Bool :=
  match runFlat (.algorithmExpr countReceiverRoot14b) with
  | Except.ok [2, 2, 2] => true
  | _ => false

#guard test14b
#eval runFlat (.algorithmExpr countReceiverRoot14b)

-- Test 14d: old length intrinsic name is no longer recognized
def test14d : Bool :=
  match runResult (.dotCall (.capture [.num 1, .num 2]) "length" none) with
  | Except.error _ => true
  | Except.ok _ => false

#guard test14d
#eval runResult (.dotCall (.capture [.num 1, .num 2]) "length" none)

-- Test 15: user-defined higher-order call keeps eager value ABI
-- ApplyTwice(f, x) = f(f(x)); passing Inc as an algorithm argument should work.
def incAlg15 : Algorithm :=
  alg ["x"] [] [] [.binary .add (.param "x") (.num 1)]

def applyTwiceAlg15 : Algorithm :=
  alg ["f", "x"] [] [] [
    .call (.param "f") [
      .call (.param "f") [.param "x"]
    ]
  ]

def test15 : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("Inc", incAlg15), ("ApplyTwice", applyTwiceAlg15)] [
    .call (resolve "ApplyTwice") [resolve "Inc", .num 10]
  ])) with
  | Except.ok [12] => true
  | _ => false

#guard test15
#eval runFlat (.algorithmExpr (algPrivate [] [] [("Inc", incAlg15), ("ApplyTwice", applyTwiceAlg15)] [
  .call (resolve "ApplyTwice") [resolve "Inc", .num 10]
]))

-- Test 16: higher-order args preserve flat fixed expression boundaries.
-- UsePair(f, x, y) = f(x) + y; a sequence-value second argument is one argument
-- expression, while a spread of a multi-output value
-- spreads x and y explicitly as separate argument slots.
def usePairAlg16 : Algorithm :=
  alg ["f", "x", "y"] [] [] [
    .binary .add
      (.call (.param "f") [.param "x"])
      (.param "y")
  ]

def pairArg16 : Algorithm :=
  alg [] [] [] [.num 10, .num 20]

-- Source: `UsePair(Inc, Pair)` where Pair = 10, 20 — the named property's
-- sequence value is ONE argument expression.
def test16SequenceValueArgDoesNotUnpack : Bool :=
  match runResult (.algorithmExpr (algPrivate [] []
    [("Inc", incAlg15), ("UsePair", usePairAlg16), ("Pair", pairArg16)] [
    .call (resolve "UsePair") [resolve "Inc", resolve "Pair"]
  ])) with
  | Except.error err => innermostIsArityMismatch 1 0 err
  | Except.ok _ => false

#guard test16SequenceValueArgDoesNotUnpack

-- Source: `UsePair(Inc, Pair*)` where Pair = 10, 20. The spread
-- `Pair*` spreads the pair's two values into the x and y argument slots:
-- Inc(10) + 20 = 31.
def test16SpreadSpreadsValues : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] []
    [("Inc", incAlg15), ("UsePair", usePairAlg16), ("Pair", pairArg16)] [
    .call (resolve "UsePair") [resolve "Inc", sequenceSpread (resolve "Pair")]
  ])) with
  | Except.ok [31] => true
  | _ => false

#guard test16SpreadSpreadsValues
#eval runFlat (.algorithmExpr (algPrivate [] []
  [("Inc", incAlg15), ("UsePair", usePairAlg16), ("Pair", pairArg16)] [
  .call (resolve "UsePair") [resolve "Inc", sequenceSpread (resolve "Pair")]
]))

-- Test 16a: ordinary dot-call fallback preserves receiver as one argument boundary.
def dotCallBoundaryAddAlg16a : Algorithm :=
  alg ["a", "b"] [] [] [
    .binary .add (.param "a") (.param "b")
  ]

def dotCallBoundaryPairReceiverAlg16a : Algorithm :=
  alg [] [] [] [.num 3, .num 7]

def dotCallBoundaryNormalCallsStillWork16a : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("F", dotCallBoundaryAddAlg16a)] [
    .call (resolve "F") [.num 3, .num 7]
  ])) with
  | Except.ok [10] => true
  | _ => false

#guard dotCallBoundaryNormalCallsStillWork16a

def dotCallBoundarySequenceValueDirectCallDoesNotUnpack16a : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("F", dotCallBoundaryAddAlg16a)] [
    .call (resolve "F") [.algorithmExpr dotCallBoundaryPairReceiverAlg16a]
  ])) with
  | Except.error err => innermostIsArityMismatch 1 0 err
  | Except.ok _ => false

#guard dotCallBoundarySequenceValueDirectCallDoesNotUnpack16a

def dotCallBoundaryScalarReceiverStillWorks16a : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("F", dotCallBoundaryAddAlg16a)] [
    .dotCall (.num 3) "F" (some [.num 7])
  ])) with
  | Except.ok [10] => true
  | _ => false

#guard dotCallBoundaryScalarReceiverStillWorks16a

def dotCallBoundaryMultiOutputReceiverNoArgsFails16a : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("F", dotCallBoundaryAddAlg16a)] [
    .dotCall (.algorithmExpr dotCallBoundaryPairReceiverAlg16a) "F" none
  ])) with
  | Except.error _ => true
  | Except.ok _ => false

#guard dotCallBoundaryMultiOutputReceiverNoArgsFails16a

def dotCallBoundaryMultiOutputReceiverEmptyArgsFails16a : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("F", dotCallBoundaryAddAlg16a)] [
    .dotCall (.algorithmExpr dotCallBoundaryPairReceiverAlg16a) "F" (some [])
  ])) with
  | Except.error _ => true
  | Except.ok _ => false

#guard dotCallBoundaryMultiOutputReceiverEmptyArgsFails16a

def dotCallBoundaryCountedPathDoesNotSpread16a : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("F", dotCallBoundaryAddAlg16a)] [
    .dotCall
      (.dotCall (.algorithmExpr dotCallBoundaryPairReceiverAlg16a) "F" none)
      "count"
      none
  ])) with
  | Except.error _ => true
  | Except.ok _ => false

#guard dotCallBoundaryCountedPathDoesNotSpread16a

def dotCallBoundarySequenceValueReceiverAlg16a : Algorithm :=
  alg ["x"] [] [] [.param "x"]

def dotCallBoundaryOneParamGetsSequenceValueReceiver16a : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("G", dotCallBoundarySequenceValueReceiverAlg16a)] [
    .dotCall (.algorithmExpr dotCallBoundaryPairReceiverAlg16a) "G" none
  ])) with
  | Except.ok (.sequenceValue [.atom 3, .atom 7]) => true
  | _ => false

#guard dotCallBoundaryOneParamGetsSequenceValueReceiver16a

def dotCallBoundaryFinalExplicitSequenceValueArgDoesNotUnpack16a : Bool :=
  let hAlg := alg ["a", "b", "c"] [] [] [
    .binary .add
      (.binary .add (.param "a") (.param "b"))
      (.param "c")
  ]
  match runResult (.algorithmExpr (algPrivate [] [] [("H", hAlg)] [
    .dotCall (.num 3) "H" (some [
      .capture [.num 4, .num 5]
    ])
  ])) with
  | Except.error err => innermostIsArityMismatch 1 0 err
  | Except.ok _ => false

#guard dotCallBoundaryFinalExplicitSequenceValueArgDoesNotUnpack16a

def dotCallBoundarySequenceSpreadSpreadsExtraArgs16a : Bool :=
  let hAlg := alg ["a", "b", "c"] [] [] [
    .binary .add
      (.binary .add (.param "a") (.param "b"))
      (.param "c")
  ]
  match runFlat (.algorithmExpr (algPrivate [] [] [("H", hAlg)] [
    .dotCall (.num 3) "H" (some [
      sequenceSpread (.capture [.num 4, .num 5])
    ])
  ])) with
  | Except.ok [12] => true
  | _ => false

#guard dotCallBoundarySequenceSpreadSpreadsExtraArgs16a

def flatFixedIssue101PairAlg : Algorithm :=
  alg [] [] [] [.num 10, .num 20]

def flatFixedIssue101SequenceValuePairAlg : Algorithm :=
  alg [] [] [] [.algorithmExpr flatFixedIssue101PairAlg]

def flatFixedIssue101AddAlg : Algorithm :=
  alg ["x", "y"] [] [] [.binary .add (.param "x") (.param "y")]

def flatFixedIssue101UseAlg : Algorithm :=
  alg ["a", "b", "c"] [] [] [
    .binary .add
      (.binary .add (.param "a") (.param "b"))
      (.param "c")
  ]

def flatFixedIssue101PairDoesNotUnpack : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("Pair", flatFixedIssue101PairAlg), ("Add", flatFixedIssue101AddAlg)] [
    .call (resolve "Add") [resolve "Pair"]
  ])) with
  | Except.error err => innermostIsArityMismatch 1 0 err
  | Except.ok _ => false

#guard flatFixedIssue101PairDoesNotUnpack

def flatFixedIssue101AtomsDoesNotSpread : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("Pair", flatFixedIssue101SequenceValuePairAlg), ("Add", flatFixedIssue101AddAlg)] [
    .call (resolve "Add") [.dotCall (resolve "Pair") "atoms" none]
  ])) with
  | Except.error err => innermostIsArityMismatch 1 0 err
  | Except.ok _ => false

#guard flatFixedIssue101AtomsDoesNotSpread

def flatFixedIssue101SeparateArgsWork : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("Add", flatFixedIssue101AddAlg)] [
    .call (resolve "Add") [.num 10, .num 20]
  ])) with
  | Except.ok [30] => true
  | _ => false

#guard flatFixedIssue101SeparateArgsWork

def flatFixedIssue101ExplicitIndexingWorks : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("Pair", flatFixedIssue101PairAlg), ("Add", flatFixedIssue101AddAlg)] [
    .call (resolve "Add") [
      .index (resolve "Pair") (.num 0),
      .index (resolve "Pair") (.num 1)
    ]
  ])) with
  | Except.ok [30] => true
  | _ => false

#guard flatFixedIssue101ExplicitIndexingWorks

def flatFixedIssue101MixedPrefixDoesNotUnpack : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("Tail", alg [] [] [] [.num 2, .num 3]), ("Use", flatFixedIssue101UseAlg)] [
    .call (resolve "Use") [.num 1, resolve "Tail"]
  ])) with
  | Except.error err => innermostIsArityMismatch 1 0 err
  | Except.ok _ => false

#guard flatFixedIssue101MixedPrefixDoesNotUnpack

-- Source `Use(1, Tail*)`: a plain leading argument `1` followed by `Tail*`
-- which spreads Tail's items 2, 3. Three call arguments → 1 + 2 + 3 = 6.
def flatFixedIssue101SequenceSpreadSpreadsArgs : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("Tail", alg [] [] [] [.num 2, .num 3]), ("Use", flatFixedIssue101UseAlg)] [
    .call (resolve "Use") [.num 1, sequenceSpread (resolve "Tail")]
  ])) with
  | Except.ok [6] => true
  | _ => false

#guard flatFixedIssue101SequenceSpreadSpreadsArgs

def collectingParameterForwardingCountItemAlg : Algorithm :=
  algWithParameters [
    { name := "values", kind := .collecting },
    { name := "item", kind := .normal }
  ] [] [] [
    .dotCall
      (.dotCall (.param "values") "filter" (some [
        .algorithmExpr (alg ["value"] [] [] [
          .binary .eq (.param "value") (.param "item")
        ])
      ]))
      "count"
      none
  ]

-- Forwarding a collected list into another collecting callable is explicit list
-- spread (`CountItem(values*, candidate)`): spread(collect(xs)) = xs, so the
-- callee re-collects exactly the caller's items.
def collectingParameterForwardingModeFreqsExpr : KatLang.Expr :=
  .dotCall
    (.dotCall (.param "values") "distinct" none)
    "map"
    (some [
      .algorithmExpr (alg ["candidate"] [] [] [
        .call (resolve "CountItem") [sequenceSpread (.param "values"), .param "candidate"]
      ])
    ])

def collectingParameterForwardingDirectUseAlg : Algorithm :=
  algWithParameters [{ name := "values", kind := .collecting }] [] [] [
    .call (resolve "CountItem") [sequenceSpread (.param "values"), .num 1]
  ]

def collectingParameterForwardingDirectCall : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("CountItem", collectingParameterForwardingCountItemAlg),
    ("Use", collectingParameterForwardingDirectUseAlg)
  ] [
    .call (resolve "Use") [sequenceSpread (sequenceItems [.num 1, .num 1, .num 2, .num 4, .num 4])]
  ])) with
  | Except.ok [2] => true
  | _ => false

#guard collectingParameterForwardingDirectCall

def collectingParameterForwardingFreqsAlg : Algorithm :=
  algWithParameters [{ name := "values", kind := .collecting }] [] [] [
    collectingParameterForwardingModeFreqsExpr
  ]

def collectingParameterForwardingCallbackBody : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("CountItem", collectingParameterForwardingCountItemAlg),
    ("Mode", collectingParameterForwardingFreqsAlg)
  ] [
    .call (resolve "Mode") [sequenceSpread (sequenceItems [.num 1, .num 1, .num 2, .num 4, .num 4])]
  ])) with
  | Except.ok [2, 1, 2] => true
  | _ => false

#guard collectingParameterForwardingCallbackBody

def collectingParameterForwardingModeAlg : Algorithm :=
  algWithParameters [{ name := "values", kind := .collecting }] [] [
    privateProp "Freqs" (alg [] [] [] [collectingParameterForwardingModeFreqsExpr]),
    privateProp "MaxFreq" (alg [] [] [] [.dotCall (resolve "Freqs") "max" none])
  ] [
    .dotCall
      (.dotCall (.param "values") "distinct" none)
      "filter"
      (some [
        .algorithmExpr (alg ["candidate"] [] [] [
          .binary .eq
            (.call (resolve "CountItem") [sequenceSpread (.param "values"), .param "candidate"])
            (resolve "MaxFreq")
        ])
      ])
  ]

def collectingParameterForwardingFullMode : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("CountItem", collectingParameterForwardingCountItemAlg),
    ("Mode", collectingParameterForwardingModeAlg)
  ] [
    .call (resolve "Mode") [sequenceSpread (sequenceItems [.num 1, .num 1, .num 2, .num 4, .num 4])]
  ])) with
  | Except.ok [1, 4] => true
  | _ => false

#guard collectingParameterForwardingFullMode

def collectingParameterForwardingNonVariadicCollectAlg : Algorithm :=
  alg ["list"] [] [] [.dotCall (.param "list") "count" none]

def collectingParameterForwardingNonVariadicUseAlg : Algorithm :=
  algWithParameters [{ name := "values", kind := .collecting }] [] [] [
    .call (resolve "Collect") [.param "values"]
  ]

-- Passing the collected list WITHOUT spread passes one list argument: `Collect(values)`
-- binds the fixed parameter to the collected list, and `list.count` opens it
-- (the ForwardAsOne shape).
def collectingParameterForwardingNonVariadicCalleeConsumesCollectedList : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("Collect", collectingParameterForwardingNonVariadicCollectAlg),
    ("Use", collectingParameterForwardingNonVariadicUseAlg)
  ] [
    .call (resolve "Use") [sequenceSpread (sequenceItems [.num 10, .num 20, .num 30])]
  ])) with
  | Except.ok [3] => true
  | _ => false

#guard collectingParameterForwardingNonVariadicCalleeConsumesCollectedList

def collectingParameterForwardingCountSequenceValueAlg : Algorithm :=
  algWithParameterPatterns [
    .sequenceValue [.capture { name := "values", kind := .collecting }]
  ] [] [] [.dotCall (.param "values") "count" none]

def collectingParameterForwardingSequenceValueUseAlg : Algorithm :=
  algWithParameters [{ name := "values", kind := .collecting }] [] [] [
    .call (resolve "CountSequenceValue") [.param "values"]
  ]

-- A deconstruction-shaped callee (`CountSequenceValue((*values))`) opens a
-- bare-forwarded collected LIST through its lone-structure rule, so the unspread
-- forward still reaches the items.
def collectingParameterForwardingSequenceValueVariadicPatternPreservesBehavior : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("CountSequenceValue", collectingParameterForwardingCountSequenceValueAlg),
    ("Use", collectingParameterForwardingSequenceValueUseAlg)
  ] [
    .call (resolve "Use") [sequenceSpread (sequenceItems [.num 10, .num 20, .num 30])]
  ])) with
  | Except.ok [3] => true
  | _ => false

#guard collectingParameterForwardingSequenceValueVariadicPatternPreservesBehavior

def collectingParameterForwardingSequenceValueHistoryArg : KatLang.Expr :=
  .capture [.num 1, .num 2, .num 3]

def collectingParameterForwardingFindNextAlg : Algorithm :=
  algWithParameters [
    { name := "history", kind := .collecting },
    { name := "pre1", kind := .normal },
    { name := "pre2", kind := .normal }
  ] [] [] [
    .binary .add
      (.binary .add (.dotCall (.param "history") "count" none) (.param "pre1"))
      (.param "pre2")
  ]

def collectingParameterForwardingSequenceValueStepAlg : Algorithm :=
  algWithParameterPatterns [
    .sequenceValue [.capture { name := "history", kind := .collecting }],
    .capture { name := "pre2", kind := .normal },
    .capture { name := "pre1", kind := .normal }
  ] [] [] [
    .call (resolve "FindNext") [sequenceSpread (.param "history"), .param "pre1", .param "pre2"]
  ]

def collectingParameterForwardingSequenceValueVariadicCaptureSpreadsCompatibleSlot : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("FindNext", collectingParameterForwardingFindNextAlg),
    ("YSStep", collectingParameterForwardingSequenceValueStepAlg)
  ] [
    .call (resolve "YSStep") [collectingParameterForwardingSequenceValueHistoryArg, .num 2, .num 3]
  ])) with
  | Except.ok [8] => true
  | _ => false

#guard collectingParameterForwardingSequenceValueVariadicCaptureSpreadsCompatibleSlot

def collectingParameterForwardingCountItemsByOtherNameAlg : Algorithm :=
  algWithParameters [
    { name := "items", kind := .collecting },
    { name := "last", kind := .normal }
  ] [] [] [
    .binary .add (.dotCall (.param "items") "count" none) (.param "last")
  ]

def collectingParameterForwardingSequenceValueHistoryUseOtherNameAlg : Algorithm :=
  algWithParameterPatterns [
    .sequenceValue [.capture { name := "history", kind := .collecting }],
    .capture { name := "last", kind := .normal }
  ] [] [] [
    .call (resolve "CountItems") [sequenceSpread (.param "history"), .param "last"]
  ]

-- Spread forwarding is pure value semantics: the callee's collecting parameter may use any
-- parameter name — there is no name-based or provenance-based special path.
def collectingParameterForwardingSequenceValueCaptureSpreadForwardsUnderAnyName : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("CountItems", collectingParameterForwardingCountItemsByOtherNameAlg),
    ("Use", collectingParameterForwardingSequenceValueHistoryUseOtherNameAlg)
  ] [
    .call (resolve "Use") [collectingParameterForwardingSequenceValueHistoryArg, .num 7]
  ])) with
  | Except.ok [10] => true
  | _ => false

#guard collectingParameterForwardingSequenceValueCaptureSpreadForwardsUnderAnyName

def collectingParameterForwardingSequenceValueHistoryNonVariadicUseAlg : Algorithm :=
  algWithParameterPatterns [
    .sequenceValue [.capture { name := "history", kind := .collecting }],
    .capture { name := "marker", kind := .normal }
  ] [] [] [
    .call (resolve "Collect") [.param "history"]
  ]

def collectingParameterForwardingSequenceValueCaptureForwardsSequenceValue : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("Collect", collectingParameterForwardingNonVariadicCollectAlg),
    ("Use", collectingParameterForwardingSequenceValueHistoryNonVariadicUseAlg)
  ] [
    .call (resolve "Use") [collectingParameterForwardingSequenceValueHistoryArg, .num 99]
  ])) with
  | Except.ok [3] => true
  | _ => false

#guard collectingParameterForwardingSequenceValueCaptureForwardsSequenceValue

def collectingParameterForwardingTakeLastAlg : Algorithm :=
  algWithParameters [
    { name := "first", kind := .collecting },
    { name := "last", kind := .normal }
  ] [] [] [
    .dotCall (.param "first") "count" none
  ]

def collectingParameterForwardingSequenceValueHistoryTakeLastUseAlg : Algorithm :=
  algWithParameterPatterns [
    .sequenceValue [.capture { name := "history", kind := .collecting }],
    .capture { name := "marker", kind := .normal }
  ] [] [] [
    .call (resolve "TakeLast") [.num 0, .param "history"]
  ]

def collectingParameterForwardingSequenceValueCaptureOnlyExpandsInTargetVariadicSlot : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("TakeLast", collectingParameterForwardingTakeLastAlg),
    ("Use", collectingParameterForwardingSequenceValueHistoryTakeLastUseAlg)
  ] [
    .call (resolve "Use") [collectingParameterForwardingSequenceValueHistoryArg, .num 99]
  ])) with
  | Except.ok [1] => true
  | _ => false

#guard collectingParameterForwardingSequenceValueCaptureOnlyExpandsInTargetVariadicSlot

def collectingParameterForwardingSequenceValueLoopStepAlg : Algorithm :=
  algWithParameterPatterns [
    .sequenceValue [.capture { name := "history", kind := .collecting }],
    .capture { name := "pre2", kind := .normal },
    .capture { name := "pre1", kind := .normal }
  ] [] [] [
    .call (resolve "FindNext") [sequenceSpread (.param "history"), .param "pre1", .param "pre2"],
    .param "pre1",
    .param "pre2"
  ]

def collectingParameterForwardingLoopStepSequenceValueCaptureSpreadsCompatibleSlot : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("FindNext", collectingParameterForwardingFindNextAlg),
    ("YSStep", collectingParameterForwardingSequenceValueLoopStepAlg)
  ] [
    .index
      (.dotCall (resolve "YSStep") "repeat" (some [
        .num 1, collectingParameterForwardingSequenceValueHistoryArg, .num 2, .num 3
      ]))
      (.num 0)
  ])) with
  | Except.ok [8] => true
  | _ => false

#guard collectingParameterForwardingLoopStepSequenceValueCaptureSpreadsCompatibleSlot

def flatFixedIssue101NestedSequenceValueBoundaryPreserved : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("A", alg [] [] [] [.num 1, .capture [.num 2, .num 3]])] [
    resolve "A"
  ])) with
  | Except.ok (.sequenceValue [.atom 1, .sequenceValue [.atom 2, .atom 3]]) => true
  | _ => false

#guard flatFixedIssue101NestedSequenceValueBoundaryPreserved

def flatFixedIssue101ExplicitOuterBodyGroupingEquivalent : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("A", alg [] [] [] [.capture [.num 1, .capture [.num 2, .num 3]]])] [
    resolve "A"
  ])) with
  | Except.ok (.sequenceValue [.atom 1, .sequenceValue [.atom 2, .atom 3]]) => true
  | _ => false

#guard flatFixedIssue101ExplicitOuterBodyGroupingEquivalent

-- Internal value shaped like sequence-value source `(1, (2, 3)*)`: a leading `1`
-- combined with a spread of the sequence value (2, 3), whose items 2 and
-- 3 are flattened by the spread.
def flatFixedIssue101SequenceSpreadFlattensNestedBlock : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("A", alg [] [] [] [.sequenceConstruct (.num 1) (sequenceSpread (.capture [.num 2, .num 3]))])] [
    resolve "A"
  ])) with
  | Except.ok [1, 2, 3] => true
  | _ => false

#guard flatFixedIssue101SequenceSpreadFlattensNestedBlock

def flatFixedIssue101DotReceiverDoesNotUnpack : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("Pair", flatFixedIssue101PairAlg), ("Add", flatFixedIssue101AddAlg)] [
    .dotCall (resolve "Pair") "Add" none
  ])) with
  | Except.error err => innermostIsArityMismatch 1 0 err
  | Except.ok _ => false

#guard flatFixedIssue101DotReceiverDoesNotUnpack

def flatFixedIssue101SequenceSpreadDotReceiverDoesNotUnpack : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("Pair", flatFixedIssue101PairAlg), ("Add", flatFixedIssue101AddAlg)] [
    .dotCall (sequenceSpreadReceiver (resolve "Pair")) "Add" none
  ])) with
  | Except.error err => innermostIsArityMismatch 1 0 err
  | Except.ok _ => false

#guard flatFixedIssue101SequenceSpreadDotReceiverDoesNotUnpack

def dotCallBoundarySequenceBuiltinsStillExpand16a : Bool :=
  match runFlat (.algorithmExpr (alg [] [] [] [
    .dotCall (.algorithmExpr dotCallBoundaryPairReceiverAlg16a) "sum" none,
    .dotCall (.algorithmExpr dotCallBoundaryPairReceiverAlg16a) "count" none,
    .dotCall (.algorithmExpr dotCallBoundaryPairReceiverAlg16a) "first" none,
    .dotCall (.algorithmExpr dotCallBoundaryPairReceiverAlg16a) "last" none
  ])) with
  | Except.ok [10, 2, 3, 7] => true
  | _ => false

#guard dotCallBoundarySequenceBuiltinsStillExpand16a

-- Test 17: extra higher-order args are not silently ignored
-- TakeFunc(f) called with two algorithm args should raise arity mismatch.
def takeFuncAlg17 : Algorithm :=
  alg ["f"] [] [] [.num 0]

def test17 : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("Inc", incAlg15), ("TakeFunc", takeFuncAlg17)] [
    .call (resolve "TakeFunc") [resolve "Inc", resolve "Inc"]
  ])) with
  | Except.error _ => true
  | Except.ok _ => false

#guard test17
#eval runResult (.algorithmExpr (algPrivate [] [] [("Inc", incAlg15), ("TakeFunc", takeFuncAlg17)] [
  .call (resolve "TakeFunc") [resolve "Inc", resolve "Inc"]
]))

-- Test 18: structural property calls share higher-order binding semantics
-- Receiver.ApplyTwice(Inc, 10) should bind Inc through AlgEnv and return 12.
def receiver18 : Algorithm :=
  algPrivate [] [] [("ApplyTwice", applyTwiceAlg15)] []

def outer18 : Algorithm :=
  algPrivate [] [] [("Inc", incAlg15), ("Receiver", receiver18)] [
    .dotCall (resolve "Receiver") "ApplyTwice" (some [resolve "Inc", .num 10])
  ]

def test18 : Bool :=
  match runFlat (.algorithmExpr outer18) with
  | Except.ok [12] => true
  | _ => false

#guard test18
#eval runFlat (.algorithmExpr outer18)

-- Test 19: an inline algorithm block ALWAYS provides its contained Algorithm
-- on the algorithm channel, regardless of parameter/declaration/output count —
-- `{42}` is as much an Algorithm as `{a + 1}`. Reading the bound parameter as
-- a value still observes the block's value; calling it invokes the algorithm.
-- (A capture, by contrast, never crosses: see captureSuppressesCallableIdentity.)
def constSevenAlg19 : Algorithm :=
  alg [] [] [] [.num 7]

def twoValueAlg19 : Algorithm :=
  alg [] [] [] [.num 1, .num 2]

def readInlineArgAlg19 : Algorithm :=
  alg ["f"] [] [] [
    .param "f"
  ]

def callInlineArgAlg19 : Algorithm :=
  alg ["f"] [] [] [
    .call (.param "f") []
  ]

def test19 : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("Apply", readInlineArgAlg19)] [
    .call (resolve "Apply") [.algorithmExpr constSevenAlg19]
  ])) with
  | Except.ok [7] => true
  | _ => false

#guard test19
#eval runFlat (.algorithmExpr (algPrivate [] [] [("Apply", readInlineArgAlg19)] [
  .call (resolve "Apply") [.algorithmExpr constSevenAlg19]
]))

-- `Call0({7})`: the zero-parameter inline block crosses the higher-order
-- boundary and `f()` invokes it — exactly like a named zero-parameter
-- property (`Call0(Const)`).
def test19SingleOutputBlockCrossesHigherOrderBoundary : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("Apply", callInlineArgAlg19)] [
    .call (resolve "Apply") [.algorithmExpr constSevenAlg19]
  ])) with
  | Except.ok [7] => true
  | _ => false

#guard test19SingleOutputBlockCrossesHigherOrderBoundary
#eval runFlat (.algorithmExpr (algPrivate [] [] [("Apply", callInlineArgAlg19)] [
  .call (resolve "Apply") [.algorithmExpr constSevenAlg19]
]))

def test19MultiOutput : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("Apply", readInlineArgAlg19)] [
    .call (resolve "Apply") [.algorithmExpr twoValueAlg19]
  ])) with
  | Except.ok [1, 2] => true
  | _ => false

#guard test19MultiOutput
#eval runFlat (.algorithmExpr (algPrivate [] [] [("Apply", readInlineArgAlg19)] [
  .call (resolve "Apply") [.algorithmExpr twoValueAlg19]
]))

-- Multi-output blocks cross identically: output count never gates algorithm
-- identity, and `f()` emits the block algorithm's two outputs.
def test19MultiOutputBlockCrossesHigherOrderBoundary : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("Apply", callInlineArgAlg19)] [
    .call (resolve "Apply") [.algorithmExpr twoValueAlg19]
  ])) with
  | Except.ok [1, 2] => true
  | _ => false

#guard test19MultiOutputBlockCrossesHigherOrderBoundary
#eval runFlat (.algorithmExpr (algPrivate [] [] [("Apply", callInlineArgAlg19)] [
  .call (resolve "Apply") [.algorithmExpr twoValueAlg19]
]))

-- Test 19a: same-name clause-group elaboration classifies a sole plain-binder
-- clause as an ordinary algorithm, not a conditional.
def applyClauseBody19a : Algorithm :=
  alg [] [] [] [
    .call (.param "f") [.param "x"]
  ]

def applyClauseAlg19a : Algorithm :=
  Algorithm.elaborateClauseGroup [{
    pattern := KatLang.Pattern.sequenceValue [KatLang.Pattern.bind "x", KatLang.Pattern.bind "f"]
    body := applyClauseBody19a
  }]

def test19aShape : Bool :=
  match applyClauseAlg19a with
  | .mk _ [.capture { name := "x", kind := .normal }, .capture { name := "f", kind := .normal }] _ _ _ => true
  | _ => false

#guard test19aShape

def test19aRun : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("Inc", incAlg15), ("Apply", applyClauseAlg19a)] [
    .call (resolve "Apply") [.num 9, resolve "Inc"]
  ])) with
  | Except.ok [10] => true
  | _ => false

#guard test19aRun

def idClauseAlg19a : Algorithm :=
  Algorithm.elaborateClauseGroup [{
    pattern := KatLang.Pattern.bind "x"
    body := alg [] [] [] [.param "x"]
  }]

def test19aSingleBinderShape : Bool :=
  match Algorithm.elaborateClauseGroup [{
      pattern := KatLang.Pattern.bind "x"
      body := alg [] [] [] [.param "x"]
    }] with
  | .mk _ [.capture { name := "x", kind := .normal }] _ _ _ => true
  | _ => false

#guard test19aSingleBinderShape

def test19aSingleBinderRun : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("Id", idClauseAlg19a)] [
    .call (resolve "Id") [.num 7]
  ])) with
  | Except.ok [7] => true
  | _ => false

#guard test19aSingleBinderRun

def fallbackClauseAlg19a : Algorithm :=
  Algorithm.elaborateClauseGroup [
    {
      pattern := KatLang.Pattern.litInt 0
      body := alg [] [] [] [.num 0]
    },
    {
      pattern := KatLang.Pattern.bind "x"
      body := alg [] [] [] [.num 1]
    }
  ]

def test19aMultiClauseShape : Bool :=
  match fallbackClauseAlg19a with
  | .conditional _ _ [_, _] => true
  | _ => false

#guard test19aMultiClauseShape

def test19aMultiClauseRun : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("F", fallbackClauseAlg19a)] [
    .call (resolve "F") [.num 2]
  ])) with
  | Except.ok [1] => true
  | _ => false

#guard test19aMultiClauseRun

def test19aLiteralPatternIsConditional : Bool :=
  match Algorithm.elaborateClauseGroup [{
      pattern := KatLang.Pattern.litInt 1
      body := alg [] [] [] [.num 42]
    }] with
  | .conditional _ _ [_] => true
  | _ => false

#guard test19aLiteralPatternIsConditional

def test19aSequenceValuePatternIsOrdinaryStructuredParameter : Bool :=
  match Algorithm.elaborateClauseGroup [{
      pattern := KatLang.Pattern.sequenceValue [
        KatLang.Pattern.bind "x",
        KatLang.Pattern.sequenceValue [KatLang.Pattern.bind "acc", KatLang.Pattern.bind "counter"]
      ]
      body := alg [] [] [] [.param "x"]
    }] with
  | .mk _ [.capture { name := "x" }, .sequenceValue [.capture { name := "acc" }, .capture { name := "counter" }]] _ _ _ => true
  | _ => false

#guard test19aSequenceValuePatternIsOrdinaryStructuredParameter

def repeatedFlatClauseAlg : Algorithm :=
  Algorithm.elaborateClauseGroup [{
    pattern := KatLang.Pattern.sequenceValue [
      KatLang.Pattern.bind "x",
      KatLang.Pattern.bind "x"
    ]
    body := alg [] [] [] [.param "x"]
  }]

def repeatedFlatClauseEqualArgumentsMatch : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("F", repeatedFlatClauseAlg)] [
    .call (resolve "F") [.num 1, .num 1]
  ])) with
  | Except.ok [1] => true
  | _ => false

#guard repeatedFlatClauseEqualArgumentsMatch

def repeatedFlatClauseUnequalArgumentsFail : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("F", repeatedFlatClauseAlg)] [
    .call (resolve "F") [.num 1, .num 2]
  ])) with
  | Except.error err => innermostIsBadArity err
  | _ => false

#guard repeatedFlatClauseUnequalArgumentsFail

def repeatedSequenceValueClauseAlg : Algorithm :=
  Algorithm.elaborateClauseGroup [{
    pattern := KatLang.Pattern.sequenceValue [
      KatLang.Pattern.sequenceValue [
        KatLang.Pattern.bind "x",
        KatLang.Pattern.bind "x"
      ]
    ]
    body := alg [] [] [] [.param "x"]
  }]

def repeatedSequenceValueClauseMatchesOnlyEqualItems : Bool :=
  let equalCall :=
    runFlat (.algorithmExpr (algPrivate [] [] [("F", repeatedSequenceValueClauseAlg)] [
      .call (resolve "F") [
        .capture [.num 1, .num 1]
      ]
    ]))
  let unequalCall :=
    runResult (.algorithmExpr (algPrivate [] [] [("F", repeatedSequenceValueClauseAlg)] [
      .call (resolve "F") [
        .capture [.num 1, .num 2]
      ]
    ]))
  match equalCall, unequalCall with
  | Except.ok [1], Except.error err => innermostIsBadArity err
  | _, _ => false

#guard repeatedSequenceValueClauseMatchesOnlyEqualItems

def repeatedAcrossNestedClauseAlg : Algorithm :=
  Algorithm.elaborateClauseGroup [{
    pattern := KatLang.Pattern.sequenceValue [
      KatLang.Pattern.bind "x",
      KatLang.Pattern.sequenceValue [KatLang.Pattern.bind "x"]
    ]
    body := alg [] [] [] [.param "x"]
  }]

def repeatedAcrossNestedClauseMatchesOnlyEqualItems : Bool :=
  let equalCall :=
    runFlat (.algorithmExpr (algPrivate [] [] [("F", repeatedAcrossNestedClauseAlg)] [
      .call (resolve "F") [
        .num 1,
        .capture [.num 1]
      ]
    ]))
  let unequalCall :=
    runResult (.algorithmExpr (algPrivate [] [] [("F", repeatedAcrossNestedClauseAlg)] [
      .call (resolve "F") [
        .num 1,
        .capture [.num 2]
      ]
    ]))
  match equalCall, unequalCall with
  | Except.ok [1], Except.error err => innermostIsBadArity err
  | _, _ => false

#guard repeatedAcrossNestedClauseMatchesOnlyEqualItems

def repeatedFlatClauseUsesStructuralSequenceValueEquality : Bool :=
  let sequenceValueAlg := Algorithm.elaborateClauseGroup [{
    pattern := KatLang.Pattern.sequenceValue [
      KatLang.Pattern.bind "x",
      KatLang.Pattern.bind "x"
    ]
    body := alg [] [] [] [.param "x"]
  }]
  match runFlat (.algorithmExpr (algPrivate [] [] [("F", sequenceValueAlg)] [
    .call (resolve "F") [
      .capture [.num 1, .num 2],
      .capture [.num 1, .num 2]
    ]
  ])) with
  | Except.ok [1, 2] => true
  | _ => false

#guard repeatedFlatClauseUsesStructuralSequenceValueEquality

def repeatedPatternProducesOneBinding : Bool :=
  match KatLang.matchPattern
      (.sequenceValue [.bind "x", .bind "x"])
      (.sequenceValue [.atom 4, .atom 4]) with
  | some bindings => bindings == [("x", .atom 4)]
  | none => false

#guard repeatedPatternProducesOneBinding

def repeatedAlgorithmOnlyArgumentsAreUnsupported : Bool :=
  let applySame := Algorithm.elaborateClauseGroup [{
    pattern := KatLang.Pattern.sequenceValue [
      KatLang.Pattern.bind "f",
      KatLang.Pattern.bind "f"
    ]
    body := alg [] [] [] [
      .call (.param "f") [.num 1]
    ]
  }]
  match runResult (.algorithmExpr (algPrivate [] [] [
    ("Inc", incAlg15),
    ("ApplySame", applySame)
  ] [
    .call (resolve "ApplySame") [resolve "Inc", resolve "Inc"]
  ])) with
  | Except.error err =>
      innermostIsTypeMismatch
        "Repeated bind equality is not supported for algorithm-only arguments"
        err
  | _ => false

#guard repeatedAlgorithmOnlyArgumentsAreUnsupported

def repeatedConditionalFallbackAlg : Algorithm :=
  Algorithm.elaborateClauseGroup [
    {
      pattern := KatLang.Pattern.sequenceValue [
        KatLang.Pattern.bind "x",
        KatLang.Pattern.bind "x"
      ]
      body := alg [] [] [] [.num 1]
    },
    {
      pattern := KatLang.Pattern.sequenceValue [
        KatLang.Pattern.bind "x",
        KatLang.Pattern.bind "y"
      ]
      body := alg [] [] [] [.num 0]
    }
  ]

def repeatedConditionalFallbackWorks : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("Equal", repeatedConditionalFallbackAlg)] [
    .call (resolve "Equal") [.num 1, .num 1],
    .call (resolve "Equal") [.num 1, .num 2]
  ])) with
  | Except.ok [1, 0] => true
  | _ => false

#guard repeatedConditionalFallbackWorks

def repeatedSequenceValueConditionalFallbackWorks : Bool :=
  let samePair := Algorithm.elaborateClauseGroup [
    {
      pattern := KatLang.Pattern.sequenceValue [
        KatLang.Pattern.sequenceValue [
          KatLang.Pattern.bind "x",
          KatLang.Pattern.bind "x"
        ]
      ]
      body := alg [] [] [] [.num 1]
    },
    {
      pattern := KatLang.Pattern.sequenceValue [
        KatLang.Pattern.sequenceValue [
          KatLang.Pattern.bind "x",
          KatLang.Pattern.bind "y"
        ]
      ]
      body := alg [] [] [] [.num 0]
    }
  ]
  match runFlat (.algorithmExpr (algPrivate [] [] [("SamePair", samePair)] [
    .call (resolve "SamePair") [
      .capture [.num 5, .num 5]
    ],
    .call (resolve "SamePair") [
      .capture [.num 5, .num 6]
    ]
  ])) with
  | Except.ok [1, 0] => true
  | _ => false

#guard repeatedSequenceValueConditionalFallbackWorks

-- Repeated-bind equality must also hold on the counted callback path
-- (map/filter/reduce), not only on direct user calls. The non-counted guards
-- above exercise `mergeEqualValEnv` / `matchCallPattern`; these guards exercise
-- the counted matchers (`mergeEqualCountedParamEnv`, `matchCountedPatternInto`)
-- so both paths stay aligned with C# EvaluatorTests.Eval_Callback_Repeated*.

-- Ordinary sequenceValue repeated binder reused as a map callback: equal pair items
-- bind once and project the shared value.
def repeatedSequenceValueBinderCallbackEqualItemsMap : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("Same", repeatedSequenceValueClauseAlg)] [
    .call (resolve "map") [
      sequenceItems [
        .capture [.num 1, .num 1],
        .capture [.num 2, .num 2]
      ],
      .resolve "Same"
    ]
  ])) with
  | Except.ok [1, 2] => true
  | _ => false

#guard repeatedSequenceValueBinderCallbackEqualItemsMap

-- An unequal pair item fails the equality constraint with the same badArity
-- shape as the direct-call path.
def repeatedSequenceValueBinderCallbackUnequalItemMapFails : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("Same", repeatedSequenceValueClauseAlg)] [
    .call (resolve "map") [
      sequenceItems [
        .capture [.num 1, .num 2],
        .capture [.num 3, .num 3]
      ],
      .resolve "Same"
    ]
  ])) with
  | Except.error err => innermostIsBadArity err
  | _ => false

#guard repeatedSequenceValueBinderCallbackUnequalItemMapFails

-- Conditional sequenceValue repeated binder reused as a map callback: the equality
-- branch matches equal pairs while unequal pairs fall through to the next clause.
def repeatedSequenceValueConditionalCallbackAlg : Algorithm :=
  Algorithm.elaborateClauseGroup [
    {
      pattern := KatLang.Pattern.sequenceValue [
        KatLang.Pattern.sequenceValue [
          KatLang.Pattern.bind "x",
          KatLang.Pattern.bind "x"
        ]
      ]
      body := alg [] [] [] [.num 1]
    },
    {
      pattern := KatLang.Pattern.sequenceValue [
        KatLang.Pattern.sequenceValue [
          KatLang.Pattern.bind "x",
          KatLang.Pattern.bind "y"
        ]
      ]
      body := alg [] [] [] [.num 0]
    }
  ]

def repeatedSequenceValueConditionalCallbackFallthroughMap : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("Equal", repeatedSequenceValueConditionalCallbackAlg)] [
    .call (resolve "map") [
      sequenceItems [
        .capture [.num 1, .num 1],
        .capture [.num 1, .num 2]
      ],
      .resolve "Equal"
    ]
  ])) with
  | Except.ok [1, 0] => true
  | _ => false

#guard repeatedSequenceValueConditionalCallbackFallthroughMap

-- A map callback whose parameter name collides with an enclosing call parameter
-- must not recurse without bound. `Wrap(x)` shares the name `x` with `Pick`'s
-- pattern variable; the bad map shape (`Pick` over scalar items) makes the
-- `Wrap` argument fail, which previously deferred it as a self-referential thunk
-- that re-entered the same map call forever (C#: process-crashing stack
-- overflow). The evaluator must instead terminate with a structured error.
-- Mirrors C# SequenceCallbackArgumentTests.CallbackArgumentInsideUserCall_FailsCleanly.
def callbackParamCollisionWrapAlg : Algorithm :=
  alg ["x"] [] [] [.param "x"]

def callbackParamCollisionPickAlg : Algorithm :=
  algWithParameterPatterns [
    .sequenceValue [.capture { name := "x", kind := .normal }, .capture { name := "y", kind := .normal }]
  ] [] [] [.param "x"]

def callbackParamCollisionProgram : KatLang.Expr :=
  .algorithmExpr (algPrivate [] [] [
    ("Wrap", callbackParamCollisionWrapAlg),
    ("Pick", callbackParamCollisionPickAlg)
  ] [
    .call (resolve "Wrap") [
      .dotCall
        (.dotCall (sequenceItems [.num 1, .num 2]) "map" (some [resolve "Pick"]))
        "sum" none
    ]
  ])

-- The key property is termination: it returns a structured error rather than
-- looping. (Before the fix the Lean model was non-terminating on this shape.)
def callbackParamCollisionFailsCleanly : Bool :=
  match runResult callbackParamCollisionProgram with
  | Except.error _ => true
  | _ => false

#guard callbackParamCollisionFailsCleanly

-- Test 19b: compatibility fallback for a manually constructed single-branch
-- flat-binder conditional still preserves higher-order args in the core AST.
def applyCondAlg19b : Algorithm :=
  .conditional none [] [
    ⟨ KatLang.Pattern.sequenceValue [KatLang.Pattern.bind "x", KatLang.Pattern.bind "f"],
      alg [] [] [] [
        .call (.param "f") [.param "x"]
      ] ⟩
  ]

def test19b : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("Inc", incAlg15), ("Apply", applyCondAlg19b)] [
    .call (resolve "Apply") [.num 9, resolve "Inc"]
  ])) with
  | Except.ok [10] => true
  | _ => false

#guard test19b
#eval runFlat (.algorithmExpr (algPrivate [] [] [("Inc", incAlg15), ("Apply", applyCondAlg19b)] [
  .call (resolve "Apply") [.num 9, resolve "Inc"]
]))

-- Test 19c: structural property call preserves higher-order args for the same subset
def receiver19c : Algorithm :=
  algPrivate [] [] [("Apply", applyCondAlg19b)] []

def test19c : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("Inc", incAlg15), ("Receiver", receiver19c)] [
    .dotCall (resolve "Receiver") "Apply" (some [.num 9, resolve "Inc"])
  ])) with
  | Except.ok [10] => true
  | _ => false

#guard test19c
#eval runFlat (.algorithmExpr (algPrivate [] [] [("Inc", incAlg15), ("Receiver", receiver19c)] [
  .dotCall (resolve "Receiver") "Apply" (some [.num 9, resolve "Inc"])
]))

-- Test 19d: sequenceValue eager values stay whole when a sibling argument binds only
-- through AlgEnv. The occurrence count is the kept-item count: filter materializes an
-- exact list ([(1, 2)] here) and count opens exactly that one list boundary, so one
-- kept pair counts as 1.
def occurrenceCountAlg19d : Algorithm :=
  alg ["values", "predicate"] [] [] [
    .dotCall
      (.call (.resolve "filter") [.param "values", .param "predicate"])
      "count"
      none
  ]

def test19d : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("OccurrenceCount", occurrenceCountAlg19d)
  ] [
    .call (.resolve "OccurrenceCount") [
      sequenceItems [
        .capture [.num 1, .num 2],
        .capture [.num 1, .num 3]
      ],
      .algorithmExpr evenPredicateAlg19d
    ]
  ])) with
  | Except.ok [1] => true
  | _ => false

#guard test19d
#eval runFlat (.algorithmExpr (algPrivate [] [] [
  ("OccurrenceCount", occurrenceCountAlg19d)
] [
  .call (.resolve "OccurrenceCount") [
    sequenceItems [
      .capture [.num 1, .num 2],
      .capture [.num 1, .num 3]
    ],
    .algorithmExpr evenPredicateAlg19d
  ]
]))

-- Test 19e: inline predicate captures an outer value parameter rather than
-- re-declaring it as a local parameter.
--
-- The fixed collection argument is a grouped collection of explicit pair
-- items. One pair matches the target, so the
-- filter(...).count occurrence count is the kept-item count 1 (the kept pair
-- stays one exact list element; count opens only the list boundary).
def occurrenceCountAlg19e : Algorithm :=
  alg ["target"] [] [] [
    .dotCall
      (.call (.resolve "filter") [
        sequenceItems [
          .capture [.num 1, .num 10],
          .capture [.num 2, .num 20],
          .capture [.num 2, .num 30]
        ],
        .algorithmExpr (alg ["item"] [] [] [
          .binary .eq
            (.index (.param "item") (.num 1))
            (.index (.param "target") (.num 1))
        ])
      ])
      "count"
      none
  ]

def test19e : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("OccurrenceCount", occurrenceCountAlg19e)
  ] [
    .call (.resolve "OccurrenceCount") [
      .capture [.num 2, .num 20]
    ]
  ])) with
  | Except.ok [1] => true
  | _ => false

#guard test19e
#eval runFlat (.algorithmExpr (algPrivate [] [] [
  ("OccurrenceCount", occurrenceCountAlg19e)
] [
  .call (.resolve "OccurrenceCount") [
    .capture [.num 2, .num 20]
  ]
]))

-- if builtin tests
-- if(cond, whenTrue, whenFalse): the only supported form.
--------------------------------------------------------------------------------

-- Test 20: 3-arg if true → produce then-branch value
-- if(1, 5, 6) → [5]
def test20 : Bool :=
  match runFlat (.call (resolve "if") [.num 1, .num 5, .num 6]) with
  | Except.ok [5] => true
  | _ => false

#guard test20
#eval runFlat (.call (resolve "if") [.num 1, .num 5, .num 6])

-- Test 21: 3-arg if false → produce else-branch value
-- if(0, 5, 6) → [6]
def test21 : Bool :=
  match runFlat (.call (resolve "if") [.num 0, .num 5, .num 6]) with
  | Except.ok [6] => true
  | _ => false

#guard test21
#eval runFlat (.call (resolve "if") [.num 0, .num 5, .num 6])

end KatLangTests
