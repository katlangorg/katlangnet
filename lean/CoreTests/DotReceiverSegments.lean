import KatLang
import CoreTests.Common

namespace KatLangTests
open KatLang (alg algWithParameters algWithParameterPatterns algPrivate privateProp publicProp privateLocalProp publicLocalProp runFlat runResult Algorithm Error Result PropExposure)
open KatLang (resolve param num)
open KatLang (Pattern CondBranch)

--------------------------------------------------------------------------------
-- Dot-call passes a value: the extension-call receiver is an ordinary argument
--------------------------------------------------------------------------------
-- For extension-call fallback, `receiver.F(args)` is exactly the written call
-- `F(receiver, args)` (`prepareLexicalDotCallArgs` + the ONE
-- `evalResolvedCallCounted` funnel): the receiver is ONE ordinary leading
-- argument whatever it is — a stored property, a written group `(10, 20)`, a
-- brace block, a list literal, a capture of a spread `(Pair*)`, `()` — so its
-- item count never satisfies arity, a FIXED parameter binds it whole, and a
-- collecting parameter collects it as ONE item. Only the spread marker opens a
-- receiver: `Pair*.F(args)` is the ordinary spread call `F(Pair*, args)`. The
-- guards below pin the dotted spelling against its written rewrite for every
-- callee shape (fixed, collecting, prefix/collector/suffix, patterned).

def expectInnermostTypeMismatch (result : Except Error (List Int)) : Bool :=
  match result with
  | Except.error err => innermostIsAnyTypeMismatch err
  | _ => false

-- A numeric aggregate over a collected non-numeric element (`[(10, 20)].sum`)
-- is the builtin's element-shape rejection (badArity under its context).
def expectNumericElementRejection (result : Except Error (List Int)) : Bool :=
  match result with
  | Except.error err => innermostIsBadArity err
  | _ => false

-- NItems(*values) = values.count
def receiverSymmetryNItemsAlg : Algorithm :=
  algWithParameters [{ name := "values", kind := .collecting }] [] []
    [.dotCall (.param "values") "count" none]

-- BeforeLastCount(*values, last) = values.count
def receiverSymmetryBeforeLastCountAlg : Algorithm :=
  algWithParameters [{ name := "values", kind := .collecting }, { name := "last" }] [] []
    [.dotCall (.param "values") "count" none]

-- SumPlusLast(*values, last) = values.sum + last
def receiverSymmetrySumAlg : Algorithm :=
  algWithParameters [{ name := "values", kind := .collecting }, { name := "last" }] [] []
    [.binary .add (.dotCall (.param "values") "sum" none) (.param "last")]

-- Pair = (10, 20): one sequence value.
def sequenceValuePairReceiverProp : Prod String Algorithm :=
  ("Pair", alg [] [] [] [.capture [.num 10, .num 20]])

-- Values = 10, 20: two emitted top-level values.
def multiOutputValuesReceiverProp : Prod String Algorithm :=
  ("Values", alg [] [] [] [.num 10, .num 20])

def runReceiverSymmetryCase (receiverProp calleeProp : Prod String Algorithm)
    (out : KatLang.Expr) : Except Error (List Int) :=
  runFlat (.algorithmExpr (algPrivate [] [] [receiverProp, calleeProp] [out]))

-- Pair normalizes to the two-item sequence it contains; the dotted receiver
-- and the written argument are the SAME one sequence-valued slot, which the
-- collecting parameter collects as a one-element list (count 1).
def sequenceValueReceiverLeadingVariadicIsOneSlot : Bool :=
  let callee := ("NItems", receiverSymmetryNItemsAlg)
  expectFlat (runReceiverSymmetryCase sequenceValuePairReceiverProp callee
    (.dotCall (resolve "Pair") "NItems" none)) [1] &&
  expectFlat (runReceiverSymmetryCase sequenceValuePairReceiverProp callee
    (.call (resolve "NItems") [resolve "Pair"])) [1]

#guard sequenceValueReceiverLeadingVariadicIsOneSlot

-- Only the spread marker opens a receiver. The spread receiver `Pair*.NItems`
-- is the written spread call `NItems(Pair*)`: two ordinary slots, collected as
-- one exact list of count 2. The CAPTURE of the spread `(Pair*)` is one value
-- again — `(Pair*).NItems` is `NItems((Pair*))`, count 1.
def sequenceValueReceiverSpreadFeedsItemSupply : Bool :=
  let callee := ("NItems", receiverSymmetryNItemsAlg)
  expectFlat (runReceiverSymmetryCase sequenceValuePairReceiverProp callee
    (.dotCall (sequenceSpread (resolve "Pair")) "NItems" none)) [2] &&
  expectFlat (runReceiverSymmetryCase sequenceValuePairReceiverProp callee
    (.call (resolve "NItems") [sequenceSpread (resolve "Pair")])) [2] &&
  expectFlat (runReceiverSymmetryCase sequenceValuePairReceiverProp callee
    (.dotCall (sequenceSpreadReceiver (resolve "Pair")) "NItems" none)) [1] &&
  expectFlat (runReceiverSymmetryCase sequenceValuePairReceiverProp callee
    (.call (resolve "NItems") [sequenceSpreadReceiver (resolve "Pair")])) [1]

#guard sequenceValueReceiverSpreadFeedsItemSupply

-- BeforeLastCount(*values, last): the dotted spelling assembles exactly the
-- written call's slots. `Pair.BeforeLastCount(99)` is
-- `BeforeLastCount(Pair, 99)` — one sequence-valued slot plus the suffix
-- (collected count 1); the spread receiver supplies Pair's two items before
-- the suffix (collected count 2); the captured spread is one slot again.
def sequenceValueReceiverWithSuffixMatchesCanonicalCalls : Bool :=
  let callee := ("BeforeLastCount", receiverSymmetryBeforeLastCountAlg)
  let suffixArgs : List KatLang.Expr := [.num 99]
  expectFlat (runReceiverSymmetryCase sequenceValuePairReceiverProp callee
    (.dotCall (resolve "Pair") "BeforeLastCount" (some suffixArgs))) [1] &&
  expectFlat (runReceiverSymmetryCase sequenceValuePairReceiverProp callee
    (.call (resolve "BeforeLastCount") [resolve "Pair", .num 99])) [1] &&
  expectFlat (runReceiverSymmetryCase sequenceValuePairReceiverProp callee
    (.dotCall (sequenceSpread (resolve "Pair")) "BeforeLastCount" (some suffixArgs))) [2] &&
  expectFlat (runReceiverSymmetryCase sequenceValuePairReceiverProp callee
    (.call (resolve "BeforeLastCount") [sequenceSpread (resolve "Pair"), .num 99])) [2] &&
  expectFlat (runReceiverSymmetryCase sequenceValuePairReceiverProp callee
    (.dotCall (sequenceSpreadReceiver (resolve "Pair")) "BeforeLastCount" (some suffixArgs))) [1] &&
  expectFlat (runReceiverSymmetryCase sequenceValuePairReceiverProp callee
    (.call (resolve "BeforeLastCount") [sequenceSpreadReceiver (resolve "Pair"), .num 99])) [1]

#guard sequenceValueReceiverWithSuffixMatchesCanonicalCalls

-- Values emits two top-level values. The ordinary forms pass ONE
-- sequence-valued slot (collected count 1); the spread forms supply two slots
-- (collected count 2); the captured spread is one slot. Dot-call and written
-- call agree within each shape.
def multiOutputReceiverCountsMatchCanonicalCalls : Bool :=
  let callee := ("NItems", receiverSymmetryNItemsAlg)
  expectFlat (runReceiverSymmetryCase multiOutputValuesReceiverProp callee
    (.dotCall (resolve "Values") "NItems" none)) [1] &&
  expectFlat (runReceiverSymmetryCase multiOutputValuesReceiverProp callee
    (.call (resolve "NItems") [resolve "Values"])) [1] &&
  expectFlat (runReceiverSymmetryCase multiOutputValuesReceiverProp callee
    (.dotCall (sequenceSpread (resolve "Values")) "NItems" none)) [2] &&
  expectFlat (runReceiverSymmetryCase multiOutputValuesReceiverProp callee
    (.call (resolve "NItems") [sequenceSpread (resolve "Values")])) [2] &&
  expectFlat (runReceiverSymmetryCase multiOutputValuesReceiverProp callee
    (.dotCall (sequenceSpreadReceiver (resolve "Values")) "NItems" none)) [1] &&
  expectFlat (runReceiverSymmetryCase multiOutputValuesReceiverProp callee
    (.call (resolve "NItems") [sequenceSpreadReceiver (resolve "Values")])) [1]

#guard multiOutputReceiverCountsMatchCanonicalCalls

-- BeforeLastCount(*values, last) over the multi-output property: the same
-- three shapes, each agreeing with its written rewrite.
def multiOutputReceiverWithSuffixMatchesCanonicalCalls : Bool :=
  let callee := ("BeforeLastCount", receiverSymmetryBeforeLastCountAlg)
  let suffixArgs : List KatLang.Expr := [.num 99]
  expectFlat (runReceiverSymmetryCase multiOutputValuesReceiverProp callee
    (.dotCall (resolve "Values") "BeforeLastCount" (some suffixArgs))) [1] &&
  expectFlat (runReceiverSymmetryCase multiOutputValuesReceiverProp callee
    (.call (resolve "BeforeLastCount") [resolve "Values", .num 99])) [1] &&
  expectFlat (runReceiverSymmetryCase multiOutputValuesReceiverProp callee
    (.dotCall (sequenceSpread (resolve "Values")) "BeforeLastCount" (some suffixArgs))) [2] &&
  expectFlat (runReceiverSymmetryCase multiOutputValuesReceiverProp callee
    (.call (resolve "BeforeLastCount") [sequenceSpread (resolve "Values"), .num 99])) [2] &&
  expectFlat (runReceiverSymmetryCase multiOutputValuesReceiverProp callee
    (.dotCall (sequenceSpreadReceiver (resolve "Values")) "BeforeLastCount" (some suffixArgs))) [1] &&
  expectFlat (runReceiverSymmetryCase multiOutputValuesReceiverProp callee
    (.call (resolve "BeforeLastCount") [sequenceSpreadReceiver (resolve "Values"), .num 99])) [1]

#guard multiOutputReceiverWithSuffixMatchesCanonicalCalls

-- SumPlusLast(*values, last) with no extra argument receives exactly one
-- sequence value, so `last` gets that value and the numeric body fails — in
-- the dotted spelling exactly as in the written one.
def ordinaryMultiOutputReceiverStaysOneSlotAtSuffixAllocation : Bool :=
  let callee := ("SumPlusLast", receiverSymmetrySumAlg)
  expectInnermostTypeMismatch (runReceiverSymmetryCase multiOutputValuesReceiverProp callee
    (.dotCall (resolve "Values") "SumPlusLast" none)) &&
  expectInnermostTypeMismatch (runReceiverSymmetryCase multiOutputValuesReceiverProp callee
    (.call (resolve "SumPlusLast") [resolve "Values"]))

#guard ordinaryMultiOutputReceiverStaysOneSlotAtSuffixAllocation

-- A capture of the spread is ONE value: `(Values*).SumPlusLast` is
-- `SumPlusLast((Values*))`, so the fixed suffix `last` binds the captured
-- sequence (10, 20) whole and the numeric body fails, while the spread
-- receiver `Values*.SumPlusLast` is `SumPlusLast(Values*)`: 10 and 20 are
-- ordinary slots, `last` binds 20, the collector collects [10], sum 30.
def capturedSpreadReceiverIsOneValueAtSuffixAllocation : Bool :=
  let callee := ("SumPlusLast", receiverSymmetrySumAlg)
  expectInnermostTypeMismatch (runReceiverSymmetryCase multiOutputValuesReceiverProp callee
    (.dotCall (sequenceSpreadReceiver (resolve "Values")) "SumPlusLast" none)) &&
  expectInnermostTypeMismatch (runReceiverSymmetryCase multiOutputValuesReceiverProp callee
    (.call (resolve "SumPlusLast") [sequenceSpreadReceiver (resolve "Values")])) &&
  expectFlat (runReceiverSymmetryCase multiOutputValuesReceiverProp callee
    (.dotCall (sequenceSpread (resolve "Values")) "SumPlusLast" none)) [30] &&
  expectFlat (runReceiverSymmetryCase multiOutputValuesReceiverProp callee
    (.call (resolve "SumPlusLast") [sequenceSpread (resolve "Values")])) [30]

#guard capturedSpreadReceiverIsOneValueAtSuffixAllocation

-- With an extra written argument the suffix takes it from the back and the
-- collector collects the receiver: the spread receiver supplies [10, 20]
-- (sum 35), the captured spread is one non-numeric collected item (the sum
-- fails), each agreeing with its written rewrite.
def spreadReceiverWithSuffixArgSuppliesSlots : Bool :=
  let callee := ("SumPlusLast", receiverSymmetrySumAlg)
  expectFlat (runReceiverSymmetryCase multiOutputValuesReceiverProp callee
    (.dotCall (sequenceSpread (resolve "Values")) "SumPlusLast" (some [.num 5]))) [35] &&
  expectFlat (runReceiverSymmetryCase multiOutputValuesReceiverProp callee
    (.call (resolve "SumPlusLast") [sequenceSpread (resolve "Values"), .num 5])) [35] &&
  expectNumericElementRejection (runReceiverSymmetryCase multiOutputValuesReceiverProp callee
    (.dotCall (sequenceSpreadReceiver (resolve "Values")) "SumPlusLast" (some [.num 5]))) &&
  expectNumericElementRejection (runReceiverSymmetryCase multiOutputValuesReceiverProp callee
    (.call (resolve "SumPlusLast") [sequenceSpreadReceiver (resolve "Values"), .num 5]))

#guard spreadReceiverWithSuffixArgSuppliesSlots

-- A written inline group receiver is ONE value: `(10, 20).NItems` is
-- `NItems((10, 20))` and collects one item, exactly like the written call.
-- The spread group `(10, 20)*.NItems` is `NItems(10, 20)`: two items.
def inlineGroupReceiverIsOneCollectedItem : Bool :=
  expectFlat (runFlat (.algorithmExpr (algPrivate [] [] [
    ("NItems", receiverSymmetryNItemsAlg)
  ] [
    .dotCall (.capture [.num 10, .num 20]) "NItems" none
  ]))) [1] &&
  expectFlat (runFlat (.algorithmExpr (algPrivate [] [] [
    ("NItems", receiverSymmetryNItemsAlg)
  ] [
    .call (resolve "NItems") [.capture [.num 10, .num 20]]
  ]))) [1] &&
  expectFlat (runFlat (.algorithmExpr (algPrivate [] [] [
    ("NItems", receiverSymmetryNItemsAlg)
  ] [
    .dotCall (sequenceSpread (.capture [.num 10, .num 20])) "NItems" none
  ]))) [2] &&
  expectFlat (runFlat (.algorithmExpr (algPrivate [] [] [
    ("NItems", receiverSymmetryNItemsAlg)
  ] [
    .call (resolve "NItems") [sequenceSpread (.capture [.num 10, .num 20])]
  ]))) [2]

#guard inlineGroupReceiverIsOneCollectedItem

--------------------------------------------------------------------------------
-- Dot-call passes a value: the required regression matrix
--------------------------------------------------------------------------------
-- Mean(*vector) = vector.sum / vector.count — the integer twin of the C#
-- headline example: the direct flat call and the SPREAD group receiver
-- produce the same mean (2 under integer division), while the unspread group
-- receiver is one non-numeric collected item and fails.
def dotReceiverMeanAlg : Algorithm :=
  algWithParameters [{ name := "vector", kind := .collecting }] [] [] [
    .binary .div
      (.dotCall (.param "vector") "sum" none)
      (.dotCall (.param "vector") "count" none)
  ]

def dotReceiverMeanIntegerTwin : Bool :=
  expectFlat (runFlat (.algorithmExpr (algPrivate [] [] [
    ("Mean", dotReceiverMeanAlg)
  ] [
    .call (resolve "Mean") [.num 1, .num 2, .num 3],
    .dotCall (sequenceSpread (.capture [.num 1, .num 2, .num 3])) "Mean" none
  ]))) [2, 2] &&
  expectNumericElementRejection (runFlat (.algorithmExpr (algPrivate [] [] [
    ("Mean", dotReceiverMeanAlg)
  ] [
    .dotCall (.capture [.num 1, .num 2, .num 3]) "Mean" none
  ])))

#guard dotReceiverMeanIntegerTwin

def dotReceiverCollectAlg : Algorithm :=
  algWithParameters [{ name := "items", kind := .collecting }] [] [] [
    .param "items"
  ]

def runDotReceiverCollect (receiver : KatLang.Expr) : Except Error Result :=
  runResult (.algorithmExpr (algPrivate [] [] [
    ("Collect", dotReceiverCollectAlg),
    ("Values", alg [] [] [] [.num 1, .num 2, .num 3]),
    ("E", alg [] [] [] [.emptySequence 1])
  ] [
    .dotCall receiver "Collect" none
  ]))

def runWrittenCollect (argument : KatLang.Expr) : Except Error Result :=
  runResult (.algorithmExpr (algPrivate [] [] [
    ("Collect", dotReceiverCollectAlg),
    ("Values", alg [] [] [] [.num 1, .num 2, .num 3]),
    ("E", alg [] [] [] [.emptySequence 1])
  ] [
    .call (resolve "Collect") [argument]
  ]))

-- The dotted receiver collects exactly what the written argument collects.
def expectCollectResult (receiver : KatLang.Expr) (expected : Result) : Bool :=
  (match runDotReceiverCollect receiver with
   | Except.ok value => reprStr value == reprStr expected
   | _ => false) &&
  (match runWrittenCollect receiver with
   | Except.ok value => reprStr value == reprStr expected
   | _ => false) &&
  -- Pin execution and emitted count, not only argument-helper equality.
  ([.dotCall receiver "Collect" none,
    .call (resolve "Collect") [receiver]] : List KatLang.Expr).all (fun out =>
      match runCountedProgram (.algorithmExpr (algPrivate [] [] [
        ("Collect", dotReceiverCollectAlg),
        ("Values", alg [] [] [] [.num 1, .num 2, .num 3]),
        ("E", alg [] [] [] [.emptySequence 1])
      ] [out])) with
      | Except.ok (value, count) => reprStr value == reprStr expected && count == 1
      | _ => false)

-- Boundary and cardinality matrix of the rule. Every unspread receiver is ONE
-- collected item — a written group, a nested group, `()` (a visible empty
-- value, never a missing argument), a list literal, a spread-join group, a
-- brace block, a stored property, a stored `()` property — and the spread
-- receiver supplies the value's items as ordinary slots; nothing is
-- recursively flattened.
def dotReceiverCollectBoundaryMatrix : Bool :=
  expectCollectResult (.capture [.num 1, .num 2])
    (.listValue [.sequenceValue [.atom 1, .atom 2]]) &&
  expectCollectResult (.capture [.capture [.num 1, .num 2]])
    (.listValue [.sequenceValue [.atom 1, .atom 2]]) &&
  expectCollectResult (.emptySequence 1)
    (.listValue [.sequenceValue []]) &&
  expectCollectResult (.listLiteral [])
    (.listValue [.listValue []]) &&
  expectCollectResult (.listLiteral [.num 1, .num 2])
    (.listValue [.listValue [.atom 1, .atom 2]]) &&
  expectCollectResult (.listLiteral [.listLiteral [.num 1, .num 2]])
    (.listValue [.listValue [.listValue [.atom 1, .atom 2]]]) &&
  expectCollectResult (.capture [.num 1, .capture [.num 2, .num 3]])
    (.listValue [.sequenceValue [.atom 1, .sequenceValue [.atom 2, .atom 3]]]) &&
  expectCollectResult (.capture [sequenceSpread (resolve "Values"), .num 7])
    (.listValue [.sequenceValue [.atom 1, .atom 2, .atom 3, .atom 7]]) &&
  expectCollectResult (.algorithmExpr (alg [] [] [] [.num 1, .num 2, .num 3]))
    (.listValue [.sequenceValue [.atom 1, .atom 2, .atom 3]]) &&
  expectCollectResult (resolve "Values")
    (.listValue [.sequenceValue [.atom 1, .atom 2, .atom 3]]) &&
  expectCollectResult (resolve "E")
    (.listValue [.sequenceValue []]) &&
  expectCollectResult (sequenceSpread (.capture [.num 1, .num 2]))
    (.listValue [.atom 1, .atom 2]) &&
  expectCollectResult (sequenceSpread (.listLiteral [.num 1, .num 2]))
    (.listValue [.atom 1, .atom 2]) &&
  expectCollectResult (sequenceSpread (.listLiteral []))
    (.listValue []) &&
  expectCollectResult (sequenceSpread (.listLiteral [.listLiteral [.num 1, .num 2]]))
    (.listValue [.listValue [.atom 1, .atom 2]]) &&
  expectCollectResult (sequenceSpread (.emptySequence 1))
    (.listValue []) &&
  expectCollectResult (sequenceSpread (resolve "E"))
    (.listValue []) &&
  expectCollectResult (sequenceSpread (.capture [.num 1, .capture [.num 2, .num 3]]))
    (.listValue [.atom 1, .sequenceValue [.atom 2, .atom 3]]) &&
  expectCollectResult (sequenceSpread (resolve "Values"))
    (.listValue [.atom 1, .atom 2, .atom 3])

#guard dotReceiverCollectBoundaryMatrix

-- F(first, *middle, last) with the written pair receiver and one extra
-- argument: the receiver is the first written slot, so the fixed prefix binds
-- the whole pair, the collector collects nothing, and the suffix takes 9.
def dotReceiverPrefixSuffixAlg : Algorithm :=
  algWithParameters [
    { name := "first", kind := .normal },
    { name := "middle", kind := .collecting },
    { name := "last", kind := .normal }
  ] [] [] [
    .param "first", .param "middle", .param "last"
  ]

def expectPrefixSuffixResult (out : KatLang.Expr) (expected : Result) : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [
    ("F", dotReceiverPrefixSuffixAlg)
  ] [out])) with
  | Except.ok value => reprStr value == reprStr expected
  | _ => false

def dotReceiverFixedPrefixBindsValue : Bool :=
  expectPrefixSuffixResult
    (.dotCall (.capture [.num 1, .num 2]) "F" (some [.num 9]))
    (Result.sequenceValue [.sequenceValue [.atom 1, .atom 2], .listValue [], .atom 9]) &&
  expectPrefixSuffixResult
    (.call (resolve "F") [.capture [.num 1, .num 2], .num 9])
    (Result.sequenceValue [.sequenceValue [.atom 1, .atom 2], .listValue [], .atom 9]) &&
  -- The spread receiver supplies 1 and 2 as slots: first = 1, middle = [], last = 2.
  expectPrefixSuffixResult
    (.dotCall (sequenceSpread (.capture [.num 1, .num 2])) "F" none)
    (Result.sequenceValue [.atom 1, .listValue [], .atom 2])

#guard dotReceiverFixedPrefixBindsValue

-- The receiver's item count never satisfies arity: one receiver against two
-- required fixed parameters is the ordinary minimum-arity error, in the
-- dotted spelling exactly as in the written one.
def dotReceiverCountNeverSatisfiesArity : Bool :=
  expectInnermostArityMismatch 2 1 (runFlat (.algorithmExpr (algPrivate [] [] [
    ("F", dotReceiverPrefixSuffixAlg)
  ] [
    .dotCall (.capture [.num 1, .num 2]) "F" none
  ]))) &&
  expectInnermostArityMismatch 2 1 (runFlat (.algorithmExpr (algPrivate [] [] [
    ("F", dotReceiverPrefixSuffixAlg)
  ] [
    .call (resolve "F") [.capture [.num 1, .num 2]]
  ])))

#guard dotReceiverCountNeverSatisfiesArity

-- F(*middle, last) with only the receiver: the fixed suffix binds the
-- receiver's one value and the collector collects the empty middle.
def dotReceiverSuffixAlg : Algorithm :=
  algWithParameters [
    { name := "middle", kind := .collecting },
    { name := "last", kind := .normal }
  ] [] [] [
    .param "middle", .param "last"
  ]

def expectSuffixResult (calleeName : String) (out : KatLang.Expr) (expected : Result) : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [
    (calleeName, dotReceiverSuffixAlg)
  ] [out])) with
  | Except.ok value => reprStr value == reprStr expected
  | _ => false

def dotReceiverSuffixTakesReceiverWhole : Bool :=
  expectSuffixResult "F"
    (.dotCall (.capture [.num 1, .num 2]) "F" none)
    (Result.sequenceValue [.listValue [], .sequenceValue [.atom 1, .atom 2]]) &&
  expectSuffixResult "F"
    (.call (resolve "F") [.capture [.num 1, .num 2]])
    (Result.sequenceValue [.listValue [], .sequenceValue [.atom 1, .atom 2]])

#guard dotReceiverSuffixTakesReceiverWhole

-- Scale(*values, factor) with an extra argument: the suffix takes the factor
-- and the collector collects the receiver as ONE item; the spread receiver
-- supplies the three items as slots instead.
def dotReceiverScaleCollectsReceiverAfterSuffix : Bool :=
  expectSuffixResult "Scale"
    (.dotCall (.capture [.num 1, .num 2, .num 3]) "Scale" (some [.num 10]))
    (Result.sequenceValue [.listValue [.sequenceValue [.atom 1, .atom 2, .atom 3]], .atom 10]) &&
  expectSuffixResult "Scale"
    (.call (resolve "Scale") [.capture [.num 1, .num 2, .num 3], .num 10])
    (Result.sequenceValue [.listValue [.sequenceValue [.atom 1, .atom 2, .atom 3]], .atom 10]) &&
  expectSuffixResult "Scale"
    (.dotCall (sequenceSpread (.capture [.num 1, .num 2, .num 3])) "Scale" (some [.num 10]))
    (Result.sequenceValue [.listValue [.atom 1, .atom 2, .atom 3], .atom 10]) &&
  expectSuffixResult "Scale"
    (.call (resolve "Scale") [sequenceSpread (.capture [.num 1, .num 2, .num 3]), .num 10])
    (Result.sequenceValue [.listValue [.atom 1, .atom 2, .atom 3], .atom 10])

#guard dotReceiverScaleCollectsReceiverAfterSuffix

-- Nested sequence-value parameter patterns keep one-boundary destructuring:
-- the receiver is one value that the pattern opens one level, exactly like
-- the written argument.
def dotReceiverNestedPatternAlg : Algorithm :=
  algWithParameterPatterns [
    .sequenceValue [
      .capture { name := "x", kind := .normal },
      .capture { name := "y", kind := .collecting },
      .capture { name := "z", kind := .normal }]
  ] [] [] [
    .param "x", .param "y", .param "z"
  ]

def expectNestedPatternResult (out : KatLang.Expr) : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [
    ("F", dotReceiverNestedPatternAlg)
  ] [out])) with
  | Except.ok value =>
      reprStr value ==
        reprStr (Result.sequenceValue [.atom 1, .listValue [.atom 2, .atom 3], .atom 4])
  | _ => false

def dotReceiverNestedPatternKeepsOneBoundary : Bool :=
  expectNestedPatternResult (.dotCall (.capture [.num 1, .num 2, .num 3, .num 4]) "F" none) &&
  expectNestedPatternResult (.call (resolve "F") [.capture [.num 1, .num 2, .num 3, .num 4]])

#guard dotReceiverNestedPatternKeepsOneBoundary

end KatLangTests
