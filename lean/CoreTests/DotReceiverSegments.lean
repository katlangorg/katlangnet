import KatLang
import CoreTests.Common

namespace KatLangTests
open KatLang (alg algWithParameters algWithParameterPatterns algPrivate privateProp publicProp privateLocalProp publicLocalProp runFlat runResult Algorithm Error Result PropExposure)
open KatLang (resolve param num)
open KatLang (Pattern CondBranch)

--------------------------------------------------------------------------------
-- Dot-call receiver symmetry for user-defined leading flat variadic callees
--------------------------------------------------------------------------------
-- The general segment rule: the dot-call receiver is ONE leading argument
-- segment for arity checking and fixed prefix/suffix allocation, and a flat
-- top-level collecting parameter allocated the segment consumes the segment's
-- evaluated top-level supply. A STORED property receiver evaluates at its
-- value boundary, so its segment supply is one item (`Pair.NItems` collects
-- [Pair]) and the dot form coincides with the canonical `NItems(Pair)`; a
-- WRITTEN group receiver — `(10, 20)` or `(Pair*)` — emits its raw row
-- supply, which the allocated collector consumes. A FIXED parameter allocated
-- the receiver segment always binds the segment's one captured value; the
-- receiver is never pre-expanded to satisfy prefix/suffix arity.

def expectInnermostTypeMismatch (result : Except Error (List Int)) : Bool :=
  match result with
  | Except.error err => innermostIsAnyTypeMismatch err
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

-- Pair normalizes to the two-item sequence it contains; ordinary receiver and
-- canonical call agree on that ONE sequence-valued slot, which the collecting parameter
-- collects as a one-element list (count 1).
def sequenceValueReceiverLeadingVariadicIsOneSlot : Bool :=
  let callee := ("NItems", receiverSymmetryNItemsAlg)
  expectFlat (runReceiverSymmetryCase sequenceValuePairReceiverProp callee
    (.dotCall (resolve "Pair") "NItems" none)) [1] &&
  expectFlat (runReceiverSymmetryCase sequenceValuePairReceiverProp callee
    (.call (resolve "NItems") [resolve "Pair"])) [1]

#guard sequenceValueReceiverLeadingVariadicIsOneSlot

-- Pair* spreads two slots; single-collecting `NItems(*values)` collects those two
-- slots into one exact list of count 2.
def sequenceValueReceiverSpreadFeedsItemSupply : Bool :=
  let callee := ("NItems", receiverSymmetryNItemsAlg)
  expectFlat (runReceiverSymmetryCase sequenceValuePairReceiverProp callee
    (.dotCall (sequenceSpreadReceiver (resolve "Pair")) "NItems" none)) [2] &&
  expectFlat (runReceiverSymmetryCase sequenceValuePairReceiverProp callee
    (.call (resolve "NItems") [sequenceSpread (resolve "Pair")])) [2]

#guard sequenceValueReceiverSpreadFeedsItemSupply

-- BeforeLastCount(*values, last) binds the supplied item supply:
-- Pair.BeforeLastCount(99) and the canonical call pass ONE sequence-valued slot
-- plus the suffix (collected count 1). In the spread forms, the suffix takes
-- 99 and the collector receives Pair's two items — the dot form through the
-- grouped receiver segment's supply, the canonical form through ordinary
-- spread slots (collected count 2). Dot-call and canonical call agree within
-- each shape.
def sequenceValueReceiverWithSuffixMatchesCanonicalCalls : Bool :=
  let callee := ("BeforeLastCount", receiverSymmetryBeforeLastCountAlg)
  let suffixArgs : List KatLang.Expr := [.num 99]
  expectFlat (runReceiverSymmetryCase sequenceValuePairReceiverProp callee
    (.dotCall (resolve "Pair") "BeforeLastCount" (some suffixArgs))) [1] &&
  expectFlat (runReceiverSymmetryCase sequenceValuePairReceiverProp callee
    (.call (resolve "BeforeLastCount") [resolve "Pair", .num 99])) [1] &&
  expectFlat (runReceiverSymmetryCase sequenceValuePairReceiverProp callee
    (.dotCall (sequenceSpreadReceiver (resolve "Pair")) "BeforeLastCount" (some suffixArgs))) [2] &&
  expectFlat (runReceiverSymmetryCase sequenceValuePairReceiverProp callee
    (.call (resolve "BeforeLastCount") [sequenceSpread (resolve "Pair"), .num 99])) [2]

#guard sequenceValueReceiverWithSuffixMatchesCanonicalCalls

-- Values emits two top-level values. The ordinary forms pass ONE sequence-valued
-- slot (collected count 1); the explicit spread forms supply two slots (collected count
-- 2). Dot-call and canonical call agree within each shape.
def multiOutputReceiverCountsMatchCanonicalCalls : Bool :=
  let callee := ("NItems", receiverSymmetryNItemsAlg)
  expectFlat (runReceiverSymmetryCase multiOutputValuesReceiverProp callee
    (.dotCall (resolve "Values") "NItems" none)) [1] &&
  expectFlat (runReceiverSymmetryCase multiOutputValuesReceiverProp callee
    (.call (resolve "NItems") [resolve "Values"])) [1] &&
  expectFlat (runReceiverSymmetryCase multiOutputValuesReceiverProp callee
    (.dotCall (sequenceSpreadReceiver (resolve "Values")) "NItems" none)) [2] &&
  expectFlat (runReceiverSymmetryCase multiOutputValuesReceiverProp callee
    (.call (resolve "NItems") [sequenceSpread (resolve "Values")])) [2]

#guard multiOutputReceiverCountsMatchCanonicalCalls

-- BeforeLastCount(*values, last) binds the supplied item supply. The ordinary
-- and canonical forms pass ONE sequence-valued slot plus the suffix (collected
-- count 1); in the spread forms the suffix takes 99 and the collector receives
-- Values' two items — grouped receiver-segment supply on the dot side,
-- ordinary spread slots on the canonical side (collected count 2). Dot-call
-- and canonical call agree within each shape.
def multiOutputReceiverWithSuffixMatchesCanonicalCalls : Bool :=
  let callee := ("BeforeLastCount", receiverSymmetryBeforeLastCountAlg)
  let suffixArgs : List KatLang.Expr := [.num 99]
  expectFlat (runReceiverSymmetryCase multiOutputValuesReceiverProp callee
    (.dotCall (resolve "Values") "BeforeLastCount" (some suffixArgs))) [1] &&
  expectFlat (runReceiverSymmetryCase multiOutputValuesReceiverProp callee
    (.call (resolve "BeforeLastCount") [resolve "Values", .num 99])) [1] &&
  expectFlat (runReceiverSymmetryCase multiOutputValuesReceiverProp callee
    (.dotCall (sequenceSpreadReceiver (resolve "Values")) "BeforeLastCount" (some suffixArgs))) [2] &&
  expectFlat (runReceiverSymmetryCase multiOutputValuesReceiverProp callee
    (.call (resolve "BeforeLastCount") [sequenceSpread (resolve "Values"), .num 99])) [2]

#guard multiOutputReceiverWithSuffixMatchesCanonicalCalls

-- SumPlusLast(*values, last) with no extra argument receives exactly one
-- grouped sequence value, so `last` gets that value and the numeric body fails.
-- Explicit spread below is the successful path.
def ordinaryMultiOutputReceiverStaysOneSlotAtSuffixAllocation : Bool :=
  let callee := ("SumPlusLast", receiverSymmetrySumAlg)
  expectInnermostTypeMismatch (runReceiverSymmetryCase multiOutputValuesReceiverProp callee
    (.dotCall (resolve "Values") "SumPlusLast" none)) &&
  expectInnermostTypeMismatch (runReceiverSymmetryCase multiOutputValuesReceiverProp callee
    (.call (resolve "SumPlusLast") [resolve "Values"]))

#guard ordinaryMultiOutputReceiverStaysOneSlotAtSuffixAllocation

-- Allocation precedes supply consumption, and a receiver is never
-- pre-expanded: with no extra argument, `(Values*).SumPlusLast` is ONE
-- receiver segment, so the fixed suffix `last` binds the segment's captured
-- value (10, 20) whole and the numeric body fails. The canonical spread-slot
-- call `SumPlusLast(Values*)` supplies 10 and 20 as ordinary slots before
-- allocation, so `last` binds 20 and the collector captures [10] — the two
-- spellings are observably different at a fixed suffix.
def groupedSpreadReceiverStaysOneSegmentAtSuffixAllocation : Bool :=
  let callee := ("SumPlusLast", receiverSymmetrySumAlg)
  expectInnermostTypeMismatch (runReceiverSymmetryCase multiOutputValuesReceiverProp callee
    (.dotCall (sequenceSpreadReceiver (resolve "Values")) "SumPlusLast" none)) &&
  expectFlat (runReceiverSymmetryCase multiOutputValuesReceiverProp callee
    (.call (resolve "SumPlusLast") [sequenceSpread (resolve "Values")])) [30]

#guard groupedSpreadReceiverStaysOneSegmentAtSuffixAllocation

-- With an extra written argument the suffix takes it from the back and the
-- collector consumes the grouped receiver segment's supply, agreeing with the
-- canonical spread-slot call: values = [10, 20], last = 5, sum = 35.
def groupedSpreadReceiverWithSuffixArgConsumesSupply : Bool :=
  let callee := ("SumPlusLast", receiverSymmetrySumAlg)
  expectFlat (runReceiverSymmetryCase multiOutputValuesReceiverProp callee
    (.dotCall (sequenceSpreadReceiver (resolve "Values")) "SumPlusLast" (some [.num 5]))) [35] &&
  expectFlat (runReceiverSymmetryCase multiOutputValuesReceiverProp callee
    (.call (resolve "SumPlusLast") [sequenceSpread (resolve "Values"), .num 5])) [35]

#guard groupedSpreadReceiverWithSuffixArgConsumesSupply

-- A written inline group receiver emits its raw row supply as the receiver
-- segment's supply, so the allocated collector collects both rows (count 2).
-- The direct call `NItems((10, 20))` still collects one written grouped
-- argument — receiver segments and written argument slots are different
-- receivers.
def inlineGroupReceiverSuppliesRowItemsToLeadingVariadic : Bool :=
  expectFlat (runFlat (.algorithmExpr (algPrivate [] [] [
    ("NItems", receiverSymmetryNItemsAlg)
  ] [
    .dotCall (.capture [.num 10, .num 20]) "NItems" none
  ]))) [2] &&
  expectFlat (runFlat (.algorithmExpr (algPrivate [] [] [
    ("NItems", receiverSymmetryNItemsAlg)
  ] [
    .call (resolve "NItems") [.capture [.num 10, .num 20]]
  ]))) [1]

#guard inlineGroupReceiverSuppliesRowItemsToLeadingVariadic

--------------------------------------------------------------------------------
-- Dot-receiver segment rule: the required regression matrix
--------------------------------------------------------------------------------
-- Mean(*vector) = vector.sum / vector.count — the integer twin of the C#
-- headline example: the direct flat call and the written group receiver
-- produce the same mean (2 under integer division).
def dotReceiverSegmentMeanAlg : Algorithm :=
  algWithParameters [{ name := "vector", kind := .collecting }] [] [] [
    .binary .div
      (.dotCall (.param "vector") "sum" none)
      (.dotCall (.param "vector") "count" none)
  ]

def dotReceiverSegmentMeanIntegerTwin : Bool :=
  expectFlat (runFlat (.algorithmExpr (algPrivate [] [] [
    ("Mean", dotReceiverSegmentMeanAlg)
  ] [
    .call (resolve "Mean") [.num 1, .num 2, .num 3],
    .dotCall (.capture [.num 1, .num 2, .num 3]) "Mean" none
  ]))) [2, 2]

#guard dotReceiverSegmentMeanIntegerTwin

def dotReceiverSegmentCollectAlg : Algorithm :=
  algWithParameters [{ name := "items", kind := .collecting }] [] [] [
    .param "items"
  ]

def runDotReceiverCollect (receiver : KatLang.Expr) : Except Error Result :=
  runResult (.algorithmExpr (algPrivate [] [] [
    ("Collect", dotReceiverSegmentCollectAlg),
    ("Values", alg [] [] [] [.num 1, .num 2, .num 3])
  ] [
    .dotCall receiver "Collect" none
  ]))

def expectCollectResult (receiver : KatLang.Expr) (expected : Result) : Bool :=
  match runDotReceiverCollect receiver with
  | Except.ok value => reprStr value == reprStr expected
  | _ => false

-- Boundary and cardinality matrix for the collector-consumes-segment-supply
-- rule. A written group receiver supplies its raw rows; one extra written
-- boundary survives as one item; `()` supplies zero items; exact lists stay
-- opaque; nothing is recursively flattened.
def dotReceiverSegmentCollectBoundaryMatrix : Bool :=
  expectCollectResult (.capture [.num 1, .num 2])
    (.listValue [.atom 1, .atom 2]) &&
  expectCollectResult (.capture [.capture [.num 1, .num 2]])
    (.listValue [.sequenceValue [.atom 1, .atom 2]]) &&
  expectCollectResult (.emptySequence 1)
    (.listValue []) &&
  expectCollectResult (.listLiteral [.num 1, .num 2])
    (.listValue [.listValue [.atom 1, .atom 2]]) &&
  expectCollectResult (.capture [.num 1, .capture [.num 2, .num 3]])
    (.listValue [.atom 1, .sequenceValue [.atom 2, .atom 3]]) &&
  expectCollectResult (.capture [sequenceSpread (resolve "Values"), .num 7])
    (.listValue [.atom 1, .atom 2, .atom 3, .atom 7]) &&
  expectCollectResult (.capture [.capture [sequenceSpread (resolve "Values"), .num 7]])
    (.listValue [.sequenceValue [.atom 1, .atom 2, .atom 3, .atom 7]]) &&
  expectCollectResult (.algorithmExpr (alg [] [] [] [.num 1, .num 2, .num 3]))
    (.listValue [.atom 1, .atom 2, .atom 3]) &&
  expectCollectResult (resolve "Values")
    (.listValue [.sequenceValue [.atom 1, .atom 2, .atom 3]])

#guard dotReceiverSegmentCollectBoundaryMatrix

-- Allocation precedes supply consumption. F(first, *middle, last) with the
-- written pair receiver and one extra argument binds the whole receiver value
-- to the fixed prefix, collects nothing, and takes the suffix from the back.
def dotReceiverSegmentPrefixSuffixAlg : Algorithm :=
  algWithParameters [
    { name := "first", kind := .normal },
    { name := "middle", kind := .collecting },
    { name := "last", kind := .normal }
  ] [] [] [
    .param "first", .param "middle", .param "last"
  ]

def dotReceiverSegmentFixedPrefixBindsValue : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [
    ("F", dotReceiverSegmentPrefixSuffixAlg)
  ] [
    .dotCall (.capture [.num 1, .num 2]) "F" (some [.num 9])
  ])) with
  | Except.ok value =>
      reprStr value ==
        reprStr (Result.sequenceValue [.sequenceValue [.atom 1, .atom 2], .listValue [], .atom 9])
  | _ => false

#guard dotReceiverSegmentFixedPrefixBindsValue

-- The receiver segment's item count never satisfies arity: one segment
-- against two required fixed parameters is the ordinary minimum-arity error.
def dotReceiverSegmentCountNeverSatisfiesArity : Bool :=
  expectInnermostArityMismatch 2 1 (runFlat (.algorithmExpr (algPrivate [] [] [
    ("F", dotReceiverSegmentPrefixSuffixAlg)
  ] [
    .dotCall (.capture [.num 1, .num 2]) "F" none
  ])))

#guard dotReceiverSegmentCountNeverSatisfiesArity

-- F(*middle, last) with only the receiver segment: the fixed suffix binds the
-- receiver's one captured value and the collector collects the empty middle.
def dotReceiverSegmentSuffixAlg : Algorithm :=
  algWithParameters [
    { name := "middle", kind := .collecting },
    { name := "last", kind := .normal }
  ] [] [] [
    .param "middle", .param "last"
  ]

def dotReceiverSegmentSuffixTakesReceiverWhole : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [
    ("F", dotReceiverSegmentSuffixAlg)
  ] [
    .dotCall (.capture [.num 1, .num 2]) "F" none
  ])) with
  | Except.ok value =>
      reprStr value ==
        reprStr (Result.sequenceValue [.listValue [], .sequenceValue [.atom 1, .atom 2]])
  | _ => false

#guard dotReceiverSegmentSuffixTakesReceiverWhole

-- Scale(*values, factor) with an extra argument: the suffix takes the factor
-- and the collector consumes the written group receiver's supply.
def dotReceiverSegmentScaleConsumesSupplyAfterSuffix : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [
    ("Scale", dotReceiverSegmentSuffixAlg)
  ] [
    .dotCall (.capture [.num 1, .num 2, .num 3]) "Scale" (some [.num 10])
  ])) with
  | Except.ok value =>
      reprStr value ==
        reprStr (Result.sequenceValue [.listValue [.atom 1, .atom 2, .atom 3], .atom 10])
  | _ => false

#guard dotReceiverSegmentScaleConsumesSupplyAfterSuffix

-- Nested sequence-value parameter patterns keep one-boundary destructuring:
-- the receiver's written slots destructure through the pattern, and the
-- nested collecting binding is NOT fed the segment supply.
def dotReceiverSegmentNestedPatternAlg : Algorithm :=
  algWithParameterPatterns [
    .sequenceValue [
      .capture { name := "x", kind := .normal },
      .capture { name := "y", kind := .collecting },
      .capture { name := "z", kind := .normal }]
  ] [] [] [
    .param "x", .param "y", .param "z"
  ]

def dotReceiverSegmentNestedPatternKeepsOneBoundary : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [
    ("F", dotReceiverSegmentNestedPatternAlg)
  ] [
    .dotCall (.capture [.num 1, .num 2, .num 3, .num 4]) "F" none
  ])) with
  | Except.ok value =>
      reprStr value ==
        reprStr (Result.sequenceValue [.atom 1, .listValue [.atom 2, .atom 3], .atom 4])
  | _ => false

#guard dotReceiverSegmentNestedPatternKeepsOneBoundary

end KatLangTests
