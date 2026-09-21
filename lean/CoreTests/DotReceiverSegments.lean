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
-- item count never satisfies arity and a FIXED parameter binds it whole. What a
-- COLLECTING parameter then binds is decided by the collector supply-boundary
-- law (`collectorSupply`, September 2026) exactly as for the written call: the
-- segment allocated to the collector after the fixed prefix/suffix positions
-- is collected exactly, except that a segment that is ONE lone written
-- (non-spread) sequence value opens one level — so `Pair.NItems` is
-- `NItems(Pair)` is 2, `[1, 2].Collect` is `[[1, 2]]`, and `(1, 2).G` with
-- `G(*middle, last)` binds `last` to the whole pair. The spread marker is the
-- other way to open a receiver: `Pair*.F(args)` is the ordinary spread call
-- `F(Pair*, args)`, whose items are already final. The guards below pin the
-- dotted spelling against its written rewrite for every callee shape (fixed,
-- collecting, prefix/collector/suffix, patterned).

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

-- Pair normalizes to the two-item sequence it contains; the dotted receiver
-- and the written argument are the SAME one written sequence-valued slot. It
-- is the lone collector's whole segment, so the collector supply-boundary law
-- opens it one level: `values = [10, 20]`, count 2.
def sequenceValueReceiverLeadingVariadicOpensOneLevel : Bool :=
  let callee := ("NItems", receiverSymmetryNItemsAlg)
  expectFlat (runReceiverSymmetryCase sequenceValuePairReceiverProp callee
    (.dotCall (resolve "Pair") "NItems" none)) [2] &&
  expectFlat (runReceiverSymmetryCase sequenceValuePairReceiverProp callee
    (.call (resolve "NItems") [resolve "Pair"])) [2]

#guard sequenceValueReceiverLeadingVariadicOpensOneLevel

-- The spread receiver `Pair*.NItems` is the written spread call
-- `NItems(Pair*)`: two final slots, collected as one exact list of count 2.
-- The CAPTURE of the spread `(Pair*)` is one written sequence value again —
-- `(Pair*).NItems` is `NItems((Pair*))` — and, being the lone collector's
-- whole segment, it opens one level to the same count 2: for a SEQUENCE value
-- at a lone collector the grouped and the spread spellings coincide.
def sequenceValueReceiverSpreadFeedsItemSupply : Bool :=
  let callee := ("NItems", receiverSymmetryNItemsAlg)
  expectFlat (runReceiverSymmetryCase sequenceValuePairReceiverProp callee
    (.dotCall (sequenceSpread (resolve "Pair")) "NItems" none)) [2] &&
  expectFlat (runReceiverSymmetryCase sequenceValuePairReceiverProp callee
    (.call (resolve "NItems") [sequenceSpread (resolve "Pair")])) [2] &&
  expectFlat (runReceiverSymmetryCase sequenceValuePairReceiverProp callee
    (.dotCall (sequenceSpreadReceiver (resolve "Pair")) "NItems" none)) [2] &&
  expectFlat (runReceiverSymmetryCase sequenceValuePairReceiverProp callee
    (.call (resolve "NItems") [sequenceSpreadReceiver (resolve "Pair")])) [2]

#guard sequenceValueReceiverSpreadFeedsItemSupply

-- BeforeLastCount(*values, last): the dotted spelling assembles exactly the
-- written call's slots. `Pair.BeforeLastCount(99)` is
-- `BeforeLastCount(Pair, 99)` — the suffix takes 99 FIRST, and the segment
-- left to the collector is the lone written sequence slot, which opens one
-- level (collected count 2); the spread receiver supplies Pair's two final
-- items before the suffix (count 2); the captured spread is one written
-- sequence slot again (count 2).
def sequenceValueReceiverWithSuffixMatchesCanonicalCalls : Bool :=
  let callee := ("BeforeLastCount", receiverSymmetryBeforeLastCountAlg)
  let suffixArgs : List KatLang.Expr := [.num 99]
  expectFlat (runReceiverSymmetryCase sequenceValuePairReceiverProp callee
    (.dotCall (resolve "Pair") "BeforeLastCount" (some suffixArgs))) [2] &&
  expectFlat (runReceiverSymmetryCase sequenceValuePairReceiverProp callee
    (.call (resolve "BeforeLastCount") [resolve "Pair", .num 99])) [2] &&
  expectFlat (runReceiverSymmetryCase sequenceValuePairReceiverProp callee
    (.dotCall (sequenceSpread (resolve "Pair")) "BeforeLastCount" (some suffixArgs))) [2] &&
  expectFlat (runReceiverSymmetryCase sequenceValuePairReceiverProp callee
    (.call (resolve "BeforeLastCount") [sequenceSpread (resolve "Pair"), .num 99])) [2] &&
  expectFlat (runReceiverSymmetryCase sequenceValuePairReceiverProp callee
    (.dotCall (sequenceSpreadReceiver (resolve "Pair")) "BeforeLastCount" (some suffixArgs))) [2] &&
  expectFlat (runReceiverSymmetryCase sequenceValuePairReceiverProp callee
    (.call (resolve "BeforeLastCount") [sequenceSpreadReceiver (resolve "Pair"), .num 99])) [2]

#guard sequenceValueReceiverWithSuffixMatchesCanonicalCalls

-- Values emits two top-level values, which reach a caller as ONE sequence
-- value `(10, 20)`. The ordinary forms pass that one written sequence-valued
-- slot, which the lone collector opens one level (count 2); the spread forms
-- supply two final slots (count 2); the captured spread is one written
-- sequence slot (count 2). Dot-call and written call agree within each shape.
def multiOutputReceiverCountsMatchCanonicalCalls : Bool :=
  let callee := ("NItems", receiverSymmetryNItemsAlg)
  expectFlat (runReceiverSymmetryCase multiOutputValuesReceiverProp callee
    (.dotCall (resolve "Values") "NItems" none)) [2] &&
  expectFlat (runReceiverSymmetryCase multiOutputValuesReceiverProp callee
    (.call (resolve "NItems") [resolve "Values"])) [2] &&
  expectFlat (runReceiverSymmetryCase multiOutputValuesReceiverProp callee
    (.dotCall (sequenceSpread (resolve "Values")) "NItems" none)) [2] &&
  expectFlat (runReceiverSymmetryCase multiOutputValuesReceiverProp callee
    (.call (resolve "NItems") [sequenceSpread (resolve "Values")])) [2] &&
  expectFlat (runReceiverSymmetryCase multiOutputValuesReceiverProp callee
    (.dotCall (sequenceSpreadReceiver (resolve "Values")) "NItems" none)) [2] &&
  expectFlat (runReceiverSymmetryCase multiOutputValuesReceiverProp callee
    (.call (resolve "NItems") [sequenceSpreadReceiver (resolve "Values")])) [2]

#guard multiOutputReceiverCountsMatchCanonicalCalls

-- BeforeLastCount(*values, last) over the multi-output property: the same
-- three shapes, each agreeing with its written rewrite, and all count 2 —
-- the suffix takes 99 and the collector's segment is the lone written
-- sequence value (opened one level) or its two final items.
def multiOutputReceiverWithSuffixMatchesCanonicalCalls : Bool :=
  let callee := ("BeforeLastCount", receiverSymmetryBeforeLastCountAlg)
  let suffixArgs : List KatLang.Expr := [.num 99]
  expectFlat (runReceiverSymmetryCase multiOutputValuesReceiverProp callee
    (.dotCall (resolve "Values") "BeforeLastCount" (some suffixArgs))) [2] &&
  expectFlat (runReceiverSymmetryCase multiOutputValuesReceiverProp callee
    (.call (resolve "BeforeLastCount") [resolve "Values", .num 99])) [2] &&
  expectFlat (runReceiverSymmetryCase multiOutputValuesReceiverProp callee
    (.dotCall (sequenceSpread (resolve "Values")) "BeforeLastCount" (some suffixArgs))) [2] &&
  expectFlat (runReceiverSymmetryCase multiOutputValuesReceiverProp callee
    (.call (resolve "BeforeLastCount") [sequenceSpread (resolve "Values"), .num 99])) [2] &&
  expectFlat (runReceiverSymmetryCase multiOutputValuesReceiverProp callee
    (.dotCall (sequenceSpreadReceiver (resolve "Values")) "BeforeLastCount" (some suffixArgs))) [2] &&
  expectFlat (runReceiverSymmetryCase multiOutputValuesReceiverProp callee
    (.call (resolve "BeforeLastCount") [sequenceSpreadReceiver (resolve "Values"), .num 99])) [2]

#guard multiOutputReceiverWithSuffixMatchesCanonicalCalls

-- SumPlusLast(*values, last) with no extra argument receives exactly one
-- written sequence value. Fixed positions are allocated BEFORE the collector
-- law reads its segment: the suffix `last` takes that value whole, the
-- collector's segment is empty, and the numeric body fails — in the dotted
-- spelling exactly as in the written one. The lone-sequence opening never
-- reaches a fixed position.
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
-- collector's segment is the receiver: the spread receiver supplies the final
-- items [10, 20] (sum 35), and the captured spread is one written sequence
-- slot that is the collector's whole segment, so it opens one level to the
-- same [10, 20] (sum 35) — each agreeing with its written rewrite.
def spreadReceiverWithSuffixArgSuppliesSlots : Bool :=
  let callee := ("SumPlusLast", receiverSymmetrySumAlg)
  expectFlat (runReceiverSymmetryCase multiOutputValuesReceiverProp callee
    (.dotCall (sequenceSpread (resolve "Values")) "SumPlusLast" (some [.num 5]))) [35] &&
  expectFlat (runReceiverSymmetryCase multiOutputValuesReceiverProp callee
    (.call (resolve "SumPlusLast") [sequenceSpread (resolve "Values"), .num 5])) [35] &&
  expectFlat (runReceiverSymmetryCase multiOutputValuesReceiverProp callee
    (.dotCall (sequenceSpreadReceiver (resolve "Values")) "SumPlusLast" (some [.num 5]))) [35] &&
  expectFlat (runReceiverSymmetryCase multiOutputValuesReceiverProp callee
    (.call (resolve "SumPlusLast") [sequenceSpreadReceiver (resolve "Values"), .num 5])) [35]

#guard spreadReceiverWithSuffixArgSuppliesSlots

-- A written inline group receiver is ONE value: `(10, 20).NItems` is
-- `NItems((10, 20))`, exactly like the written call — one written sequence
-- slot, which the lone collector opens one level (count 2). The spread group
-- `(10, 20)*.NItems` is `NItems(10, 20)`: two final items, count 2.
def inlineGroupReceiverOpensOneLevelAtLoneCollector : Bool :=
  expectFlat (runFlat (.algorithmExpr (algPrivate [] [] [
    ("NItems", receiverSymmetryNItemsAlg)
  ] [
    .dotCall (.capture [.num 10, .num 20]) "NItems" none
  ]))) [2] &&
  expectFlat (runFlat (.algorithmExpr (algPrivate [] [] [
    ("NItems", receiverSymmetryNItemsAlg)
  ] [
    .call (resolve "NItems") [.capture [.num 10, .num 20]]
  ]))) [2] &&
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

#guard inlineGroupReceiverOpensOneLevelAtLoneCollector

--------------------------------------------------------------------------------
-- Dot-call passes a value: the required regression matrix
--------------------------------------------------------------------------------
-- Mean(*vector) = vector.sum / vector.count — the integer twin of the C#
-- headline example: the direct flat call, the SPREAD group receiver, and the
-- unspread group receiver all produce the same mean (2 under integer
-- division). The unspread group `(1, 2, 3).Mean` is `Mean((1, 2, 3))`: one
-- written sequence slot that is the lone collector's whole segment, opened
-- one level by the collector supply-boundary law.
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
    .dotCall (sequenceSpread (.capture [.num 1, .num 2, .num 3])) "Mean" none,
    .dotCall (.capture [.num 1, .num 2, .num 3]) "Mean" none
  ]))) [2, 2, 2]

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
-- written slot, and at the lone collector that slot is the whole segment, so
-- the collector supply-boundary law decides what is collected: a written
-- group, a nested group (normalized to the same sequence value), `()` (a
-- visible empty sequence value, whose opening supplies nothing), a spread-join
-- group, a brace block, a stored property, and a stored `()` property are
-- SEQUENCE values and open exactly one level — a nested sequence element stays
-- one collected item; a list literal of any depth is an exact value and never
-- opens. The spread receiver supplies the value's items as final slots, which
-- are collected exactly as supplied; nothing is recursively flattened.
def dotReceiverCollectBoundaryMatrix : Bool :=
  expectCollectResult (.capture [.num 1, .num 2])
    (.listValue [.atom 1, .atom 2]) &&
  expectCollectResult (.capture [.capture [.num 1, .num 2]])
    (.listValue [.atom 1, .atom 2]) &&
  expectCollectResult (.emptySequence 1)
    (.listValue []) &&
  expectCollectResult (.listLiteral [])
    (.listValue [.listValue []]) &&
  expectCollectResult (.listLiteral [.num 1, .num 2])
    (.listValue [.listValue [.atom 1, .atom 2]]) &&
  expectCollectResult (.listLiteral [.listLiteral [.num 1, .num 2]])
    (.listValue [.listValue [.listValue [.atom 1, .atom 2]]]) &&
  expectCollectResult (.capture [.num 1, .capture [.num 2, .num 3]])
    (.listValue [.atom 1, .sequenceValue [.atom 2, .atom 3]]) &&
  expectCollectResult (.capture [sequenceSpread (resolve "Values"), .num 7])
    (.listValue [.atom 1, .atom 2, .atom 3, .atom 7]) &&
  expectCollectResult (.algorithmExpr (alg [] [] [] [.num 1, .num 2, .num 3]))
    (.listValue [.atom 1, .atom 2, .atom 3]) &&
  expectCollectResult (resolve "Values")
    (.listValue [.atom 1, .atom 2, .atom 3]) &&
  expectCollectResult (resolve "E")
    (.listValue []) &&
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

-- The written spelling and the spread spelling of a lone SEQUENCE receiver
-- coincide at a lone collector, while a lone LIST receiver keeps the
-- grouped/spread distinction: lists are exact values and only the spread
-- marker opens them.
def dotReceiverSequenceCoincidesListDistinguishes : Bool :=
  (match runDotReceiverCollect (.capture [.num 1, .num 2]),
         runDotReceiverCollect (sequenceSpread (.capture [.num 1, .num 2])) with
   | Except.ok grouped, Except.ok spread => reprStr grouped == reprStr spread
   | _, _ => false) &&
  (match runDotReceiverCollect (.listLiteral [.num 1, .num 2]),
         runDotReceiverCollect (sequenceSpread (.listLiteral [.num 1, .num 2])) with
   | Except.ok grouped, Except.ok spread => reprStr grouped != reprStr spread
   | _, _ => false)

#guard dotReceiverSequenceCoincidesListDistinguishes

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
-- dotted spelling exactly as in the written one. The collector law never
-- runs before arity is satisfied.
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
-- FIRST, and the segment left to the collector is the receiver — one lone
-- written sequence slot, opened one level to `[1, 2, 3]`; the spread receiver
-- supplies the same three items as final slots. Written and spread receivers
-- coincide for a sequence value here.
def dotReceiverScaleOpensReceiverAfterSuffix : Bool :=
  expectSuffixResult "Scale"
    (.dotCall (.capture [.num 1, .num 2, .num 3]) "Scale" (some [.num 10]))
    (Result.sequenceValue [.listValue [.atom 1, .atom 2, .atom 3], .atom 10]) &&
  expectSuffixResult "Scale"
    (.call (resolve "Scale") [.capture [.num 1, .num 2, .num 3], .num 10])
    (Result.sequenceValue [.listValue [.atom 1, .atom 2, .atom 3], .atom 10]) &&
  expectSuffixResult "Scale"
    (.dotCall (sequenceSpread (.capture [.num 1, .num 2, .num 3])) "Scale" (some [.num 10]))
    (Result.sequenceValue [.listValue [.atom 1, .atom 2, .atom 3], .atom 10]) &&
  expectSuffixResult "Scale"
    (.call (resolve "Scale") [sequenceSpread (.capture [.num 1, .num 2, .num 3]), .num 10])
    (Result.sequenceValue [.listValue [.atom 1, .atom 2, .atom 3], .atom 10])

#guard dotReceiverScaleOpensReceiverAfterSuffix

-- Scale(*values, factor) with a LIST receiver and an extra argument: the
-- suffix takes the factor and the collector's lone written slot is a list,
-- which never opens — `[1, 2, 3].Scale(10)` collects `[[1, 2, 3]]`, while the
-- spread list receiver supplies three final items.
def dotReceiverScaleKeepsListReceiverExactAfterSuffix : Bool :=
  expectSuffixResult "Scale"
    (.dotCall (.listLiteral [.num 1, .num 2, .num 3]) "Scale" (some [.num 10]))
    (Result.sequenceValue [.listValue [.listValue [.atom 1, .atom 2, .atom 3]], .atom 10]) &&
  expectSuffixResult "Scale"
    (.call (resolve "Scale") [.listLiteral [.num 1, .num 2, .num 3], .num 10])
    (Result.sequenceValue [.listValue [.listValue [.atom 1, .atom 2, .atom 3]], .atom 10]) &&
  expectSuffixResult "Scale"
    (.dotCall (sequenceSpread (.listLiteral [.num 1, .num 2, .num 3])) "Scale" (some [.num 10]))
    (Result.sequenceValue [.listValue [.atom 1, .atom 2, .atom 3], .atom 10])

#guard dotReceiverScaleKeepsListReceiverExactAfterSuffix

-- Nested sequence-value parameter patterns keep one-boundary destructuring:
-- the receiver is one value that the pattern opens one level, exactly like
-- the written argument; the items a pattern opens are final, so the nested
-- collector collects them exactly.
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
