import KatLang
import CoreTests.Common

namespace KatLangTests
open KatLang (alg algWithParameters algWithParameterPatterns algPrivate privateProp publicProp privateLocalProp publicLocalProp runFlat runResult Algorithm Error Result PropExposure)

--------------------------------------------------------------------------------
-- Higher-order dot fallback: the ELABORATED lexical-fallback identity
-- After structural member lookup fails, `receiver.F(args...)` invokes the dot
-- edge's STORED fallback — `.param "F"` after front-end elaboration decides
-- the member is a parameter reference, `.resolve "F"` otherwise — through
-- canonical `resolveAlg`.
-- No runtime environment reconstructs the Param-vs-Resolve decision.
--------------------------------------------------------------------------------

-- `{a+1}`: the one-parameter increment algorithm passed as the `t` argument.
def higherOrderDotIncrement : Algorithm :=
  alg ["a"] [] [] [.binary .add (.param "a") (.num 1)]

-- K(a, t) = t(a) — plain-call control.
def higherOrderPlainCallK : Algorithm :=
  alg ["a", "t"] [] [] [.call (.param "t") [.param "a"]]

def higherOrderPlainCallControl : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("K", higherOrderPlainCallK)] [
    .call (.resolve "K") [.num 7, .algorithmExpr higherOrderDotIncrement]
  ])) with
  | Except.ok [8] => true
  | _ => false

#guard higherOrderPlainCallControl

-- K(a, t) = a.t — elaborated form: the member's fallback identity is
-- `.param "t"` (the front-end's decision), so the dot spelling agrees with
-- `t(a)` by consuming the same canonical parameter resolution.
def higherOrderDotParamK : Algorithm :=
  alg ["a", "t"] [] [] [.dotMember (.param "a") "t" (.param "t") none]

def higherOrderDotParamMemberResolvesStoredParamFallback : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("K", higherOrderDotParamK)] [
    .call (.resolve "K") [.num 7, .algorithmExpr higherOrderDotIncrement]
  ])) with
  | Except.ok [8] => true
  | _ => false

#guard higherOrderDotParamMemberResolvesStoredParamFallback

-- K(a, t) = {a.t} — nested scope: the front-end still elaborates the member's
-- fallback to `.param "t"` (captured ancestor parameter), and the stored
-- identity rides the node regardless of the runtime scope topology.
def higherOrderDotCapturedParamK : Algorithm :=
  alg ["a", "t"] [] [] [
    .algorithmExpr (alg [] [] [] [.dotMember (.param "a") "t" (.param "t") none])
  ]

def higherOrderDotParamMemberResolvesCapturedParameter : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("K", higherOrderDotCapturedParamK)] [
    .call (.resolve "K") [.num 7, .algorithmExpr higherOrderDotIncrement]
  ])) with
  | Except.ok [8] => true
  | _ => false

#guard higherOrderDotParamMemberResolvesCapturedParameter

-- Ordinary lexical fallback uses the same ownership-first lookup as a direct
-- callee name when the callable is owned by the dot-call algorithm's immediate
-- parent. Both output rows must therefore select the same `t` declaration.
def higherOrderImmediateParentT : Algorithm :=
  alg ["a"] [] [] [.binary .add (.param "a") (.num 2)]

def higherOrderImmediateParentK : Algorithm :=
  alg ["a"] [] [] [
    .dotCall (.param "a") "t" none,
    .call (.resolve "t") [.param "a"]
  ]

def higherOrderImmediateParentLexicalFallbackMatchesDirectCall : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("Outer", algPrivate [] [] [
      ("t", higherOrderImmediateParentT),
      ("K", higherOrderImmediateParentK)
    ] [.call (.resolve "K") [.num 7]])
  ] [.resolve "Outer"])) with
  | Except.ok [9, 9] => true
  | _ => false

#guard higherOrderImmediateParentLexicalFallbackMatchesDirectCall

-- The same law crosses more than one lexical parent and obeys nearest-owner
-- shadowing: K is owned by Inner, the nearer `t` is owned by Outer, and the
-- root's same-name property must not win for either spelling.
def higherOrderGrandparentRootT : Algorithm :=
  alg ["a"] [] [] [.binary .add (.param "a") (.num 100)]

def higherOrderGrandparentNearT : Algorithm :=
  alg ["a"] [] [] [.binary .add (.param "a") (.num 10)]

def higherOrderGrandparentLexicalFallbackMatchesDirectCall : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("t", higherOrderGrandparentRootT),
    ("Outer", algPrivate [] [] [
      ("t", higherOrderGrandparentNearT),
      ("Inner", algPrivate [] [] [
        ("K", higherOrderImmediateParentK)
      ] [.call (.resolve "K") [.num 7]])
    ] [.resolve "Inner"])
  ] [.resolve "Outer"])) with
  | Except.ok [17, 17] => true
  | _ => false

#guard higherOrderGrandparentLexicalFallbackMatchesDirectCall

-- Value-bound parameter parity: `K(7, 5)` fails with the SAME canonical
-- parameter-resolution error for `t(a)` and `a.t` — notAnAlgorithm "param(t)".
def higherOrderValueBoundPlainCallIsParamError : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("K", higherOrderPlainCallK)] [
    .call (.resolve "K") [.num 7, .num 5]
  ])) with
  | Except.error err => innermostIsNotAnAlgorithm "param(t)" err
  | Except.ok _ => false

#guard higherOrderValueBoundPlainCallIsParamError

def higherOrderValueBoundDotCallIsParamError : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("K", higherOrderDotParamK)] [
    .call (.resolve "K") [.num 7, .num 5]
  ])) with
  | Except.error err => innermostIsNotAnAlgorithm "param(t)" err
  | Except.ok _ => false

#guard higherOrderValueBoundDotCallIsParamError

-- Shadow rule (front-end elaborated): inside G(x) = x.t, `t` is NOT a
-- parameter of G and the visible property `t = 5` keeps the member's fallback
-- identity `.resolve "t"` (the `Expr.dotCall` sugar), so the fallback stays
-- LEXICAL: calling the zero-parameter property with the injected receiver is
-- arityMismatch 0 1 — exactly like the plain form `t(x)` written in G's body.
def higherOrderShadowG : Algorithm :=
  alg ["x"] [] [] [.dotCall (.param "x") "t" none]

def higherOrderShadowK : Algorithm :=
  alg ["a", "t"] [] [] [.call (.resolve "G") [.param "a"]]

def higherOrderShadowedDotMemberStaysLexical : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [
    ("t", alg [] [] [] [.num 5]),
    ("G", higherOrderShadowG),
    ("K", higherOrderShadowK)
  ] [
    .call (.resolve "K") [.num 7, .algorithmExpr higherOrderDotIncrement]
  ])) with
  | Except.error err => innermostIsArityMismatch 0 1 err
  | Except.ok _ => false

#guard higherOrderShadowedDotMemberStaysLexical

-- Local parameter precedence: the front-end stores `.param "t"` for a member
-- that is a parameter of the current algorithm even when a same-name property
-- is visible, so the parameter wins exactly as for a bare callee name.
def higherOrderLocalParamBeatsProperty : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("t", alg [] [] [] [.num 5]),
    ("K", higherOrderDotParamK)
  ] [
    .call (.resolve "K") [.num 7, .algorithmExpr higherOrderDotIncrement]
  ])) with
  | Except.ok [8] => true
  | _ => false

#guard higherOrderLocalParamBeatsProperty

-- A parameter bound to a BUILTIN algorithm takes the stored-Param channel too:
-- `K((1, 2, 3), count)` with `K(a, t) = a.t` calls builtin `count` with the
-- receiver as its one ordinary collection argument — the same boundary the
-- plain form `t(a)` uses (NOT the sequence-builtin dot-receiver view).
def higherOrderBuiltinBoundParamDotCall : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("K", higherOrderDotParamK)] [
    .call (.resolve "K") [.capture [.num 1, .num 2, .num 3], .resolve "count"]
  ])) with
  | Except.ok [3] => true
  | _ => false

#guard higherOrderBuiltinBoundParamDotCall

-- An UNELABORATED (hand-built) dot edge keeps plain lexical-fallback
-- semantics: the `Expr.dotCall` sugar stores `.resolve "t"`, so with no
-- lexical `t` in sight the member fails as unknownName even though a
-- dynamically visible `t` binding exists — the stored identity, not the
-- runtime environment, decides.
def higherOrderUnelaboratedDotKeepsLexicalFallback : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [
    ("K", alg ["a", "t"] [] [] [.dotCall (.param "a") "t" none])
  ] [
    .call (.resolve "K") [.num 7, .algorithmExpr higherOrderDotIncrement]
  ])) with
  | Except.error err => innermostIsUnknownName "t" err
  | Except.ok _ => false

#guard higherOrderUnelaboratedDotKeepsLexicalFallback

--------------------------------------------------------------------------------
-- Grace composed with DotCall (`a~.t` / `a.~t`)
-- The C# front end consumes ordinary postfix Grace on receiver `a` or ordinary
-- prefix Grace on fallback occurrence `t`. Base source order (a,t) becomes
-- (t,a) in either graced form through the one general Grace pass. All three
-- sources encode the SAME `dotMember` body here; Lean has no Grace construct
-- and no source-spelling-specific evaluation rule.
--------------------------------------------------------------------------------

-- `K = a.t`, `K = a~.t`, and `K = a.~t` share this ONE body.
def graceDotBody : KatLang.Expr :=
  .dotMember (.param "a") "t" (.param "t") none

def ordinaryDotEdgeK : Algorithm :=
  alg ["a", "t"] [] [] [graceDotBody]

def postfixGraceDotK : Algorithm :=
  alg ["t", "a"] [] [] [graceDotBody]

def prefixMemberGraceDotK : Algorithm :=
  alg ["t", "a"] [] [] [graceDotBody]

-- Direct source `K = t(a)` has its own occurrence order (t, a), even though
-- the dot fallback arm later invokes the same callable/receiver arrangement.
-- Invocation order does not determine the containing algorithm's parameters.
def sourceOrderedDirectCallK : Algorithm :=
  alg ["t", "a"] [] [] [.call (.param "t") [.param "a"]]

def sourceOrderedDirectCallInvokesBoundAlgorithm : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("K", sourceOrderedDirectCallK)] [
    .call (.resolve "K") [.algorithmExpr higherOrderDotIncrement, .num 7]
  ])) with
  | Except.ok [8] => true
  | _ => false

#guard sourceOrderedDirectCallInvokesBoundAlgorithm

def graceDotMemberInvokesBoundAlgorithm : Bool :=
  let ordinary :=
    match runFlat (.algorithmExpr (algPrivate [] [] [("K", ordinaryDotEdgeK)] [
      .call (.resolve "K") [.num 7, .algorithmExpr higherOrderDotIncrement]
    ])) with
    | Except.ok [8] => true
    | _ => false
  let postfixGraced :=
    match runFlat (.algorithmExpr (algPrivate [] [] [("K", postfixGraceDotK)] [
      .call (.resolve "K") [.algorithmExpr higherOrderDotIncrement, .num 7]
    ])) with
    | Except.ok [8] => true
    | _ => false
  let prefixGraced :=
    match runFlat (.algorithmExpr (algPrivate [] [] [("K", prefixMemberGraceDotK)] [
      .call (.resolve "K") [.algorithmExpr higherOrderDotIncrement, .num 7]
    ])) with
    | Except.ok [8] => true
    | _ => false
  ordinary && postfixGraced && prefixGraced

#guard graceDotMemberInvokesBoundAlgorithm

-- Structural precedence is SHARED: `Obj.V` and `Obj~.V` are the same edge, so
-- both read Obj's structural property (42) even though a lexical `V` exists.
-- Only the written CALL `V(Obj)` reaches the lexical declaration (99).
-- Obj also defines output so the call form binds Obj's value.
def graceDotSplitObj : Algorithm :=
  algPrivate [] [] [("V", alg [] [] [] [.num 42])] [.num 0]

def graceDotSplitLexicalV : Algorithm :=
  alg ["x"] [] [] [.num 99]

def graceDotSplitRoot (edge : KatLang.Expr) : KatLang.Expr :=
  .algorithmExpr (algPrivate [] [] [
    ("V", graceDotSplitLexicalV),
    ("Obj", graceDotSplitObj)
  ] [edge])

def ordinaryDotKeepsStructuralPrecedence : Bool :=
  match runFlat (graceDotSplitRoot (.dotCall (.resolve "Obj") "V" none)) with
  | Except.ok [42] => true
  | _ => false

#guard ordinaryDotKeepsStructuralPrecedence

def writtenCallReachesLexicalDeclaration : Bool :=
  match runFlat (graceDotSplitRoot
    (.call (.resolve "V") [.resolve "Obj"])) with
  | Except.ok [99] => true
  | _ => false

#guard writtenCallReachesLexicalDeclaration

-- Extra explicit arguments follow the receiver: `v~.F(1, 2)` is the ordinary
-- dot edge `v.F(1, 2)`, whose fallback arm calls `F(v, 1, 2)` (encoded here
-- with the receiver value inline).
def graceDotExtraArgs : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("F", alg ["x", "y", "z"] [] [] [
      .binary .add
        (.binary .add
          (.binary .mul (.param "x") (.num 100))
          (.binary .mul (.param "y") (.num 10)))
        (.param "z")])
  ] [
    .dotMember (.num 3) "F" (.resolve "F") (some [.num 1, .num 2])
  ])) with
  | Except.ok [312] => true
  | _ => false

#guard graceDotExtraArgs

-- Receiver-segment supply is ordinary dot semantics, so Grace inherits
-- it unchanged: a WRITTEN GROUP receiver supplies its rows to the flat
-- collecting parameter (count 2), while a NAMED receiver supplies one item
-- (count 1). A written group is not eligible for postfix Grace; the executable
-- named edge remains the same ordinary dot.
def graceDotCountItemsAlg : Algorithm :=
  algWithParameters [{ name := "items", kind := .collecting }] [] [] [
    .dotCall (.param "items") "count" none
  ]

def graceDotCountItemsRoot (edge : KatLang.Expr) : KatLang.Expr :=
  .algorithmExpr (algPrivate [] [] [
    ("S", alg [] [] [] [.num 1, .num 2]),
    ("CountItems", graceDotCountItemsAlg)
  ] [edge])

def namedReceiverSuppliesOneItem : Bool :=
  match runFlat (graceDotCountItemsRoot
    (.dotCall (.resolve "S") "CountItems" none)) with
  | Except.ok [1] => true
  | _ => false

#guard namedReceiverSuppliesOneItem

def writtenGroupReceiverSegmentSupplyContrast : Bool :=
  match runFlat (graceDotCountItemsRoot
    (.dotCall (.capture [.num 1, .num 2]) "CountItems" none)) with
  | Except.ok [2] => true
  | _ => false

#guard writtenGroupReceiverSegmentSupplyContrast

-- Chaining composes by ordinary rules: `a~.t.string` is the ordinary chain
-- `a.t.string` — an ordinary `.string` dot on the first edge's result.
def graceDotChainOrdinaryString : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("K",
    alg ["t", "a"] [] [] [
      .dotCall (.dotMember (.param "a") "t" (.param "t") none) "string" none
    ])
  ] [
    .call (.resolve "K") [.algorithmExpr higherOrderDotIncrement, .num 7]
  ])) with
  | Except.ok (KatLang.Result.str "8") => true
  | _ => false

#guard graceDotChainOrdinaryString

-- The `.string` value intrinsic is dot-only. Grace does NOT switch
-- channels: `v~.string` is the ordinary dot edge, so
-- it keeps the intrinsic ("5") even when a lexical `string` callable is
-- visible — only the written CALL reaches that declaration (105).
def dotStringIntrinsicIsSharedByBothSpellings : Bool :=
  let stringFn : Algorithm := alg ["x"] [] [] [.binary .add (.param "x") (.num 100)]
  let root (edge : KatLang.Expr) : KatLang.Expr :=
    .algorithmExpr (algPrivate [] [] [("string", stringFn)] [edge])
  let dotEdgeIntrinsic :=
    match runResult (root (.dotCall (.num 5) "string" none)) with
    | Except.ok (KatLang.Result.str "5") => true
    | _ => false
  let writtenCallReachesDeclaration :=
    match runResult (root (.call (.resolve "string") [.num 5])) with
    | Except.ok (KatLang.Result.atom 105) => true
    | _ => false
  let callWithoutDeclaration :=
    match runResult (.algorithmExpr (algPrivate [] [] [] [
      .call (.resolve "string") [.num 5]
    ])) with
    | Except.error err => innermostIsUnknownName "string" err
    | Except.ok _ => false
  dotEdgeIntrinsic && writtenCallReachesDeclaration && callWithoutDeclaration

#guard dotStringIntrinsicIsSharedByBothSpellings

-- A grace-marked open target (`open M~.C`) is a C# parse error — `open`
-- consumes structural algorithm identity and has no parameter inference to
-- reorder — so it never reaches Lean. The ORDINARY dotted open target is the
-- valid form and resolves through the argumentless dot path. The body must
-- reference an opened name so the (lazy) open resolution runs.
def ordinaryDottedOpenTargetResolves : Bool :=
  let inner : Algorithm :=
    Algorithm.mk none [] [] [publicProp "V" (alg [] [] [] [.num 5])] []
  let outer : Algorithm :=
    Algorithm.mk none [] [] [publicProp "C" inner] []
  match runFlat (.algorithmExpr (Algorithm.mk none []
    [.dotCall (.resolve "M") "C" none]
    [privateProp "M" outer]
    [.resolve "V"])) with
  | Except.ok [5] => true
  | _ => false

#guard ordinaryDottedOpenTargetResolves

def userCollectingDotCallCountItemsAlg : Algorithm :=
  algWithParameters [{ name := "items", kind := .collecting }] [] [] [
    .dotCall (.param "items") "count" none
  ]

def userCollectingDotCallCountItemsRoot : Algorithm :=
  algPrivate [] [] [("CountItems", userCollectingDotCallCountItemsAlg)] [
    .dotCall (.capture [.num 1, .num 2]) "CountItems" none
  ]

-- Ordinary dot-call receiver injection under the general segment rule:
-- `(1, 2).CountItems` injects the written group as ONE leading segment, and
-- the collecting parameter allocated that segment consumes the segment's raw
-- row supply, so `items = [1, 2]` and `items.count` is 2. (A direct call
-- `CountItems((1, 2))` still collects the one written grouped argument.)
def userCollectingDotCallReceiverSuppliesRowItems : Bool :=
  match runFlat (.algorithmExpr userCollectingDotCallCountItemsRoot) with
  | Except.ok [2] => true
  | _ => false

#guard userCollectingDotCallReceiverSuppliesRowItems

def userCollectingDotCallMeanAlg : Algorithm :=
  algWithParameters [{ name := "vector", kind := .collecting }] [] [] [
    .dotCall (.param "vector") "sum" none
  ]

def userCollectingDotCallMeanRoot : Algorithm :=
  algPrivate [] [] [("Mean", userCollectingDotCallMeanAlg)] [
    .dotCall (.capture [.num 1, .num 2]) "Mean" none
  ]

-- `(1, 2).Mean` binds `vector = [1, 2]` — the collector consumes the written
-- group receiver's row supply — so `vector.sum` is 3. This is the headline
-- correction of the general segment rule (formerly the receiver was one
-- captured sequence element and the sum hit the numeric constraint).
def userCollectingDotCallReceiverSumsSuppliedItems : Bool :=
  match runFlat (.algorithmExpr userCollectingDotCallMeanRoot) with
  | Except.ok [3] => true
  | _ => false

#guard userCollectingDotCallReceiverSumsSuppliedItems

def userNonCollectingDotCallCountOneAlg : Algorithm :=
  alg ["value"] [] [] [
    .dotCall (.param "value") "count" none
  ]

def userNonCollectingDotCallCountOneRoot : Algorithm :=
  algPrivate [] [] [("CountOne", userNonCollectingDotCallCountOneAlg)] [
    .dotCall (.capture [.num 1, .num 2]) "CountOne" none
  ]

def userNonCollectingDotCallReceiverIsOneSequenceArgument : Bool :=
  match runFlat (.algorithmExpr userNonCollectingDotCallCountOneRoot) with
  | Except.ok [2] => true
  | _ => false

#guard userNonCollectingDotCallReceiverIsOneSequenceArgument

def flatCollectingSlotQmeanAlg : Algorithm :=
  algWithParameters [{ name := "args", kind := .collecting }] [] [] [
    .binary .div
      (.dotCall (.param "args") "sum" none)
      (.dotCall (.param "args") "count" none)
  ]

def flatCollectingSlotVectorAlg : Algorithm :=
  alg [] [] [] [.call (.resolve "range") [.num 1, .num 3]]

def flatCollectingSlotQmeanNormalRoot : Algorithm :=
  algPrivate [] [] [("Vector", flatCollectingSlotVectorAlg), ("Qmean", flatCollectingSlotQmeanAlg)] [
    .call (.resolve "Qmean") [.resolve "Vector"]
  ]

-- `Qmean(Vector)` supplies ONE grouped argument, so the collecting parameter collects
-- `args = [Vector]` and `args.sum` hits the numeric element constraint.
-- Supplying the items is the explicit-spread call `Qmean(Vector*)` below.
def flatCollectingSlotQmeanSingleGroupedArgumentIsNumericConstraintError : Bool :=
  match runResult (.algorithmExpr flatCollectingSlotQmeanNormalRoot) with
  | Except.error err => innermostIsBadArity err
  | _ => false

#guard flatCollectingSlotQmeanSingleGroupedArgumentIsNumericConstraintError

def flatCollectingSlotQmeanExplicitRoot : Algorithm :=
  algPrivate [] [] [("Vector", flatCollectingSlotVectorAlg), ("Qmean", flatCollectingSlotQmeanAlg)] [
    .call (.resolve "Qmean") [sequenceSpread (.resolve "Vector")]
  ]

-- The explicit-spread call `Qmean(Vector*)` supplies Vector's items as
-- separate argument slots, so `args = [1, 2, 3]` and the mean is 2.
def flatCollectingSlotQmeanExplicitSpreadSuppliesItems : Bool :=
  match runFlat (.algorithmExpr flatCollectingSlotQmeanExplicitRoot) with
  | Except.ok [2] => true
  | _ => false

#guard flatCollectingSlotQmeanExplicitSpreadSuppliesItems

def flatCollectingSlotQmeanDotRoot : Algorithm :=
  algPrivate [] [] [("Vector", flatCollectingSlotVectorAlg), ("Qmean", flatCollectingSlotQmeanAlg)] [
    .dotCall (.resolve "Vector") "Qmean" none
  ]

-- `Vector.Qmean` is `Qmean(Vector)`: the receiver is one leading argument
-- slot, so the grouped-argument numeric-constraint error matches the plain
-- call above.
def flatCollectingSlotQmeanDotCallMatchesGroupedCall : Bool :=
  match runResult (.algorithmExpr flatCollectingSlotQmeanDotRoot) with
  | Except.error err => innermostIsBadArity err
  | _ => false

#guard flatCollectingSlotQmeanDotCallMatchesGroupedCall

def flatCollectingSlotCountAlg : Algorithm :=
  algWithParameters [{ name := "args", kind := .collecting }] [] [] [
    .dotCall (.param "args") "count" none
  ]

def flatCollectingSlotValuesAlg : Algorithm :=
  alg [] [] [] [.num 10, .num 20]

def flatCollectingSlotCountValuesRoot : Algorithm :=
  algPrivate [] [] [("Values", flatCollectingSlotValuesAlg), ("Count", flatCollectingSlotCountAlg)] [
    .call (.resolve "Count") [.resolve "Values"]
  ]

-- `Count(Values)` with a multi-output property supplies ONE argument boundary
-- (a property reference is a value boundary), so the collecting parameter collects
-- `args = [(10, 20)]` and the count is 1; `Count(Values*)` supplies 2 items.
def flatCollectingSlotMultiOutputPropertyIsOneCapturedSlot : Bool :=
  match runFlat (.algorithmExpr flatCollectingSlotCountValuesRoot) with
  | Except.ok [1] => true
  | _ => false

#guard flatCollectingSlotMultiOutputPropertyIsOneCapturedSlot

def flatCollectingSlotSequenceValuePairAlg : Algorithm :=
  alg [] [] [] [.capture [.num 10, .num 20]]

def flatCollectingSlotCountSequenceValuePairRoot : Algorithm :=
  algPrivate [] [] [("Pair", flatCollectingSlotSequenceValuePairAlg), ("Count", flatCollectingSlotCountAlg)] [
    .call (.resolve "Count") [.resolve "Pair"]
  ]

-- A visible sequence-value property is likewise ONE captured argument slot:
-- `Count(Pair)` collects `args = [(10, 20)]`, so the count is 1.
def flatCollectingSlotVisibleSequenceValueIsOneCapturedSlot : Bool :=
  match runFlat (.algorithmExpr flatCollectingSlotCountSequenceValuePairRoot) with
  | Except.ok [1] => true
  | _ => false

#guard flatCollectingSlotVisibleSequenceValueIsOneCapturedSlot

def flatCollectingSlotSumAlg : Algorithm :=
  algWithParameters [
    { name := "values", kind := .collecting },
    { name := "last", kind := .normal }
  ] [] [] [
    .binary .add (.dotCall (.param "values") "sum" none) (.param "last")
  ]

def flatCollectingSlotSumNormalRoot : Algorithm :=
  algPrivate [] [] [("Values", flatCollectingSlotValuesAlg), ("Sum", flatCollectingSlotSumAlg)] [
    .call (.resolve "Sum") [.resolve "Values", .num 7]
  ]

-- `Sum(Values, 7)`: the suffix takes `last = 7` and the collecting parameter collects the one
-- grouped argument (`values = [(10, 20)]`), so `values.sum` hits the numeric
-- element constraint. `Sum(Values*, 7)` below is the item-supplying form.
def flatCollectingSlotGroupedMiddleArgumentIsNumericConstraintError : Bool :=
  match runResult (.algorithmExpr flatCollectingSlotSumNormalRoot) with
  | Except.error err => innermostIsBadArity err
  | _ => false

#guard flatCollectingSlotGroupedMiddleArgumentIsNumericConstraintError

def flatCollectingSlotSumExplicitRoot : Algorithm :=
  algPrivate [] [] [("Values", flatCollectingSlotValuesAlg), ("Sum", flatCollectingSlotSumAlg)] [
    .call (.resolve "Sum") [sequenceSpread (.resolve "Values")]
  ]

def flatCollectingSlotExplicitSpreadCanSatisfySuffix : Bool :=
  match runFlat (.algorithmExpr flatCollectingSlotSumExplicitRoot) with
  | Except.ok [30] => true
  | _ => false

#guard flatCollectingSlotExplicitSpreadCanSatisfySuffix

def flatCollectingSlotSumSingleNormalRoot : Algorithm :=
  algPrivate [] [] [("Values", flatCollectingSlotValuesAlg), ("Sum", flatCollectingSlotSumAlg)] [
    .call (.resolve "Sum") [.resolve "Values"]
  ]

-- Sum(*values, last) receives one sequence-valued argument. Function-call
-- binding does not implicitly open it, so `last` receives the sequence value and
-- the old numeric body no longer succeeds.
def flatCollectingSlotNormalSegmentDoesNotSatisfySuffixBySpreading : Bool :=
  match runResult (.algorithmExpr flatCollectingSlotSumSingleNormalRoot) with
  | Except.error err => innermostIsAnyTypeMismatch err
  | _ => false

#guard flatCollectingSlotNormalSegmentDoesNotSatisfySuffixBySpreading

def flatCollectingSlotSumDotMissingSuffixRoot : Algorithm :=
  algPrivate [] [] [("Values", flatCollectingSlotValuesAlg), ("Sum", flatCollectingSlotSumAlg)] [
    .dotCall (.resolve "Values") "Sum" none
  ]

-- Same boundary through a dot-call receiver: Values.Sum passes the receiver as
-- one leading argument unless explicit spread is used.
def flatCollectingSlotDotReceiverDoesNotSatisfySuffixBySpreading : Bool :=
  match runResult (.algorithmExpr flatCollectingSlotSumDotMissingSuffixRoot) with
  | Except.error err => innermostIsAnyTypeMismatch err
  | _ => false

#guard flatCollectingSlotDotReceiverDoesNotSatisfySuffixBySpreading

def flatCollectingSlotSumDotSuffixRoot : Algorithm :=
  algPrivate [] [] [("Values", flatCollectingSlotValuesAlg), ("Sum", flatCollectingSlotSumAlg)] [
    .dotCall (.resolve "Values") "Sum" (some [.num 7])
  ]

-- `Values.Sum(7)` is `Sum(Values, 7)`: the receiver is one leading argument
-- slot, so the grouped-middle numeric-constraint error matches the plain call.
def flatCollectingSlotDotReceiverWithSuffixMatchesGroupedCall : Bool :=
  match runResult (.algorithmExpr flatCollectingSlotSumDotSuffixRoot) with
  | Except.error err => innermostIsBadArity err
  | _ => false

#guard flatCollectingSlotDotReceiverWithSuffixMatchesGroupedCall

def flatFixedSlotAddAlg : Algorithm :=
  alg ["x", "y"] [] [] [.binary .add (.param "x") (.param "y")]

def flatFixedSlotAddPairRoot : Algorithm :=
  algPrivate [] [] [("Pair", flatCollectingSlotValuesAlg), ("Add", flatFixedSlotAddAlg)] [
    .call (.resolve "Add") [.resolve "Pair"]
  ]

def flatFixedCallStillDoesNotAutoSpread : Bool :=
  match runResult (.algorithmExpr flatFixedSlotAddPairRoot) with
  | Except.error _ => true
  | Except.ok _ => false

#guard flatFixedCallStillDoesNotAutoSpread

def flatFixedSlotAddPairExplicitRoot : Algorithm :=
  algPrivate [] [] [("Pair", flatCollectingSlotValuesAlg), ("Add", flatFixedSlotAddAlg)] [
    .call (.resolve "Add") [sequenceSpread (.resolve "Pair")]
  ]

def flatFixedCallExplicitSpreadStillWorks : Bool :=
  match runFlat (.algorithmExpr flatFixedSlotAddPairExplicitRoot) with
  | Except.ok [30] => true
  | _ => false

#guard flatFixedCallExplicitSpreadStillWorks

def collectingForwardingCountItemsAlg : Algorithm :=
  algWithParameters [{ name := "items", kind := .collecting }] [] [] [
    .dotCall (.param "items") "count" none
  ]

-- Collecting-parameter forwarding is ordinary list spread: `Use(*values) =
-- CountItems(values*)` re-supplies exactly the collected items
-- (spread(collect(xs)) = xs). The root call spreads its grouped sequence so the
-- collecting parameter collects the three items.
def collectingForwardingUseValuesAlg : Algorithm :=
  algWithParameters [{ name := "values", kind := .collecting }] [] [] [
    .call (.resolve "CountItems") [sequenceSpread (.param "values")]
  ]

def collectingForwardingTopLevelRoot : Algorithm :=
  algPrivate [] [] [("CountItems", collectingForwardingCountItemsAlg), ("Use", collectingForwardingUseValuesAlg)] [
    .call (.resolve "Use") [sequenceSpread (sequenceItems [.num 1, .num 2, .num 3])]
  ]

def collectingForwardingTopLevelCaptureStillWorks : Bool :=
  match runFlat (.algorithmExpr collectingForwardingTopLevelRoot) with
  | Except.ok [3] => true
  | _ => false

#guard collectingForwardingTopLevelCaptureStillWorks

-- The bare-name forward `CountItems(values)` passes the collected list as ONE
-- list argument, so the callee's collecting parameter holds one element (the list): forwarding
-- items requires the explicit spread above.
def collectingForwardingBareNameUseValuesAlg : Algorithm :=
  algWithParameters [{ name := "values", kind := .collecting }] [] [] [
    .call (.resolve "CountItems") [.param "values"]
  ]

def collectingForwardingBareNamePassesOneListArgument : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("CountItems", collectingForwardingCountItemsAlg),
    ("Use", collectingForwardingBareNameUseValuesAlg)
  ] [
    .call (.resolve "Use") [.num 1, .num 2, .num 3]
  ])) with
  | Except.ok [1] => true
  | _ => false

#guard collectingForwardingBareNamePassesOneListArgument

def collectingForwardingUseSequenceValueHistoryAlg : Algorithm :=
  algWithParameterPatterns [
    .sequenceValue [.capture { name := "history", kind := .collecting }]
  ] [] [] [
    .call (.resolve "CountItems") [sequenceSpread (.param "history")]
  ]

def collectingForwardingSequenceValueRoot : Algorithm :=
  algPrivate [] [] [("CountItems", collectingForwardingCountItemsAlg), ("Use", collectingForwardingUseSequenceValueHistoryAlg)] [
    .call (.resolve "Use") [.capture [.num 1, .num 2, .num 3]]
  ]

def collectingForwardingSequenceValueCaptureStillWorks : Bool :=
  match runFlat (.algorithmExpr collectingForwardingSequenceValueRoot) with
  | Except.ok [3] => true
  | _ => false

#guard collectingForwardingSequenceValueCaptureStillWorks

def sequenceValueCollectingBoundaryCountSequenceValueAlg : Algorithm :=
  algWithParameterPatterns [
    .sequenceValue [.capture { name := "items", kind := .collecting }]
  ] [] [] [
    .dotCall (.param "items") "count" none
  ]

def sequenceValueCollectingBoundaryRoot : Algorithm :=
  algPrivate [] [] [("Pair", flatCollectingSlotValuesAlg), ("CountSequenceValue", sequenceValueCollectingBoundaryCountSequenceValueAlg)] [
    .call (.resolve "CountSequenceValue") [.resolve "Pair"]
  ]

def sequenceValueCollectingBoundaryDoesNotUseFlatSlotSpread : Bool :=
  match runFlat (.algorithmExpr sequenceValueCollectingBoundaryRoot) with
  | Except.ok [2] => true
  | _ => false

#guard sequenceValueCollectingBoundaryDoesNotUseFlatSlotSpread

def explicitCallSiteSequenceValue123 : Nat -> KatLang.Expr
  | 0 => .capture [.num 1, .num 2, .num 3]
  | Nat.succ depth => .capture [explicitCallSiteSequenceValue123 depth]

def explicitCallSiteSequenceValueLeftNested : KatLang.Expr :=
  .capture [.capture [.num 1, .num 2], .num 3]

def explicitCallSiteSequenceValueRightNested : KatLang.Expr :=
  .capture [.num 1, .capture [.num 2, .num 3]]

def explicitCallSiteSequenceValueCountSequenceValue1Alg : Algorithm :=
  algWithParameterPatterns [
    .capture { name := "values", kind := .collecting }
  ] [] [] [
    .dotCall (.param "values") "count" none
  ]

def explicitCallSiteSequenceValueCountSequenceValue2Alg : Algorithm :=
  algWithParameterPatterns [
    .sequenceValue [.capture { name := "values", kind := .collecting }]
  ] [] [] [
    .dotCall (.param "values") "count" none
  ]

def explicitCallSiteSequenceValueCountSequenceValue3Alg : Algorithm :=
  algWithParameterPatterns [
    .sequenceValue [.sequenceValue [.capture { name := "values", kind := .collecting }]]
  ] [] [] [
    .dotCall (.param "values") "count" none
  ]

def explicitCallSiteSequenceValueMatrixRoot : Algorithm :=
  algPrivate [] [] [
    ("CountSequenceValue1", explicitCallSiteSequenceValueCountSequenceValue1Alg),
    ("CountSequenceValue2", explicitCallSiteSequenceValueCountSequenceValue2Alg),
    ("CountSequenceValue3", explicitCallSiteSequenceValueCountSequenceValue3Alg)
  ] [
    .call (.resolve "CountSequenceValue1") [explicitCallSiteSequenceValue123 0],
    .call (.resolve "CountSequenceValue1") [explicitCallSiteSequenceValue123 1],
    .call (.resolve "CountSequenceValue2") [explicitCallSiteSequenceValue123 0],
    .call (.resolve "CountSequenceValue2") [explicitCallSiteSequenceValue123 1],
    .call (.resolve "CountSequenceValue2") [explicitCallSiteSequenceValue123 2],
    .call (.resolve "CountSequenceValue3") [explicitCallSiteSequenceValue123 1],
    .call (.resolve "CountSequenceValue3") [explicitCallSiteSequenceValue123 2],
    .call (.resolve "CountSequenceValue2") [explicitCallSiteSequenceValueLeftNested],
    .call (.resolve "CountSequenceValue2") [explicitCallSiteSequenceValueRightNested]
  ]

-- CountSequenceValue1 (flat collecting) collects the ONE grouped argument, so both
-- written depths count 1. CountSequenceValue2/3 (sequence-value patterns) open
-- exactly as many written grouping levels as they declare: at matching depth
-- the spread items collect to a three-element collected list (count 3), while one
-- EXTRA written level leaves a single grouped item in the collected list (count 1).
def sequenceValueCollectingParameterRespectsExplicitCallSiteSequenceValueDepth : Bool :=
  match runFlat (.algorithmExpr explicitCallSiteSequenceValueMatrixRoot) with
  | Except.ok [1, 1, 3, 1, 1, 3, 3, 2, 2] => true
  | _ => false

#guard sequenceValueCollectingParameterRespectsExplicitCallSiteSequenceValueDepth

def nestedSequenceValueCollectingParameterRejectsTooShallowExplicitSequenceValue : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [
    ("CountSequenceValue3", explicitCallSiteSequenceValueCountSequenceValue3Alg)
  ] [
    .call (.resolve "CountSequenceValue3") [explicitCallSiteSequenceValue123 0]
  ])) with
  | Except.error err => innermostIsArityMismatch 1 3 err
  | _ => false

#guard nestedSequenceValueCollectingParameterRejectsTooShallowExplicitSequenceValue

def explicitPropertyReferenceSequenceValueRoot : Algorithm :=
  algPrivate [] [] [
    ("Inner", alg [] [] [] [explicitCallSiteSequenceValue123 0]),
    ("CountSequenceValue2", explicitCallSiteSequenceValueCountSequenceValue2Alg)
  ] [
    .call (.resolve "CountSequenceValue2") [.resolve "Inner"],
    .call (.resolve "CountSequenceValue2") [.capture [.resolve "Inner"]],
    .call (.resolve "CountSequenceValue2") [.capture [.capture [.resolve "Inner"]]]
  ]

-- A bare property reference opens through the deconstruction pattern
-- (count 3), while each written parenthes level around it is one grouped item
-- for the pattern's collecting binding (count 1): written grouping is not erased by segment
-- collection.
def explicitPropertyReferenceSequenceValueIsSourceBacked : Bool :=
  match runFlat (.algorithmExpr explicitPropertyReferenceSequenceValueRoot) with
  | Except.ok [3, 1, 1] => true
  | _ => false

#guard explicitPropertyReferenceSequenceValueIsSourceBacked

-- Test 4: Ambiguous ordinary-dot lexical fallback via opens (error case)
-- Two opens both export G → ambiguousOpen error
def libA : Algorithm :=
  alg [] [] [publicProp "G" (alg ["x"] [] [] [.binary .add (.param "x") (.num 1)])] []

def libB : Algorithm :=
  alg [] [] [publicProp "G" (alg ["x"] [] [] [.binary .add (.param "x") (.num 2)])] []

def caller4 : Algorithm :=
  alg [] [.algorithmExpr libA, .algorithmExpr libB] [] [
    .dotCall (.algorithmExpr (alg [] [] [] [.num 5])) "G" none
  ]

def test4 : Bool :=
  match runResult (.algorithmExpr caller4) with
  | Except.error _ => true
  | Except.ok _ => false

#guard test4
-- EXPECTED: Expect.error (Error.ambiguousOpen "G" [...])
#eval runResult (.algorithmExpr caller4)

-- Open resolution regressions
--------------------------------------------------------------------------------

def openPrivateHeadLib : Algorithm :=
  alg [] []
    [ publicProp "X" (alg [] [] [] [.num 1])
    , privateProp "Hidden" (alg [] [] [] [.num 2])
    , privateProp "PrivateSub" (alg [] [] [publicProp "Y" (alg [] [] [] [.num 3])] [])
    ]
    []

-- Models the surface form:
--   open Lib
--   Lib = { ... }
-- where the open appears first and `Lib` is defined later in the same body.
def openPrivateHeadLaterRoot : Algorithm :=
  algPrivate [] [.resolve "Lib"] [("Lib", openPrivateHeadLib)] [.resolve "X"]

def openPrivateHeadLaterWorks : Bool :=
  match runFlat (.algorithmExpr openPrivateHeadLaterRoot) with
  | Except.ok [1] => true
  | _ => false

#guard openPrivateHeadLaterWorks

def openDoesNotExposePrivateMemberRoot : Algorithm :=
  algPrivate [] [.resolve "Lib"] [("Lib", openPrivateHeadLib)] [.resolve "Hidden"]

def openDoesNotExposePrivateMember : Bool :=
  match runResult (.algorithmExpr openDoesNotExposePrivateMemberRoot) with
  | Except.error err => innermostIsUnknownName "Hidden" err
  | Except.ok _ => false

#guard openDoesNotExposePrivateMember

def openMissingHeadRoot : Algorithm :=
  alg [] [.resolve "Missing"] [] [.resolve "X"]

def openMissingHeadStillErrors : Bool :=
  match runResult (.algorithmExpr openMissingHeadRoot) with
  | Except.error err =>
      hasContext "while resolving open: Missing" err
      && innermostIsUnknownName "Missing" err
  | Except.ok _ => false

#guard openMissingHeadStillErrors

def openBuiltinTargetRoot : Algorithm :=
  alg [] [.resolve "if"] [] [.resolve "X"]

def openBuiltinTargetStillIllegal : Bool :=
  match runResult (.algorithmExpr openBuiltinTargetRoot) with
  | Except.error err =>
      hasContext "while resolving open: if" err
      && innermostIsIllegalInOpen "builtin 'if'" err
  | Except.ok _ => false

#guard openBuiltinTargetStillIllegal

def openQualifiedPrivatePathRoot : Algorithm :=
  algPrivate [] [.dotCall (.resolve "Lib") "PrivateSub" none] [("Lib", openPrivateHeadLib)] [.resolve "Y"]

def openQualifiedPrivatePathStillRestricted : Bool :=
  match runResult (.algorithmExpr openQualifiedPrivatePathRoot) with
  | Except.error err =>
      hasContext "while resolving open: Lib.PrivateSub" err
      && innermostIsNotPublicProperty "Lib" "PrivateSub" err
  | Except.ok _ => false

#guard openQualifiedPrivatePathStillRestricted

def publicWrapperPrivateHelperAlg : Algorithm :=
  alg ["Candidate"] [] [
    privateLocalProp "Step" .localCapturedAncestorParams
      (alg [] [] [] [.binary .add (.param "Candidate") (.num 1)])
  ] [.resolve "Step"]

def publicWrapperPrivateHelperApi : Algorithm :=
  alg ["N"] [] [] [
    .call (.resolve "PrivateHelper") [.param "N"]
  ]

def publicWrapperPrivateHelperLib : Algorithm :=
  alg [] [] [
    privateProp "PrivateHelper" publicWrapperPrivateHelperAlg,
    publicProp "PublicApi" publicWrapperPrivateHelperApi
  ] []

def publicWrapperPrivateHelperOpenRoot : Algorithm :=
  alg [] [.algorithmExpr publicWrapperPrivateHelperLib] [] [
    .call (.resolve "PublicApi") [.num 5]
  ]

def publicWrapperPrivateHelperImportsPublicApi : Bool :=
  match runFlat (.algorithmExpr publicWrapperPrivateHelperOpenRoot) with
  | Except.ok [6] => true
  | _ => false

#guard publicWrapperPrivateHelperImportsPublicApi

def publicWrapperPrivateHelperHiddenRoot : Algorithm :=
  alg [] [.algorithmExpr publicWrapperPrivateHelperLib] [] [
    .call (.resolve "PrivateHelper") [.num 5]
  ]

def publicWrapperPrivateHelperKeepsPrivateHelperHidden : Bool :=
  match runResult (.algorithmExpr publicWrapperPrivateHelperHiddenRoot) with
  | Except.error err => innermostIsUnknownName "PrivateHelper" err
  | Except.ok _ => false

#guard publicWrapperPrivateHelperKeepsPrivateHelperHidden

def openedMemberBuiltinIfAlg : Algorithm :=
  alg ["x"] [] [] [
    .call (.resolve "if") [
      .binary .gt (.param "x") (.num 0),
      .num 1,
      .num 0
    ]
  ]

def openedMemberBuiltinIfVec : Algorithm :=
  alg [] [] [publicProp "Test" openedMemberBuiltinIfAlg] []

def openedMemberBuiltinIfRoot : Algorithm :=
  algPrivate [] [.resolve "Vec"] [("Vec", openedMemberBuiltinIfVec)] [
    .call (.resolve "Test") [.num 35]
  ]

def openedMemberBuiltinIfWorks : Bool :=
  match runFlat (.algorithmExpr openedMemberBuiltinIfRoot) with
  | Except.ok [1] => true
  | _ => false

#guard openedMemberBuiltinIfWorks

def openedMemberBuiltinSumVec : Algorithm :=
  alg [] [] [publicProp "SumPair" (alg ["x", "y"] [] [] [
    .dotCall (.capture [.param "x", .param "y"]) "sum" none
  ])] []

def openedMemberBuiltinSumRoot : Algorithm :=
  algPrivate [] [.resolve "Vec"] [("Vec", openedMemberBuiltinSumVec)] [
    .call (.resolve "SumPair") [.num 3, .num 4]
  ]

def openedMemberBuiltinSumWorks : Bool :=
  match runFlat (.algorithmExpr openedMemberBuiltinSumRoot) with
  | Except.ok [7] => true
  | _ => false

#guard openedMemberBuiltinSumWorks

def inlineOpenedMemberBuiltinSumVec : Algorithm :=
  alg [] [] [publicProp "SumPair" (alg ["x", "y"] [] [] [
    .dotCall (.capture [.param "x", .param "y"]) "sum" none
  ])] []

def inlineOpenedMemberBuiltinSumRoot : Algorithm :=
  alg [] [.algorithmExpr inlineOpenedMemberBuiltinSumVec] [] [
    .call (.resolve "SumPair") [.num 3, .num 4]
  ]

def inlineOpenedMemberBuiltinSumWorks : Bool :=
  match runFlat (.algorithmExpr inlineOpenedMemberBuiltinSumRoot) with
  | Except.ok [7] => true
  | _ => false

#guard inlineOpenedMemberBuiltinSumWorks

def inlineOpenedMemberBuiltinSumShadowVec : Algorithm :=
  alg [] [] [publicProp "Use" (alg [] [] [] [
    .dotCall (.capture [.num 1, .num 2]) "sum" none
  ])] []

def inlineOpenedMemberBuiltinSumShadowRoot : Algorithm :=
  algPrivate [] [.algorithmExpr inlineOpenedMemberBuiltinSumShadowVec] [
    ("sum", alg [] [] [] [.num 99])
  ] [.resolve "Use"]

def inlineOpenedMemberBuiltinSumIgnoresOpenerShadow : Bool :=
  match runFlat (.algorithmExpr inlineOpenedMemberBuiltinSumShadowRoot) with
  | Except.ok [3] => true
  | _ => false

#guard inlineOpenedMemberBuiltinSumIgnoresOpenerShadow

def openedMemberDefinitionSiteCaptureVec : Algorithm :=
  alg [] [] [
    publicProp "Test" (alg ["x"] [] [] [.binary .add (.resolve "A") (.param "x")])
  ] []

def openedMemberDefinitionSiteCaptureScope : Algorithm :=
  algPrivate [] [.resolve "Vec"] [("A", alg [] [] [] [.num 100])] [
    .call (.resolve "Test") [.num 5]
  ]

def openedMemberDefinitionSiteCaptureRoot : Algorithm :=
  algPrivate [] [] [
    ("A", alg [] [] [] [.num 10]),
    ("Vec", openedMemberDefinitionSiteCaptureVec),
    ("Scope", openedMemberDefinitionSiteCaptureScope)
  ] [.resolve "Scope"]

def openedMemberUsesDefinitionSiteNotOpenerSite : Bool :=
  match runFlat (.algorithmExpr openedMemberDefinitionSiteCaptureRoot) with
  | Except.ok [15] => true
  | _ => false

#guard openedMemberUsesDefinitionSiteNotOpenerSite

-- Test 5: Structural property takes precedence over ordinary-dot lexical fallback
-- a.G where G(x) = x+1 is structural on receiver, no args → arity mismatch (navigation-only)
-- Even though lexical scope also defines G, structural match takes priority → error, not fallback
def lexicalG : Algorithm :=
  alg ["x"] [] [] [.binary .mul (.param "x") (.num 100)]

def receiver5 : Algorithm :=
  algPrivate [] [] [("G", incAlg)] [.num 5]

def outer5 : Algorithm :=
  algPrivate [] [] [("G", lexicalG)] [
    .dotCall (.algorithmExpr receiver5) "G" none
  ]

def test5a : Bool :=
  match runResult (.algorithmExpr outer5) with
  | Except.error _ => true   -- structural G found but arity mismatch (no fallback to lexical)
  | Except.ok _ => false

#guard test5a
-- EXPECTED: Except.error (arityMismatch 1 0)
#eval runResult (.algorithmExpr outer5)

-- Test 5b: Structural property with explicit args → navigation wins over lexical
-- a.G(5) where structural G(x)=x+1 → 6 (not lexicalG which would give 500)
def test5b : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("G", lexicalG)] [
    .dotCall (.algorithmExpr receiver5) "G" (some [.num 5])
  ])) with
  | Except.ok [6] => true
  | _ => false

#guard test5b
-- EXPECTED: Except.ok [6] (structural incAlg wins, not lexicalG)
#eval runFlat (.algorithmExpr (algPrivate [] [] [("G", lexicalG)] [
    .dotCall (.algorithmExpr receiver5) "G" (some [.num 5])
  ]))

end KatLangTests
