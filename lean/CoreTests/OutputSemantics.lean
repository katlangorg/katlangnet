import KatLang
import CoreTests.Common

namespace KatLangTests
open KatLang (alg algWithParameters algWithParameterPatterns algPrivate privateProp publicProp privateLocalProp publicLocalProp runFlat runResult Algorithm Error Result PropExposure)

--------------------------------------------------------------------------------
-- missingOutput semantics tests
--------------------------------------------------------------------------------

def noOutputBraceAlg : Algorithm :=
  algPrivate [] [] [("X", alg [] [] [] [.num 1])] []

def missingOutputRootOnlyDefinitions : Algorithm :=
  algPrivate [] [] [("A", noOutputBraceAlg)] []

def missingOutputRootOnlyDefinitionsFails : Bool :=
  match runResult (.algorithmExpr missingOutputRootOnlyDefinitions) with
  | Except.error err => innermostIsMissingOutput err
  | Except.ok _ => false

#guard missingOutputRootOnlyDefinitionsFails

def missingOutputRootWithTrailingOutput : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("T", alg [] [] [] [.num 4])] [
    .resolve "T"
  ])) with
  | Except.ok [4] => true
  | _ => false

#guard missingOutputRootWithTrailingOutput

def missingOutputRootWithExplicitEmptyOutput : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("T", alg [] [] [] [.num 4])] [
    .emptySequence 0
  ])) with
  | Except.ok (.sequenceValue []) => true
  | _ => false

#guard missingOutputRootWithExplicitEmptyOutput

def missingOutputRootValueDoesNotEqualEmpty : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("T", alg [] [] [] [.num 4])] [
    .binary .eq (.resolve "T") (.emptySequence 0)
  ])) with
  | Except.ok [0] => true
  | _ => false

#guard missingOutputRootValueDoesNotEqualEmpty

def missingOutputMultipleDefinitionsRoot : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [
    ("Price", alg [] [] [] [.num 10]),
    ("Tax", alg [] [] [] [.num 2]),
    ("Total", alg [] [] [] [.binary .add (.resolve "Price") (.resolve "Tax")])
  ] [])) with
  | Except.error err => innermostIsMissingOutput err
  | Except.ok _ => false

#guard missingOutputMultipleDefinitionsRoot

def missingOutputMultipleDefinitionsWithOutput : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("Price", alg [] [] [] [.num 10]),
    ("Tax", alg [] [] [] [.num 2]),
    ("Total", alg [] [] [] [.binary .add (.resolve "Price") (.resolve "Tax")])
  ] [
    .resolve "Total"
  ])) with
  | Except.ok [12] => true
  | _ => false

#guard missingOutputMultipleDefinitionsWithOutput

def missingOutputValid2Root : Algorithm :=
  algPrivate [] [] [("A", noOutputBraceAlg)] [
    .dotCall (.resolve "A") "X" none
  ]

def missingOutputValid2 : Bool :=
  match runFlat (.algorithmExpr missingOutputValid2Root) with
  | Except.ok [1] => true
  | _ => false

#guard missingOutputValid2

def applyMissingOutputAlg : Algorithm :=
  alg ["f"] [] [] [
    .call (.param "f") [.num 4]
  ]

def incMissingOutputAlg : Algorithm :=
  alg ["x"] [] [] [
    .binary .add (.param "x") (.num 1)
  ]

def missingOutputValid3Root : Algorithm :=
  algPrivate [] [] [("Apply", applyMissingOutputAlg), ("Inc", incMissingOutputAlg)] [
    .call (.resolve "Apply") [.resolve "Inc"]
  ]

def missingOutputValid3 : Bool :=
  match runFlat (.algorithmExpr missingOutputValid3Root) with
  | Except.ok [5] => true
  | _ => false

#guard missingOutputValid3

def holderMissingOutputAlg : Algorithm :=
  algPrivate [] [] [("F", noOutputBraceAlg)] [.num 0]

def missingOutputValid4Root : Algorithm :=
  algPrivate [] [] [("Holder", holderMissingOutputAlg)] [.resolve "Holder"]

def missingOutputValid4 : Bool :=
  match runFlat (.algorithmExpr missingOutputValid4Root) with
  | Except.ok [0] => true
  | _ => false

#guard missingOutputValid4

def missingOutputError5Root : Algorithm :=
  algPrivate [] [] [("A", noOutputBraceAlg)] [.resolve "A"]

def missingOutputError5 : Bool :=
  match runResult (.algorithmExpr missingOutputError5Root) with
  | Except.error err =>
      hasContext "while evaluating property A" err
      && innermostIsMissingOutput err
  | Except.ok _ => false

#guard missingOutputError5

def missingOutputError6Root : Algorithm :=
  algPrivate [] [] [("A", noOutputBraceAlg)] [
    .call (.resolve "A") []
  ]

def missingOutputError6 : Bool :=
  match runResult (.algorithmExpr missingOutputError6Root) with
  | Except.error err =>
      hasContext "while evaluating call to A" err
      && innermostIsMissingOutput err
  | Except.ok _ => false

#guard missingOutputError6

def missingOutputError6bRoot : Algorithm :=
  algPrivate [] [] [("A", noOutputBraceAlg)] [
    .call (.resolve "A") [.num 6]
  ]

def missingOutputError6b : Bool :=
  match runResult (.algorithmExpr missingOutputError6bRoot) with
  | Except.error err =>
      hasContext "while evaluating call to A" err
      && innermostIsMissingOutput err
  | Except.ok _ => false

#guard missingOutputError6b

def missingOutputError7Root : Algorithm :=
  algPrivate [] [] [("A", noOutputBraceAlg)] [
    .binary .add (.resolve "A") (.num 1)
  ]

def missingOutputError7 : Bool :=
  match runResult (.algorithmExpr missingOutputError7Root) with
  | Except.error err =>
      hasContext "while evaluating property A" err
      && innermostIsMissingOutput err
  | Except.ok _ => false

#guard missingOutputError7

def missingOutputError8Root : Algorithm :=
  algPrivate [] [] [("A", noOutputBraceAlg)] [
    .unary .minus (.resolve "A")
  ]

def missingOutputError8 : Bool :=
  match runResult (.algorithmExpr missingOutputError8Root) with
  | Except.error err =>
      hasContext "while evaluating property A" err
      && innermostIsMissingOutput err
  | Except.ok _ => false

#guard missingOutputError8

def missingOutputError9Root : Algorithm :=
  algPrivate [] [] [
    ("A", noOutputBraceAlg),
    ("B", alg [] [] [] [.resolve "A"])
  ] [
    .resolve "B"
  ]

def missingOutputError9 : Bool :=
  match runResult (.algorithmExpr missingOutputError9Root) with
  | Except.error err => innermostIsMissingOutput err
  | Except.ok _ => false

#guard missingOutputError9

def useMissingOutputAlg : Algorithm :=
  alg ["f"] [] [] [.num 0]

def missingOutputValid10Root : Algorithm :=
  algPrivate [] [] [("A", noOutputBraceAlg), ("Use", useMissingOutputAlg)] [
    .call (.resolve "Use") [.resolve "A"]
  ]

def missingOutputValid10 : Bool :=
  match runFlat (.algorithmExpr missingOutputValid10Root) with
  | Except.ok [0] => true
  | _ => false

#guard missingOutputValid10

--------------------------------------------------------------------------------
-- empty sequence value () tests
--------------------------------------------------------------------------------

def explicitEmptyExpr : KatLang.Expr := .emptySequence 0

def explicitEmptyOutputBody : KatLang.Expr :=
  .algorithmExpr (alg [] [] [] [explicitEmptyExpr])

def missingOutputBodyExpr : KatLang.Expr :=
  .algorithmExpr (alg [] [] [] [])

def explicitEmptyIsEvenAlg : Algorithm :=
  alg ["x"] [] [] [
    .binary .eq (.binary .mod (.param "x") (.num 2)) (.num 0)
  ]

def explicitEmptyNoOutputContainer : Algorithm :=
  algPrivate [] [] [("Prop", alg [] [] [] [.num 7])] []

def explicitEmptyProducesZeroValues : Bool :=
  match runResult explicitEmptyExpr, runFlat explicitEmptyExpr with
  | Except.ok (.sequenceValue []), Except.ok [] => true
  | _, _ => false

#guard explicitEmptyProducesZeroValues

def explicitEmptyCountsAsZero : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("A", alg [] [] [] [explicitEmptyExpr])] [
    .dotCall explicitEmptyExpr "count" none,
    .call (.resolve "count") [explicitEmptyExpr],
    .dotCall explicitEmptyOutputBody "count" none,
    .dotCall (.algorithmExpr (alg [] [] [] [explicitEmptyExpr])) "count" none,
    .dotCall (.resolve "A") "count" none
  ])) with
  | Except.ok [0, 0, 0, 0, 0] => true
  | _ => false

#guard explicitEmptyCountsAsZero

def explicitEmptyEquality : Bool :=
  match runFlat (.algorithmExpr (alg [] [] [] [
    .binary .eq explicitEmptyExpr explicitEmptyExpr,
    .binary .ne explicitEmptyExpr explicitEmptyExpr,
    .binary .eq explicitEmptyExpr explicitEmptyOutputBody,
    .binary .eq explicitEmptyOutputBody explicitEmptyExpr,
    -- Collection builtins materialize exact lists, so an all-rejected filter
    -- and an all-skipped skip yield `[]`, which is NOT the empty sequence `()`.
    .binary .eq
      (.call (.resolve "filter") [
        .sequenceConstruct (.num 1) (.sequenceConstruct (.num 3) (.num 5)),
        .algorithmExpr explicitEmptyIsEvenAlg
      ])
      explicitEmptyExpr,
    .binary .eq
      explicitEmptyExpr
      (.call (.resolve "filter") [
        .sequenceConstruct (.num 1) (.sequenceConstruct (.num 3) (.num 5)),
        .algorithmExpr explicitEmptyIsEvenAlg
      ]),
    .binary .eq
      (.dotCall (.num 0) "skip" (some [.num 1]))
      explicitEmptyExpr
  ])) with
  | Except.ok [1, 0, 1, 1, 0, 0, 0] => true
  | _ => false

#guard explicitEmptyEquality

-- Internal sequence construction of spreads:
-- `sequenceConstruct (sequenceConstruct (sequenceSpread 1) empty) (sequenceSpread 2)`.
-- The `empty` contribution adds no items (join semantics), so the flat
-- result is [1, 2].
def spreadEmptyJoinContributesNoItems : Bool :=
  match runFlat (.sequenceConstruct
      (.sequenceConstruct (sequenceSpread (.num 1)) explicitEmptyExpr)
      (sequenceSpread (.num 2))) with
  | Except.ok [1, 2] => true
  | _ => false

#guard spreadEmptyJoinContributesNoItems

-- `()*` spreads the empty sequence value, contributing zero items.
def spreadOfEmptyContributesNoItems : Bool :=
  match runFlat (sequenceSpread explicitEmptyExpr) with
  | Except.ok [] => true
  | _ => false

#guard spreadOfEmptyContributesNoItems

-- A written sequence value with a spread beside a sibling slot splices the
-- spread items: source `A = 1, 2` then `(A*, 99)` is `(1, 2, 99)`, never the
-- grouped `((1, 2), 99)`. This pins `evalAlgOutputCore` as the value
-- projection of `evalAlgOutputCountedCore` (July 2026 fix): the plain and
-- counted evaluators must agree on value-position block output.
def valuePositionSpreadWithSiblingSplices : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("A", alg [] [] [] [.num 1, .num 2])] [
    .capture [sequenceSpread (.resolve "A"), .num 99]
  ])) with
  | Except.ok (.sequenceValue [.atom 1, .atom 2, .atom 99]) => true
  | _ => false

#guard valuePositionSpreadWithSiblingSplices

-- The same splicing holds for the root program output observed through the
-- plain `runResult` path: `A*, 99` is three root slots `1, 2, 99`.
def rootSpreadWithSiblingSplices : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("A", alg [] [] [] [.num 1, .num 2])] [
    sequenceSpread (.resolve "A"), .num 99
  ])) with
  | Except.ok (.sequenceValue [.atom 1, .atom 2, .atom 99]) => true
  | _ => false

#guard rootSpreadWithSiblingSplices

-- Splicing spreads never erases a written non-spread `()` slot between them:
-- `(1*, (), 2*)` keeps the empty sequence value as a visible item.
def spreadSiblingsKeepWrittenEmptySlot : Bool :=
  match runResult (.algorithmExpr (alg [] [] [] [
    .capture [sequenceSpread (.num 1), explicitEmptyExpr, sequenceSpread (.num 2)]
  ])) with
  | Except.ok (.sequenceValue [.atom 1, .sequenceValue [], .atom 2]) => true
  | _ => false

#guard spreadSiblingsKeepWrittenEmptySlot

-- Structural equality observes the spliced value through the plain
-- (non-counted) evaluation path used for binary operands.
def spreadSeqLiteralEqualsFlatLiteral : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("P", alg [] [] [] [.num 1, .num 2])] [
    .binary .eq (.capture [sequenceSpread (.resolve "P"), .num 99])
      (.capture [.num 1, .num 2, .num 99])
  ])) with
  | Except.ok [1] => true
  | _ => false

#guard spreadSeqLiteralEqualsFlatLiteral

-- Spreading a DIRECT written block whose output is missing reports the
-- spread-specific error, exactly like the generic operand arm (T4-2, Aug
-- 2026): `{X = 1}*` is `spreadMissingOutput`, never raw `missingOutput`,
-- and the rule holds at every spread position — root row, list element,
-- and call-argument slot. C#: `EvalSequenceSpreadOperandItems` Block arm.
def directBlockSpreadMissingOutput : Bool :=
  match runResult (.algorithmExpr (alg [] [] [] [sequenceSpread (.algorithmExpr noOutputBraceAlg)])) with
  | Except.error err => innermostIsSpreadMissingOutput err
  | _ => false

#guard directBlockSpreadMissingOutput

def directBlockSpreadInListMissingOutput : Bool :=
  match runResult (.algorithmExpr (alg [] [] [] [.listLiteral [sequenceSpread (.algorithmExpr noOutputBraceAlg)]])) with
  | Except.error err => innermostIsSpreadMissingOutput err
  | _ => false

#guard directBlockSpreadInListMissingOutput

def directBlockSpreadCallArgMissingOutput : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("F", alg ["a"] [] [] [.param "a"])] [
    .call (.resolve "F") [sequenceSpread (.algorithmExpr noOutputBraceAlg)]
  ])) with
  | Except.error err => innermostIsSpreadMissingOutput err
  | _ => false

#guard directBlockSpreadCallArgMissingOutput

-- Control: the resolved-name operand keeps its established behavior —
-- `Bad = {X = 1}` then `Bad*` reports the same spread-specific error, so
-- the direct-block and resolved spellings agree.
def resolvedSpreadMissingOutput : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("Bad", noOutputBraceAlg)] [
    sequenceSpread (.resolve "Bad")
  ])) with
  | Except.error err => innermostIsSpreadMissingOutput err
  | _ => false

#guard resolvedSpreadMissingOutput

-- Control: only the missing-output failure is translated — any other
-- error from a direct block spread operand propagates unchanged.
def directBlockSpreadOtherErrorPropagates : Bool :=
  match runResult (.algorithmExpr (alg [] [] [] [
    sequenceSpread (.algorithmExpr (alg [] [] [] [.resolve "nope"]))
  ])) with
  | Except.error err => innermostIsUnknownName "nope" err && !innermostIsSpreadMissingOutput err
  | _ => false

#guard directBlockSpreadOtherErrorPropagates

-- INTERNAL-NODE CONTAINMENT (July 2026 audit). `sequenceConstruct` is an
-- internal join node — NOT the representation of written parentheses, which
-- parse to `capture` nodes since the OutputBundle split. Its value evaluation
-- DROPS `()` leaves (join semantics: an empty contribution adds no items);
-- written parentheses always keep a non-spread `()` item visible. The guards
-- below pin that intentional difference structurally so any change to either
-- side — including a parser/desugaring change that routes surface syntax
-- through the internal node — is caught. C# twins live in
-- SequenceConstructContainmentTests; Lean/C# agreement on these exact ASTs
-- is enforced by the generated SemanticExplorerCases internal-node section.

-- sequenceConstruct ((), 1) drops the `()` leaf and singleton-collapses to 1 …
def internalSequenceConstructDropsEmptyLeafAndCollapses : Bool :=
  match runResult (.sequenceConstruct (.emptySequence 0) (.num 1)) with
  | Except.ok (.atom 1) => true
  | _ => false

#guard internalSequenceConstructDropsEmptyLeafAndCollapses

-- … while the written form `((), 1)` (a surviving capture) keeps the
-- empty item visible. This pair is the intentional-difference contrast.
def writtenParenthesesKeepEmptyItemVisible : Bool :=
  match runResult (.capture [.emptySequence 0, .num 1]) with
  | Except.ok (.sequenceValue [.sequenceValue [], .atom 1]) => true
  | _ => false

#guard writtenParenthesesKeepEmptyItemVisible

-- sequenceConstruct ((), ()) drops both leaves to the empty sequence value.
def internalSequenceConstructBothEmptyLeavesDropToEmpty : Bool :=
  match runResult (.sequenceConstruct (.emptySequence 0) (.emptySequence 0)) with
  | Except.ok (.sequenceValue []) => true
  | _ => false

#guard internalSequenceConstructBothEmptyLeavesDropToEmpty

-- sequenceConstruct ((1, 2), ()) drops `()` and collapses to the pair; the
-- written `((1, 2), ())` keeps both items.
def internalSequenceConstructDropsEmptyBesidePair : Bool :=
  match
    runResult (.sequenceConstruct (.capture [.num 1, .num 2]) (.emptySequence 0)),
    runResult (.algorithmExpr (alg [] [] [] [.capture [.capture [.num 1, .num 2], .emptySequence 0]]))
  with
  | Except.ok (.sequenceValue [.atom 1, .atom 2]),
    Except.ok (.sequenceValue [.sequenceValue [.atom 1, .atom 2], .sequenceValue []]) => true
  | _, _ => false

#guard internalSequenceConstructDropsEmptyBesidePair

-- A lone sequenceConstruct argument to a builtin is an ordinary value
-- expression: it evaluates to ONE grouped value and counts as ONE fixed-arity
-- argument — the same as the written grouped form. take(SC[1, 2, 5]) is one
-- argument where `take(collection, count)` expects two, exactly like surface
-- `take((1, 2, 5))`; with an explicit count both forms agree, and
-- sequenceConstruct still drops its `()` leaves (sum(SC[(), 1, 2]) is 3).
-- (C# once had a legacy reshape that special-cased this shape and diverged;
-- it was removed in the July 2026 containment audit.)
def internalSequenceConstructLoneBuiltinArgBindsLikeGroupedForm : Bool :=
  let loneScErrsLikeGroupedSurfaceForm :=
    match
      runResult (.call (.resolve "take") [
        .sequenceConstruct (.sequenceConstruct (.num 1) (.num 2)) (.num 5)]),
      runResult (.call (.resolve "take") [
        .capture [.num 1, .num 2, .num 5]])
    with
    | Except.error scErr, Except.error groupedErr =>
        innermostIsArityMismatch 2 1 scErr && innermostIsArityMismatch 2 1 groupedErr
    | _, _ => false
  let scBindsLikeGroupedForm :=
    match
      runResult (.call (.resolve "take") [
        .sequenceConstruct (.sequenceConstruct (.num 1) (.num 2)) (.num 5), .num 2]),
      runResult (.call (.resolve "sum") [
        .sequenceConstruct (.num 1) (.num 2)])
    with
    | Except.ok (.listValue [.atom 1, .atom 2]), Except.ok (.atom 3) => true
    | _, _ => false
  let scStillDropsEmptyLeaves :=
    match runResult (.call (.resolve "sum") [
      .sequenceConstruct (.sequenceConstruct (.emptySequence 0) (.num 1)) (.num 2)]) with
    | Except.ok (.atom 3) => true
    | _ => false
  loneScErrsLikeGroupedSurfaceForm && scBindsLikeGroupedForm && scStillDropsEmptyLeaves

#guard internalSequenceConstructLoneBuiltinArgBindsLikeGroupedForm

-- Repeated ordinary parentheses around the empty sequence canonicalize to `()`.
def emptyVsNestedEmptyEquality : Bool :=
  match runFlat (.algorithmExpr (alg [] [] [] [
    .binary .eq (.emptySequence 0) (.emptySequence 0),
    .binary .eq (.emptySequence 0) (.emptySequence 1),
    .binary .ne (.emptySequence 0) (.emptySequence 1)
  ])) with
  | Except.ok [1, 1, 0] => true
  | _ => false

#guard emptyVsNestedEmptyEquality

-- The empty sequence value has zero items; redundant empty nesting does too.
def emptyAndNestedEmptyCount : Bool :=
  match runFlat (.algorithmExpr (alg [] [] [] [
    .call (.resolve "count") [.emptySequence 0],
    .call (.resolve "count") [.emptySequence 1]
  ])) with
  | Except.ok [0, 0] => true
  | _ => false

#guard emptyAndNestedEmptyCount

-- (()) and ((())) evaluate to the canonical empty sequence value.
def nestedEmptyStructureCanonicalizes : Bool :=
  match runResult (.emptySequence 1) with
  | Except.ok (.sequenceValue []) => true
  | _ => false

#guard nestedEmptyStructureCanonicalizes

-- `empty` is no longer reserved: it is an ordinary identifier that can be defined.
def emptyIsOrdinaryIdentifier : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("empty", alg [] [] [] [.num 123])] [
    .resolve "empty"
  ])) with
  | Except.ok [123] => true
  | _ => false

#guard emptyIsOrdinaryIdentifier

-- Block/root output preserves visible empty sequence slots, but redundant empty
-- nesting has already canonicalized to `()`.
def blockOutputCanonicalizesNestedEmptyDepth : Bool :=
  match
    runResult (.emptySequence 0),
    runResult (.emptySequence 1),
    runResult (.algorithmExpr (alg [] [] [] [.emptySequence 0])),
    runResult (.algorithmExpr (alg [] [] [] [.emptySequence 1])),
    runResult (.algorithmExpr (alg [] [] [] [.emptySequence 2]))
  with
  | Except.ok (.sequenceValue []),
    Except.ok (.sequenceValue []),
    Except.ok (.sequenceValue []),
    Except.ok (.sequenceValue []),
    Except.ok (.sequenceValue []) => true
  | _, _, _, _, _ => false

#guard blockOutputCanonicalizesNestedEmptyDepth

-- Mixed output: a normal non-spread `()` output is a VISIBLE slot, not dropped, so it sits
-- beside other outputs. (Only an explicit spread `()*` contributes zero items.) These would
-- fail if evalAlgOutputCore dropped count-0 non-spread slots.
def mixedOutputKeepsLeadingEmptySlot : Bool :=
  match runResult (.algorithmExpr (alg [] [] [] [.emptySequence 0, .num 1])) with
  | Except.ok (.sequenceValue [.sequenceValue [], .atom 1]) => true
  | _ => false

#guard mixedOutputKeepsLeadingEmptySlot

def mixedOutputKeepsMiddleEmptySlot : Bool :=
  match runResult (.algorithmExpr (alg [] [] [] [.num 1, .emptySequence 0, .num 2])) with
  | Except.ok (.sequenceValue [.atom 1, .sequenceValue [], .atom 2]) => true
  | _ => false

#guard mixedOutputKeepsMiddleEmptySlot

-- An explicit spread of `()` still contributes zero items, so it does NOT add a slot:
-- `(()*, 1)` is just `1`.
def mixedOutputSpreadOfEmptyContributesNoSlot : Bool :=
  match runResult (.algorithmExpr (alg [] [] [] [sequenceSpread (.emptySequence 0), .num 1])) with
  | Except.ok (.atom 1) => true
  | _ => false

#guard mixedOutputSpreadOfEmptyContributesNoSlot

-- Redundant empty nesting is not a surface way to construct a one-item
-- collection containing `()`; collection builtins see it as the empty collection.
def collectionBuiltinAlwaysTrue : KatLang.Expr := .algorithmExpr (alg ["x"] [] [] [.num 1])

def filterNestedEmptyInputCanonicalizesToEmptyCollection : Bool :=
  match runResult (.call (.resolve "filter") [.emptySequence 1, collectionBuiltinAlwaysTrue]) with
  | Except.ok (.listValue []) => true
  | _ => false

#guard filterNestedEmptyInputCanonicalizesToEmptyCollection

def countFilterNestedEmptyInputCanonicalizesToZero : Bool :=
  match runResult (.call (.resolve "count") [
        .call (.resolve "filter") [.emptySequence 1, collectionBuiltinAlwaysTrue]
      ]) with
  | Except.ok (.atom 0) => true
  | _ => false

#guard countFilterNestedEmptyInputCanonicalizesToZero

def takeNestedEmptyInputCanonicalizesToEmptyCollection : Bool :=
  match runResult (.call (.resolve "take") [.emptySequence 1, .num 1]) with
  | Except.ok (.listValue []) => true
  | _ => false

#guard takeNestedEmptyInputCanonicalizesToEmptyCollection

def skipNestedEmptyInputCanonicalizesToEmptyCollection : Bool :=
  match runResult (.call (.resolve "skip") [.emptySequence 1, .num 0]) with
  | Except.ok (.listValue []) => true
  | _ => false

#guard skipNestedEmptyInputCanonicalizesToEmptyCollection

def distinctNestedEmptyInputCanonicalizesToEmptyCollection : Bool :=
  match runResult (.call (.resolve "distinct") [.emptySequence 1]) with
  | Except.ok (.listValue []) => true
  | _ => false

#guard distinctNestedEmptyInputCanonicalizesToEmptyCollection

-- Filtering a two-item collection down to one kept `(1, 2)` materializes the
-- exact one-element list `[(1, 2)]`: collection-producing builtins never apply
-- singleton-boundary erasure to their list results — the kept sequence value
-- stays one exact element (`[(1, 2)]` is a writable KatLang value).
def filterSingleKeptSequenceValueItemStaysExactElement : Bool :=
  let keepFirstPair : KatLang.Expr := .algorithmExpr (alg ["pair"] [] [] [
    .binary .eq (.index (.param "pair") (.num 0)) (.num 1)
  ])
  match runResult (.call (.resolve "filter") [
        sequenceItems [
          .capture [.num 1, .num 2],
          .capture [.num 3, .num 4]
        ],
        keepFirstPair
      ]) with
  | Except.ok (.listValue [.sequenceValue [.atom 1, .atom 2]]) => true
  | _ => false

#guard filterSingleKeptSequenceValueItemStaysExactElement

-- An internal `sequenceConstruct (sequenceSpread A) B` is ONE sequence-value argument in
-- fixed-arity call-argument position and therefore fails to bind a two-parameter
-- call. Surface `A* B` is an expression list, not this constructed value.
def spreadThenJoinIsOneSequenceValueArgument : Bool :=
  let useTwo := alg ["a", "b"] [] [] [.binary .add (.param "a") (.param "b")]
  let joined := algPrivate [] [] [("A", alg [] [] [] [.num 1]), ("F", useTwo)] [
    .call (.resolve "F") [.sequenceConstruct (sequenceSpread (.resolve "A")) (.num 2)]
  ]
  match runFlat (.algorithmExpr joined) with
  | Except.error err => innermostIsArityMismatch 1 0 err
  | _ => false

#guard spreadThenJoinIsOneSequenceValueArgument

-- An internal `sequenceConstruct` node in call-FUNCTION position cannot
-- resolve to an algorithm; the structured payload is exactly
-- "sequence construct expression" on both sides of the differential
-- (T4-3, Aug 2026 — the C# `ResolveAlg` description must match verbatim).
def sequenceConstructCallFunctionNotAnAlgorithm : Bool :=
  match runResult (.algorithmExpr (alg [] [] [] [
    .call (.sequenceConstruct (.num 1) (.num 2)) [.num 3]
  ])) with
  | Except.error err => innermostIsNotAnAlgorithm "sequence construct expression" err
  | _ => false

#guard sequenceConstructCallFunctionNotAnAlgorithm

-- Source `1` followed by `depth` attached spread markers is the unary chain
-- `sequenceSpread (sequenceSpread (... (num 1)))`. Built tail-recursively to
-- avoid overflow while constructing the term.
partial def buildNestedSpread (depth : Nat) (acc : KatLang.Expr) : KatLang.Expr :=
  if depth = 0 then acc
  else buildNestedSpread (depth - 1) (KatLang.Expr.sequenceSpread acc)

def deeplyNestedSpreadExpr (depth : Nat) : KatLang.Expr :=
  buildNestedSpread depth (KatLang.Expr.num 1)

-- Deeply-nested unary spread must stay stack-safe: `evalSequenceSpreadCounted`
-- peels the nesting iteratively via `peelSequenceSpread` rather than recursing
-- once per level. A recursive peel would overflow at this depth. Each level
-- spreads the same single item, so the flat result is `[1]` with count 1.
def deepNestedSequenceSpreadIsStackSafe : Bool :=
  match KatLang.runEvalM (KatLang.evalCounted (deeplyNestedSpreadExpr 8192)
      { callStack := [KatLang.preludeAlg], algEnv := [] } []) with
  | Except.ok (value, count) => KatLang.Result.atoms value == [1] && count == 1
  | _ => false

#guard deepNestedSequenceSpreadIsStackSafe

def sequenceConstructEmitsOneConstructedSequenceValue : Bool :=
  match runResult (.sequenceConstruct (.num 1) (.num 2)),
        runFlat (.sequenceConstruct (.num 1) (.num 2)) with
  | Except.ok (.sequenceValue [.atom 1, .atom 2]), Except.ok [1, 2] => true
  | _, _ => false

#guard sequenceConstructEmitsOneConstructedSequenceValue

def sequenceConstructCommaPriorityConstructsOneValue : Bool :=
  let joined := .sequenceConstruct (.sequenceConstruct (.num 1) (.num 2)) (.num 3)
  match runResult (.algorithmExpr (alg [] [] [] [joined])),
        KatLang.runEvalM (KatLang.evalCounted joined { callStack := [KatLang.preludeAlg], algEnv := [] } []) with
  | Except.ok (.sequenceValue [.atom 1, .atom 2, .atom 3]),
    Except.ok (.sequenceValue [.atom 1, .atom 2, .atom 3], 1) => true
  | _, _ => false

#guard sequenceConstructCommaPriorityConstructsOneValue

def sequenceConstructExplicitSequenceValueBoundaryProtected : Bool :=
  let joined := .sequenceConstruct (.capture [.num 1, .num 2]) (.num 3)
  match runResult (.algorithmExpr (alg [] [] [] [joined])),
        KatLang.runEvalM (KatLang.evalCounted joined { callStack := [KatLang.preludeAlg], algEnv := [] } []) with
  | Except.ok (.sequenceValue [.sequenceValue [.atom 1, .atom 2], .atom 3]),
    Except.ok (.sequenceValue [.sequenceValue [.atom 1, .atom 2], .atom 3], 1) => true
  | _, _ => false

#guard sequenceConstructExplicitSequenceValueBoundaryProtected

def sequenceConstructMaterializedCommaRows : Bool :=
  let leftRow := .capture [.num 1, .num 2, .num 3]
  let rightRow := .capture [.num 4, .num 5, .num 6]
  let table := .sequenceConstruct leftRow rightRow
  match runResult (.algorithmExpr (alg [] [] [] [table])),
        KatLang.runEvalM (KatLang.evalCounted table { callStack := [KatLang.preludeAlg], algEnv := [] } []) with
  | Except.ok (.sequenceValue [
      .sequenceValue [.atom 1, .atom 2, .atom 3],
      .sequenceValue [.atom 4, .atom 5, .atom 6]
    ]),
    Except.ok (.sequenceValue [
      .sequenceValue [.atom 1, .atom 2, .atom 3],
      .sequenceValue [.atom 4, .atom 5, .atom 6]
    ], 1) => true
  | _, _ => false

#guard sequenceConstructMaterializedCommaRows

def sequenceConstructNestedAssociativeAtConstructedValueLevel : Bool :=
  let leftNested := .sequenceConstruct (.sequenceConstruct (.num 1) (.num 2)) (.num 3)
  let rightNested := .sequenceConstruct (.num 1) (.sequenceConstruct (.num 2) (.num 3))
  match runResult (.algorithmExpr (alg [] [] [] [leftNested])), runResult (.algorithmExpr (alg [] [] [] [rightNested])) with
  | Except.ok (.sequenceValue [.atom 1, .atom 2, .atom 3]),
    Except.ok (.sequenceValue [.atom 1, .atom 2, .atom 3]) => true
  | _, _ => false

#guard sequenceConstructNestedAssociativeAtConstructedValueLevel

def explicitSequenceValueTripleStaysOneTopLevelValue : Bool :=
  let sequenceValueTriple := .capture [.num 1, .num 2, .num 3]
  let constructedTriple := .sequenceConstruct (.num 1) (.sequenceConstruct (.num 2) (.num 3))
  let sequenceValueCount := .call (.resolve "count") [sequenceValueTriple]
  let constructedCount := .call (.resolve "count") [constructedTriple]
  match runResult (.algorithmExpr (alg [] [] [] [sequenceValueTriple])), runFlat sequenceValueCount, runFlat constructedCount with
  | Except.ok (.sequenceValue [.atom 1, .atom 2, .atom 3]), Except.ok [3], Except.ok [3] => true
  | _, _, _ => false

#guard explicitSequenceValueTripleStaysOneTopLevelValue

def mixedCommaSequenceConstructPreservesRootSlots : Bool :=
  let mixed := alg [] [] [] [.num 1, .sequenceConstruct (.num 2) (.num 3)]
  match runResult (.algorithmExpr mixed) with
  | Except.ok (.sequenceValue [.atom 1, .sequenceValue [.atom 2, .atom 3]]) => true
  | _ => false

#guard mixedCommaSequenceConstructPreservesRootSlots

def sequenceSpreadAfterSequenceConstructMatchesSequenceValueForm : Bool :=
  let concise :=
    sequenceSpread (.sequenceConstruct (.num 1) (.num 2))
  let sequenceValue :=
    sequenceSpread (.capture [.sequenceConstruct (.num 1) (.num 2)])
  match runFlat concise, runFlat sequenceValue with
  | Except.ok [1, 2], Except.ok [1, 2] => true
  | _, _ => false

#guard sequenceSpreadAfterSequenceConstructMatchesSequenceValueForm

-- Single-collecting `X(*values)` collects the supplied argument slots as one exact
-- list: the explicit-spread form `X((1, b)*)` supplies two items
-- (`values = [1, (2, 3)]`, count 2), while the constructed sequence-value form
-- `X((1, b))` supplies ONE grouped argument (`values = [(1, (2, 3))]`,
-- count 1). Exact segment collection removed the old grouped/spread coincidence.
def sequenceSpreadAfterSequenceConstructMatchesConstructedSequenceValue : Bool :=
  let countValues := algWithParameters [{ name := "values", kind := .collecting }] [] [] [
    .dotCall (.param "values") "count" none
  ]
  let multiB := alg [] [] [] [.num 2, .num 3]
  let explicitSpreadForm := algPrivate [] [] [("b", multiB), ("X", countValues)] [
    .call (.resolve "X") [
      sequenceSpread (.sequenceConstruct (.num 1) (.resolve "b"))
    ]
  ]
  let constructedArgForm := algPrivate [] [] [("b", multiB), ("X", countValues)] [
    .call (.resolve "X") [
      .sequenceConstruct (.num 1) (.resolve "b")
    ]
  ]
  let explicitSpreadOk :=
    match runFlat (.algorithmExpr explicitSpreadForm) with
    | Except.ok [2] => true
    | _ => false
  let constructedArgOk :=
    match runFlat (.algorithmExpr constructedArgForm) with
    | Except.ok [1] => true
    | _ => false
  explicitSpreadOk && constructedArgOk

#guard sequenceSpreadAfterSequenceConstructMatchesConstructedSequenceValue

def missingOutputBodyAsResultStillFails : Bool :=
  match runResult (.algorithmExpr (alg [] [] [] [missingOutputBodyExpr])) with
  | Except.error err => innermostIsMissingOutput err
  | Except.ok _ => false

#guard missingOutputBodyAsResultStillFails

def missingOutputBodyCountStillFails : Bool :=
  let dotCount :=
    match runResult (.dotCall missingOutputBodyExpr "count" none) with
    | Except.error err => innermostIsMissingOutput err
    | Except.ok _ => false
  let plainCount :=
    match runResult (.call (.resolve "count") [missingOutputBodyExpr]) with
    | Except.error err => innermostIsMissingOutput err
    | Except.ok _ => false
  dotCount && plainCount

#guard missingOutputBodyCountStillFails

def missingOutputBodyEqualityStillFails : Bool :=
  let leftMissing :=
    match runResult (.binary .eq missingOutputBodyExpr explicitEmptyExpr) with
    | Except.error err => innermostIsMissingOutput err
    | Except.ok _ => false
  let rightMissing :=
    match runResult (.binary .eq explicitEmptyExpr missingOutputBodyExpr) with
    | Except.error err => innermostIsMissingOutput err
    | Except.ok _ => false
  let bothMissing :=
    match runResult (.binary .eq missingOutputBodyExpr missingOutputBodyExpr) with
    | Except.error err => innermostIsMissingOutput err
    | Except.ok _ => false
  leftMissing && rightMissing && bothMissing

#guard missingOutputBodyEqualityStillFails

def missingOutputContainerPropertyStillFails : Bool :=
  let countFails :=
    match runResult (.algorithmExpr (algPrivate [] [] [("Lib", explicitEmptyNoOutputContainer)] [
      .dotCall (.resolve "Lib") "count" none
    ])) with
    | Except.error err => innermostIsMissingOutput err
    | Except.ok _ => false
  let equalityFails :=
    match runResult (.algorithmExpr (algPrivate [] [] [("Lib", explicitEmptyNoOutputContainer)] [
      .binary .eq (.resolve "Lib") explicitEmptyExpr
    ])) with
    | Except.error err => innermostIsMissingOutput err
    | Except.ok _ => false
  countFails && equalityFails

#guard missingOutputContainerPropertyStillFails

--------------------------------------------------------------------------------
-- explicit algorithm params require output
--------------------------------------------------------------------------------

def noOutputHelperContainer : Algorithm :=
  algPrivate [] [] [("Prop", alg [] [] [] [.num 7])] []

def invalidExplicitParamClauseAlg : Algorithm :=
  Algorithm.elaborateClauseDefinition (KatLang.Pattern.bind "x") noOutputHelperContainer

def explicitParamsWithoutOutputRejected : Bool :=
  match KatLang.runEvalM (KatLang.validateExplicitParamOutputInvariant invalidExplicitParamClauseAlg) with
  | Except.error Error.explicitParamsRequireOutput => true
  | _ => false

#guard explicitParamsWithoutOutputRejected

def explicitParamsWithoutOutputRejectedAtRun : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("Algo", invalidExplicitParamClauseAlg)] [.num 0])) with
  | Except.error err => innermostIsExplicitParamsRequireOutput err
  | Except.ok _ => false

#guard explicitParamsWithoutOutputRejectedAtRun

-- The stored Algorithm.mk field is the parameter-pattern LIST: a legal pattern
-- with ZERO captures (sequenceValue []) is still one explicit parameter
-- pattern, so an algorithm carrying it with empty output violates the
-- invariant in both root and property placement. C# twin:
-- ExplicitParameterOutputValidationTests (the C# walker must test the stored
-- ParameterPatterns list, not the flattened capture list).
def zeroCaptureAlg : Algorithm :=
  .mk none [KatLang.ParameterPattern.sequenceValue []] [] [] []

def zeroCapturePatternWithoutOutputRejectedAtRoot : Bool :=
  match runResult (.algorithmExpr zeroCaptureAlg) with
  | Except.error err => innermostIsExplicitParamsRequireOutput err
  | Except.ok _ => false

#guard zeroCapturePatternWithoutOutputRejectedAtRoot

def zeroCapturePatternWithoutOutputRejectedInPropertyPosition : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("G", zeroCaptureAlg)] [.num 7])) with
  | Except.error err => innermostIsExplicitParamsRequireOutput err
  | Except.ok _ => false

#guard zeroCapturePatternWithoutOutputRejectedInPropertyPosition

def parameterizedChildPropertyContainer : Algorithm :=
  algPrivate [] [] [("Prop", alg ["x", "y"] [] [] [.num 7])] []

def parameterizedChildPropertyWithoutOuterParamsStillValid : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("Algo", parameterizedChildPropertyContainer)] [
    .dotCall (.resolve "Algo") "Prop" (some [.num 1, .num 2])
  ])) with
  | Except.ok [7] => true
  | _ => false

#guard parameterizedChildPropertyWithoutOuterParamsStillValid

-- Test 3: Ordinary-dot lexical fallback
-- Receiver has no G, but lexical scope defines G(x) = x * 2
-- Receiver output = 5 → 10
def lexicalGAlg : Algorithm :=
  alg ["x"] [] [] [.binary .mul (.param "x") (.num 2)]

def outer3 : Algorithm :=
  algPrivate [] [] [("G", lexicalGAlg)] [
    .dotCall (.algorithmExpr (alg [] [] [] [.num 5])) "G" none
  ]

def test3 : Bool :=
  match runFlat (.algorithmExpr outer3) with
  | Except.ok [10] => true
  | _ => false

#guard test3
-- EXPECTED: Except.ok [10]
#eval runFlat (.algorithmExpr outer3)

end KatLangTests
