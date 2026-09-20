import KatLang
import CoreTests.Common

namespace KatLangTests
open KatLang (alg algWithParameters algWithParameterPatterns algPrivate privateProp publicProp privateLocalProp publicLocalProp runFlat runResult Algorithm Error Result PropExposure)
open KatLang (resolve param num)
open KatLang (Pattern CondBranch)

--------------------------------------------------------------------------------
-- atoms builtin: recursive list traversal and exact-list results (issue #136)
--------------------------------------------------------------------------------
-- `atoms` materializes ONE list of the recursively collected
-- numeric atoms: sequence AND list boundaries open depth-first, left to right;
-- strings contribute no atoms; the result kind never depends on the input
-- kind, and the emitted count is always 1 (including the empty result `[]`).
-- Truth is Boolean-only (`Result.asBool?` reads no atom view), so none of
-- these guards changes any `if` outcome — see the Boolean condition guards below.

def atomsCallOn (argBody : List KatLang.Expr) : KatLang.Expr :=
  .algorithmExpr (algPrivate [] [] [] [.call (.resolve "atoms") argBody])

def atomsNumberIsSingletonList : Bool :=
  match runCountedProgram (atomsCallOn [.num 7]) with
  | .ok (Result.listValue [Result.atom 7], 1) => true
  | _ => false

#guard atomsNumberIsSingletonList

def atomsStringIsEmptyList : Bool :=
  match runCountedProgram (atomsCallOn [.stringLiteral "text"]) with
  | .ok (Result.listValue [], 1) => true
  | _ => false

#guard atomsStringIsEmptyList

def atomsEmptySequenceIsEmptyList : Bool :=
  match runCountedProgram (atomsCallOn [.emptySequence 0]) with
  | .ok (Result.listValue [], 1) => true
  | _ => false

#guard atomsEmptySequenceIsEmptyList

def atomsEmptyListIsEmptyList : Bool :=
  match runCountedProgram (atomsCallOn [.listLiteral []]) with
  | .ok (Result.listValue [], 1) => true
  | _ => false

#guard atomsEmptyListIsEmptyList

-- atoms([1, 2]) → [1, 2] (lists are traversed, not opaque)
def atomsListTraversalIsExactList : Bool :=
  match runCountedProgram (atomsCallOn [.listLiteral [.num 1, .num 2]]) with
  | .ok (Result.listValue [Result.atom 1, Result.atom 2], 1) => true
  | _ => false

#guard atomsListTraversalIsExactList

-- atoms([[1, 2], [3, 4]]) → [1, 2, 3, 4]
def atomsNestedListsFlatten : Bool :=
  match runCountedProgram (atomsCallOn [.listLiteral [
      .listLiteral [.num 1, .num 2], .listLiteral [.num 3, .num 4]]]) with
  | .ok (Result.listValue [Result.atom 1, Result.atom 2, Result.atom 3, Result.atom 4], 1) => true
  | _ => false

#guard atomsNestedListsFlatten

-- atoms([(1, 2), [3, [4]], 5]) → [1, 2, 3, 4, 5]
def atomsMixedStructuresFlatten : Bool :=
  match runCountedProgram (atomsCallOn [.listLiteral [
      .capture [.num 1, .num 2],
      .listLiteral [.num 3, .listLiteral [.num 4]],
      .num 5]]) with
  | .ok (Result.listValue
      [Result.atom 1, Result.atom 2, Result.atom 3, Result.atom 4, Result.atom 5], 1) => true
  | _ => false

#guard atomsMixedStructuresFlatten

-- atoms([3, (1, [4, 2])]) → [3, 1, 4, 2] (structural left-to-right order)
def atomsPreservesLeftToRightOrder : Bool :=
  match runCountedProgram (atomsCallOn [.listLiteral [
      .num 3,
      .capture [.num 1, .listLiteral [.num 4, .num 2]]]]) with
  | .ok (Result.listValue [Result.atom 3, Result.atom 1, Result.atom 4, Result.atom 2], 1) => true
  | _ => false

#guard atomsPreservesLeftToRightOrder

-- [1, 2, 3].skip(1).atoms → [2, 3] (builtin-produced lists compose directly)
def atomsComposesWithListProducingBuiltins : Bool :=
  match runCountedProgram (.algorithmExpr (algPrivate [] [] []
      [.dotCall (.dotCall (.listLiteral [.num 1, .num 2, .num 3]) "skip"
          (some [.num 1])) "atoms" none])) with
  | .ok (Result.listValue [Result.atom 2, Result.atom 3], 1) => true
  | _ => false

#guard atomsComposesWithListProducingBuiltins

-- The two atom views agree on a list-bearing value (language collection and
-- host flattening both open lists); neither is a truth view — only a Boolean
-- value has a truth value, so `asBool?` is `none` here.
def atomViewSeparationValue : Result :=
  Result.listValue [Result.atom 1, Result.sequenceValue [Result.atom 2], Result.str "s"]

#guard Result.languageAtoms atomViewSeparationValue == [1, 2]
#guard Result.hostAtoms atomViewSeparationValue == [1, 2]
#guard Result.asBool? atomViewSeparationValue == none
-- Booleans are not numeric atoms: every atom view drops them.
#guard Result.languageAtoms (Result.sequenceValue [Result.bool true, Result.atom 3]) == [3]
#guard Result.hostAtoms (Result.listValue [Result.bool false, Result.atom 3]) == [3]

--------------------------------------------------------------------------------
-- Boolean condition guards: `if` requires a Boolean value, never a truth test
--------------------------------------------------------------------------------
-- Lists, numbers, strings, and sequence values have no truth value; only
-- `true` / `false` (possibly under a redundant singleton boundary) select a
-- branch. Every rejection is the ONE value-kind error naming the condition
-- (`booleanRequiredMessage`), never an arity or numeric error.

def truthIfCall (cond : KatLang.Expr) : KatLang.Expr :=
  .call (.resolve "if") [cond, .num 10, .num 20]

def ifConditionRejected (cond : KatLang.Expr) (description : String) : Bool :=
  match runFlat (truthIfCall cond) with
  | Except.error err => innermostIsBooleanRequired "if condition" description err
  | _ => false

#guard ifConditionRejected (.listLiteral [.num 1]) "a list value with 1 element: [1]"
#guard ifConditionRejected (.listLiteral []) "a list value with 0 elements: []"
#guard ifConditionRejected (.listLiteral [.num 0]) "a list value with 1 element: [0]"
#guard ifConditionRejected (.listLiteral [.listLiteral [.num 1]]) "a list value with 1 element: [[1]]"
-- Numbers have NO truth value: neither `1` nor `0` selects a branch.
#guard ifConditionRejected (.num 1) "numeric value 1"
#guard ifConditionRejected (.num 0) "numeric value 0"
#guard ifConditionRejected (.stringLiteral "x") "a string: 'x'"
-- A sequence value is not a Boolean, whatever its first item — no flattening.
#guard ifConditionRejected (.capture [.num 1, .listLiteral [.num 2]])
  "a sequence value with 2 sequence elements: (1, [2])"
#guard ifConditionRejected (.capture [.boolLiteral true, .boolLiteral false])
  "a sequence value with 2 sequence elements: (true, false)"
#guard ifConditionRejected (.emptySequence 0) "a sequence value with 0 sequence elements: ()"
-- if(atoms((1, 2)), 10, 20) is invalid: the atoms result is a list like any other.
#guard ifConditionRejected (.call (.resolve "atoms") [.capture [.num 1, .num 2]])
  "a list value with 2 elements: [1, 2]"

-- Boolean conditions select the branch; a redundant singleton sequence
-- boundary normalizes away exactly as it does for numbers.
def ifSelects (cond : KatLang.Expr) (expected : Int) : Bool :=
  match runFlat (truthIfCall cond) with
  | Except.ok [value] => value == expected
  | _ => false

#guard ifSelects (.boolLiteral true) 10
#guard ifSelects (.boolLiteral false) 20
#guard ifSelects (.capture [.boolLiteral true]) 10
#guard ifSelects (.binary .lt (.num 1) (.num 2)) 10
#guard ifSelects (.binary .eq (.num 1) (.num 2)) 20
#guard ifSelects (.unary .not (.boolLiteral true)) 20
#guard ifSelects (.call (.resolve "contains") [.listLiteral [.num 1, .num 2], .num 2]) 10

--------------------------------------------------------------------------------
-- List values (`[]` syntax)
--------------------------------------------------------------------------------
-- C# parity: tests/KatLang.Tests/ListValueTests.cs. Binder laws:
-- KatLangArityLaws.lean list bridge laws (exact list values are
-- intentionally not modeled in the CoreArityAlgebra paper artifact).

-- `[1, 2, 3]` constructs ONE exact list value.
def listLiteralConstructsExactValue : Bool :=
  match runResult (.algorithmExpr (alg [] [] [] [.listLiteral [.num 1, .num 2, .num 3]])) with
  | Except.ok (Result.listValue [Result.atom 1, Result.atom 2, Result.atom 3]) => true
  | _ => false

#guard listLiteralConstructsExactValue

-- `[]`, `[7]`, and `[[7]]` keep exact cardinality and nesting: no singleton
-- erasure and no empty-nesting collapse applies to list structure.
def listExactnessPreserved : Bool :=
  (match runResult (.algorithmExpr (alg [] [] [] [.listLiteral []])) with
   | Except.ok (Result.listValue []) => true | _ => false) &&
  (match runResult (.algorithmExpr (alg [] [] [] [.listLiteral [.num 7]])) with
   | Except.ok (Result.listValue [Result.atom 7]) => true | _ => false) &&
  (match runResult (.algorithmExpr (alg [] [] [] [.listLiteral [.listLiteral [.num 7]]])) with
   | Except.ok (Result.listValue [Result.listValue [Result.atom 7]]) => true | _ => false)

#guard listExactnessPreserved

-- Equality is structural, recursive, and kind-exact: a list never equals a
-- sequence value or the lone item it contains.
def listEqualityIsKindExact : Bool :=
  evaluatesToBools (.algorithmExpr (alg [] [] [] [
    .binary .eq (.listLiteral [.num 1, .num 2]) (.listLiteral [.num 1, .num 2]),
    .binary .eq (.listLiteral []) (.emptySequence 0),
    .binary .eq (.listLiteral [.num 7]) (.num 7),
    .binary .eq (.listLiteral [.num 1, .num 2]) (.capture [.num 1, .num 2])]))
    [true, false, false, false]

#guard listEqualityIsKindExact

-- Ordinary parentheses stay a redundant SEQUENCE grouping around lists:
-- `([1, 2])` normalizes to the exact list itself.
def redundantParensAroundListCanonicalize : Bool :=
  match runResult (.algorithmExpr (alg [] [] [] [.listLiteral [.num 1, .num 2]])) with
  | Except.ok (Result.listValue [Result.atom 1, Result.atom 2]) => true
  | _ => false

#guard redundantParensAroundListCanonicalize

-- A non-spread `()` element stays one visible list element.
def listKeepsVisibleEmptyElement : Bool :=
  match runResult (.algorithmExpr (alg [] [] [] [.listLiteral [.num 1, .emptySequence 0, .num 2]])) with
  | Except.ok (Result.listValue [Result.atom 1, Result.sequenceValue [], Result.atom 2]) => true
  | _ => false

#guard listKeepsVisibleEmptyElement

-- Spread opens exactly ONE list boundary; capturing the spread yields
-- the canonical sequence of the elements.
def spreadCaptureConvertsListToSequence : Bool :=
  match runResult (.algorithmExpr (algPrivate [] []
    [("A", alg [] [] [] [.listLiteral [.num 1, .num 2, .num 3]]),
     ("B", alg [] [] [] [sequenceSpread (.resolve "A")])]
    [.resolve "B"])) with
  | Except.ok (Result.sequenceValue [Result.atom 1, Result.atom 2, Result.atom 3]) => true
  | _ => false

#guard spreadCaptureConvertsListToSequence

-- Spread edge cases: `[]*` supplies zero items (captures as `()`),
-- `[7]*` supplies the item, `[[7]]*` supplies the inner list intact.
def listSpreadEdgeCasesOpenOneBoundary : Bool :=
  (match runResult (.algorithmExpr (algPrivate [] []
      [("A", alg [] [] [] [.listLiteral []])] [sequenceSpread (.resolve "A")])) with
   | Except.ok (Result.sequenceValue []) => true | _ => false) &&
  (match runResult (.algorithmExpr (algPrivate [] []
      [("A", alg [] [] [] [.listLiteral [.num 7]])] [sequenceSpread (.resolve "A")])) with
   | Except.ok (Result.atom 7) => true | _ => false) &&
  (match runResult (.algorithmExpr (algPrivate [] []
      [("A", alg [] [] [] [.listLiteral [.listLiteral [.num 7]]])] [sequenceSpread (.resolve "A")])) with
   | Except.ok (Result.listValue [Result.atom 7]) => true | _ => false)

#guard listSpreadEdgeCasesOpenOneBoundary

-- List-literal elements use the ordinary expression-list model: spread
-- elements insert their item supply into the constructed list.
def listLiteralSpreadElements : Bool :=
  match runResult (.algorithmExpr (algPrivate [] []
    [("A", alg [] [] [] [.num 1, .num 2, .num 3])]
    [.listLiteral [.num 0, sequenceSpread (.resolve "A"), .num 4]])) with
  | Except.ok (Result.listValue
      [Result.atom 0, Result.atom 1, Result.atom 2, Result.atom 3, Result.atom 4]) => true
  | _ => false

#guard listLiteralSpreadElements

-- Empty spreads contribute no elements; a NON-spread `[]` stays one element.
def emptyListSpreadIsNeutralInListLiteral : Bool :=
  (match runResult (.algorithmExpr (alg [] [] []
      [.listLiteral [.num 1, sequenceSpread (.listLiteral []), .num 2]])) with
   | Except.ok (Result.listValue [Result.atom 1, Result.atom 2]) => true | _ => false) &&
  (match runResult (.algorithmExpr (alg [] [] []
      [.listLiteral [.num 1, .listLiteral [], .num 2]])) with
   | Except.ok (Result.listValue [Result.atom 1, Result.listValue [], Result.atom 2]) => true
   | _ => false)

#guard emptyListSpreadIsNeutralInListLiteral

-- Calls preserve list boundaries: a list without spread is ONE argument.
def callPreservesListBoundary : Bool :=
  match runResult (.algorithmExpr (algPrivate [] []
    [("F", alg ["a"] [] [] [.param "a"]),
     ("A", alg [] [] [] [.listLiteral [.num 1, .num 2]])]
    [.call (.resolve "F") [.resolve "A"]])) with
  | Except.ok (Result.listValue [Result.atom 1, Result.atom 2]) => true
  | _ => false

#guard callPreservesListBoundary

-- Explicit spread supplies the elements as separate arguments.
def spreadOpensListIntoCallArguments : Bool :=
  expectFlat (runFlat (.algorithmExpr (algPrivate [] []
    [("F", alg ["a", "b", "c"] [] []
        [.binary .add (.binary .add (.param "a") (.param "b")) (.param "c")]),
     ("A", alg [] [] [] [.listLiteral [.num 1, .num 2, .num 3]])]
    [.call (.resolve "F") [sequenceSpread (.resolve "A")]]))) [6]

#guard spreadOpensListIntoCallArguments

-- A fixed-arity callee rejects an unspread list (calls never open lists).
-- The list behaves exactly like any other single non-openable argument
-- (scalar, string): the Lean final-arg binding path reports the remaining
-- parameter/argument counts after the first binding step (`2 0`), a
-- pre-existing payload shape shared by `F(5)` and `F('xy')`; the C# runtime
-- reports the full signature counts (`3 1`). Both are category `arity`.
def callDoesNotImplicitlyOpenList : Bool :=
  expectInnermostArityMismatch 2 0 (runFlat (.algorithmExpr (algPrivate [] []
    [("F", alg ["a", "b", "c"] [] []
        [.binary .add (.binary .add (.param "a") (.param "b")) (.param "c")]),
     ("A", alg [] [] [] [.listLiteral [.num 1, .num 2, .num 3]])]
    [.call (.resolve "F") [.resolve "A"]])))

#guard callDoesNotImplicitlyOpenList

-- Mixed fixed/variadic call: a lone list argument stays whole — `first` receives
-- the entire list, `rest` captures nothing.
def mixedVariadicCallKeepsLoneListWhole : Bool :=
  match runResult (.algorithmExpr (algPrivate [] []
    [("F", algWithParameters [{ name := "first" }, { name := "rest", kind := .collecting }] [] []
        [.param "first"]),
     ("A", alg [] [] [] [.listLiteral [.num 1, .num 2]])]
    [.call (.resolve "F") [.resolve "A"]])) with
  | Except.ok (Result.listValue [Result.atom 1, Result.atom 2]) => true
  | _ => false

#guard mixedVariadicCallKeepsLoneListWhole

-- Deconstruction (the sequence-value parameter pattern) opens a lone LIST
-- exactly like a lone sequence value: `x, y, z = [1, 2, 3]` binds elementwise.
def deconstructionOpensLoneList : Bool :=
  let helper := KatLang.Expr.algorithmExpr (algWithParameterPatterns
    [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }, .capture { name := "z" }]]
    [] [] [.param "y"])
  expectFlat (runFlat (.algorithmExpr (algPrivate [] []
    [("d", alg [] [] [] [.listLiteral [.num 1, .num 2, .num 3]])]
    [.call helper [.resolve "d"]]))) [2]

#guard deconstructionOpensLoneList

-- Collecting binding in deconstruction COLLECTS the remaining items as one exact
-- immutable list: `x, *rest = [1, 2, 3]` binds `rest = [2, 3]`.
def listCollectingCaptureCollectsExactList : Bool :=
  let helper := KatLang.Expr.algorithmExpr (algWithParameterPatterns
    [.sequenceValue [.capture { name := "x" }, .capture { name := "rest", kind := .collecting }]]
    [] [] [.param "rest"])
  match runResult (.algorithmExpr (algPrivate [] []
    [("d", alg [] [] [] [.listLiteral [.num 1, .num 2, .num 3]])]
    [.call helper [.resolve "d"]])) with
  | Except.ok (Result.listValue [Result.atom 2, Result.atom 3]) => true
  | _ => false

#guard listCollectingCaptureCollectsExactList

-- Deconstruction opens only the OUTER lone structure: nested lists stay whole.
def deconstructionDoesNotOpenListRecursively : Bool :=
  let helper := KatLang.Expr.algorithmExpr (algWithParameterPatterns
    [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]]
    [] [] [.param "x"])
  match runResult (.algorithmExpr (algPrivate [] []
    [("d", alg [] [] [] [.listLiteral [.listLiteral [.num 1, .num 2], .num 3]])]
    [.call helper [.resolve "d"]])) with
  | Except.ok (Result.listValue [Result.atom 1, Result.atom 2]) => true
  | _ => false

#guard deconstructionDoesNotOpenListRecursively

-- The builtin collection view opens a lone list like a lone sequence value:
-- the shared collection-item view opens ONE outer sequence or list boundary,
-- so `count([1, 2, 3])` counts three items.
def builtinLoneListCollectionOpens : Bool :=
  expectFlat (runFlat (.algorithmExpr (alg [] [] []
    [.call (.resolve "count") [.listLiteral [.num 1, .num 2, .num 3]]])))
    [3]

#guard builtinLoneListCollectionOpens

-- Opening is never recursive: two sibling lists grouped into ONE collection
-- argument are two items (`count(([], []))` is 2), the ungrouped `count([], [])`
-- is a two-argument arity error, and a nested list inside an opened lone list
-- stays one opaque item (`count([1, [2], 3])` is 3).
def builtinSiblingListsCountAsItems : Bool :=
  expectFlat (runFlat (.algorithmExpr (alg [] [] []
    [.call (.resolve "count") [.capture [.listLiteral [], .listLiteral []]]])))
    [2] &&
  (match runResult (.algorithmExpr (alg [] [] []
    [.call (.resolve "count") [.listLiteral [], .listLiteral []]])) with
   | Except.error err => innermostIsArityMismatch 1 2 err
   | _ => false)

#guard builtinSiblingListsCountAsItems

def builtinNestedListStaysOneItem : Bool :=
  expectFlat (runFlat (.algorithmExpr (alg [] [] []
    [.call (.resolve "count") [.listLiteral [.num 1, .listLiteral [.num 2], .num 3]]])))
    [3]

#guard builtinNestedListStaysOneItem

-- Spread keeps only its ordinary meaning at builtin calls: `count([1, 2, 3]*)`
-- opens the list into THREE ordinary argument slots, an arity error under
-- `count(collection)` (same for sum). Grouping the spread back into one
-- argument is the rewrite idiom: `count(([1, 2, 3]*))` is 3, and the
-- unspread `count([1, 2, 3])` stays the direct form (see
-- builtinLoneListCollectionOpens above).
def builtinSpreadListFollowsFixedArity : Bool :=
  (match runResult (.algorithmExpr (alg [] [] []
    [.call (.resolve "count") [sequenceSpread (.listLiteral [.num 1, .num 2, .num 3])]])) with
   | Except.error err => innermostIsArityMismatch 1 3 err
   | _ => false) &&
  (match runResult (.algorithmExpr (alg [] [] []
    [.call (.resolve "sum") [sequenceSpread (.listLiteral [.num 1, .num 2, .num 3])]])) with
   | Except.error err => innermostIsArityMismatch 1 3 err
   | _ => false) &&
  expectFlat (runFlat (.algorithmExpr (alg [] [] []
    [.call (.resolve "count") [.capture [sequenceSpread (.listLiteral [.num 1, .num 2, .num 3])]]]))) [3]

#guard builtinSpreadListFollowsFixedArity

-- Indexing returns the selected element exactly as stored: selecting a list
-- ITEM from a sequence preserves the list (projection does not erase
-- listness).
def indexingPreservesSelectedList : Bool :=
  match runResult (.algorithmExpr (algPrivate [] []
    [("A", alg [] [] [] [.capture [.num 0, .listLiteral [.num 1, .num 2]]])]
    [.index (.resolve "A") (.num 1)])) with
  | Except.ok (Result.listValue [Result.atom 1, Result.atom 2]) => true
  | _ => false

#guard indexingPreservesSelectedList

-- Indexing `:` opens a LIST TARGET to its immediate elements exactly like a
-- sequence target (`Result.projectionItems`): `[1, 2, 3]:0` is `1`, `[7]:0`
-- is `7`, and the selected element keeps its exact kind.
def listIndexingSelectsElement : Bool :=
  (match runResult (.algorithmExpr (alg [] [] []
      [.index (.listLiteral [.num 1, .num 2, .num 3]) (.num 0)])) with
   | Except.ok (Result.atom 1) => true | _ => false) &&
  (match runResult (.algorithmExpr (alg [] [] []
      [.index (.listLiteral [.num 1, .num 2, .num 3]) (.num 1)])) with
   | Except.ok (Result.atom 2) => true | _ => false) &&
  (match runResult (.algorithmExpr (alg [] [] []
      [.index (.listLiteral [.num 1, .num 2, .num 3]) (.num 2)])) with
   | Except.ok (Result.atom 3) => true | _ => false) &&
  (match runResult (.algorithmExpr (alg [] [] []
      [.index (.listLiteral [.num 7]) (.num 0)])) with
   | Except.ok (Result.atom 7) => true | _ => false)

#guard listIndexingSelectsElement

-- A selected LIST element stays one exact opaque list (no flattening, no
-- sequence conversion): `[[1, 2], [3, 4]]:0` is `[1, 2]` and `[[]]:0` is `[]`.
def listIndexingNestedElementStaysList : Bool :=
  (match runResult (.algorithmExpr (alg [] [] []
      [.index (.listLiteral
        [.listLiteral [.num 1, .num 2], .listLiteral [.num 3, .num 4]]) (.num 0)])) with
   | Except.ok (Result.listValue [Result.atom 1, Result.atom 2]) => true | _ => false) &&
  (match runResult (.algorithmExpr (alg [] [] []
      [.index (.listLiteral [.listLiteral []]) (.num 0)])) with
   | Except.ok (Result.listValue []) => true | _ => false)

#guard listIndexingNestedElementStaysList

-- Chained projection peels one boundary per `:`: `[[1, 2], [3, 4]]:1:0` is `3`.
def listIndexingChainedSelectsOneLevelAtATime : Bool :=
  match runResult (.algorithmExpr (alg [] [] []
    [.index (.index (.listLiteral
      [.listLiteral [.num 1, .num 2], .listLiteral [.num 3, .num 4]]) (.num 1)) (.num 0)])) with
  | Except.ok (Result.atom 3) => true
  | _ => false

#guard listIndexingChainedSelectsOneLevelAtATime

-- A selected SEQUENCE element inside a list projects one level with its item
-- count, exactly like the sequence-target twin; a selected `()` element stays
-- one visible empty row at root.
def listIndexingSequenceElementProjectsCounted : Bool :=
  (match runCountedProgram (.algorithmExpr (alg [] [] []
      [.index (.listLiteral
        [.capture [.num 1, .num 2],
         .capture [.num 3, .num 4]]) (.num 0)])) with
   | .ok (Result.sequenceValue [Result.atom 1, Result.atom 2], 2) => true | _ => false) &&
  (match runCountedProgram (.algorithmExpr (alg [] [] []
      [.index (.listLiteral [.emptySequence 0]) (.num 0)])) with
   | .ok (Result.sequenceValue [], 1) => true | _ => false)

#guard listIndexingSequenceElementProjectsCounted

-- Empty and out-of-range list projection is the existing out-of-range
-- projection error: `[]:0`, `[1, 2]:2`, and `[1, 2]:100` are badIndex, and a
-- negative selector stays badIndex for list targets too. A selector beyond
-- the C# host int range (3000000000) is an ordinary out-of-range badIndex in
-- the unbounded-Int model — the twin of the C# int-cast guard — for both
-- target kinds.
def listIndexingOutOfRangeIsBadIndex : Bool :=
  (match runResult (.algorithmExpr (alg [] [] []
      [.index (.listLiteral []) (.num 0)])) with
   | Except.error err => innermostIsBadIndex err | _ => false) &&
  (match runResult (.algorithmExpr (alg [] [] []
      [.index (.listLiteral [.num 1, .num 2]) (.num 2)])) with
   | Except.error err => innermostIsBadIndex err | _ => false) &&
  (match runResult (.algorithmExpr (alg [] [] []
      [.index (.listLiteral [.num 1, .num 2]) (.num 100)])) with
   | Except.error err => innermostIsBadIndex err | _ => false) &&
  (match runResult (.algorithmExpr (alg [] [] []
      [.index (.listLiteral [.num 1, .num 2]) (.num (-1))])) with
   | Except.error err => innermostIsBadIndex err | _ => false) &&
  (match runResult (.algorithmExpr (alg [] [] []
      [.index (.listLiteral [.num 1, .num 2, .num 3]) (.num 3000000000)])) with
   | Except.error err => innermostIsBadIndex err | _ => false) &&
  (match runResult (.algorithmExpr (alg [] [] []
      [.index (.capture [.num 1, .num 2, .num 3]) (.num 3000000000)])) with
   | Except.error err => innermostIsBadIndex err | _ => false)

#guard listIndexingOutOfRangeIsBadIndex

-- Selector validation is unchanged by list targets: a list-valued selector
-- never coerces to a number (badArity), and a string selector stays the
-- string type mismatch — identical to sequence targets.
def listIndexingSelectorValidationUnchanged : Bool :=
  (match runResult (.algorithmExpr (alg [] [] []
      [.index (.listLiteral [.num 1, .num 2]) (.listLiteral [.num 0])])) with
   | Except.error err => innermostIsBadArity err | _ => false) &&
  (match runResult (.algorithmExpr (alg [] [] []
      [.index (.listLiteral [.num 1, .num 2]) (.stringLiteral "0")])) with
   | Except.error err => innermostIsTypeMismatch "Expected a number, got a string" err | _ => false)

#guard listIndexingSelectorValidationUnchanged

-- Diagnostic expression names use KatLang SOURCE syntax: an index renders as
-- `target:selector`, never `target[selector]` (`[...]` is exact list literal
-- syntax, so `Rows[0]` would be a missing-separator error, never an index).
-- These pin the exact text C# produces; C#:
-- `Eval_Index_DiagnosticName_RendersSourceFaithfulColonSyntax` and
-- `Eval_Index_ChainedDiagnosticName_RendersEachSelector`.
def indexDiagnosticNameIsSourceFaithful : Bool :=
  (KatLang.exprDiagnosticName (.index (.resolve "Rows") (.num 0)) == "Rows:0") &&
  -- Chained projection is left-associative, so each selector renders in turn
  -- and the target needs no parentheses.
  (KatLang.exprDiagnosticName (.index (.index (.resolve "Rows") (.num 0)) (.num 1)) == "Rows:0:1") &&
  -- The renderer is syntax-based, so a list target renders the same way.
  (KatLang.exprDiagnosticName (.index (.listLiteral [.num 1, .num 2]) (.num 0)) == "[1, 2]:0")

#guard indexDiagnosticNameIsSourceFaithful

-- Operands that would rebind under the real precedence are parenthesized.
-- C#: `Eval_Index_DiagnosticName_ParenthesizesOperandsThatWouldRebind`.
def indexDiagnosticNameParenthesizesRebindingOperands : Bool :=
  -- Indexing binds tighter than unary and every binary operator.
  (KatLang.exprDiagnosticName (.index (.binary .add (.resolve "A") (.resolve "B")) (.num 0))
    == "(A + B):0") &&
  (KatLang.exprDiagnosticName (.index (.unary .minus (.resolve "A")) (.num 0)) == "(-A):0") &&
  (KatLang.exprDiagnosticName (.index (.resolve "Rows") (.binary .add (.resolve "i") (.num 1)))
    == "Rows:(i + 1)") &&
  -- The selector is a primary in source syntax, so anything that would continue
  -- the postfix chain (`.`, `:`, a call) rebinds to the target without parens.
  (KatLang.exprDiagnosticName (.index (.resolve "A") (.dotCall (.resolve "B") "C" none)) == "A:(B.C)") &&
  (KatLang.exprDiagnosticName (.index (.resolve "A") (.index (.resolve "B") (.resolve "C")))
    == "A:(B:C)") &&
  (KatLang.exprDiagnosticName (.index (.resolve "A") (.call (.resolve "f") [.num 0]))
    == "A:(f(...))") &&
  -- A bare negative literal is not selector syntax at all (`A:-1` is a parse
  -- error), so it keeps parentheses.
  (KatLang.exprDiagnosticName (.index (.resolve "A") (.num (-1))) == "A:(-1)")

#guard indexDiagnosticNameParenthesizesRebindingOperands

-- C#: `Eval_Spread_DiagnosticName_ParenthesizesOperandsThatWouldRebind`.
def spreadDiagnosticNameParenthesizesRebindingOperands : Bool :=
  (KatLang.exprDiagnosticName
      (.sequenceSpread (.unary .minus (.resolve "A"))) == "(-A)*") &&
  (KatLang.exprDiagnosticName
      (.sequenceSpread (.binary .add (.resolve "A") (.resolve "B"))) == "(A + B)*") &&
  (KatLang.exprDiagnosticName
      (.sequenceSpread (.sequenceSpread (.resolve "A"))) == "A**")

#guard spreadDiagnosticNameParenthesizesRebindingOperands

-- `^` binds tighter than prefix unary on the LEFT, so a unary or
-- negative-literal power BASE keeps parentheses, while the exponent side is
-- the unary level and renders bare. A bare unary over a power now reads back
-- correctly (`-a ^ b` IS `-(a ^ b)`), so the unary arm needs no wrapping.
-- C#: `Golden_PowerBaseParenthesization_RendersExactly`.
def powerBaseDiagnosticNameParenthesizesRebindingBases : Bool :=
  (KatLang.exprDiagnosticName (.binary .pow (.unary .minus (.resolve "a")) (.resolve "b"))
    == "(-a) ^ b") &&
  (KatLang.exprDiagnosticName (.binary .pow (.unary .not (.resolve "a")) (.resolve "b"))
    == "(not a) ^ b") &&
  (KatLang.exprDiagnosticName (.binary .pow (.num (-2)) (.resolve "b")) == "(-2) ^ b") &&
  -- Exponent side: unary and negative-literal exponents render bare.
  (KatLang.exprDiagnosticName (.binary .pow (.resolve "a") (.unary .minus (.resolve "b")))
    == "a ^ -b") &&
  (KatLang.exprDiagnosticName (.binary .pow (.resolve "a") (.num (-2))) == "a ^ -2") &&
  -- Non-rebinding bases render as before.
  (KatLang.exprDiagnosticName (.binary .pow (.num 2) (.resolve "b")) == "2 ^ b") &&
  -- Unary over a power renders bare and reads back with the same grouping.
  (KatLang.exprDiagnosticName (.unary .minus (.binary .pow (.resolve "a") (.resolve "b")))
    == "-a ^ b") &&
  -- The right-associative chain reads back identically bare.
  (KatLang.exprDiagnosticName
      (.binary .pow (.num 2) (.binary .pow (.num 3) (.num 2))) == "2 ^ 3 ^ 2") &&
  -- The standalone binary-name entry point shares the same arm.
  (KatLang.binaryExprDiagnosticName .pow (.unary .minus (.resolve "a")) (.resolve "b")
    == "(-a) ^ b") &&
  (KatLang.binaryExprDiagnosticName .pow (.num (-2)) (.resolve "b") == "(-2) ^ b") &&
  (KatLang.binaryExprDiagnosticName .add (.unary .minus (.resolve "a")) (.resolve "b")
    == "-a + b")

#guard powerBaseDiagnosticNameParenthesizesRebindingBases

-- Under `not`-below-comparisons precedence (comparisons > not > and > xor >
-- or), a `not` operand of any tighter operator keeps parentheses on either
-- side, a `not` operand of a logical operator renders bare, a negated
-- comparison renders bare (it reads back as the same tree), a negated logical
-- binary keeps parentheses, and a `not` under prefix `-` keeps parentheses
-- (bare `-not a` is not an operand at all). C# twin:
-- `ExprNameRendererTests.Golden_NotOperandParenthesization_RendersExactly`.
def notOperandDiagnosticNameParenthesizesRebindingOperands : Bool :=
  (KatLang.exprDiagnosticName (.binary .eq (.unary .not (.resolve "a")) (.resolve "b"))
    == "(not a) == b") &&
  (KatLang.exprDiagnosticName (.binary .eq (.resolve "a") (.unary .not (.resolve "b")))
    == "a == (not b)") &&
  (KatLang.exprDiagnosticName (.binary .gt (.unary .not (.resolve "a")) (.resolve "b"))
    == "(not a) > b") &&
  (KatLang.exprDiagnosticName (.binary .add (.unary .not (.resolve "a")) (.resolve "b"))
    == "(not a) + b") &&
  (KatLang.exprDiagnosticName (.binary .mul (.resolve "a") (.unary .not (.resolve "b")))
    == "a * (not b)") &&
  (KatLang.exprDiagnosticName (.binary .pow (.resolve "a") (.unary .not (.resolve "b")))
    == "a ^ (not b)") &&
  (KatLang.exprDiagnosticName (.binary .and (.unary .not (.resolve "a")) (.resolve "b"))
    == "not a and b") &&
  (KatLang.exprDiagnosticName (.binary .or (.resolve "a") (.unary .not (.resolve "b")))
    == "a or not b") &&
  (KatLang.exprDiagnosticName (.binary .xor (.unary .not (.resolve "a")) (.resolve "b"))
    == "not a xor b") &&
  (KatLang.exprDiagnosticName (.unary .not (.binary .gt (.resolve "a") (.resolve "b")))
    == "not a > b") &&
  (KatLang.exprDiagnosticName (.unary .not (.binary .and (.resolve "a") (.resolve "b")))
    == "not (a and b)") &&
  (KatLang.exprDiagnosticName (.unary .minus (.unary .not (.resolve "a")))
    == "-(not a)") &&
  (KatLang.exprDiagnosticName (.unary .not (.unary .not (.resolve "a")))
    == "not not a") &&
  (KatLang.binaryExprDiagnosticName .eq (.unary .not (.resolve "a")) (.resolve "b")
    == "(not a) == b")

#guard notOperandDiagnosticNameParenthesizesRebindingOperands

-- `openExprName` renders an index with source-faithful `:` rather than falling
-- back to the generic `(index)` kind word. Leaf kinds this minimal renderer
-- does not model still print as `(kind)` — a PRE-EXISTING divergence from C#'s
-- merged `OpenExprName`, uniform across `.dotCall`, `.sequenceSpread`, and
-- `.index` alike, and independent of indexing.
def openExprNameRendersIndexSourceFaithfully : Bool :=
  (KatLang.openExprName (.index (.resolve "Rows") (.resolve "i")) == "Rows:i") &&
  (KatLang.openExprName (.index (.index (.resolve "Rows") (.resolve "i")) (.resolve "j"))
    == "Rows:i:j") &&
  -- A selector this renderer prints BARE and that would continue the postfix
  -- chain is still parenthesized.
  (KatLang.openExprName (.index (.resolve "A") (.dotCall (.resolve "B") "C" none)) == "A:(B.C)") &&
  (KatLang.openExprName (.index (.resolve "A") (.index (.resolve "B") (.resolve "C")))
    == "A:(B:C)") &&
  -- Unmodelled leaf: the `(num)` fallback, not `(index)`.
  (KatLang.openExprName (.index (.resolve "Rows") (.num 0)) == "Rows:(num)") &&
  -- An unmodelled kind is ALREADY self-delimiting as `(kind)`, so it must not
  -- be parenthesized a second time into `A:((binary))`.
  (KatLang.openExprName (.index (.resolve "A") (.binary .add (.resolve "i") (.num 1)))
    == "A:(binary)") &&
  (KatLang.openExprName (.index (.resolve "A") (.num (-1))) == "A:(num)")

#guard openExprNameRendersIndexSourceFaithfully

-- Collection-producing builtin results are directly indexable:
-- `range(1, 3):2` is `3` and `[3, 1, 2].order:0` is `1`.
def listIndexingBuiltinResultsDirectlyIndexable : Bool :=
  (match runResult (.algorithmExpr (alg [] [] []
      [.index (.call (.resolve "range") [.num 1, .num 3]) (.num 2)])) with
   | Except.ok (Result.atom 3) => true | _ => false) &&
  (match runResult (.algorithmExpr (alg [] [] []
      [.index (.dotCall (.listLiteral [.num 3, .num 1, .num 2]) "order" none) (.num 0)])) with
   | Except.ok (Result.atom 1) => true | _ => false) &&
  (match runResult (.algorithmExpr (alg [] [] []
      [.index (.call (.resolve "take") [.listLiteral [.num 1, .num 2, .num 3], .num 2]) (.num 1)])) with
   | Except.ok (Result.atom 2) => true | _ => false)

#guard listIndexingBuiltinResultsDirectlyIndexable

-- Stacked spread is compositional: `A**` agrees with the value-boundary-
-- separated form `(A*)*` — each extra star spreads the value the previous
-- star's supply re-captures at the ordinary expression boundary. A LONE
-- structured item singleton-collapses at that capture, so a singleton-list
-- chain opens one more list boundary per written star, while a multi-item
-- supply is a fixed point (see the dedicated guards below).
def stackedSpreadAgreesWithGroupedCompositionalForm : Bool :=
  (match runResult (.algorithmExpr (algPrivate [] []
      [("A", alg [] [] [] [.listLiteral [.listLiteral [.num 7]]])]
      [.sequenceSpread (.sequenceSpread (.resolve "A"))])) with
   | Except.ok (Result.atom 7) => true | _ => false) &&
  (match runResult (.algorithmExpr (algPrivate [] []
      [("A", alg [] [] [] [.listLiteral [.listLiteral [.num 1, .num 2]]])]
      [.sequenceSpread (.sequenceSpread (.resolve "A"))])) with
   | Except.ok (Result.sequenceValue [Result.atom 1, Result.atom 2]) => true | _ => false) &&
  (match runResult (.algorithmExpr (algPrivate [] []
      [("A", alg [] [] [] [.capture [.num 1, .num 2]])]
      [.sequenceSpread (.sequenceSpread (.resolve "A"))])) with
   | Except.ok (Result.sequenceValue [Result.atom 1, Result.atom 2]) => true | _ => false)

#guard stackedSpreadAgreesWithGroupedCompositionalForm

-- The multi-item fixed point, asserted as DIRECT equality between the
-- stacked spelling `A**` and the grouped spelling `(A*)*` (`.capture` is the
-- written-parentheses boundary), plus the pinned value: the two inner lists
-- survive unopened. This guard is what stops a future refactor from
-- replacing capture-law composition with a concatMap-style per-item lift,
-- which would flatten to S[1, 2, 3, 4] here.
def stackedSpreadMultiItemFixedPoint : Bool :=
  let multiA : KatLang.Expr -> KatLang.Expr := fun output =>
    .algorithmExpr (algPrivate [] []
      [("A", alg [] [] [] [.listLiteral
        [.listLiteral [.num 1, .num 2], .listLiteral [.num 3, .num 4]]])]
      [output])
  let stacked := runResult (multiA (.sequenceSpread (.sequenceSpread (.resolve "A"))))
  let grouped := runResult (multiA
    (.sequenceSpread (.capture [.sequenceSpread (.resolve "A")])))
  match stacked, grouped with
  | Except.ok s, Except.ok g =>
      s == g &&
      s == Result.sequenceValue
        [Result.listValue [Result.atom 1, Result.atom 2],
         Result.listValue [Result.atom 3, Result.atom 4]]
  | _, _ => false

#guard stackedSpreadMultiItemFixedPoint

-- A MIXED multi-item supply stays a fixed point too: the second star
-- re-spreads the captured pair; it does not selectively open the structured
-- member.
def stackedSpreadMixedSupplyStaysUnopened : Bool :=
  match runResult (.algorithmExpr (algPrivate [] []
      [("A", alg [] [] [] [.listLiteral [.listLiteral [.num 1, .num 2], .num 3]])]
      [.sequenceSpread (.sequenceSpread (.resolve "A"))])) with
  | Except.ok r =>
      r == Result.sequenceValue [Result.listValue [Result.atom 1, Result.atom 2], Result.atom 3]
  | _ => false

#guard stackedSpreadMixedSupplyStaysUnopened

end KatLangTests
