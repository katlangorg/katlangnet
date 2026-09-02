import KatLang
import CoreTests.Common

namespace KatLangTests
open KatLang (alg algWithParameters algWithParameterPatterns algPrivate privateProp publicProp privateLocalProp publicLocalProp runFlat runResult Algorithm Error Result PropExposure)
open KatLang (resolve param num)
open KatLang (Pattern CondBranch)

--------------------------------------------------------------------------------
-- property/call/builtin boundary arity = 1 (reCountValueBoundary)
--------------------------------------------------------------------------------
-- A property/call/builtin RESULT boundary always returns ONE value: a body or
-- collection that internally produces an item supply is observed by the caller
-- as one sequence value (emitted count 1). Only an explicit caller-site
-- `value*` slot re-spreads it. Root output is NOT a call
-- boundary and keeps its slot count;
-- `while`/`repeat` loop state and the strict map/reduce callback paths are also
-- unchanged. These guards pin the emitted count exactly. Lean: reCountValueBoundary.

/-- `F(*a) = a` then `F(5, 9)`. -/
def boundaryVariadicReturnAlg : Algorithm :=
  algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"]

def boundaryVariadicReturnRoot (body : List KatLang.Expr) : Algorithm :=
  algPrivate [] [] [("F", algWithParameters [{ name := "a", kind := .collecting }] [] [] body)]
    [.call (.resolve "F") [.num 5, .num 9]]

def boundaryVariadicReturnIsOneValue : Bool :=
  match runCountedProgram (.algorithmExpr (boundaryVariadicReturnRoot [.param "a"])) with
  | .ok (Result.listValue [Result.atom 5, Result.atom 9], 1) => true
  | _ => false

#guard boundaryVariadicReturnIsOneValue

/-- `F(*a) = a*` then `F(5, 9)` -- the body spread opens the capture, but the
    call boundary still returns one value. -/
def boundaryVariadicBodySpreadIsOneValue : Bool :=
  match runCountedProgram (.algorithmExpr (boundaryVariadicReturnRoot [sequenceSpread (.param "a")])) with
  | .ok (Result.sequenceValue [Result.atom 5, Result.atom 9], 1) => true
  | _ => false

#guard boundaryVariadicBodySpreadIsOneValue

/-- `F(*a) = a, 0` then `F(5, 9)` -- the collected list stays one nested list value. -/
def boundaryVariadicCommaSlotGroupsCapture : Bool :=
  match runCountedProgram (.algorithmExpr (boundaryVariadicReturnRoot [.param "a", .num 0])) with
  | .ok (Result.sequenceValue [Result.listValue [Result.atom 5, Result.atom 9], Result.atom 0], 1) => true
  | _ => false

#guard boundaryVariadicCommaSlotGroupsCapture

/-- `F(*a) = a*, 0` then `F(5, 9)` -- body spread flattens, boundary still one value. -/
def boundaryVariadicBodySpreadThenSlotIsOneFlatValue : Bool :=
  match runCountedProgram (.algorithmExpr (boundaryVariadicReturnRoot [sequenceSpread (.param "a"), .num 0])) with
  | .ok (Result.sequenceValue [Result.atom 5, Result.atom 9, Result.atom 0], 1) => true
  | _ => false

#guard boundaryVariadicBodySpreadThenSlotIsOneFlatValue

/-- `F(*a) = a` then `F(5, 9)*` -- caller-site spread turns the returned value back into an item supply. -/
def boundaryCallerSpreadOpensReturnedValue : Bool :=
  match runCountedProgram (.algorithmExpr (algPrivate [] [] [("F", boundaryVariadicReturnAlg)]
      [sequenceSpread (.call (.resolve "F") [.num 5, .num 9])])) with
  | .ok (Result.sequenceValue [Result.atom 5, Result.atom 9], 2) => true
  | _ => false

#guard boundaryCallerSpreadOpensReturnedValue

/-- `X = 1, 2, 3` accessed three ways: lexical `X`, explicit call `X()`, and the
    multi-output property body. -/
def boundaryMultiOutputProp : Algorithm := alg [] [] [] [.num 1, .num 2, .num 3]

def boundaryLexicalAccessIsOneValue : Bool :=
  match runCountedProgram (.algorithmExpr (algPrivate [] [] [("X", boundaryMultiOutputProp)] [.resolve "X"])) with
  | .ok (Result.sequenceValue [Result.atom 1, Result.atom 2, Result.atom 3], 1) => true
  | _ => false

#guard boundaryLexicalAccessIsOneValue

def boundaryExplicitZeroArgCallIsOneValue : Bool :=
  match runCountedProgram (.algorithmExpr (algPrivate [] [] [("X", boundaryMultiOutputProp)]
      [.call (.resolve "X") []])) with
  | .ok (Result.sequenceValue [Result.atom 1, Result.atom 2, Result.atom 3], 1) => true
  | _ => false

#guard boundaryExplicitZeroArgCallIsOneValue

/-- Structural dot zero-arg access `M.P` now matches lexical access (count 1). -/
def boundaryStructuralHolder : Algorithm :=
  alg [] [] [publicProp "P" boundaryMultiOutputProp] [.num 0]

def boundaryStructuralDotAccessIsOneValue : Bool :=
  match runCountedProgram (.algorithmExpr (algPrivate [] [] [("M", boundaryStructuralHolder)]
      [.dotCall (.resolve "M") "P" none])) with
  | .ok (Result.sequenceValue [Result.atom 1, Result.atom 2, Result.atom 3], 1) => true
  | _ => false

#guard boundaryStructuralDotAccessIsOneValue

/-- Collection-producing builtin `order` returns one exact list value; spread
    opens it. -/
def boundaryOrderIsOneValue : Bool :=
  match runCountedProgram (.algorithmExpr (algPrivate [] [] [("X", alg [] [] [] [.num 3, .num 1, .num 2])]
      [.dotCall (.resolve "X") "order" none])) with
  | .ok (Result.listValue [Result.atom 1, Result.atom 2, Result.atom 3], 1) => true
  | _ => false

#guard boundaryOrderIsOneValue

def boundaryOrderSpreadOpensItems : Bool :=
  match runCountedProgram (.algorithmExpr (algPrivate [] [] [("X", alg [] [] [] [.num 3, .num 1, .num 2])]
      [sequenceSpread (.dotCall (.resolve "X") "order" none)])) with
  | .ok (Result.sequenceValue [Result.atom 1, Result.atom 2, Result.atom 3], 3) => true
  | _ => false

#guard boundaryOrderSpreadOpensItems

/-- `range(1, 3)` is a collection-producing builtin: one exact list value,
    opened by spread. -/
def boundaryRangeIsOneValue : Bool :=
  match runCountedProgram (.algorithmExpr (algPrivate [] [] []
      [.call (.resolve "range") [.num 1, .num 3]])) with
  | .ok (Result.listValue [Result.atom 1, Result.atom 2, Result.atom 3], 1) => true
  | _ => false

#guard boundaryRangeIsOneValue

/-- `F(*a) = a.sum` sums the exact collected list through the builtin's
    post-binding collection view. -/
def boundaryVariadicForwardingUsesCollectedListView : Bool :=
  match runCountedProgram (.algorithmExpr (algPrivate [] []
      [("F", algWithParameters [{ name := "a", kind := .collecting }] [] []
        [.dotCall (.param "a") "sum" none])]
      [.call (.resolve "F") [.num 5, .num 9]])) with
  | .ok (Result.atom 14, 1) => true
  | _ => false

#guard boundaryVariadicForwardingUsesCollectedListView

/-- Regression: root output is NOT a call boundary and stays multi-output. -/
def boundaryRootOutputStaysMultiOutput : Bool :=
  match runCountedProgram (.algorithmExpr (algPrivate [] [] [] [.num 1, .num 2, .num 3])) with
  | .ok (Result.sequenceValue [Result.atom 1, Result.atom 2, Result.atom 3], 3) => true
  | _ => false

#guard boundaryRootOutputStaysMultiOutput

/-- Regression: redundant empty sequence nesting canonicalizes before the
    boundary re-count observes it. -/
def boundaryCanonicalizesNestedEmptySequence : Bool :=
  match runCountedProgram (.algorithmExpr (algPrivate [] [] [("F", alg [] [] [] [.emptySequence 1])] [.resolve "F"])) with
  | .ok (Result.sequenceValue [], 1) => true
  | _ => false

#guard boundaryCanonicalizesNestedEmptySequence

-- Collection-producing builtin parity: each returns one exact list value (count 1)
-- at the call/property boundary; caller-site `value*`
-- opens it into an item supply.
-- (`order` and `range` are covered by the guards above.)

def boundaryDesc312 : Algorithm := alg [] [] [] [.num 3, .num 1, .num 2]
def boundary123 : Algorithm := alg [] [] [] [.num 1, .num 2, .num 3]

/-- `X.orderDesc` is one value; `X.orderDesc*` opens it. -/
def boundaryOrderDescIsOneValue : Bool :=
  match runCountedProgram (.algorithmExpr (algPrivate [] [] [("X", boundaryDesc312)]
      [.dotCall (.resolve "X") "orderDesc" none])) with
  | .ok (Result.listValue [Result.atom 3, Result.atom 2, Result.atom 1], 1) => true
  | _ => false

#guard boundaryOrderDescIsOneValue

def boundaryOrderDescSpreadOpensItems : Bool :=
  match runCountedProgram (.algorithmExpr (algPrivate [] [] [("X", boundaryDesc312)]
      [sequenceSpread (.dotCall (.resolve "X") "orderDesc" none)])) with
  | .ok (Result.sequenceValue [Result.atom 3, Result.atom 2, Result.atom 1], 3) => true
  | _ => false

#guard boundaryOrderDescSpreadOpensItems

/-- `X.distinct` is one value; `X.distinct*` opens it. -/
def boundaryDistinctIsOneValue : Bool :=
  match runCountedProgram (.algorithmExpr (algPrivate [] [] [("X", alg [] [] [] [.num 1, .num 1, .num 2, .num 3])]
      [.dotCall (.resolve "X") "distinct" none])) with
  | .ok (Result.listValue [Result.atom 1, Result.atom 2, Result.atom 3], 1) => true
  | _ => false

#guard boundaryDistinctIsOneValue

def boundaryDistinctSpreadOpensItems : Bool :=
  match runCountedProgram (.algorithmExpr (algPrivate [] [] [("X", alg [] [] [] [.num 1, .num 1, .num 2, .num 3])]
      [sequenceSpread (.dotCall (.resolve "X") "distinct" none)])) with
  | .ok (Result.sequenceValue [Result.atom 1, Result.atom 2, Result.atom 3], 3) => true
  | _ => false

#guard boundaryDistinctSpreadOpensItems

/-- `X.take(2)` is one value. -/
def boundaryTakeIsOneValue : Bool :=
  match runCountedProgram (.algorithmExpr (algPrivate [] [] [("X", boundary123)]
      [.dotCall (.resolve "X") "take" (some [.num 2])])) with
  | .ok (Result.listValue [Result.atom 1, Result.atom 2], 1) => true
  | _ => false

#guard boundaryTakeIsOneValue

/-- `X.skip(1)` is one value; `X.skip(1)*` opens it. -/
def boundarySkipIsOneValue : Bool :=
  match runCountedProgram (.algorithmExpr (algPrivate [] [] [("X", boundary123)]
      [.dotCall (.resolve "X") "skip" (some [.num 1])])) with
  | .ok (Result.listValue [Result.atom 2, Result.atom 3], 1) => true
  | _ => false

#guard boundarySkipIsOneValue

def boundarySkipSpreadOpensItems : Bool :=
  match runCountedProgram (.algorithmExpr (algPrivate [] [] [("X", boundary123)]
      [sequenceSpread (.dotCall (.resolve "X") "skip" (some [.num 1]))])) with
  | .ok (Result.sequenceValue [Result.atom 2, Result.atom 3], 2) => true
  | _ => false

#guard boundarySkipSpreadOpensItems

/-- `X.filter(IsBig)` (with `IsBig(x) = x > 1`) is one value; caller-side spread opens it. -/
def boundaryFilterPredicate : Algorithm := alg ["x"] [] [] [.binary .gt (.param "x") (.num 1)]

def boundaryFilterIsOneValue : Bool :=
  match runCountedProgram (.algorithmExpr (algPrivate [] [] [("IsBig", boundaryFilterPredicate), ("X", boundary123)]
      [.dotCall (.resolve "X") "filter" (some [.resolve "IsBig"])])) with
  | .ok (Result.listValue [Result.atom 2, Result.atom 3], 1) => true
  | _ => false

#guard boundaryFilterIsOneValue

def boundaryFilterSpreadOpensItems : Bool :=
  match runCountedProgram (.algorithmExpr (algPrivate [] [] [("IsBig", boundaryFilterPredicate), ("X", boundary123)]
      [sequenceSpread (.dotCall (.resolve "X") "filter" (some [.resolve "IsBig"]))])) with
  | .ok (Result.sequenceValue [Result.atom 2, Result.atom 3], 2) => true
  | _ => false

#guard boundaryFilterSpreadOpensItems

/-- `X.map(Double)` (with `Double(x) = x * 2`) is one value; caller-side spread opens it. -/
def boundaryMapTransform : Algorithm := alg ["x"] [] [] [.binary .mul (.param "x") (.num 2)]

def boundaryMapIsOneValue : Bool :=
  match runCountedProgram (.algorithmExpr (algPrivate [] [] [("Double", boundaryMapTransform), ("X", boundary123)]
      [.dotCall (.resolve "X") "map" (some [.resolve "Double"])])) with
  | .ok (Result.listValue [Result.atom 2, Result.atom 4, Result.atom 6], 1) => true
  | _ => false

#guard boundaryMapIsOneValue

def boundaryMapSpreadOpensItems : Bool :=
  match runCountedProgram (.algorithmExpr (algPrivate [] [] [("Double", boundaryMapTransform), ("X", boundary123)]
      [sequenceSpread (.dotCall (.resolve "X") "map" (some [.resolve "Double"]))])) with
  | .ok (Result.sequenceValue [Result.atom 2, Result.atom 4, Result.atom 6], 3) => true
  | _ => false

#guard boundaryMapSpreadOpensItems

/-- `atoms((1, (2, 3)))` is ONE exact list value `[1, 2, 3]`;
    `atoms(...)*` opens the one list boundary into three items. -/
def boundaryAtomsArg : List KatLang.Expr := [sequenceItems [.num 1, sequenceItems [.num 2, .num 3]]]

def boundaryAtomsIsOneValue : Bool :=
  match runCountedProgram (.algorithmExpr (algPrivate [] [] []
      [.call (.resolve "atoms") boundaryAtomsArg])) with
  | .ok (Result.listValue [Result.atom 1, Result.atom 2, Result.atom 3], 1) => true
  | _ => false

#guard boundaryAtomsIsOneValue

def boundaryAtomsSpreadOpensItems : Bool :=
  match runCountedProgram (.algorithmExpr (algPrivate [] [] []
      [sequenceSpread (.call (.resolve "atoms") boundaryAtomsArg)])) with
  | .ok (Result.sequenceValue [Result.atom 1, Result.atom 2, Result.atom 3], 3) => true
  | _ => false

#guard boundaryAtomsSpreadOpensItems

end KatLangTests
