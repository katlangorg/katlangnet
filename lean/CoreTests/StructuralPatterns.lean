import KatLang
import CoreTests.Common

namespace KatLangTests
open KatLang (alg algWithParameters algWithParameterPatterns algPrivate privateProp publicProp privateLocalProp publicLocalProp runFlat runResult Algorithm Error Result PropExposure)
open KatLang (resolve param num)
open KatLang (Pattern CondBranch)

--------------------------------------------------------------------------------
-- Structural patterns select the value kind they destructure (September 2026)
--------------------------------------------------------------------------------
-- In both pattern languages a parenthesized structural pattern `(p1, …, pn)`
-- matches SEQUENCE values only and a bracketed structural pattern `[p1, …, pn]`
-- matches LIST values only; neither destructures the other kind and no scalar is
-- a one-item structure. A bare binder is the only pattern that takes a value
-- whole. There is no one-item sequence value, so a sequence pattern with exactly
-- one non-collecting item is invalid (rejected before evaluation), the
-- collector-only `(*xs)` stays valid, and the one-element pattern is `[x]`.
-- Ordinary and family patterns follow the SAME kind law; they differ only in
-- what a mismatch does (an ordinary binding fails, a family tries its next
-- clause) and in collectors (ordinary only). C# twins:
-- `StructuralPatternKindTests`, `SingletonSequencePatternTests`; spec cases
-- `structural-patterns-open-only-their-own-kind` and `singleton-sequence-pattern-is-invalid`.

private def spLit (s : String) : KatLang.Expr := .stringLiteral s

private def spRun (props : List (Prod String Algorithm)) (out : KatLang.Expr) : Except Error Result :=
  runResult (.algorithmExpr (algPrivate [] [] props [out]))

private def spIs (props : List (Prod String Algorithm)) (expected : Result) (out : KatLang.Expr) : Bool :=
  match spRun props out with
  | .ok value => value == expected
  | _ => false

private def spFails (props : List (Prod String Algorithm)) (classify : Error -> Bool) (out : KatLang.Expr) : Bool :=
  match spRun props out with
  | .error err => classify err
  | _ => false

private def spIsDuplicateBranchPattern : Error -> Bool
  | .withContext _ inner => spIsDuplicateBranchPattern inner
  | .duplicateBranchPattern => true
  | _ => false

-- 1. A family distinguishes list cardinalities with list patterns:
--    Kind([]) = 'empty' / Kind([x]) = 'one' / Kind([x, y]) = 'two' / Kind(other) = 'other'.
--    A sequence or a scalar is never a list, so it reaches the catch-all.
def spKindAlg : Algorithm :=
  Algorithm.elaborateClauseGroup [
    { pattern := .sequenceValue [.listValue []], body := alg [] [] [] [spLit "empty"] },
    { pattern := .sequenceValue [.listValue [.bind "x"]], body := alg [] [] [] [spLit "one"] },
    { pattern := .sequenceValue [.listValue [.bind "x", .bind "y"]], body := alg [] [] [] [spLit "two"] },
    { pattern := .bind "other", body := alg [] [] [] [spLit "other"] } ]

def familyListPatternsMatchListsOfTheirLength : Bool :=
  let props := [("Kind", spKindAlg)]
  spIs props (.str "empty") (.call (resolve "Kind") [.listLiteral []]) &&
  spIs props (.str "one") (.call (resolve "Kind") [.listLiteral [.num 7]]) &&
  spIs props (.str "one") (.call (resolve "Kind") [.listLiteral [.capture [.num 1, .num 2]]]) &&
  spIs props (.str "two") (.call (resolve "Kind") [.listLiteral [.num 1, .num 2]]) &&
  spIs props (.str "other") (.call (resolve "Kind") [.listLiteral [.num 1, .num 2, .num 3]]) &&
  spIs props (.str "other") (.call (resolve "Kind") [.emptySequence 0]) &&
  spIs props (.str "other") (.call (resolve "Kind") [.capture [.num 1, .num 2]]) &&
  spIs props (.str "other") (.call (resolve "Kind") [.num 7])

#guard familyListPatternsMatchListsOfTheirLength

-- 2. A family distinguishes sequences with sequence patterns:
--    Seq(()) = 'empty' / Seq((x, y)) = 'pair' / Seq(other) = 'other'.
--    A list is never a sequence: `[]` and `[1, 2]` reach the catch-all.
def spSeqAlg : Algorithm :=
  Algorithm.elaborateClauseGroup [
    { pattern := .sequenceValue [.sequenceValue []], body := alg [] [] [] [spLit "empty"] },
    { pattern := .sequenceValue [.sequenceValue [.bind "x", .bind "y"]], body := alg [] [] [] [spLit "pair"] },
    { pattern := .bind "other", body := alg [] [] [] [spLit "other"] } ]

def familySequencePatternsMatchSequencesOnly : Bool :=
  let props := [("Seq", spSeqAlg)]
  spIs props (.str "empty") (.call (resolve "Seq") [.emptySequence 0]) &&
  spIs props (.str "pair") (.call (resolve "Seq") [.capture [.num 1, .num 2]]) &&
  spIs props (.str "other") (.call (resolve "Seq") [.capture [.num 1, .num 2, .num 3]]) &&
  spIs props (.str "other") (.call (resolve "Seq") [.listLiteral []]) &&
  spIs props (.str "other") (.call (resolve "Seq") [.listLiteral [.num 1, .num 2]]) &&
  spIs props (.str "other") (.call (resolve "Seq") [.num 7])

#guard familySequencePatternsMatchSequencesOnly

-- 3. Without a catch-all, a wrong kind is the family's NoMatchingBranch (never a
--    kind mismatch: families only reject clauses), while an ordinary single clause
--    with the same head fails its binding with the kind mismatch.
def spPairFamilyAlg : Algorithm :=
  Algorithm.elaborateClauseGroup [
    { pattern := .sequenceValue [.sequenceValue [.litInt 0, .bind "y"]], body := alg [] [] [] [param "y"] },
    { pattern := .sequenceValue [.sequenceValue [.bind "x", .bind "y"]], body := alg [] [] [] [param "x"] } ]

def spPairOrdinaryAlg : Algorithm :=
  Algorithm.elaborateClauseGroup [
    { pattern := .sequenceValue [.sequenceValue [.bind "x", .bind "y"]], body := alg [] [] [] [param "x"] } ]

def wrongKindIsNoMatchInAFamilyAndAKindMismatchInAnOrdinaryCall : Bool :=
  let props := [("Fam", spPairFamilyAlg), ("Ord", spPairOrdinaryAlg)]
  spIs props (.atom 5) (.call (resolve "Fam") [.capture [.num 0, .num 5]]) &&
  spFails props (innermostIsNoMatchingBranch "Fam") (.call (resolve "Fam") [.listLiteral [.num 0, .num 5]]) &&
  spFails props (innermostIsNoMatchingBranch "Fam") (.call (resolve "Fam") [.num 5]) &&
  spIs props (.atom 3) (.call (resolve "Ord") [.capture [.num 3, .num 4]]) &&
  spFails props innermostIsAnyTypeMismatch (.call (resolve "Ord") [.listLiteral [.num 3, .num 4]]) &&
  spFails props innermostIsAnyTypeMismatch (.call (resolve "Ord") [.num 3]) &&
  spFails props (innermostIsArityMismatch 2 3) (.call (resolve "Ord") [.capture [.num 3, .num 4, .num 5]])

#guard wrongKindIsNoMatchInAFamilyAndAKindMismatchInAnOrdinaryCall

-- 4. Nested structural patterns preserve kind at EVERY level.
--    F(([x, y], z)) = x + y + z: a sequence whose first element is a two-element list.
--    G([(x, y), z]) = x + y + z: a list whose first element is a two-element sequence.
def spMixedAlgs : List (Prod String Algorithm) :=
  [ ("F", algWithParameterPatterns
      [.sequenceValue [.listValue [.capture { name := "x" }, .capture { name := "y" }], .capture { name := "z" }]] [] []
      [.binary .add (.binary .add (param "x") (param "y")) (param "z")]),
    ("G", algWithParameterPatterns
      [.listValue [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }], .capture { name := "z" }]] [] []
      [.binary .add (.binary .add (param "x") (param "y")) (param "z")]) ]

def nestedStructuralPatternsPreserveKindAtEveryLevel : Bool :=
  spIs spMixedAlgs (.atom 60) (.call (resolve "F") [.capture [.listLiteral [.num 10, .num 20], .num 30]]) &&
  spIs spMixedAlgs (.atom 6) (.call (resolve "G") [.listLiteral [.capture [.num 1, .num 2], .num 3]]) &&
  -- The outer kind is checked: F's sequence pattern never opens a list.
  spFails spMixedAlgs innermostIsAnyTypeMismatch
    (.call (resolve "F") [.listLiteral [.listLiteral [.num 10, .num 20], .num 30]]) &&
  -- The inner kind is checked too: a sequence where F wants a list, a list where G
  -- wants a sequence.
  spFails spMixedAlgs innermostIsAnyTypeMismatch
    (.call (resolve "F") [.capture [.capture [.num 10, .num 20], .num 30]]) &&
  spFails spMixedAlgs innermostIsAnyTypeMismatch
    (.call (resolve "G") [.listLiteral [.listLiteral [.num 1, .num 2], .num 3]]) &&
  -- The callback spelling binds exactly the same way.
  spIs spMixedAlgs (.listValue [.atom 60])
    (.call (resolve "map") [.listLiteral [.capture [.listLiteral [.num 10, .num 20], .num 30]], resolve "F"])

#guard nestedStructuralPatternsPreserveKindAtEveryLevel

-- 5. The empty structures stay distinct: `()` matches only the empty sequence and
--    `[]` only the empty list, at the top of a pattern and nested alike.
def spEmptyAlgs : List (Prod String Algorithm) :=
  [ ("ES", algWithParameterPatterns [.sequenceValue []] [] [] [spLit "()"]),
    ("EL", algWithParameterPatterns [.listValue []] [] [] [spLit "[]"]),
    ("LE", algWithParameterPatterns [.listValue [.sequenceValue []]] [] [] [spLit "[()]"]),
    ("LL", algWithParameterPatterns [.listValue [.listValue []]] [] [] [spLit "[[]]"]),
    ("SE", algWithParameterPatterns [.sequenceValue [.sequenceValue [], .listValue []]] [] [] [spLit "((), [])"]) ]

def emptySequenceAndEmptyListPatternsStayDistinct : Bool :=
  spIs spEmptyAlgs (.str "()") (.call (resolve "ES") [.emptySequence 0]) &&
  spFails spEmptyAlgs innermostIsAnyTypeMismatch (.call (resolve "ES") [.listLiteral []]) &&
  spIs spEmptyAlgs (.str "[]") (.call (resolve "EL") [.listLiteral []]) &&
  spFails spEmptyAlgs innermostIsAnyTypeMismatch (.call (resolve "EL") [.emptySequence 0]) &&
  spIs spEmptyAlgs (.str "[()]") (.call (resolve "LE") [.listLiteral [.emptySequence 0]]) &&
  spFails spEmptyAlgs innermostIsAnyTypeMismatch (.call (resolve "LE") [.listLiteral [.listLiteral []]]) &&
  spIs spEmptyAlgs (.str "[[]]") (.call (resolve "LL") [.listLiteral [.listLiteral []]]) &&
  spFails spEmptyAlgs innermostIsAnyTypeMismatch (.call (resolve "LL") [.listLiteral [.emptySequence 0]]) &&
  spIs spEmptyAlgs (.str "((), [])") (.call (resolve "SE") [.capture [.emptySequence 0, .listLiteral []]]) &&
  spFails spEmptyAlgs innermostIsAnyTypeMismatch (.call (resolve "SE") [.capture [.listLiteral [], .emptySequence 0]]) &&
  -- A nonempty structure never matches an empty pattern: the length decides.
  spFails spEmptyAlgs (innermostIsArityMismatch 0 2) (.call (resolve "ES") [.capture [.num 1, .num 2]]) &&
  spFails spEmptyAlgs (innermostIsArityMismatch 0 1) (.call (resolve "EL") [.listLiteral [.num 1]])

#guard emptySequenceAndEmptyListPatternsStayDistinct

-- 6. Collector allocation is the same algorithm for both kinds: fixed prefix and
--    suffix bind first, the collector takes the exact middle as one list. A list
--    collector sees every cardinality; a sequence collector sees 0 or at least 2
--    elements, because no one-item sequence exists.
def spCollectorAlgs : List (Prod String Algorithm) :=
  [ ("SM", algWithParameterPatterns
      [.sequenceValue [.capture { name := "x" }, .capture { name := "m", kind := .collecting }, .capture { name := "z" }]] [] []
      [.listLiteral [param "x", param "m", param "z"]]),
    ("LM", algWithParameterPatterns
      [.listValue [.capture { name := "x" }, .capture { name := "m", kind := .collecting }, .capture { name := "z" }]] [] []
      [.listLiteral [param "x", param "m", param "z"]]),
    ("LP", algWithParameterPatterns
      [.listValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] []
      [.listLiteral [param "p", param "z"]]),
    ("LX", algWithParameterPatterns [.listValue [.capture { name := "xs", kind := .collecting }]] [] [] [param "xs"]),
    ("SX", algWithParameterPatterns [.sequenceValue [.capture { name := "xs", kind := .collecting }]] [] [] [param "xs"]) ]

def collectorAllocationIsTheSameForBothKinds : Bool :=
  spIs spCollectorAlgs (.listValue [.atom 1, .listValue [.atom 2, .atom 3], .atom 4])
    (.call (resolve "SM") [.capture [.num 1, .num 2, .num 3, .num 4]]) &&
  spIs spCollectorAlgs (.listValue [.atom 1, .listValue [.atom 2, .atom 3], .atom 4])
    (.call (resolve "LM") [.listLiteral [.num 1, .num 2, .num 3, .num 4]]) &&
  spIs spCollectorAlgs (.listValue [.atom 1, .listValue [], .atom 4])
    (.call (resolve "LM") [.listLiteral [.num 1, .num 4]]) &&
  spFails spCollectorAlgs (innermostIsArityMismatch 2 1) (.call (resolve "LM") [.listLiteral [.num 1]]) &&
  spIs spCollectorAlgs (.listValue [.listValue [], .atom 9]) (.call (resolve "LP") [.listLiteral [.num 9]]) &&
  spIs spCollectorAlgs (.listValue []) (.call (resolve "LX") [.listLiteral []]) &&
  spIs spCollectorAlgs (.listValue [.atom 7]) (.call (resolve "LX") [.listLiteral [.num 7]]) &&
  spIs spCollectorAlgs (.listValue [.atom 1, .atom 2]) (.call (resolve "LX") [.listLiteral [.num 1, .num 2]]) &&
  spIs spCollectorAlgs (.listValue []) (.call (resolve "SX") [.emptySequence 0]) &&
  spIs spCollectorAlgs (.listValue [.atom 1, .atom 2]) (.call (resolve "SX") [.capture [.num 1, .num 2]]) &&
  -- A one-item "sequence" is its item: `(7)` IS 7, which the sequence collector rejects.
  spFails spCollectorAlgs innermostIsAnyTypeMismatch (.call (resolve "SX") [.capture [.num 7]]) &&
  spFails spCollectorAlgs innermostIsAnyTypeMismatch (.call (resolve "SX") [.listLiteral [.num 7]])

#guard collectorAllocationIsTheSameForBothKinds

-- 7. Duplicate branch detection: the structural KIND is part of a pattern's shape,
--    binder spelling is not.
def duplicateDetectionRespectsKind : Bool :=
  let seqPair : Pattern := .sequenceValue [.sequenceValue [.bind "x", .bind "y"]]
  let listPair : Pattern := .sequenceValue [.listValue [.bind "a", .bind "b"]]
  let listPairRenamed : Pattern := .sequenceValue [.listValue [.bind "p", .bind "q"]]
  let emptySeq : Pattern := .sequenceValue [.sequenceValue []]
  let emptyList : Pattern := .sequenceValue [.listValue []]
  !seqPair.isMatchEquivalent listPair &&
  listPair.isMatchEquivalent listPairRenamed &&
  !emptySeq.isMatchEquivalent emptyList &&
  emptyList.isMatchEquivalent emptyList &&
  -- A family holding `F((x, y))` and `F([a, b])` is no duplicate and dispatches by kind.
  (let family := Algorithm.elaborateClauseGroup [
      { pattern := seqPair, body := alg [] [] [] [spLit "sequence"] },
      { pattern := listPair, body := alg [] [] [] [spLit "list"] } ]
   spIs [("F", family)] (.str "sequence") (.call (resolve "F") [.capture [.num 1, .num 2]]) &&
   spIs [("F", family)] (.str "list") (.call (resolve "F") [.listLiteral [.num 1, .num 2]])) &&
  -- Two renamed list clauses ARE duplicates.
  (let duplicate := Algorithm.elaborateClauseGroup [
      { pattern := listPair, body := alg [] [] [] [.num 1] },
      { pattern := listPairRenamed, body := alg [] [] [] [.num 2] } ]
   spFails [("D", duplicate)] spIsDuplicateBranchPattern (.call (resolve "D") [.listLiteral [.num 1, .num 2]]))

#guard duplicateDetectionRespectsKind

-- 8. A single clause with only binders and structural patterns of either kind is an
--    ORDINARY algorithm (its structural parameter patterns keep their kinds); a
--    literal anywhere makes it a family.
def singleListClauseIsOrdinary : Bool :=
  (match Algorithm.clauseGroupDefinitionKind [{ pattern := .sequenceValue [.listValue [.bind "x"]], body := alg [] [] [] [param "x"] }] with
   | .ordinary [.listValue [.capture { name := "x", kind := .normal }]] => true
   | _ => false) &&
  (match Algorithm.clauseGroupDefinitionKind [{ pattern := .sequenceValue [.listValue [.litInt 0]], body := alg [] [] [] [.num 0] }] with
   | .conditional => true
   | _ => false) &&
  (match Algorithm.clauseGroupDefinitionKind [{ pattern := .sequenceValue [.sequenceValue [.listValue [.bind "x", .bind "y"], .bind "z"]], body := alg [] [] [] [param "z"] }] with
   | .ordinary [.sequenceValue [.listValue [_, _], .capture _]] => true
   | _ => false)

#guard singleListClauseIsOrdinary

-- 9. THE SINGLETON RULE over heads: a nested one-item sequence pattern is invalid
--    wherever it stands (`(x)`, `((x, y))`, `([x])`, `[(x)]`), the head's own
--    parentheses are not a sequence pattern, and `[x]` / `(*xs)` / `()` are valid.
def singletonRuleOverHeads : Bool :=
  (Pattern.sequenceValue [.sequenceValue [.bind "x"]]).headHasSingletonSequenceGroup &&
  (Pattern.sequenceValue [.sequenceValue [.sequenceValue [.bind "x", .bind "y"]]]).headHasSingletonSequenceGroup &&
  (Pattern.sequenceValue [.sequenceValue [.listValue [.bind "x"]]]).headHasSingletonSequenceGroup &&
  (Pattern.sequenceValue [.listValue [.sequenceValue [.bind "x"]]]).headHasSingletonSequenceGroup &&
  !(Pattern.sequenceValue [.bind "x"]).headHasSingletonSequenceGroup &&
  !(Pattern.bind "x").headHasSingletonSequenceGroup &&
  !(Pattern.sequenceValue [.listValue [.bind "x"]]).headHasSingletonSequenceGroup &&
  !(Pattern.sequenceValue [.sequenceValue []]).headHasSingletonSequenceGroup &&
  !(Pattern.sequenceValue [.sequenceValue [.bind "x", .bind "y"]]).headHasSingletonSequenceGroup &&
  -- The ordinary language: a collector-only group is valid, a nested one-item group is not.
  !(KatLang.ParameterPattern.anyHasSingletonSequenceGroup
      [.sequenceValue [.capture { name := "xs", kind := .collecting }]]) &&
  KatLang.ParameterPattern.anyHasSingletonSequenceGroup
      [.listValue [.sequenceValue [.capture { name := "x" }]]]

#guard singletonRuleOverHeads

end KatLangTests
