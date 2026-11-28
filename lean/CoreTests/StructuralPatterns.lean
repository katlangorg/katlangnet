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
-- clause): a family head collects inside a structural pattern of an argument
-- exactly as an ordinary head does, and only refuses a collector directly among
-- its call arguments (Q-47, the last section of this module). C# twins:
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

-- 10. X-02: ONE VALIDITY RULE FOR EVERY SIGNATURE, written or inferred
--     (`ParameterPattern.signatureViolation?`, C# `ParameterPattern.FindSignatureViolation`).
--     The C# front end rejects formula lifting that would compose `K(a, *p, b, *q)` from
--     `C1(a, *p)` and `C2(b, *q)`; a collecting name two callees share is ONE binding, and
--     a collector nested in its own group is that group's level. C# twin:
--     `InferredSignatureValidityTests`.
private def spCap (name : String) : KatLang.ParameterPattern := .capture { name := name }
private def spColl (name : String) : KatLang.ParameterPattern := .capture { name := name, kind := .collecting }

def signatureValidityWitnesses : Bool :=
  -- The X-02 composition, and every position of a second top-level collector.
  KatLang.ParameterPattern.signatureViolation? [spCap "a", spColl "p", spCap "b", spColl "q"]
      == some .multipleCollectingAtOneLevel &&
  KatLang.ParameterPattern.signatureViolation? [spColl "p", spCap "a", spCap "b", spColl "q"]
      == some .multipleCollectingAtOneLevel &&
  -- One lifted binding for the shared collecting name; one collector per group level.
  KatLang.ParameterPattern.signatureViolation? [spCap "a", spColl "rest", spCap "b"] == none &&
  KatLang.ParameterPattern.signatureViolation?
      [.sequenceValue [spCap "a", spColl "p"], .sequenceValue [spCap "b", spColl "q"]] == none &&
  KatLang.ParameterPattern.signatureViolation?
      [.sequenceValue [spCap "a", spColl "p"], spCap "d", spColl "r"] == none &&
  -- A nested level is its own level.
  KatLang.ParameterPattern.signatureViolation? [.listValue [spColl "r", spColl "s"]]
      == some .multipleCollectingAtOneLevel &&
  -- Repeated fixed names are Q-05's constraints; a repeated name with a collector is not.
  KatLang.ParameterPattern.signatureViolation? [spCap "x", spCap "x"] == none &&
  KatLang.ParameterPattern.signatureViolation? [spCap "x", spColl "x"]
      == some .repeatedNameIncludesCollecting &&
  -- Rule order: the singleton rule, then the collector rule, then repeated collecting names.
  KatLang.ParameterPattern.signatureViolation? [.sequenceValue [spCap "x"], spColl "p", spColl "q"]
      == some .singletonSequencePattern &&
  KatLang.ParameterPattern.signatureViolation? [spColl "x", spCap "x", spColl "q"]
      == some .multipleCollectingAtOneLevel

#guard signatureValidityWitnesses

-- A host-built algorithm cannot reach a binder with two collectors at one level: the
-- pre-evaluation validation rejects it, like the singleton rule (C#:
-- `PreEvaluationAstViolation.MultipleCollectingCaptures`).
def twoCollectorSignatureIsIllegalBeforeEvaluation : Bool :=
  let k := algWithParameterPatterns [spCap "a", spColl "p", spCap "b", spColl "q"] [] [] [param "a"]
  let nested := algWithParameterPatterns [.listValue [spColl "p", spColl "q"]] [] [] [num 0]
  let valid := algWithParameterPatterns [spCap "a", spColl "rest", spCap "b"] [] [] [param "a"]
  (match runResult (.algorithmExpr (algPrivate [] [] [("K", k)] [.call (resolve "K") [num 1, num 2]])) with
   | .error (.illegalInEval message) => message == KatLang.multipleCollectingBindingsPerLevelMessage
   | _ => false) &&
  (match runResult (.algorithmExpr (algPrivate [] [] [("K", nested)] [num 1])) with
   | .error (.illegalInEval message) => message == KatLang.multipleCollectingBindingsPerLevelMessage
   | _ => false) &&
  spIs [("K", valid)] (.atom 1) (.call (resolve "K") [num 1, num 2, num 3])

#guard twoCollectorSignatureIsIllegalBeforeEvaluation

-- The third X-02 rule is also a pre-evaluation invariant, including names
-- repeated across different pattern levels. The unused definition wins over
-- the failing output row; fixed repeated names remain ordinary constraints.
def repeatedCollectorSignatureIsIllegalBeforeEvaluation : Bool :=
  ([[spCap "x", spColl "x"],
    [.listValue [spCap "x", spColl "x"]],
    [.sequenceValue [spCap "x", spColl "x"]],
    [.unpacking [spCap "x", spColl "x"]],
    [spCap "x", .listValue [spColl "x"]]] : List (List KatLang.ParameterPattern)).all fun ps =>
      let k := algWithParameterPatterns ps [] [] [num 7]
      match runResult (.algorithmExpr (algPrivate [] [] [("K", k)] [.binary .div (num 1) (num 0)])) with
      | .error (.illegalInEval message) => message == KatLang.repeatedNameIncludesCollectingMessage
      | _ => false
#guard repeatedCollectorSignatureIsIllegalBeforeEvaluation

def invalidSignatureOrderPrecedesMissingOutput : Bool :=
  ([([.sequenceValue [spCap "x"], spColl "x", spColl "x"], KatLang.singletonSequencePatternMessage),
    ([spColl "x", spColl "x"], KatLang.multipleCollectingBindingsPerLevelMessage),
    ([spCap "x", spColl "x"], KatLang.repeatedNameIncludesCollectingMessage)]
    : List (List KatLang.ParameterPattern × String)).all fun (ps, expected) =>
      match runResult (.algorithmExpr (algWithParameterPatterns ps [] [] [])) with
      | .error (.illegalInEval message) => message == expected
      | _ => false
#guard invalidSignatureOrderPrecedesMissingOutput

--------------------------------------------------------------------------------
-- Collecting bindings inside clause-family patterns (Q-47, decided 2026-11-27)
--------------------------------------------------------------------------------
-- A CLAUSE FAMILY HAS ONE FIXED CALL ARITY. Within any argument, a list or
-- sequence pattern may contain collecting bindings under the ordinary
-- structural-pattern rules: `F([head, *rest])` inspects ONE list argument and
-- `F((head, *rest))` ONE sequence argument, in a single literal-bearing clause
-- and in a family of several clauses alike. A collector directly among a
-- family's call arguments (`F(head, *rest)`, `F(*xs)`) is invalid. Expectations
-- are hand-written. C# twins: `ClauseFamilyCollectingPatternTests`; spec cases
-- `family-list-pattern-collects-tail` and its neighbours in
-- `conformance/features/clause-dispatch.json`.

private def fcClause (pattern : Pattern) (out : KatLang.Expr) : CondBranch :=
  { pattern := pattern, body := alg [] [] [] [out] }

private def fcColl (name : String) : Pattern := .bind name true

-- Tail([]) = []
-- Tail([head, *rest]) = rest
def fcTailAlg : Algorithm :=
  Algorithm.elaborateClauseGroup [
    fcClause (.sequenceValue [.listValue []]) (.listLiteral []),
    fcClause (.sequenceValue [.listValue [.bind "head", fcColl "rest"]]) (param "rest") ]

-- 11. THE ACCEPTANCE EXAMPLE. The family stays a family (two clauses), each clause
--     consumes exactly one argument, and the collector takes the remaining
--     elements as one exact list, nested values kept as elements.
def familyListPatternCollectsTheTail : Bool :=
  let props := [("Tail", fcTailAlg)]
  (match fcTailAlg with
   | .conditional _ _ branches _ => branches.length == 2
   | _ => false) &&
  -- Tail(['a', ['b', 'c'], 'd']) is [['b', 'c'], 'd'].
  spIs props (.listValue [.listValue [.str "b", .str "c"], .str "d"])
    (.call (resolve "Tail") [.listLiteral [spLit "a", .listLiteral [spLit "b", spLit "c"], spLit "d"]]) &&
  -- Tail([]) is [] from the empty-list clause.
  spIs props (.listValue []) (.call (resolve "Tail") [.listLiteral []]) &&
  -- Tail(['a']) is [] from an empty collecting slice.
  spIs props (.listValue []) (.call (resolve "Tail") [.listLiteral [spLit "a"]]) &&
  -- Tail([1 / 0, 'b']) is ['b']: binding the unused head leaves that position undemanded.
  spIs props (.listValue [.str "b"])
    (.call (resolve "Tail") [.listLiteral [.binary .div (num 1) (num 0), spLit "b"]]) &&
  -- Tail(('a', 'b')) is NoMatchingBranch: one argument, and no list pattern matches a sequence.
  spFails props (innermostIsNoMatchingBranch "Tail") (.call (resolve "Tail") [.capture [spLit "a", spLit "b"]]) &&
  -- Tail('a', 'b') is ArityMismatch at the family call, before branch selection.
  spFails props (innermostIsArityMismatch 1 2) (.call (resolve "Tail") [spLit "a", spLit "b"]) &&
  spFails props (innermostIsArityMismatch 1 0) (.call (resolve "Tail") []) &&
  -- A scalar is one argument that no list pattern matches.
  spFails props (innermostIsNoMatchingBranch "Tail") (.call (resolve "Tail") [spLit "a"])

#guard familyListPatternCollectsTheTail

-- Payload(('packet', *fields, 'end')) = fields
def fcPayloadAlg : Algorithm :=
  Algorithm.elaborateClauseGroup [
    fcClause (.sequenceValue [.sequenceValue [.litString "packet", fcColl "fields", .litString "end"]]) (param "fields") ]

-- 12. A SINGLE LITERAL-BEARING CLAUSE IS A FAMILY, and its collector stands between
--     fixed positions: the sequence pattern consumes one argument however many
--     elements go into `fields`.
def literalBearingClauseCollectsBetweenFixedPositions : Bool :=
  let props := [("Payload", fcPayloadAlg)]
  (match fcPayloadAlg with
   | .conditional _ _ [_] _ => true
   | _ => false) &&
  -- Payload(('packet', 10, [20, 30], 'end')) is [10, [20, 30]].
  spIs props (.listValue [.atom 10, .listValue [.atom 20, .atom 30]])
    (.call (resolve "Payload") [.capture [spLit "packet", num 10, .listLiteral [num 20, num 30], spLit "end"]]) &&
  -- Payload(('packet', 'end')) is [].
  spIs props (.listValue []) (.call (resolve "Payload") [.capture [spLit "packet", spLit "end"]]) &&
  -- The wrong closing literal is NoMatchingBranch.
  spFails props (innermostIsNoMatchingBranch "Payload")
    (.call (resolve "Payload") [.capture [spLit "packet", num 10, spLit "stop"]]) &&
  -- Too few elements for the fixed positions, a list, and a scalar are non-matches too.
  spFails props (innermostIsNoMatchingBranch "Payload") (.call (resolve "Payload") [spLit "packet"]) &&
  spFails props (innermostIsNoMatchingBranch "Payload")
    (.call (resolve "Payload") [.listLiteral [spLit "packet", spLit "end"]]) &&
  -- Separate arguments are the family's arity error: the head has call arity 1.
  spFails props (innermostIsArityMismatch 1 3)
    (.call (resolve "Payload") [spLit "packet", num 10, spLit "end"])

#guard literalBearingClauseCollectsBetweenFixedPositions

-- 13. A collector below a SECOND structural level, a failed first clause followed by
--     a matching fallback, and a demanded field whose failure propagates.
--     Deep(('pair', [x, (first, *others)])) = others
--     Deep((tag, [x, *more])) = more
--     Deep(other) = 'fallback'
def fcDeepAlg : Algorithm :=
  Algorithm.elaborateClauseGroup [
    fcClause (.sequenceValue [.sequenceValue [.litString "pair",
        .listValue [.bind "x", .sequenceValue [.bind "first", fcColl "others"]]]]) (param "others"),
    fcClause (.sequenceValue [.sequenceValue [.bind "tag", .listValue [.bind "x", fcColl "more"]]]) (param "more"),
    fcClause (.bind "other") (spLit "fallback") ]

-- Lit([0, *rest]) = rest
-- Lit(other) = 'other'
def fcLitAlg : Algorithm :=
  Algorithm.elaborateClauseGroup [
    fcClause (.sequenceValue [.listValue [.litInt 0, fcColl "rest"]]) (param "rest"),
    fcClause (.bind "other") (spLit "other") ]

def nestedCollectorFallbackAndFailurePropagation : Bool :=
  let props := [("Deep", fcDeepAlg), ("Lit", fcLitAlg)]
  -- The first clause: the collector two structural levels below the argument.
  spIs props (.listValue [.atom 3, .atom 4])
    (.call (resolve "Deep") [.capture [spLit "pair", .listLiteral [num 1, .capture [num 2, num 3, num 4]]]]) &&
  -- The first clause fails on its literal; the second matches the same supply and
  -- collects the nested sequence whole, as one element.
  spIs props (.listValue [.sequenceValue [.atom 2, .atom 3]])
    (.call (resolve "Deep") [.capture [spLit "other", .listLiteral [num 1, .capture [num 2, num 3]]]]) &&
  -- The first clause fails on the inner list's cardinality; the second collects.
  spIs props (.listValue [.atom 2, .atom 3])
    (.call (resolve "Deep") [.capture [spLit "pair", .listLiteral [num 1, num 2, num 3]]]) &&
  -- The first clause fails on the inner kind (a scalar where it wants a sequence); the second collects.
  spIs props (.listValue [.atom 2])
    (.call (resolve "Deep") [.capture [spLit "pair", .listLiteral [num 1, num 2]]]) &&
  -- Neither structural clause matches: the catch-all does.
  spIs props (.str "fallback") (.call (resolve "Deep") [num 7]) &&
  spIs props (.str "fallback") (.call (resolve "Deep") [.capture [spLit "pair", num 7]]) &&
  -- An element only a plain binder takes is never demanded by matching.
  spIs props (.listValue [.atom 9])
    (.call (resolve "Deep") [.capture [spLit "none", .listLiteral [.binary .div (num 1) (num 0), num 9]]]) &&
  -- A DEMANDED field's failure propagates and is never a non-match: the literal `0`
  -- demands the first list position, so the catch-all is not tried.
  spIs props (.listValue [.atom 2, .atom 3]) (.call (resolve "Lit") [.listLiteral [num 0, num 2, num 3]]) &&
  spIs props (.str "other") (.call (resolve "Lit") [.listLiteral [num 1, num 2]]) &&
  spFails props innermostIsDivByZero
    (.call (resolve "Lit") [.listLiteral [.binary .div (num 1) (num 0), num 2]]) &&
  -- So does the failure of the argument a structural pattern must open.
  spFails props innermostIsDivByZero
    (.call (resolve "Deep") [.capture [.binary .div (num 1) (num 0), .listLiteral [num 1, num 2]]])

#guard nestedCollectorFallbackAndFailurePropagation

-- 14. Classification is of the WHOLE group, before the family restriction: a single
--     literal-free clause keeps its top-level collecting parameter as an ordinary
--     algorithm, nested collectors convert with their kind, and adding the
--     empty-list clause leaves the meaning of the nonempty-list pattern unchanged.
def wholeGroupClassificationKeepsOrdinaryCollectors : Bool :=
  (match Algorithm.clauseGroupDefinitionKind [fcClause (.sequenceValue [.bind "head", fcColl "rest"]) (param "rest")] with
   | .ordinary [.capture { name := "head", kind := .normal }, .capture { name := "rest", kind := .collecting }] => true
   | _ => false) &&
  (match Algorithm.clauseGroupDefinitionKind [fcClause (.sequenceValue [.listValue [.bind "head", fcColl "rest"]]) (param "rest")] with
   | .ordinary [.listValue [.capture { name := "head", kind := .normal }, .capture { name := "rest", kind := .collecting }]] => true
   | _ => false) &&
  (match Algorithm.clauseGroupDefinitionKind [fcClause (.sequenceValue [.sequenceValue [.litInt 0, fcColl "rest"]]) (param "rest")] with
   | .conditional => true
   | _ => false) &&
  (let ordinaryArgs := Algorithm.elaborateClauseGroup [fcClause (.sequenceValue [.bind "head", fcColl "rest"]) (param "rest")]
   let ordinaryTail := Algorithm.elaborateClauseGroup [fcClause (.sequenceValue [.listValue [.bind "head", fcColl "rest"]]) (param "rest")]
   let props := [("TailArgs", ordinaryArgs), ("OrdinaryTail", ordinaryTail), ("Tail", fcTailAlg)]
   -- The ordinary top-level collector still gathers separate arguments.
   spIs props (.listValue [.atom 2, .atom 3]) (.call (resolve "TailArgs") [num 1, num 2, num 3]) &&
   spIs props (.listValue []) (.call (resolve "TailArgs") [num 1]) &&
   -- The nonempty-list pattern means the same alone and beside the empty-list clause.
   spIs props (.listValue [.atom 2, .atom 3]) (.call (resolve "OrdinaryTail") [.listLiteral [num 1, num 2, num 3]]) &&
   spIs props (.listValue [.atom 2, .atom 3]) (.call (resolve "Tail") [.listLiteral [num 1, num 2, num 3]]) &&
   -- Only the mismatch differs: an ordinary binding fails, a family has no matching branch.
   spFails props innermostIsAnyTypeMismatch (.call (resolve "OrdinaryTail") [.capture [num 1, num 2]]) &&
   spFails props (innermostIsNoMatchingBranch "Tail") (.call (resolve "Tail") [.capture [num 1, num 2]]))

#guard wholeGroupClassificationKeepsOrdinaryCollectors

-- 15. THE COLLECTOR RULES OF A FAMILY HEAD are pre-evaluation invariants: no collector
--     directly among the call arguments, at most one collector per pattern level,
--     no repeated name involving a collector, and the singleton rule. Each wins
--     over the failing output row, so nothing is evaluated.
def familyCollectorRulesAreIllegalBeforeEvaluation : Bool :=
  let refused (heads : List Pattern) (expected : String) : Bool :=
    let family := Algorithm.conditional none [] (heads.map (fun head => fcClause head (num 7)))
    match runResult (.algorithmExpr (algPrivate [] [] [("F", family)] [.binary .div (num 1) (num 0)])) with
    | .error (.illegalInEval message) => message == expected
    | _ => false
  -- F(0) = 7 / F(head, *rest) = 7 and F(0) = 7 / F(*xs) = 7: a direct collector.
  refused [.sequenceValue [.litInt 0, .litInt 0], .sequenceValue [.bind "head", fcColl "rest"]]
    KatLang.familyDirectCollectorMessage &&
  refused [.litInt 0, fcColl "xs"] KatLang.familyDirectCollectorMessage &&
  -- A single literal-bearing clause is a family too: F(0, *rest) = 7.
  refused [.sequenceValue [.litInt 0, fcColl "rest"]] KatLang.familyDirectCollectorMessage &&
  -- One collector per level, nested and at the head's own level.
  refused [.sequenceValue [.listValue []], .sequenceValue [.listValue [fcColl "a", .bind "x", fcColl "b"]]]
    KatLang.multipleCollectingBindingsPerLevelMessage &&
  refused [.sequenceValue [.litInt 0, fcColl "a", fcColl "b"]] KatLang.multipleCollectingBindingsPerLevelMessage &&
  -- No repeated name involving a collector, in one level and across levels.
  refused [.sequenceValue [.listValue []], .sequenceValue [.listValue [.bind "x", fcColl "x"]]]
    KatLang.repeatedNameIncludesCollectingMessage &&
  refused [.sequenceValue [.litInt 0, .bind "r", .listValue [fcColl "r"]]]
    KatLang.repeatedNameIncludesCollectingMessage &&
  -- The singleton rule: a group around a collector-only sequence pattern is a one-item sequence pattern.
  refused [.sequenceValue [.litInt 0, .sequenceValue [.sequenceValue [fcColl "xs"]]]]
    KatLang.singletonSequencePatternMessage &&
  -- The collector-only sequence pattern itself is valid in a family and matches every sequence.
  (let any := Algorithm.elaborateClauseGroup [
      fcClause (.sequenceValue [.sequenceValue [fcColl "xs"]]) (param "xs"),
      fcClause (.bind "other") (spLit "other") ]
   spIs [("Any", any)] (.listValue []) (.call (resolve "Any") [.emptySequence 0]) &&
   spIs [("Any", any)] (.listValue [.atom 1, .atom 2]) (.call (resolve "Any") [.capture [num 1, num 2]]) &&
   spIs [("Any", any)] (.str "other") (.call (resolve "Any") [.listLiteral [num 1, num 2]]) &&
   spIs [("Any", any)] (.str "other") (.call (resolve "Any") [num 7]))

#guard familyCollectorRulesAreIllegalBeforeEvaluation

-- 16. Duplicate heads: renamed structurally identical collecting heads are duplicates,
--     while `[x]` and `[*xs]` are distinct heads that dispatch by cardinality.
def collectingHeadsAndDuplicateDetection : Bool :=
  let renamed := Algorithm.conditional none [] [
    fcClause (.sequenceValue [.listValue [.bind "head", fcColl "rest"]]) (num 1),
    fcClause (.sequenceValue [.listValue [.bind "first", fcColl "others"]]) (num 2) ]
  let distinct := Algorithm.elaborateClauseGroup [
    fcClause (.sequenceValue [.listValue [.bind "x"]]) (spLit "one"),
    fcClause (.sequenceValue [.listValue [fcColl "xs"]]) (spLit "any") ]
  spFails [("D", renamed)] spIsDuplicateBranchPattern (.call (resolve "D") [.listLiteral [num 1]]) &&
  spIs [("K", distinct)] (.str "one") (.call (resolve "K") [.listLiteral [num 1]]) &&
  spIs [("K", distinct)] (.str "any") (.call (resolve "K") [.listLiteral []]) &&
  spIs [("K", distinct)] (.str "any") (.call (resolve "K") [.listLiteral [num 1, num 2]]) &&
  spFails [("K", distinct)] (innermostIsNoMatchingBranch "K") (.call (resolve "K") [num 1])

#guard collectingHeadsAndDuplicateDetection

end KatLangTests
