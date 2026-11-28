import KatLangArityLaws.PatternHelpers

open KatLang KatLang.PatternHelpers

/-!
# Executable guards for the R3′ pattern helpers (finite evidence, never theorems)

Concrete witnesses, with independently stated expectations, for the laws of
`KatLangArityLaws.PatternHelpers`: the duplicate relation's repeated-name and kind cases, the
value matcher's environment contract (prepopulated and duplicate-name environments included),
the conversion boundary, and the exact diagnostic text. The universal statements are the
theorems; the preservation comparison against the frozen pre-R3′ `partial` definitions is
separate, bounded evidence (`experimental/features/r3prime-pattern-helper-totalization.md`).
-/

namespace KatLang.PatternHelperGuards

def b (x : Ident) : Pattern := .bind x
/-- A collecting binder `*x` (Q-47). -/
def c (x : Ident) : Pattern := .bind x true
def seq (ps : List Pattern) : Pattern := .sequenceValue ps
def lst (ps : List Pattern) : Pattern := .listValue ps
def cap (x : Ident) (kind : ParameterKind := .normal) : ParameterPattern := .capture { name := x, kind := kind }

def typeMismatchText? : Error → Option String
  | .typeMismatch message => some message
  | _ => none

/-! ## Duplicate comparison: structural equality up to consistent renaming -/

#guard (seq [b "x", b "x"]).isMatchEquivalent (seq [b "a", b "a"])
#guard !(seq [b "x", b "x"]).isMatchEquivalent (seq [b "a", b "b"])
-- A reused right name is rejected: the renaming must be injective.
#guard !(seq [b "x", b "y"]).isMatchEquivalent (seq [b "a", b "a"])
#guard !(seq [b "x", b "y"]).isMatchEquivalent (lst [b "a", b "b"])
#guard !(seq []).isMatchEquivalent (lst [])
-- Repeated-name consistency spans nested siblings.
#guard (seq [lst [b "x"], lst [b "x"]]).isMatchEquivalent (seq [lst [b "a"], lst [b "a"]])
#guard !(seq [lst [b "x"], lst [b "x"]]).isMatchEquivalent (seq [lst [b "a"], lst [b "b"]])
#guard !(seq [lst [b "x"], lst [b "y"]]).isMatchEquivalent (seq [lst [b "a"], lst [b "a"]])
-- Literal payloads and lengths are part of the shape.
#guard (seq [.litInt (-1), b "x"]).isMatchEquivalent (seq [.litInt (-1), b "y"])
#guard !(seq [.litInt 1, b "x"]).isMatchEquivalent (seq [.litInt 2, b "x"])
#guard !(seq [.litBool true, b "x"]).isMatchEquivalent (seq [.litInt 1, b "x"])
#guard !(seq [b "x", b "y"]).isMatchEquivalent (seq [b "x", b "y", b "z"])
-- Not extensional: a binder and a literal match overlapping values but are different shapes.
#guard !(b "x").isMatchEquivalent (.litInt 1)
-- The seeded comparison: complete returned tables, prepended in traversal order.
#guard Pattern.matchEquivalentWithRenaming (seq [b "x", b "y", b "x"]) (seq [b "a", b "b", b "a"]) []
  == some [("y", "b"), ("x", "a")]
#guard Pattern.matchEquivalentWithRenaming (b "x") (b "c") [("x", "c"), ("x", "d")] == some [("x", "c"), ("x", "d")]
#guard Pattern.matchEquivalentWithRenaming (b "x") (b "d") [("x", "c"), ("x", "d")] == none
#guard Pattern.matchEquivalentWithRenaming (b "y") (b "d") [("x", "c"), ("x", "d")] == none

-- The collecting flag is part of the shape (Q-47): renamed collecting heads are duplicates, a
-- fixed binder never meets a collecting one, and the collector's POSITION distinguishes heads.
#guard (lst [b "head", c "rest"]).isMatchEquivalent (lst [b "first", c "others"])
#guard !(lst [b "x"]).isMatchEquivalent (lst [c "xs"])
#guard !(lst [c "xs"]).isMatchEquivalent (lst [b "x"])
#guard !(lst [b "x", c "r"]).isMatchEquivalent (lst [c "r", b "x"])
#guard !(lst [b "x", c "r"]).isMatchEquivalent (seq [b "x", c "r"])
#guard (seq [.litString "packet", c "fields", .litString "end"]).isMatchEquivalent
  (seq [.litString "packet", c "payload", .litString "end"])
#guard !(seq [.litString "packet", c "fields", .litString "end"]).isMatchEquivalent
  (seq [.litString "packet", c "fields", .litString "stop"])
#guard Pattern.matchEquivalentWithRenaming (lst [b "h", c "t"]) (lst [b "a", c "z"]) [] == some [("t", "z"), ("h", "a")]
#guard Pattern.matchEquivalentWithRenaming (c "t") (b "z") [] == none

def clause (pattern : Pattern) (n : Nat) : CondBranch := ⟨pattern, .mk none [] [] [] [.num n]⟩
def family (bs : List CondBranch) : Algorithm := .conditional none [] bs

#guard (family [clause (seq [b "x", b "x"]) 1, clause (seq [b "a", b "b"]) 2,
  clause (seq [b "p", b "p"]) 3]).hasDuplicateBranchPatterns
#guard !(family [clause (seq [b "x", b "x"]) 1, clause (seq [b "a", b "b"]) 1]).hasDuplicateBranchPatterns
#guard !(family [clause (seq [b "x", b "y"]) 1, clause (lst [b "x", b "y"]) 1]).hasDuplicateBranchPatterns
#guard (family [clause (seq [lst []]) 1, clause (seq [lst [b "head", c "rest"]]) 2,
  clause (seq [lst [b "first", c "others"]]) 3]).hasDuplicateBranchPatterns
#guard !(family [clause (seq [lst []]) 1, clause (seq [lst [b "x"]]) 2, clause (seq [lst [c "xs"]]) 3]).hasDuplicateBranchPatterns

/-! ## Value matching: the environment contract -/

#guard matchPattern (seq [b "x", b "x"]) (.sequenceValue [.atom 1, .atom 1]) == some [("x", .atom 1)]
#guard matchPattern (seq [b "x", b "x"]) (.sequenceValue [.atom 1, .atom 2]) == none
#guard matchPattern (seq [b "x", lst [b "y", b "x"]]) (.sequenceValue [.atom 1, .listValue [.str "s", .atom 1]])
  == some [("x", .atom 1), ("y", .str "s")]
-- No truthiness, coercion or kind adaptation.
#guard matchPattern (.litBool true) (.atom 1) == none
#guard matchPattern (.litInt 1) (.bool true) == none
#guard matchPattern (.litString "1") (.atom 1) == none
#guard matchPattern (.litInt (-3)) (.atom (-3)) == some []
#guard matchPattern (seq [b "x", b "y"]) (.listValue [.atom 1, .atom 2]) == none
#guard matchPattern (lst [b "x"]) (.sequenceValue [.atom 1]) == none
#guard matchPattern (lst [b "x"]) (.atom 1) == none
#guard matchPattern (seq [b "x", b "y"]) (.sequenceValue [.atom 1, .atom 2, .atom 3]) == none
#guard matchPattern (lst []) (.listValue []) == some []
#guard matchPattern (seq []) (.listValue []) == none
-- A prepopulated environment keeps its entries, duplicates and lookup precedence.
#guard matchPatternInto (b "x") (.atom 1) [("x", .atom 1), ("x", .atom 2)] == some [("x", .atom 1), ("x", .atom 2)]
#guard matchPatternInto (b "x") (.atom 2) [("x", .atom 1), ("x", .atom 2)] == none
#guard matchPatternInto (seq [b "y", b "z"]) (.sequenceValue [.atom 5, .atom 6]) [("z", .atom 6)]
  == some [("z", .atom 6), ("y", .atom 5)]
-- The direct structure helper keeps its distinctions.
#guard matchStructureInto [b "x"] none [] == none
#guard matchStructureInto [] (some []) [("k", .atom 0)] == some [("k", .atom 0)]
#guard matchStructureInto [b "x", b "y"] (some [.atom 1]) [] == none
#guard matchStructureInto [b "x"] (some [.atom 1, .atom 2]) [] == none
-- A collecting binder is no value pattern: only the need binder allocates its slice (Q-47).
#guard matchPattern (c "xs") (.listValue [.atom 1]) == none
#guard matchPattern (lst [b "h", c "t"]) (.listValue [.atom 1, .atom 2]) == none
-- A raw one-item sequence (rejected earlier by source admission) keeps its current result.
#guard matchPattern (seq [b "x"]) (.sequenceValue [.atom 4]) == some [("x", .atom 4)]
#guard matchPattern (seq [b "x"]) (.atom 4) == none

/-! ## Conversion and captures -/

#guard (seq [b "x", lst [b "y"]]).parameterPattern?.map ParameterPattern.displayName == some "(x, [y])"
#guard (seq [b "x", .litInt 1]).parameterPattern? |>.isNone
#guard (seq [b "x", seq [b "y", b "z"]]).plainClauseParameterPatterns?.map (·.map ParameterPattern.displayName)
  == some ["x", "(y, z)"]
#guard (lst [b "x", b "y"]).plainClauseParameterPatterns?.map (·.map ParameterPattern.displayName)
  == some ["[x, y]"]
#guard (seq [b "x", lst [b "x", b "y"]]).plainClauseParamNames? == some ["x", "x", "y"]
-- A collecting binder converts to a collecting capture, at the top of a sole head and nested (Q-47).
#guard (seq [b "head", c "rest"]).plainClauseParameterPatterns?.map (·.map ParameterPattern.displayName)
  == some ["head", "*rest"]
#guard (seq [lst [b "head", c "rest"]]).plainClauseParameterPatterns?.map (·.map ParameterPattern.displayName)
  == some ["[head, *rest]"]
#guard (c "xs").plainClauseParameterPatterns?.map (·.map ParameterPattern.displayName) == some ["*xs"]
#guard (seq [.litInt 0, lst [c "xs"]]).plainClauseParameterPatterns?.isNone
#guard (clauseCaptures (seq [b "a", lst [b "b", c "r"], .litInt 0])).map CallableParameter.displayName == ["a", "b", "*r"]

/-! ## The collector rules of a clause head (Q-47) -/

-- A collector directly among the head's call arguments, or a head that is itself one.
#guard (seq [b "head", c "rest"]).headHasDirectCollector
#guard (c "xs").headHasDirectCollector
#guard !(seq [lst [b "head", c "rest"]]).headHasDirectCollector
#guard !(seq [seq [b "head", c "rest"], b "y"]).headHasDirectCollector
#guard !(lst [c "xs"]).headHasDirectCollector
-- One collector per level: the head's own list and every nested group are levels.
#guard (seq [lst [c "a", c "b"]]).hasMultipleCollectingLevel
#guard (seq [c "a", c "b"]).hasMultipleCollectingLevel
#guard (seq [b "x", seq [b "y", lst [c "a", b "z", c "b"]]]).hasMultipleCollectingLevel
#guard !(seq [lst [c "a"], lst [c "b"]]).hasMultipleCollectingLevel
#guard !(seq [lst [b "x", c "a", seq [c "b"]]]).hasMultipleCollectingLevel
-- No repeated name involving a collector, at any depth.
#guard (seq [lst [b "x", c "x"]]).hasRepeatedNameIncludingCollecting
#guard (seq [b "r", lst [c "r"]]).hasRepeatedNameIncludingCollecting
#guard (seq [lst [c "r"], lst [c "r"]]).hasRepeatedNameIncludingCollecting
#guard !(seq [b "x", lst [b "x", c "r"]]).hasRepeatedNameIncludingCollecting
#guard !(seq [lst [c "a"], lst [c "b"]]).hasRepeatedNameIncludingCollecting
-- The singleton rule: a collector-only sequence pattern is valid, a group around it is not.
#guard !(seq [seq [c "xs"]]).headHasSingletonSequenceGroup
#guard (seq [seq [seq [c "xs"]]]).headHasSingletonSequenceGroup
#guard (seq [seq [b "x"]]).headHasSingletonSequenceGroup
#guard !(seq [seq [b "x", c "xs"]]).headHasSingletonSequenceGroup
-- The collecting kind reaches the binder: only a head without a direct collector has a fixed arity.
#guard needAcceptsCardinality (needClauseHead (seq [lst [b "head", c "rest"]])) 1
#guard !needAcceptsCardinality (needClauseHead (seq [lst [b "head", c "rest"]])) 2
#guard !needAcceptsCardinality (needClauseHead (seq [lst [b "head", c "rest"]])) 0
#guard needAcceptsCardinality (needClauseHead (seq [b "head", c "rest"])) 5
#guard (ParameterPattern.sequenceValue [cap "a", .listValue [cap "b", cap "r" .collecting], cap "m" .metaRef]).captures.map
  CallableParameter.displayName == ["a", "b", "*r", "meta m"]

/-! ## Rendering: exact text -/

#guard (ParameterPattern.unpacking [cap "x", cap "rest" .collecting, cap "z"]).displayName == "x, *rest, z"
#guard (ParameterPattern.sequenceValue [cap "x", .listValue [], .sequenceValue []]).displayName == "(x, [], ())"
#guard (cap "r" .metaRef).displayName == "meta r"
#guard resultDiagnosticString (.sequenceValue []) == "()"
#guard resultDiagnosticString (.listValue []) == "[]"
#guard resultDiagnosticString (.listValue [.atom (-3), .str "it's", .bool false, .sequenceValue [.atom 1, .atom 2]])
  == "[-3, 'it's', false, (1, 2)]"
#guard resultDiagnosticString (.listValue [.callRef 7, .argView 7]) == "[a call reference, an argument view]"
#guard operandDescription (.listValue [.atom 1]) == "a list value with 1 element: [1]"
#guard operandDescription (.listValue []) == "a list value with 0 elements: []"
#guard operandDescription (.sequenceValue [.atom 1, .str "a"]) == "a sequence value with 2 sequence elements: (1, 'a')"
#guard typeMismatchText? (structuralPatternKindMismatch (.sequenceValue [cap "x", cap "y"]) (.atom 5))
  == some "sequence pattern `(x, y)` expects a sequence value, but received numeric value 5"
#guard typeMismatchText? (structuralPatternKindMismatch (.listValue [cap "x", cap "r" .collecting]) (.sequenceValue []))
  == some "list pattern `[x, *r]` expects a list value, but received a sequence value with 0 sequence elements: ()"
-- Direct calls outside the binder's domain keep the current payload.
#guard typeMismatchText? (structuralPatternKindMismatch (.unpacking [cap "x", cap "y"]) (.bool true))
  == some "sequence pattern `x, y` expects a sequence value, but received a Boolean value: true"
#guard typeMismatchText? (structuralPatternKindMismatch (cap "x") (.callRef 0))
  == some "sequence pattern `x` expects a sequence value, but received a call reference"

end KatLang.PatternHelperGuards
