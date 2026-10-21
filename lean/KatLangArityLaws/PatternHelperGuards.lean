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

def clause (pattern : Pattern) (n : Nat) : CondBranch := ⟨pattern, .mk none [] [] [] [.num n]⟩
def family (bs : List CondBranch) : Algorithm := .conditional none [] bs

#guard (family [clause (seq [b "x", b "x"]) 1, clause (seq [b "a", b "b"]) 2,
  clause (seq [b "p", b "p"]) 3]).hasDuplicateBranchPatterns
#guard !(family [clause (seq [b "x", b "x"]) 1, clause (seq [b "a", b "b"]) 1]).hasDuplicateBranchPatterns
#guard !(family [clause (seq [b "x", b "y"]) 1, clause (lst [b "x", b "y"]) 1]).hasDuplicateBranchPatterns

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
