import KatLang
import CoreTests.Common

--------------------------------------------------------------------------------
-- EMPTY STRUCTURAL PATTERNS ARE VALID, DISTINCT HEADS (PAT-05 with PAT-06)
--------------------------------------------------------------------------------
-- PAT-05 as corrected on 2026-10-09: patterns use the pattern grammar, not general
-- expression syntax (an arithmetic expression such as `1 + 1` is not a pattern), and
-- the empty sequence pattern `()` and the empty list pattern `[]` are valid, distinct
-- structural patterns, each matching only the empty value of its own kind (PAT-06).
-- Lean's `Pattern` has no expression constructor at all — binders, the three literal
-- kinds, and the two structural kinds only — so the front-end rejection of
-- `F(1 + 1) = 2` has no elaborated Lean program; the C# parser diagnostics are pinned
-- by `EmptyStructuralPatternLawTests`. These guards evaluate the production model on
-- the elaborated ASTs of the source witnesses (families and ordinary single clauses),
-- and check the static head relations (duplicates, singleton groups) the front end
-- shares with the model. Spec case: `empty-structural-patterns-are-distinct-heads`.

namespace KatLangTests.EmptyStructuralPatterns
open KatLang

private def run (props : List (Prod Ident Algorithm)) (out : List Expr) : Except Error Result :=
  runResult (.algorithmExpr (algPrivate [] [] props out))

private def yields (props : List (Prod Ident Algorithm)) (out : List Expr) (expected : Result) : Bool :=
  match run props out with
  | .ok value => value == expected
  | _ => false

private def fails (props : List (Prod Ident Algorithm)) (out : List Expr) (classify : Error -> Bool) : Bool :=
  match run props out with
  | .error err => classify err
  | _ => false

private def lit (s : String) : Expr := .stringLiteral s
private def emptySeq : Expr := .emptySequence 0
private def emptyList : Expr := .listLiteral []
private def call (name : Ident) (args : List Expr) : Expr := .call (.resolve name) args
private def family (clauses : List (Prod Pattern Expr)) : Algorithm :=
  .conditional none [] (clauses.map fun (pattern, body) => ⟨pattern, alg [] [] [] [body]⟩)

-- A clause head over one argument: `F(p)` is the head `.sequenceValue [p]`.
private def head (p : Pattern) : Pattern := .sequenceValue [p]

-- 1. The canonical witnesses ------------------------------------------------------

-- P1: F(()) = 1 / F(x) = 2 / F(()), F(5)
private def p1 : Algorithm := family [(head (.sequenceValue []), .num 1), (.bind "x", .num 2)]
#guard yields [("F", p1)] [call "F" [emptySeq], call "F" [.num 5]] (.sequenceValue [.atom 1, .atom 2])

-- P2: F([]) = 1 / F(x) = 2 / F([]), F(5)
private def p2 : Algorithm := family [(head (.listValue []), .num 1), (.bind "x", .num 2)]
#guard yields [("F", p2)] [call "F" [emptyList], call "F" [.num 5]] (.sequenceValue [.atom 1, .atom 2])

-- P3: one family, both empty heads, and a catch-all.
private def kind : Algorithm :=
  family [(head (.sequenceValue []), lit "empty sequence"), (head (.listValue []), lit "empty list"), (.bind "x", lit "other")]
#guard yields [("Kind", kind)] [call "Kind" [emptySeq], call "Kind" [emptyList], call "Kind" [.num 0]]
  (.sequenceValue [.str "empty sequence", .str "empty list", .str "other"])

-- 2. The two empty patterns never match the other kind ------------------------------

-- P3a/P3b: `[]` never matches `()`, and `()` never matches `[]`.
#guard yields [("F", p1)] [call "F" [emptyList]] (.atom 2)
#guard yields [("G", p2)] [call "G" [emptySeq]] (.atom 2)
-- P3c/P3d: two different heads, no catch-all: each selects its own kind; anything else
-- is the family's NoMatchingBranch.
private def both : Algorithm := family [(head (.sequenceValue []), .num 1), (head (.listValue []), .num 2)]
#guard yields [("H", both)] [call "H" [emptySeq], call "H" [emptyList]] (.sequenceValue [.atom 1, .atom 2])
#guard fails [("H", both)] [call "H" [.num 0]] (innermostIsNoMatchingBranch "H")
-- Value, not spelling: a property holding `()` and a computed `[]` select by kind.
#guard yields [("A", alg [] [] [] [emptySeq]), ("F", p1)]
  [call "F" [.resolve "A"], call "F" [call "take" [.capture [.num 1, .num 2], .num 0]]]
  (.sequenceValue [.atom 1, .atom 2])
#guard yields [("F", p2)] [call "F" [call "take" [.capture [.num 1, .num 2], .num 0]]] (.atom 1)

-- 3. A single clause is an ordinary algorithm: kind and length fail the binding ------

private def ordinary (p : ParameterPattern) : Algorithm := algWithParameterPatterns [p] [] [] [.num 1]
-- P3e..P3h: E(()) = 1
#guard yields [("E", ordinary (.sequenceValue []))] [call "E" [emptySeq]] (.atom 1)
#guard fails [("E", ordinary (.sequenceValue []))] [call "E" [emptyList]] innermostIsAnyTypeMismatch
#guard fails [("E", ordinary (.sequenceValue []))] [call "E" [.capture [.num 1, .num 2]]] (innermostIsArityMismatch 0 2)
#guard fails [("E", ordinary (.sequenceValue []))] [call "E" [.num 5]] innermostIsAnyTypeMismatch
-- P3i..P3k: L([]) = 1
#guard yields [("L", ordinary (.listValue []))] [call "L" [emptyList]] (.atom 1)
#guard fails [("L", ordinary (.listValue []))] [call "L" [emptySeq]] innermostIsAnyTypeMismatch
#guard fails [("L", ordinary (.listValue []))] [call "L" [.listLiteral [.num 7]]] (innermostIsArityMismatch 0 1)
-- P3l/P3m: an empty pattern beside a binder: G((), y) = y and G([], y) = y.
#guard yields [("G", algWithParameterPatterns [.sequenceValue [], .capture { name := "y" }] [] [] [.param "y"])]
  [call "G" [emptySeq, .num 5]] (.atom 5)
#guard yields [("G", algWithParameterPatterns [.listValue [], .capture { name := "y" }] [] [] [.param "y"])]
  [call "G" [emptyList, .num 5]] (.atom 5)

-- 4. Nested empties keep their kind at every level --------------------------------

-- P5d: F([[]]) = 1 / F(x) = 2 — `[[]]`, `[]`, `[()]`.
#guard yields [("F", family [(head (.listValue [.listValue []]), .num 1), (.bind "x", .num 2)])]
  [call "F" [.listLiteral [emptyList]], call "F" [emptyList], call "F" [.listLiteral [emptySeq]]]
  (.sequenceValue [.atom 1, .atom 2, .atom 2])
-- P5f: F(((), [])) = 1 / F(x) = 2 — the pair's elements are checked by kind, in order.
#guard yields [("F", family [(head (.sequenceValue [.sequenceValue [], .listValue []]), .num 1), (.bind "x", .num 2)])]
  [call "F" [.capture [emptySeq, emptyList]], call "F" [.capture [emptyList, emptySeq]], call "F" [.capture [emptySeq, emptySeq]]]
  (.sequenceValue [.atom 1, .atom 2, .atom 2])
-- P5k: K(([], x)) / K(((), x)) / K(y): the inner empty pattern selects the clause.
#guard yields [("K", family [(head (.sequenceValue [.listValue [], .bind "x"]), lit "list-first"),
      (head (.sequenceValue [.sequenceValue [], .bind "x"]), lit "seq-first"), (.bind "y", lit "other")])]
  [call "K" [.capture [emptyList, .num 1]], call "K" [.capture [emptySeq, .num 1]], call "K" [.capture [.num 1, .num 1]]]
  (.sequenceValue [.str "list-first", .str "seq-first", .str "other"])
-- P5l: in an ordinary definition the inner kind fails the binding.
#guard fails [("N", algWithParameterPatterns [.sequenceValue [.listValue [], .capture { name := "x" }]] [] [] [.param "x"])]
  [call "N" [.capture [emptySeq, .num 5]]] innermostIsAnyTypeMismatch
-- P5m: callback elements dispatch through the same family heads.
#guard yields [("F", family [(head (.listValue []), .num 0), (head (.listValue [.bind "x"]), .num 1), (.bind "xs", .num 2)])]
  [call "map" [.listLiteral [emptyList, .listLiteral [.num 5], emptySeq, .num 7], .resolve "F"]]
  (.listValue [.atom 0, .atom 1, .atom 2, .atom 2])

-- 5. Static head relations --------------------------------------------------------

-- `()` and `[]` are different heads; two equal empty heads are duplicates.
#guard !(head (.sequenceValue [])).isMatchEquivalent (head (.listValue []))
#guard (head (.sequenceValue [])).isMatchEquivalent (head (.sequenceValue []))
#guard (head (.listValue [])).isMatchEquivalent (head (.listValue []))
#guard !both.hasDuplicateBranchPatterns
#guard (family [(head (.sequenceValue []), .num 1), (head (.sequenceValue []), .num 2)]).hasDuplicateBranchPatterns
#guard (family [(head (.listValue []), .num 1), (head (.listValue []), .num 2)]).hasDuplicateBranchPatterns
-- An empty pattern is not a singleton group; a sequence group whose ONE item is an empty
-- pattern is (`F((()))` and `F(([]))` are the front end's SingletonSequencePattern).
#guard !(head (.sequenceValue [])).headHasSingletonSequenceGroup
#guard !(head (.listValue [])).headHasSingletonSequenceGroup
#guard (head (.sequenceValue [.sequenceValue []])).headHasSingletonSequenceGroup
#guard (head (.sequenceValue [.listValue []])).headHasSingletonSequenceGroup
#guard !(head (.listValue [.listValue []])).headHasSingletonSequenceGroup

end KatLangTests.EmptyStructuralPatterns
