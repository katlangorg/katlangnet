import KatLang
import CoreTests.Common

namespace KatLangTests
open KatLang (alg algWithParameters algWithParameterPatterns algPrivate privateProp publicProp privateLocalProp publicLocalProp runFlat runResult Algorithm Error Result PropExposure)
open KatLang (resolve param num)

--------------------------------------------------------------------------------
-- Conditional algorithm tests
--------------------------------------------------------------------------------

open KatLang (Pattern CondBranch)

-- Test 22: K combinator via conditional algorithm
-- K(a, b) = a  →  K(10, 20) => 10
def kAlg : Algorithm :=
  .conditional none [] [
    ⟨ .sequenceValue [.bind "a", .bind "b"],
      alg [] [] [] [.param "a"] ⟩
  ]

def test34 : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("K", kAlg)] [
    .call (resolve "K") [.num 10, .num 20]
  ])) with
  | Except.ok [10] => true
  | _ => false

#guard test34
#eval runFlat (.algorithmExpr (algPrivate [] [] [("K", kAlg)] [
  .call (resolve "K") [.num 10, .num 20]
]))

-- Test 35: Multiple branches with literal match
-- Else(1, (a, b)) = a
-- Else(c, (a, b)) = b
def elseAlg : Algorithm :=
  .conditional none [] [
    ⟨ .sequenceValue [.litInt 1, .sequenceValue [.bind "a", .bind "b"]],
      alg [] [] [] [.param "a"] ⟩,
    ⟨ .sequenceValue [.bind "c", .sequenceValue [.bind "a", .bind "b"]],
      alg [] [] [] [.param "b"] ⟩
  ]

-- Else(1, (2, 3)) → first branch matches → a = 2
def test35a : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("Else", elseAlg)] [
    .call (resolve "Else") [.num 1, .capture [.num 2, .num 3]]
  ])) with
  | Except.ok [2] => true
  | _ => false

#guard test35a

-- Else(0, (2, 3)) → second branch matches → b = 3
def test35b : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("Else", elseAlg)] [
    .call (resolve "Else") [.num 0, .capture [.num 2, .num 3]]
  ])) with
  | Except.ok [3] => true
  | _ => false

#guard test35b

-- Test 36: Non-exhaustive — no match → error
-- Sign(1) = 1; Sign(-1) = -1;  Sign(0) → noMatchingBranch
def signAlg : Algorithm :=
  .conditional none [] [
    ⟨ .litInt 1,  alg [] [] [] [.num 1] ⟩,
    ⟨ .litInt (-1), alg [] [] [] [.num (-1)] ⟩
  ]

def test36 : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("Sign", signAlg)] [
    .call (resolve "Sign") [.num 0]
  ])) with
  | Except.error _ => true    -- noMatchingBranch
  | Except.ok _    => false

#guard test36

-- Test 37: First-match-wins
-- F(x) = 1  (catch-all, always matches)
-- F(1) = 2  (never reached)
-- F(1) → 1
def firstMatchAlg : Algorithm :=
  .conditional none [] [
    ⟨ .bind "x", alg [] [] [] [.num 1] ⟩,
    ⟨ .litInt 1,  alg [] [] [] [.num 2] ⟩
  ]

def test37 : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("F", firstMatchAlg)] [
    .call (resolve "F") [.num 1]
  ])) with
  | Except.ok [1] => true
  | _ => false

#guard test37

-- Test 22: 2-arg if is rejected
def test22 : Bool :=
  match runResult (.call (resolve "if") [.num 1, .num 5]) with
  | Except.error _ => true
  | Except.ok _ => false

#guard test22
#eval runResult (.call (resolve "if") [.num 1, .num 5])

-- Test 23: 2-arg if in addition is rejected
def test23 : Bool :=
  match runResult (.binary .add (.num 10) (.call (resolve "if") [.num 1, .num 5])) with
  | Except.error _ => true
  | Except.ok _ => false

#guard test23
#eval runResult (.binary .add (.num 10) (.call (resolve "if") [.num 1, .num 5]))

-- Test 24: 2-arg if in multiplication is rejected
def test24 : Bool :=
  match runResult (.binary .mul (.num 10) (.call (resolve "if") [
    .binary .lt (.num 7) (.num 6),
    .num 1
  ])) with
  | Except.error _ => true
  | Except.ok _ => false

#guard test24
#eval runResult (.binary .mul (.num 10) (.call (resolve "if") [
  .binary .lt (.num 7) (.num 6),
  .num 1
]))

-- The `if` arity payload is NORMATIVE: `if` requires exactly three arguments,
-- so every reachable `if` arity failure carries expected = 3 (never the
-- generic-builtin placeholder 0) with actual = the assembled argument count.
-- Dot-call reproducers (`A = 1` / `A.if(2)`): the receiver is one leading
-- argument, so the assembled arities are 2 and 4. C# twin:
-- IfBuiltinArityPayloadTests (`WrongBuiltinArity` populates expected 3 for
-- `if` alone; other builtins keep the placeholder on both sides).
def ifDotCallUnderArityProgram : KatLang.Expr :=
  .algorithmExpr (algPrivate [] [] [("A", alg [] [] [] [.num 1])] [
    .dotCall (resolve "A") "if" (some [.num 2])
  ])

def ifDotCallUnderArityCarriesExpectedThree : Bool :=
  match runResult ifDotCallUnderArityProgram with
  | Except.error err =>
      hasContext "while evaluating dotCall .if of A" err
        && hasContext "expected 3 arguments" err
        && innermostIsArityMismatch 3 2 err
  | Except.ok _ => false

#guard ifDotCallUnderArityCarriesExpectedThree
#eval runResult ifDotCallUnderArityProgram

def ifDotCallOverArityProgram : KatLang.Expr :=
  .algorithmExpr (algPrivate [] [] [("A", alg [] [] [] [.num 1])] [
    .dotCall (resolve "A") "if" (some [.num 2, .num 3, .num 4])
  ])

def ifDotCallOverArityCarriesExpectedThree : Bool :=
  match runResult ifDotCallOverArityProgram with
  | Except.error err =>
      hasContext "while evaluating dotCall .if of A" err
        && hasContext "expected 3 arguments" err
        && innermostIsArityMismatch 3 4 err
  | Except.ok _ => false

#guard ifDotCallOverArityCarriesExpectedThree
#eval runResult ifDotCallOverArityProgram

-- Exactly three assembled arguments through the same dot-call surface still
-- dispatch: `A.if(20, 30)` is `if(A, 20, 30)` = `if(1, 20, 30)` → 20.
def ifDotCallExactArityStillDispatches : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("A", alg [] [] [] [.num 1])] [
    .dotCall (resolve "A") "if" (some [.num 20, .num 30])
  ])) with
  | Except.ok [20] => true
  | _ => false

#guard ifDotCallExactArityStillDispatches

-- Test 25: Spread of an internal constructed sequence `(1, if(0, 2, 9), 3)*` with a
-- 3-arg if that selects the else branch → [1, 9, 3]
def test25 : Bool :=
  match runFlat (sequenceSpread (.sequenceConstruct (.sequenceConstruct (.num 1) (.call (resolve "if") [.num 0, .num 2, .num 9])) (.num 3))) with
  | Except.ok [1, 9, 3] => true
  | _ => false

#guard test25
#eval runFlat (sequenceSpread (.sequenceConstruct (.sequenceConstruct (.num 1) (.call (resolve "if") [.num 0, .num 2, .num 9])) (.num 3)))

-- Internal sequence `(1, 2, 3, 4)*`: spread over the constructed sequence value.
def sequenceSpread1234 : KatLang.Expr :=
  sequenceSpread (.sequenceConstruct (.sequenceConstruct (.sequenceConstruct (.num 1) (.num 2)) (.num 3)) (.num 4))

def test25a : Bool :=
  let sequence1234 := .sequenceConstruct (.sequenceConstruct (.sequenceConstruct (.num 1) (.num 2)) (.num 3)) (.num 4)
  match runFlat (.algorithmExpr (alg [] [] [] [
    .call (resolve "sum") [sequence1234],
    .call (resolve "count") [sequence1234],
    .call (resolve "first") [sequence1234],
    .call (resolve "last") [sequence1234]
  ])) with
  | Except.ok [10, 4, 1, 4] => true
  | _ => false

#guard test25a

def test25b : Bool :=
  -- Internal constructed-sequence variants of `count(((1, 2)*, 3))` and
  -- `count((1, (2, 3)*))`: a flattening spread contributes inside the one
  -- sequence-valued argument.
  match runFlat (.algorithmExpr (alg [] [] [] [
    .call (resolve "count") [
      sequenceItems [sequenceSpread (.capture [.num 1, .num 2]), .num 3]
    ],
    .call (resolve "count") [
      sequenceItems [.num 1, sequenceSpread (.capture [.num 2, .num 3])]
    ]
  ])) with
  | Except.ok [3, 3] => true
  | _ => false

#guard test25b

def test25bNestedSequenceValues : Bool :=
  let nestedLeft := .sequenceConstruct (sequenceSpread (.capture [.capture [.num 1, .num 2]])) (.num 3)
  let nestedMiddle := .sequenceConstruct (sequenceSpread (.capture [.num 1, .capture [.num 2, .num 3]])) (.num 4)
  match runResult (.algorithmExpr (alg [] [] [] [nestedLeft, nestedMiddle])) with
  | Except.ok value =>
      value == Result.sequenceValue [
        Result.sequenceValue [Result.atom 1, Result.atom 2, Result.atom 3],
        Result.sequenceValue [Result.atom 1, Result.sequenceValue [Result.atom 2, Result.atom 3], Result.atom 4]
      ]
  | _ => false

#guard test25bNestedSequenceValues

def sequenceSpreadNamedSequenceValueOperandPreservesBoundary : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [
    ("A", alg [] [] [] [.capture [.num 1, .num 2]])
  ] [
    .sequenceConstruct (sequenceSpread (resolve "A")) (.num 3)
  ])) with
  | Except.ok (.sequenceValue [.atom 1, .atom 2, .atom 3]) => true
  | _ => false

#guard sequenceSpreadNamedSequenceValueOperandPreservesBoundary

def test25bCommaSimilarity : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("A", alg [] [] [] [.num 1, .num 2]),
    ("B", alg [] [] [] [sequenceSpread (.sequenceConstruct (.num 1) (.num 2))])
  ] [
    .dotCall (resolve "A") "count" none,
    .dotCall (resolve "B") "count" none
  ])) with
  | Except.ok [2, 2] => true
  | _ => false

#guard test25bCommaSimilarity

def test25c : Bool :=
  -- Internal sequence `(P*, 3, 4, 5)` where P = 1, 2 is ONE collection argument,
  -- opened by the post-binding one-level collection view; sum 15.
  let pThenMore := sequenceItems [sequenceSpread (resolve "P"), .num 3, .num 4, .num 5]
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("P", alg [] [] [] [.num 1, .num 2]),
    ("X", alg [] [] [] [.call (resolve "sum") [pThenMore]])
  ] [
    resolve "X"
  ])) with
  | Except.ok [15] => true
  | _ => false

#guard test25c

def test25dResultShape : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [
    ("A", alg [] [] [] [.num 1, .num 2]),
    ("F", alg ["a"] [] [] [.param "a", .num 3])
  ] [
    .dotCall (resolve "A") "F" none
  ])) with
  | Except.ok value =>
      value == Result.sequenceValue [Result.sequenceValue [Result.atom 1, Result.atom 2], Result.atom 3]
  | _ => false

#guard test25dResultShape

def test25e : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("A", alg [] [] [] [.num 1, .num 2]),
    ("F", alg ["a"] [] [] [.sequenceConstruct (sequenceSpread (.param "a")) (.num 3)])
  ] [
    .dotCall (resolve "A") "F" none
  ])) with
  | Except.ok [1, 2, 3] => true
  | _ => false

#guard test25e

def test25f : Bool :=
  let a := alg [] [] [publicProp "X" (alg [] [] [] [.num 1])] [.num 10]
  let b := alg [] [] [publicProp "Y" (alg [] [] [] [.num 2])] [.num 20]
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("A", a),
    ("B", b),
    ("C", alg [] [] [] [.sequenceConstruct (sequenceSpread (resolve "A")) (sequenceSpread (resolve "B"))])
  ] [
    resolve "C"
  ])) with
  | Except.ok [10, 20] => true
  | _ => false

#guard test25f

def test25g : Bool :=
  let a := alg [] [] [publicProp "X" (alg [] [] [] [.num 1])] [.num 10]
  let b := alg [] [] [publicProp "Y" (alg [] [] [] [.num 2])] [.num 20]
  match runFlat (.algorithmExpr (algPrivate [] [] [
    ("A", a),
    ("B", b),
    ("C", alg [] [] [] [.sequenceConstruct (sequenceSpread (resolve "A")) (sequenceSpread (resolve "B"))])
  ] [
    .dotCall (resolve "C") "X" none
  ])) with
  | Except.error err => innermostIsUnknownName "X" err
  | _ => false

#guard test25g

-- A spread of a no-output operand fails with the spread
-- missing-output diagnostic: source `bad*` is `sequenceSpread bad`, whose
-- single operand produces no output. The direct `.algorithmExpr` operand reports
-- the spread-specific error, exactly like a resolved operand (T4-2).
def test25h : Bool :=
  let bad := .algorithmExpr (alg [] [] [privateProp "X" (alg [] [] [] [.num 1])] [])
  match runFlat (sequenceSpread bad) with
  | Except.error err => innermostIsSpreadMissingOutput err
  | _ => false

#guard test25h

-- A spread is not a valid open target. Source `open A*`
-- is the spread node `sequenceSpread (resolve "A")`, rendered `A*`.
def test25j : Bool :=
  let a := alg [] [] [publicProp "X" (alg [] [] [] [.num 1])] []
  let b := alg [] [] [publicProp "Y" (alg [] [] [] [.num 2])] []
  match runFlat (.algorithmExpr (algPrivate [] [sequenceSpread (resolve "A")] [
    ("A", a),
    ("B", b)
  ] [
    .binary .add (resolve "X") (resolve "Y")
  ])) with
  | Except.error err => innermostIsBadOpenForm "spread: A*" err
  | _ => false

#guard test25j

-- Test 26: Nested 3-arg if uses the selected inner branch
-- if(1, if(1, 5, 6), 9) → [5]
def test26 : Bool :=
  match runFlat (.call (resolve "if") [
    .num 1,
    .call (resolve "if") [.num 1, .num 5, .num 6],
    .num 9
  ]) with
  | Except.ok [5] => true
  | _ => false

#guard test26

-- Test 27: Nested 3-arg if uses the outer else branch
-- if(0, if(1, 5, 6), 9) → [9]
def test27 : Bool :=
  match runFlat (.call (resolve "if") [
    .num 0,
    .call (resolve "if") [.num 1, .num 5, .num 6],
    .num 9
  ]) with
  | Except.ok [9] => true
  | _ => false

#guard test27

-- Test 28: 3-arg if still works — if(1, 10, 20) → [10]
def test28 : Bool :=
  match runFlat (.call (resolve "if") [.num 1, .num 10, .num 20]) with
  | Except.ok [10] => true
  | _ => false

#guard test28

-- Test 29: 3-arg if false → if(0, 10, 20) → [20]
def test29 : Bool :=
  match runFlat (.call (resolve "if") [.num 0, .num 10, .num 20]) with
  | Except.ok [20] => true
  | _ => false

#guard test29

-- Test 30: 3-arg if with non-zero condition → true
-- if(42, 7, 9) → [7]
def test30 : Bool :=
  match runFlat (.call (resolve "if") [.num 42, .num 7, .num 9]) with
  | Except.ok [7] => true
  | _ => false

#guard test30

-- Test 31: 3-arg if with negative condition → true
-- if(-1, 7, 9) → [7]
def test31 : Bool :=
  match runFlat (.call (resolve "if") [.num (-1), .num 7, .num 9]) with
  | Except.ok [7] => true
  | _ => false

#guard test31

--------------------------------------------------------------------------------
-- Conditional algorithms in value position fail like no-arg dot-call access
--------------------------------------------------------------------------------

def valueAccessConditionalAlg : Algorithm :=
  .conditional none [] [
    ⟨ .litInt 0, alg [] [] [] [.num 0] ⟩,
    ⟨ .bind "x", alg [] [] [] [.num 1] ⟩
  ]

-- Sanity: calling the conditional still selects branches normally.
def conditionalDirectCallStillSelectsBranch : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("F", valueAccessConditionalAlg)] [
    .call (resolve "F") [.num 0],
    .call (resolve "F") [.num 7]
  ])) with
  | Except.ok [0, 1] => true
  | _ => false

#guard conditionalDirectCallStillSelectsBranch

-- Bare property-style reference must raise noMatchingBranch, not return a
-- silently cached empty sequence value.
def bareConditionalPropertyReferenceFails : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("F", valueAccessConditionalAlg)] [
    resolve "F"
  ])) with
  | Except.error err => innermostIsNoMatchingBranch "F" err
  | _ => false

#guard bareConditionalPropertyReferenceFails

-- Dot-call access without arguments agrees with the bare reference.
def dotCallConditionalWithoutArgsFails : Bool :=
  match runResult (.dotCall (.algorithmExpr (algPrivate [] [] [
    ("F", valueAccessConditionalAlg)
  ] [.num 0])) "F" none) with
  | Except.error err => innermostIsNoMatchingBranch "F" err
  | _ => false

#guard dotCallConditionalWithoutArgsFails

-- Forcing a conditional through a sequence-builtin collection argument also
-- fails instead of silently contributing nothing.
def conditionalCollectionArgumentFails : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("F", valueAccessConditionalAlg)] [
    .call (resolve "sum") [resolve "F"]
  ])) with
  | Except.error err => innermostIsNoMatchingBranch "conditional" err
  | _ => false

#guard conditionalCollectionArgumentFails

-- A conditional bound as a higher-order argument fails when referenced as a
-- bare zero-argument thunk inside the callee body.
def conditionalHigherOrderThunkReferenceFails : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [
    ("F", valueAccessConditionalAlg),
    ("Apply", alg ["f"] [] [] [.param "f"])
  ] [
    .call (resolve "Apply") [resolve "F"]
  ])) with
  | Except.error err => innermostIsNoMatchingBranch "f" err
  | _ => false

#guard conditionalHigherOrderThunkReferenceFails

--------------------------------------------------------------------------------
-- Singleton sequence-value patterns match identically in direct and callback calls
--------------------------------------------------------------------------------

-- G((0)) = 100; G((x)) = x. Result normalization collapses singleton sequence values,
-- so the singleton sequence-value pattern must accept a plain scalar argument.
def singletonSequenceValueConditionalAlg : Algorithm :=
  .conditional none [] [
    ⟨ .sequenceValue [.sequenceValue [.litInt 0]], alg [] [] [] [.num 100] ⟩,
    ⟨ .sequenceValue [.sequenceValue [.bind "x"]], alg [] [] [] [.param "x"] ⟩
  ]

def singletonSequenceValuePatternMatchesDirectCall : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("G", singletonSequenceValueConditionalAlg)] [
    .call (resolve "G") [.num 0],
    .call (resolve "G") [.num 5]
  ])) with
  | Except.ok [100, 5] => true
  | _ => false

#guard singletonSequenceValuePatternMatchesDirectCall

-- The same conditional must accept the same shapes through map callbacks.
def singletonSequenceValuePatternMatchesMapCallback : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("G", singletonSequenceValueConditionalAlg)] [
    .call (resolve "map") [sequenceItems [.num 0, .num 5], resolve "G"]
  ])) with
  | Except.ok [100, 5] => true
  | _ => false

#guard singletonSequenceValuePatternMatchesMapCallback

-- Multi-member sequence-value patterns still reject scalars; only the singleton
-- adaptation is permitted.
def multiMemberSequenceValuePatternStillRejectsScalars : Bool :=
  let pairFirst : Algorithm :=
    .conditional none [] [
      ⟨ .sequenceValue [.sequenceValue [.bind "a", .bind "b"]], alg [] [] [] [.num 1] ⟩,
      ⟨ .sequenceValue [.bind "x"], alg [] [] [] [.num 2] ⟩
    ]
  match runFlat (.algorithmExpr (algPrivate [] [] [("H", pairFirst)] [
    .call (resolve "H") [.num 9]
  ])) with
  | Except.ok [2] => true
  | _ => false

#guard multiMemberSequenceValuePatternStillRejectsScalars

--------------------------------------------------------------------------------
-- Conditional branch arity invariants are Lean-enforced before evaluation
--------------------------------------------------------------------------------
-- runResultM validates every conditional in the algorithm tree: all branches
-- must share one top-level pattern arity and one top-level output arity.
-- Mirrors the C# parser's clause-elaboration checks.

-- F(0) = 1; F(x, y) = x + y → top-level pattern arities 1 vs 2.
def branchInputArityMismatchIsRejected : Bool :=
  let cond : Algorithm := .conditional none [] [
    ⟨ .litInt 0, alg [] [] [] [.num 1] ⟩,
    ⟨ .sequenceValue [.bind "x", .bind "y"], alg [] [] [] [.binary .add (.param "x") (.param "y")] ⟩
  ]
  match runResult (.algorithmExpr (algPrivate [] [] [("F", cond)] [
    .call (resolve "F") [.num 0]
  ])) with
  | Except.error err => innermostIsBranchArityMismatch "F" 1 2 err
  | _ => false

#guard branchInputArityMismatchIsRejected

-- F(0) = 1; F(x) = 1, 2 → top-level output arities 1 vs 2.
def branchOutputArityMismatchIsRejected : Bool :=
  let cond : Algorithm := .conditional none [] [
    ⟨ .litInt 0, alg [] [] [] [.num 1] ⟩,
    ⟨ .bind "x", alg [] [] [] [.num 1, .num 2] ⟩
  ]
  match runResult (.algorithmExpr (algPrivate [] [] [("F", cond)] [
    .call (resolve "F") [.num 0]
  ])) with
  | Except.error err => innermostIsBranchOutputArityMismatch "F" 1 2 err
  | _ => false

#guard branchOutputArityMismatchIsRejected

-- F((0, y)) = y; F((x, y)) = x + y → both branches have ONE top-level
-- pattern (a sequence-value pair); nested substructure may vary.
def sequenceValuePatternsWithSameTopLevelArityPass : Bool :=
  let cond : Algorithm := .conditional none [] [
    ⟨ .sequenceValue [.sequenceValue [.litInt 0, .bind "y"]], alg [] [] [] [.param "y"] ⟩,
    ⟨ .sequenceValue [.sequenceValue [.bind "x", .bind "y"]], alg [] [] [] [.binary .add (.param "x") (.param "y")] ⟩
  ]
  match runFlat (.algorithmExpr (algPrivate [] [] [("F", cond)] [
    .call (resolve "F") [.capture [.num 0, .num 5]],
    .call (resolve "F") [.capture [.num 1, .num 2]]
  ])) with
  | Except.ok [5, 3] => true
  | _ => false

#guard sequenceValuePatternsWithSameTopLevelArityPass

-- F(0) = 1, 2; F(x) = x, x → both branches emit TWO top-level outputs.
def uniformBranchOutputArityPasses : Bool :=
  let cond : Algorithm := .conditional none [] [
    ⟨ .litInt 0, alg [] [] [] [.num 1, .num 2] ⟩,
    ⟨ .bind "x", alg [] [] [] [.param "x", .param "x"] ⟩
  ]
  match runFlat (.algorithmExpr (algPrivate [] [] [("F", cond)] [
    .call (resolve "F") [.num 0],
    .call (resolve "F") [.num 7]
  ])) with
  | Except.ok [1, 2, 7, 7] => true
  | _ => false

#guard uniformBranchOutputArityPasses

-- Validation covers nested local algorithms and runs before evaluation:
-- an arity-violating conditional nested inside an inner property is rejected
-- even though nothing ever references it.
def nestedUnusedConditionalIsStillValidated : Bool :=
  let badCond : Algorithm := .conditional none [] [
    ⟨ .litInt 0, alg [] [] [] [.num 1] ⟩,
    ⟨ .sequenceValue [.bind "x", .bind "y"], alg [] [] [] [.param "x"] ⟩
  ]
  let outer : Algorithm := algPrivate [] [] [("Bad", badCond)] [.num 1]
  match runResult (.algorithmExpr (algPrivate [] [] [("Outer", outer)] [.num 42])) with
  | Except.error err => innermostIsBranchArityMismatch "Bad" 1 2 err
  | _ => false

#guard nestedUnusedConditionalIsStillValidated

end KatLangTests
