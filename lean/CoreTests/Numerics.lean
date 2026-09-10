import KatLang
import CoreTests.Common

namespace KatLangTests
open KatLang (alg algWithParameters algWithParameterPatterns algPrivate privateProp publicProp privateLocalProp publicLocalProp runFlat runResult Algorithm Error Result PropExposure)
open KatLang (resolve param num)
open KatLang (Pattern CondBranch)

--------------------------------------------------------------------------------
-- Numeric semantics: truncating division/modulo (C# reference parity)
--------------------------------------------------------------------------------

def binaryAtomResult? (op : KatLang.BinaryOp) (a b : Int) : Option Int :=
  match runResult (.binary op (.num a) (.num b)) with
  | Except.ok (.atom value) => some value
  | _ => none

-- Division truncates toward zero (Int.tdiv), matching the C# runtime
-- (`Math.Truncate` for `div`): -7 div 2 = -3, not the Euclidean -4.
def truncatingDivisionMatchesRuntime : Bool :=
  binaryAtomResult? .idiv 7 2 == some 3 &&
  binaryAtomResult? .idiv (-7) 2 == some (-3) &&
  binaryAtomResult? .idiv 7 (-2) == some (-3) &&
  binaryAtomResult? .idiv (-7) (-2) == some 3 &&
  binaryAtomResult? .div (-7) 2 == some (-3) &&
  binaryAtomResult? .div 7 (-2) == some (-3)

#guard truncatingDivisionMatchesRuntime

-- Modulo keeps the sign of the dividend (Int.tmod), matching the C# runtime
-- (decimal remainder): -7 mod 2 = -1, not the Euclidean 1.
def truncatingModuloMatchesRuntime : Bool :=
  binaryAtomResult? .mod 7 2 == some 1 &&
  binaryAtomResult? .mod (-7) 2 == some (-1) &&
  binaryAtomResult? .mod 7 (-2) == some 1 &&
  binaryAtomResult? .mod (-7) (-2) == some (-1)

#guard truncatingModuloMatchesRuntime

--------------------------------------------------------------------------------
-- Numeric semantics: negative exponents are never a silent 0
--------------------------------------------------------------------------------

-- Negative exponents with base 1 or -1 have exact integer reciprocals and
-- evaluate exactly, matching the C# runtime.
def negativeExponentExactCases : Bool :=
  binaryAtomResult? .pow 2 3 == some 8 &&
  binaryAtomResult? .pow 1 (-2) == some 1 &&
  binaryAtomResult? .pow (-1) (-3) == some (-1) &&
  binaryAtomResult? .pow (-1) (-2) == some 1

#guard negativeExponentExactCases

-- 0 ^ negative is a domain error (same message as the C# runtime).
def zeroToNegativeExponentIsDomainError : Bool :=
  match runResult (.binary .pow (.num 0) (.num (-1))) with
  | Except.error err =>
      innermostIsIllegalInEval "zero cannot be raised to a negative integer exponent" err
  | _ => false

#guard zeroToNegativeExponentIsDomainError

-- |base| >= 2 with a negative exponent has a fractional reciprocal
-- (2 ^ -1 = 0.5 in the decimal runtime). The Int core raises an explicit
-- error instead of silently truncating the reciprocal to 0.
def fractionalReciprocalExponentIsExplicitError : Bool :=
  (match runResult (.binary .pow (.num 2) (.num (-1))) with
   | Except.error (.illegalInEval _) => true
   | _ => false) &&
  (match runResult (.binary .pow (.num (-3)) (.num (-2))) with
   | Except.error (.illegalInEval _) => true
   | _ => false)

#guard fractionalReciprocalExponentIsExplicitError

--------------------------------------------------------------------------------
-- SYN-01: the empty sequence VALUE is not a scalar-operator identity
--------------------------------------------------------------------------------
-- `()` is a real KatLang value with no numeric scalar value. It therefore
-- reaches the SAME operand validation as any other non-scalar operand
-- (`(1, 2)`, `[]`, a string) for every non-equality operator, on either side,
-- instead of being returned as the operator's result. This is the OPERAND
-- rule; empty NEUTRALITY belongs to the arity algebra's supply operations
-- (capture/collect/spread), which are unchanged and pinned below.

def emptyOperandExpr : KatLang.Expr := .emptySequence 0

def emptyOperandMessage (op : KatLang.BinaryOp) (side : String) : String :=
  s!"operator `{op.symbol}` expects numeric scalar operands, but the {side} operand was a sequence value with 0 sequence elements: ()"

def rejectsEmptyOperand (op : KatLang.BinaryOp) : Bool :=
  (match runResult (.binary op emptyOperandExpr (.num 10)) with
   | Except.error err => innermostIsTypeMismatch (emptyOperandMessage op "left") err
   | _ => false) &&
  (match runResult (.binary op (.num 10) emptyOperandExpr) with
   | Except.error err => innermostIsTypeMismatch (emptyOperandMessage op "right") err
   | _ => false) &&
  (match runResult (.binary op emptyOperandExpr emptyOperandExpr) with
   | Except.error err => innermostIsTypeMismatch (emptyOperandMessage op "left") err
   | _ => false)

/-- Every operator except the structural `==`/`!=` pair. -/
def nonEqualityOperators : List KatLang.BinaryOp :=
  [.add, .sub, .mul, .div, .idiv, .mod, .pow, .lt, .gt, .le, .ge, .and, .or, .xor]

-- Left-empty, right-empty, and both-empty for every non-equality operator.
def emptyOperandRejectedByEveryScalarOperator : Bool :=
  nonEqualityOperators.all rejectsEmptyOperand

#guard emptyOperandRejectedByEveryScalarOperator

-- The four SYN-01 reproductions specifically (plus the mirrored string case):
-- none of them yields the other operand. `() + 'text'` reaches the unchanged
-- string/non-string contract rather than passing the string through.
def syn01ReproductionsRejected : Bool :=
  (match runResult (.binary .div (.num 10) emptyOperandExpr) with
   | Except.error err => innermostIsTypeMismatch (emptyOperandMessage .div "right") err
   | _ => false) &&
  (match runResult (.binary .gt emptyOperandExpr (.num 10)) with
   | Except.error err => innermostIsTypeMismatch (emptyOperandMessage .gt "left") err
   | _ => false) &&
  (match runResult (.binary .and emptyOperandExpr (.num 7)) with
   | Except.error err => innermostIsTypeMismatch (emptyOperandMessage .and "left") err
   | _ => false) &&
  (match runResult (.binary .add emptyOperandExpr (.stringLiteral "text")) with
   | Except.error err =>
       innermostIsTypeMismatch "Cannot apply operator to string and non-string operands" err
   | _ => false) &&
  (match runResult (.binary .add (.stringLiteral "text") emptyOperandExpr) with
   | Except.error err =>
       innermostIsTypeMismatch "Cannot apply operator to string and non-string operands" err
   | _ => false)

#guard syn01ReproductionsRejected

/-- `runResult e` succeeded with exactly `expected`. (`Error` has no `BEq`, so
    the whole `Except` cannot be compared directly.) -/
def evaluatesTo (e : KatLang.Expr) (expected : Result) : Bool :=
  match runResult e with
  | Except.ok value => value == expected
  | _ => false

-- Positive control 1: structural equality is decided BEFORE operand
-- validation and is unaffected -- `()` compares as an ordinary value.
def emptyStructuralEqualityUnaffected : Bool :=
  evaluatesTo (.binary .eq emptyOperandExpr emptyOperandExpr) (.atom 1) &&
  evaluatesTo (.binary .ne emptyOperandExpr emptyOperandExpr) (.atom 0) &&
  evaluatesTo (.binary .eq emptyOperandExpr (.emptySequence 1)) (.atom 1) &&
  evaluatesTo (.binary .ne emptyOperandExpr (.emptySequence 1)) (.atom 0) &&
  evaluatesTo (.binary .eq emptyOperandExpr (.num 0)) (.atom 0) &&
  evaluatesTo (.binary .ne emptyOperandExpr (.capture [.num 1, .num 2])) (.atom 1) &&
  evaluatesTo (.binary .eq emptyOperandExpr (.stringLiteral "text")) (.atom 0) &&
  evaluatesTo (.binary .eq (.listLiteral []) emptyOperandExpr) (.atom 0)

#guard emptyStructuralEqualityUnaffected

-- Positive control 2: ordinary scalar operators still compute, and the
-- ordering operators still return the numeric boolean representation rather
-- than one of their operands.
def ordinaryScalarOperatorsUnaffected : Bool :=
  binaryAtomResult? .add 1 2 == some 3 &&
  binaryAtomResult? .sub 1 2 == some (-1) &&
  binaryAtomResult? .gt 10 1 == some 1 &&
  binaryAtomResult? .gt 1 10 == some 0 &&
  binaryAtomResult? .ge 1 1 == some 1 &&
  binaryAtomResult? .and 1 7 == some 1 &&
  binaryAtomResult? .and 0 7 == some 0 &&
  binaryAtomResult? .or 0 0 == some 0

#guard ordinaryScalarOperatorsUnaffected

-- Unary operators use the existing expectInt validation: every unsupported
-- sequence/list value is badArity, including `()`; strings keep typeMismatch.
def unaryNonScalarOperandsRejected : Bool :=
  ([KatLang.UnaryOp.minus, .not]).all fun op =>
    ([emptyOperandExpr, .emptySequence 2, .capture [.num 1, .num 2],
      .listLiteral [], .listLiteral [.num 1], .listLiteral [.num 1, .num 2]]).all
      (fun operand => match runResult (.unary op operand) with
       | Except.error err => innermostIsBadArity err
       | _ => false) &&
    (match runResult (.unary op (.stringLiteral "text")) with
     | Except.error err =>
         innermostIsTypeMismatch "Unary operator is not supported for strings" err
     | _ => false)

#guard unaryNonScalarOperandsRejected

def ordinaryUnaryOperatorsUnaffected : Bool :=
  evaluatesTo (.unary .minus (.num 7)) (.atom (-7)) &&
  evaluatesTo (.unary .minus (.num (-7))) (.atom 7) &&
  evaluatesTo (.unary .minus (.num 0)) (.atom 0) &&
  evaluatesTo (.unary .not (.num 0)) (.atom 1) &&
  evaluatesTo (.unary .not (.num 7)) (.atom 0) &&
  evaluatesTo (.unary .not (.num (-7))) (.atom 0)

#guard ordinaryUnaryOperatorsUnaffected

-- Positive control 3: empty SUPPLY neutrality is untouched. `()` is still a
-- real value that captures, counts, spreads to zero items, and stays a
-- VISIBLE non-spread slot.
def emptySupplyNeutralityUnchanged : Bool :=
  evaluatesTo emptyOperandExpr (.sequenceValue []) &&
  evaluatesTo (.capture [emptyOperandExpr]) (.sequenceValue []) &&
  evaluatesTo (.capture [sequenceSpread emptyOperandExpr, .num 1]) (.atom 1) &&
  evaluatesTo (.capture [emptyOperandExpr, .num 1]) (.sequenceValue [.sequenceValue [], .atom 1]) &&
  evaluatesTo (.call (.resolve "count") [emptyOperandExpr]) (.atom 0) &&
  evaluatesTo (.listLiteral [emptyOperandExpr]) (.listValue [.sequenceValue []])

#guard emptySupplyNeutralityUnchanged

end KatLangTests
