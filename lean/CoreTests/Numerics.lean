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

-- G-3 (C# reference parity, September 2026): `div` truncates the EXACT
-- quotient. The C# runtime used to truncate a quotient ALREADY rounded to 34
-- significant digits, answering 3000000000000000000000000000000000 here and
-- 13 for the small landing (13 * 3e32 - 1) div 3e32; the exact truncated
-- quotients are representable Decimal128 integers and the Int core has always
-- returned them. `mod` is exact in both engines, so the truncated-division
-- identity x = y * (x div y) + (x mod y) holds on every pair below.
def exactTruncatedQuotientAt34Digits : Bool :=
  binaryAtomResult? .idiv 8999999999999999999999999999999999 3 == some 2999999999999999999999999999999999 &&
  binaryAtomResult? .mod 8999999999999999999999999999999999 3 == some 2 &&
  binaryAtomResult? .idiv (-8999999999999999999999999999999999) 3 == some (-2999999999999999999999999999999999) &&
  binaryAtomResult? .idiv 8999999999999999999999999999999999 (-3) == some (-2999999999999999999999999999999999) &&
  binaryAtomResult? .idiv (-8999999999999999999999999999999999) (-3) == some 2999999999999999999999999999999999 &&
  binaryAtomResult? .mod (-8999999999999999999999999999999999) 3 == some (-2) &&
  -- the small quotient that the runtime rounded UP to 13 (a landing from below) …
  binaryAtomResult? .idiv 3899999999999999999999999999999999 300000000000000000000000000000000 == some 12 &&
  -- … and its mirror image, where the runtime's rounding lands DOWN on 12
  binaryAtomResult? .idiv 3600000000000000000000000000000001 300000000000000000000000000000000 == some 12 &&
  -- the rounded quotient …429 times 7 rounds back to exactly 1e34 in Decimal128
  binaryAtomResult? .idiv 10000000000000000000000000000000000 7 == some 1428571428571428571428571428571428 &&
  binaryAtomResult? .mod 10000000000000000000000000000000000 7 == some 4

#guard exactTruncatedQuotientAt34Digits

def truncatedDivisionIdentityPairs : List (Int × Int) :=
  [(8999999999999999999999999999999999, 3),
   (-8999999999999999999999999999999999, 3),
   (8999999999999999999999999999999999, -3),
   (-8999999999999999999999999999999999, -3),
   (3899999999999999999999999999999999, 300000000000000000000000000000000),
   (3600000000000000000000000000000001, 300000000000000000000000000000000),
   (10000000000000000000000000000000000, 7),
   (9999999999999999999999999999999998, 3333333333333333333333333333333333)]

def truncatedDivisionIdentityHolds : Bool :=
  truncatedDivisionIdentityPairs.all fun (x, y) =>
    match binaryAtomResult? .idiv x y, binaryAtomResult? .mod x y with
    | some q, some r => x == y * q + r
    | _, _ => false

#guard truncatedDivisionIdentityHolds

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

-- 0 ^ negative is a domain error (same message as the C# runtime, whose rule
-- rejects EVERY exponent below zero -- `0 ^ -0.5` too; the Int core states the
-- integer instance).
def zeroToNegativeExponentIsDomainError : Bool :=
  match runResult (.binary .pow (.num 0) (.num (-1))) with
  | Except.error err =>
      innermostIsIllegalInEval "zero cannot be raised to a negative exponent" err
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
  match op with
  -- The logical operators require Boolean operands; every other non-equality
  -- operator requires numeric scalars. `()` satisfies neither.
  | .and | .or | .xor =>
      s!"operator `{op.symbol}` expects Boolean operands, but the {side} operand was a sequence value with 0 sequence elements: ()"
  | _ =>
      s!"operator `{op.symbol}` expects numeric scalar operands, but the {side} operand was a sequence value with 0 sequence elements: ()"

/-- A valid other operand for `op`, so that the EMPTY operand is the one
    rejected: a Boolean for the logical operators, a number otherwise. -/
def validOperandFor (op : KatLang.BinaryOp) : KatLang.Expr :=
  match op with
  | .and | .or | .xor => .boolLiteral true
  | _ => .num 10

def rejectsEmptyOperand (op : KatLang.BinaryOp) : Bool :=
  (match runResult (.binary op emptyOperandExpr (validOperandFor op)) with
   | Except.error err => innermostIsTypeMismatch (emptyOperandMessage op "left") err
   | _ => false) &&
  (match runResult (.binary op (validOperandFor op) emptyOperandExpr) with
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
  evaluatesTo (.binary .eq emptyOperandExpr emptyOperandExpr) (.bool true) &&
  evaluatesTo (.binary .ne emptyOperandExpr emptyOperandExpr) (.bool false) &&
  evaluatesTo (.binary .eq emptyOperandExpr (.emptySequence 1)) (.bool true) &&
  evaluatesTo (.binary .ne emptyOperandExpr (.emptySequence 1)) (.bool false) &&
  evaluatesTo (.binary .eq emptyOperandExpr (.num 0)) (.bool false) &&
  evaluatesTo (.binary .ne emptyOperandExpr (.capture [.num 1, .num 2])) (.bool true) &&
  evaluatesTo (.binary .eq emptyOperandExpr (.stringLiteral "text")) (.bool false) &&
  evaluatesTo (.binary .eq (.listLiteral []) emptyOperandExpr) (.bool false) &&
  -- Booleans join the total equality: `() == false` is false, not an error,
  -- and a Boolean never equals the number it would once have encoded.
  evaluatesTo (.binary .eq emptyOperandExpr (.boolLiteral false)) (.bool false) &&
  evaluatesTo (.binary .eq (.boolLiteral true) (.num 1)) (.bool false) &&
  evaluatesTo (.binary .eq (.boolLiteral false) (.num 0)) (.bool false) &&
  evaluatesTo (.binary .ne (.boolLiteral true) (.num 1)) (.bool true) &&
  evaluatesTo (.binary .eq (.boolLiteral true) (.boolLiteral true)) (.bool true) &&
  evaluatesTo (.binary .eq (.boolLiteral true) (.boolLiteral false)) (.bool false)

#guard emptyStructuralEqualityUnaffected

-- Positive control 2: ordinary scalar operators still compute, the ordering
-- operators return BOOLEAN values (never a numeric representation and never
-- one of their operands), and the logical operators combine Boolean operands.
def ordinaryScalarOperatorsUnaffected : Bool :=
  binaryAtomResult? .add 1 2 == some 3 &&
  binaryAtomResult? .sub 1 2 == some (-1) &&
  evaluatesToBool (.binary .gt (.num 10) (.num 1)) true &&
  evaluatesToBool (.binary .gt (.num 1) (.num 10)) false &&
  evaluatesToBool (.binary .ge (.num 1) (.num 1)) true &&
  evaluatesToBool (.binary .and (.boolLiteral true) (.boolLiteral true)) true &&
  evaluatesToBool (.binary .and (.boolLiteral false) (.boolLiteral true)) false &&
  evaluatesToBool (.binary .or (.boolLiteral false) (.boolLiteral false)) false &&
  evaluatesToBool (.binary .or (.boolLiteral false) (.boolLiteral true)) true &&
  evaluatesToBool (.binary .xor (.boolLiteral true) (.boolLiteral false)) true &&
  evaluatesToBool (.binary .xor (.boolLiteral true) (.boolLiteral true)) false &&
  -- A comparison is never a number, and the logical operators never accept
  -- numbers: there is no `0`/`1` truth encoding left anywhere.
  binaryAtomResult? .gt 10 1 == none &&
  binaryAtomResult? .and 1 7 == none &&
  binaryAtomResult? .or 0 0 == none

#guard ordinaryScalarOperatorsUnaffected

/-- The logical operators reject every non-Boolean operand with the ONE
    Boolean-operand message naming the operand; the ordering operators reject
    Boolean operands (Booleans are not ordered) with the numeric-scalar message. -/
def logicalOperatorsRejectNonBooleanOperands : Bool :=
  (match runResult (.binary .and (.num 1) (.num 2)) with
   | Except.error err =>
       hasContext "while evaluating `1 and 2`" err &&
       innermostIsTypeMismatch
         "operator `and` expects Boolean operands, but the left operand was numeric value 1" err
   | _ => false) &&
  (match runResult (.binary .or (.boolLiteral true) (.num 0)) with
   | Except.error err =>
       innermostIsTypeMismatch
         "operator `or` expects Boolean operands, but the right operand was numeric value 0" err
   | _ => false) &&
  (match runResult (.binary .xor (.stringLiteral "a") (.boolLiteral true)) with
   | Except.error err =>
       innermostIsTypeMismatch
         "operator `xor` expects Boolean operands, but the left operand was a string: 'a'" err
   | _ => false) &&
  (match runResult (.binary .and (.listLiteral [.num 1]) (.boolLiteral true)) with
   | Except.error err =>
       innermostIsTypeMismatch
         "operator `and` expects Boolean operands, but the left operand was a list value with 1 element: [1]" err
   | _ => false) &&
  (match runResult (.binary .lt (.boolLiteral true) (.boolLiteral false)) with
   | Except.error err =>
       innermostIsTypeMismatch
         "operator `<` expects numeric scalar operands, but the left operand was a Boolean value: true" err
   | _ => false) &&
  (match runResult (.binary .gt (.boolLiteral true) (.num 0)) with
   | Except.error err =>
       innermostIsTypeMismatch
         "operator `>` expects numeric scalar operands, but the left operand was a Boolean value: true" err
   | _ => false) &&
  (match runResult (.binary .add (.boolLiteral true) (.num 1)) with
   | Except.error err =>
       innermostIsTypeMismatch
         "operator `+` expects numeric scalar operands, but the left operand was a Boolean value: true" err
   | _ => false) &&
  (match runResult (.binary .mul (.num 10) (.boolLiteral false)) with
   | Except.error err =>
       innermostIsTypeMismatch
         "operator `*` expects numeric scalar operands, but the right operand was a Boolean value: false" err
   | _ => false)

#guard logicalOperatorsRejectNonBooleanOperands

/-- Both logical operands are evaluated left to right before the operator
    applies (no short circuit): a rejected RIGHT operand is reported even when
    the left operand alone would decide the result. -/
def logicalOperatorsEvaluateBothOperands : Bool :=
  (match runResult (.binary .or (.boolLiteral true) (.num 1)) with
   | Except.error err =>
       innermostIsTypeMismatch
         "operator `or` expects Boolean operands, but the right operand was numeric value 1" err
   | _ => false) &&
  (match runResult (.binary .and (.boolLiteral false) (.binary .div (.num 1) (.num 0))) with
   | Except.error err => innermostIsDivByZero err
   | _ => false)

#guard logicalOperatorsEvaluateBothOperands

-- Unary `-` uses the existing expectInt validation: every unsupported
-- sequence/list value is badArity, including `()`; strings keep typeMismatch;
-- a Boolean operand is a value-kind error. Unary `not` REQUIRES a Boolean:
-- every other operand kind — numbers included — is the one typeMismatch
-- naming the operand.
def unaryNonScalarOperandsRejected : Bool :=
  ([emptyOperandExpr, .emptySequence 2, .capture [.num 1, .num 2],
    .listLiteral [], .listLiteral [.num 1], .listLiteral [.num 1, .num 2]]).all
    (fun operand => match runResult (.unary .minus operand) with
     | Except.error err => innermostIsBadArity err
     | _ => false) &&
  (match runResult (.unary .minus (.stringLiteral "text")) with
   | Except.error err =>
       innermostIsTypeMismatch "Unary operator is not supported for strings" err
   | _ => false) &&
  (match runResult (.unary .minus (.boolLiteral true)) with
   | Except.error err =>
       innermostIsTypeMismatch
         "operator `-` expects a numeric scalar operand, but the operand was a Boolean value: true" err
   | _ => false) &&
  (([(emptyOperandExpr, "a sequence value with 0 sequence elements: ()"),
     (.capture [.num 1, .num 2], "a sequence value with 2 sequence elements: (1, 2)"),
     (.listLiteral [], "a list value with 0 elements: []"),
     (.listLiteral [.num 1], "a list value with 1 element: [1]"),
     (.stringLiteral "text", "a string: 'text'"),
     (.num 0, "numeric value 0"),
     (.num 7, "numeric value 7"),
     (.num (-7), "numeric value -7")] : List (KatLang.Expr × String)).all
    (fun (operand, description) => match runResult (.unary .not operand) with
     | Except.error err =>
         innermostIsTypeMismatch
           s!"operator `not` expects a Boolean operand, but the operand was {description}" err
     | _ => false))

#guard unaryNonScalarOperandsRejected

def ordinaryUnaryOperatorsUnaffected : Bool :=
  evaluatesTo (.unary .minus (.num 7)) (.atom (-7)) &&
  evaluatesTo (.unary .minus (.num (-7))) (.atom 7) &&
  evaluatesTo (.unary .minus (.num 0)) (.atom 0) &&
  evaluatesTo (.unary .not (.boolLiteral false)) (.bool true) &&
  evaluatesTo (.unary .not (.boolLiteral true)) (.bool false) &&
  -- A redundant singleton boundary normalizes away, as for numbers.
  evaluatesTo (.unary .not (.capture [.boolLiteral true])) (.bool false) &&
  evaluatesTo (.unary .not (.binary .lt (.num 1) (.num 2))) (.bool false)

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
