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

/-- The numeric-atom projection of a one-link comparison chain: always `none`,
    because a comparison is a Boolean, never a number. -/
def comparisonAtomResult? (op : KatLang.ComparisonOp) (a b : Int) : Option Int :=
  match runResult (.compare op (.num a) (.num b)) with
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
    rejected: a Boolean for the logical operators, a number otherwise. As a
    LEFT operand the Boolean must not decide the operator, or the empty right
    operand would be skipped by the short circuit: `true` for `and` (and
    `xor`), `false` for `or`. -/
def validOperandFor (op : KatLang.BinaryOp) : KatLang.Expr :=
  match op with
  | .and | .xor => .boolLiteral true
  | .or => .boolLiteral false
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

/-- Every binary operator (the structural `==`/`!=` pair is not a binary
    operator: comparisons are chain links, covered by the ordering list below). -/
def nonEqualityOperators : List KatLang.BinaryOp :=
  [.add, .sub, .mul, .div, .idiv, .mod, .pow, .and, .or, .xor]

-- Left-empty, right-empty, and both-empty for every non-equality operator.
def emptyOperandRejectedByEveryScalarOperator : Bool :=
  nonEqualityOperators.all rejectsEmptyOperand

#guard emptyOperandRejectedByEveryScalarOperator

/-- The ordering comparisons — the non-equality links of a comparison chain —
    share the numeric-scalar operand rule and its message. -/
def orderingComparisonOperators : List KatLang.ComparisonOp := [.lt, .gt, .le, .ge]

def emptyComparisonOperandMessage (op : KatLang.ComparisonOp) (side : String) : String :=
  s!"operator `{op.symbol}` expects numeric scalar operands, but the {side} operand was a sequence value with 0 sequence elements: ()"

def rejectsEmptyComparisonOperand (op : KatLang.ComparisonOp) : Bool :=
  (match runResult (.compare op emptyOperandExpr (.num 10)) with
   | Except.error err => innermostIsTypeMismatch (emptyComparisonOperandMessage op "left") err
   | _ => false) &&
  (match runResult (.compare op (.num 10) emptyOperandExpr) with
   | Except.error err => innermostIsTypeMismatch (emptyComparisonOperandMessage op "right") err
   | _ => false) &&
  (match runResult (.compare op emptyOperandExpr emptyOperandExpr) with
   | Except.error err => innermostIsTypeMismatch (emptyComparisonOperandMessage op "left") err
   | _ => false)

def emptyOperandRejectedByEveryOrderingComparison : Bool :=
  orderingComparisonOperators.all rejectsEmptyComparisonOperand

#guard emptyOperandRejectedByEveryOrderingComparison

-- The four SYN-01 reproductions specifically (plus the mirrored string case):
-- none of them yields the other operand. `() + 'text'` reaches the unchanged
-- string/non-string contract rather than passing the string through.
def syn01ReproductionsRejected : Bool :=
  (match runResult (.binary .div (.num 10) emptyOperandExpr) with
   | Except.error err => innermostIsTypeMismatch (emptyOperandMessage .div "right") err
   | _ => false) &&
  (match runResult (.compare .gt emptyOperandExpr (.num 10)) with
   | Except.error err => innermostIsTypeMismatch (emptyComparisonOperandMessage .gt "left") err
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
  evaluatesTo (.compare .eq emptyOperandExpr emptyOperandExpr) (.bool true) &&
  evaluatesTo (.compare .ne emptyOperandExpr emptyOperandExpr) (.bool false) &&
  evaluatesTo (.compare .eq emptyOperandExpr (.emptySequence 1)) (.bool true) &&
  evaluatesTo (.compare .ne emptyOperandExpr (.emptySequence 1)) (.bool false) &&
  evaluatesTo (.compare .eq emptyOperandExpr (.num 0)) (.bool false) &&
  evaluatesTo (.compare .ne emptyOperandExpr (.capture [.num 1, .num 2])) (.bool true) &&
  evaluatesTo (.compare .eq emptyOperandExpr (.stringLiteral "text")) (.bool false) &&
  evaluatesTo (.compare .eq (.listLiteral []) emptyOperandExpr) (.bool false) &&
  -- Booleans join the total equality: `() == false` is false, not an error,
  -- and a Boolean never equals the number it would once have encoded.
  evaluatesTo (.compare .eq emptyOperandExpr (.boolLiteral false)) (.bool false) &&
  evaluatesTo (.compare .eq (.boolLiteral true) (.num 1)) (.bool false) &&
  evaluatesTo (.compare .eq (.boolLiteral false) (.num 0)) (.bool false) &&
  evaluatesTo (.compare .ne (.boolLiteral true) (.num 1)) (.bool true) &&
  evaluatesTo (.compare .eq (.boolLiteral true) (.boolLiteral true)) (.bool true) &&
  evaluatesTo (.compare .eq (.boolLiteral true) (.boolLiteral false)) (.bool false)

#guard emptyStructuralEqualityUnaffected

-- Positive control 2: ordinary scalar operators still compute, the ordering
-- operators return BOOLEAN values (never a numeric representation and never
-- one of their operands), and the logical operators combine Boolean operands.
def ordinaryScalarOperatorsUnaffected : Bool :=
  binaryAtomResult? .add 1 2 == some 3 &&
  binaryAtomResult? .sub 1 2 == some (-1) &&
  evaluatesToBool (.compare .gt (.num 10) (.num 1)) true &&
  evaluatesToBool (.compare .gt (.num 1) (.num 10)) false &&
  evaluatesToBool (.compare .ge (.num 1) (.num 1)) true &&
  evaluatesToBool (.binary .and (.boolLiteral true) (.boolLiteral true)) true &&
  evaluatesToBool (.binary .and (.boolLiteral false) (.boolLiteral true)) false &&
  evaluatesToBool (.binary .or (.boolLiteral false) (.boolLiteral false)) false &&
  evaluatesToBool (.binary .or (.boolLiteral false) (.boolLiteral true)) true &&
  evaluatesToBool (.binary .xor (.boolLiteral true) (.boolLiteral false)) true &&
  evaluatesToBool (.binary .xor (.boolLiteral true) (.boolLiteral true)) false &&
  -- A comparison is never a number, and the logical operators never accept
  -- numbers: there is no `0`/`1` truth encoding left anywhere.
  comparisonAtomResult? .gt 10 1 == none &&
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
  (match runResult (.binary .or (.boolLiteral false) (.num 0)) with
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
  (match runResult (.compare .lt (.boolLiteral true) (.boolLiteral false)) with
   | Except.error err =>
       innermostIsTypeMismatch
         "operator `<` expects numeric scalar operands, but the left operand was a Boolean value: true" err
   | _ => false) &&
  (match runResult (.compare .gt (.boolLiteral true) (.num 0)) with
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

--------------------------------------------------------------------------------
-- Short-circuit `and` / `or`
--------------------------------------------------------------------------------
-- `and` / `or` evaluate the left operand, require it to be a Boolean, and
-- evaluate the right operand only when the left one does not decide the result
-- (`false and _` is `false`, `true or _` is `true`). A skipped right operand has
-- no effect at all: no failure, no `tick()`, no value-kind check. `xor` needs
-- both operands and stays eager.

/-- `1 / 0 > 0`: a Boolean-shaped operand whose evaluation fails. -/
def failingComparisonOperand : KatLang.Expr :=
  .compare .gt (.binary .div (.num 1) (.num 0)) (.num 0)

def tickCallExpr : KatLang.Expr := .call (resolve "tick") []

/-- `tick() == n`: an effectful Boolean operand that is `true` iff it ran as the run's n-th tick. -/
def tickIs (n : Int) : KatLang.Expr := .compare .eq tickCallExpr (.num n)

/-- The outcome of `e` and the number of `tick()` executions of the WHOLE run, kept for a
    failed run too. -/
def outcomeAndTicks (e : KatLang.Expr) : Except Error Result × Nat :=
  let (result, state) := (KatLang.runResultM e).runState KatLang.EvalState.empty
  (result, state.tickCounter)

/-- `e` is the Boolean `expected`, and the run executed exactly `ticks` ticks. -/
def boolAfterTicks (e : KatLang.Expr) (expected : Bool) (ticks : Nat) : Bool :=
  match outcomeAndTicks e with
  | (Except.ok (.bool value), ran) => value == expected && ran == ticks
  | _ => false

/-- `e` fails with `expected` as its innermost error after exactly `ticks` ticks. -/
def failsAfterTicks (e : KatLang.Expr) (expected : Error -> Bool) (ticks : Nat) : Bool :=
  match outcomeAndTicks e with
  | (Except.error err, ran) => expected err && ran == ticks
  | _ => false

-- The four examples of the short-circuit decision: a deciding left operand
-- skips the failing right operand; a non-deciding one evaluates it.
def shortCircuitDecidesByTheLeftOperand : Bool :=
  evaluatesToBool (.binary .and (.boolLiteral false) failingComparisonOperand) false &&
  evaluatesToBool (.binary .or (.boolLiteral true) failingComparisonOperand) true &&
  (match runResult (.binary .and (.boolLiteral true) failingComparisonOperand) with
   | Except.error err => innermostIsDivByZero err
   | _ => false) &&
  (match runResult (.binary .or (.boolLiteral false) failingComparisonOperand) with
   | Except.error err => innermostIsDivByZero err
   | _ => false)

#guard shortCircuitDecidesByTheLeftOperand

-- A skipped right operand runs ZERO times; an evaluated one runs exactly ONCE.
def shortCircuitSkippedOperandHasNoEffect : Bool :=
  boolAfterTicks (.binary .and (.boolLiteral false) (tickIs 1)) false 0 &&
  boolAfterTicks (.binary .or (.boolLiteral true) (tickIs 1)) true 0 &&
  boolAfterTicks (.binary .and (.boolLiteral true) (tickIs 1)) true 1 &&
  boolAfterTicks (.binary .and (.boolLiteral true) (tickIs 2)) false 1 &&
  boolAfterTicks (.binary .or (.boolLiteral false) (tickIs 1)) true 1 &&
  boolAfterTicks (.binary .or (.boolLiteral false) (tickIs 2)) false 1

#guard shortCircuitSkippedOperandHasNoEffect

-- Left before right, each evaluated operand once, with a left operand computed
-- at run time: the left operand takes tick 1, and the right operand takes tick
-- 2 only when the left one did not decide.
def shortCircuitEvaluatesLeftThenRightOnce : Bool :=
  boolAfterTicks (.binary .and (tickIs 1) (tickIs 2)) true 2 &&
  boolAfterTicks (.binary .and (tickIs 1) (tickIs 1)) false 2 &&
  boolAfterTicks (.binary .and (tickIs 2) (tickIs 2)) false 1 &&
  boolAfterTicks (.binary .or (tickIs 1) (tickIs 2)) true 1 &&
  boolAfterTicks (.binary .or (tickIs 2) (tickIs 2)) true 2 &&
  boolAfterTicks (.binary .or (tickIs 2) (tickIs 1)) false 2 &&
  -- Nested: `false and (…)` skips a whole right operand tree, and the skipped
  -- operand of an inner operator stays skipped inside an evaluated outer one.
  boolAfterTicks (.binary .and (.boolLiteral false) (.binary .or (tickIs 1) (tickIs 2))) false 0 &&
  boolAfterTicks (.binary .or (.binary .and (.boolLiteral false) (tickIs 1)) (tickIs 1)) true 1 &&
  boolAfterTicks (.binary .and (.binary .or (.boolLiteral true) (tickIs 1)) (tickIs 1)) true 1

#guard shortCircuitEvaluatesLeftThenRightOnce

/-- `Guard(x) = x != 0 and 8 / x > 1`, called with `x`. (The dividend is a
    multiple of the nonzero divisors used below, so the integer core and the
    C# decimal runtime compute the same quotient.) -/
def zeroDenominatorGuard (x : Int) : KatLang.Expr :=
  .algorithmExpr (algPrivate [] []
    [("Guard", alg ["x"] [] []
      [.binary .and (.compare .ne (param "x") (num 0))
        (.compare .gt (.binary .div (num 8) (param "x")) (num 1))])]
    [.call (resolve "Guard") [num x]])

/-- `Alternative(x) = x == 0 or 8 / x > 1`, called with `x`. -/
def zeroDenominatorAlternative (x : Int) : KatLang.Expr :=
  .algorithmExpr (algPrivate [] []
    [("Alternative", alg ["x"] [] []
      [.binary .or (.compare .eq (param "x") (num 0))
        (.compare .gt (.binary .div (num 8) (param "x")) (num 1))])]
    [.call (resolve "Alternative") [num x]])

-- The practical guard, with a left operand computed at run time: a zero
-- denominator is never divided by, and a nonzero one still is.
def shortCircuitGuardsAZeroDenominator : Bool :=
  evaluatesToBool (zeroDenominatorGuard 0) false &&
  evaluatesToBool (zeroDenominatorGuard 4) true &&
  evaluatesToBool (zeroDenominatorGuard (-4)) false &&
  evaluatesToBool (zeroDenominatorAlternative 0) true &&
  evaluatesToBool (zeroDenominatorAlternative 4) true &&
  evaluatesToBool (zeroDenominatorAlternative (-4)) false

#guard shortCircuitGuardsAZeroDenominator

-- The left operand's failure, or its value-kind rejection, is the outcome
-- BEFORE any right operand work: the effectful right operand never ran.
def shortCircuitLeftOperandIsJudgedFirst : Bool :=
  failsAfterTicks (.binary .and (.num 1) (tickIs 1))
    (fun err =>
      hasContext "while evaluating `1 and tick(...) == 1`" err &&
      innermostIsTypeMismatch
        "operator `and` expects Boolean operands, but the left operand was numeric value 1" err) 0 &&
  failsAfterTicks (.binary .or (.num 0) (tickIs 1))
    (innermostIsTypeMismatch
      "operator `or` expects Boolean operands, but the left operand was numeric value 0") 0 &&
  failsAfterTicks (.binary .and (.binary .div (.num 1) (.num 0)) (tickIs 1)) innermostIsDivByZero 0 &&
  failsAfterTicks (.binary .or failingComparisonOperand (tickIs 1)) innermostIsDivByZero 0

#guard shortCircuitLeftOperandIsJudgedFirst

-- A non-Boolean RIGHT operand is the ordinary right-operand rejection when it
-- is evaluated, and is never looked at when it is skipped.
def shortCircuitRightOperandIsCheckedOnlyWhenEvaluated : Bool :=
  (match runResult (.binary .and (.boolLiteral true) (.num 1)) with
   | Except.error err =>
       hasContext "while evaluating `true and 1`" err &&
       innermostIsTypeMismatch
         "operator `and` expects Boolean operands, but the right operand was numeric value 1" err
   | _ => false) &&
  (match runResult (.binary .or (.boolLiteral false) (.num 1)) with
   | Except.error err =>
       hasContext "while evaluating `false or 1`" err &&
       innermostIsTypeMismatch
         "operator `or` expects Boolean operands, but the right operand was numeric value 1" err
   | _ => false) &&
  evaluatesToBool (.binary .and (.boolLiteral false) (.num 1)) false &&
  evaluatesToBool (.binary .or (.boolLiteral true) (.num 1)) true &&
  evaluatesToBool (.binary .and (.boolLiteral false) (.stringLiteral "a")) false &&
  evaluatesToBool (.binary .or (.boolLiteral true) emptyOperandExpr) true

#guard shortCircuitRightOperandIsCheckedOnlyWhenEvaluated

-- Control: `xor` is EAGER. Both operands are evaluated, left then right, once
-- each, whatever the left operand is — a failing or non-Boolean right operand
-- is still reported, and the left operand's value kind is checked only after
-- both were evaluated.
def xorEvaluatesBothOperands : Bool :=
  boolAfterTicks (.binary .xor (.boolLiteral true) (tickIs 1)) false 1 &&
  boolAfterTicks (.binary .xor (.boolLiteral false) (tickIs 1)) true 1 &&
  boolAfterTicks (.binary .xor (tickIs 1) (tickIs 2)) false 2 &&
  failsAfterTicks (.binary .xor (.boolLiteral true) failingComparisonOperand) innermostIsDivByZero 0 &&
  failsAfterTicks (.binary .xor (.boolLiteral false) failingComparisonOperand) innermostIsDivByZero 0 &&
  failsAfterTicks (.binary .xor (.boolLiteral true) (.num 1))
    (innermostIsTypeMismatch
      "operator `xor` expects Boolean operands, but the right operand was numeric value 1") 0 &&
  failsAfterTicks (.binary .xor (.num 1) (tickIs 1))
    (innermostIsTypeMismatch
      "operator `xor` expects Boolean operands, but the left operand was numeric value 1") 1

#guard xorEvaluatesBothOperands

-- Unary `-` rejects every non-numeric operand as a value KIND (Q-27): a
-- sequence or list value — `()` included — and a Boolean are the one
-- typeMismatch naming the operand; strings keep their own typeMismatch. Unary
-- `not` REQUIRES a Boolean: every other operand kind — numbers included — is
-- the one typeMismatch naming the operand.
def unaryNonScalarOperandsRejected : Bool :=
  (([(emptyOperandExpr, "a sequence value with 0 sequence elements: ()"),
     (.capture [.num 1, .num 2], "a sequence value with 2 sequence elements: (1, 2)"),
     (.listLiteral [], "a list value with 0 elements: []"),
     (.listLiteral [.num 1], "a list value with 1 element: [1]"),
     (.listLiteral [.num 1, .num 2], "a list value with 2 elements: [1, 2]")] : List (KatLang.Expr × String)).all
    (fun (operand, description) => match runResult (.unary .minus operand) with
     | Except.error err =>
         innermostIsTypeMismatch
           s!"operator `-` expects a numeric scalar operand, but the operand was {description}" err
     | _ => false)) &&
  (match runResult (.unary .minus (.emptySequence 2)) with
   | Except.error err => innermostIsAnyTypeMismatch err
   | _ => false) &&
  (match runResult (.unary .minus (.stringLiteral "text")) with
   | Except.error err =>
       innermostIsTypeMismatch
         "operator `-` expects a numeric scalar operand, but the operand was a string: 'text'" err
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
  evaluatesTo (.unary .not (.compare .lt (.num 1) (.num 2))) (.bool false)

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
