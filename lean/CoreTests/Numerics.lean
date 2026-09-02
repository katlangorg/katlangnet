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

end KatLangTests
