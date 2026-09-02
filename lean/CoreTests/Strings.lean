import KatLang
import CoreTests.Common

namespace KatLangTests
open KatLang (alg algWithParameters algWithParameterPatterns algPrivate privateProp publicProp privateLocalProp publicLocalProp runFlat runResult Algorithm Error Result PropExposure)
open KatLang (resolve param num)
open KatLang (Pattern CondBranch)

--------------------------------------------------------------------------------
-- string intrinsic tests
--------------------------------------------------------------------------------

-- Test 52: string intrinsic on positive integer via algorithm
-- (block [123]).string → Result.str "123"
def test52 : Bool :=
  match runResult (.dotCall (.algorithmExpr (alg [] [] [] [.num 123])) "string" none) with
  | Except.ok (Result.str "123") => true
  | _ => false

#guard test52
#eval runResult (.dotCall (.algorithmExpr (alg [] [] [] [.num 123])) "string" none)

-- Test 53: string intrinsic on zero
-- (block [0]).string → Result.str "0"
def test53 : Bool :=
  match runResult (.dotCall (.algorithmExpr (alg [] [] [] [.num 0])) "string" none) with
  | Except.ok (Result.str "0") => true
  | _ => false

#guard test53

-- Test 54: string intrinsic on negative integer
-- (block [-5]).string → Result.str "-5"
def test54 : Bool :=
  match runResult (.dotCall (.algorithmExpr (alg [] [] [] [.num (-5)])) "string" none) with
  | Except.ok (Result.str "-5") => true
  | _ => false

#guard test54

-- Test 55: string intrinsic on a named property
-- A = 123; A.string → Result.str "123"
def test55 : Bool :=
  let innerAlg := algPrivate [] [] [("A", alg [] [] [] [.num 123])] [
    .dotCall (.resolve "A") "string" none
  ]
  match runResult (.algorithmExpr innerAlg) with
  | Except.ok (Result.str "123") => true
  | _ => false

#guard test55

-- Test 56: string intrinsic on numeric literal (notAnAlgorithm path)
-- (.num 42).string → Result.str "42"
def test56 : Bool :=
  match runResult (.dotCall (.num 42) "string" none) with
  | Except.ok (Result.str "42") => true
  | _ => false

#guard test56

-- Test 57: string intrinsic on string literal → typeMismatch error
-- ("hello").string → Error.typeMismatch
def test57 : Bool :=
  match runResult (.dotCall (.stringLiteral "hello") "string" none) with
  | Except.error _ => true
  | _ => false

#guard test57

-- Test 58: string intrinsic on multi-output → typeMismatch error
-- (1, 2).string -> Error (sequence value is not a numeric atom)
def test58 : Bool :=
  match runResult (.dotCall (.capture [.num 1, .num 2]) "string" none) with
  | Except.error _ => true
  | _ => false

#guard test58

--------------------------------------------------------------------------------
-- String literal tests (first-class string values)
--------------------------------------------------------------------------------

-- Test 38: String literal evaluates to Result.str
def test38 : Bool :=
  match runResult (.stringLiteral "hello") with
  | Except.ok (.str "hello") => true
  | _ => false

#guard test38

-- Test 39: String equality — same values
def test39 : Bool :=
  match runFlat (.binary .eq (.stringLiteral "a") (.stringLiteral "a")) with
  | Except.ok [1] => true
  | _ => false

#guard test39

-- Test 40: String equality — different values
def test40 : Bool :=
  match runFlat (.binary .eq (.stringLiteral "a") (.stringLiteral "b")) with
  | Except.ok [0] => true
  | _ => false

#guard test40

-- Test 41: String inequality
def test41 : Bool :=
  match runFlat (.binary .ne (.stringLiteral "a") (.stringLiteral "b")) with
  | Except.ok [1] => true
  | _ => false

#guard test41

-- Test 42: String equality is case-sensitive
def test42 : Bool :=
  match runFlat (.binary .eq (.stringLiteral "Apples") (.stringLiteral "apples")) with
  | Except.ok [0] => true
  | _ => false

#guard test42

-- Test 43: Unsupported binary operation on strings → typeMismatch
def test43 : Bool :=
  match runResult (.binary .add (.stringLiteral "a") (.stringLiteral "b")) with
  | Except.error (Error.typeMismatch _) => true
  | _ => false

#guard test43

-- Test 44: Mixed string/number in binary → typeMismatch
def test44 : Bool :=
  match runResult (.binary .add (.num 1) (.stringLiteral "a")) with
  | Except.error (Error.typeMismatch _) => true
  | _ => false

#guard test44

-- Test 45: Unary minus on string → typeMismatch
def test45 : Bool :=
  match runResult (.unary .minus (.stringLiteral "hello")) with
  | Except.error (Error.typeMismatch _) => true
  | _ => false

#guard test45

def numericScalarModLeftSequenceValueMessage : String :=
  "operator `mod` expects numeric scalar operands, but the left operand was a sequence value with 4 sequence elements: (3, 4, 5, 6)"

def numericScalarModRightSequenceValueMessage : String :=
  "operator `mod` expects numeric scalar operands, but the right operand was a sequence value with 4 sequence elements: (3, 4, 5, 6)"

-- Test 45a: sequenceValue left operand in a numeric operator reports scalar shape
def test45a : Bool :=
  match runResult (.binary .mod
    (.capture [.num 3, .num 4, .num 5, .num 6])
    (.num 2)) with
  | Except.error err =>
      hasContext "while evaluating `(3, 4, 5, 6) mod 2`" err &&
      innermostIsTypeMismatch numericScalarModLeftSequenceValueMessage err
  | _ => false

#guard test45a

-- Test 45b: sequenceValue right operand in a numeric operator reports scalar shape
def test45b : Bool :=
  match runResult (.binary .mod
    (.num 2)
    (.capture [.num 3, .num 4, .num 5, .num 6])) with
  | Except.error err =>
      hasContext "while evaluating `2 mod (3, 4, 5, 6)`" err &&
      innermostIsTypeMismatch numericScalarModRightSequenceValueMessage err
  | _ => false

#guard test45b

-- Structural value equality for `==` / `!=` ----------------------------------
-- `==` and `!=` compare KatLang values structurally across all value kinds:
-- numbers by value, strings by exact value, and sequence values by length plus
-- recursive pairwise equality. Different value kinds compare unequal rather than
-- raising a type mismatch. Arithmetic and ordering keep the numeric-scalar path
-- (Test 45a/45b above already cover sequence-operand rejection for `mod`).

-- Helper: a written sequence-value group in operand position,
-- e.g. `seqVal [1, 2]` stands in for `(1, 2)`.
def seqVal (xs : List Int) : KatLang.Expr :=
  .capture (xs.map (fun n => KatLang.Expr.num n))

-- Test 45c: structurally identical sequence values compare equal.
def sequenceValueEqualitySameElements : Bool :=
  match runFlat (.binary .eq (seqVal [1, 2]) (seqVal [1, 2])) with
  | Except.ok [1] => true
  | _ => false

#guard sequenceValueEqualitySameElements

-- Test 45d: sequence values differing in an element compare unequal.
def sequenceValueEqualityDifferentElement : Bool :=
  match runFlat (.binary .eq (seqVal [1, 2]) (seqVal [1, 3])) with
  | Except.ok [0] => true
  | _ => false

#guard sequenceValueEqualityDifferentElement

-- Test 45e: sequence values of different lengths compare unequal.
def sequenceValueEqualityDifferentLength : Bool :=
  match runFlat (.binary .eq (seqVal [1, 2]) (seqVal [1, 2, 3])) with
  | Except.ok [0] => true
  | _ => false

#guard sequenceValueEqualityDifferentLength

-- Test 45f: nested sequence values compare recursively (equal).
def nestedSequenceValueEqualityEqual : Bool :=
  let left  := .capture [.num 1, seqVal [2, 3]]
  let right := .capture [.num 1, seqVal [2, 3]]
  match runFlat (.binary .eq left right) with
  | Except.ok [1] => true
  | _ => false

#guard nestedSequenceValueEqualityEqual

-- Test 45g: nested sequence values compare recursively (unequal inner element).
def nestedSequenceValueEqualityDifferentInner : Bool :=
  let left  := .capture [.num 1, seqVal [2, 3]]
  let right := .capture [.num 1, seqVal [2, 4]]
  match runFlat (.binary .eq left right) with
  | Except.ok [0] => true
  | _ => false

#guard nestedSequenceValueEqualityDifferentInner

-- Test 45h: equality between different value kinds returns 0, never a type error.
def numberVsSequenceValueEqualityDifferentKinds : Bool :=
  match runFlat (.binary .eq (.num 1) (seqVal [1, 2])) with
  | Except.ok [0] => true
  | _ => false

#guard numberVsSequenceValueEqualityDifferentKinds

-- Test 45i: inequality is the negation of structural equality across kinds.
def numberVsSequenceValueInequalityDifferentKinds : Bool :=
  match runFlat (.binary .ne (.num 1) (seqVal [1, 2])) with
  | Except.ok [1] => true
  | _ => false

#guard numberVsSequenceValueInequalityDifferentKinds

-- Test 45j: `!=` negates structural equality for equal sequence values.
def sequenceValueInequalitySameElements : Bool :=
  match runFlat (.binary .ne (seqVal [1, 2]) (seqVal [1, 2])) with
  | Except.ok [0] => true
  | _ => false

#guard sequenceValueInequalitySameElements

-- Test 45k: mixed number/string equality returns 0 (different kinds, not a type
-- mismatch). Contrast with Test 44, where `+` on number/string still type-errors.
def mixedNumberStringEqualityDifferentKinds : Bool :=
  match runFlat (.binary .eq (.num 1) (.stringLiteral "a")) with
  | Except.ok [0] => true
  | _ => false

#guard mixedNumberStringEqualityDifferentKinds

def mixedNumberStringInequalityDifferentKinds : Bool :=
  match runFlat (.binary .ne (.num 1) (.stringLiteral "a")) with
  | Except.ok [1] => true
  | _ => false

#guard mixedNumberStringInequalityDifferentKinds

-- Test 45l: ordering operators still reject sequence-value operands.
def numericScalarLtLeftSequenceValueMessage : String :=
  "operator `<` expects numeric scalar operands, but the left operand was a sequence value with 2 sequence elements: (1, 2)"

def orderingSequenceValueOperandStillRejected : Bool :=
  match runResult (.binary .lt (seqVal [1, 2]) (seqVal [1, 2])) with
  | Except.error err =>
      hasContext "while evaluating `(1, 2) < (1, 2)`" err &&
      innermostIsTypeMismatch numericScalarLtLeftSequenceValueMessage err
  | _ => false

#guard orderingSequenceValueOperandStillRejected

-- Test 45m: arithmetic operators still reject sequence-value operands.
def numericScalarAddLeftSequenceValueMessage : String :=
  "operator `+` expects numeric scalar operands, but the left operand was a sequence value with 2 sequence elements: (1, 2)"

def arithmeticSequenceValueOperandStillRejected : Bool :=
  match runResult (.binary .add (seqVal [1, 2]) (seqVal [1, 2])) with
  | Except.error err =>
      hasContext "while evaluating `(1, 2) + (1, 2)`" err &&
      innermostIsTypeMismatch numericScalarAddLeftSequenceValueMessage err
  | _ => false

#guard arithmeticSequenceValueOperandStillRejected

-- Test 45n: structural equality preserves nesting; it must not flatten sequence
-- values. `(1, (2, 3))` has shape [1, [2, 3]] and `((1, 2), 3)` has shape
-- [[1, 2], 3]; they flatten to the same atoms but are structurally unequal.
def nestedSequenceValueEqualityDoesNotFlatten : Bool :=
  let left  := .capture [.num 1, seqVal [2, 3]]
  let right := .capture [seqVal [1, 2], .num 3]
  match runFlat (.binary .eq left right) with
  | Except.ok [0] => true
  | _ => false

#guard nestedSequenceValueEqualityDoesNotFlatten

-- Test 45o: sequence equality is ordered pairwise equality, not set equality.
def sequenceValueEqualityIsOrderSensitive : Bool :=
  match runFlat (.binary .eq (seqVal [1, 2]) (seqVal [2, 1])) with
  | Except.ok [0] => true
  | _ => false

#guard sequenceValueEqualityIsOrderSensitive

-- Test 45p: empty sequence equality is stable across independently bound properties.
-- A = (); B = (); A == B → 1.
def emptyPropertyToPropertyEquality : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [
      ("A", alg [] [] [] [.emptySequence 0]),
      ("B", alg [] [] [] [.emptySequence 0])
    ] [
      .binary .eq (.resolve "A") (.resolve "B")
    ])) with
  | Except.ok [1] => true
  | _ => false

#guard emptyPropertyToPropertyEquality

-- Test 46: Conditional algorithm with string literal pattern
-- Price('apples') = 0.80  (using Int for simplicity: 80)
def priceAlg : Algorithm :=
  .conditional none [] [
    ⟨ .litString "apples",  alg [] [] [] [.num 80] ⟩,
    ⟨ .litString "tomatoes", alg [] [] [] [.num 120] ⟩
  ]

def test46 : Bool :=
  match runFlat (.algorithmExpr (algPrivate [] [] [("Price", priceAlg)] [
    .call (resolve "Price") [.stringLiteral "apples"]
  ])) with
  | Except.ok [80] => true
  | _ => false

#guard test46

-- Test 47: Conditional algorithm with string pattern — no match
def test47 : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("Price", priceAlg)] [
    .call (resolve "Price") [.stringLiteral "bananas"]
  ])) with
  | Except.error _ => true   -- noMatchingBranch
  | Except.ok _    => false

#guard test47

-- Test 48: String passed as algorithm argument
-- Echo = x, Echo('hello') → 'hello'
def echoAlg : Algorithm := alg ["x"] [] [] [.param "x"]
def test48 : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [("Echo", echoAlg)] [
    .call (resolve "Echo") [.stringLiteral "hello"]
  ])) with
  | Except.ok (.str "hello") => true
  | _ => false

#guard test48

-- Test 49: String stored in property and returned
-- Name = 'KatLang', output = Name
def test49 : Bool :=
  let nameAlg := alg [] [] [] [.stringLiteral "KatLang"]
  match runResult (.algorithmExpr (algPrivate [] [] [("Name", nameAlg)] [resolve "Name"])) with
  | Except.ok (.str "KatLang") => true
  | _ => false

#guard test49

-- Test 50: Pattern matching — litString in isMatchEquivalent
def test50a : Bool := Pattern.isMatchEquivalent (.litString "a") (.litString "a")
def test50b : Bool := !Pattern.isMatchEquivalent (.litString "a") (.litString "b")
def test50c : Bool := !Pattern.isMatchEquivalent (.litString "a") (.litInt 1)
def test50d : Bool := !Pattern.isMatchEquivalent (.litString "a") (.bind "x")

#guard test50a
#guard test50b
#guard test50c
#guard test50d

-- Test 51: Block with unresolved implicit params → unresolvedImplicitParams error
-- A block whose algorithm has params (unresolved names become params) should
-- produce unresolvedImplicitParams, not arityMismatch.
def test51 : Bool :=
  -- param "x" makes the block have params=["x"]
  match runResult (.algorithmExpr (alg ["x"] [] [] [.param "x"])) with
  | Except.error (Error.unresolvedImplicitParams ["x"]) => true
  | _ => false

#guard test51

end KatLangTests
