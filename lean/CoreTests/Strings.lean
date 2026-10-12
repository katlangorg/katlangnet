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
  match runResult (.compare .eq (.stringLiteral "a") (.stringLiteral "a")) with
  | Except.ok (.bool true) => true
  | _ => false

#guard test39

-- Test 40: String equality — different values
def test40 : Bool :=
  match runResult (.compare .eq (.stringLiteral "a") (.stringLiteral "b")) with
  | Except.ok (.bool false) => true
  | _ => false

#guard test40

-- Test 41: String inequality
def test41 : Bool :=
  match runResult (.compare .ne (.stringLiteral "a") (.stringLiteral "b")) with
  | Except.ok (.bool true) => true
  | _ => false

#guard test41

-- Test 42: String equality is case-sensitive
def test42 : Bool :=
  match runResult (.compare .eq (.stringLiteral "Apples") (.stringLiteral "apples")) with
  | Except.ok (.bool false) => true
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
  match runResult (.compare .eq (seqVal [1, 2]) (seqVal [1, 2])) with
  | Except.ok (.bool true) => true
  | _ => false

#guard sequenceValueEqualitySameElements

-- Test 45d: sequence values differing in an element compare unequal.
def sequenceValueEqualityDifferentElement : Bool :=
  match runResult (.compare .eq (seqVal [1, 2]) (seqVal [1, 3])) with
  | Except.ok (.bool false) => true
  | _ => false

#guard sequenceValueEqualityDifferentElement

-- Test 45e: sequence values of different lengths compare unequal.
def sequenceValueEqualityDifferentLength : Bool :=
  match runResult (.compare .eq (seqVal [1, 2]) (seqVal [1, 2, 3])) with
  | Except.ok (.bool false) => true
  | _ => false

#guard sequenceValueEqualityDifferentLength

-- Test 45f: nested sequence values compare recursively (equal).
def nestedSequenceValueEqualityEqual : Bool :=
  let left  := .capture [.num 1, seqVal [2, 3]]
  let right := .capture [.num 1, seqVal [2, 3]]
  match runResult (.compare .eq left right) with
  | Except.ok (.bool true) => true
  | _ => false

#guard nestedSequenceValueEqualityEqual

-- Test 45g: nested sequence values compare recursively (unequal inner element).
def nestedSequenceValueEqualityDifferentInner : Bool :=
  let left  := .capture [.num 1, seqVal [2, 3]]
  let right := .capture [.num 1, seqVal [2, 4]]
  match runResult (.compare .eq left right) with
  | Except.ok (.bool false) => true
  | _ => false

#guard nestedSequenceValueEqualityDifferentInner

-- Test 45h: equality between different value kinds returns 0, never a type error.
def numberVsSequenceValueEqualityDifferentKinds : Bool :=
  match runResult (.compare .eq (.num 1) (seqVal [1, 2])) with
  | Except.ok (.bool false) => true
  | _ => false

#guard numberVsSequenceValueEqualityDifferentKinds

-- Test 45i: inequality is the negation of structural equality across kinds.
def numberVsSequenceValueInequalityDifferentKinds : Bool :=
  match runResult (.compare .ne (.num 1) (seqVal [1, 2])) with
  | Except.ok (.bool true) => true
  | _ => false

#guard numberVsSequenceValueInequalityDifferentKinds

-- Test 45j: `!=` negates structural equality for equal sequence values.
def sequenceValueInequalitySameElements : Bool :=
  match runResult (.compare .ne (seqVal [1, 2]) (seqVal [1, 2])) with
  | Except.ok (.bool false) => true
  | _ => false

#guard sequenceValueInequalitySameElements

-- Test 45k: mixed number/string equality returns 0 (different kinds, not a type
-- mismatch). Contrast with Test 44, where `+` on number/string still type-errors.
def mixedNumberStringEqualityDifferentKinds : Bool :=
  match runResult (.compare .eq (.num 1) (.stringLiteral "a")) with
  | Except.ok (.bool false) => true
  | _ => false

#guard mixedNumberStringEqualityDifferentKinds

def mixedNumberStringInequalityDifferentKinds : Bool :=
  match runResult (.compare .ne (.num 1) (.stringLiteral "a")) with
  | Except.ok (.bool true) => true
  | _ => false

#guard mixedNumberStringInequalityDifferentKinds

-- Test 45l: ordering operators still reject sequence-value operands.
def numericScalarLtLeftSequenceValueMessage : String :=
  "operator `<` expects numeric scalar operands, but the left operand was a sequence value with 2 sequence elements: (1, 2)"

def orderingSequenceValueOperandStillRejected : Bool :=
  match runResult (.compare .lt (seqVal [1, 2]) (seqVal [1, 2])) with
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
  match runResult (.compare .eq left right) with
  | Except.ok (.bool false) => true
  | _ => false

#guard nestedSequenceValueEqualityDoesNotFlatten

-- Test 45o: sequence equality is ordered pairwise equality, not set equality.
def sequenceValueEqualityIsOrderSensitive : Bool :=
  match runResult (.compare .eq (seqVal [1, 2]) (seqVal [2, 1])) with
  | Except.ok (.bool false) => true
  | _ => false

#guard sequenceValueEqualityIsOrderSensitive

-- Test 45p: empty sequence equality is stable across independently bound properties.
-- A = (); B = (); A == B → 1.
def emptyPropertyToPropertyEquality : Bool :=
  match runResult (.algorithmExpr (algPrivate [] [] [
      ("A", alg [] [] [] [.emptySequence 0]),
      ("B", alg [] [] [] [.emptySequence 0])
    ] [
      .compare .eq (.resolve "A") (.resolve "B")
    ])) with
  | Except.ok (.bool true) => true
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

-- Final audit (September 2026): the `.string` intrinsic is a ZERO-parameter member.
-- A written argument list is assembled like every call's and then rejected by
-- arity (`arityMismatch 0 n`) on BOTH receiver paths — the algorithm receiver
-- (`(block [123]).string(1)`) and the value receiver (`(42).string(1, 2)`) — a
-- spread slot counts by its opened items, and an EMPTY written list (`x.string()`)
-- stays the intrinsic. C#: `RejectDotStringIntrinsicArguments`.
def testStringIntrinsicRejectsArguments_AlgorithmReceiver : Bool :=
  match runResult (.dotCall (.algorithmExpr (alg [] [] [] [.num 123])) "string" (some [.num 1])) with
  | Except.error err => innermostIsArityMismatch 0 1 err
  | _ => false

def testStringIntrinsicRejectsArguments_ValueReceiver : Bool :=
  match runResult (.dotCall (.num 42) "string" (some [.num 1, .num 2])) with
  | Except.error err => innermostIsArityMismatch 0 2 err
  | _ => false

def testStringIntrinsicRejectsArguments_SpreadCountsOpenedItems : Bool :=
  let three := alg [] [] [] [.num 1, .num 2, .num 3]
  match runResult (.dotCall (.num 42) "string" (some [.sequenceSpread (.algorithmExpr three)])) with
  | Except.error err => innermostIsArityMismatch 0 3 err
  | _ => false

def testStringIntrinsicEmptyArgumentList_StaysTheIntrinsic : Bool :=
  match runResult (.dotCall (.num 42) "string" (some [])) with
  | Except.ok (Result.str "42") => true
  | _ => false

#guard testStringIntrinsicRejectsArguments_AlgorithmReceiver
#guard testStringIntrinsicRejectsArguments_ValueReceiver
#guard testStringIntrinsicRejectsArguments_SpreadCountsOpenedItems
#guard testStringIntrinsicEmptyArgumentList_StaysTheIntrinsic

-- Q-45 (RESOLVED BY DECISION 2026-10-10: the Model-C order is the law). A written
-- argument list of the `.string` intrinsic follows the ordinary call steps (NEED-05):
-- the supply is formed — an explicit spread executes there, and its failure is raised
-- there — every other slot stays suspended, a supply of one or more items is rejected
-- by cardinality before the receiver or any ordinary argument is demanded, and only a
-- supply of zero items reaches the intrinsic, which then demands its receiver. There is
-- no argument-first or receiver-first rule. Lean models no host effects, so these
-- trace-free twins observe the order through failures: a computation that is never
-- demanded cannot fail. C#:
-- `ModelCPropagationTests.StringIntrinsicArguments_AreFormedAndRejectedBeforeAnyDemand`.
def q45Fails : KatLang.Expr := .binary .div (.num 1) (.num 0)

def q45StringCall (receiver : KatLang.Expr) (args : List KatLang.Expr) : KatLang.Expr :=
  .dotCall receiver "string" (some args)

def q45IsTypeMismatch : Error -> Bool
  | .withContext _ inner => q45IsTypeMismatch inner
  | .typeMismatch _ => true
  | _ => false

-- `(1 / 0).string(1 / 0)` and `{ 1 / 0 }.string(1 / 0)`: on both receiver paths the
-- cardinality rejection demands neither the receiver nor the ordinary argument.
def testQ45_RejectionDemandsNothing : Bool :=
  [q45Fails, .algorithmExpr (alg [] [] [] [q45Fails])].all fun receiver =>
    match runResult (q45StringCall receiver [q45Fails]) with
    | Except.error err => innermostIsArityMismatch 0 1 err
    | _ => false

-- `(1 / 0).string([2]*)`: the spread is formed — its one item is counted — and the
-- receiver is still never demanded.
def testQ45_FormedSpreadIsCountedWithoutTheReceiver : Bool :=
  match runResult (q45StringCall q45Fails [.sequenceSpread (.listLiteral [.num 2])]) with
  | Except.error err => innermostIsArityMismatch 0 1 err
  | _ => false

-- `42.string([1 / 0]*)`: an explicit spread executes while the supply is formed, so its
-- failure is raised there, before the cardinality check.
def testQ45_SpreadFailureIsRaisedAtFormation : Bool :=
  match runResult (q45StringCall (.num 42) [.sequenceSpread (.listLiteral [q45Fails])]) with
  | Except.error err => innermostIsDivByZero err
  | _ => false

-- `(1 / 0).string([not 1]*)`: formation precedes the receiver demand — the spread's own
-- failure is reported, never the receiver's division.
def testQ45_FormationPrecedesTheReceiver : Bool :=
  match runResult (q45StringCall q45Fails [.sequenceSpread (.listLiteral [.unary .not (.num 1)])]) with
  | Except.error err => q45IsTypeMismatch err && !innermostIsDivByZero err
  | _ => false

-- `42.string(()*)`, `(1 / 0).string(()*)` and `{ 1 / 0 }.string()`: a supply of zero
-- items — a spread that supplies none, or an empty written list — is the intrinsic
-- itself, which demands its receiver after formation.
def testQ45_ZeroItemSupplyDemandsTheReceiver : Bool :=
  (match runResult (q45StringCall (.num 42) [.sequenceSpread (.emptySequence 0)]) with
   | Except.ok (Result.str "42") => true
   | _ => false) &&
  (match runResult (q45StringCall q45Fails [.sequenceSpread (.emptySequence 0)]) with
   | Except.error err => innermostIsDivByZero err
   | _ => false) &&
  (match runResult (q45StringCall (.algorithmExpr (alg [] [] [] [q45Fails])) []) with
   | Except.error err => innermostIsDivByZero err
   | _ => false)

#guard testQ45_RejectionDemandsNothing
#guard testQ45_FormedSpreadIsCountedWithoutTheReceiver
#guard testQ45_SpreadFailureIsRaisedAtFormation
#guard testQ45_FormationPrecedesTheReceiver
#guard testQ45_ZeroItemSupplyDemandsTheReceiver

--------------------------------------------------------------------------------
-- String interpolation (STR-02, VAL-12)
--------------------------------------------------------------------------------
-- `"head{h1}t1…"` is `.interpolatedString head [{ hole := h1, text := t1 }, …]`. When its
-- value is demanded the holes are evaluated LEFT TO RIGHT, each EXACTLY ONCE, each value
-- converted at once to its structural text (`Result.canonicalText`: numbers, `true`/`false`,
-- strings VERBATIM at every nesting level, `(a, b)`, `[a, b]`, `()`, `[]`), the first failure
-- ends the node, and the result is ONE string. The laws are theorems over `interpolateWith`
-- (`KatLangArityLaws.lean` § String interpolation); these guards pin that the evaluator arm
-- instantiates it with the ordinary value read. Effects are counted, as in
-- `CoreTests.ArgumentValueOutcome`, by the binding contexts a run opens: `Id(5)` opens one.

/-- One link: a hole and the decoded text written after it. -/
def ipLink (hole : KatLang.Expr) (text : String := "") : KatLang.InterpolationLink := { hole, text }

def ipText (e : KatLang.Expr) (expected : String) : Bool :=
  match runResult e with
  | Except.ok (Result.str s) => s == expected
  | _ => false

-- A hole-free node is its head, exactly like the string literal (the parser never builds
-- one; a host-built one evaluates to its text).
#guard ipText (.interpolatedString "abc" []) "abc"
#guard ipText (.interpolatedString "" []) ""
-- Number, string and Boolean holes; a string is inserted verbatim and never re-scanned.
#guard ipText (.interpolatedString "n=" [ipLink (.num 42) "!"]) "n=42!"
#guard ipText (.interpolatedString "" [ipLink (.num (-5))]) "-5"
#guard ipText (.interpolatedString "Hi " [ipLink (.stringLiteral "Ada") "."]) "Hi Ada."
#guard ipText (.interpolatedString "" [ipLink (.stringLiteral "{Unknown}")]) "{Unknown}"
#guard ipText (.interpolatedString "" [ipLink (.boolLiteral true) " ", ipLink (.boolLiteral false)]) "true false"
#guard ipText (.interpolatedString "" [ipLink (.comparison (.num 1) [{ op := .lt, operand := .num 2 }])]) "true"
-- Sequences and lists keep their boundaries; strings stay unquoted inside them; `()` and `[]`
-- are values with distinct text.
#guard ipText (.interpolatedString "" [ipLink (.capture [.num 1, .num 2])]) "(1, 2)"
#guard ipText (.interpolatedString "" [ipLink (.capture [.stringLiteral "Alice", .stringLiteral "Bob"])]) "(Alice, Bob)"
#guard ipText (.interpolatedString "" [ipLink (.listLiteral [.stringLiteral "Alice", .stringLiteral "Bob"])]) "[Alice, Bob]"
#guard ipText (.interpolatedString "" [ipLink (.listLiteral [.num 1, .stringLiteral "Alice", .boolLiteral true])]) "[1, Alice, true]"
#guard ipText (.interpolatedString "" [ipLink (.emptySequence 0)]) "()"
#guard ipText (.interpolatedString "" [ipLink (.listLiteral [])]) "[]"
#guard ipText (.interpolatedString ""
    [ipLink (.listLiteral [.capture [.num 1, .num 2], .listLiteral [.stringLiteral "A", .stringLiteral "B"]])])
  "[(1, 2), [A, B]]"
#guard ipText (.interpolatedString "" [ipLink (.listLiteral [.stringLiteral "one, two", .stringLiteral "three"])])
  "[one, two, three]"
-- A one-item list is a list; a singleton sequence normalizes to its item before the text.
#guard ipText (.interpolatedString "" [ipLink (.listLiteral [.num 7])]) "[7]"
#guard ipText (.interpolatedString "" [ipLink (.algorithmExpr (alg [] [] [] [.capture [.num 7]]))]) "7"
-- Nested interpolation.
#guard ipText (.interpolatedString "outer [" [ipLink (.interpolatedString "inner " [ipLink (.binary .add (.num 1) (.num 1))]) "]"])
  "outer [inner 2]"

-- No callable identity: calling an interpolated string is `notAnAlgorithm`.
#guard match runResult (.call (.interpolatedString "x" [ipLink (.num 1)]) []) with
  | Except.error err => innermostIsNotAnAlgorithm "interpolated string" err
  | _ => false

-- An output-less hole is its ordinary `missingOutput`, never empty text or `()`.
#guard match runResult (.interpolatedString "a" [ipLink (.algorithmExpr (alg [] [] [] []))]) with
  | Except.error err => innermostIsMissingOutput err
  | _ => false

-- The FIRST failure ends it: a failing hole before an ill-kinded one reports the first, and
-- the reverse order the other.
#guard match runResult (.interpolatedString "" [ipLink (.binary .div (.num 1) (.num 0)), ipLink (.unary .minus (.stringLiteral "s"))]) with
  | Except.error err => innermostIsDivByZero err
  | _ => false
#guard match runResult (.interpolatedString "" [ipLink (.unary .minus (.stringLiteral "s")), ipLink (.binary .div (.num 1) (.num 0))]) with
  | Except.error err => innermostIsAnyTypeMismatch err
  | _ => false

/-- `Id(y) = y`, `Bad = Id(1) / 0`, `K(s) = 5`, `F(x) = "{x}|{x}"`, `S = "{Id(5)}"`. -/
def ipRoot (out : List KatLang.Expr) : KatLang.Expr :=
  .algorithmExpr (algPrivate [] []
    [ ("Id", alg ["y"] [] [] [param "y"])
    , ("Bad", alg [] [] [] [.binary .div (.call (resolve "Id") [num 1]) (num 0)])
    , ("K", alg ["s"] [] [] [num 5])
    , ("F", alg ["x"] [] [] [.interpolatedString "" [ipLink (param "x") "|", ipLink (param "x")]])
    , ("S", alg [] [] [] [.interpolatedString "" [ipLink (.call (resolve "Id") [num 5])]]) ]
    out)

/-- The outcome of a run and the binding contexts it opened (kept for a failed run too). -/
def ipRun (out : List KatLang.Expr) : Except Error Result × Nat :=
  let (result, state) := (KatLang.runResultM (ipRoot out)).runState KatLang.EvalState.empty
  (result, state.nextBindingContext - 1)

/-- The run succeeds with `expected` after opening exactly `contexts` binding contexts. -/
def ipRunsTo (out : List KatLang.Expr) (expected : Result) (contexts : Nat) : Bool :=
  match ipRun out with
  | (.ok value, opened) => value == expected && opened == contexts
  | _ => false

-- Each hole once, left to right: two holes calling `Id` open two contexts.
#guard ipRunsTo [.interpolatedString "" [ipLink (.call (resolve "Id") [num 5]), ipLink (.call (resolve "Id") [num 6])]]
  (.str "56") 2
-- A failing first hole stops the node: the later hole's `Id(5)` never runs (only `Bad`'s own
-- `Id(1)` opened a context); in the other order both ran.
#guard match ipRun [.interpolatedString "" [ipLink (resolve "Bad"), ipLink (.call (resolve "Id") [num 5])]] with
  | (.error err, contexts) => innermostIsDivByZero err && contexts == 1
  | _ => false
#guard match ipRun [.interpolatedString "" [ipLink (.call (resolve "Id") [num 5]), ipLink (resolve "Bad")]] with
  | (.error err, contexts) => innermostIsDivByZero err && contexts == 2
  | _ => false
-- An undemanded interpolation evaluates no hole: `K` never reads its argument.
#guard ipRunsTo [.call (resolve "K") [.interpolatedString "" [ipLink (resolve "Bad")]]] (.atom 5) 1
-- ... and `if` evaluates only the selected branch.
#guard ipRunsTo [.call (resolve "if") [.boolLiteral true, .stringLiteral "ok", .interpolatedString "" [ipLink (resolve "Bad")]]]
  (.str "ok") 0
-- A parameter read twice in one string is ONE supplied computation: `F(Id(5))` opens F's
-- context and Id's, once.
#guard ipRunsTo [.call (resolve "F") [.call (resolve "Id") [num 5]]] (.str "5|5") 2
-- A zero-parameter property holding an interpolation is cached per binding: `S, S` runs its
-- hole once; the explicit `S()` evaluates afresh.
#guard ipRunsTo [resolve "S", resolve "S"] (.sequenceValue [.str "5", .str "5"]) 1
#guard ipRunsTo [.call (resolve "S") [], .call (resolve "S") []] (.sequenceValue [.str "5", .str "5"]) 4

-- An interpolated string equals the literal with the same text (no provenance), counts as
-- one value, and is matched by a literal clause pattern.
#guard match runResult (.comparison (.interpolatedString "a" [ipLink (.num 1) "b"]) [{ op := .eq, operand := .stringLiteral "a1b" }]) with
  | Except.ok (Result.bool true) => true
  | _ => false
#guard match runResult (.call (resolve "count") [.interpolatedString "x" [ipLink (.num 1)]]) with
  | Except.ok (Result.atom 1) => true
  | _ => false
#guard match runResult (.algorithmExpr (algPrivate [] []
    [("Kind", .conditional none [] [{ pattern := .litString "circle", body := alg [] [] [] [num 1] },
                                     { pattern := .bind "other", body := alg [] [] [] [num 0] }] none)]
    [.call (resolve "Kind") [.interpolatedString "cir" [ipLink (.stringLiteral "cle")]]])) with
  | Except.ok (Result.atom 1) => true
  | _ => false

-- Post-elaboration and validation walk into holes: an unelaborated `load` in a hole violates
-- the invariant, and an alias inside a hole block is counted.
#guard !KatLang.postElabInvariant (.interpolatedString "" [ipLink (.call (resolve "load") [.stringLiteral "u"])])
#guard KatLang.postElabInvariant (.interpolatedString "" [ipLink (.num 1)])

-- The diagnostic name of an interpolated string reads back as source: a hole whose name could
-- BEGIN with a brace (a block at the left end of its spine) is spaced, so `{{` never reads as a
-- literal brace, while a block further right needs nothing (C#: `ExprNameRendererTests`).
#guard KatLang.exprDiagnosticName (.interpolatedString "x" [ipLink (resolve "a")]) == "\"x{a}\""
#guard KatLang.holeMayRenderLeadingBrace (.binary .add (.algorithmExpr (alg [] [] [] [num 1])) (num 2))
#guard KatLang.holeMayRenderLeadingBrace (.index (.algorithmExpr (alg [] [] [] [num 1])) [num 0])
#guard !KatLang.holeMayRenderLeadingBrace (.binary .add (num 2) (.algorithmExpr (alg [] [] [] [num 1])))
#guard (KatLang.exprDiagnosticName
    (.interpolatedString "x" [ipLink (.binary .add (.algorithmExpr (alg [] [] [] [num 1])) (num 2))])).startsWith "\"x{ "

end KatLangTests
