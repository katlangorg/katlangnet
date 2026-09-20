import KatLang
import CoreTests.Common

namespace KatLangTests
open KatLang (alg algWithParameters algWithParameterPatterns algPrivate privateProp publicProp privateLocalProp publicLocalProp runFlat runResult Algorithm Error Result PropExposure)
open KatLang (resolve param num)

--------------------------------------------------------------------------------
-- Comparison chains (September 2026): the ONE comparison tier `< <= > >= == !=`
-- is chainable. `Expr.comparison first links` compares ADJACENT operands
-- (`a < b <= c == d` is `a < b`, `b <= c`, `c == d`), evaluates every operand
-- exactly once, left to right, keeps going after a `false` link (eager Boolean
-- composition), stops at the first error, and is `true` iff every link held.
-- C# twins: `ComparisonChainEvaluationTests`, `ComparisonChainParserTests`.
--------------------------------------------------------------------------------

/-- `first op1 x1 op2 x2 …` from alternating operator/operand pairs. -/
def chain (first : KatLang.Expr) (links : List (KatLang.ComparisonOp × KatLang.Expr)) : KatLang.Expr :=
  .comparison first (links.map (fun (op, operand) => { op := op, operand := operand }))

-- Every comparison — one link or many — is a comparison chain, and a one-link
-- chain is the ordinary comparison it always was.
def oneLinkChainsAreOrdinaryComparisons : Bool :=
  evaluatesToBool (.compare .lt (.num 1) (.num 2)) true &&
  evaluatesToBool (.compare .gt (.num 1) (.num 2)) false &&
  evaluatesToBool (.compare .le (.num 2) (.num 2)) true &&
  evaluatesToBool (.compare .ge (.num 1) (.num 2)) false &&
  evaluatesToBool (.compare .eq (.num 2) (.num 2)) true &&
  evaluatesToBool (.compare .ne (.num 2) (.num 2)) false &&
  -- Equality is total across kinds; a Boolean is never a number.
  evaluatesToBool (.compare .eq (.boolLiteral true) (.num 1)) false &&
  evaluatesToBool (.compare .ne (.boolLiteral false) (.num 0)) true &&
  evaluatesToBool (.compare .eq (.stringLiteral "a") (.stringLiteral "a")) true

#guard oneLinkChainsAreOrdinaryComparisons

-- ADJACENT-PAIR semantics over every operator class: ordering-only,
-- equality-only, inequality-only, and mixed chains.
def chainsCompareAdjacentPairs : Bool :=
  -- all true
  evaluatesToBool (chain (.num 1) [(.lt, .num 2), (.lt, .num 3)]) true &&
  evaluatesToBool (chain (.num 1) [(.le, .num 1), (.le, .num 2)]) true &&
  evaluatesToBool (chain (.num 3) [(.gt, .num 2), (.ge, .num 2)]) true &&
  evaluatesToBool (chain (.num 1) [(.eq, .num 1), (.eq, .num 1)]) true &&
  -- `!=` compares ADJACENT pairs only: 1 != 2 and 2 != 1, never "all distinct".
  evaluatesToBool (chain (.num 1) [(.ne, .num 2), (.ne, .num 1)]) true &&
  evaluatesToBool (chain (.num 1) [(.ne, .num 1), (.ne, .num 1)]) false &&
  -- mixed chains: a < b == c, a == b < c, a != b <= c, and the five-operand chain
  evaluatesToBool (chain (.num 1) [(.lt, .num 2), (.eq, .num 2)]) true &&
  evaluatesToBool (chain (.num 1) [(.eq, .num 1), (.lt, .num 2)]) true &&
  evaluatesToBool (chain (.num 1) [(.ne, .num 2), (.le, .num 2)]) true &&
  evaluatesToBool (chain (.num 1) [(.lt, .num 2), (.le, .num 2), (.eq, .num 2), (.ne, .num 3)]) true &&
  -- first / middle / last link false
  evaluatesToBool (chain (.num 2) [(.lt, .num 1), (.lt, .num 3)]) false &&
  evaluatesToBool (chain (.num 1) [(.lt, .num 3), (.lt, .num 2), (.lt, .num 4)]) false &&
  evaluatesToBool (chain (.num 1) [(.lt, .num 2), (.lt, .num 2)]) false &&
  -- equality versus ordering on the same operands
  evaluatesToBool (chain (.num 1) [(.eq, .num 1), (.lt, .num 2)]) true &&
  evaluatesToBool (chain (.num 1) [(.lt, .num 1), (.eq, .num 1)]) false &&
  -- Boolean equality inside a mixed chain: 1 < 2 == true compares 2 with true
  -- structurally, which is false (a number is never a Boolean).
  evaluatesToBool (chain (.num 1) [(.lt, .num 2), (.eq, .boolLiteral true)]) false &&
  -- and a Boolean-valued FIRST operand is fine under equality
  evaluatesToBool (chain (.boolLiteral true) [(.eq, .boolLiteral true), (.ne, .boolLiteral false)]) true

#guard chainsCompareAdjacentPairs

-- The empty chain (host-built only) evaluates its operand and is `true`.
def emptyChainIsTrue : Bool :=
  evaluatesToBool (.comparison (.num 7) []) true &&
  (match runResult (.comparison (.compare .lt (.num 1) (.boolLiteral true)) []) with
   | Except.error err =>
       innermostIsTypeMismatch
         "operator `<` expects numeric scalar operands, but the right operand was a Boolean value: true" err
   | _ => false)

#guard emptyChainIsTrue

-- FALSE DOES NOT STOP A CHAIN: `3 < 2 < true` compares 3 < 2 (false) and then
-- still compares 2 < true, whose Boolean operand is the ordering rejection —
-- reported against THAT link, `2 < true`, never against the whole chain.
def falseLinkNeverShortCircuits : Bool :=
  (match runResult (chain (.num 3) [(.lt, .num 2), (.lt, .boolLiteral true)]) with
   | Except.error err =>
       hasContext "while evaluating `2 < true`" err &&
       innermostIsTypeMismatch
         "operator `<` expects numeric scalar operands, but the right operand was a Boolean value: true" err
   | _ => false) &&
  -- a later operand's evaluation error is reported after an earlier false link
  (match runResult (chain (.num 3) [(.lt, .num 2), (.lt, .binary .div (.num 1) (.num 0))]) with
   | Except.error err => innermostIsDivByZero err
   | _ => false) &&
  -- the same holds when the false link is followed by a string rejection
  (match runResult (chain (.num 3) [(.lt, .num 2), (.lt, .stringLiteral "s")]) with
   | Except.error err => innermostIsTypeMismatch "Cannot apply operator to string and non-string operands" err
   | _ => false)

#guard falseLinkNeverShortCircuits

-- ERRORS TERMINATE: an error in an earlier operand or an earlier link is the
-- chain's outcome; a later invalid link is never reached (the earlier error is
-- what surfaces, not the later one).
def errorsTerminateTheChain : Bool :=
  -- operand error before a later invalid link: the division error wins
  (match runResult (chain (.binary .div (.num 1) (.num 0)) [(.lt, .num 2), (.lt, .boolLiteral true)]) with
   | Except.error err => innermostIsDivByZero err
   | _ => false) &&
  -- link error before a later invalid link: the FIRST link's rejection wins
  (match runResult (chain (.num 1) [(.lt, .boolLiteral true), (.lt, .stringLiteral "s")]) with
   | Except.error err =>
       hasContext "while evaluating `1 < true`" err &&
       innermostIsTypeMismatch
         "operator `<` expects numeric scalar operands, but the right operand was a Boolean value: true" err
   | _ => false) &&
  -- a link error's context names the two ADJACENT operands (here the middle pair)
  (match runResult (chain (.num 1) [(.lt, .num 2), (.gt, .boolLiteral false), (.lt, .num 9)]) with
   | Except.error err =>
       hasContext "while evaluating `2 > false`" err &&
       innermostIsTypeMismatch
         "operator `>` expects numeric scalar operands, but the right operand was a Boolean value: false" err
   | _ => false)

#guard errorsTerminateTheChain

-- EXACTLY-ONCE evaluation at the semantic layer: every explicit call `A()`
-- allocates one binding context (`EvalCtx.bindParameters`), so the evaluation
-- state's binding-context counter observes how many times a written call ran.
-- A middle operand `A()` written ONCE runs once — the chain reuses its VALUE
-- for the second link — exactly like a lone call, while a chain with two
-- written calls runs two.
def middleOperandIsEvaluatedOnce : Bool :=
  let program (body : KatLang.Expr) : KatLang.Expr :=
    .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [] [.num 2])] [body])
  let contextsAfter (body : KatLang.Expr) : Option (Result × Nat) :=
    match KatLang.runResultWithState (program body) with
    | Except.ok (value, state) => some (value, state.nextBindingContext)
    | _ => none
  match contextsAfter (.compare .eq (.call (resolve "A") []) (.num 2)),
        contextsAfter (chain (.num 1) [(.lt, .call (resolve "A") []), (.lt, .num 3)]),
        contextsAfter (chain (.num 1) [(.lt, .call (resolve "A") []), (.lt, .call (resolve "A") [])]) with
  | some (.bool true, once), some (.bool true, middle), some (.bool false, twice) =>
      middle = once && twice = once + 1
  | _, _, _ => false

#guard middleOperandIsEvaluatedOnce

-- Operands are evaluated LEFT TO RIGHT, incrementally: the first operand's
-- error precedes any later operand's evaluation, and the first link is applied
-- before the third operand is evaluated (its error is never reached).
def operandsEvaluateLeftToRightIncrementally : Bool :=
  -- the first operand's error (div0) wins over the second operand's DIFFERENT error
  -- (the string negation), so the first operand was evaluated first
  (match runResult (chain (.binary .div (.num 1) (.num 0)) [(.lt, .unary .minus (.stringLiteral "s"))]) with
   | Except.error err => innermostIsDivByZero err
   | _ => false) &&
  -- and the mirror image: a failing second operand surfaces after a fine first one
  (match runResult (chain (.num 1) [(.lt, .unary .minus (.stringLiteral "s"))]) with
   | Except.error err => innermostIsTypeMismatch "Unary operator is not supported for strings" err
   | _ => false) &&
  (match runResult (chain (.num 1) [(.lt, .boolLiteral true), (.lt, .binary .div (.num 1) (.num 0))]) with
   | Except.error err =>
       innermostIsTypeMismatch
         "operator `<` expects numeric scalar operands, but the right operand was a Boolean value: true" err
   | _ => false)

#guard operandsEvaluateLeftToRightIncrementally

-- A chain is an ordinary Boolean value: it composes with `not`, `and`, and `if`,
-- and a parenthesized chain is an ordinary operand of an outer chain.
def chainsAreOrdinaryBooleanValues : Bool :=
  evaluatesToBool (.unary .not (chain (.num 1) [(.lt, .num 2), (.lt, .num 3)])) false &&
  evaluatesToBool (.binary .and (chain (.num 1) [(.lt, .num 2), (.lt, .num 3)]) (.compare .lt (.num 3) (.num 4))) true &&
  -- (1 < 2) == true: the nested chain's Boolean value is the first operand of the outer chain
  evaluatesToBool (.compare .eq (.compare .lt (.num 1) (.num 2)) (.boolLiteral true)) true &&
  -- (1 < 2 < 3) == true
  evaluatesToBool (.compare .eq (chain (.num 1) [(.lt, .num 2), (.lt, .num 3)]) (.boolLiteral true)) true &&
  -- 1 == (2 < 3 < 4) compares 1 with a Boolean: false, never a chain
  evaluatesToBool (.compare .eq (.num 1) (chain (.num 2) [(.lt, .num 3), (.lt, .num 4)])) false &&
  -- (1 < 2) == (3 < 4)
  evaluatesToBool (.compare .eq (.compare .lt (.num 1) (.num 2)) (.compare .lt (.num 3) (.num 4))) true &&
  -- 1 < (2 == 2) orders a number against a Boolean: the ordering rejection
  (match runResult (.compare .lt (.num 1) (.compare .eq (.num 2) (.num 2))) with
   | Except.error err =>
       hasContext "while evaluating `1 < (2 == 2)`" err &&
       innermostIsTypeMismatch
         "operator `<` expects numeric scalar operands, but the right operand was a Boolean value: true" err
   | _ => false) &&
  (match runFlat (.call (resolve "if") [chain (.num 1) [(.lt, .num 2), (.lt, .num 3)], .num 7, .num 9]) with
   | Except.ok [7] => true
   | _ => false)

#guard chainsAreOrdinaryBooleanValues

-- Plain/counted parity: `eval` is the value projection of `evalCounted` on a
-- chain, and a chain emits exactly one value.
def chainCountedParity : Bool :=
  match runCountedProgram (.algorithmExpr (alg [] [] [] [chain (.num 1) [(.lt, .num 2), (.eq, .num 2)]])) with
  | Except.ok (.bool true, 1) => true
  | _ => false

#guard chainCountedParity

-- DIAGNOSTIC NAMES: a chain renders as the flat chain it is; a parenthesized
-- nested chain, a `not`, and a logical operator keep their parentheses as
-- chain operands; arithmetic, powers, and prefix minus read back bare; a chain
-- under an arithmetic operator or under prefix minus keeps its parentheses;
-- and a link's own name is exactly its two adjacent operands. C# twin:
-- `ExprNameRendererTests.Golden_ComparisonChains_RenderExactly`.
def comparisonChainDiagnosticNames : Bool :=
  let a := KatLang.Expr.resolve "a"
  let b := KatLang.Expr.resolve "b"
  let c := KatLang.Expr.resolve "c"
  let d := KatLang.Expr.resolve "d"
  (KatLang.exprDiagnosticName (.comparison (.num 7) []) == "<comparison with no links>") &&
  (KatLang.exprDiagnosticName (chain a [(.lt, b), (.le, c), (.eq, d)]) == "a < b <= c == d") &&
  (KatLang.exprDiagnosticName (.compare .eq (.compare .lt a b) c) == "(a < b) == c") &&
  (KatLang.exprDiagnosticName (.compare .lt a (.compare .eq b c)) == "a < (b == c)") &&
  (KatLang.exprDiagnosticName (.compare .eq (.compare .lt a b) (.compare .lt c d)) == "(a < b) == (c < d)") &&
  (KatLang.exprDiagnosticName (.compare .eq (.unary .not a) b) == "(not a) == b") &&
  (KatLang.exprDiagnosticName (.compare .eq a (.binary .and b c)) == "a == (b and c)") &&
  (KatLang.exprDiagnosticName (chain (.binary .add a b) [(.lt, .binary .mul c d)]) == "a + b < c * d") &&
  (KatLang.exprDiagnosticName (.compare .lt (.unary .minus (.binary .pow a b)) c) == "-a ^ b < c") &&
  (KatLang.exprDiagnosticName (.binary .add (.compare .lt a b) c) == "(a < b) + c") &&
  (KatLang.exprDiagnosticName (.unary .minus (.compare .lt a b)) == "-(a < b)") &&
  (KatLang.exprDiagnosticName (.unary .not (chain a [(.lt, b), (.lt, c)])) == "not a < b < c") &&
  (KatLang.exprDiagnosticName (.binary .and (.compare .lt a b) (.compare .lt c d)) == "a < b and c < d") &&
  -- a chain (or binary) as a call / dot-call target keeps its parentheses: postfix binds tightest
  (KatLang.exprDiagnosticName (.dotCall (.compare .lt a b) "count" none) == "(a < b).count") &&
  (KatLang.exprDiagnosticName (.call (.binary .add a b) []) == "(a + b)(...)") &&
  (KatLang.exprDiagnosticName (.dotCall (.unary .minus a) "f" none) == "(-a).f") &&
  (KatLang.exprDiagnosticName (.dotCall (.unary .not a) "f" none) == "(not a).f") &&
  (KatLang.exprDiagnosticName (.dotCall (.num (-2)) "abs" none) == "(-2).abs") &&
  (KatLang.exprDiagnosticName (.call (.unary .minus a) []) == "(-a)(...)") &&
  (KatLang.exprDiagnosticName (.index (.num (-2)) (.num 0)) == "(-2):0") &&
  (KatLang.exprDiagnosticName (.sequenceSpread (.num (-2))) == "(-2)*") &&
  (KatLang.comparisonLinkDiagnosticName .lt (.num 2) (.boolLiteral true) == "2 < true") &&
  (KatLang.comparisonLinkDiagnosticName .lt (.capture [.num 1, .num 2]) (.capture [.num 1, .num 2]) == "(1, 2) < (1, 2)")

#guard comparisonChainDiagnosticNames

-- The precedence-faithful binary rendering that comparison chains exposed:
-- nested binaries, equal-tier right operands, and prefix operators over
-- binaries keep exactly the parentheses the ladder needs.
def binaryDiagnosticNamesReadBackFaithfully : Bool :=
  let a := KatLang.Expr.resolve "a"
  let b := KatLang.Expr.resolve "b"
  let c := KatLang.Expr.resolve "c"
  (KatLang.exprDiagnosticName (.binary .add (.binary .add a b) c) == "a + b + c") &&
  (KatLang.exprDiagnosticName (.binary .sub a (.binary .sub b c)) == "a - (b - c)") &&
  (KatLang.exprDiagnosticName (.binary .mul (.binary .add a b) c) == "(a + b) * c") &&
  (KatLang.exprDiagnosticName (.binary .add a (.binary .mul b c)) == "a + b * c") &&
  (KatLang.exprDiagnosticName (.binary .pow (.binary .pow a b) c) == "(a ^ b) ^ c") &&
  (KatLang.exprDiagnosticName (.binary .pow a (.binary .pow b c)) == "a ^ b ^ c") &&
  (KatLang.exprDiagnosticName (.binary .and (.binary .or a b) c) == "(a or b) and c") &&
  (KatLang.exprDiagnosticName (.binary .or a (.binary .and b c)) == "a or b and c") &&
  (KatLang.exprDiagnosticName (.unary .minus (.binary .add a b)) == "-(a + b)") &&
  (KatLang.exprDiagnosticName (.unary .minus (.binary .pow a b)) == "-a ^ b") &&
  (KatLang.exprDiagnosticName (.unary .minus (.unary .minus a)) == "-(-a)") &&
  (KatLang.exprDiagnosticName (.unary .not (.unary .not a)) == "not not a") &&
  (KatLang.exprDiagnosticName (.binary .add (.unary .minus a) b) == "-a + b")

#guard binaryDiagnosticNamesReadBackFaithfully

end KatLangTests
