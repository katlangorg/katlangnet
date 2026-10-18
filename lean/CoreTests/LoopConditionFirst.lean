import KatLang
import CoreTests.Common

namespace KatLangTests
open KatLang (alg algPrivate runResult Algorithm Error Result)
open KatLang (resolve param num)

--------------------------------------------------------------------------------
-- A `while` ROUND READS ITS CONDITION FIRST (LOOP-06; LOOP-CF1, decided October 2026)
--------------------------------------------------------------------------------
-- A `while` round forms the step's rows from the LAST row backwards until a row
-- supplies an item (`WhileRound.discover`); that row's last item is the Boolean
-- flag. `false` returns the state that entered the round WITHOUT forming the
-- remaining earlier rows; `true` forms them left to right, and the supply without
-- its last item is the next state (a one-item supply is both). Protection is
-- row-granular: a call or spread inside one row is one ordinary value. `repeat`
-- and ordinary calls still form every row left to right.
--
-- C#: `LoopConditionFirstTests` (six routes, host effects, budgets), the spec
-- cases `loop-while-condition-first-*`. Laws: `KatLangArityLaws/WhileRound.lean`.

private def cfDiv (a b : KatLang.Expr) : KatLang.Expr := .binary .div a b
private def cfSub (a : KatLang.Expr) (n : Int) : KatLang.Expr := .binary .sub a (.num n)
private def cfAdd (a b : KatLang.Expr) : KatLang.Expr := .binary .add a b
private def cfCmp (a : KatLang.Expr) (op : KatLang.ComparisonOp) (b : KatLang.Expr) : KatLang.Expr :=
  .comparison a [⟨op, b⟩]
private def cfSpread (callee : String) (args : List KatLang.Expr) : KatLang.Expr :=
  .sequenceSpread (.call (resolve callee) args)

-- Step(x) = 10 / (x - 1), x > 1
def cfStepAlg : Algorithm :=
  alg ["x"] [] [] [cfDiv (.num 10) (cfSub (.param "x") 1), cfCmp (.param "x") .gt (.num 1)]

-- Count(x) = x - 1, x > 1
def cfCountAlg : Algorithm :=
  alg ["x"] [] [] [cfSub (.param "x") 1, cfCmp (.param "x") .gt (.num 1)]

-- Fib(a, b, n) = b, a + b, n - 1, n > 1
def cfFibAlg : Algorithm :=
  alg ["a", "b", "n"] [] []
    [.param "b", cfAdd (.param "a") (.param "b"), cfSub (.param "n") 1, cfCmp (.param "n") .gt (.num 1)]

-- Fs(a, b) = b, a + b, a < 100
def cfFibStopAlg : Algorithm :=
  alg ["a", "b"] [] [] [.param "b", cfAdd (.param "a") (.param "b"), cfCmp (.param "a") .lt (.num 100)]

-- Col(n, k) = if(n mod 2 == 0, n div 2, 3 * n + 1), k + 1, n != 1
def cfCollatzAlg : Algorithm :=
  alg ["n", "k"] [] []
    [.call (resolve "if") [cfCmp (.binary .mod (.param "n") (.num 2)) .eq (.num 0),
        .binary .idiv (.param "n") (.num 2), cfAdd (.binary .mul (.num 3) (.param "n")) (.num 1)],
     cfAdd (.param "k") (.num 1),
     cfCmp (.param "n") .ne (.num 1)]

-- Twice(x) = 10 / (x - 1), 10 / (x - 1) > 0       (the flag itself divides)
def cfFlagDividesAlg : Algorithm :=
  alg ["x"] [] [] [cfDiv (.num 10) (cfSub (.param "x") 1),
    cfCmp (cfDiv (.num 10) (cfSub (.param "x") 1)) .gt (.num 0)]

-- Sh(x) = { Q = 10 / (x - 1) ⏎ Q, Q > 0 }        (a shared failing local)
def cfSharedFailingAlg : Algorithm :=
  alg ["x"] [] [KatLang.privateProp "Q" (alg [] [] [] [cfDiv (.num 10) (cfSub (.param "x") 1)])]
    [resolve "Q", cfCmp (resolve "Q") .gt (.num 0)]

-- Pack(x) = 10 / (x - 1), x > 1 ;  Wrapped(x) = Pack(x)*
def cfWrappedAlg : Algorithm := alg ["x"] [] [] [cfSpread "Step" [.param "x"]]

-- Tail(n) = () ;  Tl(n) = n + 1, n < 2, Tail(n)*
def cfTailAlg : Algorithm := alg ["n"] [] [] [.emptySequence 0]
def cfTrailingAlg : Algorithm :=
  alg ["n"] [] [] [cfAdd (.param "n") (.num 1), cfCmp (.param "n") .lt (.num 2), cfSpread "Tail" [.param "n"]]

-- Bad(x) = if(x > 'a', (), ()) ;  Tr(x) = 1 / 0, false, Bad(x)*
-- (the trailing row is formed FIRST and fails; step-first would divide by zero first)
def cfBadTailAlg : Algorithm :=
  alg ["x"] [] [] [.call (resolve "if") [cfCmp (.param "x") .gt (.stringLiteral "a"), .emptySequence 0, .emptySequence 0]]
def cfTrailingFailsAlg : Algorithm :=
  alg ["x"] [] [] [cfDiv (.num 1) (.num 0), .boolLiteral false, cfSpread "Bad" [.param "x"]]

-- Fam(0) = 0, false ;  Fam(n) = n - 1, n > 0
def cfFamilyAlg : Algorithm :=
  .conditional none [] [
    ⟨ .litInt 0, alg [] [] [] [.num 0, .boolLiteral false] ⟩,
    ⟨ .bind "n", alg [] [] [] [cfSub (.param "n") 1, cfCmp (.param "n") .gt (.num 0)] ⟩
  ]

-- Done(n) = (n - 1, n > 1) ;  Sp(a, n) = a + 1, Done(n)*   (the flag inside a spread row)
def cfDoneAlg : Algorithm :=
  alg ["n"] [] [] [.capture [cfSub (.param "n") 1, cfCmp (.param "n") .gt (.num 1)]]
def cfSpreadFlagAlg : Algorithm :=
  alg ["a", "n"] [] [] [cfAdd (.param "a") (.num 1), cfSpread "Done" [.param "n"]]

-- Not(x) = not x                                    (one item: flag and state)
def cfNotAlg : Algorithm := alg ["x"] [] [] [.unary .not (.param "x")]

-- Ee(x) = Tail(x)*, Tail(x)*                         (no item at all)
def cfEmptyAlg : Algorithm := alg ["x"] [] [] [cfSpread "Tail" [.param "x"], cfSpread "Tail" [.param "x"]]

-- Init(x, y) = x - 1, y, x > 0 ;  Over(x, y) = x - 1, 0, x > 0
def cfInitAlg : Algorithm :=
  alg ["x", "y"] [] [] [cfSub (.param "x") 1, .param "y", cfCmp (.param "x") .gt (.num 0)]
def cfOverAlg : Algorithm :=
  alg ["x", "y"] [] [] [cfSub (.param "x") 1, .num 0, cfCmp (.param "x") .gt (.num 0)]

-- Ar(a, b) = a + b, true ;  Dc(a, b) = (a, b, a)*, a > 5
def cfArityAlg : Algorithm := alg ["a", "b"] [] [] [cfAdd (.param "a") (.param "b"), .boolLiteral true]
def cfDiscardedAlg : Algorithm :=
  alg ["a", "b"] [] [] [.sequenceSpread (.capture [.param "a", .param "b", .param "a"]), cfCmp (.param "a") .gt (.num 5)]

-- Nb1(x) = 1 / 0, 'a' < 1 ;  Nb2(x) = 1 / 0, 5 ;  Ok(x) = 1 / 0, false
def cfNonBoolCmpAlg : Algorithm :=
  alg ["x"] [] [] [cfDiv (.num 1) (.num 0), cfCmp (.stringLiteral "a") .lt (.num 1)]
def cfNonBoolNumAlg : Algorithm := alg ["x"] [] [] [cfDiv (.num 1) (.num 0), .num 5]
def cfFailThenFalseAlg : Algorithm := alg ["x"] [] [] [cfDiv (.num 1) (.num 0), .boolLiteral false]

-- Cy(x) = { P = P + 1 ⏎ P, x > 1 }                 (a cycle only the transition row reaches)
def cfCycleAlg : Algorithm :=
  alg ["x"] [] [KatLang.privateProp "P" (alg [] [] [] [cfAdd (resolve "P") (.num 1)])]
    [resolve "P", cfCmp (.param "x") .gt (.num 1)]

-- C1(x) = x - 1, x > 0 ;  C2(x) = x - 1, x - 1 > 0  (input-value and candidate-value flags)
def cfInputFlagAlg : Algorithm := alg ["x"] [] [] [cfSub (.param "x") 1, cfCmp (.param "x") .gt (.num 0)]
def cfCandidateFlagAlg : Algorithm :=
  alg ["x"] [] [] [cfSub (.param "x") 1, cfCmp (cfSub (.param "x") 1) .gt (.num 0)]

private def cfProgram (rows : List KatLang.Expr) : KatLang.Expr :=
  .algorithmExpr (algPrivate [] [] [
    ("Step", cfStepAlg), ("Count", cfCountAlg), ("Fib", cfFibAlg), ("Fs", cfFibStopAlg),
    ("Col", cfCollatzAlg), ("Twice", cfFlagDividesAlg), ("Sh", cfSharedFailingAlg),
    ("Wrapped", cfWrappedAlg), ("Tail", cfTailAlg), ("Tl", cfTrailingAlg), ("Bad", cfBadTailAlg),
    ("Tr", cfTrailingFailsAlg), ("Fam", cfFamilyAlg), ("Done", cfDoneAlg), ("Sp", cfSpreadFlagAlg),
    ("Not", cfNotAlg), ("Ee", cfEmptyAlg), ("Init", cfInitAlg), ("Over", cfOverAlg),
    ("Ar", cfArityAlg), ("Dc", cfDiscardedAlg), ("Nb1", cfNonBoolCmpAlg), ("Nb2", cfNonBoolNumAlg),
    ("Ok", cfFailThenFalseAlg), ("Cy", cfCycleAlg), ("C1", cfInputFlagAlg), ("C2", cfCandidateFlagAlg),
    ("Al", .alias none [] [] (resolve "Count")),
    -- Run(f, x) = while(f, x)
    ("Run", alg ["f", "x"] [] [] [.call (resolve "while") [.param "f", .param "x"]])
  ] rows)

private def cfWhile (step : String) (state : List KatLang.Expr) : KatLang.Expr :=
  .call (resolve "while") (resolve step :: state)

private def cfOk (rows : List KatLang.Expr) (expected : Result) : Bool :=
  match runResult (cfProgram rows) with
  | .ok value => value == expected
  | _ => false

private def cfFails (rows : List KatLang.Expr) (check : Error -> Bool) : Bool :=
  match runResult (cfProgram rows) with
  | .error e => check e
  | _ => false

-- 1. Initially false: the division row is never formed; the initial state returns.
#guard cfOk [cfWhile "Step" [.num 1]] (.atom 1)
-- ... while `repeat` (and the ordinary call) still form every row left to right.
#guard cfFails [.call (resolve "repeat") [resolve "Step", .num 1, .num 1]] innermostIsDivByZero
#guard cfFails [.call (resolve "Step") [.num 1]] innermostIsDivByZero
-- 2. Initially true: the transition runs.
#guard cfOk [cfWhile "Count" [.num 4]] (.atom 1)
-- 3/5. Multi-slot state: zero transitions keep the initial slots; Fibonacci keeps its values.
#guard cfOk [cfWhile "Fs" [.num 144, .num 233]] (.sequenceValue [.atom 144, .atom 233])
#guard cfOk [cfWhile "Fib" [.num 0, .num 1, .num 10]] (.sequenceValue [.atom 34, .atom 55, .atom 1])
-- 6. Collatz: 111 accepted transitions from 27; an initially stopped state returns unchanged.
#guard cfOk [cfWhile "Col" [.num 27, .num 0]] (.sequenceValue [.atom 1, .atom 111])
#guard cfOk [cfWhile "Col" [.num 1, .num 0]] (.sequenceValue [.atom 1, .atom 0])
-- 9. What the flag itself needs still runs: its own and a shared local's division fail.
#guard cfFails [cfWhile "Twice" [.num 1]] innermostIsDivByZero
#guard cfFails [cfWhile "Sh" [.num 1]] innermostIsDivByZero
-- 10. Row granularity: a flag produced inside one spread call row gets no early exit.
#guard cfFails [cfWhile "Wrapped" [.num 1]] innermostIsDivByZero
-- 11. Trailing empty spreads: discovery passes them right to left; the flag is the last item.
#guard cfOk [cfWhile "Tl" [.num 0]] (.atom 2)
-- ... and the trailing row is formed FIRST: its failure precedes the earlier row's.
#guard cfFails [cfWhile "Tr" [.num 1]] innermostIsAnyTypeMismatch
-- 13. A flag supplied inside a spread row: the row's other items join the state after `true`.
#guard cfOk [cfWhile "Sp" [.num 0, .num 3]] (.sequenceValue [.atom 2, .atom 1])
-- 14. A family dispatches first; the selected clause's rows are read condition first.
#guard cfOk [cfWhile "Fam" [.num 2]] (.atom 0)
-- 15/17. Builtin, alias and higher-order steps keep their eligibility.
#guard cfOk [cfWhile "if" [.boolLiteral true, .boolLiteral false, .boolLiteral true]]
  (.sequenceValue [.bool true, .bool false, .bool true])
#guard cfOk [cfWhile "Al" [.num 3]] (.atom 1)
#guard cfOk [.call (resolve "Run") [resolve "Count", .num 3]] (.atom 1)
-- 18/19. One item is both flag and state; no item at all is the missing-flag BadArity.
#guard cfOk [cfWhile "Not" [.boolLiteral false]] (.bool true)
#guard cfFails [cfWhile "Ee" [.num 1]] innermostIsBadArity
#guard cfFails [cfWhile "Ee" [.num 1]] (hasContext "a while step must output at least its continuation flag")
-- 20. The next round's binder checks an accepted state; a false round forms no candidate.
#guard cfFails [cfWhile "Ar" [.num 1, .num 2]] innermostIsAnyArityMismatch
#guard cfOk [cfWhile "Dc" [.num 1, .num 2]] (.sequenceValue [.atom 1, .atom 2])
-- 21. A failing unread initial component fails at the final materialization (LOOP-07);
--     an overwritten one is never demanded.
#guard cfFails [cfWhile "Init" [.num 0, cfDiv (.num 1) (.num 0)]] innermostIsDivByZero
#guard cfOk [cfWhile "Over" [.num 1, cfDiv (.num 1) (.num 0)]] (.sequenceValue [.atom 0, .atom 0])
-- Error precedence: the flag row's non-Boolean value is reported before an earlier failure.
#guard cfFails [cfWhile "Nb1" [.num 1]] innermostIsAnyTypeMismatch
#guard cfFails [cfWhile "Nb2" [.num 1]] innermostIsAnyTypeMismatch
-- 26. An earlier failing row is skipped by a false flag (step-first failed with DivByZero).
#guard cfOk [cfWhile "Ok" [.num 1]] (.atom 1)
-- 27. A cycle reached only from a skipped row is never entered.
#guard cfOk [cfWhile "Cy" [.num 1]] (.atom 1)
-- Input-value and candidate-value flags keep their meaning.
#guard cfOk [cfWhile "C1" [.num 1], cfWhile "C2" [.num 1]] (.sequenceValue [.atom 0, .atom 1])

end KatLangTests
