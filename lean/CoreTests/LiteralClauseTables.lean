import KatLang
import CoreTests.Common

namespace KatLangTests
open KatLang (alg algPrivate runFlat runResult Algorithm Error Result)
open KatLang (resolve param num)
open KatLang (Pattern CondBranch)

--------------------------------------------------------------------------------
-- Literal clause tables (2026-11-22; finding values-builtins-numerics-literal-clause-table-quadratic)
--------------------------------------------------------------------------------
-- The family dispatcher is the ordered clause search (`NeedBinder.chooseBranch`): every
-- clause in written order, a literal demanding the value it inspects, the first match
-- selected. C# selects through a run's literal index instead (`Evaluator.LiteralClauseRun`);
-- `LiteralClauseRunTests.TheProgramsLeanShares_ComputeLeansValues_OnEveryRoute` runs these
-- programs, written as source, on every C# route and pins the same values. This file
-- changes no semantics: it guards the shared tier (integer, Boolean and string literals,
-- ticks, failures) of the tables that the C# index serves. The arithmetic below is spelled
-- with functions because `+`, `-`, `*` and `/` build KatLang expressions in this file.

/-- A clause whose head is `pattern` and whose one output row is `row`. -/
def tableClause (pattern : Pattern) (row : KatLang.Expr) : CondBranch :=
  ⟨pattern, alg [] [] [] [row]⟩

def callNamed (name : String) (args : List KatLang.Expr) : KatLang.Expr :=
  .call (resolve name) args

def tickCall : KatLang.Expr := .call (resolve "tick") []

def divideOneByZero : KatLang.Expr := .binary .div (.num 1) (.num 0)

/-- `T(0) = 0`, `T(1) = 3`, … `T(n-1) = 3(n-1)`. -/
def tripleClauses (n : Nat) : List CondBranch :=
  (List.range n).map fun i => tableClause (.litInt (Int.ofNat i)) (.num (Int.mul 3 (Int.ofNat i)))

/-- `G(c div 4, c mod 4) = c` for the sixteen cells `c < 16`. -/
def gridClauses : List CondBranch :=
  (List.range 16).map fun c =>
    tableClause (.sequenceValue [.litInt (Int.ofNat (Nat.div c 4)), .litInt (Int.ofNat (Nat.mod c 4))]) (.num (Int.ofNat c))

def program (props : List (String × Algorithm)) (rows : List KatLang.Expr) : KatLang.Expr :=
  .algorithmExpr (algPrivate [] [] props rows)

-- 1. Every key of a sixteen-clause table, then two misses through the default.
def tripleWithDefault : Algorithm :=
  .conditional none [] (List.append (tripleClauses 16) [tableClause (.bind "k") (.num 100)])

#guard expectFlat
  (runFlat (program [("T", tripleWithDefault)] ((List.range 18).map fun k => callNamed "T" [.num (Int.ofNat k)])))
  (List.append ((List.range 16).map fun i => Int.mul 3 (Int.ofNat i)) [100, 100])

-- 2. A miss of a table without a default is the family's noMatchingBranch.
def tripleOnly : Algorithm := .conditional none [] (tripleClauses 16)

#guard match runResult (program [("T", tripleOnly)] [callNamed "T" [.num 20]]) with
  | Except.error err => innermostIsNoMatchingBranch "T" err
  | Except.ok _ => false

-- 3. Two positions: the second value is demanded only where a clause matches the first.
--    `G(5, 1 / 0)` never divides; each `G(tick(), tick())` ticks twice; the last tick is 5.
def gridWithDefault : Algorithm :=
  .conditional none [] (List.append gridClauses [tableClause (.sequenceValue [.bind "a", .bind "b"]) (.num 99)])

#guard expectFlat
  (runFlat (program [("G", gridWithDefault)]
    [callNamed "G" [.num 2, .num 3], callNamed "G" [.num 3, .num 0], callNamed "G" [.num 5, divideOneByZero],
     callNamed "G" [.num 0, .num 9], callNamed "G" [tickCall, tickCall], callNamed "G" [tickCall, tickCall], tickCall]))
  [11, 12, 99, 99, 6, 99, 5]

-- 4. A matching first value demands the second, whose failure is the call's.
#guard match runResult (program [("G", gridWithDefault)] [callNamed "G" [.num 1, divideOneByZero]]) with
  | Except.error err => innermostIsDivByZero err
  | Except.ok _ => false

-- 5. Nested lookups: an inner dispatch runs inside the outer one's first demand.
def rotationTable : Algorithm :=
  .conditional none [] ((List.range 8).map fun i =>
    tableClause (.litInt (Int.ofNat i)) (.num (Int.ofNat (Nat.mod (Nat.add i 3) 8))))

#guard expectFlat
  (runFlat (program [("N", rotationTable)]
    [callNamed "N" [callNamed "N" [callNamed "N" [.num 2]]], callNamed "N" [callNamed "N" [.num 5]]]))
  [3, 3]

-- 6. String keys: a number is not a text, and a prefix is not the key.
def stringTable : Algorithm :=
  .conditional none [] (List.append
    ((List.range 8).map fun i => tableClause (.litString ("k" ++ toString i)) (.num (Int.ofNat i)))
    [tableClause (.bind "s") (.num (-1))])

#guard expectFlat
  (runFlat (program [("S", stringTable)]
    [callNamed "S" [.stringLiteral "k5"], callNamed "S" [.stringLiteral "k"], callNamed "S" [.num 5], callNamed "S" [.stringLiteral "k7"]]))
  [5, -1, -1, 7]

-- 7. Booleans are not numbers: true and false select their own clauses, 1 and 0 theirs.
def kindTable : Algorithm :=
  .conditional none []
    [tableClause (.litBool true) (.num 1), tableClause (.litBool false) (.num 2), tableClause (.litInt 1) (.num 3),
     tableClause (.litInt 0) (.num 4), tableClause (.bind "x") (.num 5)]

#guard expectFlat
  (runFlat (program [("F", kindTable)]
    [callNamed "F" [.comparison (.num 1) [{ op := .gt, operand := .num 0 }]], callNamed "F" [.num 1],
     callNamed "F" [.comparison (.num 0) [{ op := .gt, operand := .num 1 }]], callNamed "F" [.num 0], callNamed "F" [.num 7]]))
  [1, 3, 2, 4, 5]

-- 8. Two runs split by a structural clause: the clauses are still tried in written order.
def splitTable : Algorithm :=
  .conditional none [] (List.append
    ((List.range 8).map fun i => tableClause (.litInt (Int.ofNat i)) (.num (Int.ofNat i)))
    (List.append
      [tableClause (.sequenceValue [.sequenceValue [.bind "a", .bind "b"]]) (.binary .mul (.param "a") (.param "b"))]
      (List.append
        ((List.range 8).map fun i => tableClause (.litInt (Int.ofNat (Nat.add i 8))) (.num (Int.ofNat (Nat.add i 8))))
        [tableClause (.bind "k") (.num (-1))])))

#guard expectFlat
  (runFlat (program [("T", splitTable)]
    [callNamed "T" [.num 3], callNamed "T" [.capture [.num 6, .num 7]], callNamed "T" [.num 12], callNamed "T" [.num 40]]))
  [3, 42, 12, -1]

end KatLangTests
