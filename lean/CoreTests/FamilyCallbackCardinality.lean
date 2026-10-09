import KatLang
import CoreTests.Common

namespace KatLangTests
open KatLang (alg algPrivate runResult Algorithm Error Result)
open KatLang (resolve)

--------------------------------------------------------------------------------
-- A CLAUSE-FAMILY CALLBACK IS JUDGED BY ITS OWN EMITTED COUNT (HO-03 + PAT-11)
--------------------------------------------------------------------------------
-- A `map` transform and a `reduce` step must each EMIT exactly one top-level
-- value that is not `()` (`expectSingleMappedElement` /
-- `expectSingleAccumulator`), judged by the callback's OWN emitted count, never
-- re-counted at the call's value boundary (HO-03). A clause family is an ordinary
-- callable (PAT-11), so its callback result is judged exactly like a user
-- algorithm's: `evalResolvedCallbackCallCounted` dispatches a family through
-- `evalConditionalCallbackCallCounted`, which evaluates the selected clause with
-- `recount = false`, while the ORDINARY call (`evalConditionalCallCounted`) keeps
-- the value boundary — so the same family is one value as a call and a rejected
-- two-row result as a callback. A `filter` predicate reads only its result's
-- value, which must be a Boolean. A loop step's rows are its next state
-- (LOOP-03), never this contract.
--
-- These guards pin the Lean side of defect D1 of the 2026-10-09 constitution
-- audit, which C# had re-counted (accepting a two-row family callback).
-- C#: `EvalNeedCallbackBody` → `EvalNeedFamilySupply (recount: false)`,
-- `ClauseFamilyCallbackCardinalityTests` (six routes), and the spec cases
-- `clause-family-multirow-callback-rejected`,
-- `clause-family-multirow-reduce-step-rejected` and
-- `clause-family-callback-single-value-accepted`.

-- F(0) = 1, 2
-- F(n) = n, n
def fcTwoRowsAlg : Algorithm :=
  .conditional none [] [
    ⟨ .litInt 0, alg [] [] [] [.num 1, .num 2] ⟩,
    ⟨ .bind "n", alg [] [] [] [.param "n", .param "n"] ⟩
  ]

-- One(0) = 1, 2          (a lone literal clause is a one-branch family)
def fcOneBranchAlg : Algorithm :=
  .conditional none [] [ ⟨ .litInt 0, alg [] [] [] [.num 1, .num 2] ⟩ ]

-- R(e, 0) = e, 0
-- R(e, acc) = e, acc
def fcReduceTwoRowsAlg : Algorithm :=
  .conditional none [] [
    ⟨ .sequenceValue [.bind "e", .litInt 0], alg [] [] [] [.param "e", .num 0] ⟩,
    ⟨ .sequenceValue [.bind "e", .bind "acc"], alg [] [] [] [.param "e", .param "acc"] ⟩
  ]

-- R1(e, 0) = e, 0        (a one-branch reduce step)
def fcReduceOneBranchAlg : Algorithm :=
  .conditional none [] [ ⟨ .sequenceValue [.bind "e", .litInt 0], alg [] [] [] [.param "e", .num 0] ⟩ ]

-- P(0) = (1, 2)
-- P(n) = (n, n)          (ONE emitted sequence value per call)
def fcPairAlg : Algorithm :=
  .conditional none [] [
    ⟨ .litInt 0, alg [] [] [] [.capture [.num 1, .num 2]] ⟩,
    ⟨ .bind "n", alg [] [] [] [.capture [.param "n", .param "n"]] ⟩
  ]

-- Add(e, 0) = e
-- Add(e, acc) = e + acc
def fcAddAlg : Algorithm :=
  .conditional none [] [
    ⟨ .sequenceValue [.bind "e", .litInt 0], alg [] [] [] [.param "e"] ⟩,
    ⟨ .sequenceValue [.bind "e", .bind "acc"], alg [] [] [] [.binary .add (.param "e") (.param "acc")] ⟩
  ]

-- L(0) = []
-- L(n) = [n]
def fcListAlg : Algorithm :=
  .conditional none [] [
    ⟨ .litInt 0, alg [] [] [] [.listLiteral []] ⟩,
    ⟨ .bind "n", alg [] [] [] [.listLiteral [.param "n"]] ⟩
  ]

-- E(0) = ()
-- E(n) = n
def fcEmptyAlg : Algorithm :=
  .conditional none [] [
    ⟨ .litInt 0, alg [] [] [] [.emptySequence 0] ⟩,
    ⟨ .bind "n", alg [] [] [] [.param "n"] ⟩
  ]

-- IsZero(0) = true
-- IsZero(n) = false
def fcIsZeroAlg : Algorithm :=
  .conditional none [] [
    ⟨ .litInt 0, alg [] [] [] [.boolLiteral true] ⟩,
    ⟨ .bind "n", alg [] [] [] [.boolLiteral false] ⟩
  ]

-- Both(0) = true, true
-- Both(n) = false, false
def fcTwoBoolsAlg : Algorithm :=
  .conditional none [] [
    ⟨ .litInt 0, alg [] [] [] [.boolLiteral true, .boolLiteral true] ⟩,
    ⟨ .bind "n", alg [] [] [] [.boolLiteral false, .boolLiteral false] ⟩
  ]

private def fcProgram (rows : List KatLang.Expr) : KatLang.Expr :=
  .algorithmExpr (algPrivate [] [] [
    ("F", fcTwoRowsAlg), ("One", fcOneBranchAlg), ("R", fcReduceTwoRowsAlg), ("R1", fcReduceOneBranchAlg),
    ("P", fcPairAlg), ("Add", fcAddAlg), ("L", fcListAlg), ("E", fcEmptyAlg), ("IsZero", fcIsZeroAlg),
    ("Both", fcTwoBoolsAlg),
    -- G = F (a callable alias of the family)
    ("G", .alias none [] [] (resolve "F")),
    -- Apply(f, xs) = map(xs, f)
    ("Apply", alg ["f", "xs"] [] [] [.call (resolve "map") [.param "xs", .param "f"]]),
    -- The user-algorithm controls, and each family clause written as a user algorithm:
    -- D(x) = x, x ; Ru(e, acc) = e, acc ; Q(x) = true, true
    ("D", alg ["x"] [] [] [.param "x", .param "x"]),
    ("Ru", alg ["e", "acc"] [] [] [.param "e", .param "acc"]),
    ("Q", alg ["x"] [] [] [.boolLiteral true, .boolLiteral true]),
    -- U0(x) = 1, 2 ; Up0(x) = (1, 2) ; Up(n) = (n, n) ; Ue(x) = ()
    ("U0", alg ["x"] [] [] [.num 1, .num 2]),
    ("Up0", alg ["x"] [] [] [.capture [.num 1, .num 2]]),
    ("Up", alg ["n"] [] [] [.capture [.param "n", .param "n"]]),
    ("Ue", alg ["x"] [] [] [.emptySequence 0])
  ] rows)

private def fcMap (xs : List KatLang.Expr) (f : KatLang.Expr) : KatLang.Expr :=
  .call (resolve "map") [.listLiteral xs, f]

private def fcReduce (xs : List KatLang.Expr) (f : KatLang.Expr) (initial : KatLang.Expr) : KatLang.Expr :=
  .call (resolve "reduce") [.listLiteral xs, f, initial]

private def fcFilter (xs : List KatLang.Expr) (f : KatLang.Expr) : KatLang.Expr :=
  .call (resolve "filter") [.listLiteral xs, f]

private def fcOk (rows : List KatLang.Expr) (expected : Result) : Bool :=
  match runResult (fcProgram rows) with
  | .ok value => value == expected
  | _ => false

private def fcFails (rows : List KatLang.Expr) (check : Error -> Bool) : Bool :=
  match runResult (fcProgram rows) with
  | .error e => check e
  | _ => false

private def mapRejected (e : Error) : Bool :=
  hasContext "map transform must return a single element" e && innermostIsBadArity e

private def reduceRejected (e : Error) : Bool :=
  hasContext "reduce step must return a single accumulator value" e && innermostIsBadArity e

private def fcPair (a b : Int) : Result := .sequenceValue [.atom a, .atom b]

-- The canonical witness (D1-A): a two-row family transform is rejected — through
-- its literal clause and through its binder clause alike.
#guard fcFails [fcMap [.num 0, .num 3] (resolve "F")] mapRejected
#guard fcFails [fcMap [.num 3] (resolve "F")] mapRejected

-- A one-branch family is a family too (D1-B).
#guard fcFails [fcMap [.num 0] (resolve "One")] mapRejected

-- A two-row family reduce step is rejected (D1-C), one-branch or two.
#guard fcFails [fcReduce [.num 1] (resolve "R") (.num 0)] reduceRejected
#guard fcFails [fcReduce [.num 1] (resolve "R1") (.num 0)] reduceRejected

-- The user-algorithm controls (D1-D, D1-E) and a family returning `()` (D1-F).
#guard fcFails [fcMap [.num 1, .num 3] (resolve "D")] mapRejected
#guard fcFails [fcReduce [.num 1] (resolve "Ru") (.num 0)] reduceRejected
#guard fcFails [fcMap [.num 0] (resolve "E")] mapRejected

-- An alias is its target's callable, and a forwarded callable is the callable.
#guard fcFails [fcMap [.num 0] (resolve "G")] mapRejected
#guard fcFails [.call (resolve "Apply") [resolve "F", .listLiteral [.num 0]]] mapRejected

-- ONE emitted value is accepted however many elements it holds: a sequence, a
-- list (`[]` included) and a reduce step's single sequence accumulator.
#guard fcOk [fcMap [.num 0, .num 3] (resolve "P")] (.listValue [fcPair 1 2, fcPair 3 3])
#guard fcOk [fcMap [.num 0, .num 3] (resolve "L")] (.listValue [.listValue [], .listValue [.atom 3]])
#guard fcOk [fcReduce [.num 1, .num 2, .num 3] (resolve "Add") (.num 0)] (.atom 6)

-- The η-expanded callback `{ F(x) }` is accepted: its one row is the ORDINARY
-- call, a value boundary (the HO-03 Known tension, unchanged).
#guard fcOk [fcMap [.num 0, .num 3] (.algorithmExpr (alg ["x"] [] [] [.call (resolve "F") [.param "x"]]))]
  (.listValue [fcPair 1 2, fcPair 3 3])

-- The ordinary call keeps its value boundary: one sequence value, emitted count 1.
#guard fcOk [.call (resolve "F") [.num 0], .listLiteral [.call (resolve "F") [.num 3]]]
  (.sequenceValue [fcPair 1 2, .listValue [fcPair 3 3]])
#guard match runCountedProgram (fcProgram [.call (resolve "F") [.num 0]]) with
  | .ok (value, count) => value == fcPair 1 2 && count == 1
  | _ => false

-- An empty collection never invokes the callback.
#guard fcOk [fcMap [] (resolve "F"), fcReduce [] (resolve "R") (.num 7)] (.sequenceValue [.listValue [], .atom 7])

-- `filter` reads its predicate's VALUE: a Boolean is required, so a two-row
-- predicate is the Boolean-required type error for a family and a user
-- algorithm alike, while a one-row family predicate filters.
#guard fcFails [fcFilter [.num 0, .num 3] (resolve "Both")] innermostIsAnyTypeMismatch
#guard fcFails [fcFilter [.num 0] (resolve "Q")] innermostIsAnyTypeMismatch
#guard fcOk [fcFilter [.num 0, .num 1, .num 0] (resolve "IsZero")] (.listValue [.atom 0, .atom 0])

-- A loop step is not a callback: the selected clause's two rows are the next
-- state (two slots), whose completed loop is one value.
#guard fcOk [.call (resolve "repeat") [resolve "F", .num 1, .num 0]] (fcPair 1 2)

/-- THE CALLBACK-RESULT LAW FOR FAMILIES: a family callback is judged exactly
    like its SELECTED CLAUSE written as a user callback — value for value, and
    failure for failure down to the innermost error (PAT-11: a family is an
    ordinary callable; HO-03 judges the callee's own emitted count). -/
def fcFamilyCallbackEqualsItsSelectedClause : Bool :=
  let cases : List (KatLang.Expr × KatLang.Expr) := [
    (fcMap [.num 0] (resolve "F"), fcMap [.num 0] (resolve "U0")),
    (fcMap [.num 3] (resolve "F"), fcMap [.num 3] (resolve "D")),
    (fcMap [.num 0] (resolve "One"), fcMap [.num 0] (resolve "U0")),
    (fcMap [.num 0] (resolve "P"), fcMap [.num 0] (resolve "Up0")),
    (fcMap [.num 3] (resolve "P"), fcMap [.num 3] (resolve "Up")),
    (fcMap [.num 0] (resolve "E"), fcMap [.num 0] (resolve "Ue")),
    (fcReduce [.num 1] (resolve "R") (.num 0), fcReduce [.num 1] (resolve "Ru") (.num 0)),
    (fcReduce [.num 1] (resolve "R") (.num 5), fcReduce [.num 1] (resolve "Ru") (.num 5)),
    (fcFilter [.num 0] (resolve "Both"), fcFilter [.num 0] (resolve "Q"))
  ]
  cases.all fun (family, user) =>
    match runResult (fcProgram [family]), runResult (fcProgram [user]) with
    | .ok a, .ok b => a == b
    | .error a, .error b => (repr (innermost a)).pretty == (repr (innermost b)).pretty
    | _, _ => false
where
  innermost : Error -> Error
    | .withContext _ inner => innermost inner
    | e => e

#guard fcFamilyCallbackEqualsItsSelectedClause

-- Independent D1 review: repeated-name incompatibility tries the later clause.
-- The nested sequence in the head consumes ONE ordinary pair element.
private def fcRepeatedFamily (twoRows : Bool) : Algorithm :=
  .conditional none [] [
    ⟨.sequenceValue [.sequenceValue [.bind "x", .bind "x"]],
      alg [] [] [] (if twoRows then [.num 10, .num 11] else [.num 10])⟩,
    ⟨.sequenceValue [.sequenceValue [.bind "x", .bind "y"]],
      alg [] [] [] (if twoRows then [.num 20, .num 21] else [.num 20])⟩]

private def fcRepeatedProgram (twoRows : Bool) (row : KatLang.Expr) : KatLang.Expr :=
  .algorithmExpr (algPrivate [] [] [("F", fcRepeatedFamily twoRows)] [row])

private def fcExpected (program : KatLang.Expr) (expected : Result) (count : Nat := 1) : Bool :=
  match runCountedProgram program with
  | .ok (value, emitted) => value == expected && emitted == count
  | _ => false

#guard fcExpected (fcRepeatedProgram false (fcMap [.capture [.num 1, .num 1], .capture [.num 1, .num 2]] (resolve "F")))
  (.listValue [.atom 10, .atom 20])
#guard match runResult (fcRepeatedProgram true (fcMap [.capture [.num 1, .num 2]] (resolve "F"))) with
  | .error e => mapRejected e
  | _ => false
#guard fcExpected (fcRepeatedProgram true (.call (resolve "F") [.capture [.num 1, .num 2]]))
  (.sequenceValue [.atom 20, .atom 21])

-- Host-built single-flat-binder families are outside the source-reachable core
-- (FORMAL-08). Lean's compatibility fallback uses the user binder. These pins
-- explicitly preserve its repeated-name error instead of normalizing it away;
-- C#'s host-built family dispatcher reports NoMatchingBranch for that case.
private def fcHostFlat (repeated oneRow : Bool) : Algorithm :=
  .conditional none [] [
    ⟨.sequenceValue [.bind "x", .bind (if repeated then "x" else "y")],
      alg [] [] [] (if repeated then [.param "x"]
        else if oneRow then [.capture [.param "x", .param "y"]]
        else [.param "x", .param "y"])⟩]
private def fcHostProgram (repeated oneRow : Bool) (row : KatLang.Expr) : KatLang.Expr :=
  .algorithmExpr (algPrivate [] [] [("F", fcHostFlat repeated oneRow)] [row])

#guard match runResult (fcHostProgram false false (fcReduce [.num 1] (resolve "F") (.num 0))) with
  | .error e => reduceRejected e
  | _ => false
#guard fcExpected (fcHostProgram false true (fcReduce [.num 1] (resolve "F") (.num 0)))
  (.sequenceValue [.atom 1, .atom 0])
#guard fcExpected (fcHostProgram false false (.call (resolve "F") [.num 1, .num 0]))
  (.sequenceValue [.atom 1, .atom 0])
#guard fcExpected (fcHostProgram false false (.call (resolve "repeat") [resolve "F", .num 1, .num 1, .num 0]))
  (.sequenceValue [.atom 1, .atom 0])
#guard fcExpected (fcHostProgram true true (fcReduce [.num 1] (resolve "F") (.num 1))) (.atom 1)
#guard match runResult (fcHostProgram true true (fcReduce [.num 1] (resolve "F") (.num 0))) with
  | .error e => innermostIsBadArity e
  | _ => false

end KatLangTests
