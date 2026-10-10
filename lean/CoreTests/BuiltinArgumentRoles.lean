import KatLang
import CoreTests.Common

namespace KatLangTests
open KatLang (alg algPrivate runResultM Algorithm Error Result EvalState Builtin SequenceBuiltinSlotRole)
open KatLang (resolve param num)

--------------------------------------------------------------------------------
-- Builtin call assembly respects argument roles (PV-05 / PV-19 / PV-20, September 2026)
--------------------------------------------------------------------------------
-- THE RULE: collection-builtin argument assembly (`collectSequenceCallableCallItems`)
-- handles every written slot by the ROLE its position has in the builtin's metadata
-- (`SequenceBuiltinMetadata.slotRole`):
--   * a VALUE slot is demanded ONCE; its value or its failure is final for the call and
--     is never retried — `reduce`'s `initial` is a value slot (PV-05);
--   * a CALLBACK slot carries its algorithm and is INVOKED by the builtin; supplying it
--     evaluates nothing — an unused callback has no effect, cannot fail and cannot
--     recurse (PV-19);
--   * a SPREAD slot is supply assembly: it supplies exactly its items, or its failure is
--     the call's failure, raised before the arity check and before any later slot — never
--     one phantom supplied item (PV-20).
-- Before the rule the assembly was role-blind: every argument without declared
-- parameters was evaluated eagerly (callback slots included), a failed evaluation was
-- kept as ONE item whether or not it was a spread, `reduce`'s `initial` was an
-- algorithm-kind slot that `evalReduceCounted` evaluated a second time, and every
-- failure in a callback slot was dropped.
--
-- Evidence without host operations, as in `ArgumentValueOutcome.lean`: `Bad = Id(1) / 0`
-- and `A = Id(5)` open exactly ONE binding context per evaluation of their bodies (the
-- `Id` call; `EvalState.nextBindingContext`), and every user call opens one more, so the
-- contexts a run opens — kept for a FAILED run too — count evaluations. The property
-- cache (`EvalState.zeroArgPropertyCache`) records every successful property read.

/-- `Id(y) = y`: one binding context per call. -/
def brIdAlg : Algorithm := alg ["y"] [] [] [param "y"]

/-- `Bad = Id(1) / 0`: its body opens exactly one context, then fails. -/
def brBadAlg : Algorithm :=
  alg [] [] [] [.binary .div (.call (resolve "Id") [num 1]) (num 0)]

/-- `A = Id(5)`: its body opens exactly one context and succeeds. -/
def brGoodAlg : Algorithm := alg [] [] [] [.call (resolve "Id") [num 5]]

/-- `BadType = 1 + "a"`: a failure of another kind. -/
def brBadTypeAlg : Algorithm := alg [] [] [] [.binary .add (num 1) (.stringLiteral "a")]

/-- `BadIndex = [1]:5`: a failure of a third kind. -/
def brBadIndexAlg : Algorithm := alg [] [] [] [.index (.listLiteral [num 1]) (num 5)]

/-- `L = L + 1`: reading it never terminates (until a resource limit in C#). -/
def brLoopAlg : Algorithm := alg [] [] [] [.binary .add (resolve "L") (num 1)]

/-- `E = ()`. -/
def brEmptyAlg : Algorithm := alg [] [] [] [.capture []]

/-- `D = filter(E, D)`: names ITSELF as the unused predicate of an empty filter. -/
def brSelfFilterAlg : Algorithm :=
  alg [] [] [] [.call (resolve "filter") [resolve "E", resolve "D"]]

/-- `Keep(e, a) = a`: a reducer that returns the accumulator. -/
def brKeepAlg : Algorithm := alg ["e", "a"] [] [] [param "a"]

/-- `Add(e, a) = e + a`. -/
def brAddAlg : Algorithm := alg ["e", "a"] [] [] [.binary .add (param "e") (param "a")]

/-- `Inc(z) = z + 1`. -/
def brIncAlg : Algorithm := alg ["z"] [] [] [.binary .add (param "z") (num 1)]

/-- `G(v) = reduce([], Keep, v)`: forwards its parameter to `reduce`'s `initial`. -/
def brForwardInitialAlg : Algorithm :=
  alg ["v"] [] [] [.call (resolve "reduce") [.listLiteral [], resolve "Keep", param "v"]]

/-- `T(a, b) = take(a, b)`: the user-call spelling of `take`. -/
def brTakeWrapperAlg : Algorithm :=
  alg ["a", "b"] [] [] [.call (resolve "take") [param "a", param "b"]]

/-- `Pair = [1, 2, 3], 2`: a successful spread operand. -/
def brPairAlg : Algorithm :=
  alg [] [] [] [.listLiteral [num 1, num 2, num 3], num 2]

def brRoot (out : List KatLang.Expr) : KatLang.Expr :=
  .algorithmExpr (algPrivate [] []
    [ ("Id", brIdAlg), ("Bad", brBadAlg), ("A", brGoodAlg), ("BadType", brBadTypeAlg)
    , ("BadIndex", brBadIndexAlg), ("L", brLoopAlg), ("E", brEmptyAlg), ("D", brSelfFilterAlg)
    , ("Keep", brKeepAlg), ("Add", brAddAlg), ("Inc", brIncAlg), ("G", brForwardInitialAlg)
    , ("T", brTakeWrapperAlg), ("Pair", brPairAlg) ]
    out)

/-- The outcome of a run, the binding contexts it opened, and whether it stored any
    property in the cache — kept for a FAILED run too (`runState`, as `evalAttempt`). -/
def brRun (out : List KatLang.Expr) : Except Error Result × Nat × Bool :=
  let (result, state) := (runResultM (brRoot out)).runState EvalState.empty
  (result, state.nextBindingContext - 1, state.zeroArgPropertyCache.isEmpty)

def brContexts (out : List KatLang.Expr) : Nat := (brRun out).2.1

def brFails (isExpected : Error -> Bool) (out : List KatLang.Expr) : Bool :=
  match (brRun out).1 with
  | .error err => isExpected err
  | .ok _ => false

def brSucceedsWith (out : List KatLang.Expr) (expected : Result) : Bool :=
  match (brRun out).1 with
  | .ok value => value == expected
  | .error _ => false

def brCall (callee : String) (args : List KatLang.Expr) : KatLang.Expr :=
  .call (resolve callee) args

def brNone : List KatLang.Expr := []

--------------------------------------------------------------------------------
-- 1. The roles are metadata: `reduce`'s `initial` is a VALUE slot, the reducer, the
--    mapper and the predicate are CALLBACK slots, the collection is always a value.
--------------------------------------------------------------------------------

def brRoleOf (b : Builtin) (slot : Nat) : Option SequenceBuiltinSlotRole :=
  (KatLang.sequenceBuiltinMetadata? b).map (·.slotRole slot)

#guard brRoleOf .reduceBuiltin 0 == some .value
#guard brRoleOf .reduceBuiltin 1 == some .callback
#guard brRoleOf .reduceBuiltin 2 == some .value
#guard brRoleOf .reduceBuiltin 3 == some .surplus
#guard brRoleOf .mapBuiltin 1 == some .callback
#guard brRoleOf .filterBuiltin 1 == some .callback
#guard brRoleOf .containsBuiltin 1 == some .value
#guard brRoleOf .takeBuiltin 1 == some .value
#guard brRoleOf .countBuiltin 1 == some .surplus

-- The reference counts: each body opens exactly one context; a read of `A` is cached.
#guard brFails innermostIsDivByZero [resolve "Bad"]
#guard brContexts [resolve "Bad"] == 1
#guard brSucceedsWith [resolve "A"] (.atom 5)
#guard brContexts [resolve "A"] == 1

--------------------------------------------------------------------------------
-- 2. PV-05 — `reduce`'s `initial` is demanded ONCE; a failure is final, never retried.
--------------------------------------------------------------------------------

/-- `reduce([], Keep, initial)`. -/
def brReduceEmpty (initial : KatLang.Expr) : KatLang.Expr :=
  brCall "reduce" [.listLiteral [], resolve "Keep", initial]

-- A failed initial is the call's failure after ONE evaluation (formerly two: the
-- assembly's attempt, then `evalReduceCounted` evaluated the algorithm again).
#guard brFails innermostIsDivByZero [brReduceEmpty (resolve "Bad")]
#guard brContexts [brReduceEmpty (resolve "Bad")] == 1
#guard brFails innermostIsDivByZero [brReduceEmpty (.binary .div (brCall "Id" [num 1]) (num 0))]
#guard brContexts [brReduceEmpty (.binary .div (brCall "Id" [num 1]) (num 0))] == 1

-- A successful initial is evaluated once too, and its one value is the accumulator.
#guard brSucceedsWith [brReduceEmpty (brCall "Id" [num 5])] (.atom 5)
#guard brContexts [brReduceEmpty (brCall "Id" [num 5])] == 1
-- `reduce([1, 2], Add, Id(5))` is 8: one context for the initial, one per reducer call.
#guard brSucceedsWith [brCall "reduce" [.listLiteral [num 1, num 2], resolve "Add", brCall "Id" [num 5]]] (.atom 8)
#guard brContexts [brCall "reduce" [.listLiteral [num 1, num 2], resolve "Add", brCall "Id" [num 5]]] == 3
-- A non-empty reduce fails with the initial's own failure before any reducer call.
#guard brFails innermostIsDivByZero [brCall "reduce" [.listLiteral [num 1, num 2], resolve "Add", resolve "Bad"]]
#guard brContexts [brCall "reduce" [.listLiteral [num 1, num 2], resolve "Add", resolve "Bad"]] == 1

/-- `reduce([], Keep, reduce([], Keep, … Id(1) / 0))`, `depth` levels deep. -/
def brNestedInitial : Nat -> KatLang.Expr
  | 0 => .binary .div (brCall "Id" [num 1]) (num 0)
  | .succ depth => brReduceEmpty (brNestedInitial depth)

-- Nested failing initials evaluate the innermost failure ONCE (formerly 2^depth times).
#guard brFails innermostIsDivByZero [brNestedInitial 5]
#guard brContexts [brNestedInitial 5] == 1
#guard brContexts [brNestedInitial 8] == 1

-- A forwarded initial agrees with the direct one: the user call `G(Bad)` evaluates its
-- written argument once (+1 context for `G`), and `initial` reads the recorded outcome.
#guard brFails innermostIsDivByZero [brCall "G" [resolve "Bad"]]
#guard brContexts [brCall "G" [resolve "Bad"]] == brContexts [brReduceEmpty (resolve "Bad")] + 1

--------------------------------------------------------------------------------
-- 3. PV-19 — a CALLBACK slot is never value-evaluated merely because it was supplied.
--------------------------------------------------------------------------------

/-- The run of these rows succeeds with `expected` without opening a binding context
    and without storing any property read: nothing was evaluated for its value. -/
def brSucceedsReadingNothing (out : List KatLang.Expr) (expected : Result) : Bool :=
  brSucceedsWith out expected && brContexts out == 0 && (brRun out).2.2

-- An unused callback runs no body and reads no property (formerly `A` was evaluated
-- and cached by the eager attempt), exactly like a zero-iteration loop step.
#guard brSucceedsReadingNothing [brCall "map" [.listLiteral [], resolve "A"]] (.listValue [])
#guard brSucceedsReadingNothing [brCall "filter" [.listLiteral [], resolve "A"]] (.listValue [])
#guard brSucceedsReadingNothing [brCall "reduce" [.listLiteral [], resolve "A", num 0]] (.atom 0)
#guard brSucceedsReadingNothing [.dotCall (.listLiteral []) "map" (some [resolve "A"])] (.listValue [])
#guard brSucceedsReadingNothing [brCall "map" [.listLiteral [], .algorithmExpr brGoodAlg]] (.listValue [])
#guard brSucceedsReadingNothing [brCall "repeat" [resolve "A", num 0, num 5]] (.atom 5)

-- An unused callback cannot fail and cannot recurse: `map([], L)` with `L = L + 1` and
-- `D = filter(E, D)` terminate (formerly the eager attempt read `L` / `D` forever).
#guard brSucceedsReadingNothing [brCall "map" [.listLiteral [], resolve "L"]] (.listValue [])
#guard brSucceedsWith [.dotCall (resolve "D") "count" none] (.atom 0)
#guard brSucceedsReadingNothing [brCall "map" [.listLiteral [], resolve "Bad"]] (.listValue [])

-- An invoked callback is an ordinary call per element: two elements, two calls.
#guard brSucceedsWith [brCall "map" [.listLiteral [num 1, num 2], resolve "Inc"]]
  (.listValue [.atom 2, .atom 3])
#guard brContexts [brCall "map" [.listLiteral [num 1, num 2], resolve "Inc"]] == 2
-- A zero-parameter callable invoked with an element is rejected by the binder before
-- its body runs: the ordinary arity error, and no evaluation of `A` at all.
#guard brFails (innermostIsArityMismatch 0 1) [brCall "map" [.listLiteral [num 1], resolve "A"]]
#guard brContexts [brCall "map" [.listLiteral [num 1], resolve "A"]] == 0

--------------------------------------------------------------------------------
-- 4. PV-20 — a failed SPREAD is the call's failure; it never supplies a phantom item.
--------------------------------------------------------------------------------

-- The spread operand's own failure, whatever its kind, before the arity check
-- (formerly `take(Bad*)` was an arity error "called with 1 argument").
#guard brFails innermostIsDivByZero [brCall "take" [.sequenceSpread (resolve "Bad")]]
#guard brFails innermostIsAnyTypeMismatch [brCall "take" [.sequenceSpread (resolve "BadType")]]
#guard brFails innermostIsBadIndex [brCall "take" [.sequenceSpread (resolve "BadIndex")]]
#guard brFails innermostIsSpreadMissingOutput
  [brCall "count" [num 1, .sequenceSpread (.algorithmExpr (alg [] [] [] []))]]
-- The failure does not disappear because a callback would never run (formerly `[]`/`0`).
#guard brFails innermostIsDivByZero [brCall "map" [.listLiteral [], .sequenceSpread (resolve "Bad")]]
#guard brFails innermostIsDivByZero [brCall "reduce" [.listLiteral [], .sequenceSpread (resolve "Bad"), num 0]]
#guard brFails innermostIsBadIndex [brCall "map" [.listLiteral [], .sequenceSpread (resolve "BadIndex")]]
-- Raised during supply formation: no other slot is evaluated (neither `Id(7)` nor `Id(8)` runs;
-- NEED-01).
#guard brFails innermostIsDivByZero
  [brCall "take" [brCall "Id" [num 7], .sequenceSpread (resolve "Bad"), brCall "Id" [num 8]]]
#guard brContexts
  [brCall "take" [brCall "Id" [num 7], .sequenceSpread (resolve "Bad"), brCall "Id" [num 8]]] == 1
-- An earlier value slot is not evaluated during supply formation (NEED-01; until Model C
-- its ordinary failure was retained, not raised), so the first failure RAISED is the
-- later spread's own.
#guard brFails innermostIsAnyTypeMismatch
  [brCall "take" [resolve "Bad", .sequenceSpread (resolve "BadType")]]
-- The user-call spelling agrees: the spread fails the same way before `T` is entered.
#guard brFails innermostIsDivByZero [brCall "T" [.sequenceSpread (resolve "Bad")]]
#guard brContexts [brCall "T" [.sequenceSpread (resolve "Bad")]]
  == brContexts [brCall "take" [.sequenceSpread (resolve "Bad")]]
-- A successful spread still supplies exactly its items, in their positions' roles.
#guard brSucceedsWith [brCall "take" [.sequenceSpread (resolve "Pair")]]
  (.listValue [.atom 1, .atom 2])
#guard brFails (innermostIsArityMismatch 2 0) [brCall "take" [.sequenceSpread (.capture [])]]

-- Roles follow SUPPLIED positions, not written-slot indices: an empty spread
-- shifts nothing, a multi-item spread fills several positions, and only a later
-- value slot is demanded. Binding-context counts witness absence of callback work.
def brMapAfterEmptySpread : KatLang.Expr :=
  brCall "map" [.sequenceSpread (resolve "E"), .listLiteral [], resolve "A"]
#guard brSucceedsWith [brMapAfterEmptySpread] (.listValue [])
#guard brContexts [brMapAfterEmptySpread] == 0

def brReduceAfterPairSpread : KatLang.Expr :=
  brCall "reduce" [.sequenceSpread (.capture [.listLiteral [], num 17]), brCall "Id" [num 9]]
#guard brSucceedsWith [brReduceAfterPairSpread] (.atom 9)
#guard brContexts [brReduceAfterPairSpread] == 1

def brFailedInitialAfterEmptySpread : KatLang.Expr :=
  brCall "reduce" [.listLiteral [], resolve "Keep", .sequenceSpread (resolve "E"), resolve "Bad"]
#guard brFails innermostIsDivByZero [brFailedInitialAfterEmptySpread]
#guard brContexts [brFailedInitialAfterEmptySpread] == 1

def brLaterFailedSpread : KatLang.Expr :=
  brCall "take" [.sequenceSpread (.listLiteral [num 1]),
    .sequenceSpread (resolve "BadType"), brCall "Id" [num 3]]
#guard brFails innermostIsAnyTypeMismatch [brLaterFailedSpread]
#guard brContexts [brLaterFailedSpread] == 0

end KatLangTests
