import KatLang
import CoreTests.Common

namespace KatLangTests
open KatLang (alg algWithParameters algPrivate publicProp runResultM Algorithm Error Result EvalState)
open KatLang (resolve param num)

--------------------------------------------------------------------------------
-- At-most-once argument value evaluation (Q-01 / PV-04, September 2026)
--------------------------------------------------------------------------------
-- THE RULE: within one call, a written argument slot is evaluated at most once
-- for its value. If that evaluation succeeds, that is its value; if it fails,
-- that is its failure. Reading the bound parameter never causes the argument
-- expression to execute again: argument evaluation uses the proper semantic
-- route once, and every parameter read reuses its outcome. The algorithm
-- channel stays available for invocation, structural navigation and
-- forwarding, but it is never a second route to the parameter's value. Since
-- Model C (October 2026) the one route is the parameter's need cell
-- (`supplyNeed`, `demandNeed`, `EvalState.needs`; the `.param` arm of
-- `evalCounted` demands it first). `AlgBinding.valueFailure?` and
-- `parameterValueFailure?` remain as legacy Ready-tier readers with no
-- production writer; the former `resolveArgAlgExpr` is gone (builtin argument
-- resolution now supplies need cells, `resolveArgAlgsWithSequenceSpread`), and
-- the eager writer `slotAlgorithmBinding` survives only in the historical
-- fixture `HistoricalReadyBinding.lean`.
--
-- Evidence without host operations: `Bad = Id(1) / 0` and `A = Id(5)` open
-- exactly ONE binding context per evaluation of their bodies (the `Id` call;
-- `EvalState.nextBindingContext`, allocated by `EvalCtx.bindParameters`), and
-- every user call opens one more. The contexts a run opens — kept for a FAILED
-- run too (`runWithContexts`) — therefore count how often each written
-- argument's body ran. Before the rule, every value read of a parameter whose
-- slot had failed re-evaluated the argument's algorithm: one context more per
-- read and per forwarding level, and a failure could become a value.

/-- `Id(y) = y`: one binding context per call. -/
def aoIdAlg : Algorithm := alg ["y"] [] [] [param "y"]

/-- `Bad = Id(1) / 0`: its body opens exactly one context, then fails. -/
def aoBadAlg : Algorithm :=
  alg [] [] [] [.binary .div (.call (resolve "Id") [num 1]) (num 0)]

/-- `A = Id(5)`: its body opens exactly one context and succeeds. -/
def aoGoodAlg : Algorithm := alg [] [] [] [.call (resolve "Id") [num 5]]

/-- `One(x) = x`. -/
def aoOneAlg : Algorithm := alg ["x"] [] [] [param "x"]

/-- `Two(x) = x, x`. -/
def aoTwoAlg : Algorithm := alg ["x"] [] [] [param "x", param "x"]

/-- `Three(x) = x, x, x`. -/
def aoThreeAlg : Algorithm := alg ["x"] [] [] [param "x", param "x", param "x"]

/-- `Fwd(w) = One(w), Two(w)`: forwards the parameter to two further calls. -/
def aoFwdAlg : Algorithm :=
  alg ["w"] [] [] [.call (resolve "One") [param "w"], .call (resolve "Two") [param "w"]]

/-- `Sum(v) = sum(v)`: a builtin VALUE slot reading the parameter. -/
def aoSumAlg : Algorithm := alg ["v"] [] [] [.call (resolve "sum") [param "v"]]

/-- `If(v) = if(true, v, 0)`: the lazy `if` VALUE slot reading the parameter. -/
def aoIfAlg : Algorithm :=
  alg ["v"] [] [] [.call (resolve "if") [.boolLiteral true, param "v", num 0]]

/-- `Show(v) = v.string`: the intrinsic reading the parameter. -/
def aoShowAlg : Algorithm := alg ["v"] [] [] [.dotCall (param "v") "string" none]

/-- `First(x, y) = x`: never reads `y`. -/
def aoFirstAlg : Algorithm := alg ["x", "y"] [] [] [param "x"]

/-- `Inc(z) = z + 1`. -/
def aoIncAlg : Algorithm := alg ["z"] [] [] [.binary .add (param "z") (num 1)]

/-- `Apply(f, x) = f(x)`: INVOKES the algorithm channel. -/
def aoApplyAlg : Algorithm := alg ["f", "x"] [] [] [.call (param "f") [param "x"]]

/-- `Plus(f, x) = f + x`: reads the parameter `f` for its VALUE. -/
def aoPlusAlg : Algorithm := alg ["f", "x"] [] [] [.binary .add (param "f") (param "x")]

/-- `MapWith(f, xs) = map(xs, f)`: forwards `f` to an invoking builtin slot. -/
def aoMapWithAlg : Algorithm :=
  alg ["f", "xs"] [] [] [.call (resolve "map") [param "xs", param "f"]]

/-- `Box = { public X = 5 }`: members and no output, so its VALUE evaluation fails. -/
def aoBoxAlg : Algorithm := alg [] [] [publicProp "X" (alg [] [] [] [num 5])] []

/-- `Member(o) = o.X`: structural member access through the algorithm channel. -/
def aoMemberAlg : Algorithm := alg ["o"] [] [] [.dotCall (param "o") "X" none]

/-- `Call0(f) = f()`: an EXPLICIT invocation, which evaluates afresh. -/
def aoCall0Alg : Algorithm := alg ["f"] [] [] [.call (param "f") []]

/-- `Coll(*xs) = xs`. -/
def aoCollAlg : Algorithm :=
  algWithParameters [{ name := "xs", kind := .collecting }] [] [] [param "xs"]

def aoRoot (out : List KatLang.Expr) : KatLang.Expr :=
  .algorithmExpr (algPrivate [] []
    [ ("Id", aoIdAlg), ("Bad", aoBadAlg), ("A", aoGoodAlg), ("One", aoOneAlg)
    , ("Two", aoTwoAlg), ("Three", aoThreeAlg), ("Fwd", aoFwdAlg), ("Sum", aoSumAlg)
    , ("If", aoIfAlg), ("Show", aoShowAlg), ("First", aoFirstAlg), ("Inc", aoIncAlg)
    , ("Apply", aoApplyAlg), ("Plus", aoPlusAlg), ("MapWith", aoMapWithAlg)
    , ("Box", aoBoxAlg), ("Member", aoMemberAlg), ("Call0", aoCall0Alg), ("Coll", aoCollAlg) ]
    out)

/-- The outcome of a run AND the binding contexts it opened, kept for a FAILED
    run too: `runResultM` from the empty state, read without discarding the
    state (as `evalAttempt` does). -/
def runWithContexts (e : KatLang.Expr) : Except Error Result × Nat :=
  let (result, state) := (runResultM e).runState EvalState.empty
  (result, state.nextBindingContext - 1)

/-- The binding contexts a run of these rows opened, whether it succeeded or failed. -/
def aoContexts (out : List KatLang.Expr) : Nat :=
  (runWithContexts (aoRoot out)).snd

/-- The run of these rows fails with `divByZero`. -/
def aoFailsWithDivByZero (out : List KatLang.Expr) : Bool :=
  match (runWithContexts (aoRoot out)).fst with
  | .error err => innermostIsDivByZero err
  | .ok _ => false

/-- The run of these rows succeeds with `expected`. -/
def aoSucceedsWith (out : List KatLang.Expr) (expected : Result) : Bool :=
  match (runWithContexts (aoRoot out)).fst with
  | .ok value => value == expected
  | .error _ => false

def callOf (callee : String) (args : List KatLang.Expr) : KatLang.Expr :=
  .call (resolve callee) args

-- The reference counts: the body of `Bad` (and of `A`) opens exactly one context.
#guard aoFailsWithDivByZero [resolve "Bad"]
#guard aoContexts [resolve "Bad"] == 1
#guard aoSucceedsWith [resolve "A"] (.atom 5)
#guard aoContexts [resolve "A"] == 1

-- 1. A FAILED argument is evaluated once and its failure is reused: `One(Bad)`
--    fails with the slot's own `divByZero` after exactly one evaluation of Bad's
--    body (+1 context for the call to `One`), never a second one for the read.
#guard aoFailsWithDivByZero [callOf "One" [resolve "Bad"]]
#guard aoContexts [callOf "One" [resolve "Bad"]] == aoContexts [resolve "Bad"] + 1

-- 2. LAW A — duplicating the parameter read is observationally inert: `Two` and
--    `Three` read `x` more often, and no extra evaluation of the argument occurs.
#guard aoFailsWithDivByZero [callOf "Two" [resolve "Bad"]]
#guard aoFailsWithDivByZero [callOf "Three" [resolve "Bad"]]
#guard aoContexts [callOf "Two" [resolve "Bad"]] == aoContexts [callOf "One" [resolve "Bad"]]
#guard aoContexts [callOf "Three" [resolve "Bad"]] == aoContexts [callOf "One" [resolve "Bad"]]
#guard aoSucceedsWith [callOf "Two" [resolve "A"]] (.sequenceValue [.atom 5, .atom 5])
#guard aoSucceedsWith [callOf "Three" [resolve "A"]] (.sequenceValue [.atom 5, .atom 5, .atom 5])
#guard aoContexts [callOf "Two" [resolve "A"]] == aoContexts [callOf "One" [resolve "A"]]
#guard aoContexts [callOf "Three" [resolve "A"]] == aoContexts [callOf "One" [resolve "A"]]
#guard aoContexts [callOf "One" [resolve "A"]] == aoContexts [resolve "A"] + 1

-- 3. LAW B — a failure cannot become a value through a parameter read. The read
--    below finds an algorithm-channel binding whose algorithm WOULD evaluate to 5,
--    but whose slot recorded `divByZero`: the read reports the recorded failure,
--    evaluates nothing (no binding context is opened), and never yields 5.
def readOfFailedBinding : Except Error Result × Nat :=
  let ctx : KatLang.EvalCtx :=
    { callStack := [KatLang.preludeAlg],
      algEnv := [("x", { algorithm := alg [] [] [] [num 5], valueFailure? := some Error.divByZero })] }
  let (result, state) := (KatLang.eval (param "x") ctx []).runState EvalState.empty
  (result, state.nextBindingContext)

#guard match readOfFailedBinding with
  | (.error .divByZero, 1) => true
  | _ => false

-- The same binding WITHOUT a recorded failure but WITH a value reads the value; the
-- algorithm channel is never consulted for a value that exists.
def readOfValuedBinding : Except Error Result :=
  let ctx : KatLang.EvalCtx :=
    { callStack := [KatLang.preludeAlg],
      algEnv := [("x", { algorithm := alg [] [] [] [num 5] })] }
  KatLang.runEvalM (KatLang.eval (param "x") ctx [("x", .atom 7)])

#guard match readOfValuedBinding with
  | .ok (.atom 7) => true
  | _ => false

-- 4. LAW D — forwarding transports the one supplied cell (NEED-08); it never
--    re-evaluates the source. `Fwd(Bad)` forwards `w` into `One(w)` (its first row fails there): Bad's
--    body runs ONCE, and the only other contexts are the calls to Fwd and One.
#guard aoFailsWithDivByZero [callOf "Fwd" [resolve "Bad"]]
#guard aoContexts [callOf "Fwd" [resolve "Bad"]] == aoContexts [resolve "Bad"] + 2

-- 5. Builtin VALUE slots and the `.string` receiver read a failed parameter through
--    the ordinary parameter read (the parameter's need cell, `demandNeed`; formerly
--    `resolveArgAlgExpr` and `parameterValueFailure?`): the slot's failure, with no
--    second evaluation of the argument.
#guard aoFailsWithDivByZero [callOf "Sum" [resolve "Bad"]]
#guard aoContexts [callOf "Sum" [resolve "Bad"]] == aoContexts [resolve "Bad"] + 1
#guard aoFailsWithDivByZero [callOf "If" [resolve "Bad"]]
#guard aoContexts [callOf "If" [resolve "Bad"]] == aoContexts [resolve "Bad"] + 1
#guard aoFailsWithDivByZero [callOf "Show" [resolve "Bad"]]
#guard aoContexts [callOf "Show" [resolve "Bad"]] == aoContexts [resolve "Bad"] + 1

-- 6. Laziness is preserved: a failed argument nobody demands is not an error, and it
--    is never evaluated (one context: the call to First; Model C, NEED-01).
#guard aoSucceedsWith [callOf "First" [num 1, resolve "Bad"]] (.atom 1)
#guard aoContexts [callOf "First" [num 1, resolve "Bad"]] == 1

-- 7. The algorithm channel remains available where the language uses it: invocation,
--    an invoking builtin slot, and structural member access through a parameter whose
--    VALUE evaluation failed.
#guard aoSucceedsWith [callOf "Apply" [resolve "Inc", num 5]] (.atom 6)
#guard aoSucceedsWith [callOf "MapWith" [resolve "Inc", .listLiteral [num 1, num 2]]]
  (.listValue [.atom 2, .atom 3])
#guard aoSucceedsWith [callOf "Member" [resolve "Box"]] (.atom 5)
-- Reading such a parameter for its VALUE reports the failure its slot established:
-- demanding the parameterized property `Inc` with zero arguments, at the call.
#guard match (runWithContexts (aoRoot [callOf "Plus" [resolve "Inc", num 5]])).fst with
  | .error err => innermostIsArityMismatch 1 0 err && hasContext "while evaluating property Inc" err
  | .ok _ => false

-- 8. An EXPLICIT invocation of the forwarded callable is still a fresh call (the
--    `A` versus `A()` rule): `Call0(A)` reads A for the argument slot once and then
--    runs A's body afresh — one explicit-call context and one `Id` context more than
--    `One(A)`.
#guard aoSucceedsWith [callOf "Call0" [resolve "A"]] (.atom 5)
#guard aoContexts [callOf "Call0" [resolve "A"]] == aoContexts [callOf "One" [resolve "A"]] + 1

-- 9. Unrelated binding semantics are unchanged: a value-only argument binds its value;
--    a collecting parameter binds its slice without demanding it, and reading the
--    collected list demands every cell, so `Coll(Bad)` fails with Bad's own failure when
--    the body reads `xs` — after the call's own binding context opened (VAR-03, NEED-07).
#guard aoSucceedsWith [callOf "Two" [num 3]] (.sequenceValue [.atom 3, .atom 3])
#guard aoFailsWithDivByZero [callOf "Coll" [resolve "Bad"]]
#guard aoContexts [callOf "Coll" [resolve "Bad"]] == aoContexts [resolve "Bad"] + 1

-- A callable's signature must never replace a PARAMETER's recorded failure at a
-- builtin value boundary. The raw algorithm requires an argument and could run
-- successfully when invoked; the established value outcome is still divByZero.
def aoFailedCallableBoundary (consumer : KatLang.Expr) (contexts : Nat := 1) : Bool :=
  let ctx : KatLang.EvalCtx :=
    { callStack := [KatLang.preludeAlg],
      algEnv := [("x", { algorithm := aoIncAlg, valueFailure? := some Error.divByZero })] }
  let (result, state) := (KatLang.eval consumer ctx []).runState EvalState.empty
  match result with
  | .error err => innermostIsDivByZero err && state.nextBindingContext == contexts
  | .ok _ => false

#guard aoFailedCallableBoundary (param "x")
#guard aoFailedCallableBoundary (callOf "sum" [param "x"])
#guard aoFailedCallableBoundary (callOf "count" [param "x"])
#guard aoFailedCallableBoundary (callOf "first" [param "x"])
#guard aoFailedCallableBoundary (callOf "last" [param "x"])
#guard aoFailedCallableBoundary (callOf "take" [.listLiteral [num 1], param "x"])
#guard aoFailedCallableBoundary (callOf "if" [.boolLiteral true, param "x", num 0])
#guard aoFailedCallableBoundary (callOf "range" [param "x", num 3])
#guard aoFailedCallableBoundary (callOf "repeat" [.algorithmExpr aoIncAlg, num 1, param "x"]) 2
#guard aoFailedCallableBoundary (callOf "repeat" [.algorithmExpr aoIncAlg, param "x", num 0])
#guard aoFailedCallableBoundary (callOf "reduce"
  [.listLiteral [num 1], .algorithmExpr (alg ["e", "a"] [] [] [param "a"]), param "x"])
#guard aoFailedCallableBoundary (.dotCall (param "x") "string" none)

end KatLangTests
