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
-- `evalCounted` demands it first), and a builtin call forms its supply of need
-- cells the same way (`formNeedSupply`). The pre-Model-C eager writer
-- `slotAlgorithmBinding`, which recorded a failed slot beside its
-- algorithm-channel binding, was deleted with Model C (its last Lean copy, the
-- pre-Model-C Ready binder, was retired on 2026-10-12), and the algorithm-tier
-- failure readers it fed were removed on 2026-10-13 (P3 maintenance cleanup).
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

-- 3. LAW B — a failure cannot become a value through a parameter read: the need
--    cell's completed failure is the outcome every later demand reuses, with no
--    further work (`CoreTests/ModelC.lean`: `stickyFailure`,
--    `failedCompletionDoesNoFurtherWork`).
--    The read's remaining tiers on a hand-built evaluation context: a parameter
--    without a supplied cell reads its value binding, and one with neither is
--    `unknownName` — nothing is evaluated (no binding context opens). The
--    algorithm-channel and counted tiers that once sat between them had no
--    production writer and were retired on 2026-10-13 (their guards
--    `readOfAlgorithmOnlyBinding` and the algorithm half of `readOfValuedBinding`
--    with them). C#: `ParameterReadFallbackTests`.
def readOfValuedBinding : Except Error Result :=
  let ctx : KatLang.EvalCtx := { callStack := [KatLang.preludeAlg] }
  KatLang.runEvalM (KatLang.eval (param "x") ctx [("x", .atom 7)])

#guard match readOfValuedBinding with
  | .ok (.atom 7) => true
  | _ => false

def readOfUnboundParameter : Except Error Result × Nat :=
  let ctx : KatLang.EvalCtx := { callStack := [KatLang.preludeAlg] }
  let (result, state) := (KatLang.eval (param "x") ctx []).runState EvalState.empty
  (result, state.nextBindingContext)

#guard match readOfUnboundParameter with
  | (.error (.unknownName "x"), 1) => true
  | _ => false

-- 4. LAW D — forwarding transports the one supplied cell (NEED-08); it never
--    re-evaluates the source. `Fwd(Bad)` forwards `w` into `One(w)` (its first row fails there): Bad's
--    body runs ONCE, and the only other contexts are the calls to Fwd and One.
#guard aoFailsWithDivByZero [callOf "Fwd" [resolve "Bad"]]
#guard aoContexts [callOf "Fwd" [resolve "Bad"]] == aoContexts [resolve "Bad"] + 2

-- 5. Builtin VALUE slots and the `.string` receiver read a failed parameter through
--    the ordinary parameter read (the parameter's need cell, `demandNeed`): the
--    slot's failure, with no second evaluation of the argument.
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


--------------------------------------------------------------------------------
-- 10. The `.string` receiver of a parameter reports what the written argument
--     raises (2026-10-13)
--------------------------------------------------------------------------------
-- A parameter bound to a supplied cell is read through that cell by the
-- ordinary-dot `string` intrinsic as well: the receiver is a VALUE demand of the
-- slot (CALL-06), so its first demand evaluates the written argument once and a
-- failure is that argument's own report — exactly what the value-position read
-- `Plus(f, x) = f + x` reports (section 7) — never a report re-judged against
-- the parameter's callable (`hasSuppliedParameterCell` in the `string` arm of
-- `evalDotCallCounted`). Until 2026-10-13 that arm applied the zero-argument law
-- to the PARAMETER first: `Show(Inc)` lost Inc's property frame, `Show({ x + 1 })`
-- was the parameter-shaped `arityMismatch 1 0` instead of the block's
-- `unresolvedImplicitParams [x]`, and a clause family's `noMatchingBranch` named
-- the parameter instead of the family. The C# engine already read the cell first.
#guard match (runWithContexts (aoRoot [callOf "Show" [resolve "Inc"]])).fst with
  | .error err => innermostIsArityMismatch 1 0 err && hasContext "while evaluating property Inc" err
  | .ok _ => false

-- The cross-engine table. Each program is the C# elaborated AST of the source in
-- its doc comment, encoded by `LeanAstEncoder`; the C# test class
-- `DotStringParameterReceiverFrameTests` renders the C# error tree of the same
-- source in the same neutral spelling on every C# route, and checks that this
-- file holds the same programs and the same expectations. The neutral tree lists
-- every frame, outermost first — a `dotCall` frame with its receiver — then the
-- leaf with its payload. It omits only two documented presentation differences:
-- Lean's builtin-arity description frame (`builtinArityError`; C# keeps that
-- description on the `ArityMismatch` leaf), and C#'s implicit-parameter frame
-- around `UnresolvedImplicitParams` (no Lean counterpart). Until 2026-10-13 it
-- omitted a `dotCall` frame's receiver too, because `openExprName` wrote a
-- parameter receiver `(param)` where C# writes its name; both now write the name
-- (`HigherOrderCalls.lean` § "Parameter callee and receiver names").

section DotStringParameterReceiver
open KatLang (Expr privateProp runResult)

/-- One frame of the neutral tree, or `none` for a frame the tree omits. -/
def dsrNeutralFrame (message : String) : Option String :=
  let callPrefix := "while evaluating call to "
  let dotCallPrefix := "while evaluating dotCall ."
  let propertyPrefix := "while evaluating property "
  if message.startsWith callPrefix then
    some ("call " ++ (message.drop callPrefix.length).toString)
  else if message.startsWith dotCallPrefix then
    some ("dotCall ." ++ (message.drop dotCallPrefix.length).toString)
  else if message.startsWith propertyPrefix then
    some ("property " ++ (message.drop propertyPrefix.length).toString)
  else if message.startsWith "expected " && message.endsWith " arguments" then
    none
  else
    some message

/-- The leaf of the neutral tree: the error kind and its payload. -/
def dsrNeutralLeaf : Error -> String
  | .arityMismatch expected actual => s!"arityMismatch {expected} {actual}"
  | .unresolvedImplicitParams names => s!"unresolvedImplicitParams {names}"
  | .noMatchingBranch name => s!"noMatchingBranch {name}"
  | .typeMismatch message => s!"typeMismatch {message}"
  | .notAnAlgorithm description => s!"notAnAlgorithm {description}"
  | .divByZero => "divByZero"
  | .badArity => "badArity"
  | other => s!"other {reprStr other}"

/-- The neutral error tree: kept frames outermost first, then the leaf. -/
def dsrNeutralError : Error -> String
  | .withContext message inner =>
      match dsrNeutralFrame message with
      | some frame => frame ++ " > " ++ dsrNeutralError inner
      | none => dsrNeutralError inner
  | leaf => dsrNeutralLeaf leaf

/-- The neutral spelling of a value (the language-spec corpus's spelling). -/
partial def dsrNeutralResult : Result -> String
  | .atom n => toString n
  | .str s => "'" ++ s ++ "'"
  | .bool b => Result.boolText b
  | .sequenceValue items => "S[" ++ String.intercalate ", " (items.map dsrNeutralResult) ++ "]"
  | .listValue items => "L[" ++ String.intercalate ", " (items.map dsrNeutralResult) ++ "]"
  -- A run result never holds a call reference (the run boundary refuses it).
  | .callRef _ => "CallReference"
  | .argView _ => "CallReference"

/-- The neutral observation of a program: `ok <value>`, or its neutral error tree. -/
def dsrObserve (program : Expr) : String :=
  match runResult program with
  | .ok value => "ok " ++ dsrNeutralResult value
  | .error err => dsrNeutralError err

/-- `Inc(z) = z + 1` / `Show(v) = v.string` / `Show(Inc)` -/
def dsrParameterizedProperty : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Inc" (alg ["z"] [] [] [(.binary .add (.param "z") (.num 1))]), privateProp "Show" (alg ["v"] [] [] [(.dotCall (.param "v") "string" none)])] [(.call (.resolve "Show") [.resolve "Inc"])])
#guard dsrObserve dsrParameterizedProperty == "call Show > dotCall .string of v > property Inc > arityMismatch 1 0"

/-- `Inc(z) = z + 1` / `Plus(f, x) = f + x` / `Plus(Inc, 5)` -/
def dsrParameterizedPropertyValueRead : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Inc" (alg ["z"] [] [] [(.binary .add (.param "z") (.num 1))]), privateProp "Plus" (alg ["f", "x"] [] [] [(.binary .add (.param "f") (.param "x"))])] [(.call (.resolve "Plus") [.resolve "Inc", .num 5])])
#guard dsrObserve dsrParameterizedPropertyValueRead == "call Plus > property Inc > arityMismatch 1 0"

/-- `Show(v) = v.string` / `Show({ x + 1 })` -/
def dsrWrittenBlock : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Show" (alg ["v"] [] [] [(.dotCall (.param "v") "string" none)])] [(.call (.resolve "Show") [(.algorithmExpr (alg ["x"] [] [] [(.binary .add (.param "x") (.num 1))]))])])
#guard dsrObserve dsrWrittenBlock == "call Show > dotCall .string of v > unresolvedImplicitParams [x]"

/-- `Plus(f, x) = f + x` / `Plus({ y + 1 }, 5)` -/
def dsrWrittenBlockValueRead : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Plus" (alg ["f", "x"] [] [] [(.binary .add (.param "f") (.param "x"))])] [(.call (.resolve "Plus") [(.algorithmExpr (alg ["y"] [] [] [(.binary .add (.param "y") (.num 1))])), .num 5])])
#guard dsrObserve dsrWrittenBlockValueRead == "call Plus > unresolvedImplicitParams [y]"

/-- `Inc(z) = z + 1` / `Show(v) = v.string` / `Show({ Inc })` -/
def dsrInlineAlias : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Inc" (alg ["z"] [] [] [(.binary .add (.param "z") (.num 1))]), privateProp "Show" (alg ["v"] [] [] [(.dotCall (.param "v") "string" none)])] [(.call (.resolve "Show") [(.algorithmExpr (.alias none [] [] (.resolve "Inc") none false))])])
#guard dsrObserve dsrInlineAlias == "call Show > dotCall .string of v > property Inc > arityMismatch 1 0"

/-- `F(0) = 1` / `F(n) = n` / `Show(v) = v.string` / `Show(F)` -/
def dsrClauseFamily : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (.conditional none [] [⟨.litInt 0, (alg [] [] [] [.num 1])⟩, ⟨.bind "n", (alg [] [] [] [.param "n"])⟩]), privateProp "Show" (alg ["v"] [] [] [(.dotCall (.param "v") "string" none)])] [(.call (.resolve "Show") [.resolve "F"])])
#guard dsrObserve dsrClauseFamily == "call Show > dotCall .string of v > noMatchingBranch F"

/-- `F(0) = 1` / `F(n) = n` / `Plus(f, x) = f + x` / `Plus(F, 5)` -/
def dsrClauseFamilyValueRead : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (.conditional none [] [⟨.litInt 0, (alg [] [] [] [.num 1])⟩, ⟨.bind "n", (alg [] [] [] [.param "n"])⟩]), privateProp "Plus" (alg ["f", "x"] [] [] [(.binary .add (.param "f") (.param "x"))])] [(.call (.resolve "Plus") [.resolve "F", .num 5])])
#guard dsrObserve dsrClauseFamilyValueRead == "call Plus > noMatchingBranch F"

/-- `Inc(z) = z + 1` / `A = Inc` / `Show(v) = v.string` / `Show(A)` -/
def dsrCallableAlias : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (.alias none [] [] (.resolve "Inc")), privateProp "Inc" (alg ["z"] [] [] [(.binary .add (.param "z") (.num 1))]), privateProp "Show" (alg ["v"] [] [] [(.dotCall (.param "v") "string" none)])] [(.call (.resolve "Show") [.resolve "A"])])
#guard dsrObserve dsrCallableAlias == "call Show > dotCall .string of v > property A > arityMismatch 1 0"

/-- `F(0) = 1` / `F(n) = n` / `A = F` / `Show(v) = v.string` / `Show(A)` -/
def dsrFamilyAlias : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (.alias none [] [] (.resolve "F")), privateProp "F" (.conditional none [] [⟨.litInt 0, (alg [] [] [] [.num 1])⟩, ⟨.bind "n", (alg [] [] [] [.param "n"])⟩]), privateProp "Show" (alg ["v"] [] [] [(.dotCall (.param "v") "string" none)])] [(.call (.resolve "Show") [.resolve "A"])])
#guard dsrObserve dsrFamilyAlias == "call Show > dotCall .string of v > noMatchingBranch A"

/-- `Lib = { public F(x) = x }` / `Show(v) = v.string` / `Show(Lib.F)` -/
def dsrMemberPath : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Lib" (alg [] [] [publicProp "F" (alg ["x"] [] [] [.param "x"])] []), privateProp "Show" (alg ["v"] [] [] [(.dotCall (.param "v") "string" none)])] [(.call (.resolve "Show") [(.dotCall (.resolve "Lib") "F" none)])])
#guard dsrObserve dsrMemberPath == "call Show > dotCall .string of v > dotCall .F of Lib > arityMismatch 1 0"

/-- `Inc(z) = z + 1` / `Lib = { public A = Inc }` / `Show(v) = v.string` / `Show(Lib.A)` -/
def dsrMemberAlias : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Lib" (alg [] [] [publicProp "A" (.alias none [] [] (.resolve "Inc"))] []), privateProp "Inc" (alg ["z"] [] [] [(.binary .add (.param "z") (.num 1))]), privateProp "Show" (alg ["v"] [] [] [(.dotCall (.param "v") "string" none)])] [(.call (.resolve "Show") [(.dotCall (.resolve "Lib") "A" none)])])
#guard dsrObserve dsrMemberAlias == "call Show > dotCall .string of v > dotCall .A of Lib > arityMismatch 1 0"

/-- `Inc(z) = z + 1` / `Show(v) = v.string` / `Show2(w) = Show(w)` / `Show2(Inc)` -/
def dsrForwardedParameter : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Inc" (alg ["z"] [] [] [(.binary .add (.param "z") (.num 1))]), privateProp "Show" (alg ["v"] [] [] [(.dotCall (.param "v") "string" none)]), privateProp "Show2" (alg ["w"] [] [] [(.call (.resolve "Show") [.param "w"])])] [(.call (.resolve "Show2") [.resolve "Inc"])])
#guard dsrObserve dsrForwardedParameter == "call Show2 > call Show > dotCall .string of v > property Inc > arityMismatch 1 0"

/-- `Head(x, *rest) = x` / `Show(v) = v.string` / `Show(Head)` -/
def dsrMinimumSupply : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Head" (algWithParameters [{ name := "x" }, { name := "rest", kind := .collecting }] [] [] [.param "x"]), privateProp "Show" (alg ["v"] [] [] [(.dotCall (.param "v") "string" none)])] [(.call (.resolve "Show") [.resolve "Head"])])
#guard dsrObserve dsrMinimumSupply == "call Show > dotCall .string of v > property Head > arityMismatch 1 0"

/-- `Show(v) = v.string` / `Show(count)` -/
def dsrBuiltin : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Show" (alg ["v"] [] [] [(.dotCall (.param "v") "string" none)])] [(.call (.resolve "Show") [.resolve "count"])])
#guard dsrObserve dsrBuiltin == "call Show > dotCall .string of v > arityMismatch 1 0"

/-- `Only(*xs) = xs` / `Show(v) = v.string` / `Show(Only)` -/
def dsrCollectingOnlyCallable : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Only" (algWithParameters [{ name := "xs", kind := .collecting }] [] [] [.param "xs"]), privateProp "Show" (alg ["v"] [] [] [(.dotCall (.param "v") "string" none)])] [(.call (.resolve "Show") [.resolve "Only"])])
#guard dsrObserve dsrCollectingOnlyCallable == "call Show > dotCall .string of v > typeMismatch builtin property `string` expects a numeric receiver"

/-- `Z = 5` / `Show(v) = v.string` / `Show(Z)` -/
def dsrZeroParameterProperty : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Z" (alg [] [] [] [.num 5]), privateProp "Show" (alg ["v"] [] [] [(.dotCall (.param "v") "string" none)])] [(.call (.resolve "Show") [.resolve "Z"])])
#guard dsrObserve dsrZeroParameterProperty == "ok '5'"

/-- `Bad = 1 / 0` / `Show(v) = v.string` / `Show(Bad)` -/
def dsrFailingProperty : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Bad" (alg [] [] [] [(.binary .div (.num 1) (.num 0))]), privateProp "Show" (alg ["v"] [] [] [(.dotCall (.param "v") "string" none)])] [(.call (.resolve "Show") [.resolve "Bad"])])
#guard dsrObserve dsrFailingProperty == "call Show > dotCall .string of v > divByZero"

/-- `Show(v) = v.string` / `Show(1 / 0)` -/
def dsrFailingArgument : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Show" (alg ["v"] [] [] [(.dotCall (.param "v") "string" none)])] [(.call (.resolve "Show") [(.binary .div (.num 1) (.num 0))])])
#guard dsrObserve dsrFailingArgument == "call Show > dotCall .string of v > divByZero"

/-- `Z = 5` / `Show(v) = v + 0, v.string` / `Show(Z)` -/
def dsrReadThenString : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Z" (alg [] [] [] [.num 5]), privateProp "Show" (alg ["v"] [] [] [(.binary .add (.param "v") (.num 0)), (.dotCall (.param "v") "string" none)])] [(.call (.resolve "Show") [.resolve "Z"])])
#guard dsrObserve dsrReadThenString == "ok S[5, '5']"

/-- `Inc(z) = z + 1` / `Show(v) = v.string` / `Step(x) = Show(Inc)` / `repeat(Step(0), 1)` -/
def dsrLoopStep : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Inc" (alg ["z"] [] [] [(.binary .add (.param "z") (.num 1))]), privateProp "Show" (alg ["v"] [] [] [(.dotCall (.param "v") "string" none)]), privateProp "Step" (alg ["x"] [] [] [(.call (.resolve "Show") [.resolve "Inc"])])] [(.call (.resolve "repeat") [(.call (.resolve "Step") [.num 0]), .num 1])])
#guard dsrObserve dsrLoopStep == "call repeat > call Show > dotCall .string of v > property Inc > arityMismatch 1 0"

/-- `Inc(z) = z + 1` / `Show(*vs) = vs.string` / `Show(Inc)` -/
def dsrCollectingParameter : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Inc" (alg ["z"] [] [] [(.binary .add (.param "z") (.num 1))]), privateProp "Show" (algWithParameters [{ name := "vs", kind := .collecting }] [] [] [(.dotCall (.param "vs") "string" none)])] [(.call (.resolve "Show") [.resolve "Inc"])])
#guard dsrObserve dsrCollectingParameter == "call Show > dotCall .string of vs > property Inc > arityMismatch 1 0"

/-- `Inc(z) = z + 1` / `Show(v) = v.string(1)` / `Show(Inc)` -/
def dsrIntrinsicArguments : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Inc" (alg ["z"] [] [] [(.binary .add (.param "z") (.num 1))]), privateProp "Show" (alg ["v"] [] [] [(.dotCall (.param "v") "string" (some [.num 1]))])] [(.call (.resolve "Show") [.resolve "Inc"])])
#guard dsrObserve dsrIntrinsicArguments == "call Show > dotCall .string of v > arityMismatch 0 1"

end DotStringParameterReceiver

end KatLangTests
