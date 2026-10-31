import KatLangArityLaws.Tick

open KatLang

/-!
# `tick()` guards: whole programs over the authoritative evaluator

Every guard runs a whole program through `runResultM` from an explicit initial state (`EvalState.empty`
for an ordinary run) and reads both the outcome and the FINAL counter, so a guard pins how many times
the primitive actually executed — including on a failed run, whose state `runState` keeps. They are
the executable evidence for the laws of `Tick.lean` composed with the ordinary demand rules: laziness,
the property cache and CACHE-PUB-1, NeedCell sharing, callable transport, aliases, `if`, META replay
and the arity gate. C# routes, async, cancellation and concurrency are C# evidence (`TickBuiltinTests`).
-/

namespace KatLang.TickGuards

def add (a b : Expr) : Expr := .binary .add a b
def dv (a b : Expr) : Expr := .binary .div a b
def callN (f : Ident) (args : List Expr) : Expr := .call (.resolve f) args
def tickCall : Expr := callN "tick" []
def aliasOf (target : Expr) : Algorithm := .alias none [] [] target
def metaParam (name : Ident) : CallableParameter := { name := name, kind := .metaRef }

/-- `A = tick()`, `B = { tick() }`, `Ignore(x) = 7`, `Twice(x) = x + x`, `T = tick`, `Apply(f) = f()`,
    `Replay(meta op) = op.Invoke() + op.Invoke()`. -/
def decls : List (Ident × Algorithm) :=
  [("A", alg [] [] [] [tickCall]),
   ("B", alg [] [] [] [.algorithmExpr (alg [] [] [] [tickCall])]),
   ("Ignore", alg ["x"] [] [] [.num 7]),
   ("Twice", alg ["x"] [] [] [add (.param "x") (.param "x")]),
   ("T", aliasOf (.resolve "tick")),
   ("Apply", alg ["f"] [] [] [.call (.param "f") []]),
   ("Replay", algWithParameters [metaParam "op"] [] []
      [add (Expr.dotCall (.param "op") "Invoke" (some [])) (Expr.dotCall (.param "op") "Invoke" (some []))])]

def program (rows : List Expr) : Expr := .algorithmExpr (algPrivate [] [] decls rows)

/-- The outcome and the final counter of a run that starts from `start`. -/
def runFrom (start : EvalState) (rows : List Expr) : Except Error Result × Nat :=
  let (result, state) := (runResultM (program rows)).runState start
  (result, state.tickCounter)

def run (rows : List Expr) : Except Error Result × Nat := runFrom EvalState.empty rows

def atoms (values : List Int) : Result := .sequenceValue (values.map Result.atom)

def innermost : Error → Error
  | .withContext _ inner => innermost inner
  | e => e

def okWith (outcome : Except Error Result × Nat) (value : Result) (ticks : Nat) : Bool :=
  match outcome with
  | (.ok v, n) => v == value && n == ticks
  | _ => false

def failsWith (outcome : Except Error Result × Nat) (p : Error → Bool) (ticks : Nat) : Bool :=
  match outcome with
  | (.error e, n) => p (innermost e) && n == ticks
  | _ => false

def isInvocationRequired : Error → Bool
  | .illegalInEval m => m == builtinInvocationRequiredMessage .tickBuiltin
  | _ => false

def isDivByZero : Error → Bool
  | .divByZero => true
  | _ => false

def isExhausted : Error → Bool
  | .illegalInEval m => m == tickExhaustedMessage
  | _ => false

def isArity (expected actual : Nat) : Error → Bool
  | .arityMismatch x y => x == expected && y == actual
  | _ => false

/-! ## Direct calls, the property cache, fresh calls and publication -/

-- `tick(), tick(), tick()` is (1, 2, 3).
#guard okWith (run [tickCall, tickCall, tickCall]) (atoms [1, 2, 3]) 3
-- Declaring `A = tick()` ticks nothing; `A + A` reads ONE cached execution.
#guard okWith (run [.num 0]) (.atom 0) 0
#guard okWith (run [add (.resolve "A") (.resolve "A")]) (.atom 2) 1
-- `A() + A()` and `B() + B()` are two fresh executions.
#guard okWith (run [add (callN "A" []) (callN "A" [])]) (.atom 3) 2
#guard okWith (run [add (callN "B" []) (callN "B" [])]) (.atom 3) 2
-- CACHE-PUB-1: the first `A()` establishes the empty entry; later calls stay fresh.
#guard okWith (run [callN "A" [], .resolve "A", callN "A" [], .resolve "A"]) (atoms [1, 1, 2, 1]) 2
#guard okWith (run [.resolve "A", callN "A" [], .resolve "A"]) (atoms [1, 2, 1]) 2

/-! ## Laziness, NeedCell sharing, callable transport and META replay -/

#guard okWith (run [callN "Ignore" [tickCall], tickCall]) (atoms [7, 1]) 1
#guard okWith (run [callN "Twice" [tickCall], tickCall]) (atoms [2, 2]) 2
#guard okWith (run [callN "T" [], callN "Apply" [.resolve "tick"], tickCall]) (atoms [1, 2, 3]) 3
#guard okWith (run [callN "if" [.boolLiteral false, tickCall, .num 0], tickCall]) (atoms [0, 1]) 1
#guard okWith (run [callN "Replay" [tickCall], tickCall]) (atoms [3, 3]) 3
-- Transporting the callable executes nothing.
#guard okWith (run [callN "Ignore" [.resolve "tick"], callN "Ignore" [.resolve "T"]]) (atoms [7, 7]) 0

/-! ## Rejected entry advances nothing -/

-- A bare VALUE demand is the invocation-required refusal, directly or through an alias.
#guard failsWith (run [.resolve "tick"]) isInvocationRequired 0
#guard failsWith (run [add (.resolve "tick") (.num 1)]) isInvocationRequired 0
#guard failsWith (run [.resolve "T"]) isInvocationRequired 0
-- A supplied argument is the ordinary arity rejection, before the argument is demanded.
#guard failsWith (run [callN "tick" [dv (.num 1) (.num 0)]]) (isArity 0 1) 0
#guard failsWith (run [callN "T" [.num 1]]) (isArity 0 1) 0
#guard failsWith (run [Expr.dotCall (.num 5) "tick" none]) (isArity 0 1) 0
-- No rollback: a tick that executed stays counted when a later computation fails.
#guard failsWith (run [tickCall, dv (.num 1) (.num 0), tickCall]) isDivByZero 1

/-! ## The checked boundary -/

-- The last representable value is returned exactly…
#guard okWith (runFrom { tickCounter := tickCounterLimit - 1 } [tickCall])
  (.atom (Int.ofNat tickCounterLimit)) tickCounterLimit
#guard tickCounterLimit = 9223372036854775807
-- …and the next execution is the deterministic refusal, leaving the counter where it was.
#guard failsWith (runFrom { tickCounter := tickCounterLimit } [tickCall])
  isExhausted tickCounterLimit
-- A refused execution does not stop an independent earlier value from being produced first.
#guard failsWith (runFrom { tickCounter := tickCounterLimit - 1 } [tickCall, tickCall])
  isExhausted tickCounterLimit

end KatLang.TickGuards
