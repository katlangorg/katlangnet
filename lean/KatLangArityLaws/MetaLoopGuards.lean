import KatLangArityLaws.MetaLoop

open KatLang

/-!
# META-S3-3 guards: `while(meta step)` and `repeat(meta step, count)` on whole programs

Every guard runs a whole program through the authoritative `runResult` / `runResultWithState`:
the builtin META binding step of `applyBuiltinCounted` (`builtinDeclaresMeta`, the arity gate,
THE ONE binder `bindNeedPatterns` whose `.metaRef` arm is `NeedPlan.reference`), the captured
plan's canonical callee cell (`NeedPlan.calleeCell`, CR-13) and ONE sticky supply
(`argumentViewCells`, CR-9), and the unchanged loop kernels (`WhileRound.advance`,
`runNeedWhileRound`, `runNeedStepSlots`, `loopResultCounted`). They are the executable evidence
for the source facts the total laws of `MetaLoop.lean` state over their capabilities: that the
evaluator installs that sequence, in that order (RP-1), on the plain and the dot route.
Serial Lean says nothing about C# async resolution, cancellation, J7 plan retention or
diagnostics text; those are pinned by the C# suites (`MetaLoopInterfaceTests`).
-/

namespace KatLang.MetaLoopGuards

def metaParam (name : Ident) : CallableParameter := { name := name, kind := .metaRef }
def add (a b : Expr) : Expr := .binary .add a b
def sub (a b : Expr) : Expr := .binary .sub a b
def dv (a b : Expr) : Expr := .binary .div a b
def lt (a b : Expr) : Expr := .comparison a [⟨.lt, b⟩]
def callN (f : Ident) (args : List Expr) : Expr := .call (.resolve f) args
def aliasOf (target : Expr) : Algorithm := .alias none [] [] target
def dot (receiver : Expr) (name : Ident) (args : Option (List Expr)) : Expr := Expr.dotCall receiver name args
def algorithmOf (receiver : Expr) : Expr := Expr.dotCall receiver "Algorithm" none
def argumentsOf (receiver : Expr) : Expr := Expr.dotCall receiver "Arguments" none
/-- `[1][5]*`: an explicit spread whose own evaluation fails (`badIndex`). -/
def badSpread : Expr := .sequenceSpread (.index (.listLiteral [.num 1]) [.num 5])

/-- `Step(x) = x + 1, x < 3`, `Inc(x) = x + 1`, `Fib(a, b) = b, a + b`, `Keep(meta op) = op`,
    `Z = false` (zero parameters), `F(0) = 100`, `F(n) = n - 1`, `Box = { S(x) = x + 1, x < 3 }`,
    `Id(y) = y`, `N = 5`, `Start = Step(0)`, `C(*xs) = xs*`, `E = ()`, `P = 0, 1`. -/
def decls : List (Ident × Algorithm) :=
  [("Step", alg ["x"] [] [] [add (.param "x") (.num 1), lt (.param "x") (.num 3)]),
   ("Inc", alg ["x"] [] [] [add (.param "x") (.num 1)]),
   ("Fib", alg ["a", "b"] [] [] [.param "b", add (.param "a") (.param "b")]),
   ("Keep", algWithParameters [metaParam "op"] [] [] [.param "op"]),
   ("Z", alg [] [] [] [.boolLiteral false]),
   ("F", .conditional none [] [
      ⟨.litInt 0, alg [] [] [] [.num 100]⟩,
      ⟨.bind "n", alg [] [] [] [sub (.param "n") (.num 1)]⟩]),
   ("Box", algPrivate [] [] [("S", alg ["x"] [] [] [add (.param "x") (.num 1), lt (.param "x") (.num 3)])] []),
   ("Id", alg ["y"] [] [] [.param "y"]),
   ("N", alg [] [] [] [.num 5]),
   ("Start", alg [] [] [] [callN "Step" [.num 0]]),
   ("C", algWithParameters [{ name := "xs", kind := .collecting }] [] [] [.sequenceSpread (.param "xs")]),
   ("E", alg [] [] [] [.emptySequence 0]),
   ("P", alg [] [] [] [.num 0, .num 1])]

def program (extra : List (Ident × Algorithm)) (rows : List Expr) : Expr :=
  .algorithmExpr (algPrivate [] [] (decls ++ extra) rows)

def run (extra : List (Ident × Algorithm)) (rows : List Expr) : Except Error Result :=
  runResult (program extra rows)

def heap (extra : List (Ident × Algorithm)) (rows : List Expr) : Array NeedCell :=
  match runResultWithState (program extra rows) with
  | .ok (_, s) => s.needs
  | .error _ => #[]

/-- The heap cells whose suspension is the written expression `source`. -/
def cellsOf (h : Array NeedCell) (source : Expr) : Nat :=
  (h.toList.filter fun cell =>
    match cell.suspension with
    | .expression e _ _ => reprStr e == reprStr source
    | _ => false).length

def innermost : Error → Error
  | .withContext _ inner => innermost inner
  | e => e

def valueIs (r : Except Error Result) (v : Result) : Bool :=
  match r with | .ok value => value == v | .error _ => false

def isMetaRefusal (r : Except Error Result) : Bool :=
  match r with
  | .error e => match innermost e with
    | .notAnAlgorithm m => m == "meta: not a supplied call computation" | _ => false
  | .ok _ => false

def isArity (r : Except Error Result) (expected actual : Nat) : Bool :=
  match r with
  | .error e => match innermost e with | .arityMismatch x y => x == expected && y == actual | _ => false
  | .ok _ => false

def isIllegal (r : Except Error Result) (m : String) : Bool :=
  match r with
  | .error e => match innermost e with | .illegalInEval x => x == m | _ => false
  | .ok _ => false

def isTypeMismatch (r : Except Error Result) : Bool :=
  match r with
  | .error e => match innermost e with | .typeMismatch _ => true | _ => false
  | .ok _ => false

def isDivByZero (r : Except Error Result) : Bool :=
  match r with
  | .error e => match innermost e with | .divByZero => true | _ => false
  | .ok _ => false

def isBadIndex (r : Except Error Result) : Bool :=
  match r with
  | .error e => match innermost e with | .badIndex => true | _ => false
  | .ok _ => false

def isNotAnAlgorithm (r : Except Error Result) : Bool :=
  match r with
  | .error e => match innermost e with | .notAnAlgorithm _ => true | _ => false
  | .ok _ => false

def unit : Result := .sequenceValue []

/-! ## D1/D7: plain and dot forms bind the same META parameter -/

#guard valueIs (run [] [callN "while" [callN "Step" [.num 0]]]) (.atom 3)
#guard valueIs (run [] [dot (callN "Step" [.num 0]) "while" none]) (.atom 3)
#guard valueIs (run [] [dot (callN "Step" [.num 0]) "while" (some [])]) (.atom 3)
#guard valueIs (run [] [callN "repeat" [callN "Inc" [.num 0], .num 5]]) (.atom 5)
#guard valueIs (run [] [dot (callN "Inc" [.num 0]) "repeat" (some [.num 5])]) (.atom 5)
-- Multi-state; an explicit spread inside the captured call; family redispatch per iteration.
#guard valueIs (run [] [dot (callN "Fib" [.num 0, .num 1]) "repeat" (some [.num 10])])
  (.sequenceValue [.atom 55, .atom 89])
#guard valueIs (run [] [dot (callN "Fib" [.sequenceSpread (.resolve "P")]) "repeat" (some [.num 10])])
  (.sequenceValue [.atom 55, .atom 89])
#guard valueIs (run [] [dot (callN "F" [.num 2]) "repeat" (some [.num 3])]) (.atom 100)
-- LOOP-01: a non-spread sequence argument is ONE state slot.
#guard valueIs (run [] [dot (callN "Id" [.resolve "P"]) "repeat" (some [.num 2])])
  (.sequenceValue [.atom 0, .atom 1])
-- Chained and nested.
#guard valueIs (run [] [dot (dot (callN "Step" [.num 0]) "while" none) "Inc" none]) (.atom 4)
#guard valueIs (run [] [dot (callN "Inc" [dot (callN "Step" [.num 0]) "while" none]) "repeat" (some [.num 2])]) (.atom 5)

/-! ## CR-9: the original argument cell is the initial state, supplied once, never re-formed -/

#guard cellsOf (heap [] [dot (callN "Inc" [.num 5]) "repeat" (some [.num 4])]) (.num 5) == 1
#guard valueIs (run [] [dot (callN "Inc" [.num 5]) "repeat" (some [.num 4])]) (.atom 9)
-- The captured call is never dispatched: no cell of `Inc`'s body `x + 1` is a written call of `Inc`.
#guard cellsOf (heap [] [callN "while" [callN "Step" [.num 0]]]) (callN "Step" [.num 0]) == 1

/-! ## D6: no implicit provenance -/

#guard isMetaRefusal (run [] [dot (.resolve "Start") "while" none])
#guard isMetaRefusal (run [] [callN "while" [.resolve "Start"]])
-- An already captured reference supplied as a VALUE is not a call computation either.
#guard isMetaRefusal (run [("R", alg [] [] [] [callN "Keep" [callN "Step" [.num 0]]])] [dot (.resolve "R") "while" none])
-- The explicit `Start()` is a fresh call: its step is `Start` over ZERO state; its one row
-- `(1, true)` is not a Boolean flag.
#guard isTypeMismatch (run [] [dot (callN "Start" []) "while" none])
-- A bare step and a value are not supplied calls.
#guard isMetaRefusal (run [] [callN "while" [.resolve "Step"]])
#guard isMetaRefusal (run [] [callN "repeat" [.num 5, .num 0]])

/-! ## RP-1: capture, then the captured supply, then the count -/

-- A captured spread's failure precedes an invalid count (the retired `repeat(Inc, 1 / 0, [1][5]*)`
-- was `badIndex` too).
#guard isBadIndex (run [] [dot (callN "Inc" [badSpread]) "repeat" (some [dv (.num 1) (.num 0)])])
#guard isBadIndex (run [] [callN "repeat" [callN "Inc" [badSpread], .num (-1)]])
-- After a successful spread the count is demanded and validated.
#guard isDivByZero (run [] [dot (callN "Fib" [.sequenceSpread (.resolve "P")]) "repeat" (some [dv (.num 1) (.num 0)])])
#guard isIllegal (run [] [dot (callN "Inc" [.num 0]) "repeat" (some [.num (-1)])]) "Repeat count must be >= 0"
#guard isTypeMismatch (run [] [dot (callN "Inc" [.num 0]) "repeat" (some [.boolLiteral true])])
-- A non-spread initial cell stays lazy: the invalid count is reported, not the cell's failure.
#guard isIllegal (run [] [dot (callN "Inc" [dv (.num 1) (.num 0)]) "repeat" (some [.num (-1)])]) "Repeat count must be >= 0"
-- Zero iterations still materialize the initial state, without projecting the step (LOOP-05).
#guard isDivByZero (run [] [dot (callN "Inc" [dv (.num 1) (.num 0)]) "repeat" (some [.num 0])])
#guard valueIs (run [] [dot (callN "Inc" [.num 7]) "repeat" (some [.num 0])]) (.atom 7)
#guard valueIs (run [] [dot (callN "N" [.num 1]) "repeat" (some [.num 0])]) (.atom 1)
-- One iteration binds the zero-parameter step `N` over one state slot: its own arity failure.
#guard isArity (run [] [dot (callN "N" [.num 1]) "repeat" (some [.num 1])]) 0 1

/-! ## Outer arity is the builtin's exact fixed arity, decided before any demand -/

#guard isArity (run [] [callN "while" [callN "Step" [.num 0], .num 1]]) 1 2
#guard isArity (run [] [callN "repeat" [callN "Inc" [.num 0]]]) 2 1
#guard isArity (run [] [callN "while" [.resolve "Step", .num 0]]) 1 2
#guard isArity (run [] [callN "repeat" [.resolve "Inc", .num 3, .num 0]]) 2 3
#guard isArity (run [] [dot (callN "Step" [.num 0]) "while" (some [.num 1])]) 1 2
#guard isArity (run [] [callN "while" []]) 1 0
-- The gate precedes the binder: a failing argument of a refused supply is never demanded.
#guard isArity (run [] [callN "while" [callN "Step" [dv (.num 1) (.num 0)], dv (.num 1) (.num 0)]]) 1 2

/-! ## OD-1: zero effective initial state is the ordinary empty state -/

#guard valueIs (run [] [dot (callN "Z" []) "while" none]) unit
#guard valueIs (run [] [dot (callN "Z" []) "repeat" (some [.num 0])]) unit
-- An empty explicit spread supplies zero slots.
#guard valueIs (run [] [dot (callN "Z" [.sequenceSpread (.resolve "E")]) "while" none]) unit
-- A collecting step over zero slots: each round emits zero slots.
#guard valueIs (run [] [dot (callN "C" []) "repeat" (some [.num 3])]) unit
#guard valueIs (run [] [dot (callN "C" []) "repeat" (some [.num 1])]) unit
-- A step that requires a parameter fails through its own binding.
#guard isArity (run [] [dot (callN "Inc" []) "repeat" (some [.num 1])]) 1 0
#guard isArity (run [] [dot (callN "Step" []) "while" none]) 1 0
-- Zero repetitions of a parameterized step never bind it.
#guard valueIs (run [] [dot (callN "Inc" []) "repeat" (some [.num 0])]) unit

/-! ## CR-2 (META-S3-4): a qualified member invocation is a plan; the named alias still works -/

-- Before META-S3-4 this was the META refusal (a dot callee); it is now a written invocation.
#guard valueIs (run [] [dot (dot (.resolve "Box") "S" (some [.num 0])) "while" none]) (.atom 3)
-- An argumentless member path is still no invocation (D-2A).
#guard isMetaRefusal (run [] [dot (dot (.resolve "Box") "S" none) "while" none])
#guard valueIs (run [("S2", aliasOf (dot (.resolve "Box") "S" none))] [dot (callN "S2" [.num 0]) "while" none]) (.atom 3)

/-! ## Wrappers (CR-3/CR-4) -/

-- `While(meta step) = while(step.Algorithm(step.Arguments*))`: before META-S3-4 a refused dot
-- callee; now the rebuilt projected invocation is itself captured (CR-14).
#guard valueIs (run [("While", algWithParameters [metaParam "step"] [] []
      [callN "while" [Expr.dotCall (.param "step") "Algorithm" (some [.sequenceSpread (argumentsOf (.param "step"))])]])]
    [callN "While" [callN "Step" [.num 0]]]) (.atom 3)
-- Through a runtime alias of the projection: a name callee, captured.
def aliasWrapper : List (Ident × Algorithm) :=
  [("While", algWithParameters [metaParam "step"] [] (propsPrivate [("S", aliasOf (algorithmOf (.param "step")))])
      [callN "while" [callN "S" [.sequenceSpread (argumentsOf (.param "step"))]]])]
#guard valueIs (run aliasWrapper [dot (callN "Step" [.num 0]) "While" none]) (.atom 3)
-- Plain forwarding transports the original cell: `W(step) = while(step)`.
#guard valueIs (run [("W", alg ["step"] [] [] [callN "while" [.param "step"]])] [dot (callN "Step" [.num 0]) "W" none]) (.atom 3)
-- META forwarding hands `while` a Ready reference: refused (CR-4).
#guard isMetaRefusal (run [("W", algWithParameters [metaParam "step"] [] [] [callN "while" [.param "step"]])]
    [dot (callN "Step" [.num 0]) "W" none])

/-! ## D7: ordinary lookup decides which `while` a call selects -/

-- A user META declaration named `while` shadows the builtin in both spellings.
#guard valueIs (run [("while", algWithParameters [metaParam "s"] [] [] [.num 100])]
    [callN "while" [callN "Step" [.num 0]], dot (callN "Step" [.num 0]) "while" none])
  (.sequenceValue [.atom 100, .atom 100])
-- A structural member named `while` wins over the builtin fallback.
#guard valueIs (run [("Obj", algPrivate [] [] [("while", alg [] [] [] [.num 7])] [])] [dot (.resolve "Obj") "while" none]) (.atom 7)

/-! ## Higher-order and alias -/

#guard valueIs (run [("Run", alg ["loop", "s"] [] [] [.call (.param "loop") [.call (.param "s") [.num 0]]])]
    [callN "Run" [.resolve "while", .resolve "Step"]]) (.atom 3)
#guard valueIs (run [("W", aliasOf (.resolve "while"))] [callN "W" [callN "Step" [.num 0]]]) (.atom 3)
-- A loop builtin as a CALLBACK receives Ready element cells, which META refuses.
#guard isMetaRefusal (run [] [callN "map" [.listLiteral [.num 1], .resolve "while"]])
-- A builtin as a loop step.
#guard valueIs (run [] [dot (callN "first" [.listLiteral [.listLiteral [.num 1]]]) "repeat" (some [.num 2])]) (.atom 1)
-- `Invoke()` of a captured loop call runs the loop afresh.
#guard valueIs (run [("R", alg [] [] [] [callN "Keep" [callN "while" [callN "Step" [.num 0]]]])]
    [dot (.resolve "R") "Invoke" (some [])]) (.atom 3)

end KatLang.MetaLoopGuards
