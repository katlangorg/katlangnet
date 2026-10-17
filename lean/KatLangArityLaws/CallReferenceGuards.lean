import KatLangArityLaws.CallReference

open KatLang

/-!
# CallReference S1 guards: `meta`, `Result.callRef` and `R.Invoke()` on whole programs

Every guard runs a whole program through the authoritative `runResult` /
`runResultWithState` (the root demand, the production binder with `NeedPlan.reference`, the dot
route's `Invoke` arm and the run result boundary). Heap observations count the production
`NeedCell`s a run allocated, which is how freshness and sharing are observed without effects:

* every execution of `Sq(x) = Id(x * x)` allocates ONE fresh cell for its written argument
  `x * x`, so the number of such cells is the number of target executions;
* the argument `5` of the captured `Sq(5)` is one cell, so a single such cell means every
  execution bound the SAME memoized argument;
* the spread of `Pair()` opens into Ready item cells, so a single Ready `1` means the spread ran
  once.
These guards are executable evidence for the source facts the theorems of
`KatLangArityLaws/CallReference.lean` cannot reach (the `partial` evaluator).
-/

namespace KatLang.CallReferenceGuards

def metaParam (name : Ident) : CallableParameter := { name := name, kind := .metaRef }

def mul (a b : Expr) : Expr := .binary .mul a b
def add (a b : Expr) : Expr := .binary .add a b
def call (f : Ident) (args : List Expr) : Expr := .call (.resolve f) args
def invoke (receiver : Expr) : Expr := .dotCall receiver "Invoke" (some [])

/-- The shared declarations: `Id(y) = y`, `Sq(x) = Id(x * x)`, `Capture(meta op) = op`,
    `Inc(x) = x + 1`, `Ap(f, x) = f(x)`, `Add(a, b) = a + b`, `Pair() = 1, 2`,
    `Fwd(y) = Capture(y)`, `Fwd2(z) = Fwd(z)`, `Both(x, meta op) = x + op.Invoke()`,
    `Use(v) = v + Capture(v).Invoke()`, `Mix([x], meta op) = x`, `Mix2(meta op, [x]) = x`,
    `Sign(0) = 100`, `Sign(n) = n`, `Box = { Invoke = 3 }`, `Invoke(r) = r + 1`. -/
def decls : List (Ident × Algorithm) :=
  [("Id", alg ["y"] [] [] [.param "y"]),
   ("Sq", alg ["x"] [] [] [call "Id" [mul (.param "x") (.param "x")]]),
   ("Capture", algWithParameters [metaParam "op"] [] [] [.param "op"]),
   ("Inc", alg ["x"] [] [] [add (.param "x") (.num 1)]),
   ("Ap", alg ["f", "x"] [] [] [.call (.param "f") [.param "x"]]),
   ("Add", alg ["a", "b"] [] [] [add (.param "a") (.param "b")]),
   ("Pair", alg [] [] [] [.num 1, .num 2]),
   ("Fwd", alg ["y"] [] [] [call "Capture" [.param "y"]]),
   ("Fwd2", alg ["z"] [] [] [call "Fwd" [.param "z"]]),
   ("Both", algWithParameters [{ name := "x" }, metaParam "op"] [] []
      [add (.param "x") (invoke (.param "op"))]),
   ("Use", alg ["v"] [] [] [add (.param "v") (invoke (call "Capture" [.param "v"]))]),
   ("Mix", algWithParameterPatterns [.listValue [.capture { name := "x" }], .capture (metaParam "op")]
      [] [] [.param "x"]),
   ("Mix2", algWithParameterPatterns [.capture (metaParam "op"), .listValue [.capture { name := "x" }]]
      [] [] [.param "x"]),
   ("Sign", .conditional none [] [
      ⟨.litInt 0, alg [] [] [] [.num 100]⟩,
      ⟨.bind "n", alg [] [] [] [.param "n"]⟩]),
   ("Box", algPrivate [] [] [("Invoke", alg [] [] [] [.num 3])] []),
   ("Invoke", alg ["r"] [] [] [add (.param "r") (.num 1)])]

/-- A program: the shared declarations, extra ones, and the root output rows. -/
def program (extra : List (Ident × Algorithm)) (rows : List Expr) : Expr :=
  .algorithmExpr (algPrivate [] [] (decls ++ extra) rows)

/-- `R = Capture(Sq(5))`. -/
def refR : List (Ident × Algorithm) := [("R", alg [] [] [] [call "Capture" [call "Sq" [.num 5]]])]

def valueIs (r : Except Error Result) (v : Result) : Bool :=
  match r with
  | .ok value => value == v
  | .error _ => false

partial def innermost : Error → Error
  | .withContext _ inner => innermost inner
  | e => e

def isMetaRefusal (r : Except Error Result) : Bool :=
  match r with
  | .error e => match innermost e with
    | .notAnAlgorithm message => message == "meta: not a supplied call computation"
    | _ => false
  | .ok _ => false

def isTypeMismatch (r : Except Error Result) (message : String) : Bool :=
  match r with
  | .error e => match innermost e with
    | .typeMismatch m => m == message
    | _ => false
  | .ok _ => false

def isTypeMismatchAny (r : Except Error Result) : Bool :=
  match r with
  | .error e => match innermost e with
    | .typeMismatch _ => true
    | _ => false
  | .ok _ => false

def isArity (r : Except Error Result) (expected actual : Nat) : Bool :=
  match r with
  | .error e => match innermost e with
    | .arityMismatch x y => x == expected && y == actual
    | _ => false
  | .ok _ => false

def isIllegal (r : Except Error Result) (message : String) : Bool :=
  match r with
  | .error e => match innermost e with
    | .illegalInEval m => m == message
    | _ => false
  | .ok _ => false

def isDivByZero (r : Except Error Result) : Bool :=
  match r with
  | .error e => match innermost e with
    | .divByZero => true
    | _ => false
  | .ok _ => false

/-- The final heap of a successful run. -/
def finalHeap (e : Expr) : Array NeedCell :=
  match runResultWithState e with
  | .ok (_, s) => s.needs
  | .error _ => #[]

/-- Cells whose suspension is the written expression `source`. -/
def cellsOf (heap : Array NeedCell) (source : Expr) : Nat :=
  (heap.toList.filter fun cell =>
    match cell.suspension with
    | .expression e _ _ => reprStr e == reprStr source
    | _ => false).length

/-- Ready cells holding exactly `value`. -/
def readyCellsOf (heap : Array NeedCell) (value : Result) : Nat :=
  (heap.toList.filter fun cell =>
    match cell.suspension with
    | .ready (v, _) => v == value
    | _ => false).length

def xx : Expr := mul (.param "x") (.param "x")

/-! ## Capture and `Invoke()` -/

-- `R = Capture(Sq(5))`, `R.Invoke()` is 25.
#guard valueIs (runResult (program refR [invoke (.resolve "R")])) (.atom 25)

-- Capture is inert: `R` read without invoking executes nothing of `Sq` (no `x * x` cell).
#guard cellsOf (finalHeap (program refR [.boolLiteral (true)])) xx == 0
#guard valueIs (runResult (program (refR ++ [("K", alg [] [] [] [.resolve "R", .num 1])])
    [.index (.resolve "K") [.num 1]])) (.atom 1)
#guard cellsOf (finalHeap (program (refR ++ [("K", alg [] [] [] [.resolve "R", .num 1])])
    [.index (.resolve "K") [.num 1]])) xx == 0

-- Two invocations: two FRESH target executions over ONE memoized argument cell.
#guard valueIs (runResult (program refR [add (invoke (.resolve "R")) (invoke (.resolve "R"))])) (.atom 50)
#guard cellsOf (finalHeap (program refR [add (invoke (.resolve "R")) (invoke (.resolve "R"))])) xx == 2
#guard cellsOf (finalHeap (program refR [add (invoke (.resolve "R")) (invoke (.resolve "R"))])) (.num 5) == 1

-- A reference is a value: equal to itself (plan identity), transported by `if` and lists.
#guard valueIs (runResult (program refR [.compare .eq (.resolve "R") (.resolve "R")])) (.bool true)
-- Identity follows the property cache: the explicit call `R()` evaluates the body again and
-- captures a NEW cell.
#guard valueIs (runResult (program refR [.compare .eq (.resolve "R") (.call (.resolve "R") [])])) (.bool false)
#guard valueIs (runResult (program (refR ++ [("Q", alg [] [] [] [call "Capture" [call "Sq" [.num 5]]])])
    [.compare .eq (.resolve "R") (.resolve "Q")])) (.bool false)
#guard valueIs (runResult (program refR
    [invoke (call "if" [.boolLiteral true, .resolve "R", .num 0])])) (.atom 25)
#guard valueIs (runResult (program refR
    [invoke (.index (.listLiteral [.num 7, .resolve "R"]) [.num 1])])) (.atom 25)

/-! ## VALUE before META, forwarding, sharing -/

-- `Use(v) = v + Capture(v).Invoke()` over `Sq(5)`: VALUE first, then META reuses the cells.
#guard valueIs (runResult (program [] [call "Use" [call "Sq" [.num 5]]])) (.atom 50)
#guard cellsOf (finalHeap (program [] [call "Use" [call "Sq" [.num 5]]])) (.num 5) == 1
#guard cellsOf (finalHeap (program [] [call "Use" [call "Sq" [.num 5]]])) xx == 2

-- META before VALUE in one head: `Both(x, meta op)` with one cell in both positions.
#guard valueIs (runResult (program [("G", alg ["v"] [] [] [call "Both" [.param "v", .param "v"]])]
    [call "G" [call "Sq" [.num 5]]])) (.atom 50)
#guard cellsOf (finalHeap (program [("G", alg ["v"] [] [] [call "Both" [.param "v", .param "v"]])]
    [call "G" [call "Sq" [.num 5]]])) (.num 5) == 1

-- Two forwarding hops reach the ORIGINAL call.
#guard valueIs (runResult (program [] [invoke (call "Fwd2" [call "Sq" [.num 5]])])) (.atom 25)

-- A shadowing owner never re-resolves the captured callee: `Other` declares its own `Sq`.
#guard valueIs (runResult (program
    (refR ++ [("Other", algPrivate [] [] [("Sq", alg ["x"] [] [] [.num 0])] [invoke (.resolve "R")])])
    [.resolve "Other"])) (.atom 25)

-- A higher-order CALLABLE argument keeps its identity through the plan.
#guard valueIs (runResult (program [] [invoke (call "Capture" [call "Ap" [.resolve "Inc", .num 1]])])) (.atom 2)

-- A clause family is dispatched afresh by the ordinary dispatcher.
#guard valueIs (runResult (program [] [invoke (call "Capture" [call "Sign" [.num 0]])])) (.atom 100)
#guard valueIs (runResult (program [] [invoke (call "Capture" [call "Sign" [.num 7]])])) (.atom 7)

-- An arbitrary spread is formed ONCE, whatever the number of invocations.
#guard valueIs (runResult (program [("S", alg [] [] [] [call "Capture" [call "Add" [.sequenceSpread (call "Pair" [])]]])]
    [add (invoke (.resolve "S")) (invoke (.resolve "S"))])) (.atom 6)
#guard readyCellsOf (finalHeap (program [("S", alg [] [] [] [call "Capture" [call "Add" [.sequenceSpread (call "Pair" [])]]])]
    [add (invoke (.resolve "S")) (invoke (.resolve "S"))])) (.atom 1) == 1

/-! ## Refusals and the capture domain -/

#guard isMetaRefusal (runResult (program [] [call "Capture" [.num 5]]))
#guard isMetaRefusal (runResult (program [] [call "Capture" [.resolve "Sq"]]))
-- A property read is not a written call, even when its VALUE is one call's result.
#guard isMetaRefusal (runResult (program [("Y", alg [] [] [] [call "Sq" [.num 5]])] [call "Capture" [.resolve "Y"]]))
-- An existing reference is Ready data: capturing it again is refused.
#guard isMetaRefusal (runResult (program refR [call "Capture" [.resolve "R"]]))
-- A dot callee is out of the S1 capture domain.
#guard isMetaRefusal (runResult (program [] [call "Capture" [.dotCall (.resolve "Box") "Invoke" none]]))
-- An adapter has no CALLABLE identity: `Again(meta op) = op(3)`.
#guard match runResult (program [("Again", algWithParameters [metaParam "op"] [] [] [.call (.param "op") [.num 3]])]
    [call "Again" [call "Sq" [.num 5]]]) with
  | .error e => match innermost e with | .notAnAlgorithm _ => true | _ => false
  | .ok _ => false

-- Written-order refusal (J8b): an earlier inspecting pattern's failure wins…
#guard isDivByZero (runResult (program [] [call "Mix" [.binary .div (.num 1) (.num 0), .num 25]]))
-- …while a META position written first refuses before a later pattern is inspected.
#guard isMetaRefusal (runResult (program [] [call "Mix2" [.num 25, .binary .div (.num 1) (.num 0)]]))
-- Cardinality precedes META (NEED-05).
#guard isArity (runResult (program [] [call "Capture" [.sequenceSpread (call "Pair" [])]])) 1 2

/-! ## The `Invoke` intrinsic route -/

#guard isIllegal (runResult (program refR [.dotCall (.resolve "R") "Invoke" none])) invokeRequiresArgumentListMessage
#guard isArity (runResult (program refR [.dotCall (.resolve "R") "Invoke" (some [.num 8])])) 0 1
-- A scalar receiver is the intrinsic's kind rejection, never the lexical `Invoke(r) = r + 1`.
#guard isTypeMismatch (runResult (program [] [invoke (.num 5)])) (invokeRequiresCallReferenceMessage (.atom 5))
-- A declared structural member wins.
#guard valueIs (runResult (program [] [.dotCall (.resolve "Box") "Invoke" none])) (.atom 3)
-- A plain call `Invoke(4)` stays the user's algorithm.
#guard valueIs (runResult (program [] [call "Invoke" [.num 4]])) (.atom 5)

/-! ## Boundaries: run result, text, ordinary operations -/

#guard isTypeMismatch (runResult (program refR [.resolve "R"])) callReferenceLeavesRunMessage
#guard isTypeMismatch (runResult (program refR [.listLiteral [.num 1, .resolve "R"]])) callReferenceLeavesRunMessage
#guard isTypeMismatch (runResult (program refR [.resolve "R", .num 1])) callReferenceLeavesRunMessage
#guard isTypeMismatch (runResult (program refR [.interpolatedString "v=" [{ hole := .resolve "R", text := "" }]]))
  callReferenceHasNoTextMessage
#guard isTypeMismatchAny (runResult (program refR [add (.resolve "R") (.num 1)]))
#guard isTypeMismatchAny (runResult (program refR [.dotCall (.resolve "R") "string" none]))

/-! ## Static placement (pre-evaluation validation) -/

#guard isIllegal (runResult (.algorithmExpr (algPrivate [] []
    [("Bad", algWithParameterPatterns [.listValue [.capture (metaParam "x")]] [] [] [.num 1])] [.num 0])))
  invalidMetaParameterMessage
#guard isIllegal (runResult (.algorithmExpr (algPrivate [] []
    [("Bad", algWithParameterPatterns [.capture (metaParam "x"), .capture { name := "x" }] [] [] [.num 1])] [.num 0])))
  invalidMetaParameterMessage

end KatLang.CallReferenceGuards
