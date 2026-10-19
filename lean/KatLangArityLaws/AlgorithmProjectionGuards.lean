import KatLangArityLaws.AlgorithmProjection
import KatLangArityLaws.CallReferenceGuards

open KatLang KatLang.CallReferenceGuards

/-!
# META-S3-1 guards: `R.Algorithm` on whole programs

Every guard runs a whole program through the authoritative `runResult` / `runResultWithState`: the
`"Algorithm"` arms of `evalDotCallCounted`, the link arm of `evalCallCountedExpr`, a supplied link's
`evalSuppliedAt` / `projectNeedWrittenAt`, `NeedPlan.calleeCell` and `NeedLink.receiverCell`. They
are executable evidence for the source facts `KatLangArityLaws/AlgorithmProjection.lean` cannot reach
(the `partial` evaluator installs the total definitions). Heap observations follow
`CallReferenceGuards`: every execution of `Sq(x) = Id(x * x)` allocates ONE cell for `x * x`, so the
number of such cells counts target executions; the captured argument `5` is one cell, so one such
cell means it was supplied once — never re-supplied to a fresh call.
-/

namespace KatLang.AlgorithmProjectionGuards

def algorithm (receiver : Expr) : Expr := .dotCall receiver "Algorithm" none
def algorithmCall (receiver : Expr) (args : List Expr) : Expr := .dotCall receiver "Algorithm" (some args)
def arguments (receiver : Expr) : Expr := .dotCall receiver "Arguments" none
def lt (a b : Expr) : Expr := .compare .lt a b
def callN (f : Ident) (args : List Expr) : Expr := .call (.resolve f) args

/-- Extra declarations: `Step(x) = x + 1, x < 3`, `Twice(f, x) = f(f(x))`,
    `Mk(t) = Id(Capture(Sq(t)))` (each execution allocates one `Capture(Sq(t))` cell),
    `Pick(f) = (f, f(2))` (VALUE and CALLABLE of ONE supplied cell),
    `Outer(k) = { Scale(x) = x * k; Capture(Scale(1)) }` (a nested owner),
    `Hold(g) = Capture(g(0))`, `Lib = { Algorithm(x) = x + 1000 }`, `Algorithm(x) = x * 100`. -/
def extra : List (Ident × Algorithm) :=
  [("Step", alg ["x"] [] [] [add (.param "x") (.num 1), lt (.param "x") (.num 3)]),
   ("Twice", alg ["f", "x"] [] [] [.call (.param "f") [.call (.param "f") [.param "x"]]]),
   ("Mk", alg ["t"] [] [] [callN "Id" [callN "Capture" [callN "Sq" [.param "t"]]]]),
   ("Pick", alg ["f"] [] [] [.param "f", .call (.param "f") [.num 2]]),
   ("Outer", algPrivate ["k"] [] [("Scale", alg ["x"] [] [] [mul (.param "x") (.param "k")])]
      [callN "Capture" [callN "Scale" [.num 1]]]),
   ("Hold", alg ["g"] [] [] [callN "Capture" [.call (.param "g") [.num 0]]]),
   ("Lib", algPrivate [] [] [("Algorithm", alg ["x"] [] [] [add (.param "x") (.num 1000)])] []),
   ("Algorithm", alg ["x"] [] [] [mul (.param "x") (.num 100)])]

def run (decls : List (Ident × Algorithm)) (rows : List Expr) : Except Error Result :=
  runResult (program (extra ++ decls) rows)

def heap (decls : List (Ident × Algorithm)) (rows : List Expr) : Array NeedCell :=
  finalHeap (program (extra ++ decls) rows)

def isCycle (r : Except Error Result) : Bool :=
  match r with
  | .error e => match innermost e with | .demandCycle => true | _ => false
  | .ok _ => false

def isNotAnAlgorithm (r : Except Error Result) (description : String) : Bool :=
  match r with
  | .error e => match innermost e with | .notAnAlgorithm d => d == description | _ => false
  | .ok _ => false

/-- `R = Capture(Sq(5))`. -/
def R : Expr := .resolve "R"

/-! ## CR-14 (c) — a fresh call with exactly the new supply; the original invocation is independent -/

#guard valueIs (run refR [algorithmCall R [.num 8]]) (.atom 64)
-- …and the captured argument `5` is never supplied to it: Sq runs once, over a new `8`.
#guard cellsOf (heap refR [algorithmCall R [.num 8]]) xx == 1
#guard cellsOf (heap refR [algorithmCall R [.num 8]]) (.num 5) == 0
-- Grouped callee position (CR-14 a): `(R.Algorithm)(8)` is the same fresh call.
#guard valueIs (run refR [.call (algorithm R) [.num 8]]) (.atom 64)
-- Zero supply is a fresh call with NO arguments: Sq's ordinary arity rejection, never `R.Invoke()`.
#guard isArity (run refR [algorithmCall R []]) 1 0
#guard isArity (run refR [.call (algorithm R) []]) 1 0
-- `R.Invoke()` keeps S1 semantics beside the projection: (25, 64, 25), the original argument once.
#guard valueIs (run refR [.listLiteral [invoke R, algorithmCall R [.num 8], invoke R]])
  (.listValue [.atom 25, .atom 64, .atom 25])
#guard cellsOf (heap refR [.listLiteral [invoke R, algorithmCall R [.num 8], invoke R]]) (.num 5) == 1

/-! ## CR-14 (a) — CALLABLE transport through ordinary binders, callbacks and loops -/

#guard valueIs (run refR [callN "Ap" [algorithm R, .num 7]]) (.atom 49)
#guard valueIs (run refR [callN "Twice" [algorithm R, .num 3]]) (.atom 81)
#guard valueIs (run refR [callN "map" [.listLiteral [.num 1, .num 2, .num 3], algorithm R]])
  (.listValue [.atom 1, .atom 4, .atom 9])
-- Original argument forwarding: `R.Algorithm(R.Arguments*)` transports the ORIGINAL cell.
#guard valueIs (run refR [algorithmCall R [.sequenceSpread (arguments R)]]) (.atom 25)
#guard cellsOf (heap refR [algorithmCall R [.sequenceSpread (arguments R)], invoke R]) (.num 5) == 1
-- `R.Algorithm.while(R.Arguments*)` uses the ordinary condition-first `while`.
#guard valueIs (run [("S", alg [] [] [] [callN "Capture" [callN "Step" [.num 0]]])]
    [.dotCall (algorithm (.resolve "S")) "while" (some [.sequenceSpread (arguments (.resolve "S"))])]) (.atom 3)
-- A user META wrapper: `Loop(meta operation) = operation.Algorithm.while(operation.Arguments*)`.
#guard valueIs (run [("Loop", algWithParameters [metaParam "operation"] [] []
      [.dotCall (algorithm (.param "operation")) "while" (some [.sequenceSpread (arguments (.param "operation"))])])]
    [callN "Loop" [callN "Step" [.num 0]]]) (.atom 3)
-- `repeat`, argument order unchanged: `S.Algorithm.repeat(5, S.Arguments*)` over `Inc(0)`.
#guard valueIs (run [("S", alg [] [] [] [callN "Capture" [callN "Inc" [.num 0]]])]
    [.dotCall (algorithm (.resolve "S")) "repeat" (some [.num 5, .sequenceSpread (arguments (.resolve "S"))])]) (.atom 5)

/-! ## P8 — fresh family dispatch; lexical ownership -/

-- The captured call selected `Sign(0) = 100`; a fresh call selects by its NEW supply.
#guard valueIs (run [("F", alg [] [] [] [callN "Capture" [callN "Sign" [.num 0]]])]
    [.listLiteral [invoke (.resolve "F"), algorithmCall (.resolve "F") [.num 7], algorithmCall (.resolve "F") [.num 0]]])
  (.listValue [.atom 100, .atom 7, .atom 100])
-- A nested callee keeps its owner's activation (`k = 10`), not the consumer's names.
#guard valueIs (run [("O", alg [] [] [] [callN "Outer" [.num 10]]),
                    ("UseP", algPrivate ["r"] [] [("Scale", alg ["x"] [] [] [.num 0]), ("k", alg [] [] [] [.num 1000])]
                      [algorithmCall (.param "r") [.num 4]])]
    [callN "UseP" [.resolve "O"]]) (.atom 40)

/-! ## CR-14 (b) — bare VALUE is the callee's ordinary VALUE, never a callable result (P9) -/

#guard isArity (run refR [algorithm R]) 1 0
-- A computed value never becomes callable: a list built from `R.Algorithm` demands its VALUE.
#guard isArity (run refR [.listLiteral [algorithm R]]) 1 0
-- …and `if` selects a VALUE: `Ap(if(true, R.Algorithm, 0), 8)` has no callable.
#guard match run refR [callN "Ap" [callN "if" [.boolLiteral true, algorithm R, .num 0], .num 8]] with
  | .error e => match innermost e with | .notAnAlgorithm "param(f)" => true | _ => false
  | .ok _ => false
-- A zero-parameter callee read bare is its property value.
#guard valueIs (run [("P", alg [] [] [] [.num 42]), ("Q", alg [] [] [] [callN "Capture" [.call (.resolve "P") []]])]
    [algorithm (.resolve "Q")]) (.atom 42)

/-! ## CR-15 / P5 — one receiver for both channels of a supplied link -/

-- `Pick(Mk(5).Algorithm)` uses the link's VALUE (an arity rejection would end the run, so the
-- callee is a zero-parameter `P`) and its CALLABLE: the receiver `Mk(5)` runs ONCE.
#guard valueIs (run [("P0", algWithParameters [{ name := "rest", kind := .collecting }] [] [] [.num 9]),
                    ("MkP", alg ["t"] [] [] [callN "Id" [callN "Capture" [callN "P0" [.param "t"]]]]),
                    ("PickV", alg ["f"] [] [] [.param "f", .call (.param "f") [.num 2]])]
    [callN "PickV" [algorithm (callN "MkP" [.num 5])]]) (.sequenceValue [.atom 9, .atom 9])
#guard cellsOf (heap [("P0", algWithParameters [{ name := "rest", kind := .collecting }] [] [] [.num 9]),
                      ("MkP", alg ["t"] [] [] [callN "Id" [callN "Capture" [callN "P0" [.param "t"]]]]),
                      ("PickV", alg ["f"] [] [] [.param "f", .call (.param "f") [.num 2]])]
    [callN "PickV" [algorithm (callN "MkP" [.num 5])]])
    (callN "Capture" [callN "P0" [.param "t"]]) == 1
-- Two CALLABLE uses of one link: still one receiver run.
#guard valueIs (run [] [callN "Twice" [algorithm (callN "Mk" [.num 5]), .num 2]]) (.atom 16)
#guard cellsOf (heap [] [callN "Twice" [algorithm (callN "Mk" [.num 5]), .num 2]])
    (callN "Capture" [callN "Sq" [.param "t"]]) == 1

/-! ## CR-14 route — structural precedence, reservation, receiver kinds -/

-- A declared member `Algorithm` wins (VALUE, call, grouped call, CALLABLE transport).
#guard valueIs (run [] [.dotCall (.resolve "Lib") "Algorithm" (some [.num 1])]) (.atom 1001)
#guard valueIs (run [] [.call (algorithm (.resolve "Lib")) [.num 2]]) (.atom 1002)
#guard valueIs (run [] [callN "Ap" [algorithm (.resolve "Lib"), .num 3]]) (.atom 1003)
-- On a miss the lexical `Algorithm(x) = x * 100` is never consulted by dot syntax…
#guard isTypeMismatch (run [] [algorithm (.num 5)]) (algorithmRequiresCallReferenceMessage (.atom 5))
#guard isTypeMismatch (run [] [algorithmCall (.num 5) [.num 1]]) (algorithmRequiresCallReferenceMessage (.atom 5))
-- …while a plain call stays the user's algorithm.
#guard valueIs (run [] [callN "Algorithm" [.num 2]]) (.atom 200)
-- An argument view is not a reference.
#guard isTypeMismatchAny (run refR [algorithm (arguments R)])
#guard isTypeMismatchAny (run refR [callN "Ap" [algorithm (arguments R), .num 1]])
-- A captured callee without CALLABLE identity is absence, reported as the captured callee.
#guard isNotAnAlgorithm (run [("G", alg ["f"] [] [] [callN "Capture" [.call (.param "f") [.num 1]]])]
    [algorithmCall (callN "G" [.num 5]) [.num 2]]) capturedCalleeDescription

/-! ## NEED-06 / NEED-09 — cycles and failure provenance -/

-- `R = Hold(R.Algorithm)`: the link's CALLABLE re-enters its own projection — DemandCycle.
#guard isCycle (run [("R", alg [] [] [] [callN "Hold" [algorithm R]])] [algorithmCall R [.num 1]])
#guard isCycle (run [("R", alg [] [] [] [callN "Hold" [algorithm R]])] [callN "Ap" [algorithm R, .num 1]])
#guard isCycle (run [("R", alg [] [] [] [callN "Hold" [algorithm R]])] [invoke R])
-- L2: a parameter-rooted path over a FAILING link keeps the failure's kind (`min([])` is
-- illegalInEval), never "no identity"…
#guard isIllegal (run [("Bad", alg [] [] [] [callN "min" [.listLiteral []]]),
                       ("UseP", alg ["p"] [] [] [callN "Ap" [.dotCall (.param "p") "G" none, .num 0]])]
    [callN "UseP" [algorithm (.resolve "Bad")]]) "min requires a non-empty collection"
-- …while a value receiver is the static absence it always was (`param(f)`).
#guard isNotAnAlgorithm (run [("UseP", alg ["p"] [] [] [callN "Ap" [.dotCall (.param "p") "G" none, .num 0]])]
    [callN "UseP" [.num 5]]) "param(f)"
-- A receiver that is not a reference is a failed projection (TypeMismatch), not absence.
#guard isTypeMismatchAny (run [("UseP", alg ["p"] [] [] [callN "Ap" [.dotCall (.param "p") "G" none, .num 0]])]
    [callN "UseP" [algorithm (.num 5)]])

end KatLang.AlgorithmProjectionGuards
