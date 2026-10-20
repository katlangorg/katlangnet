import KatLangArityLaws.InvocationRoute

open KatLang

/-!
# META-S3-4 guards: generalized META capture of written invocations, on whole programs

Every guard runs a whole program through the authoritative `runResult` / `runResultWithState`,
over the generalized invocation domain (`NeedPlan.callShape?`: every written call, every
argument-bearing dot edge), the plan route (`NeedPlan.routeOf` over `classifyPlanRouteWith`, which
decides through the ordinary dot decision `selectDotEdge`) and the route-aware `execute`,
`viewCells` and `calleeCell`. They are the executable evidence for the source facts the total laws
of `InvocationRoute.lean` state over their capabilities: that the evaluator installs exactly that
route on VALUE, `Invoke()`, the argument view, `.Algorithm` and loop setup.

Sections A–C/E/S/N are the 26 META-S3-4-R research guards (scratch `MetaS34Guards.lean`, the
motivating program first), promoted unchanged except that the intrinsic-route refusal now names its
own description (`NeedPlan.invocationRefusal`, D-1A). Section D adds the settled decisions D-1A,
D-2A, D-3 and D-5 and the production cases. Section G (META-S3-4-DIAG, October 20 2026) pins the
`.Algorithm`-route dispatch name of ordinary and planned invocations. The prelude `Math` module is outside the Lean model
(SEMANTIC-ALIGNMENT), so `Math.Abs(-3).repeat(2)` is pinned by the C# suites only; serial Lean says
nothing about C# async resolution, cancellation, J7 plan retention or diagnostics text.
-/

namespace KatLang.InvocationRouteGuards

def metaParam (name : Ident) : CallableParameter := { name := name, kind := .metaRef }
def add (a b : Expr) : Expr := .binary .add a b
def mul (a b : Expr) : Expr := .binary .mul a b
def lt (a b : Expr) : Expr := .comparison a [⟨.lt, b⟩]
def eq (a b : Expr) : Expr := .comparison a [⟨.eq, b⟩]
def callN (f : Ident) (args : List Expr) : Expr := .call (.resolve f) args
def dot (receiver : Expr) (name : Ident) (args : Option (List Expr)) : Expr := Expr.dotCall receiver name args
def argsOf (r : Expr) : Expr := dot r "Arguments" none
def spreadArgs (r : Expr) : Expr := .sequenceSpread (argsOf r)
/-- `op.Algorithm(op.Arguments*)` -/
def rebuilt (op : Expr) : Expr := dot op "Algorithm" (some [spreadArgs op])

/-- `Step(x) = x + 1, x < 3`, `Inc(x) = x + 1`, `Add(a, b) = a + b`,
    `Box = { Step(x) = …, G(x) = x * 10, V = 7 }`, `Box4 = { Algorithm(x) = x * 100 }`,
    `Capture(meta op) = op`, `Inspect(meta op) = op.Arguments.count`, `Ignore(meta op) = 0`, the
    three loop wrappers, `Repeat`, `Op(meta op) = Capture(op.Algorithm(op.Arguments*))`,
    `Start = Step(0)`, `Mk(t) = Capture(Inc(t))`, `Id(y) = y`. -/
def decls : List (Ident × Algorithm) :=
  [("Step", alg ["x"] [] [] [add (.param "x") (.num 1), lt (.param "x") (.num 3)]),
   ("Inc", alg ["x"] [] [] [add (.param "x") (.num 1)]),
   ("Add", alg ["a", "b"] [] [] [add (.param "a") (.param "b")]),
   ("Box", algPrivate [] [] [
      ("Step", alg ["x"] [] [] [add (.param "x") (.num 1), lt (.param "x") (.num 3)]),
      ("G", alg ["x"] [] [] [mul (.param "x") (.num 10)]),
      ("V", alg [] [] [] [.num 7])] []),
   ("Box4", algPrivate [] [] [("Algorithm", alg ["x"] [] [] [mul (.param "x") (.num 100)])] []),
   ("Capture", algWithParameters [metaParam "op"] [] [] [.param "op"]),
   ("Inspect", algWithParameters [metaParam "op"] [] [] [dot (argsOf (.param "op")) "count" none]),
   ("Ignore", algWithParameters [metaParam "op"] [] [] [.num 0]),
   -- Loop(meta op) = op.Algorithm(op.Arguments*).while
   ("Loop", algWithParameters [metaParam "op"] [] [] [dot (rebuilt (.param "op")) "while" none]),
   -- Loop2(meta op) = while(op.Algorithm(op.Arguments*))
   ("Loop2", algWithParameters [metaParam "op"] [] [] [callN "while" [rebuilt (.param "op")]]),
   -- Loop3(meta op) = (op.Algorithm)(op.Arguments*).while
   ("Loop3", algWithParameters [metaParam "op"] [] [] [dot (.call (dot (.param "op") "Algorithm" none) [spreadArgs (.param "op")]) "while" none]),
   -- Repeat(meta op, n) = op.Algorithm(op.Arguments*).repeat(n)
   ("Repeat", algWithParameters [metaParam "op", { name := "n" }] [] [] [dot (rebuilt (.param "op")) "repeat" (some [.param "n"])]),
   -- Op(meta op) = Capture(op.Algorithm(op.Arguments*))
   ("Op", algWithParameters [metaParam "op"] [] [] [callN "Capture" [rebuilt (.param "op")]]),
   ("Start", alg [] [] [] [callN "Step" [.num 0]]),
   ("Mk", alg ["t"] [] [] [callN "Capture" [callN "Inc" [.param "t"]]]),
   ("Id", alg ["y"] [] [] [.param "y"])]

def program (extra : List (Ident × Algorithm)) (rows : List Expr) : Expr :=
  .algorithmExpr (algPrivate [] [] (decls ++ extra) rows)

def run (extra : List (Ident × Algorithm)) (rows : List Expr) : Except Error Result :=
  runResult (program extra rows)

def heap (extra : List (Ident × Algorithm)) (rows : List Expr) : Array NeedCell :=
  match runResultWithState (program extra rows) with
  | .ok (_, s) => s.needs
  | .error _ => #[]

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

def isNotAnAlgorithm (description : String) (r : Except Error Result) : Bool :=
  match r with
  | .error e => match innermost e with
    | .notAnAlgorithm m => m == description | _ => false
  | .ok _ => false

def isMetaRefusal : Except Error Result → Bool := isNotAnAlgorithm "meta: not a supplied call computation"
def isInvocationRefusal : Except Error Result → Bool := isNotAnAlgorithm "meta: not a callable invocation"

def isCycle (r : Except Error Result) : Bool :=
  match r with
  | .error e => match innermost e with | .demandCycle => true | _ => false
  | .ok _ => false

def isLocalOnly (r : Except Error Result) : Bool :=
  match r with
  | .error e => match innermost e with | .localOnlyProperty .. => true | _ => false
  | .ok _ => false

def isArityMismatch (r : Except Error Result) : Bool :=
  match r with
  | .error e => match innermost e with | .arityMismatch .. => true | _ => false
  | .ok _ => false

def invoke (e : Expr) : Expr := dot e "Invoke" (some [])

/-! ## A: the reconstructed `R.Algorithm` invocation is a written invocation META captures -/

-- THE motivating program: `Step(0).Loop` with `Loop(meta op) = op.Algorithm(op.Arguments*).while`.
#guard valueIs (run [] [dot (callN "Step" [.num 0]) "Loop" none]) (.atom 3)
#guard valueIs (run [] [callN "Loop" [callN "Step" [.num 0]]]) (.atom 3)
#guard valueIs (run [] [dot (callN "Step" [.num 0]) "Loop2" none]) (.atom 3)
#guard valueIs (run [] [dot (callN "Step" [.num 0]) "Loop3" none]) (.atom 3)
#guard valueIs (run [] [dot (callN "Step" [.num 2]) "Loop" none]) (.atom 3)
-- A member invocation captured by the wrapper, then reconstructed.
#guard valueIs (run [] [callN "Loop" [dot (.resolve "Box") "Step" (some [.num 1])]]) (.atom 3)

/-! ## B: the `repeat` wrapper -/

#guard valueIs (run [] [dot (callN "Inc" [.num 0]) "Repeat" (some [.num 5])]) (.atom 5)

/-! ## C: qualified structural member calls -/

#guard valueIs (run [] [dot (dot (.resolve "Box") "Step" (some [.num 0])) "while" none]) (.atom 3)
#guard valueIs (run [] [callN "while" [dot (.resolve "Box") "Step" (some [.num 0])]]) (.atom 3)
#guard valueIs (run [] [dot (.call (dot (.resolve "Box") "Step" none) [.num 0]) "while" none]) (.atom 3)
#guard valueIs (run [] [dot (dot (.resolve "Box") "G" (some [.num 1])) "repeat" (some [.num 2])]) (.atom 100)

/-! ## E: ordinary user META consumers; plain/dot correspondence of the extension route -/

#guard valueIs (run [] [callN "Inspect" [dot (.resolve "Box") "G" (some [.num 1])]]) (.atom 1)
#guard valueIs (run [] [callN "Inspect" [dot (.num 5) "Add" (some [.num 1])]]) (.atom 2)
#guard valueIs (run [] [callN "Inspect" [callN "Add" [.num 5, .num 1]]]) (.atom 2)
#guard valueIs (run [("R", alg [] [] [] [callN "Capture" [callN "Inc" [.num 5]]])]
  [callN "Inspect" [dot (.resolve "R") "Algorithm" (some [.num 4, .num 5])]]) (.atom 2)
-- The extension route's callee is the fallback and its supply the receiver first: `R.Algorithm(10, 20)`
-- calls `Add` afresh, `R.Invoke()` re-runs `Add(3, 4)`.
#guard valueIs (run [("R", alg [] [] [] [callN "Capture" [dot (.num 3) "Add" (some [.num 4])]])]
  [invoke (.resolve "R"), dot (.resolve "R") "Algorithm" (some [.num 10, .num 20])])
  (.sequenceValue [.atom 7, .atom 30])
-- A declared member named `Algorithm` wins: it is an ordinary member invocation.
#guard valueIs (run [] [callN "Inspect" [dot (.resolve "Box4") "Algorithm" (some [.num 2])],
  invoke (callN "Capture" [dot (.resolve "Box4") "Algorithm" (some [.num 2])])])
  (.sequenceValue [.atom 1, .atom 200])

/-! ## S: shared cells — the rebuilt invocation transports the ORIGINAL argument cells -/

-- `Op(Inc(7))` captures `Inc(7)`, rebuilds `op.Algorithm(op.Arguments*)` and captures THAT; invoking
-- it runs `Inc` over the original cell of `7`: one cell of `7` in the whole heap.
#guard valueIs (run [("R", alg [] [] [] [callN "Op" [callN "Inc" [.num 7]]])] [invoke (.resolve "R")]) (.atom 8)
#guard cellsOf (heap [("R", alg [] [] [] [callN "Op" [callN "Inc" [.num 7]]])]
  [invoke (.resolve "R"), invoke (.resolve "R")]) (.num 7) == 1

/-! ## N: negative controls -/

-- D6: no implicit provenance.
#guard isMetaRefusal (run [] [dot (.resolve "Start") "while" none])
#guard isMetaRefusal (run [] [callN "while" [.resolve "Start"]])
-- A computed value and a bare member path are not invocations.
#guard isMetaRefusal (run [] [callN "Inspect" [add (.num 1) (.num 2)]])
#guard isMetaRefusal (run [] [callN "Inspect" [dot (.resolve "Box") "G" none]])
-- A non-callable intrinsic route is refused when the reference's supply is observed (D-1A).
#guard isInvocationRefusal (run [] [callN "Inspect" [dot (.num 5) "string" (some [])]])
-- A route failure keeps its kind (a branch-only member).
#guard isLocalOnly (run [("Fam", .conditional none [] [
      ⟨.litInt 0, algPrivate [] [] [("Q", alg ["x"] [] [] [.param "x"])] [.num 0]⟩,
      ⟨.bind "n", alg [] [] [] [.param "n"]⟩])]
  [callN "Inspect" [dot (.resolve "Fam") "Q" (some [.num 1])]])
-- A self-referential rebuilt invocation is a demand cycle, never a hang.
#guard isCycle (run [("R", alg [] [] [] [callN "Capture" [dot (.resolve "R") "Algorithm" (some [.num 1])]])]
  [invoke (.resolve "R")])

/-! ## D: settled decisions and production cases -/

-- D-1A: capture of an intrinsic-shaped invocation is syntactic and inert — an unused META
-- parameter admits it, and reference identity needs no route.
#guard valueIs (run [] [callN "Ignore" [dot (.num 5) "string" (some [])]]) (.atom 0)
#guard valueIs (run [] [callN "Ignore" [invoke (callN "Capture" [callN "Inc" [.num 1]])]]) (.atom 0)
#guard valueIs (run [("R", alg [] [] [] [callN "Capture" [dot (.num 5) "string" (some [])]])]
  [eq (.resolve "R") (.resolve "R")]) (.bool true)
-- D-1A: every route-dependent reference operation refuses the intrinsic route with its own
-- description: invocation, the callee projection, argument-supply observation, loop setup.
#guard isInvocationRefusal (run [("R", alg [] [] [] [callN "Capture" [dot (.num 5) "string" (some [])]])]
  [invoke (.resolve "R")])
#guard isInvocationRefusal (run [("R", alg [] [] [] [callN "Capture" [dot (.num 5) "string" (some [])]])]
  [dot (.resolve "R") "Algorithm" (some [.num 1])])
#guard isInvocationRefusal (run [("R", alg [] [] [] [callN "Capture" [dot (.num 5) "string" (some [])]])]
  [dot (argsOf (.resolve "R")) "count" none])
#guard isInvocationRefusal (run [] [dot (dot (.num 5) "string" (some [])) "repeat" (some [.num 1])])
#guard isInvocationRefusal (run [] [callN "while" [invoke (callN "Capture" [callN "Step" [.num 0]])]])
-- D-1A: the captured intrinsic's ORIGINAL VALUE is the ordinary intrinsic evaluation.
#guard valueIs (run [] [callN "Id" [dot (.num 5) "string" (some [])]]) (.str "5")
#guard valueIs (run [] [callN "Id" [invoke (callN "Capture" [callN "Inc" [.num 1]])]]) (.atom 2)
-- D-2A: an explicit argument list makes the invocation; an argumentless edge never does.
#guard valueIs (run [] [callN "Inspect" [dot (.num 5) "Inc" (some [])]]) (.atom 1)
#guard isMetaRefusal (run [] [callN "Inspect" [dot (.num 5) "Inc" none]])
#guard valueIs (run [] [callN "Inspect" [dot (.resolve "Box") "V" (some [])]]) (.atom 0)
#guard isMetaRefusal (run [] [callN "Inspect" [dot (.resolve "Box") "V" none]])
#guard valueIs (run [] [invoke (callN "Capture" [dot (.resolve "Box") "V" (some [])])]) (.atom 7)
-- D-5: the extension receiver is the first supplied argument, and the callee is the fallback.
#guard valueIs (run [("R", alg [] [] [] [callN "Capture" [dot (.num 5) "Add" (some [.num 1])]])]
  [dot (argsOf (.resolve "R")) "count" none, .index (argsOf (.resolve "R")) [.num 0]])
  (.sequenceValue [.atom 2, .atom 5])
#guard isArityMismatch (run [("R", alg [] [] [] [callN "Capture" [dot (.num 5) "Add" (some [.num 1])]])]
  [dot (.resolve "R") "Algorithm" (some [.num 7])])
-- A structural member's receiver is NOT part of the supply.
#guard valueIs (run [("R", alg [] [] [] [callN "Capture" [dot (.resolve "Box") "G" (some [.num 2])]])]
  [dot (argsOf (.resolve "R")) "count" none, dot (.resolve "R") "Algorithm" (some [.num 3]), invoke (.resolve "R")])
  (.sequenceValue [.atom 1, .atom 30, .atom 20])
-- D-3: the `.Algorithm` route's receiver `Mk(1)` is ONE retained cell for the plan, shared by its
-- VALUE, every invocation and its callee projection.
#guard valueIs (run [("R", alg [] [] [] [callN "Capture" [dot (callN "Mk" [.num 1]) "Algorithm" (some [.num 3])]])]
  [invoke (.resolve "R"), dot (.resolve "R") "Algorithm" (some [.num 4]), invoke (.resolve "R")])
  (.sequenceValue [.atom 4, .atom 5, .atom 4])
#guard cellsOf (heap [("R", alg [] [] [] [callN "Capture" [dot (callN "Mk" [.num 1]) "Algorithm" (some [.num 3])]])]
  [invoke (.resolve "R"), dot (.resolve "R") "Algorithm" (some [.num 4]), invoke (.resolve "R")])
  (callN "Mk" [.num 1]) == 1
-- Distinct written invocations are distinct plans, even when spelled alike (CR-3).
#guard valueIs (run [("Two", algWithParameters [metaParam "a", metaParam "b"] [] [] [eq (.param "a") (.param "b")])]
  [callN "Two" [dot (.resolve "Box") "G" (some [.num 1]), dot (.resolve "Box") "G" (some [.num 1])]])
  (.bool false)
-- The grouped member callee `(Box.G)(2)` is a call-form plan over the member path.
#guard valueIs (run [] [callN "Inspect" [.call (dot (.resolve "Box") "G" none) [.num 2]],
  invoke (callN "Capture" [.call (dot (.resolve "Box") "G" none) [.num 2]])])
  (.sequenceValue [.atom 1, .atom 20])


/-! ## G: dispatch names on the `.Algorithm` route (META-S3-4-DIAG, October 20 2026)

A fresh call of a captured callee is named by the CAPTURED plan's effective callee — whether it runs
as the ordinary intrinsic (a root row: no plan) or as a generalized invocation plan (a supplied
argument, `NeedPlan.executeAlong` naming it by `NeedPlan.dispatchName`). The surrounding call or
dot-call context still names the written `R.Algorithm`. Before this date the planned rows reported
`noMatchingBranch "R.Algorithm"` (resp. `"Q.Algorithm"`, `"E.Algorithm"`). The C# twin is
`InvocationRoute/AlgorithmRouteDiagnosticNameTests`. -/

/-- `F(0) = 0`; `G(x, 0) = x`. -/
def zeroFamily : Algorithm := .conditional none [] [⟨.litInt 0, alg [] [] [] [.num 0]⟩]
def pairFamily : Algorithm := .conditional none [] [⟨.sequenceValue [.bind "x", .litInt 0], alg [] [] [] [.param "x"]⟩]

/-- `F`, `G`, `Sq(x) = x * x`, `Mk2(f) = Capture(f(1))`, `Pack = { F(0) = 0 }`,
    `Box5 = { Algorithm(0) = 0 }`, `R = Capture(F(0))`, `Q = Capture(Pack.F(0))`,
    `E = Capture(5.G(0))`, `S = Capture(Sq(2))`, `X = Mk2(5)`, `R2 = Capture(R.Algorithm(0))`. -/
def diagDecls : List (Ident × Algorithm) :=
  [("F", zeroFamily), ("G", pairFamily),
   ("Sq", alg ["x"] [] [] [mul (.param "x") (.param "x")]),
   ("Mk2", alg ["f"] [] [] [callN "Capture" [.call (.param "f") [.num 1]]]),
   ("Pack", algPrivate [] [] [("F", zeroFamily)] []),
   ("Box5", algPrivate [] [] [("Algorithm", zeroFamily)] []),
   ("R", alg [] [] [] [callN "Capture" [callN "F" [.num 0]]]),
   ("Q", alg [] [] [] [callN "Capture" [dot (.resolve "Pack") "F" (some [.num 0])]]),
   ("E", alg [] [] [] [callN "Capture" [dot (.num 5) "G" (some [.num 0])]]),
   ("S", alg [] [] [] [callN "Capture" [callN "Sq" [.num 2]]]),
   ("X", alg [] [] [] [callN "Mk2" [.num 5]]),
   ("R2", alg [] [] [] [callN "Capture" [dot (.resolve "R") "Algorithm" (some [.num 0])]])]

/-- The context chain of a failure and its innermost payload. -/
def chain : Error → List String
  | .withContext c inner => c :: chain inner
  | .noMatchingBranch n => [s!"noMatchingBranch {n}"]
  | .arityMismatch e a => [s!"arityMismatch {e} {a}"]
  | .notAnAlgorithm d => [s!"notAnAlgorithm {d}"]
  | .illegalInEval d => [s!"illegalInEval {d}"]
  | _ => ["other"]

def failsWith (r : Except Error Result) (expected : List String) : Bool :=
  match r with | .error e => chain e == expected | .ok _ => false

def diag (rows : List Expr) : Except Error Result := run diagDecls rows

def algoCall (receiver : Expr) (args : List Expr) : Expr := dot receiver "Algorithm" (some args)
def grouped (receiver : Expr) (args : List Expr) : Expr := .call (dot receiver "Algorithm" none) args
def inId (e : Expr) : Expr := callN "Id" [e]

def ctxR : String := "while evaluating dotCall .Algorithm of R"
def ctxId : String := "while evaluating call to Id"

-- Ordinary and planned `.Algorithm` invocations name the captured `F`.
#guard failsWith (diag [algoCall (.resolve "R") [.num 1]]) [ctxR, "noMatchingBranch F"]
#guard failsWith (diag [inId (algoCall (.resolve "R") [.num 1])]) [ctxId, ctxR, "noMatchingBranch F"]
-- Grouped `(R.Algorithm)(1)`, ordinary and planned: the call context names the written callee.
#guard failsWith (diag [grouped (.resolve "R") [.num 1]])
  ["while evaluating call to R.Algorithm", "noMatchingBranch F"]
#guard failsWith (diag [inId (grouped (.resolve "R") [.num 1])])
  [ctxId, "while evaluating call to R.Algorithm", "noMatchingBranch F"]
-- A qualified captured callee keeps its member path.
#guard failsWith (diag [algoCall (.resolve "Q") [.num 1]])
  ["while evaluating dotCall .Algorithm of Q", "noMatchingBranch Pack.F"]
#guard failsWith (diag [inId (algoCall (.resolve "Q") [.num 1])])
  [ctxId, "while evaluating dotCall .Algorithm of Q", "noMatchingBranch Pack.F"]
-- A captured extension invocation `5.G(0)` names its effective callee, the fallback `G`.
#guard failsWith (diag [algoCall (.resolve "E") [.num 1, .num 1]])
  ["while evaluating dotCall .Algorithm of E", "noMatchingBranch G"]
#guard failsWith (diag [inId (algoCall (.resolve "E") [.num 1, .num 1])])
  [ctxId, "while evaluating dotCall .Algorithm of E", "noMatchingBranch G"]
-- An arity failure carries no callee name: unchanged, ordinary and planned.
#guard failsWith (diag [algoCall (.resolve "S") [.num 1, .num 2]])
  ["while evaluating dotCall .Algorithm of S", "arityMismatch 1 2"]
#guard failsWith (diag [inId (algoCall (.resolve "S") [.num 1, .num 2])])
  [ctxId, "while evaluating dotCall .Algorithm of S", "arityMismatch 1 2"]
-- A captured callee without callable identity is the projection's own failure, never a name error.
#guard failsWith (diag [algoCall (.resolve "X") [.num 1]])
  ["while evaluating dotCall .Algorithm of X", "notAnAlgorithm captured callee"]
#guard failsWith (diag [inId (algoCall (.resolve "X") [.num 1])])
  [ctxId, "while evaluating dotCall .Algorithm of X", "notAnAlgorithm captured callee"]
-- A callee's runtime CALLABLE projection can itself fail: `Held = Mk2(Bad.Algorithm)` captures
-- `f(1)` without projecting `f`. Its later projection keeps `Bad`'s original failure and context,
-- rather than treating it as missing identity or trying to obtain a diagnostic name first.
def failedProjectionDecls : List (Ident × Algorithm) := diagDecls ++
  [("Bad", alg [] [] [] [callN "min" [.listLiteral []]]),
   ("Held", alg [] [] [] [callN "Mk2" [dot (.resolve "Bad") "Algorithm" none]])]

def failedProjection (row : Expr) : Except Error Result := run failedProjectionDecls [row]

#guard failsWith (failedProjection (algoCall (.resolve "Held") [.num 1]))
  ["while evaluating dotCall .Algorithm of Held", "while evaluating call to min",
   "illegalInEval min requires a non-empty collection"]
#guard failsWith (failedProjection (inId (algoCall (.resolve "Held") [.num 1])))
  [ctxId, "while evaluating dotCall .Algorithm of Held", "while evaluating call to min",
   "illegalInEval min requires a non-empty collection"]
#guard failsWith (failedProjection (grouped (.resolve "Held") [.num 1]))
  ["while evaluating call to Held.Algorithm", "while evaluating call to min",
   "illegalInEval min requires a non-empty collection"]
#guard failsWith (failedProjection (inId (grouped (.resolve "Held") [.num 1])))
  [ctxId, "while evaluating call to Held.Algorithm", "while evaluating call to min",
   "illegalInEval min requires a non-empty collection"]
-- A declared member `Algorithm` is the member route, outside this correction: the ordinary member
-- call names the member, the planned member route its argumentless path (unchanged here; C# names the
-- member in both, a separate member-route naming difference recorded in SEMANTIC-ALIGNMENT).
#guard failsWith (diag [algoCall (.resolve "Box5") [.num 1]])
  ["while evaluating dotCall .Algorithm of Box5", "noMatchingBranch Algorithm"]
#guard failsWith (diag [inId (algoCall (.resolve "Box5") [.num 1])])
  [ctxId, "while evaluating dotCall .Algorithm of Box5", "noMatchingBranch Box5.Algorithm"]
-- Nested reconstructed META invocations: invoking the plan `op.Algorithm(op.Arguments*)` that `Op`
-- captured (a plan on the `.Algorithm` route) names the callee `op` captured; projecting a captured
-- `.Algorithm` invocation again names that plan's own written callee, never chased further.
#guard failsWith (diag [invoke (callN "Op" [callN "F" [.num 1]])])
  ["while evaluating dotCall .Invoke of (call)", "while evaluating dotCall .Algorithm of op", "noMatchingBranch F"]
#guard failsWith (diag [inId (algoCall (callN "Op" [callN "F" [.num 0]]) [.num 1])])
  [ctxId, "while evaluating dotCall .Algorithm of (call)", "noMatchingBranch op.Algorithm"]
#guard failsWith (diag [algoCall (.resolve "R2") [.num 1]])
  ["while evaluating dotCall .Algorithm of R2", "noMatchingBranch R.Algorithm"]
#guard failsWith (diag [inId (algoCall (.resolve "R2") [.num 1])])
  [ctxId, "while evaluating dotCall .Algorithm of R2", "noMatchingBranch R.Algorithm"]
-- Successful controls: the name changes no value.
#guard valueIs (diag [algoCall (.resolve "R") [.num 0], inId (algoCall (.resolve "R") [.num 0]),
    grouped (.resolve "R") [.num 0], inId (grouped (.resolve "R") [.num 0])])
  (.sequenceValue [.atom 0, .atom 0, .atom 0, .atom 0])
#guard valueIs (diag [inId (algoCall (.resolve "Q") [.num 0]), inId (algoCall (.resolve "E") [.num 7, .num 0]),
    inId (algoCall (.resolve "S") [.num 3]), inId (algoCall (.resolve "Box5") [.num 0])])
  (.sequenceValue [.atom 0, .atom 7, .atom 9, .atom 0])
#guard valueIs (diag [invoke (callN "Op" [callN "F" [.num 0]]), invoke (callN "Op" [callN "Sq" [.num 4]]),
    inId (algoCall (.resolve "S") [spreadArgs (.resolve "S")])])
  (.sequenceValue [.atom 0, .atom 16, .atom 4])

/-- The heap after a planned `Id(R.Algorithm(0))`: the plan cell of the written `R.Algorithm(0)`. -/
def plannedHeap : Array NeedCell := heap diagDecls [inId (algoCall (.resolve "R") [.num 0])]

def plannedAddress? : Option Nat :=
  (List.range plannedHeap.size).find? fun a =>
    match plannedHeap[a]? with
    | some { suspension := .expression e _ _, .. } => reprStr e == reprStr (algoCall (.resolve "R") [.num 0])
    | _ => false

-- On the final heap of a planned run, the plan's route is `.Algorithm`, its dispatch name is the
-- captured `F` (`dispatchNameIn`), and the ordinary intrinsic's name of the decoded plan
-- (`calleeNameIn?`) is the same; the written link is what the former rule used.
#guard match plannedAddress? with
  | some a =>
    (plannedHeap[a]?.bind NeedCell.route) == some .algorithm &&
    (match NeedPlan.shapeAt? plannedHeap a with
     | some shape =>
       NeedPlan.dispatchNameIn plannedHeap a (NeedPlan.effective shape .algorithm) .algorithm == "F" &&
       openExprName (NeedPlan.effective shape .algorithm).callee == "R.Algorithm"
     | none => false) &&
    (match ((plannedHeap[a]?).bind NeedCell.callee).bind (NeedPlan.linkedPlanIn? plannedHeap) with
     | some p => NeedPlan.calleeNameIn? plannedHeap p == some "F"
     | none => false)
  | none => false

end KatLang.InvocationRouteGuards
