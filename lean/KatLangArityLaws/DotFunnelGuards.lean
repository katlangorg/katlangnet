import KatLangArityLaws.DotFunnel

open KatLang KatLang.DotFunnel

/-!
# Q-66 dot-funnel guards: the extension dot call against the written call

Executable evidence for `KatLangArityLaws/DotFunnel.lean` on concrete programs, run through the
authoritative `runResult` / `runResultWithState` and, for the full-state comparison, through the
production `evalCounted` from one entry state:

* a value receiver with a user callee: `5.Inc` and `Inc(5)` have the same value and allocate the
  same number of heap cells;
* a value receiver with a prelude builtin from the empty state: `[1, 2].count` and `count([1, 2])`
  have the SAME outcome and the SAME final state, both run from the empty state (the theorem relates
  the written call from the probe's exit state; here both spellings coincide from one entry state);
* a failing callee: both frames are visible and the inner error is the same error;
* the loop dot spellings `Inc(0).repeat(3)` and `Step(0).while` against `repeat(Inc(0), 3)` and
  `while(Step(0))`;
* the route premise: `selectDotEdge` of a value receiver is the extension miss for a user name and
  for `repeat`, and is NOT for the intrinsic names;
* the NEGATIVE CONTROL that motivates the qualification: a receiver that DECLARES `F` takes the
  member route (DOT-01, member first), so `Box.F(1)` is not `F(Box, 1)`.
-/

namespace KatLang.DotFunnelGuards

def add (a b : Expr) : Expr := .binary .add a b
def lt (a b : Expr) : Expr := .comparison a [⟨.lt, b⟩]
def callN (f : Ident) (args : List Expr) : Expr := .call (.resolve f) args
def dot (receiver : Expr) (name : Ident) (args : Option (List Expr)) : Expr := Expr.dotCall receiver name args

/-- `Inc(x) = x + 1`, `Bad(x) = x + Missing`, `Step(x) = x + 1, x < 3`,
    `Box = { F(y) = y + 100 }`, `F(b, y) = 7`, `Sub(a, b) = a - b`. -/
def decls : List (Ident × Algorithm) :=
  [("Inc", alg ["x"] [] [] [add (.param "x") (.num 1)]),
   ("Bad", alg ["x"] [] [] [add (.param "x") (.resolve "Missing")]),
   ("Step", alg ["x"] [] [] [add (.param "x") (.num 1), lt (.param "x") (.num 3)]),
   ("Box", algPrivate [] [] [("F", alg ["y"] [] [] [add (.param "y") (.num 100)])] []),
   ("F", alg ["b", "y"] [] [] [.num 7]),
   ("Sub", alg ["a", "b"] [] [] [.binary .sub (.param "a") (.param "b")])]

def program (rows : List Expr) : Expr := .algorithmExpr (algPrivate [] [] decls rows)

def run (rows : List Expr) : Except Error Result := runResult (program rows)

def heapSize (rows : List Expr) : Nat :=
  match runResultWithState (program rows) with
  | .ok (_, s) => s.needs.size
  | .error _ => 0

def valueIs (r : Except Error Result) (v : Result) : Bool :=
  match r with | .ok value => value == v | .error _ => false

/-- The outer frame and the inner error of a failed run. -/
def frameOf (r : Except Error Result) : Option (String × String) :=
  match r with
  | .error (.withContext frame inner) => some (frame, reprStr inner)
  | _ => none

/-! ## A value receiver and a user callee: `5.Inc` is `Inc(5)` -/

#guard valueIs (run [dot (.num 5) "Inc" none]) (.atom 6)
#guard valueIs (run [callN "Inc" [.num 5]]) (.atom 6)
#guard heapSize [dot (.num 5) "Inc" none] == heapSize [callN "Inc" [.num 5]]
-- A computed value receiver is the ordinary first argument too.
#guard valueIs (run [dot (add (.num 2) (.num 3)) "Inc" none]) (.atom 6)
-- With extra arguments the receiver LEADS: `10.Sub(3)` is `Sub(10, 3)` = 7, never `Sub(3, 10)`.
#guard valueIs (run [dot (.num 10) "Sub" (some [.num 3])]) (.atom 7)
#guard valueIs (run [callN "Sub" [.num 10, .num 3]]) (.atom 7)
#guard heapSize [dot (.num 10) "Sub" (some [.num 3])] == heapSize [callN "Sub" [.num 10, .num 3]]

/-! ## The same outcome AND the same final state, from one entry state -/

def ctx0 : EvalCtx := { callStack := [preludeAlg] }

def dotCount : Expr := dot (.listLiteral [.num 1, .num 2]) "count" none
def writtenCount : Expr := callN "count" [.listLiteral [.num 1, .num 2]]

#guard reprStr ((evalCounted dotCount ctx0 []).runState {}) ==
  reprStr ((evalCounted writtenCount ctx0 []).runState {})
#guard match (evalCounted dotCount ctx0 []).runState {} with
  | (.ok (v, _), _) => v == .atom 2
  | _ => false

/-! ## A failing callee: both frames visible, one inner error -/

#guard frameOf (run [dot (.num 5) "Bad" none]) ==
  some (CtxMsg.dotCall (.num 5) "Bad", reprStr (Error.unknownName "Missing"))
#guard frameOf (run [callN "Bad" [.num 5]]) ==
  some (CtxMsg.call (.resolve "Bad"), reprStr (Error.unknownName "Missing"))
#guard (frameOf (run [dot (.num 5) "Bad" none])).map Prod.snd ==
  (frameOf (run [callN "Bad" [.num 5]])).map Prod.snd
-- The two frames are different strings: the funnel relates the errors, it does not equate them.
#guard CtxMsg.dotCall (.num 5) "Bad" != CtxMsg.call (.resolve "Bad")

/-! ## Loop dot spellings (E-13 through `dot_repeat_funnel` / `dot_while_funnel`) -/

#guard valueIs (run [dot (callN "Inc" [.num 0]) "repeat" (some [.num 3])]) (.atom 3)
#guard valueIs (run [callN "repeat" [callN "Inc" [.num 0], .num 3]]) (.atom 3)
#guard heapSize [dot (callN "Inc" [.num 0]) "repeat" (some [.num 3])] ==
  heapSize [callN "repeat" [callN "Inc" [.num 0], .num 3]]
#guard valueIs (run [dot (callN "Step" [.num 0]) "while" none]) (.atom 3)
#guard valueIs (run [callN "while" [callN "Step" [.num 0]]]) (.atom 3)
#guard heapSize [dot (callN "Step" [.num 0]) "while" none] == heapSize [callN "while" [callN "Step" [.num 0]]]

/-! ## The route premise is computable and discriminating -/

def isExtensionMiss (r : Except Error DotSelection) : Bool :=
  match r with | .ok (.miss .extension) => true | _ => false

def isMember (r : Except Error DotSelection) : Bool :=
  match r with | .ok (.member _ _) => true | _ => false

-- A value receiver (`none`) misses structurally; a user name and `repeat` take the extension route.
#guard isExtensionMiss (selectDotEdge ctx0 (.num 5) "Inc" none)
#guard isExtensionMiss (selectDotEdge ctx0 (.num 5) "repeat" none)
-- The intrinsic names are their own miss routes: outside the funnel's premise.
#guard !isExtensionMiss (selectDotEdge ctx0 (.num 5) "string" none)
#guard !isExtensionMiss (selectDotEdge ctx0 (.num 5) "Invoke" none)
#guard !isExtensionMiss (selectDotEdge ctx0 (.num 5) "Arguments" none)
#guard !isExtensionMiss (selectDotEdge ctx0 (.num 5) "Algorithm" none)

/-! ## NEGATIVE CONTROL: a receiver that declares `F` is not the written call (DOT-01) -/

def boxAlg : Algorithm := algPrivate [] [] [("F", alg ["y"] [] [] [add (.param "y") (.num 100)])] []

-- The receiver's typed identity declares `F`: the member route is selected, not the miss.
#guard isMember (selectDotEdge ctx0 (.resolve "Box") "F" (some boxAlg))
#guard !isExtensionMiss (selectDotEdge ctx0 (.resolve "Box") "F" (some boxAlg))
-- So `Box.F(1)` is the member call (101), while the written `F(Box, 1)` is the top-level `F` (7).
#guard valueIs (run [dot (.resolve "Box") "F" (some [.num 1])]) (.atom 101)
#guard valueIs (run [callN "F" [.resolve "Box", .num 1]]) (.atom 7)
#guard reprStr (run [dot (.resolve "Box") "F" (some [.num 1])]) != reprStr (run [callN "F" [.resolve "Box", .num 1]])

end KatLang.DotFunnelGuards
