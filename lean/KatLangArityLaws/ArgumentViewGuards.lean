import KatLangArityLaws.ArgumentView
import KatLangArityLaws.CallReferenceGuards

open KatLang KatLang.CallReferenceGuards

/-!
# CallReference S2 guards: `R.Arguments` on whole programs

Every guard runs a whole program through the authoritative `runResult` / `runResultWithState`
(the dot route's `Arguments` arm, the `.index` arm, sequence-builtin binding, supply formation
with `evalSupplySpread`, and the run result boundary). As in `CallReferenceGuards.lean`, heap
observations count production `NeedCell`s: an `x * x` cell is one execution of `Sq`, a `Sq(5)`
cell is one prepared argument of the captured call (so ZERO such cells means the captured call's
supply was never prepared), and Ready `1` cells count executions of the spread `Pair()*`.
Failure-order guards use arguments whose preparation fails (`Boom()*`) to show which phase ran.
These guards are executable evidence for the source facts `ArgumentView.lean` cannot reach.
-/

namespace KatLang.ArgumentViewGuards

def callF (f : Ident) (as : List Expr) : Expr := .call (.resolve f) as
def args (r : Expr) : Expr := .dotCall r "Arguments" none
def dot (r : Expr) (name : Ident) : Expr := .dotCall r name none
def R : Expr := .resolve "R"
def sq (n : Int) : Expr := callF "Sq" [.num n]

/-- Extra declarations: `First(x, y) = x`, `Mul(x, y) = x * y`, `Boom() = 1 / 0, 2`,
    `Zero() = 7`, `Box2 = { Arguments = 3 }`, `Arguments(r) = r + 1`, `Pick(c, a, b) = 0`. -/
def extra : List (Ident × Algorithm) :=
  [("First", alg ["x", "y"] [] [] [.param "x"]),
   ("Mul", alg ["x", "y"] [] [] [mul (.param "x") (.param "y")]),
   ("Boom", alg [] [] [] [.binary .div (.num 1) (.num 0), .num 2]),
   ("Zero", alg [] [] [] [.num 7]),
   ("Box2", algPrivate [] [] [("Arguments", alg [] [] [] [.num 3])] []),
   ("Arguments", alg ["r"] [] [] [add (.param "r") (.num 1)]),
   ("Pick", alg ["c", "a", "b"] [] [] [.num 0])]

def withR (captured : Expr) (more : List (Ident × Algorithm) := []) : List (Ident × Algorithm) :=
  extra ++ [("R", alg [] [] [] [callF "Capture" [captured]])] ++ more

def run (captured : Expr) (rows : List Expr) (more : List (Ident × Algorithm) := []) :
    Except Error Result :=
  runResult (program (withR captured more) rows)

def heap (captured : Expr) (rows : List Expr) (more : List (Ident × Algorithm) := []) : Array NeedCell :=
  finalHeap (program (withR captured more) rows)

def isBadIndex (r : Except Error Result) : Bool :=
  match r with
  | .error e => match innermost e with | .badIndex => true | _ => false
  | .ok _ => false

def isCycle (r : Except Error Result) : Bool :=
  match r with
  | .error e => match innermost e with | .demandCycle => true | _ => false
  | .ok _ => false

def add1020 : Expr := callF "Add" [.num 10, .num 20]
def addSq : Expr := callF "Add" [sq 5, sq 6]

/-! ## The brief's example and the view's identity -/

#guard valueIs (run add1020 [dot (args R) "count"]) (.atom 2)
#guard valueIs (run add1020 [callF "count" [args R]]) (.atom 2)
#guard valueIs (run add1020 [.index (args R) [.num 0]]) (.atom 10)
#guard valueIs (run add1020 [.index (args R) [.num 1]]) (.atom 20)
#guard valueIs (run add1020 [.index (args R) [.num 0, .num 1]]) (.sequenceValue [.atom 10, .atom 20])
#guard valueIs (run add1020 [.index (args R) [.num 1, .num 1]]) (.sequenceValue [.atom 20, .atom 20])
#guard valueIs (run add1020 [invoke R]) (.atom 30)
#guard valueIs (run add1020 [dot (args R) "first"]) (.atom 10)
#guard valueIs (run add1020 [callF "last" [args R]]) (.atom 20)
-- One view per reference (stable identity); never the reference itself.
#guard valueIs (run add1020 [.compare .eq (args R) (args R)]) (.bool true)
#guard valueIs (run add1020 [.compare .eq R (args R)]) (.bool false)
-- A stored view (`A = R.Arguments`) and a view read after the original VALUE completed.
#guard valueIs (run add1020 [.index (.resolve "A") [.num 1]] [("A", alg [] [] [] [args R])]) (.atom 20)
#guard valueIs (run add1020 [add (invoke R) (.index (args R) [.num 0])]) (.atom 40)
-- VALUE before META: `Use`-style forwarding keeps the original arguments.
#guard valueIs (runResult (program extra
    [.index (args (callF "Fwd2" [add1020])) [.num 1]])) (.atom 20)

/-! ## Laziness: obtaining, counting, selecting -/

-- Obtaining the view prepares nothing (no `Sq(5)` argument cell exists).
#guard cellsOf (heap addSq [.compare .eq (args R) (args R)]) (sq 5) == 0
-- `count` prepares the supply (one `Sq(5)` cell) but executes no `Sq` (no `x * x` cell).
#guard valueIs (run addSq [dot (args R) "count"]) (.atom 2)
#guard cellsOf (heap addSq [dot (args R) "count"]) (sq 5) == 1
#guard cellsOf (heap addSq [dot (args R) "count"]) xx == 0
-- Selecting demands only the selected cell, and a repeated selection reuses it.
#guard valueIs (run addSq [.index (args R) [.num 0]]) (.atom 25)
#guard cellsOf (heap addSq [.index (args R) [.num 0]]) xx == 1
#guard valueIs (run addSq [add (.index (args R) [.num 0]) (.index (args R) [.num 0])]) (.atom 50)
#guard cellsOf (heap addSq [add (.index (args R) [.num 0]) (.index (args R) [.num 0])]) xx == 1
#guard cellsOf (heap addSq [add (.index (args R) [.num 0]) (.index (args R) [.num 1])]) xx == 2
-- `first`/`last` demand one cell each.
#guard cellsOf (heap addSq [dot (args R) "last"]) xx == 1
-- An argument failure is the selected cell's own, and only when it is selected.
#guard valueIs (run (callF "Add" [.num 5, .binary .div (.num 1) (.num 0)]) [.index (args R) [.num 0]]) (.atom 5)
#guard isDivByZero (run (callF "Add" [.num 5, .binary .div (.num 1) (.num 0)]) [.index (args R) [.num 1]])
#guard valueIs (run (callF "Add" [.num 5, .binary .div (.num 1) (.num 0)]) [dot (args R) "count"]) (.atom 2)
-- A nested sequence argument is selected whole (selection is a value boundary).
#guard valueIs (run (callF "Id" [.capture [.num 1, .num 2]]) [.index (args R) [.num 0]])
  (.sequenceValue [.atom 1, .atom 2])
-- Zero arguments: count 0, no first position.
#guard valueIs (run (callF "Zero" []) [dot (args R) "count"]) (.atom 0)
#guard isBadIndex (run (callF "Zero" []) [dot (args R) "first"])
#guard isBadIndex (run add1020 [.index (args R) [.num 2]])

/-! ## Selection formation and validation precedence (J9) -/

-- `Boom()*` fails during preparation, so the outcome shows whether preparation ran.
def boomed : Expr := callF "Add" [.sequenceSpread (callF "Boom" [])]
-- The empty selection reads nothing.
#guard valueIs (run boomed [.index (args R) []]) (.sequenceValue [])
-- A non-number and a negative selector fail before preparation …
#guard isTypeMismatchAny (run boomed [.index (args R) [.boolLiteral true]])
#guard isBadIndex (run boomed [.index (args R) [.unary .minus (.num 1)]])
-- … while a valid index needs the cardinality: preparation runs, and its failure is sticky.
#guard isDivByZero (run boomed [.index (args R) [.num 0]])
#guard isDivByZero (run boomed [dot (args R) "count"])
#guard isDivByZero (run boomed [invoke R])
-- The view never dispatches: a captured call with an arity error has a countable, selectable supply,
-- while its execution reports the target's ordinary arity error.
#guard valueIs (run (callF "Add" [.num 1, .num 2, .num 3]) [dot (args R) "count"]) (.atom 3)
#guard valueIs (run (callF "Add" [.num 1, .num 2, .num 3]) [.index (args R) [.num 2]]) (.atom 3)
#guard isArity (run (callF "Add" [.num 1, .num 2, .num 3]) [invoke R]) 2 3
-- Count includes explicit spreads; the spread runs once for every observer.
def pairs : Expr := callF "Add" [.sequenceSpread (callF "Pair" [])]
#guard valueIs (run pairs [dot (args R) "count"]) (.atom 2)
#guard valueIs (run pairs [add (dot (args R) "count") (add (invoke R) (.index (args R) [.num 1]))]) (.atom 7)
#guard readyCellsOf (heap pairs [add (dot (args R) "count") (add (invoke R) (.index (args R) [.num 1]))]) (.atom 1) == 1

/-! ## Cell-preserving spread -/

#guard valueIs (run add1020 [callF "Mul" [.sequenceSpread (args R)]]) (.atom 200)
#guard valueIs (run add1020 [add (callF "Mul" [.sequenceSpread (args R)]) (invoke R)]) (.atom 230)
-- The second argument stays undemanded: no DivisionByZero.
#guard valueIs (run (callF "Add" [.num 5, .binary .div (.num 1) (.num 0)]) [callF "First" [.sequenceSpread (args R)]]) (.atom 5)
-- CALLABLE arguments survive transport: `Ap(R.Arguments*)` with `R = Capture(Ap(Sq, 5))`.
#guard valueIs (run (callF "Ap" [.resolve "Sq", .num 5]) [callF "Ap" [.sequenceSpread (args R)]]) (.atom 25)
-- The destination and the original share memoized cells: `Sq(5)`, `Sq(6)` each run once.
#guard valueIs (run addSq [add (callF "Add" [.sequenceSpread (args R)]) (invoke R)]) (.atom 122)
#guard cellsOf (heap addSq [add (callF "Add" [.sequenceSpread (args R)]) (invoke R)]) xx == 2
#guard cellsOf (heap addSq [add (callF "Add" [.sequenceSpread (args R)]) (invoke R)]) (sq 5) == 1
-- Several spreads of one view reuse its ONE preparation (the original spread ran once).
#guard valueIs (run pairs [add (callF "Add" [.sequenceSpread (args R)]) (callF "Add" [.sequenceSpread (args R)])]) (.atom 6)
#guard readyCellsOf (heap pairs [add (callF "Add" [.sequenceSpread (args R)]) (callF "Add" [.sequenceSpread (args R)])]) (.atom 1) == 1
-- A spread view into a builtin destination binds as the original argument list would.
#guard valueIs (run (callF "Pick" [.boolLiteral true, .num 1, .num 2]) [callF "if" [.sequenceSpread (args R)]]) (.atom 1)
-- A selector supply transports the cells too.
#guard valueIs (runResult (program (withR (callF "Add" [.num 1, .num 0]))
    [.index (.listLiteral [.num 7, .num 8]) [.sequenceSpread (args R)]])) (.sequenceValue [.atom 8, .atom 7])
-- A stacked star opens the view into values first: refused; a grouped re-capture is the view.
#guard isTypeMismatch (run add1020 [callF "Mul" [.sequenceSpread (.sequenceSpread (args R))]]) argumentViewSpreadMessage
#guard valueIs (run add1020 [callF "Mul" [.sequenceSpread (.capture [args R])]]) (.atom 200)
-- A cycle through the captured call's own view is the plan's re-entrant preparation.
#guard isCycle (runResult (program (extra ++ [("Q", alg [] [] [] [callF "Capture" [callF "Add" [.sequenceSpread (args (.resolve "Q"))]]])])
    [dot (args (.resolve "Q")) "count"]))

/-! ## Unsupported operations and boundaries -/

-- Value-position spreads never open a view.
#guard isTypeMismatch (run add1020 [.listLiteral [.sequenceSpread (args R)]]) argumentViewSpreadMessage
-- Other collection builtins refuse the view instead of materializing it.
#guard isTypeMismatch (run add1020 [callF "sum" [args R]]) (argumentViewUnsupportedMessage "sum")
#guard isTypeMismatch (run add1020 [callF "map" [args R, .resolve "Inc"]]) (argumentViewUnsupportedMessage "map")
#guard isTypeMismatch (run add1020 [callF "atoms" [args R]]) (argumentViewUnsupportedMessage "atoms")
-- …but a list CONTAINING a view is an ordinary collection.
#guard valueIs (run add1020 [callF "count" [.listLiteral [args R, .num 1]]]) (.atom 2)
-- The intrinsic route.
#guard isIllegal (run add1020 [.dotCall R "Arguments" (some [])]) argumentsIsPropertyMessage
#guard isTypeMismatch (run add1020 [args (.num 5)]) (argumentsRequiresCallReferenceMessage (.atom 5))
#guard valueIs (runResult (program extra [dot (.resolve "Box2") "Arguments"])) (.atom 3)
#guard valueIs (runResult (program extra [callF "Arguments" [.num 4]])) (.atom 5)
-- A view is not a reference: it cannot be invoked, nor viewed again.
#guard isTypeMismatchAny (run add1020 [invoke (args R)])
#guard isTypeMismatchAny (run add1020 [args (args R)])
-- Run, text and operator boundaries.
#guard isTypeMismatch (run add1020 [args R]) callReferenceLeavesRunMessage
#guard isTypeMismatch (run add1020 [.listLiteral [.num 1, args R]]) callReferenceLeavesRunMessage
#guard isTypeMismatch (run add1020 [.interpolatedString "v=" [{ hole := args R, text := "" }]])
  callReferenceHasNoTextMessage
#guard isTypeMismatchAny (run add1020 [add (args R) (.num 1)])

end KatLang.ArgumentViewGuards
