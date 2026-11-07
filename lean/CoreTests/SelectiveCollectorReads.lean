import KatLang
import CoreTests.Common

/-!
# Selective observation of a retained collector (NEED-07, November 2026)

A collecting parameter retains an exact slice of its original need cells. `count`, `first`, `last`,
`take` and postfix selection read that slice as positions, so an element no result needs stays
undemanded; a genuine whole VALUE, an ordinary list and every computed carrier stay eager. Every guard
runs a whole program through the production evaluator. `tick()` shows exactly which elements executed
and in which first-demand order, and a failing `1 / 0` element shows which stayed dormant.
C# twin: `SelectiveCollectorReadTests`.
-/

namespace KatLangTests.SelectiveCollectorReads
open KatLang

def bad : Expr := .binary .div (.num 1) (.num 0)
def tick : Expr := .call (.resolve "tick") []
def xs : Expr := .param "xs"
def collecting (body : List Expr) : Algorithm :=
  algWithParameters [{ name := "xs", kind := .collecting }] [] [] body

def builtinCall (name : String) (args : List Expr) : Expr := .call (.resolve name) args
def dot (receiver : Expr) (name : String) (args : Option (List Expr) := none) : Expr :=
  .dotCall receiver name args

/-- `F(*xs) = body` called with `args`. -/
def run (body : List Expr) (args : List Expr) : Except Error Result :=
  runResult (.algorithmExpr (alg [] [] [] [.call (.algorithmExpr (collecting body)) args]))

def isOk (expected : Result) : Except Error Result → Bool
  | .ok value => value == expected
  | .error _ => false
def isDiv : Except Error Result → Bool
  | .error error => KatLangTests.innermostIsDivByZero error
  | .ok _ => false
def isBadIndex : Except Error Result → Bool
  | .error error => KatLangTests.innermostIsBadIndex error
  | .ok _ => false
partial def innermostError : Error → Error
  | .withContext _ inner => innermostError inner
  | error => error
def isType : Except Error Result → Bool
  | .error error => match innermostError error with
    | .typeMismatch _ => true
    | _ => false
  | .ok _ => false
def isArity : Except Error Result → Bool
  | .error error => match innermostError error with
    | .arityMismatch _ _ => true
    | _ => false
  | .ok _ => false

def n (value : Int) : Result := .atom value

-- The primary witnesses -----------------------------------------------------------------
#guard isOk (n 1) (run [dot xs "count"] [bad])
#guard isOk (n 10) (run [.index xs [.num 0]] [.num 10, bad])
#guard isOk (.listValue [n 10]) (run [dot xs "take" (some [.num 1])] [.num 10, bad])

-- The acceptance table ------------------------------------------------------------------
#guard isOk (n 0) (run [dot xs "count"] [])
#guard isOk (n 1) (run [dot xs "count"] [.capture []])
#guard isOk (n 10) (run [dot xs "first"] [.num 10, bad])
#guard isOk (n 20) (run [dot xs "last"] [bad, .num 20])
#guard isOk (n 20) (run [.index xs [.num 1]] [bad, .num 20])
#guard isBadIndex (run [.index xs [.num 99]] [bad])
#guard isOk (.sequenceValue []) (run [.index xs []] [bad])
#guard isOk (.sequenceValue [n 20, n 10, n 20]) (run [.index xs [.num 1, .num 0, .num 1]] [.num 10, .num 20, bad])
#guard isOk (.listValue []) (run [dot xs "take" (some [.num 0])] [bad])
#guard isDiv (run [dot xs "take" (some [.num 2])] [.num 10, bad])

-- Plain and dot spellings select one builtin ----------------------------------------------
#guard isOk (n 1) (run [builtinCall "count" [xs]] [bad])
#guard isOk (n 10) (run [builtinCall "first" [xs]] [.num 10, bad])
#guard isOk (n 20) (run [builtinCall "last" [xs]] [bad, .num 20])
#guard isOk (.listValue [n 10]) (run [builtinCall "take" [xs, .num 1]] [.num 10, bad])

-- Wrong arity rejects before any element; an empty slice reports the ordinary selection failure.
#guard isArity (run [builtinCall "take" [xs]] [bad])
#guard isBadIndex (run [dot xs "first"] [])
#guard isBadIndex (run [dot xs "last"] [])

-- A user declaration shadowing the spelling keeps its own behavior (the identity decides).
#guard isDiv (runResult (.algorithmExpr (alg [] []
  [privateProp "count" (alg ["v"] [] [] [.binary .add (.param "v") (.num 1)]),
   privateProp "F" (collecting [.call (.resolve "count") [xs]])]
  [.call (.resolve "F") [bad]])))

-- Transparent references ------------------------------------------------------------------
private def localProp (name : Ident) (a : Algorithm) (owner : Ident := "xs") : PropDef :=
  { (privateLocalProp name (.localCapturedAncestorParams [owner]) a) with requiredOwnerDepths := some [(owner, some 0)] }
private def reference (name : Ident) (target : Expr) (owner : Ident := "xs") : PropDef :=
  localProp name (.alias none [] [] target) owner
private def carrier (name : Ident) (target : Expr) : PropDef :=
  localProp name (.alias none [] [] target none false)
private def fWith (props : List PropDef) (rows : List Expr) : PropDef :=
  privateProp "F" (algWithParameters [{ name := "xs", kind := .collecting }] [] props rows)
private def program (props : List PropDef) (out : Expr) : Except Error Result :=
  runResult (.algorithmExpr (alg [] [] props [out]))
private def callF (args : List Expr) : Expr := .call (.resolve "F") args
private def oneHop : List PropDef := [reference "A" xs]
private def twoHops : List PropDef := oneHop ++ [reference "B" (.resolve "A")]
private def viaA (rows : List Expr) (args : List Expr) : Except Error Result :=
  program [fWith oneHop rows] (callF args)
private def A : Expr := .resolve "A"

#guard isOk (n 1) (viaA [dot A "count"] [bad])
#guard isOk (n 10) (viaA [.index A [.num 0]] [.num 10, bad])
#guard isOk (n 20) (viaA [dot A "last"] [bad, .num 20])
#guard isOk (.listValue [n 10]) (viaA [dot A "take" (some [.num 1])] [.num 10, bad])
#guard isOk (n 1) (viaA [builtinCall "count" [A]] [bad])
#guard isOk (n 1) (program [fWith twoHops [dot (.resolve "B") "count"]] (callF [bad]))
-- A bare VALUE read of the reference stays the whole eager list.
#guard isDiv (viaA [A] [bad])
-- A structural carrier and a calculation are no transparent references.
#guard isDiv (program [fWith [carrier "C" xs] [dot (.resolve "C") "count"]] (callF [bad]))
#guard isDiv (program [fWith [localProp "L" (alg [] [] [] [.listLiteral [.sequenceSpread xs]])] [dot (.resolve "L") "count"]] (callF [bad]))

-- A static member path selects the member without reading the receiver's output.
private def member (name : Ident) (a : Algorithm) (owner : Ident := "xs") (depth : Nat := 1) : PropDef :=
  { (publicLocalProp name (.localCapturedAncestorParams [owner]) a) with requiredOwnerDepths := some [(owner, some depth)] }
private def memberReference (name : Ident) (target : Expr) (owner : Ident := "xs") (depth : Nat := 1) : PropDef :=
  member name (.alias none [] [] target) owner depth
private def box (members : List PropDef) (output : Expr := .num 0) : PropDef :=
  privateProp "Box" (alg [] [] members [output])
private def boxA (output : Expr := .num 0) : PropDef := box [memberReference "A" xs] output
private def boxDotA : Expr := dot (.resolve "Box") "A"
#guard isOk (n 1) (program [fWith [boxA] [dot boxDotA "count"]] (callF [bad]))
#guard isOk (n 10) (program [fWith [boxA] [.index boxDotA [.num 0]]] (callF [.num 10, bad]))
#guard isOk (n 1) (program [fWith [boxA bad] [dot boxDotA "count"]] (callF [bad]))
#guard isOk (n 1) (program [fWith [boxA, reference "R" (.resolve "Box")] [dot (dot (.resolve "R") "A") "count"]] (callF [bad]))

-- A helper reads the cell it was handed: a transported collector, and a reference argument.
private def countHelper : PropDef := privateProp "Size" (alg ["v"] [] [] [dot (.param "v") "count"])
private def takeHelper : PropDef := privateProp "Head" (alg ["v"] [] [] [.index (.param "v") [.num 0]])
#guard isOk (n 1) (program [countHelper, fWith [] [.call (.resolve "Size") [xs]]] (callF [bad]))
#guard isOk (n 10) (program [takeHelper, fWith [] [.call (.resolve "Head") [xs]]] (callF [.num 10, bad]))
#guard isOk (n 1) (program [countHelper, fWith oneHop [.call (.resolve "Size") [A]]] (callF [bad]))
#guard isOk (n 10) (program [takeHelper, fWith oneHop [.call (.resolve "Head") [A]]] (callF [.num 10, bad]))
-- A chain of reference arguments through two activations is one loop over cells.
private def relay : PropDef := privateProp "Relay" (alg ["w"] [] [reference "B" (.param "w") "w"] [.call (.resolve "Size") [.resolve "B"]])
#guard isOk (n 1) (program [countHelper, relay, fWith oneHop [.call (.resolve "Relay") [A]]] (callF [bad]))
-- A list handed to a helper is ordinary data.
#guard isDiv (program [countHelper, fWith [] [.call (.resolve "Size") [.listLiteral [.sequenceSpread xs]]]] (callF [bad]))

-- A whole VALUE stays eager ---------------------------------------------------------------
#guard isDiv (run [xs] [bad])
#guard isDiv (runResult (.index (.listLiteral [.num 10, bad]) [.num 0]))
#guard isDiv (run [.index (.listLiteral [.sequenceSpread xs]) [.num 0]] [.num 10, bad])
#guard isDiv (run [dot (.listLiteral [.sequenceSpread xs]) "count"] [bad])
#guard isDiv (run [dot (.listLiteral [.sequenceSpread xs]) "take" (some [.num 0])] [bad])
#guard isDiv (run [.index (.listLiteral [.sequenceSpread xs]) []] [bad])
-- Other consumers keep the whole VALUE: this round adds no selective `skip` or `sum`.
#guard isDiv (run [dot xs "skip" (some [.num 1])] [bad, .num 2])
#guard isDiv (run [dot xs "sum"] [bad])

-- Shape: positions, not atoms, emitted values or flattened contents ----------------------
#guard isOk (n 2) (run [dot xs "count"] [.listLiteral [.num 1, .num 2], .capture [.num 3, .num 4]])
#guard isOk (.sequenceValue []) (run [dot xs "first"] [.capture [], .num 2])
#guard isOk (.listValue []) (run [dot xs "last"] [.num 2, .listLiteral []])
#guard isOk (.listValue [.sequenceValue [n 1, n 2]]) (run [dot xs "take" (some [.num 1])] [.capture [.num 1, .num 2], bad])
#guard isOk (.sequenceValue [.sequenceValue [], .listValue []])
  (run [.index xs [.num 0, .num 1]] [.capture [], .listLiteral [], bad])

-- Selector validation and order -----------------------------------------------------------
#guard isType (run [.index xs [.boolLiteral true]] [bad])
#guard isBadIndex (run [.index xs [.num (-1)]] [bad])
#guard isBadIndex (run [.index xs [.num 0, .num 99]] [.num 1, bad])
-- The first selector or element failure ends the selection.
#guard isDiv (run [.index xs [.num 1, .num 99]] [.num 1, bad])
#guard isBadIndex (run [.index xs [.num 99, .num 1]] [.num 1, bad])
-- Formation precedes validation: a spread selector runs first, an ordinary one stays suspended.
#guard isDiv (run [.index xs [.num 99, .sequenceSpread bad]] [.num 1])
#guard isBadIndex (run [.index xs [.num 99, bad]] [.num 1])

-- take controls ---------------------------------------------------------------------------
#guard isOk (.listValue []) (run [dot xs "take" (some [.num (-5)])] [bad])
#guard isOk (.listValue [n 1, n 2]) (run [dot xs "take" (some [.num 99])] [.num 1, .num 2])
#guard isDiv (run [dot xs "take" (some [.num 99])] [.num 1, bad])
#guard isType (run [dot xs "take" (some [.boolLiteral true])] [bad])
-- The count is validated BEFORE a known collector's prefix (the recorded precedence change) ...
#guard isType (run [dot (.param "xs") "take" (some [.boolLiteral true])] [bad, .num 2])
#guard isBadIndex (run [dot xs "take" (some [.index (.listLiteral []) [.num 0]])] [bad])
-- ... and an ordinary collection's receiver still fails first.
#guard isDiv (runResult (dot (.listLiteral [bad]) "take" (some [.boolLiteral true])))

-- Effects: first-demand order, one completion per cell, skipped elements execute nothing ---
#guard isOk (.sequenceValue [n 1, n 2, n 1]) (run [.index xs [.num 1, .num 0, .num 1]] [tick, tick])
#guard isOk (n 1) (run [dot xs "last"] [tick, tick])
-- The skipped element never ran: the next tick after `first` is the second.
#guard isOk (.sequenceValue [n 1, n 2]) (run [dot xs "first", tick] [tick, tick])
#guard isOk (.sequenceValue [n 2, n 1, n 2]) (run [dot xs "count", .index xs [.num 0], tick] [tick, tick])

-- Shared completion: a later whole VALUE keeps positions and reuses completed outcomes ----
#guard isOk (.sequenceValue [n 1, .listValue [n 2, n 1]]) (run [.index xs [.num 1], xs] [tick, tick])
#guard isOk (.sequenceValue [n 1, .listValue [n 2, n 1]]) (run [dot xs "last", xs] [tick, tick])
#guard isOk (.sequenceValue [.listValue [n 1], .listValue [n 1, n 2]]) (run [dot xs "take" (some [.num 1]), xs] [tick, tick])
#guard isOk (.sequenceValue [n 1, n 1]) (run [dot xs "first", dot xs "first"] [tick, tick])
-- A partial read publishes no partial list: the whole VALUE still fails on its bad element.
#guard isDiv (run [dot xs "first", xs] [.num 1, bad])

end KatLangTests.SelectiveCollectorReads
