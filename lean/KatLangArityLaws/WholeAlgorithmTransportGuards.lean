import KatLangArityLaws.WholeAlgorithmTransport
import KatLangArityLaws.AlgorithmProjectionGuards

open KatLang KatLang.CallReferenceGuards KatLang.AlgorithmProjectionGuards

/-!
# M4★ guards: whole-algorithm transport on whole programs (ALIAS-UNIFY-1)

Executable evidence, through the authoritative `runResult`, for what `WholeAlgorithmTransport.lean`
states over the evaluator's definitions: the holder example of the selected contract (a braced
CARRIER with own members whose one row forwards to a member), its transparent REFERENCE, passing,
the group-aware repeated-name match over identities, META's structural callee, the elaboration
boundary of a raw host-built body, own-member laziness, VALUE delegation without alias entries, and
static open through a reference. The shared declarations are `AlgorithmProjectionGuards`' (`Id`,
`Sq`, `Capture(meta op) = op`, …).
-/

namespace KatLang.WholeAlgorithmTransportGuards

/-- A braced structural forwarding carrier `{ props ⏎ target }`. -/
def carrier (props : List PropDef) (target : Expr) : Algorithm := .alias none [] props target none false

/-- An unbraced transparent reference `= target`. -/
def reference (target : Expr) : Algorithm := .alias none [] [] target

def getQ (receiver : Expr) : Expr := .dotCall receiver "Q" none

/-- `B = { public F(x) = x * x ⏎ public Q = 99 ⏎ F }` (the contract's holder), `A = B`,
    `Other = { public Q = 7 ⏎ Sq }`, `GetQ(b) = b.Q`, `PickQ(x, x) = x.Q`, and the captures
    `RB = Capture(B(3))`, `RA = Capture(A(3))`, `RF = Capture(B.F(3))`. -/
def holderDecls : List (Ident × Algorithm) :=
  [("B", carrier [publicProp "F" (alg ["x"] [] [] [mul (.param "x") (.param "x")]),
                  publicProp "Q" (alg [] [] [] [.num 99])] (.resolve "F")),
   ("A", reference (.resolve "B")),
   ("Other", carrier [publicProp "Q" (alg [] [] [] [.num 7])] (.resolve "Sq")),
   ("GetQ", alg ["b"] [] [] [getQ (.param "b")]),
   ("PickQ", alg ["x", "x"] [] [] [getQ (.param "x")]),
   ("RB", alg [] [] [] [callN "Capture" [callN "B" [.num 3]]]),
   ("RA", alg [] [] [] [callN "Capture" [callN "A" [.num 3]]]),
   ("RF", alg [] [] [] [callN "Capture" [.dotCall (.resolve "B") "F" (some [.num 3])]])]

def isUnknownName (r : Except Error Result) (name : Ident) : Bool :=
  match r with
  | .error e => match innermost e with | .unknownName n => n == name | _ => false
  | .ok _ => false

/-! ## The holder: invocation forwards, structure stays -/

-- `B(3)` invokes F with the supplied argument; `B()` is F's arity rejection, never an
-- algorithm-valued result.
#guard valueIs (run holderDecls [callN "B" [.num 3]]) (.atom 9)
#guard isArity (run holderDecls [callN "B" []]) 1 0
-- `B.F` denotes F (not B); `B.Q` is B's own member.
#guard valueIs (run holderDecls [.dotCall (.resolve "B") "F" (some [.num 4])]) (.atom 16)
#guard valueIs (run holderDecls [getQ (.resolve "B")]) (.atom 99)
-- Passing B preserves B: `GetQ(B)` reads B's own Q.
#guard valueIs (run holderDecls [callN "GetQ" [.resolve "B"]]) (.atom 99)
-- The REFERENCE `A = B` is B: its calls, its members, its passing.
#guard valueIs (run holderDecls [callN "A" [.num 3]]) (.atom 9)
#guard isArity (run holderDecls [callN "A" []]) 1 0
#guard valueIs (run holderDecls [getQ (.resolve "A")]) (.atom 99)
#guard valueIs (run holderDecls [callN "GetQ" [.resolve "A"]]) (.atom 99)

/-! ## Repeated names match identities (group-aware NEED-04)

`PickQ(B, B)` and `PickQ(A, B)` match by callable identity without requesting B's
argument-requiring output (a VALUE demand of B would be F's arity rejection); a different structure
is a different identity. -/

#guard valueIs (run holderDecls [callN "PickQ" [.resolve "B", .resolve "B"]]) (.atom 99)
#guard valueIs (run holderDecls [callN "PickQ" [.resolve "A", .resolve "B"]]) (.atom 99)
#guard valueIs (run holderDecls [callN "PickQ" [.resolve "B", .resolve "A"]]) (.atom 99)
#guard isTypeMismatch (run holderDecls [callN "PickQ" [.resolve "B", .resolve "Other"]])
  "Repeated bind equality requires the same callable identity"

/-! ## META: the structural callee of a captured call

A capture of `B(3)` exposes B through `.Algorithm`; a capture of `A(3)` exposes A's target B; a
capture of `B.F(3)` exposes F, which declares no Q. `R.Invoke()` replays the captured call;
`R.Algorithm(4)` is a fresh call with the new supply. -/

#guard valueIs (run holderDecls [callN "GetQ" [algorithm (.resolve "RB")]]) (.atom 99)
#guard valueIs (run holderDecls [callN "GetQ" [algorithm (.resolve "RA")]]) (.atom 99)
#guard isUnknownName (run holderDecls [callN "GetQ" [algorithm (.resolve "RF")]]) "Q"
#guard valueIs (run holderDecls [invoke (.resolve "RB")]) (.atom 9)
#guard valueIs (run holderDecls [algorithmCall (.resolve "RB") [.num 4]]) (.atom 16)
#guard valueIs (run holderDecls [algorithmCall (.resolve "RA") [.num 4]]) (.atom 16)
#guard valueIs (run holderDecls [algorithmCall (.resolve "RF") [.num 5]]) (.atom 25)

/-! ## The elaboration boundary: a raw host-built body is no alias

`H = Sq` built as a `User` (never elaborated) is an ordinary zero-parameter body: a call with a
supply is its own arity rejection (it does not forward), and `HQ = { public Q = 1 ⏎ B }` built as a
`User` keeps its own members. -/

def rawDecls : List (Ident × Algorithm) :=
  holderDecls ++
    [("H", alg [] [] [] [.resolve "Sq"]),
     ("HQ", alg [] [] [publicProp "Q" (alg [] [] [] [.num 1])] [.resolve "B"])]

#guard isArity (run rawDecls [callN "H" [.num 3]]) 0 1
#guard valueIs (run rawDecls [getQ (.resolve "HQ")]) (.atom 1)

/-! ## Structure first: an own member never touches the forwarding target

`LazyC = { public K = 5 ⏎ Boom }` with `Boom = Id(1 / 0)`: reading or passing the carrier's own K
never evaluates Boom; the bare VALUE and an explicit call reach it. -/

def lazyDecls : List (Ident × Algorithm) :=
  [("Boom", alg [] [] [] [callN "Id" [.binary .div (.num 1) (.num 0)]]),
   ("LazyC", carrier [publicProp "K" (alg [] [] [] [.num 5])] (.resolve "Boom")),
   ("GetK", alg ["c"] [] [] [.dotCall (.param "c") "K" none])]

#guard valueIs (run lazyDecls [.dotCall (.resolve "LazyC") "K" none]) (.atom 5)
#guard valueIs (run lazyDecls [callN "GetK" [.resolve "LazyC"]]) (.atom 5)
#guard isDivByZero (run lazyDecls [.resolve "LazyC"])
#guard isDivByZero (run lazyDecls [callN "LazyC" []])

/-! ## OD-E: VALUE delegation owns no entry; an explicit call publishes under the TARGET -/

def stateOf (decls : List (Ident × Algorithm)) (rows : List Expr) : Except Error Result × EvalState :=
  (runResultM (program (extra ++ decls) rows)).runState EvalState.empty

def entriesOf (state : EvalState) (name : Ident) : Nat :=
  (state.zeroArgPropertyCache.filter (fun entry => entry.fst.propertyName == name)).length

/-- `Z = Id(3)`, its reference `ZA = Z` and its carrier `CZ = { Z }`. -/
def zDecls : List (Ident × Algorithm) :=
  [("Z", alg [] [] [] [callN "Id" [.num 3]]), ("ZA", reference (.resolve "Z")),
   ("CZ", carrier [] (.resolve "Z"))]

#guard let (r, st) := stateOf zDecls [.resolve "ZA"]
  valueIs r (.atom 3) && entriesOf st "ZA" == 0 && entriesOf st "Z" == 1
#guard let (r, st) := stateOf zDecls [callN "ZA" []]
  valueIs r (.atom 3) && entriesOf st "ZA" == 0 && entriesOf st "Z" == 1
#guard let (r, st) := stateOf zDecls [.resolve "CZ", .resolve "Z"]
  valueIs r (.sequenceValue [.atom 3, .atom 3]) && entriesOf st "CZ" == 0 && entriesOf st "Z" == 1
#guard let (r, st) := stateOf zDecls [callN "CZ" []]
  valueIs r (.atom 3) && entriesOf st "CZ" == 0 && entriesOf st "Z" == 1
-- One evaluation of Z's body serves the reference, the carrier and Z itself.
#guard cellsOf (heap zDecls [.resolve "ZA", .resolve "CZ", .resolve "Z"]) (.num 3) == 1

/-! ## OD-C: static open through a reference; one provider, distinct providers stay ambiguous -/

def openDecls : List (Ident × Algorithm) :=
  [("LibQ", alg [] [] [publicProp "KQ" (alg [] [] [] [.num 99])] []),
   ("LibQ2", alg [] [] [publicProp "KQ" (alg [] [] [] [.num 98])] []),
   ("AQ", reference (.resolve "LibQ")),
   ("P1", alg [] [.resolve "AQ", .resolve "LibQ"] [] [.resolve "KQ"]),
   ("P2", alg [] [.resolve "AQ", .resolve "LibQ2"] [] [.resolve "KQ"]),
   ("CQ", carrier [publicProp "KC" (alg [] [] [] [.num 5])] (.resolve "LibQ")),
   ("P3", alg [] [.resolve "CQ"] [] [.resolve "KC"]),
   ("P4", alg [] [.resolve "CQ"] [] [.resolve "KQ"])]

-- `open AQ, LibQ` is ONE provider: no ambiguity.
#guard valueIs (run openDecls [.resolve "P1"]) (.atom 99)
-- `open AQ, LibQ2`: two providers exporting KQ stay ambiguous.
#guard match run openDecls [.resolve "P2"] with
  | .error e => match innermost e with | .ambiguousOpen _ _ => true | _ => false
  | .ok _ => false
-- A carrier opens only its own public declarations (`{LibQ}` does not expose KQ).
#guard valueIs (run openDecls [.resolve "P3"]) (.atom 5)
#guard isUnknownName (run openDecls [.resolve "P4"]) "KQ"

/-! ## An inline carrier receiver of the call-reference intrinsics reads the ONE plan

`{ R }.Invoke()`, `{ R }.Arguments` and `{ R }.Algorithm(…)` read R through its VALUE terminal's cached entry
(the `valueAlg` of the `Invoke` and `Arguments` arms and of `referenceReceiverValue`), so R's body
`Capture(Sq(5))` runs ONCE whatever reads it: one written `Sq(5)` capture cell, one plan whose argument `5` is
memoized, and `{ R }.Arguments` is R's own view (ALIAS-UNIFY-1 third review). -/

/-- `R = Capture(Sq(5))`. -/
def planDecls : List (Ident × Algorithm) := [("R", alg [] [] [] [callN "Capture" [callN "Sq" [.num 5]]])]

/-- The inline carrier `{ R }`. -/
def inlineR : Expr := .algorithmExpr (carrier [] (.resolve "R"))

/-- How many times R's body ran: the cells of its written capture argument `Sq(5)`. -/
def captures (cells : Array NeedCell) : Nat := cellsOf cells (callN "Sq" [.num 5])

#guard valueIs (run planDecls [add (invoke (.resolve "R")) (invoke inlineR)]) (.atom 50)
#guard captures (heap planDecls [add (invoke (.resolve "R")) (invoke inlineR)]) == 1
#guard cellsOf (heap planDecls [add (invoke (.resolve "R")) (invoke inlineR)]) (.num 5) == 1
#guard valueIs (run planDecls [.compare .eq (arguments inlineR) (arguments (.resolve "R"))]) (.bool true)
#guard captures (heap planDecls [.compare .eq (arguments inlineR) (arguments (.resolve "R"))]) == 1
#guard valueIs (run planDecls [add (invoke (.resolve "R")) (algorithmCall inlineR [.num 2])]) (.atom 29)
#guard captures (heap planDecls [add (invoke (.resolve "R")) (algorithmCall inlineR [.num 2])]) == 1

end KatLang.WholeAlgorithmTransportGuards
