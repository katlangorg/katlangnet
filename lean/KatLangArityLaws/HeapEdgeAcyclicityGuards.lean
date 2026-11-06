import KatLangArityLaws.HeapEdgeAcyclicity
import KatLangArityLaws.ArgumentViewGuards

open KatLang KatLang.CallReferenceGuards KatLang.ArgumentViewGuards

/-!
# FC-AC guards: stored addresses are not acyclic, and a demand cycle is a language error

Executable evidence on whole programs through `runResultWithState`.

THE COUNTEREXAMPLE to "every stored need address points backward, so the heap is acyclic":

    Capture(meta op) = op
    Inner(v) = v
    Q = P
    P = Capture(Inner(Q))
    P == P.Arguments[0]

`P` caches the reference to the plan cell `p` of `Inner(Q)`. Selecting `P.Arguments[0]` prepares that plan's supply, so `p`
stores its argument cell `a`, and demands `a`, whose VALUE is `Q`, that is `P`'s cached reference to `p`. So `p → a` through the
prepared supply and `a → p` through the completed VALUE: a two-cycle in a program that runs to `true`. Nothing goes wrong,
because no demand follows a stored reference. It is run by the C# engine too
(`SignatureCompletionBridgeTests.AStoredAddressCycle_IsAValidProgram`).
-/

namespace KatLang.HeapEdgeAcyclicityGuards

def mentions : Result → List Nat
  | .callRef a => [a]
  | .argView a => [a]
  | _ => []

/-- The stored edges this witness exercises: prepared supply and a completed VALUE's top-level reference. -/
def storedEdges (heap : Array NeedCell) : List (Nat × Nat) :=
  (heap.toList.zipIdx).flatMap fun (cell, a) =>
    let supply := match cell.plan with
      | .prepared (.ok cells) => cells.map fun entry => (a, entry.1)
      | _ => []
    let value := match cell.state with
      | .completed (.ok counted) => (mentions counted.1).map fun b => (a, b)
      | _ => []
    supply ++ value

def hasTwoCycle (edges : List (Nat × Nat)) : Bool :=
  edges.any fun (a, b) => a != b && edges.contains (b, a)

def witnessDeclarations : List (Ident × Algorithm) :=
  [("Inner", alg ["v"] [] [] [.param "v"]),
   ("Q", alg [] [] [] [.resolve "P"]),
   ("P", alg [] [] [] [callF "Capture" [callF "Inner" [.resolve "Q"]]])]

def witness : Expr :=
  program witnessDeclarations [.comparison (.resolve "P") [⟨.eq, .index (args (.resolve "P")) [.num 0]⟩]]

/- The witness runs: it is a valid program that succeeds with `true`. -/
#guard valueIs (runResult witness) (.bool true)

/- `stored_addresses_have_a_cycle`: THE STORED-ADDRESS GRAPH OF A VALID PROGRAM HAS A CYCLE. -/
#guard hasTwoCycle (storedEdges (finalHeap witness))

/- The discrimination: the same program without the selection has no such cycle. -/
#guard !hasTwoCycle (storedEdges (finalHeap (program witnessDeclarations [.comparison (.resolve "P") [⟨.eq, .resolve "P"⟩]])))

/- A DEMAND cycle is different: it is the ordinary failure `demandCycle` at run time, never a malformed heap. A preparing
    plan that reads its own arguments re-enters itself: `Q = Capture(Add(Q.Arguments*))`-style. -/
#guard isCycle (runResult (program (extra ++ [("Q", alg [] [] [] [callF "Capture" [callF "Add" [.sequenceSpread (args (.resolve "Q"))]]])])
    [dot (args (.resolve "Q")) "count"]))

/- Recursive programs are legal: a callable dependency cycle is a language feature, not a violated invariant. -/
#guard valueIs (runResult (program
    [("Down", alg ["n"] [] [] [.call (.resolve "if")
      [.comparison (.param "n") [⟨.le, .num 0⟩], .num 0, callF "Down" [.binary .sub (.param "n") (.num 1)]]])]
    [callF "Down" [.num 3]])) (.atom 0)

/-- info: 'KatLang.HeapEdgeAcyclicity.production_collector_no_cycle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KatLang.HeapEdgeAcyclicity.production_collector_no_cycle

end KatLang.HeapEdgeAcyclicityGuards
