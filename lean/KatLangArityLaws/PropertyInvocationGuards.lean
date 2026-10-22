import KatLangArityLaws.PropertyInvocationLaws
import KatLangArityLaws.AlgorithmProjectionGuards

open KatLang

namespace KatLang.PropertyInvocationGuards

/-- Source-equivalent to `A = 5; R = Capture(A()); Call0(f) = f(); Call0(R.Algorithm)`.
    The call through a supplied link must publish A, without demanding A's original captured VALUE.
    The heap, rather than a rendered constant result, distinguishes publication from bypass. -/
def linkProgram (nested : Bool) : Expr :=
  let call (f : String) (args : List Expr) := Expr.call (.resolve f) args
  let link (f : String) := Expr.dotCall (.resolve f) "Algorithm" none
  CallReferenceGuards.program
    [("A", alg [] [] [] [.num 5]),
     ("R", alg [] [] [] [call "Capture" [call "A" []]]),
     ("S", alg [] [] [] [call "Capture" [.dotCall (.resolve "R") "Algorithm" (some [])]]),
     ("Call0", alg ["f"] [] [] [.call (.param "f") []])]
    [call "Call0" [link (if nested then "S" else "R")]]

def linkPublishes (nested : Bool) : Bool :=
  let (result, state) := (runResultM (linkProgram nested)).runState EvalState.empty
  CallReferenceGuards.valueIs result (.atom 5)
    && (state.zeroArgPropertyCache.filter (fun entry => entry.fst.propertyName == "A")).map (·.snd)
         == [(.atom 5, 1)]
    && state.activeZeroArgProperties.isEmpty

#guard linkPublishes false
#guard linkPublishes true

end KatLang.PropertyInvocationGuards
