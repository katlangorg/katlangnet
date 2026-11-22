import KatLang

-- On-demand controls for surviving mutants. The four differential corpora are measured separately.
namespace LeanMutationWitnesses
open KatLang

def tick : Expr := .call (.resolve "tick") []
def divZero : Expr := .binary .div (.num 1) (.num 0)

def prefixProgram (count : Expr) (args : List Expr) : Expr :=
  let body := algWithParameters [{ name := "xs", kind := .collecting }] [] []
    [.dotCall (.param "xs") "take" (some [count])]
  .algorithmExpr (alg [] [] [privateProp "Prefix" body] [.call (.resolve "Prefix") args])

def gives (program : Expr) (expected : Result) : Bool :=
  match runResult program with
  | .ok value => value == expected
  | .error _ => false

def typeFailure : Error → Bool
  | .withContext _ inner => typeFailure inner
  | .typeMismatch _ => true
  | _ => false

-- take_zero_skips_failing_first: Prefix(*xs) = xs.take(0) / Prefix(1 / 0)
#guard gives (prefixProgram (.num 0) [divZero]) (.listValue [])

-- take_count_ticks_before_first_element: Prefix(*xs) = xs.take(tick()) / Prefix(tick(), tick())
#guard gives (prefixProgram tick [tick, tick]) (.listValue [.atom 2])

-- take_count_failure_outranks_first_element: Prefix(*xs) = xs.take('a' + 1) / Prefix(1 / 0)
#guard match runResult (prefixProgram (.binary .add (.stringLiteral "a") (.num 1)) [divZero]) with
  | .error err => typeFailure err
  | .ok _ => false

-- The three properties are the parser's lowering of a two-target deconstruction.
def deconstruction (a b : String) (rhs rows : List Expr) : Expr :=
  let source := "$deconstruct$0"
  let projection := fun name =>
    let helper := algWithParameterPatterns [.unpacking [.capture { name := a }, .capture { name := b }]]
      [] [] [.param name]
    privateProp name (alg [] [] [] [.call (.algorithmExpr helper) [.resolve source]])
  .algorithmExpr (alg [] [] [privateProp source (alg [] [] [] rhs), projection a, projection b] rows)

-- decon_target_call_twice: a, b = tick(), 20 / a(), a(), b
#guard gives (deconstruction "a" "b" [tick, .num 20] [.call (.resolve "a") [], .call (.resolve "a") [], .resolve "b"])
  (.sequenceValue [.atom 1, .atom 1, .atom 20])

-- decon_target_call_after_read: p, q = tick(), tick() / p, p(), q
#guard gives (deconstruction "p" "q" [tick, tick] [.resolve "p", .call (.resolve "p") [], .resolve "q"])
  (.sequenceValue [.atom 1, .atom 1, .atom 2])

end LeanMutationWitnesses
