import KatLang

/-!
GENERATED FILE - DO NOT EDIT BY HAND.

Differential corpus for the small-state semantic explorer
(tests/KatLang.Tests/SemanticExplorerCorpus.cs). Each case is the Lean AST
construction equivalent to a KatLang source program, and each `#guard` pins
the neutral observation recorded from the C# evaluator. A failing guard is a
Lean/C# divergence on that case.

Partition (machine-checked by the `*CaseIds.length` guards below):
- surface corpus cases: 1417
- excluded parse-level cases (Lean has no surface parser): 31
- Lean-representable surface cases: 1386
- internal-node cases: 13
- total generated guards: 1399 case guards + 2 count guards

Regenerate from the repo root with:
  $env:KATLANG_REGENERATE_SEMANTIC_EXPLORER = "1"
  dotnet test .\KatLang.slnx --filter SemanticExplorerLeanArtifact
-/

namespace SemanticExplorerCases
open KatLang

/-- Neutral raw-structure encoding shared with the C# harness:
    atom -> `1`, string -> `'x'`, sequence -> `S[a, b]`, empty -> `S[]`,
    exact list -> `L[a, b]`. -/
partial def neutral : Result -> String
  | .atom n => toString n
  | .str s => "'" ++ s ++ "'"
  | .sequenceValue rs => "S[" ++ String.intercalate ", " (rs.map neutral) ++ "]"
  | .listValue rs => "L[" ++ String.intercalate ", " (rs.map neutral) ++ "]"

/-- Innermost-error category shared with the C# harness
    (`SemanticExplorerHarness.ErrorCategory`). -/
partial def errCategory : Error -> String
  | .withContext _ inner => errCategory inner
  | .arityMismatch _ _ => "arity"
  | .badArity => "arity"
  | .branchArityMismatch _ _ _ => "arity"
  | .branchOutputArityMismatch _ _ _ => "arity"
  | .badIndex => "index"
  | .typeMismatch _ => "type"
  | .missingOutput => "missingOutput"
  | .spreadMissingOutput => "spreadMissingOutput"
  | .unknownName _ => "unknownName"
  | .divByZero => "div0"
  | .noMatchingBranch _ => "branch"
  | .unknownProperty _ _ => "unknownProperty"
  | .notPublicProperty _ _ => "notPublicProperty"
  | .localOnlyProperty _ _ _ => "localOnlyProperty"
  | .notAnAlgorithm _ => "notAnAlgorithm"
  | .illegalInOpen _ => "illegalInOpen"
  | .badOpenForm _ => "badOpenForm"
  | .illegalInEval _ => "illegalInEval"
  | .ambiguousOpen _ _ => "ambiguousOpen"
  | .duplicateProperty _ => "duplicateProperty"
  | .duplicateBranchPattern => "duplicateBranchPattern"
  | .specialOutputAccess => "specialOutputAccess"
  | .explicitParamsRequireOutput => "explicitParamsRequireOutput"
  | .unresolvedImplicitParams _ => "unresolvedImplicitParams"

/-- Counted variant of `runResultM`: the same root wiring, but keeping the
    root emitted count (`evalAlgOutputCounted` / `evalCounted`), matching the
    C# `Evaluator.RunCounted` observation. -/
def runCountedM (e : Expr) : EvalM CountedResult := do
  validateExplicitParamOutputInvariantExpr e
  let ctx := { callStack := [preludeAlg], algEnv := [] }
  match e with
  | .block a =>
      let wired := wireToCaller ctx a
      if (Algorithm.params wired).length = 0 then
        evalAlgOutputCounted wired ctx []
      else
        .error (Error.unresolvedImplicitParams (Algorithm.params wired))
  | _ => evalCounted e ctx []

/-- Neutral observation string shared verbatim with the C# harness.
    Also cross-checks Lean's plain (`runResult`) and counted evaluators on
    every case: any disagreement between the two produces an
    `internalMismatch ...` observation, which can never equal a pinned
    expectation, so the guard fails and names the case. -/
def obs (e : Expr) : String :=
  match runCountedM e |>.run EvalState.empty, runResult e with
  | .ok ((r, n), _), .ok r2 =>
      if r == r2 then s!"ok raw={neutral r} n={n}"
      else s!"internalMismatch counted={neutral r} plain={neutral r2}"
  | .error e1, .error e2 =>
      if errCategory e1 == errCategory e2 then s!"err {errCategory e1}"
      else s!"internalMismatch countedErr={errCategory e1} plainErr={errCategory e2}"
  | .ok ((r, _), _), .error e2 => s!"internalMismatch counted=ok:{neutral r} plain=err:{errCategory e2}"
  | .error e1, .ok r2 => s!"internalMismatch counted=err:{errCategory e1} plain=ok:{neutral r2}"

-- root__e: ()
def case_root__e : Expr :=
  .block (alg [] [] [] [(.emptySequence 0)])
#guard obs case_root__e == "ok raw=S[] n=1"

-- root__n0: 0
def case_root__n0 : Expr :=
  .block (alg [] [] [] [(.num 0)])
#guard obs case_root__n0 == "ok raw=0 n=1"

-- root__n1: 1
def case_root__n1 : Expr :=
  .block (alg [] [] [] [(.num 1)])
#guard obs case_root__n1 == "ok raw=1 n=1"

-- root__p1: (1)
def case_root__p1 : Expr :=
  .block (alg [] [] [] [(.block (alg [] [] [] [(.num 1)]))])
#guard obs case_root__p1 == "ok raw=1 n=1"

-- root__p12: (1, 2)
def case_root__p12 : Expr :=
  .block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)]))])
#guard obs case_root__p12 == "ok raw=S[1, 2] n=1"

-- root__p123: (1, 2, 3)
def case_root__p123 : Expr :=
  .block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2), (.num 3)]))])
#guard obs case_root__p123 == "ok raw=S[1, 2, 3] n=1"

-- root__pee: ((), ())
def case_root__pee : Expr :=
  .block (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.emptySequence 0)]))])
#guard obs case_root__pee == "ok raw=S[S[], S[]] n=1"

-- root__pe1: ((), 1)
def case_root__pe1 : Expr :=
  .block (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.num 1)]))])
#guard obs case_root__pe1 == "ok raw=S[S[], 1] n=1"

-- root__p1e: (1, ())
def case_root__p1e : Expr :=
  .block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.emptySequence 0)]))])
#guard obs case_root__p1e == "ok raw=S[1, S[]] n=1"

-- root__p12_3: ((1, 2), 3)
def case_root__p12_3 : Expr :=
  .block (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.num 3)]))])
#guard obs case_root__p12_3 == "ok raw=S[S[1, 2], 3] n=1"

-- root__p12_34: ((1, 2), (3, 4))
def case_root__p12_34 : Expr :=
  .block (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.block (alg [] [] [] [(.num 3), (.num 4)]))]))])
#guard obs case_root__p12_34 == "ok raw=S[S[1, 2], S[3, 4]] n=1"

-- root__pe_12: ((), (1, 2))
def case_root__pe_12 : Expr :=
  .block (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.block (alg [] [] [] [(.num 1), (.num 2)]))]))])
#guard obs case_root__pe_12 == "ok raw=S[S[], S[1, 2]] n=1"

-- root__ppe1_2: (((), 1), 2)
def case_root__ppe1_2 : Expr :=
  .block (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.num 1)])), (.num 2)]))])
#guard obs case_root__ppe1_2 == "ok raw=S[S[S[], 1], 2] n=1"

-- root__p12_e: ((1, 2), ())
def case_root__p12_e : Expr :=
  .block (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.emptySequence 0)]))])
#guard obs case_root__p12_e == "ok raw=S[S[1, 2], S[]] n=1"

-- root__ppe: (())
def case_root__ppe : Expr :=
  .block (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0)]))])
#guard obs case_root__ppe == "ok raw=S[] n=1"

-- root__pp1: ((1))
def case_root__pp1 : Expr :=
  .block (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1)]))]))])
#guard obs case_root__pp1 == "ok raw=1 n=1"

-- root__ppp12: (((1, 2)))
def case_root__ppp12 : Expr :=
  .block (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)]))]))]))])
#guard obs case_root__ppp12 == "ok raw=S[1, 2] n=1"

-- root__le: []
def case_root__le : Expr :=
  .block (alg [] [] [] [(.listLiteral [])])
#guard obs case_root__le == "ok raw=L[] n=1"

-- root__l7: [7]
def case_root__l7 : Expr :=
  .block (alg [] [] [] [(.listLiteral [(.num 7)])])
#guard obs case_root__l7 == "ok raw=L[7] n=1"

-- root__l12: [1, 2]
def case_root__l12 : Expr :=
  .block (alg [] [] [] [(.listLiteral [(.num 1), (.num 2)])])
#guard obs case_root__l12 == "ok raw=L[1, 2] n=1"

-- root__l12_3: [[1, 2], 3]
def case_root__l12_3 : Expr :=
  .block (alg [] [] [] [(.listLiteral [(.listLiteral [(.num 1), (.num 2)]), (.num 3)])])
#guard obs case_root__l12_3 == "ok raw=L[L[1, 2], 3] n=1"

-- root__lle: [[]]
def case_root__lle : Expr :=
  .block (alg [] [] [] [(.listLiteral [(.listLiteral [])])])
#guard obs case_root__lle == "ok raw=L[L[]] n=1"

-- root__l_e: [()]
def case_root__l_e : Expr :=
  .block (alg [] [] [] [(.listLiteral [(.emptySequence 0)])])
#guard obs case_root__l_e == "ok raw=L[S[]] n=1"

-- root__l_p12: [(1, 2)]
def case_root__l_p12 : Expr :=
  .block (alg [] [] [] [(.listLiteral [(.block (alg [] [] [] [(.num 1), (.num 2)]))])])
#guard obs case_root__l_p12 == "ok raw=L[S[1, 2]] n=1"

-- root__p_l12: ([1, 2], 3)
def case_root__p_l12 : Expr :=
  .block (alg [] [] [] [(.block (alg [] [] [] [(.listLiteral [(.num 1), (.num 2)]), (.num 3)]))])
#guard obs case_root__p_l12 == "ok raw=S[L[1, 2], 3] n=1"

-- root__pl1: ([1])
def case_root__pl1 : Expr :=
  .block (alg [] [] [] [(.block (alg [] [] [] [(.listLiteral [(.num 1)])]))])
#guard obs case_root__pl1 == "ok raw=L[1] n=1"

-- capture__e: x = () \n x
def case_capture__e : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.emptySequence 0)])] [.resolve "x"])
#guard obs case_capture__e == "ok raw=S[] n=1"

-- capture__n0: x = 0 \n x
def case_capture__n0 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.num 0)])] [.resolve "x"])
#guard obs case_capture__n0 == "ok raw=0 n=1"

-- capture__n1: x = 1 \n x
def case_capture__n1 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.num 1)])] [.resolve "x"])
#guard obs case_capture__n1 == "ok raw=1 n=1"

-- capture__p1: x = (1) \n x
def case_capture__p1 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.num 1)]))])] [.resolve "x"])
#guard obs case_capture__p1 == "ok raw=1 n=1"

-- capture__p12: x = (1, 2) \n x
def case_capture__p12 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)]))])] [.resolve "x"])
#guard obs case_capture__p12 == "ok raw=S[1, 2] n=1"

-- capture__p123: x = (1, 2, 3) \n x
def case_capture__p123 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2), (.num 3)]))])] [.resolve "x"])
#guard obs case_capture__p123 == "ok raw=S[1, 2, 3] n=1"

-- capture__pee: x = ((), ()) \n x
def case_capture__pee : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.emptySequence 0)]))])] [.resolve "x"])
#guard obs case_capture__pee == "ok raw=S[S[], S[]] n=1"

-- capture__pe1: x = ((), 1) \n x
def case_capture__pe1 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.num 1)]))])] [.resolve "x"])
#guard obs case_capture__pe1 == "ok raw=S[S[], 1] n=1"

-- capture__p1e: x = (1, ()) \n x
def case_capture__p1e : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.emptySequence 0)]))])] [.resolve "x"])
#guard obs case_capture__p1e == "ok raw=S[1, S[]] n=1"

-- capture__p12_3: x = ((1, 2), 3) \n x
def case_capture__p12_3 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.num 3)]))])] [.resolve "x"])
#guard obs case_capture__p12_3 == "ok raw=S[S[1, 2], 3] n=1"

-- capture__p12_34: x = ((1, 2), (3, 4)) \n x
def case_capture__p12_34 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.block (alg [] [] [] [(.num 3), (.num 4)]))]))])] [.resolve "x"])
#guard obs case_capture__p12_34 == "ok raw=S[S[1, 2], S[3, 4]] n=1"

-- capture__pe_12: x = ((), (1, 2)) \n x
def case_capture__pe_12 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.block (alg [] [] [] [(.num 1), (.num 2)]))]))])] [.resolve "x"])
#guard obs case_capture__pe_12 == "ok raw=S[S[], S[1, 2]] n=1"

-- capture__ppe1_2: x = (((), 1), 2) \n x
def case_capture__ppe1_2 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.num 1)])), (.num 2)]))])] [.resolve "x"])
#guard obs case_capture__ppe1_2 == "ok raw=S[S[S[], 1], 2] n=1"

-- capture__p12_e: x = ((1, 2), ()) \n x
def case_capture__p12_e : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.emptySequence 0)]))])] [.resolve "x"])
#guard obs case_capture__p12_e == "ok raw=S[S[1, 2], S[]] n=1"

-- capture__ppe: x = (()) \n x
def case_capture__ppe : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0)]))])] [.resolve "x"])
#guard obs case_capture__ppe == "ok raw=S[] n=1"

-- capture__pp1: x = ((1)) \n x
def case_capture__pp1 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1)]))]))])] [.resolve "x"])
#guard obs case_capture__pp1 == "ok raw=1 n=1"

-- capture__ppp12: x = (((1, 2))) \n x
def case_capture__ppp12 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)]))]))]))])] [.resolve "x"])
#guard obs case_capture__ppp12 == "ok raw=S[1, 2] n=1"

-- capture__le: x = [] \n x
def case_capture__le : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [])])] [.resolve "x"])
#guard obs case_capture__le == "ok raw=L[] n=1"

-- capture__l7: x = [7] \n x
def case_capture__l7 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [(.num 7)])])] [.resolve "x"])
#guard obs case_capture__l7 == "ok raw=L[7] n=1"

-- capture__l12: x = [1, 2] \n x
def case_capture__l12 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [(.num 1), (.num 2)])])] [.resolve "x"])
#guard obs case_capture__l12 == "ok raw=L[1, 2] n=1"

-- capture__l12_3: x = [[1, 2], 3] \n x
def case_capture__l12_3 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [(.listLiteral [(.num 1), (.num 2)]), (.num 3)])])] [.resolve "x"])
#guard obs case_capture__l12_3 == "ok raw=L[L[1, 2], 3] n=1"

-- capture__lle: x = [[]] \n x
def case_capture__lle : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [(.listLiteral [])])])] [.resolve "x"])
#guard obs case_capture__lle == "ok raw=L[L[]] n=1"

-- capture__l_e: x = [()] \n x
def case_capture__l_e : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [(.emptySequence 0)])])] [.resolve "x"])
#guard obs case_capture__l_e == "ok raw=L[S[]] n=1"

-- capture__l_p12: x = [(1, 2)] \n x
def case_capture__l_p12 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [(.block (alg [] [] [] [(.num 1), (.num 2)]))])])] [.resolve "x"])
#guard obs case_capture__l_p12 == "ok raw=L[S[1, 2]] n=1"

-- capture__p_l12: x = ([1, 2], 3) \n x
def case_capture__p_l12 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.listLiteral [(.num 1), (.num 2)]), (.num 3)]))])] [.resolve "x"])
#guard obs case_capture__p_l12 == "ok raw=S[L[1, 2], 3] n=1"

-- capture__pl1: x = ([1]) \n x
def case_capture__pl1 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.listLiteral [(.num 1)])]))])] [.resolve "x"])
#guard obs case_capture__pl1 == "ok raw=L[1] n=1"

-- captureCall__e: x = () \n x()
def case_captureCall__e : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.emptySequence 0)])] [.call (.resolve "x") (alg [] [] [] [])])
#guard obs case_captureCall__e == "ok raw=S[] n=1"

-- captureCall__n0: x = 0 \n x()
def case_captureCall__n0 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.num 0)])] [.call (.resolve "x") (alg [] [] [] [])])
#guard obs case_captureCall__n0 == "ok raw=0 n=1"

-- captureCall__n1: x = 1 \n x()
def case_captureCall__n1 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.num 1)])] [.call (.resolve "x") (alg [] [] [] [])])
#guard obs case_captureCall__n1 == "ok raw=1 n=1"

-- captureCall__p1: x = (1) \n x()
def case_captureCall__p1 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.num 1)]))])] [.call (.resolve "x") (alg [] [] [] [])])
#guard obs case_captureCall__p1 == "ok raw=1 n=1"

-- captureCall__p12: x = (1, 2) \n x()
def case_captureCall__p12 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)]))])] [.call (.resolve "x") (alg [] [] [] [])])
#guard obs case_captureCall__p12 == "ok raw=S[1, 2] n=1"

-- captureCall__p123: x = (1, 2, 3) \n x()
def case_captureCall__p123 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2), (.num 3)]))])] [.call (.resolve "x") (alg [] [] [] [])])
#guard obs case_captureCall__p123 == "ok raw=S[1, 2, 3] n=1"

-- captureCall__pee: x = ((), ()) \n x()
def case_captureCall__pee : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.emptySequence 0)]))])] [.call (.resolve "x") (alg [] [] [] [])])
#guard obs case_captureCall__pee == "ok raw=S[S[], S[]] n=1"

-- captureCall__pe1: x = ((), 1) \n x()
def case_captureCall__pe1 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.num 1)]))])] [.call (.resolve "x") (alg [] [] [] [])])
#guard obs case_captureCall__pe1 == "ok raw=S[S[], 1] n=1"

-- captureCall__p1e: x = (1, ()) \n x()
def case_captureCall__p1e : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.emptySequence 0)]))])] [.call (.resolve "x") (alg [] [] [] [])])
#guard obs case_captureCall__p1e == "ok raw=S[1, S[]] n=1"

-- captureCall__p12_3: x = ((1, 2), 3) \n x()
def case_captureCall__p12_3 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.num 3)]))])] [.call (.resolve "x") (alg [] [] [] [])])
#guard obs case_captureCall__p12_3 == "ok raw=S[S[1, 2], 3] n=1"

-- captureCall__p12_34: x = ((1, 2), (3, 4)) \n x()
def case_captureCall__p12_34 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.block (alg [] [] [] [(.num 3), (.num 4)]))]))])] [.call (.resolve "x") (alg [] [] [] [])])
#guard obs case_captureCall__p12_34 == "ok raw=S[S[1, 2], S[3, 4]] n=1"

-- captureCall__pe_12: x = ((), (1, 2)) \n x()
def case_captureCall__pe_12 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.block (alg [] [] [] [(.num 1), (.num 2)]))]))])] [.call (.resolve "x") (alg [] [] [] [])])
#guard obs case_captureCall__pe_12 == "ok raw=S[S[], S[1, 2]] n=1"

-- captureCall__ppe1_2: x = (((), 1), 2) \n x()
def case_captureCall__ppe1_2 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.num 1)])), (.num 2)]))])] [.call (.resolve "x") (alg [] [] [] [])])
#guard obs case_captureCall__ppe1_2 == "ok raw=S[S[S[], 1], 2] n=1"

-- captureCall__p12_e: x = ((1, 2), ()) \n x()
def case_captureCall__p12_e : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.emptySequence 0)]))])] [.call (.resolve "x") (alg [] [] [] [])])
#guard obs case_captureCall__p12_e == "ok raw=S[S[1, 2], S[]] n=1"

-- captureCall__ppe: x = (()) \n x()
def case_captureCall__ppe : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0)]))])] [.call (.resolve "x") (alg [] [] [] [])])
#guard obs case_captureCall__ppe == "ok raw=S[] n=1"

-- captureCall__pp1: x = ((1)) \n x()
def case_captureCall__pp1 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1)]))]))])] [.call (.resolve "x") (alg [] [] [] [])])
#guard obs case_captureCall__pp1 == "ok raw=1 n=1"

-- captureCall__ppp12: x = (((1, 2))) \n x()
def case_captureCall__ppp12 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)]))]))]))])] [.call (.resolve "x") (alg [] [] [] [])])
#guard obs case_captureCall__ppp12 == "ok raw=S[1, 2] n=1"

-- captureCall__le: x = [] \n x()
def case_captureCall__le : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [])])] [.call (.resolve "x") (alg [] [] [] [])])
#guard obs case_captureCall__le == "ok raw=L[] n=1"

-- captureCall__l7: x = [7] \n x()
def case_captureCall__l7 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [(.num 7)])])] [.call (.resolve "x") (alg [] [] [] [])])
#guard obs case_captureCall__l7 == "ok raw=L[7] n=1"

-- captureCall__l12: x = [1, 2] \n x()
def case_captureCall__l12 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [(.num 1), (.num 2)])])] [.call (.resolve "x") (alg [] [] [] [])])
#guard obs case_captureCall__l12 == "ok raw=L[1, 2] n=1"

-- captureCall__l12_3: x = [[1, 2], 3] \n x()
def case_captureCall__l12_3 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [(.listLiteral [(.num 1), (.num 2)]), (.num 3)])])] [.call (.resolve "x") (alg [] [] [] [])])
#guard obs case_captureCall__l12_3 == "ok raw=L[L[1, 2], 3] n=1"

-- captureCall__lle: x = [[]] \n x()
def case_captureCall__lle : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [(.listLiteral [])])])] [.call (.resolve "x") (alg [] [] [] [])])
#guard obs case_captureCall__lle == "ok raw=L[L[]] n=1"

-- captureCall__l_e: x = [()] \n x()
def case_captureCall__l_e : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [(.emptySequence 0)])])] [.call (.resolve "x") (alg [] [] [] [])])
#guard obs case_captureCall__l_e == "ok raw=L[S[]] n=1"

-- captureCall__l_p12: x = [(1, 2)] \n x()
def case_captureCall__l_p12 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [(.block (alg [] [] [] [(.num 1), (.num 2)]))])])] [.call (.resolve "x") (alg [] [] [] [])])
#guard obs case_captureCall__l_p12 == "ok raw=L[S[1, 2]] n=1"

-- captureCall__p_l12: x = ([1, 2], 3) \n x()
def case_captureCall__p_l12 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.listLiteral [(.num 1), (.num 2)]), (.num 3)]))])] [.call (.resolve "x") (alg [] [] [] [])])
#guard obs case_captureCall__p_l12 == "ok raw=S[L[1, 2], 3] n=1"

-- captureCall__pl1: x = ([1]) \n x()
def case_captureCall__pl1 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.listLiteral [(.num 1)])]))])] [.call (.resolve "x") (alg [] [] [] [])])
#guard obs case_captureCall__pl1 == "ok raw=L[1] n=1"

-- dotAccess__e: A = { \n     X = () \n } \n A.X
def case_dotAccess__e : Expr :=
  .block (alg [] [] [privateProp "A" (alg [] [] [publicProp "X" (alg [] [] [] [(.emptySequence 0)])] [])] [.dotCall (.resolve "A") "X" none])
#guard obs case_dotAccess__e == "ok raw=S[] n=1"

-- dotAccess__n0: A = { \n     X = 0 \n } \n A.X
def case_dotAccess__n0 : Expr :=
  .block (alg [] [] [privateProp "A" (alg [] [] [publicProp "X" (alg [] [] [] [(.num 0)])] [])] [.dotCall (.resolve "A") "X" none])
#guard obs case_dotAccess__n0 == "ok raw=0 n=1"

-- dotAccess__n1: A = { \n     X = 1 \n } \n A.X
def case_dotAccess__n1 : Expr :=
  .block (alg [] [] [privateProp "A" (alg [] [] [publicProp "X" (alg [] [] [] [(.num 1)])] [])] [.dotCall (.resolve "A") "X" none])
#guard obs case_dotAccess__n1 == "ok raw=1 n=1"

-- dotAccess__p1: A = { \n     X = (1) \n } \n A.X
def case_dotAccess__p1 : Expr :=
  .block (alg [] [] [privateProp "A" (alg [] [] [publicProp "X" (alg [] [] [] [(.block (alg [] [] [] [(.num 1)]))])] [])] [.dotCall (.resolve "A") "X" none])
#guard obs case_dotAccess__p1 == "ok raw=1 n=1"

-- dotAccess__p12: A = { \n     X = (1, 2) \n } \n A.X
def case_dotAccess__p12 : Expr :=
  .block (alg [] [] [privateProp "A" (alg [] [] [publicProp "X" (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)]))])] [])] [.dotCall (.resolve "A") "X" none])
#guard obs case_dotAccess__p12 == "ok raw=S[1, 2] n=1"

-- dotAccess__p123: A = { \n     X = (1, 2, 3) \n } \n A.X
def case_dotAccess__p123 : Expr :=
  .block (alg [] [] [privateProp "A" (alg [] [] [publicProp "X" (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2), (.num 3)]))])] [])] [.dotCall (.resolve "A") "X" none])
#guard obs case_dotAccess__p123 == "ok raw=S[1, 2, 3] n=1"

-- dotAccess__pee: A = { \n     X = ((), ()) \n } \n A.X
def case_dotAccess__pee : Expr :=
  .block (alg [] [] [privateProp "A" (alg [] [] [publicProp "X" (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.emptySequence 0)]))])] [])] [.dotCall (.resolve "A") "X" none])
#guard obs case_dotAccess__pee == "ok raw=S[S[], S[]] n=1"

-- dotAccess__pe1: A = { \n     X = ((), 1) \n } \n A.X
def case_dotAccess__pe1 : Expr :=
  .block (alg [] [] [privateProp "A" (alg [] [] [publicProp "X" (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.num 1)]))])] [])] [.dotCall (.resolve "A") "X" none])
#guard obs case_dotAccess__pe1 == "ok raw=S[S[], 1] n=1"

-- dotAccess__p1e: A = { \n     X = (1, ()) \n } \n A.X
def case_dotAccess__p1e : Expr :=
  .block (alg [] [] [privateProp "A" (alg [] [] [publicProp "X" (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.emptySequence 0)]))])] [])] [.dotCall (.resolve "A") "X" none])
#guard obs case_dotAccess__p1e == "ok raw=S[1, S[]] n=1"

-- dotAccess__p12_3: A = { \n     X = ((1, 2), 3) \n } \n A.X
def case_dotAccess__p12_3 : Expr :=
  .block (alg [] [] [privateProp "A" (alg [] [] [publicProp "X" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.num 3)]))])] [])] [.dotCall (.resolve "A") "X" none])
#guard obs case_dotAccess__p12_3 == "ok raw=S[S[1, 2], 3] n=1"

-- dotAccess__p12_34: A = { \n     X = ((1, 2), (3, 4)) \n } \n A.X
def case_dotAccess__p12_34 : Expr :=
  .block (alg [] [] [privateProp "A" (alg [] [] [publicProp "X" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.block (alg [] [] [] [(.num 3), (.num 4)]))]))])] [])] [.dotCall (.resolve "A") "X" none])
#guard obs case_dotAccess__p12_34 == "ok raw=S[S[1, 2], S[3, 4]] n=1"

-- dotAccess__pe_12: A = { \n     X = ((), (1, 2)) \n } \n A.X
def case_dotAccess__pe_12 : Expr :=
  .block (alg [] [] [privateProp "A" (alg [] [] [publicProp "X" (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.block (alg [] [] [] [(.num 1), (.num 2)]))]))])] [])] [.dotCall (.resolve "A") "X" none])
#guard obs case_dotAccess__pe_12 == "ok raw=S[S[], S[1, 2]] n=1"

-- dotAccess__ppe1_2: A = { \n     X = (((), 1), 2) \n } \n A.X
def case_dotAccess__ppe1_2 : Expr :=
  .block (alg [] [] [privateProp "A" (alg [] [] [publicProp "X" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.num 1)])), (.num 2)]))])] [])] [.dotCall (.resolve "A") "X" none])
#guard obs case_dotAccess__ppe1_2 == "ok raw=S[S[S[], 1], 2] n=1"

-- dotAccess__p12_e: A = { \n     X = ((1, 2), ()) \n } \n A.X
def case_dotAccess__p12_e : Expr :=
  .block (alg [] [] [privateProp "A" (alg [] [] [publicProp "X" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.emptySequence 0)]))])] [])] [.dotCall (.resolve "A") "X" none])
#guard obs case_dotAccess__p12_e == "ok raw=S[S[1, 2], S[]] n=1"

-- dotAccess__ppe: A = { \n     X = (()) \n } \n A.X
def case_dotAccess__ppe : Expr :=
  .block (alg [] [] [privateProp "A" (alg [] [] [publicProp "X" (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0)]))])] [])] [.dotCall (.resolve "A") "X" none])
#guard obs case_dotAccess__ppe == "ok raw=S[] n=1"

-- dotAccess__pp1: A = { \n     X = ((1)) \n } \n A.X
def case_dotAccess__pp1 : Expr :=
  .block (alg [] [] [privateProp "A" (alg [] [] [publicProp "X" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1)]))]))])] [])] [.dotCall (.resolve "A") "X" none])
#guard obs case_dotAccess__pp1 == "ok raw=1 n=1"

-- dotAccess__ppp12: A = { \n     X = (((1, 2))) \n } \n A.X
def case_dotAccess__ppp12 : Expr :=
  .block (alg [] [] [privateProp "A" (alg [] [] [publicProp "X" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)]))]))]))])] [])] [.dotCall (.resolve "A") "X" none])
#guard obs case_dotAccess__ppp12 == "ok raw=S[1, 2] n=1"

-- dotAccess__le: A = { \n     X = [] \n } \n A.X
def case_dotAccess__le : Expr :=
  .block (alg [] [] [privateProp "A" (alg [] [] [publicProp "X" (alg [] [] [] [(.listLiteral [])])] [])] [.dotCall (.resolve "A") "X" none])
#guard obs case_dotAccess__le == "ok raw=L[] n=1"

-- dotAccess__l7: A = { \n     X = [7] \n } \n A.X
def case_dotAccess__l7 : Expr :=
  .block (alg [] [] [privateProp "A" (alg [] [] [publicProp "X" (alg [] [] [] [(.listLiteral [(.num 7)])])] [])] [.dotCall (.resolve "A") "X" none])
#guard obs case_dotAccess__l7 == "ok raw=L[7] n=1"

-- dotAccess__l12: A = { \n     X = [1, 2] \n } \n A.X
def case_dotAccess__l12 : Expr :=
  .block (alg [] [] [privateProp "A" (alg [] [] [publicProp "X" (alg [] [] [] [(.listLiteral [(.num 1), (.num 2)])])] [])] [.dotCall (.resolve "A") "X" none])
#guard obs case_dotAccess__l12 == "ok raw=L[1, 2] n=1"

-- dotAccess__l12_3: A = { \n     X = [[1, 2], 3] \n } \n A.X
def case_dotAccess__l12_3 : Expr :=
  .block (alg [] [] [privateProp "A" (alg [] [] [publicProp "X" (alg [] [] [] [(.listLiteral [(.listLiteral [(.num 1), (.num 2)]), (.num 3)])])] [])] [.dotCall (.resolve "A") "X" none])
#guard obs case_dotAccess__l12_3 == "ok raw=L[L[1, 2], 3] n=1"

-- dotAccess__lle: A = { \n     X = [[]] \n } \n A.X
def case_dotAccess__lle : Expr :=
  .block (alg [] [] [privateProp "A" (alg [] [] [publicProp "X" (alg [] [] [] [(.listLiteral [(.listLiteral [])])])] [])] [.dotCall (.resolve "A") "X" none])
#guard obs case_dotAccess__lle == "ok raw=L[L[]] n=1"

-- dotAccess__l_e: A = { \n     X = [()] \n } \n A.X
def case_dotAccess__l_e : Expr :=
  .block (alg [] [] [privateProp "A" (alg [] [] [publicProp "X" (alg [] [] [] [(.listLiteral [(.emptySequence 0)])])] [])] [.dotCall (.resolve "A") "X" none])
#guard obs case_dotAccess__l_e == "ok raw=L[S[]] n=1"

-- dotAccess__l_p12: A = { \n     X = [(1, 2)] \n } \n A.X
def case_dotAccess__l_p12 : Expr :=
  .block (alg [] [] [privateProp "A" (alg [] [] [publicProp "X" (alg [] [] [] [(.listLiteral [(.block (alg [] [] [] [(.num 1), (.num 2)]))])])] [])] [.dotCall (.resolve "A") "X" none])
#guard obs case_dotAccess__l_p12 == "ok raw=L[S[1, 2]] n=1"

-- dotAccess__p_l12: A = { \n     X = ([1, 2], 3) \n } \n A.X
def case_dotAccess__p_l12 : Expr :=
  .block (alg [] [] [privateProp "A" (alg [] [] [publicProp "X" (alg [] [] [] [(.block (alg [] [] [] [(.listLiteral [(.num 1), (.num 2)]), (.num 3)]))])] [])] [.dotCall (.resolve "A") "X" none])
#guard obs case_dotAccess__p_l12 == "ok raw=S[L[1, 2], 3] n=1"

-- dotAccess__pl1: A = { \n     X = ([1]) \n } \n A.X
def case_dotAccess__pl1 : Expr :=
  .block (alg [] [] [privateProp "A" (alg [] [] [publicProp "X" (alg [] [] [] [(.block (alg [] [] [] [(.listLiteral [(.num 1)])]))])] [])] [.dotCall (.resolve "A") "X" none])
#guard obs case_dotAccess__pl1 == "ok raw=L[1] n=1"

-- dotAccessCall__e: A = { \n     X = () \n } \n A.X()
def case_dotAccessCall__e : Expr :=
  .block (alg [] [] [privateProp "A" (alg [] [] [publicProp "X" (alg [] [] [] [(.emptySequence 0)])] [])] [.dotCall (.resolve "A") "X" (some (alg [] [] [] []))])
#guard obs case_dotAccessCall__e == "ok raw=S[] n=1"

-- dotAccessCall__n0: A = { \n     X = 0 \n } \n A.X()
def case_dotAccessCall__n0 : Expr :=
  .block (alg [] [] [privateProp "A" (alg [] [] [publicProp "X" (alg [] [] [] [(.num 0)])] [])] [.dotCall (.resolve "A") "X" (some (alg [] [] [] []))])
#guard obs case_dotAccessCall__n0 == "ok raw=0 n=1"

-- dotAccessCall__n1: A = { \n     X = 1 \n } \n A.X()
def case_dotAccessCall__n1 : Expr :=
  .block (alg [] [] [privateProp "A" (alg [] [] [publicProp "X" (alg [] [] [] [(.num 1)])] [])] [.dotCall (.resolve "A") "X" (some (alg [] [] [] []))])
#guard obs case_dotAccessCall__n1 == "ok raw=1 n=1"

-- dotAccessCall__p1: A = { \n     X = (1) \n } \n A.X()
def case_dotAccessCall__p1 : Expr :=
  .block (alg [] [] [privateProp "A" (alg [] [] [publicProp "X" (alg [] [] [] [(.block (alg [] [] [] [(.num 1)]))])] [])] [.dotCall (.resolve "A") "X" (some (alg [] [] [] []))])
#guard obs case_dotAccessCall__p1 == "ok raw=1 n=1"

-- dotAccessCall__p12: A = { \n     X = (1, 2) \n } \n A.X()
def case_dotAccessCall__p12 : Expr :=
  .block (alg [] [] [privateProp "A" (alg [] [] [publicProp "X" (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)]))])] [])] [.dotCall (.resolve "A") "X" (some (alg [] [] [] []))])
#guard obs case_dotAccessCall__p12 == "ok raw=S[1, 2] n=1"

-- dotAccessCall__p123: A = { \n     X = (1, 2, 3) \n } \n A.X()
def case_dotAccessCall__p123 : Expr :=
  .block (alg [] [] [privateProp "A" (alg [] [] [publicProp "X" (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2), (.num 3)]))])] [])] [.dotCall (.resolve "A") "X" (some (alg [] [] [] []))])
#guard obs case_dotAccessCall__p123 == "ok raw=S[1, 2, 3] n=1"

-- dotAccessCall__pee: A = { \n     X = ((), ()) \n } \n A.X()
def case_dotAccessCall__pee : Expr :=
  .block (alg [] [] [privateProp "A" (alg [] [] [publicProp "X" (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.emptySequence 0)]))])] [])] [.dotCall (.resolve "A") "X" (some (alg [] [] [] []))])
#guard obs case_dotAccessCall__pee == "ok raw=S[S[], S[]] n=1"

-- dotAccessCall__pe1: A = { \n     X = ((), 1) \n } \n A.X()
def case_dotAccessCall__pe1 : Expr :=
  .block (alg [] [] [privateProp "A" (alg [] [] [publicProp "X" (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.num 1)]))])] [])] [.dotCall (.resolve "A") "X" (some (alg [] [] [] []))])
#guard obs case_dotAccessCall__pe1 == "ok raw=S[S[], 1] n=1"

-- dotAccessCall__p1e: A = { \n     X = (1, ()) \n } \n A.X()
def case_dotAccessCall__p1e : Expr :=
  .block (alg [] [] [privateProp "A" (alg [] [] [publicProp "X" (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.emptySequence 0)]))])] [])] [.dotCall (.resolve "A") "X" (some (alg [] [] [] []))])
#guard obs case_dotAccessCall__p1e == "ok raw=S[1, S[]] n=1"

-- dotAccessCall__p12_3: A = { \n     X = ((1, 2), 3) \n } \n A.X()
def case_dotAccessCall__p12_3 : Expr :=
  .block (alg [] [] [privateProp "A" (alg [] [] [publicProp "X" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.num 3)]))])] [])] [.dotCall (.resolve "A") "X" (some (alg [] [] [] []))])
#guard obs case_dotAccessCall__p12_3 == "ok raw=S[S[1, 2], 3] n=1"

-- dotAccessCall__p12_34: A = { \n     X = ((1, 2), (3, 4)) \n } \n A.X()
def case_dotAccessCall__p12_34 : Expr :=
  .block (alg [] [] [privateProp "A" (alg [] [] [publicProp "X" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.block (alg [] [] [] [(.num 3), (.num 4)]))]))])] [])] [.dotCall (.resolve "A") "X" (some (alg [] [] [] []))])
#guard obs case_dotAccessCall__p12_34 == "ok raw=S[S[1, 2], S[3, 4]] n=1"

-- dotAccessCall__pe_12: A = { \n     X = ((), (1, 2)) \n } \n A.X()
def case_dotAccessCall__pe_12 : Expr :=
  .block (alg [] [] [privateProp "A" (alg [] [] [publicProp "X" (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.block (alg [] [] [] [(.num 1), (.num 2)]))]))])] [])] [.dotCall (.resolve "A") "X" (some (alg [] [] [] []))])
#guard obs case_dotAccessCall__pe_12 == "ok raw=S[S[], S[1, 2]] n=1"

-- dotAccessCall__ppe1_2: A = { \n     X = (((), 1), 2) \n } \n A.X()
def case_dotAccessCall__ppe1_2 : Expr :=
  .block (alg [] [] [privateProp "A" (alg [] [] [publicProp "X" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.num 1)])), (.num 2)]))])] [])] [.dotCall (.resolve "A") "X" (some (alg [] [] [] []))])
#guard obs case_dotAccessCall__ppe1_2 == "ok raw=S[S[S[], 1], 2] n=1"

-- dotAccessCall__p12_e: A = { \n     X = ((1, 2), ()) \n } \n A.X()
def case_dotAccessCall__p12_e : Expr :=
  .block (alg [] [] [privateProp "A" (alg [] [] [publicProp "X" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.emptySequence 0)]))])] [])] [.dotCall (.resolve "A") "X" (some (alg [] [] [] []))])
#guard obs case_dotAccessCall__p12_e == "ok raw=S[S[1, 2], S[]] n=1"

-- dotAccessCall__ppe: A = { \n     X = (()) \n } \n A.X()
def case_dotAccessCall__ppe : Expr :=
  .block (alg [] [] [privateProp "A" (alg [] [] [publicProp "X" (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0)]))])] [])] [.dotCall (.resolve "A") "X" (some (alg [] [] [] []))])
#guard obs case_dotAccessCall__ppe == "ok raw=S[] n=1"

-- dotAccessCall__pp1: A = { \n     X = ((1)) \n } \n A.X()
def case_dotAccessCall__pp1 : Expr :=
  .block (alg [] [] [privateProp "A" (alg [] [] [publicProp "X" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1)]))]))])] [])] [.dotCall (.resolve "A") "X" (some (alg [] [] [] []))])
#guard obs case_dotAccessCall__pp1 == "ok raw=1 n=1"

-- dotAccessCall__ppp12: A = { \n     X = (((1, 2))) \n } \n A.X()
def case_dotAccessCall__ppp12 : Expr :=
  .block (alg [] [] [privateProp "A" (alg [] [] [publicProp "X" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)]))]))]))])] [])] [.dotCall (.resolve "A") "X" (some (alg [] [] [] []))])
#guard obs case_dotAccessCall__ppp12 == "ok raw=S[1, 2] n=1"

-- dotAccessCall__le: A = { \n     X = [] \n } \n A.X()
def case_dotAccessCall__le : Expr :=
  .block (alg [] [] [privateProp "A" (alg [] [] [publicProp "X" (alg [] [] [] [(.listLiteral [])])] [])] [.dotCall (.resolve "A") "X" (some (alg [] [] [] []))])
#guard obs case_dotAccessCall__le == "ok raw=L[] n=1"

-- dotAccessCall__l7: A = { \n     X = [7] \n } \n A.X()
def case_dotAccessCall__l7 : Expr :=
  .block (alg [] [] [privateProp "A" (alg [] [] [publicProp "X" (alg [] [] [] [(.listLiteral [(.num 7)])])] [])] [.dotCall (.resolve "A") "X" (some (alg [] [] [] []))])
#guard obs case_dotAccessCall__l7 == "ok raw=L[7] n=1"

-- dotAccessCall__l12: A = { \n     X = [1, 2] \n } \n A.X()
def case_dotAccessCall__l12 : Expr :=
  .block (alg [] [] [privateProp "A" (alg [] [] [publicProp "X" (alg [] [] [] [(.listLiteral [(.num 1), (.num 2)])])] [])] [.dotCall (.resolve "A") "X" (some (alg [] [] [] []))])
#guard obs case_dotAccessCall__l12 == "ok raw=L[1, 2] n=1"

-- dotAccessCall__l12_3: A = { \n     X = [[1, 2], 3] \n } \n A.X()
def case_dotAccessCall__l12_3 : Expr :=
  .block (alg [] [] [privateProp "A" (alg [] [] [publicProp "X" (alg [] [] [] [(.listLiteral [(.listLiteral [(.num 1), (.num 2)]), (.num 3)])])] [])] [.dotCall (.resolve "A") "X" (some (alg [] [] [] []))])
#guard obs case_dotAccessCall__l12_3 == "ok raw=L[L[1, 2], 3] n=1"

-- dotAccessCall__lle: A = { \n     X = [[]] \n } \n A.X()
def case_dotAccessCall__lle : Expr :=
  .block (alg [] [] [privateProp "A" (alg [] [] [publicProp "X" (alg [] [] [] [(.listLiteral [(.listLiteral [])])])] [])] [.dotCall (.resolve "A") "X" (some (alg [] [] [] []))])
#guard obs case_dotAccessCall__lle == "ok raw=L[L[]] n=1"

-- dotAccessCall__l_e: A = { \n     X = [()] \n } \n A.X()
def case_dotAccessCall__l_e : Expr :=
  .block (alg [] [] [privateProp "A" (alg [] [] [publicProp "X" (alg [] [] [] [(.listLiteral [(.emptySequence 0)])])] [])] [.dotCall (.resolve "A") "X" (some (alg [] [] [] []))])
#guard obs case_dotAccessCall__l_e == "ok raw=L[S[]] n=1"

-- dotAccessCall__l_p12: A = { \n     X = [(1, 2)] \n } \n A.X()
def case_dotAccessCall__l_p12 : Expr :=
  .block (alg [] [] [privateProp "A" (alg [] [] [publicProp "X" (alg [] [] [] [(.listLiteral [(.block (alg [] [] [] [(.num 1), (.num 2)]))])])] [])] [.dotCall (.resolve "A") "X" (some (alg [] [] [] []))])
#guard obs case_dotAccessCall__l_p12 == "ok raw=L[S[1, 2]] n=1"

-- dotAccessCall__p_l12: A = { \n     X = ([1, 2], 3) \n } \n A.X()
def case_dotAccessCall__p_l12 : Expr :=
  .block (alg [] [] [privateProp "A" (alg [] [] [publicProp "X" (alg [] [] [] [(.block (alg [] [] [] [(.listLiteral [(.num 1), (.num 2)]), (.num 3)]))])] [])] [.dotCall (.resolve "A") "X" (some (alg [] [] [] []))])
#guard obs case_dotAccessCall__p_l12 == "ok raw=S[L[1, 2], 3] n=1"

-- dotAccessCall__pl1: A = { \n     X = ([1]) \n } \n A.X()
def case_dotAccessCall__pl1 : Expr :=
  .block (alg [] [] [privateProp "A" (alg [] [] [publicProp "X" (alg [] [] [] [(.block (alg [] [] [] [(.listLiteral [(.num 1)])]))])] [])] [.dotCall (.resolve "A") "X" (some (alg [] [] [] []))])
#guard obs case_dotAccessCall__pl1 == "ok raw=L[1] n=1"

-- fixed__e: F(a) = a \n F(())
def case_fixed__e : Expr :=
  .block (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [.call (.resolve "F") (alg [] [] [] [(.emptySequence 0)])])
#guard obs case_fixed__e == "ok raw=S[] n=1"

-- fixed__n0: F(a) = a \n F(0)
def case_fixed__n0 : Expr :=
  .block (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [.call (.resolve "F") (alg [] [] [] [(.num 0)])])
#guard obs case_fixed__n0 == "ok raw=0 n=1"

-- fixed__n1: F(a) = a \n F(1)
def case_fixed__n1 : Expr :=
  .block (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [.call (.resolve "F") (alg [] [] [] [(.num 1)])])
#guard obs case_fixed__n1 == "ok raw=1 n=1"

-- fixed__p1: F(a) = a \n F((1))
def case_fixed__p1 : Expr :=
  .block (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [.call (.resolve "F") (alg [] [] [] [(.block (alg [] [] [] [(.num 1)]))])])
#guard obs case_fixed__p1 == "ok raw=1 n=1"

-- fixed__p12: F(a) = a \n F((1, 2))
def case_fixed__p12 : Expr :=
  .block (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [.call (.resolve "F") (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)]))])])
#guard obs case_fixed__p12 == "ok raw=S[1, 2] n=1"

-- fixed__p123: F(a) = a \n F((1, 2, 3))
def case_fixed__p123 : Expr :=
  .block (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [.call (.resolve "F") (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2), (.num 3)]))])])
#guard obs case_fixed__p123 == "ok raw=S[1, 2, 3] n=1"

-- fixed__pee: F(a) = a \n F(((), ()))
def case_fixed__pee : Expr :=
  .block (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [.call (.resolve "F") (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.emptySequence 0)]))])])
#guard obs case_fixed__pee == "ok raw=S[S[], S[]] n=1"

-- fixed__pe1: F(a) = a \n F(((), 1))
def case_fixed__pe1 : Expr :=
  .block (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [.call (.resolve "F") (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.num 1)]))])])
#guard obs case_fixed__pe1 == "ok raw=S[S[], 1] n=1"

-- fixed__p1e: F(a) = a \n F((1, ()))
def case_fixed__p1e : Expr :=
  .block (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [.call (.resolve "F") (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.emptySequence 0)]))])])
#guard obs case_fixed__p1e == "ok raw=S[1, S[]] n=1"

-- fixed__p12_3: F(a) = a \n F(((1, 2), 3))
def case_fixed__p12_3 : Expr :=
  .block (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [.call (.resolve "F") (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.num 3)]))])])
#guard obs case_fixed__p12_3 == "ok raw=S[S[1, 2], 3] n=1"

-- fixed__p12_34: F(a) = a \n F(((1, 2), (3, 4)))
def case_fixed__p12_34 : Expr :=
  .block (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [.call (.resolve "F") (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.block (alg [] [] [] [(.num 3), (.num 4)]))]))])])
#guard obs case_fixed__p12_34 == "ok raw=S[S[1, 2], S[3, 4]] n=1"

-- fixed__pe_12: F(a) = a \n F(((), (1, 2)))
def case_fixed__pe_12 : Expr :=
  .block (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [.call (.resolve "F") (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.block (alg [] [] [] [(.num 1), (.num 2)]))]))])])
#guard obs case_fixed__pe_12 == "ok raw=S[S[], S[1, 2]] n=1"

-- fixed__ppe1_2: F(a) = a \n F((((), 1), 2))
def case_fixed__ppe1_2 : Expr :=
  .block (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [.call (.resolve "F") (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.num 1)])), (.num 2)]))])])
#guard obs case_fixed__ppe1_2 == "ok raw=S[S[S[], 1], 2] n=1"

-- fixed__p12_e: F(a) = a \n F(((1, 2), ()))
def case_fixed__p12_e : Expr :=
  .block (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [.call (.resolve "F") (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.emptySequence 0)]))])])
#guard obs case_fixed__p12_e == "ok raw=S[S[1, 2], S[]] n=1"

-- fixed__ppe: F(a) = a \n F((()))
def case_fixed__ppe : Expr :=
  .block (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [.call (.resolve "F") (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0)]))])])
#guard obs case_fixed__ppe == "ok raw=S[] n=1"

-- fixed__pp1: F(a) = a \n F(((1)))
def case_fixed__pp1 : Expr :=
  .block (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [.call (.resolve "F") (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1)]))]))])])
#guard obs case_fixed__pp1 == "ok raw=1 n=1"

-- fixed__ppp12: F(a) = a \n F((((1, 2))))
def case_fixed__ppp12 : Expr :=
  .block (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [.call (.resolve "F") (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)]))]))]))])])
#guard obs case_fixed__ppp12 == "ok raw=S[1, 2] n=1"

-- fixed__le: F(a) = a \n F([])
def case_fixed__le : Expr :=
  .block (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [.call (.resolve "F") (alg [] [] [] [(.listLiteral [])])])
#guard obs case_fixed__le == "ok raw=L[] n=1"

-- fixed__l7: F(a) = a \n F([7])
def case_fixed__l7 : Expr :=
  .block (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [.call (.resolve "F") (alg [] [] [] [(.listLiteral [(.num 7)])])])
#guard obs case_fixed__l7 == "ok raw=L[7] n=1"

-- fixed__l12: F(a) = a \n F([1, 2])
def case_fixed__l12 : Expr :=
  .block (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [.call (.resolve "F") (alg [] [] [] [(.listLiteral [(.num 1), (.num 2)])])])
#guard obs case_fixed__l12 == "ok raw=L[1, 2] n=1"

-- fixed__l12_3: F(a) = a \n F([[1, 2], 3])
def case_fixed__l12_3 : Expr :=
  .block (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [.call (.resolve "F") (alg [] [] [] [(.listLiteral [(.listLiteral [(.num 1), (.num 2)]), (.num 3)])])])
#guard obs case_fixed__l12_3 == "ok raw=L[L[1, 2], 3] n=1"

-- fixed__lle: F(a) = a \n F([[]])
def case_fixed__lle : Expr :=
  .block (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [.call (.resolve "F") (alg [] [] [] [(.listLiteral [(.listLiteral [])])])])
#guard obs case_fixed__lle == "ok raw=L[L[]] n=1"

-- fixed__l_e: F(a) = a \n F([()])
def case_fixed__l_e : Expr :=
  .block (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [.call (.resolve "F") (alg [] [] [] [(.listLiteral [(.emptySequence 0)])])])
#guard obs case_fixed__l_e == "ok raw=L[S[]] n=1"

-- fixed__l_p12: F(a) = a \n F([(1, 2)])
def case_fixed__l_p12 : Expr :=
  .block (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [.call (.resolve "F") (alg [] [] [] [(.listLiteral [(.block (alg [] [] [] [(.num 1), (.num 2)]))])])])
#guard obs case_fixed__l_p12 == "ok raw=L[S[1, 2]] n=1"

-- fixed__p_l12: F(a) = a \n F(([1, 2], 3))
def case_fixed__p_l12 : Expr :=
  .block (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [.call (.resolve "F") (alg [] [] [] [(.block (alg [] [] [] [(.listLiteral [(.num 1), (.num 2)]), (.num 3)]))])])
#guard obs case_fixed__p_l12 == "ok raw=S[L[1, 2], 3] n=1"

-- fixed__pl1: F(a) = a \n F(([1]))
def case_fixed__pl1 : Expr :=
  .block (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [.call (.resolve "F") (alg [] [] [] [(.block (alg [] [] [] [(.listLiteral [(.num 1)])]))])])
#guard obs case_fixed__pl1 == "ok raw=L[1] n=1"

-- fixedSpread__e: F(a) = a \n F(spread(()))
def case_fixedSpread__e : Expr :=
  .block (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.emptySequence 0)])])
#guard obs case_fixedSpread__e == "err arity"

-- fixedSpread__n0: F(a) = a \n F(spread(0))
def case_fixedSpread__n0 : Expr :=
  .block (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.num 0)])])
#guard obs case_fixedSpread__n0 == "ok raw=0 n=1"

-- fixedSpread__n1: F(a) = a \n F(spread(1))
def case_fixedSpread__n1 : Expr :=
  .block (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.num 1)])])
#guard obs case_fixedSpread__n1 == "ok raw=1 n=1"

-- fixedSpread__p1: F(a) = a \n F(spread((1)))
def case_fixedSpread__p1 : Expr :=
  .block (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.num 1)]))])])
#guard obs case_fixedSpread__p1 == "ok raw=1 n=1"

-- fixedSpread__p12: F(a) = a \n F(spread((1, 2)))
def case_fixedSpread__p12 : Expr :=
  .block (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.num 1), (.num 2)]))])])
#guard obs case_fixedSpread__p12 == "err arity"

-- fixedSpread__p123: F(a) = a \n F(spread((1, 2, 3)))
def case_fixedSpread__p123 : Expr :=
  .block (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.num 1), (.num 2), (.num 3)]))])])
#guard obs case_fixedSpread__p123 == "err arity"

-- fixedSpread__pee: F(a) = a \n F(spread(((), ())))
def case_fixedSpread__pee : Expr :=
  .block (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.emptySequence 0), (.emptySequence 0)]))])])
#guard obs case_fixedSpread__pee == "err arity"

-- fixedSpread__pe1: F(a) = a \n F(spread(((), 1)))
def case_fixedSpread__pe1 : Expr :=
  .block (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.emptySequence 0), (.num 1)]))])])
#guard obs case_fixedSpread__pe1 == "err arity"

-- fixedSpread__p1e: F(a) = a \n F(spread((1, ())))
def case_fixedSpread__p1e : Expr :=
  .block (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.num 1), (.emptySequence 0)]))])])
#guard obs case_fixedSpread__p1e == "err arity"

-- fixedSpread__p12_3: F(a) = a \n F(spread(((1, 2), 3)))
def case_fixedSpread__p12_3 : Expr :=
  .block (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.num 3)]))])])
#guard obs case_fixedSpread__p12_3 == "err arity"

-- fixedSpread__p12_34: F(a) = a \n F(spread(((1, 2), (3, 4))))
def case_fixedSpread__p12_34 : Expr :=
  .block (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.block (alg [] [] [] [(.num 3), (.num 4)]))]))])])
#guard obs case_fixedSpread__p12_34 == "err arity"

-- fixedSpread__pe_12: F(a) = a \n F(spread(((), (1, 2))))
def case_fixedSpread__pe_12 : Expr :=
  .block (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.emptySequence 0), (.block (alg [] [] [] [(.num 1), (.num 2)]))]))])])
#guard obs case_fixedSpread__pe_12 == "err arity"

-- fixedSpread__ppe1_2: F(a) = a \n F(spread((((), 1), 2)))
def case_fixedSpread__ppe1_2 : Expr :=
  .block (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.num 1)])), (.num 2)]))])])
#guard obs case_fixedSpread__ppe1_2 == "err arity"

-- fixedSpread__p12_e: F(a) = a \n F(spread(((1, 2), ())))
def case_fixedSpread__p12_e : Expr :=
  .block (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.emptySequence 0)]))])])
#guard obs case_fixedSpread__p12_e == "err arity"

-- fixedSpread__ppe: F(a) = a \n F(spread((())))
def case_fixedSpread__ppe : Expr :=
  .block (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.emptySequence 0)]))])])
#guard obs case_fixedSpread__ppe == "err arity"

-- fixedSpread__pp1: F(a) = a \n F(spread(((1))))
def case_fixedSpread__pp1 : Expr :=
  .block (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1)]))]))])])
#guard obs case_fixedSpread__pp1 == "ok raw=1 n=1"

-- fixedSpread__ppp12: F(a) = a \n F(spread((((1, 2)))))
def case_fixedSpread__ppp12 : Expr :=
  .block (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)]))]))]))])])
#guard obs case_fixedSpread__ppp12 == "err arity"

-- fixedSpread__le: F(a) = a \n F(spread([]))
def case_fixedSpread__le : Expr :=
  .block (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.listLiteral [])])])
#guard obs case_fixedSpread__le == "err arity"

-- fixedSpread__l7: F(a) = a \n F(spread([7]))
def case_fixedSpread__l7 : Expr :=
  .block (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.listLiteral [(.num 7)])])])
#guard obs case_fixedSpread__l7 == "ok raw=7 n=1"

-- fixedSpread__l12: F(a) = a \n F(spread([1, 2]))
def case_fixedSpread__l12 : Expr :=
  .block (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.listLiteral [(.num 1), (.num 2)])])])
#guard obs case_fixedSpread__l12 == "err arity"

-- fixedSpread__l12_3: F(a) = a \n F(spread([[1, 2], 3]))
def case_fixedSpread__l12_3 : Expr :=
  .block (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.listLiteral [(.listLiteral [(.num 1), (.num 2)]), (.num 3)])])])
#guard obs case_fixedSpread__l12_3 == "err arity"

-- fixedSpread__lle: F(a) = a \n F(spread([[]]))
def case_fixedSpread__lle : Expr :=
  .block (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.listLiteral [(.listLiteral [])])])])
#guard obs case_fixedSpread__lle == "ok raw=L[] n=1"

-- fixedSpread__l_e: F(a) = a \n F(spread([()]))
def case_fixedSpread__l_e : Expr :=
  .block (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.listLiteral [(.emptySequence 0)])])])
#guard obs case_fixedSpread__l_e == "ok raw=S[] n=1"

-- fixedSpread__l_p12: F(a) = a \n F(spread([(1, 2)]))
def case_fixedSpread__l_p12 : Expr :=
  .block (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.listLiteral [(.block (alg [] [] [] [(.num 1), (.num 2)]))])])])
#guard obs case_fixedSpread__l_p12 == "ok raw=S[1, 2] n=1"

-- fixedSpread__p_l12: F(a) = a \n F(spread(([1, 2], 3)))
def case_fixedSpread__p_l12 : Expr :=
  .block (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.listLiteral [(.num 1), (.num 2)]), (.num 3)]))])])
#guard obs case_fixedSpread__p_l12 == "err arity"

-- fixedSpread__pl1: F(a) = a \n F(spread(([1])))
def case_fixedSpread__pl1 : Expr :=
  .block (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.listLiteral [(.num 1)])]))])])
#guard obs case_fixedSpread__pl1 == "ok raw=1 n=1"

-- variadic__e: F(a...) = a \n F(())
def case_variadic__e : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .variadic }] [] [] [.param "a"])] [.call (.resolve "F") (alg [] [] [] [(.emptySequence 0)])])
#guard obs case_variadic__e == "ok raw=L[S[]] n=1"

-- variadic__n0: F(a...) = a \n F(0)
def case_variadic__n0 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .variadic }] [] [] [.param "a"])] [.call (.resolve "F") (alg [] [] [] [(.num 0)])])
#guard obs case_variadic__n0 == "ok raw=L[0] n=1"

-- variadic__n1: F(a...) = a \n F(1)
def case_variadic__n1 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .variadic }] [] [] [.param "a"])] [.call (.resolve "F") (alg [] [] [] [(.num 1)])])
#guard obs case_variadic__n1 == "ok raw=L[1] n=1"

-- variadic__p1: F(a...) = a \n F((1))
def case_variadic__p1 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .variadic }] [] [] [.param "a"])] [.call (.resolve "F") (alg [] [] [] [(.block (alg [] [] [] [(.num 1)]))])])
#guard obs case_variadic__p1 == "ok raw=L[1] n=1"

-- variadic__p12: F(a...) = a \n F((1, 2))
def case_variadic__p12 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .variadic }] [] [] [.param "a"])] [.call (.resolve "F") (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)]))])])
#guard obs case_variadic__p12 == "ok raw=L[S[1, 2]] n=1"

-- variadic__p123: F(a...) = a \n F((1, 2, 3))
def case_variadic__p123 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .variadic }] [] [] [.param "a"])] [.call (.resolve "F") (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2), (.num 3)]))])])
#guard obs case_variadic__p123 == "ok raw=L[S[1, 2, 3]] n=1"

-- variadic__pee: F(a...) = a \n F(((), ()))
def case_variadic__pee : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .variadic }] [] [] [.param "a"])] [.call (.resolve "F") (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.emptySequence 0)]))])])
#guard obs case_variadic__pee == "ok raw=L[S[S[], S[]]] n=1"

-- variadic__pe1: F(a...) = a \n F(((), 1))
def case_variadic__pe1 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .variadic }] [] [] [.param "a"])] [.call (.resolve "F") (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.num 1)]))])])
#guard obs case_variadic__pe1 == "ok raw=L[S[S[], 1]] n=1"

-- variadic__p1e: F(a...) = a \n F((1, ()))
def case_variadic__p1e : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .variadic }] [] [] [.param "a"])] [.call (.resolve "F") (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.emptySequence 0)]))])])
#guard obs case_variadic__p1e == "ok raw=L[S[1, S[]]] n=1"

-- variadic__p12_3: F(a...) = a \n F(((1, 2), 3))
def case_variadic__p12_3 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .variadic }] [] [] [.param "a"])] [.call (.resolve "F") (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.num 3)]))])])
#guard obs case_variadic__p12_3 == "ok raw=L[S[S[1, 2], 3]] n=1"

-- variadic__p12_34: F(a...) = a \n F(((1, 2), (3, 4)))
def case_variadic__p12_34 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .variadic }] [] [] [.param "a"])] [.call (.resolve "F") (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.block (alg [] [] [] [(.num 3), (.num 4)]))]))])])
#guard obs case_variadic__p12_34 == "ok raw=L[S[S[1, 2], S[3, 4]]] n=1"

-- variadic__pe_12: F(a...) = a \n F(((), (1, 2)))
def case_variadic__pe_12 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .variadic }] [] [] [.param "a"])] [.call (.resolve "F") (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.block (alg [] [] [] [(.num 1), (.num 2)]))]))])])
#guard obs case_variadic__pe_12 == "ok raw=L[S[S[], S[1, 2]]] n=1"

-- variadic__ppe1_2: F(a...) = a \n F((((), 1), 2))
def case_variadic__ppe1_2 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .variadic }] [] [] [.param "a"])] [.call (.resolve "F") (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.num 1)])), (.num 2)]))])])
#guard obs case_variadic__ppe1_2 == "ok raw=L[S[S[S[], 1], 2]] n=1"

-- variadic__p12_e: F(a...) = a \n F(((1, 2), ()))
def case_variadic__p12_e : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .variadic }] [] [] [.param "a"])] [.call (.resolve "F") (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.emptySequence 0)]))])])
#guard obs case_variadic__p12_e == "ok raw=L[S[S[1, 2], S[]]] n=1"

-- variadic__ppe: F(a...) = a \n F((()))
def case_variadic__ppe : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .variadic }] [] [] [.param "a"])] [.call (.resolve "F") (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0)]))])])
#guard obs case_variadic__ppe == "ok raw=L[S[]] n=1"

-- variadic__pp1: F(a...) = a \n F(((1)))
def case_variadic__pp1 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .variadic }] [] [] [.param "a"])] [.call (.resolve "F") (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1)]))]))])])
#guard obs case_variadic__pp1 == "ok raw=L[1] n=1"

-- variadic__ppp12: F(a...) = a \n F((((1, 2))))
def case_variadic__ppp12 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .variadic }] [] [] [.param "a"])] [.call (.resolve "F") (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)]))]))]))])])
#guard obs case_variadic__ppp12 == "ok raw=L[S[1, 2]] n=1"

-- variadic__le: F(a...) = a \n F([])
def case_variadic__le : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .variadic }] [] [] [.param "a"])] [.call (.resolve "F") (alg [] [] [] [(.listLiteral [])])])
#guard obs case_variadic__le == "ok raw=L[L[]] n=1"

-- variadic__l7: F(a...) = a \n F([7])
def case_variadic__l7 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .variadic }] [] [] [.param "a"])] [.call (.resolve "F") (alg [] [] [] [(.listLiteral [(.num 7)])])])
#guard obs case_variadic__l7 == "ok raw=L[L[7]] n=1"

-- variadic__l12: F(a...) = a \n F([1, 2])
def case_variadic__l12 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .variadic }] [] [] [.param "a"])] [.call (.resolve "F") (alg [] [] [] [(.listLiteral [(.num 1), (.num 2)])])])
#guard obs case_variadic__l12 == "ok raw=L[L[1, 2]] n=1"

-- variadic__l12_3: F(a...) = a \n F([[1, 2], 3])
def case_variadic__l12_3 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .variadic }] [] [] [.param "a"])] [.call (.resolve "F") (alg [] [] [] [(.listLiteral [(.listLiteral [(.num 1), (.num 2)]), (.num 3)])])])
#guard obs case_variadic__l12_3 == "ok raw=L[L[L[1, 2], 3]] n=1"

-- variadic__lle: F(a...) = a \n F([[]])
def case_variadic__lle : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .variadic }] [] [] [.param "a"])] [.call (.resolve "F") (alg [] [] [] [(.listLiteral [(.listLiteral [])])])])
#guard obs case_variadic__lle == "ok raw=L[L[L[]]] n=1"

-- variadic__l_e: F(a...) = a \n F([()])
def case_variadic__l_e : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .variadic }] [] [] [.param "a"])] [.call (.resolve "F") (alg [] [] [] [(.listLiteral [(.emptySequence 0)])])])
#guard obs case_variadic__l_e == "ok raw=L[L[S[]]] n=1"

-- variadic__l_p12: F(a...) = a \n F([(1, 2)])
def case_variadic__l_p12 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .variadic }] [] [] [.param "a"])] [.call (.resolve "F") (alg [] [] [] [(.listLiteral [(.block (alg [] [] [] [(.num 1), (.num 2)]))])])])
#guard obs case_variadic__l_p12 == "ok raw=L[L[S[1, 2]]] n=1"

-- variadic__p_l12: F(a...) = a \n F(([1, 2], 3))
def case_variadic__p_l12 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .variadic }] [] [] [.param "a"])] [.call (.resolve "F") (alg [] [] [] [(.block (alg [] [] [] [(.listLiteral [(.num 1), (.num 2)]), (.num 3)]))])])
#guard obs case_variadic__p_l12 == "ok raw=L[S[L[1, 2], 3]] n=1"

-- variadic__pl1: F(a...) = a \n F(([1]))
def case_variadic__pl1 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .variadic }] [] [] [.param "a"])] [.call (.resolve "F") (alg [] [] [] [(.block (alg [] [] [] [(.listLiteral [(.num 1)])]))])])
#guard obs case_variadic__pl1 == "ok raw=L[L[1]] n=1"

-- variadicSpread__e: F(a...) = a \n F(spread(()))
def case_variadicSpread__e : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .variadic }] [] [] [.param "a"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.emptySequence 0)])])
#guard obs case_variadicSpread__e == "ok raw=L[] n=1"

-- variadicSpread__n0: F(a...) = a \n F(spread(0))
def case_variadicSpread__n0 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .variadic }] [] [] [.param "a"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.num 0)])])
#guard obs case_variadicSpread__n0 == "ok raw=L[0] n=1"

-- variadicSpread__n1: F(a...) = a \n F(spread(1))
def case_variadicSpread__n1 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .variadic }] [] [] [.param "a"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.num 1)])])
#guard obs case_variadicSpread__n1 == "ok raw=L[1] n=1"

-- variadicSpread__p1: F(a...) = a \n F(spread((1)))
def case_variadicSpread__p1 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .variadic }] [] [] [.param "a"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.num 1)]))])])
#guard obs case_variadicSpread__p1 == "ok raw=L[1] n=1"

-- variadicSpread__p12: F(a...) = a \n F(spread((1, 2)))
def case_variadicSpread__p12 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .variadic }] [] [] [.param "a"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.num 1), (.num 2)]))])])
#guard obs case_variadicSpread__p12 == "ok raw=L[1, 2] n=1"

-- variadicSpread__p123: F(a...) = a \n F(spread((1, 2, 3)))
def case_variadicSpread__p123 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .variadic }] [] [] [.param "a"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.num 1), (.num 2), (.num 3)]))])])
#guard obs case_variadicSpread__p123 == "ok raw=L[1, 2, 3] n=1"

-- variadicSpread__pee: F(a...) = a \n F(spread(((), ())))
def case_variadicSpread__pee : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .variadic }] [] [] [.param "a"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.emptySequence 0), (.emptySequence 0)]))])])
#guard obs case_variadicSpread__pee == "ok raw=L[S[], S[]] n=1"

-- variadicSpread__pe1: F(a...) = a \n F(spread(((), 1)))
def case_variadicSpread__pe1 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .variadic }] [] [] [.param "a"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.emptySequence 0), (.num 1)]))])])
#guard obs case_variadicSpread__pe1 == "ok raw=L[S[], 1] n=1"

-- variadicSpread__p1e: F(a...) = a \n F(spread((1, ())))
def case_variadicSpread__p1e : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .variadic }] [] [] [.param "a"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.num 1), (.emptySequence 0)]))])])
#guard obs case_variadicSpread__p1e == "ok raw=L[1, S[]] n=1"

-- variadicSpread__p12_3: F(a...) = a \n F(spread(((1, 2), 3)))
def case_variadicSpread__p12_3 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .variadic }] [] [] [.param "a"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.num 3)]))])])
#guard obs case_variadicSpread__p12_3 == "ok raw=L[S[1, 2], 3] n=1"

-- variadicSpread__p12_34: F(a...) = a \n F(spread(((1, 2), (3, 4))))
def case_variadicSpread__p12_34 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .variadic }] [] [] [.param "a"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.block (alg [] [] [] [(.num 3), (.num 4)]))]))])])
#guard obs case_variadicSpread__p12_34 == "ok raw=L[S[1, 2], S[3, 4]] n=1"

-- variadicSpread__pe_12: F(a...) = a \n F(spread(((), (1, 2))))
def case_variadicSpread__pe_12 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .variadic }] [] [] [.param "a"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.emptySequence 0), (.block (alg [] [] [] [(.num 1), (.num 2)]))]))])])
#guard obs case_variadicSpread__pe_12 == "ok raw=L[S[], S[1, 2]] n=1"

-- variadicSpread__ppe1_2: F(a...) = a \n F(spread((((), 1), 2)))
def case_variadicSpread__ppe1_2 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .variadic }] [] [] [.param "a"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.num 1)])), (.num 2)]))])])
#guard obs case_variadicSpread__ppe1_2 == "ok raw=L[S[S[], 1], 2] n=1"

-- variadicSpread__p12_e: F(a...) = a \n F(spread(((1, 2), ())))
def case_variadicSpread__p12_e : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .variadic }] [] [] [.param "a"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.emptySequence 0)]))])])
#guard obs case_variadicSpread__p12_e == "ok raw=L[S[1, 2], S[]] n=1"

-- variadicSpread__ppe: F(a...) = a \n F(spread((())))
def case_variadicSpread__ppe : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .variadic }] [] [] [.param "a"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.emptySequence 0)]))])])
#guard obs case_variadicSpread__ppe == "ok raw=L[] n=1"

-- variadicSpread__pp1: F(a...) = a \n F(spread(((1))))
def case_variadicSpread__pp1 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .variadic }] [] [] [.param "a"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1)]))]))])])
#guard obs case_variadicSpread__pp1 == "ok raw=L[1] n=1"

-- variadicSpread__ppp12: F(a...) = a \n F(spread((((1, 2)))))
def case_variadicSpread__ppp12 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .variadic }] [] [] [.param "a"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)]))]))]))])])
#guard obs case_variadicSpread__ppp12 == "ok raw=L[1, 2] n=1"

-- variadicSpread__le: F(a...) = a \n F(spread([]))
def case_variadicSpread__le : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .variadic }] [] [] [.param "a"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.listLiteral [])])])
#guard obs case_variadicSpread__le == "ok raw=L[] n=1"

-- variadicSpread__l7: F(a...) = a \n F(spread([7]))
def case_variadicSpread__l7 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .variadic }] [] [] [.param "a"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.listLiteral [(.num 7)])])])
#guard obs case_variadicSpread__l7 == "ok raw=L[7] n=1"

-- variadicSpread__l12: F(a...) = a \n F(spread([1, 2]))
def case_variadicSpread__l12 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .variadic }] [] [] [.param "a"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.listLiteral [(.num 1), (.num 2)])])])
#guard obs case_variadicSpread__l12 == "ok raw=L[1, 2] n=1"

-- variadicSpread__l12_3: F(a...) = a \n F(spread([[1, 2], 3]))
def case_variadicSpread__l12_3 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .variadic }] [] [] [.param "a"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.listLiteral [(.listLiteral [(.num 1), (.num 2)]), (.num 3)])])])
#guard obs case_variadicSpread__l12_3 == "ok raw=L[L[1, 2], 3] n=1"

-- variadicSpread__lle: F(a...) = a \n F(spread([[]]))
def case_variadicSpread__lle : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .variadic }] [] [] [.param "a"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.listLiteral [(.listLiteral [])])])])
#guard obs case_variadicSpread__lle == "ok raw=L[L[]] n=1"

-- variadicSpread__l_e: F(a...) = a \n F(spread([()]))
def case_variadicSpread__l_e : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .variadic }] [] [] [.param "a"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.listLiteral [(.emptySequence 0)])])])
#guard obs case_variadicSpread__l_e == "ok raw=L[S[]] n=1"

-- variadicSpread__l_p12: F(a...) = a \n F(spread([(1, 2)]))
def case_variadicSpread__l_p12 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .variadic }] [] [] [.param "a"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.listLiteral [(.block (alg [] [] [] [(.num 1), (.num 2)]))])])])
#guard obs case_variadicSpread__l_p12 == "ok raw=L[S[1, 2]] n=1"

-- variadicSpread__p_l12: F(a...) = a \n F(spread(([1, 2], 3)))
def case_variadicSpread__p_l12 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .variadic }] [] [] [.param "a"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.listLiteral [(.num 1), (.num 2)]), (.num 3)]))])])
#guard obs case_variadicSpread__p_l12 == "ok raw=L[L[1, 2], 3] n=1"

-- variadicSpread__pl1: F(a...) = a \n F(spread(([1])))
def case_variadicSpread__pl1 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .variadic }] [] [] [.param "a"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.listLiteral [(.num 1)])]))])])
#guard obs case_variadicSpread__pl1 == "ok raw=L[1] n=1"

-- variadicViaProp__e: F(a...) = a \n x = () \n F(x)
def case_variadicViaProp__e : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .variadic }] [] [] [.param "a"]), privateProp "x" (alg [] [] [] [(.emptySequence 0)])] [.call (.resolve "F") (alg [] [] [] [.resolve "x"])])
#guard obs case_variadicViaProp__e == "ok raw=L[S[]] n=1"

-- variadicViaProp__n0: F(a...) = a \n x = 0 \n F(x)
def case_variadicViaProp__n0 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .variadic }] [] [] [.param "a"]), privateProp "x" (alg [] [] [] [(.num 0)])] [.call (.resolve "F") (alg [] [] [] [.resolve "x"])])
#guard obs case_variadicViaProp__n0 == "ok raw=L[0] n=1"

-- variadicViaProp__n1: F(a...) = a \n x = 1 \n F(x)
def case_variadicViaProp__n1 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .variadic }] [] [] [.param "a"]), privateProp "x" (alg [] [] [] [(.num 1)])] [.call (.resolve "F") (alg [] [] [] [.resolve "x"])])
#guard obs case_variadicViaProp__n1 == "ok raw=L[1] n=1"

-- variadicViaProp__p1: F(a...) = a \n x = (1) \n F(x)
def case_variadicViaProp__p1 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .variadic }] [] [] [.param "a"]), privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.num 1)]))])] [.call (.resolve "F") (alg [] [] [] [.resolve "x"])])
#guard obs case_variadicViaProp__p1 == "ok raw=L[1] n=1"

-- variadicViaProp__p12: F(a...) = a \n x = (1, 2) \n F(x)
def case_variadicViaProp__p12 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .variadic }] [] [] [.param "a"]), privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)]))])] [.call (.resolve "F") (alg [] [] [] [.resolve "x"])])
#guard obs case_variadicViaProp__p12 == "ok raw=L[S[1, 2]] n=1"

-- variadicViaProp__p123: F(a...) = a \n x = (1, 2, 3) \n F(x)
def case_variadicViaProp__p123 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .variadic }] [] [] [.param "a"]), privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2), (.num 3)]))])] [.call (.resolve "F") (alg [] [] [] [.resolve "x"])])
#guard obs case_variadicViaProp__p123 == "ok raw=L[S[1, 2, 3]] n=1"

-- variadicViaProp__pee: F(a...) = a \n x = ((), ()) \n F(x)
def case_variadicViaProp__pee : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .variadic }] [] [] [.param "a"]), privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.emptySequence 0)]))])] [.call (.resolve "F") (alg [] [] [] [.resolve "x"])])
#guard obs case_variadicViaProp__pee == "ok raw=L[S[S[], S[]]] n=1"

-- variadicViaProp__pe1: F(a...) = a \n x = ((), 1) \n F(x)
def case_variadicViaProp__pe1 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .variadic }] [] [] [.param "a"]), privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.num 1)]))])] [.call (.resolve "F") (alg [] [] [] [.resolve "x"])])
#guard obs case_variadicViaProp__pe1 == "ok raw=L[S[S[], 1]] n=1"

-- variadicViaProp__p1e: F(a...) = a \n x = (1, ()) \n F(x)
def case_variadicViaProp__p1e : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .variadic }] [] [] [.param "a"]), privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.emptySequence 0)]))])] [.call (.resolve "F") (alg [] [] [] [.resolve "x"])])
#guard obs case_variadicViaProp__p1e == "ok raw=L[S[1, S[]]] n=1"

-- variadicViaProp__p12_3: F(a...) = a \n x = ((1, 2), 3) \n F(x)
def case_variadicViaProp__p12_3 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .variadic }] [] [] [.param "a"]), privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.num 3)]))])] [.call (.resolve "F") (alg [] [] [] [.resolve "x"])])
#guard obs case_variadicViaProp__p12_3 == "ok raw=L[S[S[1, 2], 3]] n=1"

-- variadicViaProp__p12_34: F(a...) = a \n x = ((1, 2), (3, 4)) \n F(x)
def case_variadicViaProp__p12_34 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .variadic }] [] [] [.param "a"]), privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.block (alg [] [] [] [(.num 3), (.num 4)]))]))])] [.call (.resolve "F") (alg [] [] [] [.resolve "x"])])
#guard obs case_variadicViaProp__p12_34 == "ok raw=L[S[S[1, 2], S[3, 4]]] n=1"

-- variadicViaProp__pe_12: F(a...) = a \n x = ((), (1, 2)) \n F(x)
def case_variadicViaProp__pe_12 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .variadic }] [] [] [.param "a"]), privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.block (alg [] [] [] [(.num 1), (.num 2)]))]))])] [.call (.resolve "F") (alg [] [] [] [.resolve "x"])])
#guard obs case_variadicViaProp__pe_12 == "ok raw=L[S[S[], S[1, 2]]] n=1"

-- variadicViaProp__ppe1_2: F(a...) = a \n x = (((), 1), 2) \n F(x)
def case_variadicViaProp__ppe1_2 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .variadic }] [] [] [.param "a"]), privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.num 1)])), (.num 2)]))])] [.call (.resolve "F") (alg [] [] [] [.resolve "x"])])
#guard obs case_variadicViaProp__ppe1_2 == "ok raw=L[S[S[S[], 1], 2]] n=1"

-- variadicViaProp__p12_e: F(a...) = a \n x = ((1, 2), ()) \n F(x)
def case_variadicViaProp__p12_e : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .variadic }] [] [] [.param "a"]), privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.emptySequence 0)]))])] [.call (.resolve "F") (alg [] [] [] [.resolve "x"])])
#guard obs case_variadicViaProp__p12_e == "ok raw=L[S[S[1, 2], S[]]] n=1"

-- variadicViaProp__ppe: F(a...) = a \n x = (()) \n F(x)
def case_variadicViaProp__ppe : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .variadic }] [] [] [.param "a"]), privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0)]))])] [.call (.resolve "F") (alg [] [] [] [.resolve "x"])])
#guard obs case_variadicViaProp__ppe == "ok raw=L[S[]] n=1"

-- variadicViaProp__pp1: F(a...) = a \n x = ((1)) \n F(x)
def case_variadicViaProp__pp1 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .variadic }] [] [] [.param "a"]), privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1)]))]))])] [.call (.resolve "F") (alg [] [] [] [.resolve "x"])])
#guard obs case_variadicViaProp__pp1 == "ok raw=L[1] n=1"

-- variadicViaProp__ppp12: F(a...) = a \n x = (((1, 2))) \n F(x)
def case_variadicViaProp__ppp12 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .variadic }] [] [] [.param "a"]), privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)]))]))]))])] [.call (.resolve "F") (alg [] [] [] [.resolve "x"])])
#guard obs case_variadicViaProp__ppp12 == "ok raw=L[S[1, 2]] n=1"

-- variadicViaProp__le: F(a...) = a \n x = [] \n F(x)
def case_variadicViaProp__le : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .variadic }] [] [] [.param "a"]), privateProp "x" (alg [] [] [] [(.listLiteral [])])] [.call (.resolve "F") (alg [] [] [] [.resolve "x"])])
#guard obs case_variadicViaProp__le == "ok raw=L[L[]] n=1"

-- variadicViaProp__l7: F(a...) = a \n x = [7] \n F(x)
def case_variadicViaProp__l7 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .variadic }] [] [] [.param "a"]), privateProp "x" (alg [] [] [] [(.listLiteral [(.num 7)])])] [.call (.resolve "F") (alg [] [] [] [.resolve "x"])])
#guard obs case_variadicViaProp__l7 == "ok raw=L[L[7]] n=1"

-- variadicViaProp__l12: F(a...) = a \n x = [1, 2] \n F(x)
def case_variadicViaProp__l12 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .variadic }] [] [] [.param "a"]), privateProp "x" (alg [] [] [] [(.listLiteral [(.num 1), (.num 2)])])] [.call (.resolve "F") (alg [] [] [] [.resolve "x"])])
#guard obs case_variadicViaProp__l12 == "ok raw=L[L[1, 2]] n=1"

-- variadicViaProp__l12_3: F(a...) = a \n x = [[1, 2], 3] \n F(x)
def case_variadicViaProp__l12_3 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .variadic }] [] [] [.param "a"]), privateProp "x" (alg [] [] [] [(.listLiteral [(.listLiteral [(.num 1), (.num 2)]), (.num 3)])])] [.call (.resolve "F") (alg [] [] [] [.resolve "x"])])
#guard obs case_variadicViaProp__l12_3 == "ok raw=L[L[L[1, 2], 3]] n=1"

-- variadicViaProp__lle: F(a...) = a \n x = [[]] \n F(x)
def case_variadicViaProp__lle : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .variadic }] [] [] [.param "a"]), privateProp "x" (alg [] [] [] [(.listLiteral [(.listLiteral [])])])] [.call (.resolve "F") (alg [] [] [] [.resolve "x"])])
#guard obs case_variadicViaProp__lle == "ok raw=L[L[L[]]] n=1"

-- variadicViaProp__l_e: F(a...) = a \n x = [()] \n F(x)
def case_variadicViaProp__l_e : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .variadic }] [] [] [.param "a"]), privateProp "x" (alg [] [] [] [(.listLiteral [(.emptySequence 0)])])] [.call (.resolve "F") (alg [] [] [] [.resolve "x"])])
#guard obs case_variadicViaProp__l_e == "ok raw=L[L[S[]]] n=1"

-- variadicViaProp__l_p12: F(a...) = a \n x = [(1, 2)] \n F(x)
def case_variadicViaProp__l_p12 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .variadic }] [] [] [.param "a"]), privateProp "x" (alg [] [] [] [(.listLiteral [(.block (alg [] [] [] [(.num 1), (.num 2)]))])])] [.call (.resolve "F") (alg [] [] [] [.resolve "x"])])
#guard obs case_variadicViaProp__l_p12 == "ok raw=L[L[S[1, 2]]] n=1"

-- variadicViaProp__p_l12: F(a...) = a \n x = ([1, 2], 3) \n F(x)
def case_variadicViaProp__p_l12 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .variadic }] [] [] [.param "a"]), privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.listLiteral [(.num 1), (.num 2)]), (.num 3)]))])] [.call (.resolve "F") (alg [] [] [] [.resolve "x"])])
#guard obs case_variadicViaProp__p_l12 == "ok raw=L[S[L[1, 2], 3]] n=1"

-- variadicViaProp__pl1: F(a...) = a \n x = ([1]) \n F(x)
def case_variadicViaProp__pl1 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .variadic }] [] [] [.param "a"]), privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.listLiteral [(.num 1)])]))])] [.call (.resolve "F") (alg [] [] [] [.resolve "x"])])
#guard obs case_variadicViaProp__pl1 == "ok raw=L[L[1]] n=1"

-- mixed_h__e: F(h, t...) = h \n F(spread(()))
def case_mixed_h__e : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "h" }, { name := "t", kind := .variadic }] [] [] [.param "h"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.emptySequence 0)])])
#guard obs case_mixed_h__e == "err arity"

-- mixed_h__n0: F(h, t...) = h \n F(spread(0))
def case_mixed_h__n0 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "h" }, { name := "t", kind := .variadic }] [] [] [.param "h"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.num 0)])])
#guard obs case_mixed_h__n0 == "ok raw=0 n=1"

-- mixed_h__n1: F(h, t...) = h \n F(spread(1))
def case_mixed_h__n1 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "h" }, { name := "t", kind := .variadic }] [] [] [.param "h"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.num 1)])])
#guard obs case_mixed_h__n1 == "ok raw=1 n=1"

-- mixed_h__p1: F(h, t...) = h \n F(spread((1)))
def case_mixed_h__p1 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "h" }, { name := "t", kind := .variadic }] [] [] [.param "h"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.num 1)]))])])
#guard obs case_mixed_h__p1 == "ok raw=1 n=1"

-- mixed_h__p12: F(h, t...) = h \n F(spread((1, 2)))
def case_mixed_h__p12 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "h" }, { name := "t", kind := .variadic }] [] [] [.param "h"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.num 1), (.num 2)]))])])
#guard obs case_mixed_h__p12 == "ok raw=1 n=1"

-- mixed_h__p123: F(h, t...) = h \n F(spread((1, 2, 3)))
def case_mixed_h__p123 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "h" }, { name := "t", kind := .variadic }] [] [] [.param "h"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.num 1), (.num 2), (.num 3)]))])])
#guard obs case_mixed_h__p123 == "ok raw=1 n=1"

-- mixed_h__pee: F(h, t...) = h \n F(spread(((), ())))
def case_mixed_h__pee : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "h" }, { name := "t", kind := .variadic }] [] [] [.param "h"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.emptySequence 0), (.emptySequence 0)]))])])
#guard obs case_mixed_h__pee == "ok raw=S[] n=1"

-- mixed_h__pe1: F(h, t...) = h \n F(spread(((), 1)))
def case_mixed_h__pe1 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "h" }, { name := "t", kind := .variadic }] [] [] [.param "h"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.emptySequence 0), (.num 1)]))])])
#guard obs case_mixed_h__pe1 == "ok raw=S[] n=1"

-- mixed_h__p1e: F(h, t...) = h \n F(spread((1, ())))
def case_mixed_h__p1e : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "h" }, { name := "t", kind := .variadic }] [] [] [.param "h"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.num 1), (.emptySequence 0)]))])])
#guard obs case_mixed_h__p1e == "ok raw=1 n=1"

-- mixed_h__p12_3: F(h, t...) = h \n F(spread(((1, 2), 3)))
def case_mixed_h__p12_3 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "h" }, { name := "t", kind := .variadic }] [] [] [.param "h"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.num 3)]))])])
#guard obs case_mixed_h__p12_3 == "ok raw=S[1, 2] n=1"

-- mixed_h__p12_34: F(h, t...) = h \n F(spread(((1, 2), (3, 4))))
def case_mixed_h__p12_34 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "h" }, { name := "t", kind := .variadic }] [] [] [.param "h"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.block (alg [] [] [] [(.num 3), (.num 4)]))]))])])
#guard obs case_mixed_h__p12_34 == "ok raw=S[1, 2] n=1"

-- mixed_h__pe_12: F(h, t...) = h \n F(spread(((), (1, 2))))
def case_mixed_h__pe_12 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "h" }, { name := "t", kind := .variadic }] [] [] [.param "h"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.emptySequence 0), (.block (alg [] [] [] [(.num 1), (.num 2)]))]))])])
#guard obs case_mixed_h__pe_12 == "ok raw=S[] n=1"

-- mixed_h__ppe1_2: F(h, t...) = h \n F(spread((((), 1), 2)))
def case_mixed_h__ppe1_2 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "h" }, { name := "t", kind := .variadic }] [] [] [.param "h"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.num 1)])), (.num 2)]))])])
#guard obs case_mixed_h__ppe1_2 == "ok raw=S[S[], 1] n=1"

-- mixed_h__p12_e: F(h, t...) = h \n F(spread(((1, 2), ())))
def case_mixed_h__p12_e : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "h" }, { name := "t", kind := .variadic }] [] [] [.param "h"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.emptySequence 0)]))])])
#guard obs case_mixed_h__p12_e == "ok raw=S[1, 2] n=1"

-- mixed_h__ppe: F(h, t...) = h \n F(spread((())))
def case_mixed_h__ppe : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "h" }, { name := "t", kind := .variadic }] [] [] [.param "h"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.emptySequence 0)]))])])
#guard obs case_mixed_h__ppe == "err arity"

-- mixed_h__pp1: F(h, t...) = h \n F(spread(((1))))
def case_mixed_h__pp1 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "h" }, { name := "t", kind := .variadic }] [] [] [.param "h"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1)]))]))])])
#guard obs case_mixed_h__pp1 == "ok raw=1 n=1"

-- mixed_h__ppp12: F(h, t...) = h \n F(spread((((1, 2)))))
def case_mixed_h__ppp12 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "h" }, { name := "t", kind := .variadic }] [] [] [.param "h"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)]))]))]))])])
#guard obs case_mixed_h__ppp12 == "ok raw=1 n=1"

-- mixed_h__le: F(h, t...) = h \n F(spread([]))
def case_mixed_h__le : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "h" }, { name := "t", kind := .variadic }] [] [] [.param "h"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.listLiteral [])])])
#guard obs case_mixed_h__le == "err arity"

-- mixed_h__l7: F(h, t...) = h \n F(spread([7]))
def case_mixed_h__l7 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "h" }, { name := "t", kind := .variadic }] [] [] [.param "h"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.listLiteral [(.num 7)])])])
#guard obs case_mixed_h__l7 == "ok raw=7 n=1"

-- mixed_h__l12: F(h, t...) = h \n F(spread([1, 2]))
def case_mixed_h__l12 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "h" }, { name := "t", kind := .variadic }] [] [] [.param "h"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.listLiteral [(.num 1), (.num 2)])])])
#guard obs case_mixed_h__l12 == "ok raw=1 n=1"

-- mixed_h__l12_3: F(h, t...) = h \n F(spread([[1, 2], 3]))
def case_mixed_h__l12_3 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "h" }, { name := "t", kind := .variadic }] [] [] [.param "h"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.listLiteral [(.listLiteral [(.num 1), (.num 2)]), (.num 3)])])])
#guard obs case_mixed_h__l12_3 == "ok raw=L[1, 2] n=1"

-- mixed_h__lle: F(h, t...) = h \n F(spread([[]]))
def case_mixed_h__lle : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "h" }, { name := "t", kind := .variadic }] [] [] [.param "h"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.listLiteral [(.listLiteral [])])])])
#guard obs case_mixed_h__lle == "ok raw=L[] n=1"

-- mixed_h__l_e: F(h, t...) = h \n F(spread([()]))
def case_mixed_h__l_e : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "h" }, { name := "t", kind := .variadic }] [] [] [.param "h"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.listLiteral [(.emptySequence 0)])])])
#guard obs case_mixed_h__l_e == "ok raw=S[] n=1"

-- mixed_h__l_p12: F(h, t...) = h \n F(spread([(1, 2)]))
def case_mixed_h__l_p12 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "h" }, { name := "t", kind := .variadic }] [] [] [.param "h"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.listLiteral [(.block (alg [] [] [] [(.num 1), (.num 2)]))])])])
#guard obs case_mixed_h__l_p12 == "ok raw=S[1, 2] n=1"

-- mixed_h__p_l12: F(h, t...) = h \n F(spread(([1, 2], 3)))
def case_mixed_h__p_l12 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "h" }, { name := "t", kind := .variadic }] [] [] [.param "h"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.listLiteral [(.num 1), (.num 2)]), (.num 3)]))])])
#guard obs case_mixed_h__p_l12 == "ok raw=L[1, 2] n=1"

-- mixed_h__pl1: F(h, t...) = h \n F(spread(([1])))
def case_mixed_h__pl1 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "h" }, { name := "t", kind := .variadic }] [] [] [.param "h"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.listLiteral [(.num 1)])]))])])
#guard obs case_mixed_h__pl1 == "ok raw=1 n=1"

-- mixed_t__e: F(h, t...) = t \n F(spread(()))
def case_mixed_t__e : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "h" }, { name := "t", kind := .variadic }] [] [] [.param "t"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.emptySequence 0)])])
#guard obs case_mixed_t__e == "err arity"

-- mixed_t__n0: F(h, t...) = t \n F(spread(0))
def case_mixed_t__n0 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "h" }, { name := "t", kind := .variadic }] [] [] [.param "t"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.num 0)])])
#guard obs case_mixed_t__n0 == "ok raw=L[] n=1"

-- mixed_t__n1: F(h, t...) = t \n F(spread(1))
def case_mixed_t__n1 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "h" }, { name := "t", kind := .variadic }] [] [] [.param "t"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.num 1)])])
#guard obs case_mixed_t__n1 == "ok raw=L[] n=1"

-- mixed_t__p1: F(h, t...) = t \n F(spread((1)))
def case_mixed_t__p1 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "h" }, { name := "t", kind := .variadic }] [] [] [.param "t"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.num 1)]))])])
#guard obs case_mixed_t__p1 == "ok raw=L[] n=1"

-- mixed_t__p12: F(h, t...) = t \n F(spread((1, 2)))
def case_mixed_t__p12 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "h" }, { name := "t", kind := .variadic }] [] [] [.param "t"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.num 1), (.num 2)]))])])
#guard obs case_mixed_t__p12 == "ok raw=L[2] n=1"

-- mixed_t__p123: F(h, t...) = t \n F(spread((1, 2, 3)))
def case_mixed_t__p123 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "h" }, { name := "t", kind := .variadic }] [] [] [.param "t"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.num 1), (.num 2), (.num 3)]))])])
#guard obs case_mixed_t__p123 == "ok raw=L[2, 3] n=1"

-- mixed_t__pee: F(h, t...) = t \n F(spread(((), ())))
def case_mixed_t__pee : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "h" }, { name := "t", kind := .variadic }] [] [] [.param "t"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.emptySequence 0), (.emptySequence 0)]))])])
#guard obs case_mixed_t__pee == "ok raw=L[S[]] n=1"

-- mixed_t__pe1: F(h, t...) = t \n F(spread(((), 1)))
def case_mixed_t__pe1 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "h" }, { name := "t", kind := .variadic }] [] [] [.param "t"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.emptySequence 0), (.num 1)]))])])
#guard obs case_mixed_t__pe1 == "ok raw=L[1] n=1"

-- mixed_t__p1e: F(h, t...) = t \n F(spread((1, ())))
def case_mixed_t__p1e : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "h" }, { name := "t", kind := .variadic }] [] [] [.param "t"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.num 1), (.emptySequence 0)]))])])
#guard obs case_mixed_t__p1e == "ok raw=L[S[]] n=1"

-- mixed_t__p12_3: F(h, t...) = t \n F(spread(((1, 2), 3)))
def case_mixed_t__p12_3 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "h" }, { name := "t", kind := .variadic }] [] [] [.param "t"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.num 3)]))])])
#guard obs case_mixed_t__p12_3 == "ok raw=L[3] n=1"

-- mixed_t__p12_34: F(h, t...) = t \n F(spread(((1, 2), (3, 4))))
def case_mixed_t__p12_34 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "h" }, { name := "t", kind := .variadic }] [] [] [.param "t"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.block (alg [] [] [] [(.num 3), (.num 4)]))]))])])
#guard obs case_mixed_t__p12_34 == "ok raw=L[S[3, 4]] n=1"

-- mixed_t__pe_12: F(h, t...) = t \n F(spread(((), (1, 2))))
def case_mixed_t__pe_12 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "h" }, { name := "t", kind := .variadic }] [] [] [.param "t"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.emptySequence 0), (.block (alg [] [] [] [(.num 1), (.num 2)]))]))])])
#guard obs case_mixed_t__pe_12 == "ok raw=L[S[1, 2]] n=1"

-- mixed_t__ppe1_2: F(h, t...) = t \n F(spread((((), 1), 2)))
def case_mixed_t__ppe1_2 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "h" }, { name := "t", kind := .variadic }] [] [] [.param "t"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.num 1)])), (.num 2)]))])])
#guard obs case_mixed_t__ppe1_2 == "ok raw=L[2] n=1"

-- mixed_t__p12_e: F(h, t...) = t \n F(spread(((1, 2), ())))
def case_mixed_t__p12_e : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "h" }, { name := "t", kind := .variadic }] [] [] [.param "t"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.emptySequence 0)]))])])
#guard obs case_mixed_t__p12_e == "ok raw=L[S[]] n=1"

-- mixed_t__ppe: F(h, t...) = t \n F(spread((())))
def case_mixed_t__ppe : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "h" }, { name := "t", kind := .variadic }] [] [] [.param "t"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.emptySequence 0)]))])])
#guard obs case_mixed_t__ppe == "err arity"

-- mixed_t__pp1: F(h, t...) = t \n F(spread(((1))))
def case_mixed_t__pp1 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "h" }, { name := "t", kind := .variadic }] [] [] [.param "t"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1)]))]))])])
#guard obs case_mixed_t__pp1 == "ok raw=L[] n=1"

-- mixed_t__ppp12: F(h, t...) = t \n F(spread((((1, 2)))))
def case_mixed_t__ppp12 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "h" }, { name := "t", kind := .variadic }] [] [] [.param "t"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)]))]))]))])])
#guard obs case_mixed_t__ppp12 == "ok raw=L[2] n=1"

-- mixed_t__le: F(h, t...) = t \n F(spread([]))
def case_mixed_t__le : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "h" }, { name := "t", kind := .variadic }] [] [] [.param "t"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.listLiteral [])])])
#guard obs case_mixed_t__le == "err arity"

-- mixed_t__l7: F(h, t...) = t \n F(spread([7]))
def case_mixed_t__l7 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "h" }, { name := "t", kind := .variadic }] [] [] [.param "t"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.listLiteral [(.num 7)])])])
#guard obs case_mixed_t__l7 == "ok raw=L[] n=1"

-- mixed_t__l12: F(h, t...) = t \n F(spread([1, 2]))
def case_mixed_t__l12 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "h" }, { name := "t", kind := .variadic }] [] [] [.param "t"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.listLiteral [(.num 1), (.num 2)])])])
#guard obs case_mixed_t__l12 == "ok raw=L[2] n=1"

-- mixed_t__l12_3: F(h, t...) = t \n F(spread([[1, 2], 3]))
def case_mixed_t__l12_3 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "h" }, { name := "t", kind := .variadic }] [] [] [.param "t"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.listLiteral [(.listLiteral [(.num 1), (.num 2)]), (.num 3)])])])
#guard obs case_mixed_t__l12_3 == "ok raw=L[3] n=1"

-- mixed_t__lle: F(h, t...) = t \n F(spread([[]]))
def case_mixed_t__lle : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "h" }, { name := "t", kind := .variadic }] [] [] [.param "t"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.listLiteral [(.listLiteral [])])])])
#guard obs case_mixed_t__lle == "ok raw=L[] n=1"

-- mixed_t__l_e: F(h, t...) = t \n F(spread([()]))
def case_mixed_t__l_e : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "h" }, { name := "t", kind := .variadic }] [] [] [.param "t"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.listLiteral [(.emptySequence 0)])])])
#guard obs case_mixed_t__l_e == "ok raw=L[] n=1"

-- mixed_t__l_p12: F(h, t...) = t \n F(spread([(1, 2)]))
def case_mixed_t__l_p12 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "h" }, { name := "t", kind := .variadic }] [] [] [.param "t"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.listLiteral [(.block (alg [] [] [] [(.num 1), (.num 2)]))])])])
#guard obs case_mixed_t__l_p12 == "ok raw=L[] n=1"

-- mixed_t__p_l12: F(h, t...) = t \n F(spread(([1, 2], 3)))
def case_mixed_t__p_l12 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "h" }, { name := "t", kind := .variadic }] [] [] [.param "t"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.listLiteral [(.num 1), (.num 2)]), (.num 3)]))])])
#guard obs case_mixed_t__p_l12 == "ok raw=L[3] n=1"

-- mixed_t__pl1: F(h, t...) = t \n F(spread(([1])))
def case_mixed_t__pl1 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "h" }, { name := "t", kind := .variadic }] [] [] [.param "t"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.listLiteral [(.num 1)])]))])])
#guard obs case_mixed_t__pl1 == "ok raw=L[] n=1"

-- mixedBack_t__e: F(t..., z) = t \n F(spread(()))
def case_mixedBack_t__e : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "t", kind := .variadic }, { name := "z" }] [] [] [.param "t"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.emptySequence 0)])])
#guard obs case_mixedBack_t__e == "err arity"

-- mixedBack_t__n0: F(t..., z) = t \n F(spread(0))
def case_mixedBack_t__n0 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "t", kind := .variadic }, { name := "z" }] [] [] [.param "t"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.num 0)])])
#guard obs case_mixedBack_t__n0 == "ok raw=L[] n=1"

-- mixedBack_t__n1: F(t..., z) = t \n F(spread(1))
def case_mixedBack_t__n1 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "t", kind := .variadic }, { name := "z" }] [] [] [.param "t"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.num 1)])])
#guard obs case_mixedBack_t__n1 == "ok raw=L[] n=1"

-- mixedBack_t__p1: F(t..., z) = t \n F(spread((1)))
def case_mixedBack_t__p1 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "t", kind := .variadic }, { name := "z" }] [] [] [.param "t"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.num 1)]))])])
#guard obs case_mixedBack_t__p1 == "ok raw=L[] n=1"

-- mixedBack_t__p12: F(t..., z) = t \n F(spread((1, 2)))
def case_mixedBack_t__p12 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "t", kind := .variadic }, { name := "z" }] [] [] [.param "t"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.num 1), (.num 2)]))])])
#guard obs case_mixedBack_t__p12 == "ok raw=L[1] n=1"

-- mixedBack_t__p123: F(t..., z) = t \n F(spread((1, 2, 3)))
def case_mixedBack_t__p123 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "t", kind := .variadic }, { name := "z" }] [] [] [.param "t"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.num 1), (.num 2), (.num 3)]))])])
#guard obs case_mixedBack_t__p123 == "ok raw=L[1, 2] n=1"

-- mixedBack_t__pee: F(t..., z) = t \n F(spread(((), ())))
def case_mixedBack_t__pee : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "t", kind := .variadic }, { name := "z" }] [] [] [.param "t"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.emptySequence 0), (.emptySequence 0)]))])])
#guard obs case_mixedBack_t__pee == "ok raw=L[S[]] n=1"

-- mixedBack_t__pe1: F(t..., z) = t \n F(spread(((), 1)))
def case_mixedBack_t__pe1 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "t", kind := .variadic }, { name := "z" }] [] [] [.param "t"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.emptySequence 0), (.num 1)]))])])
#guard obs case_mixedBack_t__pe1 == "ok raw=L[S[]] n=1"

-- mixedBack_t__p1e: F(t..., z) = t \n F(spread((1, ())))
def case_mixedBack_t__p1e : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "t", kind := .variadic }, { name := "z" }] [] [] [.param "t"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.num 1), (.emptySequence 0)]))])])
#guard obs case_mixedBack_t__p1e == "ok raw=L[1] n=1"

-- mixedBack_t__p12_3: F(t..., z) = t \n F(spread(((1, 2), 3)))
def case_mixedBack_t__p12_3 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "t", kind := .variadic }, { name := "z" }] [] [] [.param "t"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.num 3)]))])])
#guard obs case_mixedBack_t__p12_3 == "ok raw=L[S[1, 2]] n=1"

-- mixedBack_t__p12_34: F(t..., z) = t \n F(spread(((1, 2), (3, 4))))
def case_mixedBack_t__p12_34 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "t", kind := .variadic }, { name := "z" }] [] [] [.param "t"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.block (alg [] [] [] [(.num 3), (.num 4)]))]))])])
#guard obs case_mixedBack_t__p12_34 == "ok raw=L[S[1, 2]] n=1"

-- mixedBack_t__pe_12: F(t..., z) = t \n F(spread(((), (1, 2))))
def case_mixedBack_t__pe_12 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "t", kind := .variadic }, { name := "z" }] [] [] [.param "t"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.emptySequence 0), (.block (alg [] [] [] [(.num 1), (.num 2)]))]))])])
#guard obs case_mixedBack_t__pe_12 == "ok raw=L[S[]] n=1"

-- mixedBack_t__ppe1_2: F(t..., z) = t \n F(spread((((), 1), 2)))
def case_mixedBack_t__ppe1_2 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "t", kind := .variadic }, { name := "z" }] [] [] [.param "t"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.num 1)])), (.num 2)]))])])
#guard obs case_mixedBack_t__ppe1_2 == "ok raw=L[S[S[], 1]] n=1"

-- mixedBack_t__p12_e: F(t..., z) = t \n F(spread(((1, 2), ())))
def case_mixedBack_t__p12_e : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "t", kind := .variadic }, { name := "z" }] [] [] [.param "t"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.emptySequence 0)]))])])
#guard obs case_mixedBack_t__p12_e == "ok raw=L[S[1, 2]] n=1"

-- mixedBack_t__ppe: F(t..., z) = t \n F(spread((())))
def case_mixedBack_t__ppe : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "t", kind := .variadic }, { name := "z" }] [] [] [.param "t"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.emptySequence 0)]))])])
#guard obs case_mixedBack_t__ppe == "err arity"

-- mixedBack_t__pp1: F(t..., z) = t \n F(spread(((1))))
def case_mixedBack_t__pp1 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "t", kind := .variadic }, { name := "z" }] [] [] [.param "t"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1)]))]))])])
#guard obs case_mixedBack_t__pp1 == "ok raw=L[] n=1"

-- mixedBack_t__ppp12: F(t..., z) = t \n F(spread((((1, 2)))))
def case_mixedBack_t__ppp12 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "t", kind := .variadic }, { name := "z" }] [] [] [.param "t"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)]))]))]))])])
#guard obs case_mixedBack_t__ppp12 == "ok raw=L[1] n=1"

-- mixedBack_t__le: F(t..., z) = t \n F(spread([]))
def case_mixedBack_t__le : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "t", kind := .variadic }, { name := "z" }] [] [] [.param "t"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.listLiteral [])])])
#guard obs case_mixedBack_t__le == "err arity"

-- mixedBack_t__l7: F(t..., z) = t \n F(spread([7]))
def case_mixedBack_t__l7 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "t", kind := .variadic }, { name := "z" }] [] [] [.param "t"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.listLiteral [(.num 7)])])])
#guard obs case_mixedBack_t__l7 == "ok raw=L[] n=1"

-- mixedBack_t__l12: F(t..., z) = t \n F(spread([1, 2]))
def case_mixedBack_t__l12 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "t", kind := .variadic }, { name := "z" }] [] [] [.param "t"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.listLiteral [(.num 1), (.num 2)])])])
#guard obs case_mixedBack_t__l12 == "ok raw=L[1] n=1"

-- mixedBack_t__l12_3: F(t..., z) = t \n F(spread([[1, 2], 3]))
def case_mixedBack_t__l12_3 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "t", kind := .variadic }, { name := "z" }] [] [] [.param "t"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.listLiteral [(.listLiteral [(.num 1), (.num 2)]), (.num 3)])])])
#guard obs case_mixedBack_t__l12_3 == "ok raw=L[L[1, 2]] n=1"

-- mixedBack_t__lle: F(t..., z) = t \n F(spread([[]]))
def case_mixedBack_t__lle : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "t", kind := .variadic }, { name := "z" }] [] [] [.param "t"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.listLiteral [(.listLiteral [])])])])
#guard obs case_mixedBack_t__lle == "ok raw=L[] n=1"

-- mixedBack_t__l_e: F(t..., z) = t \n F(spread([()]))
def case_mixedBack_t__l_e : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "t", kind := .variadic }, { name := "z" }] [] [] [.param "t"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.listLiteral [(.emptySequence 0)])])])
#guard obs case_mixedBack_t__l_e == "ok raw=L[] n=1"

-- mixedBack_t__l_p12: F(t..., z) = t \n F(spread([(1, 2)]))
def case_mixedBack_t__l_p12 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "t", kind := .variadic }, { name := "z" }] [] [] [.param "t"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.listLiteral [(.block (alg [] [] [] [(.num 1), (.num 2)]))])])])
#guard obs case_mixedBack_t__l_p12 == "ok raw=L[] n=1"

-- mixedBack_t__p_l12: F(t..., z) = t \n F(spread(([1, 2], 3)))
def case_mixedBack_t__p_l12 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "t", kind := .variadic }, { name := "z" }] [] [] [.param "t"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.listLiteral [(.num 1), (.num 2)]), (.num 3)]))])])
#guard obs case_mixedBack_t__p_l12 == "ok raw=L[L[1, 2]] n=1"

-- mixedBack_t__pl1: F(t..., z) = t \n F(spread(([1])))
def case_mixedBack_t__pl1 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "t", kind := .variadic }, { name := "z" }] [] [] [.param "t"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.listLiteral [(.num 1)])]))])])
#guard obs case_mixedBack_t__pl1 == "ok raw=L[] n=1"

-- mixedBack_z__e: F(t..., z) = z \n F(spread(()))
def case_mixedBack_z__e : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "t", kind := .variadic }, { name := "z" }] [] [] [.param "z"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.emptySequence 0)])])
#guard obs case_mixedBack_z__e == "err arity"

-- mixedBack_z__n0: F(t..., z) = z \n F(spread(0))
def case_mixedBack_z__n0 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "t", kind := .variadic }, { name := "z" }] [] [] [.param "z"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.num 0)])])
#guard obs case_mixedBack_z__n0 == "ok raw=0 n=1"

-- mixedBack_z__n1: F(t..., z) = z \n F(spread(1))
def case_mixedBack_z__n1 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "t", kind := .variadic }, { name := "z" }] [] [] [.param "z"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.num 1)])])
#guard obs case_mixedBack_z__n1 == "ok raw=1 n=1"

-- mixedBack_z__p1: F(t..., z) = z \n F(spread((1)))
def case_mixedBack_z__p1 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "t", kind := .variadic }, { name := "z" }] [] [] [.param "z"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.num 1)]))])])
#guard obs case_mixedBack_z__p1 == "ok raw=1 n=1"

-- mixedBack_z__p12: F(t..., z) = z \n F(spread((1, 2)))
def case_mixedBack_z__p12 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "t", kind := .variadic }, { name := "z" }] [] [] [.param "z"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.num 1), (.num 2)]))])])
#guard obs case_mixedBack_z__p12 == "ok raw=2 n=1"

-- mixedBack_z__p123: F(t..., z) = z \n F(spread((1, 2, 3)))
def case_mixedBack_z__p123 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "t", kind := .variadic }, { name := "z" }] [] [] [.param "z"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.num 1), (.num 2), (.num 3)]))])])
#guard obs case_mixedBack_z__p123 == "ok raw=3 n=1"

-- mixedBack_z__pee: F(t..., z) = z \n F(spread(((), ())))
def case_mixedBack_z__pee : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "t", kind := .variadic }, { name := "z" }] [] [] [.param "z"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.emptySequence 0), (.emptySequence 0)]))])])
#guard obs case_mixedBack_z__pee == "ok raw=S[] n=1"

-- mixedBack_z__pe1: F(t..., z) = z \n F(spread(((), 1)))
def case_mixedBack_z__pe1 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "t", kind := .variadic }, { name := "z" }] [] [] [.param "z"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.emptySequence 0), (.num 1)]))])])
#guard obs case_mixedBack_z__pe1 == "ok raw=1 n=1"

-- mixedBack_z__p1e: F(t..., z) = z \n F(spread((1, ())))
def case_mixedBack_z__p1e : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "t", kind := .variadic }, { name := "z" }] [] [] [.param "z"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.num 1), (.emptySequence 0)]))])])
#guard obs case_mixedBack_z__p1e == "ok raw=S[] n=1"

-- mixedBack_z__p12_3: F(t..., z) = z \n F(spread(((1, 2), 3)))
def case_mixedBack_z__p12_3 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "t", kind := .variadic }, { name := "z" }] [] [] [.param "z"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.num 3)]))])])
#guard obs case_mixedBack_z__p12_3 == "ok raw=3 n=1"

-- mixedBack_z__p12_34: F(t..., z) = z \n F(spread(((1, 2), (3, 4))))
def case_mixedBack_z__p12_34 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "t", kind := .variadic }, { name := "z" }] [] [] [.param "z"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.block (alg [] [] [] [(.num 3), (.num 4)]))]))])])
#guard obs case_mixedBack_z__p12_34 == "ok raw=S[3, 4] n=1"

-- mixedBack_z__pe_12: F(t..., z) = z \n F(spread(((), (1, 2))))
def case_mixedBack_z__pe_12 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "t", kind := .variadic }, { name := "z" }] [] [] [.param "z"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.emptySequence 0), (.block (alg [] [] [] [(.num 1), (.num 2)]))]))])])
#guard obs case_mixedBack_z__pe_12 == "ok raw=S[1, 2] n=1"

-- mixedBack_z__ppe1_2: F(t..., z) = z \n F(spread((((), 1), 2)))
def case_mixedBack_z__ppe1_2 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "t", kind := .variadic }, { name := "z" }] [] [] [.param "z"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.num 1)])), (.num 2)]))])])
#guard obs case_mixedBack_z__ppe1_2 == "ok raw=2 n=1"

-- mixedBack_z__p12_e: F(t..., z) = z \n F(spread(((1, 2), ())))
def case_mixedBack_z__p12_e : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "t", kind := .variadic }, { name := "z" }] [] [] [.param "z"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.emptySequence 0)]))])])
#guard obs case_mixedBack_z__p12_e == "ok raw=S[] n=1"

-- mixedBack_z__ppe: F(t..., z) = z \n F(spread((())))
def case_mixedBack_z__ppe : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "t", kind := .variadic }, { name := "z" }] [] [] [.param "z"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.emptySequence 0)]))])])
#guard obs case_mixedBack_z__ppe == "err arity"

-- mixedBack_z__pp1: F(t..., z) = z \n F(spread(((1))))
def case_mixedBack_z__pp1 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "t", kind := .variadic }, { name := "z" }] [] [] [.param "z"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1)]))]))])])
#guard obs case_mixedBack_z__pp1 == "ok raw=1 n=1"

-- mixedBack_z__ppp12: F(t..., z) = z \n F(spread((((1, 2)))))
def case_mixedBack_z__ppp12 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "t", kind := .variadic }, { name := "z" }] [] [] [.param "z"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)]))]))]))])])
#guard obs case_mixedBack_z__ppp12 == "ok raw=2 n=1"

-- mixedBack_z__le: F(t..., z) = z \n F(spread([]))
def case_mixedBack_z__le : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "t", kind := .variadic }, { name := "z" }] [] [] [.param "z"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.listLiteral [])])])
#guard obs case_mixedBack_z__le == "err arity"

-- mixedBack_z__l7: F(t..., z) = z \n F(spread([7]))
def case_mixedBack_z__l7 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "t", kind := .variadic }, { name := "z" }] [] [] [.param "z"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.listLiteral [(.num 7)])])])
#guard obs case_mixedBack_z__l7 == "ok raw=7 n=1"

-- mixedBack_z__l12: F(t..., z) = z \n F(spread([1, 2]))
def case_mixedBack_z__l12 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "t", kind := .variadic }, { name := "z" }] [] [] [.param "z"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.listLiteral [(.num 1), (.num 2)])])])
#guard obs case_mixedBack_z__l12 == "ok raw=2 n=1"

-- mixedBack_z__l12_3: F(t..., z) = z \n F(spread([[1, 2], 3]))
def case_mixedBack_z__l12_3 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "t", kind := .variadic }, { name := "z" }] [] [] [.param "z"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.listLiteral [(.listLiteral [(.num 1), (.num 2)]), (.num 3)])])])
#guard obs case_mixedBack_z__l12_3 == "ok raw=3 n=1"

-- mixedBack_z__lle: F(t..., z) = z \n F(spread([[]]))
def case_mixedBack_z__lle : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "t", kind := .variadic }, { name := "z" }] [] [] [.param "z"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.listLiteral [(.listLiteral [])])])])
#guard obs case_mixedBack_z__lle == "ok raw=L[] n=1"

-- mixedBack_z__l_e: F(t..., z) = z \n F(spread([()]))
def case_mixedBack_z__l_e : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "t", kind := .variadic }, { name := "z" }] [] [] [.param "z"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.listLiteral [(.emptySequence 0)])])])
#guard obs case_mixedBack_z__l_e == "ok raw=S[] n=1"

-- mixedBack_z__l_p12: F(t..., z) = z \n F(spread([(1, 2)]))
def case_mixedBack_z__l_p12 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "t", kind := .variadic }, { name := "z" }] [] [] [.param "z"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.listLiteral [(.block (alg [] [] [] [(.num 1), (.num 2)]))])])])
#guard obs case_mixedBack_z__l_p12 == "ok raw=S[1, 2] n=1"

-- mixedBack_z__p_l12: F(t..., z) = z \n F(spread(([1, 2], 3)))
def case_mixedBack_z__p_l12 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "t", kind := .variadic }, { name := "z" }] [] [] [.param "z"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.listLiteral [(.num 1), (.num 2)]), (.num 3)]))])])
#guard obs case_mixedBack_z__p_l12 == "ok raw=3 n=1"

-- mixedBack_z__pl1: F(t..., z) = z \n F(spread(([1])))
def case_mixedBack_z__pl1 : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "t", kind := .variadic }, { name := "z" }] [] [] [.param "z"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.listLiteral [(.num 1)])]))])])
#guard obs case_mixedBack_z__pl1 == "ok raw=1 n=1"

-- deconPair_x__e: x, y = () \n x
def case_deconPair_x__e : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.emptySequence 0)]), privateProp "x" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) (alg [] [] [] [.resolve "d"])])] [.resolve "x"])
#guard obs case_deconPair_x__e == "err arity"

-- deconPair_x__n0: x, y = 0 \n x
def case_deconPair_x__n0 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.num 0)]), privateProp "x" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) (alg [] [] [] [.resolve "d"])])] [.resolve "x"])
#guard obs case_deconPair_x__n0 == "err arity"

-- deconPair_x__n1: x, y = 1 \n x
def case_deconPair_x__n1 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.num 1)]), privateProp "x" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) (alg [] [] [] [.resolve "d"])])] [.resolve "x"])
#guard obs case_deconPair_x__n1 == "err arity"

-- deconPair_x__p1: x, y = (1) \n x
def case_deconPair_x__p1 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.block (alg [] [] [] [(.num 1)]))]), privateProp "x" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) (alg [] [] [] [.resolve "d"])])] [.resolve "x"])
#guard obs case_deconPair_x__p1 == "err arity"

-- deconPair_x__p12: x, y = (1, 2) \n x
def case_deconPair_x__p12 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)]))]), privateProp "x" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) (alg [] [] [] [.resolve "d"])])] [.resolve "x"])
#guard obs case_deconPair_x__p12 == "ok raw=1 n=1"

-- deconPair_x__p123: x, y = (1, 2, 3) \n x
def case_deconPair_x__p123 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2), (.num 3)]))]), privateProp "x" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) (alg [] [] [] [.resolve "d"])])] [.resolve "x"])
#guard obs case_deconPair_x__p123 == "err arity"

-- deconPair_x__pee: x, y = ((), ()) \n x
def case_deconPair_x__pee : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.emptySequence 0)]))]), privateProp "x" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) (alg [] [] [] [.resolve "d"])])] [.resolve "x"])
#guard obs case_deconPair_x__pee == "ok raw=S[] n=1"

-- deconPair_x__pe1: x, y = ((), 1) \n x
def case_deconPair_x__pe1 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.num 1)]))]), privateProp "x" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) (alg [] [] [] [.resolve "d"])])] [.resolve "x"])
#guard obs case_deconPair_x__pe1 == "ok raw=S[] n=1"

-- deconPair_x__p1e: x, y = (1, ()) \n x
def case_deconPair_x__p1e : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.emptySequence 0)]))]), privateProp "x" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) (alg [] [] [] [.resolve "d"])])] [.resolve "x"])
#guard obs case_deconPair_x__p1e == "ok raw=1 n=1"

-- deconPair_x__p12_3: x, y = ((1, 2), 3) \n x
def case_deconPair_x__p12_3 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.num 3)]))]), privateProp "x" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) (alg [] [] [] [.resolve "d"])])] [.resolve "x"])
#guard obs case_deconPair_x__p12_3 == "ok raw=S[1, 2] n=1"

-- deconPair_x__p12_34: x, y = ((1, 2), (3, 4)) \n x
def case_deconPair_x__p12_34 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.block (alg [] [] [] [(.num 3), (.num 4)]))]))]), privateProp "x" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) (alg [] [] [] [.resolve "d"])])] [.resolve "x"])
#guard obs case_deconPair_x__p12_34 == "ok raw=S[1, 2] n=1"

-- deconPair_x__pe_12: x, y = ((), (1, 2)) \n x
def case_deconPair_x__pe_12 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.block (alg [] [] [] [(.num 1), (.num 2)]))]))]), privateProp "x" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) (alg [] [] [] [.resolve "d"])])] [.resolve "x"])
#guard obs case_deconPair_x__pe_12 == "ok raw=S[] n=1"

-- deconPair_x__ppe1_2: x, y = (((), 1), 2) \n x
def case_deconPair_x__ppe1_2 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.num 1)])), (.num 2)]))]), privateProp "x" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) (alg [] [] [] [.resolve "d"])])] [.resolve "x"])
#guard obs case_deconPair_x__ppe1_2 == "ok raw=S[S[], 1] n=1"

-- deconPair_x__p12_e: x, y = ((1, 2), ()) \n x
def case_deconPair_x__p12_e : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.emptySequence 0)]))]), privateProp "x" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) (alg [] [] [] [.resolve "d"])])] [.resolve "x"])
#guard obs case_deconPair_x__p12_e == "ok raw=S[1, 2] n=1"

-- deconPair_x__ppe: x, y = (()) \n x
def case_deconPair_x__ppe : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0)]))]), privateProp "x" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) (alg [] [] [] [.resolve "d"])])] [.resolve "x"])
#guard obs case_deconPair_x__ppe == "err arity"

-- deconPair_x__pp1: x, y = ((1)) \n x
def case_deconPair_x__pp1 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1)]))]))]), privateProp "x" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) (alg [] [] [] [.resolve "d"])])] [.resolve "x"])
#guard obs case_deconPair_x__pp1 == "err arity"

-- deconPair_x__ppp12: x, y = (((1, 2))) \n x
def case_deconPair_x__ppp12 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)]))]))]))]), privateProp "x" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) (alg [] [] [] [.resolve "d"])])] [.resolve "x"])
#guard obs case_deconPair_x__ppp12 == "ok raw=1 n=1"

-- deconPair_x__le: x, y = [] \n x
def case_deconPair_x__le : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.listLiteral [])]), privateProp "x" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) (alg [] [] [] [.resolve "d"])])] [.resolve "x"])
#guard obs case_deconPair_x__le == "err arity"

-- deconPair_x__l7: x, y = [7] \n x
def case_deconPair_x__l7 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.listLiteral [(.num 7)])]), privateProp "x" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) (alg [] [] [] [.resolve "d"])])] [.resolve "x"])
#guard obs case_deconPair_x__l7 == "err arity"

-- deconPair_x__l12: x, y = [1, 2] \n x
def case_deconPair_x__l12 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.listLiteral [(.num 1), (.num 2)])]), privateProp "x" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) (alg [] [] [] [.resolve "d"])])] [.resolve "x"])
#guard obs case_deconPair_x__l12 == "ok raw=1 n=1"

-- deconPair_x__l12_3: x, y = [[1, 2], 3] \n x
def case_deconPair_x__l12_3 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.listLiteral [(.listLiteral [(.num 1), (.num 2)]), (.num 3)])]), privateProp "x" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) (alg [] [] [] [.resolve "d"])])] [.resolve "x"])
#guard obs case_deconPair_x__l12_3 == "ok raw=L[1, 2] n=1"

-- deconPair_x__lle: x, y = [[]] \n x
def case_deconPair_x__lle : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.listLiteral [(.listLiteral [])])]), privateProp "x" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) (alg [] [] [] [.resolve "d"])])] [.resolve "x"])
#guard obs case_deconPair_x__lle == "err arity"

-- deconPair_x__l_e: x, y = [()] \n x
def case_deconPair_x__l_e : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.listLiteral [(.emptySequence 0)])]), privateProp "x" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) (alg [] [] [] [.resolve "d"])])] [.resolve "x"])
#guard obs case_deconPair_x__l_e == "err arity"

-- deconPair_x__l_p12: x, y = [(1, 2)] \n x
def case_deconPair_x__l_p12 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.listLiteral [(.block (alg [] [] [] [(.num 1), (.num 2)]))])]), privateProp "x" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) (alg [] [] [] [.resolve "d"])])] [.resolve "x"])
#guard obs case_deconPair_x__l_p12 == "err arity"

-- deconPair_x__p_l12: x, y = ([1, 2], 3) \n x
def case_deconPair_x__p_l12 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.block (alg [] [] [] [(.listLiteral [(.num 1), (.num 2)]), (.num 3)]))]), privateProp "x" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) (alg [] [] [] [.resolve "d"])])] [.resolve "x"])
#guard obs case_deconPair_x__p_l12 == "ok raw=L[1, 2] n=1"

-- deconPair_x__pl1: x, y = ([1]) \n x
def case_deconPair_x__pl1 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.block (alg [] [] [] [(.listLiteral [(.num 1)])]))]), privateProp "x" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) (alg [] [] [] [.resolve "d"])])] [.resolve "x"])
#guard obs case_deconPair_x__pl1 == "err arity"

-- deconPair_y__e: x, y = () \n y
def case_deconPair_y__e : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.emptySequence 0)]), privateProp "y" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) (alg [] [] [] [.resolve "d"])])] [.resolve "y"])
#guard obs case_deconPair_y__e == "err arity"

-- deconPair_y__n0: x, y = 0 \n y
def case_deconPair_y__n0 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.num 0)]), privateProp "y" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) (alg [] [] [] [.resolve "d"])])] [.resolve "y"])
#guard obs case_deconPair_y__n0 == "err arity"

-- deconPair_y__n1: x, y = 1 \n y
def case_deconPair_y__n1 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.num 1)]), privateProp "y" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) (alg [] [] [] [.resolve "d"])])] [.resolve "y"])
#guard obs case_deconPair_y__n1 == "err arity"

-- deconPair_y__p1: x, y = (1) \n y
def case_deconPair_y__p1 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.block (alg [] [] [] [(.num 1)]))]), privateProp "y" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) (alg [] [] [] [.resolve "d"])])] [.resolve "y"])
#guard obs case_deconPair_y__p1 == "err arity"

-- deconPair_y__p12: x, y = (1, 2) \n y
def case_deconPair_y__p12 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)]))]), privateProp "y" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) (alg [] [] [] [.resolve "d"])])] [.resolve "y"])
#guard obs case_deconPair_y__p12 == "ok raw=2 n=1"

-- deconPair_y__p123: x, y = (1, 2, 3) \n y
def case_deconPair_y__p123 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2), (.num 3)]))]), privateProp "y" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) (alg [] [] [] [.resolve "d"])])] [.resolve "y"])
#guard obs case_deconPair_y__p123 == "err arity"

-- deconPair_y__pee: x, y = ((), ()) \n y
def case_deconPair_y__pee : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.emptySequence 0)]))]), privateProp "y" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) (alg [] [] [] [.resolve "d"])])] [.resolve "y"])
#guard obs case_deconPair_y__pee == "ok raw=S[] n=1"

-- deconPair_y__pe1: x, y = ((), 1) \n y
def case_deconPair_y__pe1 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.num 1)]))]), privateProp "y" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) (alg [] [] [] [.resolve "d"])])] [.resolve "y"])
#guard obs case_deconPair_y__pe1 == "ok raw=1 n=1"

-- deconPair_y__p1e: x, y = (1, ()) \n y
def case_deconPair_y__p1e : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.emptySequence 0)]))]), privateProp "y" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) (alg [] [] [] [.resolve "d"])])] [.resolve "y"])
#guard obs case_deconPair_y__p1e == "ok raw=S[] n=1"

-- deconPair_y__p12_3: x, y = ((1, 2), 3) \n y
def case_deconPair_y__p12_3 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.num 3)]))]), privateProp "y" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) (alg [] [] [] [.resolve "d"])])] [.resolve "y"])
#guard obs case_deconPair_y__p12_3 == "ok raw=3 n=1"

-- deconPair_y__p12_34: x, y = ((1, 2), (3, 4)) \n y
def case_deconPair_y__p12_34 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.block (alg [] [] [] [(.num 3), (.num 4)]))]))]), privateProp "y" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) (alg [] [] [] [.resolve "d"])])] [.resolve "y"])
#guard obs case_deconPair_y__p12_34 == "ok raw=S[3, 4] n=1"

-- deconPair_y__pe_12: x, y = ((), (1, 2)) \n y
def case_deconPair_y__pe_12 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.block (alg [] [] [] [(.num 1), (.num 2)]))]))]), privateProp "y" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) (alg [] [] [] [.resolve "d"])])] [.resolve "y"])
#guard obs case_deconPair_y__pe_12 == "ok raw=S[1, 2] n=1"

-- deconPair_y__ppe1_2: x, y = (((), 1), 2) \n y
def case_deconPair_y__ppe1_2 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.num 1)])), (.num 2)]))]), privateProp "y" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) (alg [] [] [] [.resolve "d"])])] [.resolve "y"])
#guard obs case_deconPair_y__ppe1_2 == "ok raw=2 n=1"

-- deconPair_y__p12_e: x, y = ((1, 2), ()) \n y
def case_deconPair_y__p12_e : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.emptySequence 0)]))]), privateProp "y" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) (alg [] [] [] [.resolve "d"])])] [.resolve "y"])
#guard obs case_deconPair_y__p12_e == "ok raw=S[] n=1"

-- deconPair_y__ppe: x, y = (()) \n y
def case_deconPair_y__ppe : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0)]))]), privateProp "y" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) (alg [] [] [] [.resolve "d"])])] [.resolve "y"])
#guard obs case_deconPair_y__ppe == "err arity"

-- deconPair_y__pp1: x, y = ((1)) \n y
def case_deconPair_y__pp1 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1)]))]))]), privateProp "y" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) (alg [] [] [] [.resolve "d"])])] [.resolve "y"])
#guard obs case_deconPair_y__pp1 == "err arity"

-- deconPair_y__ppp12: x, y = (((1, 2))) \n y
def case_deconPair_y__ppp12 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)]))]))]))]), privateProp "y" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) (alg [] [] [] [.resolve "d"])])] [.resolve "y"])
#guard obs case_deconPair_y__ppp12 == "ok raw=2 n=1"

-- deconPair_y__le: x, y = [] \n y
def case_deconPair_y__le : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.listLiteral [])]), privateProp "y" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) (alg [] [] [] [.resolve "d"])])] [.resolve "y"])
#guard obs case_deconPair_y__le == "err arity"

-- deconPair_y__l7: x, y = [7] \n y
def case_deconPair_y__l7 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.listLiteral [(.num 7)])]), privateProp "y" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) (alg [] [] [] [.resolve "d"])])] [.resolve "y"])
#guard obs case_deconPair_y__l7 == "err arity"

-- deconPair_y__l12: x, y = [1, 2] \n y
def case_deconPair_y__l12 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.listLiteral [(.num 1), (.num 2)])]), privateProp "y" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) (alg [] [] [] [.resolve "d"])])] [.resolve "y"])
#guard obs case_deconPair_y__l12 == "ok raw=2 n=1"

-- deconPair_y__l12_3: x, y = [[1, 2], 3] \n y
def case_deconPair_y__l12_3 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.listLiteral [(.listLiteral [(.num 1), (.num 2)]), (.num 3)])]), privateProp "y" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) (alg [] [] [] [.resolve "d"])])] [.resolve "y"])
#guard obs case_deconPair_y__l12_3 == "ok raw=3 n=1"

-- deconPair_y__lle: x, y = [[]] \n y
def case_deconPair_y__lle : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.listLiteral [(.listLiteral [])])]), privateProp "y" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) (alg [] [] [] [.resolve "d"])])] [.resolve "y"])
#guard obs case_deconPair_y__lle == "err arity"

-- deconPair_y__l_e: x, y = [()] \n y
def case_deconPair_y__l_e : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.listLiteral [(.emptySequence 0)])]), privateProp "y" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) (alg [] [] [] [.resolve "d"])])] [.resolve "y"])
#guard obs case_deconPair_y__l_e == "err arity"

-- deconPair_y__l_p12: x, y = [(1, 2)] \n y
def case_deconPair_y__l_p12 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.listLiteral [(.block (alg [] [] [] [(.num 1), (.num 2)]))])]), privateProp "y" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) (alg [] [] [] [.resolve "d"])])] [.resolve "y"])
#guard obs case_deconPair_y__l_p12 == "err arity"

-- deconPair_y__p_l12: x, y = ([1, 2], 3) \n y
def case_deconPair_y__p_l12 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.block (alg [] [] [] [(.listLiteral [(.num 1), (.num 2)]), (.num 3)]))]), privateProp "y" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) (alg [] [] [] [.resolve "d"])])] [.resolve "y"])
#guard obs case_deconPair_y__p_l12 == "ok raw=3 n=1"

-- deconPair_y__pl1: x, y = ([1]) \n y
def case_deconPair_y__pl1 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.block (alg [] [] [] [(.listLiteral [(.num 1)])]))]), privateProp "y" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) (alg [] [] [] [.resolve "d"])])] [.resolve "y"])
#guard obs case_deconPair_y__pl1 == "err arity"

-- deconPairSpread_x__e: x, y = spread(()) \n x
def case_deconPairSpread_x__e : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [.sequenceSpread (.emptySequence 0)]), privateProp "x" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) (alg [] [] [] [.resolve "d"])])] [.resolve "x"])
#guard obs case_deconPairSpread_x__e == "err arity"

-- deconPairSpread_x__n0: x, y = spread(0) \n x
def case_deconPairSpread_x__n0 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [.sequenceSpread (.num 0)]), privateProp "x" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) (alg [] [] [] [.resolve "d"])])] [.resolve "x"])
#guard obs case_deconPairSpread_x__n0 == "err arity"

-- deconPairSpread_x__n1: x, y = spread(1) \n x
def case_deconPairSpread_x__n1 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [.sequenceSpread (.num 1)]), privateProp "x" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) (alg [] [] [] [.resolve "d"])])] [.resolve "x"])
#guard obs case_deconPairSpread_x__n1 == "err arity"

-- deconPairSpread_x__p1: x, y = spread((1)) \n x
def case_deconPairSpread_x__p1 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.num 1)]))]), privateProp "x" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) (alg [] [] [] [.resolve "d"])])] [.resolve "x"])
#guard obs case_deconPairSpread_x__p1 == "err arity"

-- deconPairSpread_x__p12: x, y = spread((1, 2)) \n x
def case_deconPairSpread_x__p12 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.num 1), (.num 2)]))]), privateProp "x" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) (alg [] [] [] [.resolve "d"])])] [.resolve "x"])
#guard obs case_deconPairSpread_x__p12 == "ok raw=1 n=1"

-- deconPairSpread_x__p123: x, y = spread((1, 2, 3)) \n x
def case_deconPairSpread_x__p123 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.num 1), (.num 2), (.num 3)]))]), privateProp "x" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) (alg [] [] [] [.resolve "d"])])] [.resolve "x"])
#guard obs case_deconPairSpread_x__p123 == "err arity"

-- deconPairSpread_x__pee: x, y = spread(((), ())) \n x
def case_deconPairSpread_x__pee : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.emptySequence 0), (.emptySequence 0)]))]), privateProp "x" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) (alg [] [] [] [.resolve "d"])])] [.resolve "x"])
#guard obs case_deconPairSpread_x__pee == "ok raw=S[] n=1"

-- deconPairSpread_x__pe1: x, y = spread(((), 1)) \n x
def case_deconPairSpread_x__pe1 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.emptySequence 0), (.num 1)]))]), privateProp "x" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) (alg [] [] [] [.resolve "d"])])] [.resolve "x"])
#guard obs case_deconPairSpread_x__pe1 == "ok raw=S[] n=1"

-- deconPairSpread_x__p1e: x, y = spread((1, ())) \n x
def case_deconPairSpread_x__p1e : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.num 1), (.emptySequence 0)]))]), privateProp "x" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) (alg [] [] [] [.resolve "d"])])] [.resolve "x"])
#guard obs case_deconPairSpread_x__p1e == "ok raw=1 n=1"

-- deconPairSpread_x__p12_3: x, y = spread(((1, 2), 3)) \n x
def case_deconPairSpread_x__p12_3 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.num 3)]))]), privateProp "x" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) (alg [] [] [] [.resolve "d"])])] [.resolve "x"])
#guard obs case_deconPairSpread_x__p12_3 == "ok raw=S[1, 2] n=1"

-- deconPairSpread_x__p12_34: x, y = spread(((1, 2), (3, 4))) \n x
def case_deconPairSpread_x__p12_34 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.block (alg [] [] [] [(.num 3), (.num 4)]))]))]), privateProp "x" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) (alg [] [] [] [.resolve "d"])])] [.resolve "x"])
#guard obs case_deconPairSpread_x__p12_34 == "ok raw=S[1, 2] n=1"

-- deconPairSpread_x__pe_12: x, y = spread(((), (1, 2))) \n x
def case_deconPairSpread_x__pe_12 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.emptySequence 0), (.block (alg [] [] [] [(.num 1), (.num 2)]))]))]), privateProp "x" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) (alg [] [] [] [.resolve "d"])])] [.resolve "x"])
#guard obs case_deconPairSpread_x__pe_12 == "ok raw=S[] n=1"

-- deconPairSpread_x__ppe1_2: x, y = spread((((), 1), 2)) \n x
def case_deconPairSpread_x__ppe1_2 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.num 1)])), (.num 2)]))]), privateProp "x" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) (alg [] [] [] [.resolve "d"])])] [.resolve "x"])
#guard obs case_deconPairSpread_x__ppe1_2 == "ok raw=S[S[], 1] n=1"

-- deconPairSpread_x__p12_e: x, y = spread(((1, 2), ())) \n x
def case_deconPairSpread_x__p12_e : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.emptySequence 0)]))]), privateProp "x" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) (alg [] [] [] [.resolve "d"])])] [.resolve "x"])
#guard obs case_deconPairSpread_x__p12_e == "ok raw=S[1, 2] n=1"

-- deconPairSpread_x__ppe: x, y = spread((())) \n x
def case_deconPairSpread_x__ppe : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.emptySequence 0)]))]), privateProp "x" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) (alg [] [] [] [.resolve "d"])])] [.resolve "x"])
#guard obs case_deconPairSpread_x__ppe == "err arity"

-- deconPairSpread_x__pp1: x, y = spread(((1))) \n x
def case_deconPairSpread_x__pp1 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1)]))]))]), privateProp "x" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) (alg [] [] [] [.resolve "d"])])] [.resolve "x"])
#guard obs case_deconPairSpread_x__pp1 == "err arity"

-- deconPairSpread_x__ppp12: x, y = spread((((1, 2)))) \n x
def case_deconPairSpread_x__ppp12 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)]))]))]))]), privateProp "x" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) (alg [] [] [] [.resolve "d"])])] [.resolve "x"])
#guard obs case_deconPairSpread_x__ppp12 == "ok raw=1 n=1"

-- deconPairSpread_x__le: x, y = spread([]) \n x
def case_deconPairSpread_x__le : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [.sequenceSpread (.listLiteral [])]), privateProp "x" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) (alg [] [] [] [.resolve "d"])])] [.resolve "x"])
#guard obs case_deconPairSpread_x__le == "err arity"

-- deconPairSpread_x__l7: x, y = spread([7]) \n x
def case_deconPairSpread_x__l7 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [.sequenceSpread (.listLiteral [(.num 7)])]), privateProp "x" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) (alg [] [] [] [.resolve "d"])])] [.resolve "x"])
#guard obs case_deconPairSpread_x__l7 == "err arity"

-- deconPairSpread_x__l12: x, y = spread([1, 2]) \n x
def case_deconPairSpread_x__l12 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [.sequenceSpread (.listLiteral [(.num 1), (.num 2)])]), privateProp "x" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) (alg [] [] [] [.resolve "d"])])] [.resolve "x"])
#guard obs case_deconPairSpread_x__l12 == "ok raw=1 n=1"

-- deconPairSpread_x__l12_3: x, y = spread([[1, 2], 3]) \n x
def case_deconPairSpread_x__l12_3 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [.sequenceSpread (.listLiteral [(.listLiteral [(.num 1), (.num 2)]), (.num 3)])]), privateProp "x" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) (alg [] [] [] [.resolve "d"])])] [.resolve "x"])
#guard obs case_deconPairSpread_x__l12_3 == "ok raw=L[1, 2] n=1"

-- deconPairSpread_x__lle: x, y = spread([[]]) \n x
def case_deconPairSpread_x__lle : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [.sequenceSpread (.listLiteral [(.listLiteral [])])]), privateProp "x" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) (alg [] [] [] [.resolve "d"])])] [.resolve "x"])
#guard obs case_deconPairSpread_x__lle == "err arity"

-- deconPairSpread_x__l_e: x, y = spread([()]) \n x
def case_deconPairSpread_x__l_e : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [.sequenceSpread (.listLiteral [(.emptySequence 0)])]), privateProp "x" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) (alg [] [] [] [.resolve "d"])])] [.resolve "x"])
#guard obs case_deconPairSpread_x__l_e == "err arity"

-- deconPairSpread_x__l_p12: x, y = spread([(1, 2)]) \n x
def case_deconPairSpread_x__l_p12 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [.sequenceSpread (.listLiteral [(.block (alg [] [] [] [(.num 1), (.num 2)]))])]), privateProp "x" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) (alg [] [] [] [.resolve "d"])])] [.resolve "x"])
#guard obs case_deconPairSpread_x__l_p12 == "ok raw=1 n=1"

-- deconPairSpread_x__p_l12: x, y = spread(([1, 2], 3)) \n x
def case_deconPairSpread_x__p_l12 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.listLiteral [(.num 1), (.num 2)]), (.num 3)]))]), privateProp "x" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) (alg [] [] [] [.resolve "d"])])] [.resolve "x"])
#guard obs case_deconPairSpread_x__p_l12 == "ok raw=L[1, 2] n=1"

-- deconPairSpread_x__pl1: x, y = spread(([1])) \n x
def case_deconPairSpread_x__pl1 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.listLiteral [(.num 1)])]))]), privateProp "x" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) (alg [] [] [] [.resolve "d"])])] [.resolve "x"])
#guard obs case_deconPairSpread_x__pl1 == "err arity"

-- deconCollect_t__e: h, t... = () \n t
def case_deconCollect_t__e : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.emptySequence 0)]), privateProp "t" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .variadic }]] [] [] [.param "t"])) (alg [] [] [] [.resolve "d"])])] [.resolve "t"])
#guard obs case_deconCollect_t__e == "err arity"

-- deconCollect_t__n0: h, t... = 0 \n t
def case_deconCollect_t__n0 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.num 0)]), privateProp "t" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .variadic }]] [] [] [.param "t"])) (alg [] [] [] [.resolve "d"])])] [.resolve "t"])
#guard obs case_deconCollect_t__n0 == "ok raw=L[] n=1"

-- deconCollect_t__n1: h, t... = 1 \n t
def case_deconCollect_t__n1 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.num 1)]), privateProp "t" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .variadic }]] [] [] [.param "t"])) (alg [] [] [] [.resolve "d"])])] [.resolve "t"])
#guard obs case_deconCollect_t__n1 == "ok raw=L[] n=1"

-- deconCollect_t__p1: h, t... = (1) \n t
def case_deconCollect_t__p1 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.block (alg [] [] [] [(.num 1)]))]), privateProp "t" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .variadic }]] [] [] [.param "t"])) (alg [] [] [] [.resolve "d"])])] [.resolve "t"])
#guard obs case_deconCollect_t__p1 == "ok raw=L[] n=1"

-- deconCollect_t__p12: h, t... = (1, 2) \n t
def case_deconCollect_t__p12 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)]))]), privateProp "t" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .variadic }]] [] [] [.param "t"])) (alg [] [] [] [.resolve "d"])])] [.resolve "t"])
#guard obs case_deconCollect_t__p12 == "ok raw=L[2] n=1"

-- deconCollect_t__p123: h, t... = (1, 2, 3) \n t
def case_deconCollect_t__p123 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2), (.num 3)]))]), privateProp "t" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .variadic }]] [] [] [.param "t"])) (alg [] [] [] [.resolve "d"])])] [.resolve "t"])
#guard obs case_deconCollect_t__p123 == "ok raw=L[2, 3] n=1"

-- deconCollect_t__pee: h, t... = ((), ()) \n t
def case_deconCollect_t__pee : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.emptySequence 0)]))]), privateProp "t" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .variadic }]] [] [] [.param "t"])) (alg [] [] [] [.resolve "d"])])] [.resolve "t"])
#guard obs case_deconCollect_t__pee == "ok raw=L[S[]] n=1"

-- deconCollect_t__pe1: h, t... = ((), 1) \n t
def case_deconCollect_t__pe1 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.num 1)]))]), privateProp "t" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .variadic }]] [] [] [.param "t"])) (alg [] [] [] [.resolve "d"])])] [.resolve "t"])
#guard obs case_deconCollect_t__pe1 == "ok raw=L[1] n=1"

-- deconCollect_t__p1e: h, t... = (1, ()) \n t
def case_deconCollect_t__p1e : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.emptySequence 0)]))]), privateProp "t" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .variadic }]] [] [] [.param "t"])) (alg [] [] [] [.resolve "d"])])] [.resolve "t"])
#guard obs case_deconCollect_t__p1e == "ok raw=L[S[]] n=1"

-- deconCollect_t__p12_3: h, t... = ((1, 2), 3) \n t
def case_deconCollect_t__p12_3 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.num 3)]))]), privateProp "t" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .variadic }]] [] [] [.param "t"])) (alg [] [] [] [.resolve "d"])])] [.resolve "t"])
#guard obs case_deconCollect_t__p12_3 == "ok raw=L[3] n=1"

-- deconCollect_t__p12_34: h, t... = ((1, 2), (3, 4)) \n t
def case_deconCollect_t__p12_34 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.block (alg [] [] [] [(.num 3), (.num 4)]))]))]), privateProp "t" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .variadic }]] [] [] [.param "t"])) (alg [] [] [] [.resolve "d"])])] [.resolve "t"])
#guard obs case_deconCollect_t__p12_34 == "ok raw=L[S[3, 4]] n=1"

-- deconCollect_t__pe_12: h, t... = ((), (1, 2)) \n t
def case_deconCollect_t__pe_12 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.block (alg [] [] [] [(.num 1), (.num 2)]))]))]), privateProp "t" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .variadic }]] [] [] [.param "t"])) (alg [] [] [] [.resolve "d"])])] [.resolve "t"])
#guard obs case_deconCollect_t__pe_12 == "ok raw=L[S[1, 2]] n=1"

-- deconCollect_t__ppe1_2: h, t... = (((), 1), 2) \n t
def case_deconCollect_t__ppe1_2 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.num 1)])), (.num 2)]))]), privateProp "t" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .variadic }]] [] [] [.param "t"])) (alg [] [] [] [.resolve "d"])])] [.resolve "t"])
#guard obs case_deconCollect_t__ppe1_2 == "ok raw=L[2] n=1"

-- deconCollect_t__p12_e: h, t... = ((1, 2), ()) \n t
def case_deconCollect_t__p12_e : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.emptySequence 0)]))]), privateProp "t" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .variadic }]] [] [] [.param "t"])) (alg [] [] [] [.resolve "d"])])] [.resolve "t"])
#guard obs case_deconCollect_t__p12_e == "ok raw=L[S[]] n=1"

-- deconCollect_t__ppe: h, t... = (()) \n t
def case_deconCollect_t__ppe : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0)]))]), privateProp "t" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .variadic }]] [] [] [.param "t"])) (alg [] [] [] [.resolve "d"])])] [.resolve "t"])
#guard obs case_deconCollect_t__ppe == "err arity"

-- deconCollect_t__pp1: h, t... = ((1)) \n t
def case_deconCollect_t__pp1 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1)]))]))]), privateProp "t" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .variadic }]] [] [] [.param "t"])) (alg [] [] [] [.resolve "d"])])] [.resolve "t"])
#guard obs case_deconCollect_t__pp1 == "ok raw=L[] n=1"

-- deconCollect_t__ppp12: h, t... = (((1, 2))) \n t
def case_deconCollect_t__ppp12 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)]))]))]))]), privateProp "t" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .variadic }]] [] [] [.param "t"])) (alg [] [] [] [.resolve "d"])])] [.resolve "t"])
#guard obs case_deconCollect_t__ppp12 == "ok raw=L[2] n=1"

-- deconCollect_t__le: h, t... = [] \n t
def case_deconCollect_t__le : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.listLiteral [])]), privateProp "t" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .variadic }]] [] [] [.param "t"])) (alg [] [] [] [.resolve "d"])])] [.resolve "t"])
#guard obs case_deconCollect_t__le == "err arity"

-- deconCollect_t__l7: h, t... = [7] \n t
def case_deconCollect_t__l7 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.listLiteral [(.num 7)])]), privateProp "t" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .variadic }]] [] [] [.param "t"])) (alg [] [] [] [.resolve "d"])])] [.resolve "t"])
#guard obs case_deconCollect_t__l7 == "ok raw=L[] n=1"

-- deconCollect_t__l12: h, t... = [1, 2] \n t
def case_deconCollect_t__l12 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.listLiteral [(.num 1), (.num 2)])]), privateProp "t" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .variadic }]] [] [] [.param "t"])) (alg [] [] [] [.resolve "d"])])] [.resolve "t"])
#guard obs case_deconCollect_t__l12 == "ok raw=L[2] n=1"

-- deconCollect_t__l12_3: h, t... = [[1, 2], 3] \n t
def case_deconCollect_t__l12_3 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.listLiteral [(.listLiteral [(.num 1), (.num 2)]), (.num 3)])]), privateProp "t" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .variadic }]] [] [] [.param "t"])) (alg [] [] [] [.resolve "d"])])] [.resolve "t"])
#guard obs case_deconCollect_t__l12_3 == "ok raw=L[3] n=1"

-- deconCollect_t__lle: h, t... = [[]] \n t
def case_deconCollect_t__lle : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.listLiteral [(.listLiteral [])])]), privateProp "t" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .variadic }]] [] [] [.param "t"])) (alg [] [] [] [.resolve "d"])])] [.resolve "t"])
#guard obs case_deconCollect_t__lle == "ok raw=L[] n=1"

-- deconCollect_t__l_e: h, t... = [()] \n t
def case_deconCollect_t__l_e : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.listLiteral [(.emptySequence 0)])]), privateProp "t" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .variadic }]] [] [] [.param "t"])) (alg [] [] [] [.resolve "d"])])] [.resolve "t"])
#guard obs case_deconCollect_t__l_e == "ok raw=L[] n=1"

-- deconCollect_t__l_p12: h, t... = [(1, 2)] \n t
def case_deconCollect_t__l_p12 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.listLiteral [(.block (alg [] [] [] [(.num 1), (.num 2)]))])]), privateProp "t" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .variadic }]] [] [] [.param "t"])) (alg [] [] [] [.resolve "d"])])] [.resolve "t"])
#guard obs case_deconCollect_t__l_p12 == "ok raw=L[] n=1"

-- deconCollect_t__p_l12: h, t... = ([1, 2], 3) \n t
def case_deconCollect_t__p_l12 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.block (alg [] [] [] [(.listLiteral [(.num 1), (.num 2)]), (.num 3)]))]), privateProp "t" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .variadic }]] [] [] [.param "t"])) (alg [] [] [] [.resolve "d"])])] [.resolve "t"])
#guard obs case_deconCollect_t__p_l12 == "ok raw=L[3] n=1"

-- deconCollect_t__pl1: h, t... = ([1]) \n t
def case_deconCollect_t__pl1 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.block (alg [] [] [] [(.listLiteral [(.num 1)])]))]), privateProp "t" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .variadic }]] [] [] [.param "t"])) (alg [] [] [] [.resolve "d"])])] [.resolve "t"])
#guard obs case_deconCollect_t__pl1 == "ok raw=L[] n=1"

-- deconCollectSpread_t__e: h, t... = spread(()) \n t
def case_deconCollectSpread_t__e : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [.sequenceSpread (.emptySequence 0)]), privateProp "t" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .variadic }]] [] [] [.param "t"])) (alg [] [] [] [.resolve "d"])])] [.resolve "t"])
#guard obs case_deconCollectSpread_t__e == "err arity"

-- deconCollectSpread_t__n0: h, t... = spread(0) \n t
def case_deconCollectSpread_t__n0 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [.sequenceSpread (.num 0)]), privateProp "t" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .variadic }]] [] [] [.param "t"])) (alg [] [] [] [.resolve "d"])])] [.resolve "t"])
#guard obs case_deconCollectSpread_t__n0 == "ok raw=L[] n=1"

-- deconCollectSpread_t__n1: h, t... = spread(1) \n t
def case_deconCollectSpread_t__n1 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [.sequenceSpread (.num 1)]), privateProp "t" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .variadic }]] [] [] [.param "t"])) (alg [] [] [] [.resolve "d"])])] [.resolve "t"])
#guard obs case_deconCollectSpread_t__n1 == "ok raw=L[] n=1"

-- deconCollectSpread_t__p1: h, t... = spread((1)) \n t
def case_deconCollectSpread_t__p1 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.num 1)]))]), privateProp "t" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .variadic }]] [] [] [.param "t"])) (alg [] [] [] [.resolve "d"])])] [.resolve "t"])
#guard obs case_deconCollectSpread_t__p1 == "ok raw=L[] n=1"

-- deconCollectSpread_t__p12: h, t... = spread((1, 2)) \n t
def case_deconCollectSpread_t__p12 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.num 1), (.num 2)]))]), privateProp "t" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .variadic }]] [] [] [.param "t"])) (alg [] [] [] [.resolve "d"])])] [.resolve "t"])
#guard obs case_deconCollectSpread_t__p12 == "ok raw=L[2] n=1"

-- deconCollectSpread_t__p123: h, t... = spread((1, 2, 3)) \n t
def case_deconCollectSpread_t__p123 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.num 1), (.num 2), (.num 3)]))]), privateProp "t" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .variadic }]] [] [] [.param "t"])) (alg [] [] [] [.resolve "d"])])] [.resolve "t"])
#guard obs case_deconCollectSpread_t__p123 == "ok raw=L[2, 3] n=1"

-- deconCollectSpread_t__pee: h, t... = spread(((), ())) \n t
def case_deconCollectSpread_t__pee : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.emptySequence 0), (.emptySequence 0)]))]), privateProp "t" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .variadic }]] [] [] [.param "t"])) (alg [] [] [] [.resolve "d"])])] [.resolve "t"])
#guard obs case_deconCollectSpread_t__pee == "ok raw=L[S[]] n=1"

-- deconCollectSpread_t__pe1: h, t... = spread(((), 1)) \n t
def case_deconCollectSpread_t__pe1 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.emptySequence 0), (.num 1)]))]), privateProp "t" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .variadic }]] [] [] [.param "t"])) (alg [] [] [] [.resolve "d"])])] [.resolve "t"])
#guard obs case_deconCollectSpread_t__pe1 == "ok raw=L[1] n=1"

-- deconCollectSpread_t__p1e: h, t... = spread((1, ())) \n t
def case_deconCollectSpread_t__p1e : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.num 1), (.emptySequence 0)]))]), privateProp "t" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .variadic }]] [] [] [.param "t"])) (alg [] [] [] [.resolve "d"])])] [.resolve "t"])
#guard obs case_deconCollectSpread_t__p1e == "ok raw=L[S[]] n=1"

-- deconCollectSpread_t__p12_3: h, t... = spread(((1, 2), 3)) \n t
def case_deconCollectSpread_t__p12_3 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.num 3)]))]), privateProp "t" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .variadic }]] [] [] [.param "t"])) (alg [] [] [] [.resolve "d"])])] [.resolve "t"])
#guard obs case_deconCollectSpread_t__p12_3 == "ok raw=L[3] n=1"

-- deconCollectSpread_t__p12_34: h, t... = spread(((1, 2), (3, 4))) \n t
def case_deconCollectSpread_t__p12_34 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.block (alg [] [] [] [(.num 3), (.num 4)]))]))]), privateProp "t" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .variadic }]] [] [] [.param "t"])) (alg [] [] [] [.resolve "d"])])] [.resolve "t"])
#guard obs case_deconCollectSpread_t__p12_34 == "ok raw=L[S[3, 4]] n=1"

-- deconCollectSpread_t__pe_12: h, t... = spread(((), (1, 2))) \n t
def case_deconCollectSpread_t__pe_12 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.emptySequence 0), (.block (alg [] [] [] [(.num 1), (.num 2)]))]))]), privateProp "t" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .variadic }]] [] [] [.param "t"])) (alg [] [] [] [.resolve "d"])])] [.resolve "t"])
#guard obs case_deconCollectSpread_t__pe_12 == "ok raw=L[S[1, 2]] n=1"

-- deconCollectSpread_t__ppe1_2: h, t... = spread((((), 1), 2)) \n t
def case_deconCollectSpread_t__ppe1_2 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.num 1)])), (.num 2)]))]), privateProp "t" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .variadic }]] [] [] [.param "t"])) (alg [] [] [] [.resolve "d"])])] [.resolve "t"])
#guard obs case_deconCollectSpread_t__ppe1_2 == "ok raw=L[2] n=1"

-- deconCollectSpread_t__p12_e: h, t... = spread(((1, 2), ())) \n t
def case_deconCollectSpread_t__p12_e : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.emptySequence 0)]))]), privateProp "t" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .variadic }]] [] [] [.param "t"])) (alg [] [] [] [.resolve "d"])])] [.resolve "t"])
#guard obs case_deconCollectSpread_t__p12_e == "ok raw=L[S[]] n=1"

-- deconCollectSpread_t__ppe: h, t... = spread((())) \n t
def case_deconCollectSpread_t__ppe : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.emptySequence 0)]))]), privateProp "t" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .variadic }]] [] [] [.param "t"])) (alg [] [] [] [.resolve "d"])])] [.resolve "t"])
#guard obs case_deconCollectSpread_t__ppe == "err arity"

-- deconCollectSpread_t__pp1: h, t... = spread(((1))) \n t
def case_deconCollectSpread_t__pp1 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1)]))]))]), privateProp "t" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .variadic }]] [] [] [.param "t"])) (alg [] [] [] [.resolve "d"])])] [.resolve "t"])
#guard obs case_deconCollectSpread_t__pp1 == "ok raw=L[] n=1"

-- deconCollectSpread_t__ppp12: h, t... = spread((((1, 2)))) \n t
def case_deconCollectSpread_t__ppp12 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)]))]))]))]), privateProp "t" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .variadic }]] [] [] [.param "t"])) (alg [] [] [] [.resolve "d"])])] [.resolve "t"])
#guard obs case_deconCollectSpread_t__ppp12 == "ok raw=L[2] n=1"

-- deconCollectSpread_t__le: h, t... = spread([]) \n t
def case_deconCollectSpread_t__le : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [.sequenceSpread (.listLiteral [])]), privateProp "t" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .variadic }]] [] [] [.param "t"])) (alg [] [] [] [.resolve "d"])])] [.resolve "t"])
#guard obs case_deconCollectSpread_t__le == "err arity"

-- deconCollectSpread_t__l7: h, t... = spread([7]) \n t
def case_deconCollectSpread_t__l7 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [.sequenceSpread (.listLiteral [(.num 7)])]), privateProp "t" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .variadic }]] [] [] [.param "t"])) (alg [] [] [] [.resolve "d"])])] [.resolve "t"])
#guard obs case_deconCollectSpread_t__l7 == "ok raw=L[] n=1"

-- deconCollectSpread_t__l12: h, t... = spread([1, 2]) \n t
def case_deconCollectSpread_t__l12 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [.sequenceSpread (.listLiteral [(.num 1), (.num 2)])]), privateProp "t" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .variadic }]] [] [] [.param "t"])) (alg [] [] [] [.resolve "d"])])] [.resolve "t"])
#guard obs case_deconCollectSpread_t__l12 == "ok raw=L[2] n=1"

-- deconCollectSpread_t__l12_3: h, t... = spread([[1, 2], 3]) \n t
def case_deconCollectSpread_t__l12_3 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [.sequenceSpread (.listLiteral [(.listLiteral [(.num 1), (.num 2)]), (.num 3)])]), privateProp "t" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .variadic }]] [] [] [.param "t"])) (alg [] [] [] [.resolve "d"])])] [.resolve "t"])
#guard obs case_deconCollectSpread_t__l12_3 == "ok raw=L[3] n=1"

-- deconCollectSpread_t__lle: h, t... = spread([[]]) \n t
def case_deconCollectSpread_t__lle : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [.sequenceSpread (.listLiteral [(.listLiteral [])])]), privateProp "t" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .variadic }]] [] [] [.param "t"])) (alg [] [] [] [.resolve "d"])])] [.resolve "t"])
#guard obs case_deconCollectSpread_t__lle == "err arity"

-- deconCollectSpread_t__l_e: h, t... = spread([()]) \n t
def case_deconCollectSpread_t__l_e : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [.sequenceSpread (.listLiteral [(.emptySequence 0)])]), privateProp "t" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .variadic }]] [] [] [.param "t"])) (alg [] [] [] [.resolve "d"])])] [.resolve "t"])
#guard obs case_deconCollectSpread_t__l_e == "err arity"

-- deconCollectSpread_t__l_p12: h, t... = spread([(1, 2)]) \n t
def case_deconCollectSpread_t__l_p12 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [.sequenceSpread (.listLiteral [(.block (alg [] [] [] [(.num 1), (.num 2)]))])]), privateProp "t" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .variadic }]] [] [] [.param "t"])) (alg [] [] [] [.resolve "d"])])] [.resolve "t"])
#guard obs case_deconCollectSpread_t__l_p12 == "ok raw=L[2] n=1"

-- deconCollectSpread_t__p_l12: h, t... = spread(([1, 2], 3)) \n t
def case_deconCollectSpread_t__p_l12 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.listLiteral [(.num 1), (.num 2)]), (.num 3)]))]), privateProp "t" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .variadic }]] [] [] [.param "t"])) (alg [] [] [] [.resolve "d"])])] [.resolve "t"])
#guard obs case_deconCollectSpread_t__p_l12 == "ok raw=L[3] n=1"

-- deconCollectSpread_t__pl1: h, t... = spread(([1])) \n t
def case_deconCollectSpread_t__pl1 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.listLiteral [(.num 1)])]))]), privateProp "t" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .variadic }]] [] [] [.param "t"])) (alg [] [] [] [.resolve "d"])])] [.resolve "t"])
#guard obs case_deconCollectSpread_t__pl1 == "ok raw=L[] n=1"

-- deconPrefix_p__e: p..., z = () \n p
def case_deconPrefix_p__e : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.emptySequence 0)]), privateProp "p" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .variadic }, .capture { name := "z" }]] [] [] [.param "p"])) (alg [] [] [] [.resolve "d"])])] [.resolve "p"])
#guard obs case_deconPrefix_p__e == "err arity"

-- deconPrefix_p__n0: p..., z = 0 \n p
def case_deconPrefix_p__n0 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.num 0)]), privateProp "p" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .variadic }, .capture { name := "z" }]] [] [] [.param "p"])) (alg [] [] [] [.resolve "d"])])] [.resolve "p"])
#guard obs case_deconPrefix_p__n0 == "ok raw=L[] n=1"

-- deconPrefix_p__n1: p..., z = 1 \n p
def case_deconPrefix_p__n1 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.num 1)]), privateProp "p" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .variadic }, .capture { name := "z" }]] [] [] [.param "p"])) (alg [] [] [] [.resolve "d"])])] [.resolve "p"])
#guard obs case_deconPrefix_p__n1 == "ok raw=L[] n=1"

-- deconPrefix_p__p1: p..., z = (1) \n p
def case_deconPrefix_p__p1 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.block (alg [] [] [] [(.num 1)]))]), privateProp "p" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .variadic }, .capture { name := "z" }]] [] [] [.param "p"])) (alg [] [] [] [.resolve "d"])])] [.resolve "p"])
#guard obs case_deconPrefix_p__p1 == "ok raw=L[] n=1"

-- deconPrefix_p__p12: p..., z = (1, 2) \n p
def case_deconPrefix_p__p12 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)]))]), privateProp "p" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .variadic }, .capture { name := "z" }]] [] [] [.param "p"])) (alg [] [] [] [.resolve "d"])])] [.resolve "p"])
#guard obs case_deconPrefix_p__p12 == "ok raw=L[1] n=1"

-- deconPrefix_p__p123: p..., z = (1, 2, 3) \n p
def case_deconPrefix_p__p123 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2), (.num 3)]))]), privateProp "p" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .variadic }, .capture { name := "z" }]] [] [] [.param "p"])) (alg [] [] [] [.resolve "d"])])] [.resolve "p"])
#guard obs case_deconPrefix_p__p123 == "ok raw=L[1, 2] n=1"

-- deconPrefix_p__pee: p..., z = ((), ()) \n p
def case_deconPrefix_p__pee : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.emptySequence 0)]))]), privateProp "p" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .variadic }, .capture { name := "z" }]] [] [] [.param "p"])) (alg [] [] [] [.resolve "d"])])] [.resolve "p"])
#guard obs case_deconPrefix_p__pee == "ok raw=L[S[]] n=1"

-- deconPrefix_p__pe1: p..., z = ((), 1) \n p
def case_deconPrefix_p__pe1 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.num 1)]))]), privateProp "p" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .variadic }, .capture { name := "z" }]] [] [] [.param "p"])) (alg [] [] [] [.resolve "d"])])] [.resolve "p"])
#guard obs case_deconPrefix_p__pe1 == "ok raw=L[S[]] n=1"

-- deconPrefix_p__p1e: p..., z = (1, ()) \n p
def case_deconPrefix_p__p1e : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.emptySequence 0)]))]), privateProp "p" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .variadic }, .capture { name := "z" }]] [] [] [.param "p"])) (alg [] [] [] [.resolve "d"])])] [.resolve "p"])
#guard obs case_deconPrefix_p__p1e == "ok raw=L[1] n=1"

-- deconPrefix_p__p12_3: p..., z = ((1, 2), 3) \n p
def case_deconPrefix_p__p12_3 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.num 3)]))]), privateProp "p" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .variadic }, .capture { name := "z" }]] [] [] [.param "p"])) (alg [] [] [] [.resolve "d"])])] [.resolve "p"])
#guard obs case_deconPrefix_p__p12_3 == "ok raw=L[S[1, 2]] n=1"

-- deconPrefix_p__p12_34: p..., z = ((1, 2), (3, 4)) \n p
def case_deconPrefix_p__p12_34 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.block (alg [] [] [] [(.num 3), (.num 4)]))]))]), privateProp "p" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .variadic }, .capture { name := "z" }]] [] [] [.param "p"])) (alg [] [] [] [.resolve "d"])])] [.resolve "p"])
#guard obs case_deconPrefix_p__p12_34 == "ok raw=L[S[1, 2]] n=1"

-- deconPrefix_p__pe_12: p..., z = ((), (1, 2)) \n p
def case_deconPrefix_p__pe_12 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.block (alg [] [] [] [(.num 1), (.num 2)]))]))]), privateProp "p" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .variadic }, .capture { name := "z" }]] [] [] [.param "p"])) (alg [] [] [] [.resolve "d"])])] [.resolve "p"])
#guard obs case_deconPrefix_p__pe_12 == "ok raw=L[S[]] n=1"

-- deconPrefix_p__ppe1_2: p..., z = (((), 1), 2) \n p
def case_deconPrefix_p__ppe1_2 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.num 1)])), (.num 2)]))]), privateProp "p" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .variadic }, .capture { name := "z" }]] [] [] [.param "p"])) (alg [] [] [] [.resolve "d"])])] [.resolve "p"])
#guard obs case_deconPrefix_p__ppe1_2 == "ok raw=L[S[S[], 1]] n=1"

-- deconPrefix_p__p12_e: p..., z = ((1, 2), ()) \n p
def case_deconPrefix_p__p12_e : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.emptySequence 0)]))]), privateProp "p" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .variadic }, .capture { name := "z" }]] [] [] [.param "p"])) (alg [] [] [] [.resolve "d"])])] [.resolve "p"])
#guard obs case_deconPrefix_p__p12_e == "ok raw=L[S[1, 2]] n=1"

-- deconPrefix_p__ppe: p..., z = (()) \n p
def case_deconPrefix_p__ppe : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0)]))]), privateProp "p" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .variadic }, .capture { name := "z" }]] [] [] [.param "p"])) (alg [] [] [] [.resolve "d"])])] [.resolve "p"])
#guard obs case_deconPrefix_p__ppe == "err arity"

-- deconPrefix_p__pp1: p..., z = ((1)) \n p
def case_deconPrefix_p__pp1 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1)]))]))]), privateProp "p" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .variadic }, .capture { name := "z" }]] [] [] [.param "p"])) (alg [] [] [] [.resolve "d"])])] [.resolve "p"])
#guard obs case_deconPrefix_p__pp1 == "ok raw=L[] n=1"

-- deconPrefix_p__ppp12: p..., z = (((1, 2))) \n p
def case_deconPrefix_p__ppp12 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)]))]))]))]), privateProp "p" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .variadic }, .capture { name := "z" }]] [] [] [.param "p"])) (alg [] [] [] [.resolve "d"])])] [.resolve "p"])
#guard obs case_deconPrefix_p__ppp12 == "ok raw=L[1] n=1"

-- deconPrefix_p__le: p..., z = [] \n p
def case_deconPrefix_p__le : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.listLiteral [])]), privateProp "p" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .variadic }, .capture { name := "z" }]] [] [] [.param "p"])) (alg [] [] [] [.resolve "d"])])] [.resolve "p"])
#guard obs case_deconPrefix_p__le == "err arity"

-- deconPrefix_p__l7: p..., z = [7] \n p
def case_deconPrefix_p__l7 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.listLiteral [(.num 7)])]), privateProp "p" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .variadic }, .capture { name := "z" }]] [] [] [.param "p"])) (alg [] [] [] [.resolve "d"])])] [.resolve "p"])
#guard obs case_deconPrefix_p__l7 == "ok raw=L[] n=1"

-- deconPrefix_p__l12: p..., z = [1, 2] \n p
def case_deconPrefix_p__l12 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.listLiteral [(.num 1), (.num 2)])]), privateProp "p" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .variadic }, .capture { name := "z" }]] [] [] [.param "p"])) (alg [] [] [] [.resolve "d"])])] [.resolve "p"])
#guard obs case_deconPrefix_p__l12 == "ok raw=L[1] n=1"

-- deconPrefix_p__l12_3: p..., z = [[1, 2], 3] \n p
def case_deconPrefix_p__l12_3 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.listLiteral [(.listLiteral [(.num 1), (.num 2)]), (.num 3)])]), privateProp "p" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .variadic }, .capture { name := "z" }]] [] [] [.param "p"])) (alg [] [] [] [.resolve "d"])])] [.resolve "p"])
#guard obs case_deconPrefix_p__l12_3 == "ok raw=L[L[1, 2]] n=1"

-- deconPrefix_p__lle: p..., z = [[]] \n p
def case_deconPrefix_p__lle : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.listLiteral [(.listLiteral [])])]), privateProp "p" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .variadic }, .capture { name := "z" }]] [] [] [.param "p"])) (alg [] [] [] [.resolve "d"])])] [.resolve "p"])
#guard obs case_deconPrefix_p__lle == "ok raw=L[] n=1"

-- deconPrefix_p__l_e: p..., z = [()] \n p
def case_deconPrefix_p__l_e : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.listLiteral [(.emptySequence 0)])]), privateProp "p" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .variadic }, .capture { name := "z" }]] [] [] [.param "p"])) (alg [] [] [] [.resolve "d"])])] [.resolve "p"])
#guard obs case_deconPrefix_p__l_e == "ok raw=L[] n=1"

-- deconPrefix_p__l_p12: p..., z = [(1, 2)] \n p
def case_deconPrefix_p__l_p12 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.listLiteral [(.block (alg [] [] [] [(.num 1), (.num 2)]))])]), privateProp "p" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .variadic }, .capture { name := "z" }]] [] [] [.param "p"])) (alg [] [] [] [.resolve "d"])])] [.resolve "p"])
#guard obs case_deconPrefix_p__l_p12 == "ok raw=L[] n=1"

-- deconPrefix_p__p_l12: p..., z = ([1, 2], 3) \n p
def case_deconPrefix_p__p_l12 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.block (alg [] [] [] [(.listLiteral [(.num 1), (.num 2)]), (.num 3)]))]), privateProp "p" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .variadic }, .capture { name := "z" }]] [] [] [.param "p"])) (alg [] [] [] [.resolve "d"])])] [.resolve "p"])
#guard obs case_deconPrefix_p__p_l12 == "ok raw=L[L[1, 2]] n=1"

-- deconPrefix_p__pl1: p..., z = ([1]) \n p
def case_deconPrefix_p__pl1 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.block (alg [] [] [] [(.listLiteral [(.num 1)])]))]), privateProp "p" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .variadic }, .capture { name := "z" }]] [] [] [.param "p"])) (alg [] [] [] [.resolve "d"])])] [.resolve "p"])
#guard obs case_deconPrefix_p__pl1 == "ok raw=L[] n=1"

-- deconPrefix_z__e: p..., z = () \n z
def case_deconPrefix_z__e : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.emptySequence 0)]), privateProp "z" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .variadic }, .capture { name := "z" }]] [] [] [.param "z"])) (alg [] [] [] [.resolve "d"])])] [.resolve "z"])
#guard obs case_deconPrefix_z__e == "err arity"

-- deconPrefix_z__n0: p..., z = 0 \n z
def case_deconPrefix_z__n0 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.num 0)]), privateProp "z" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .variadic }, .capture { name := "z" }]] [] [] [.param "z"])) (alg [] [] [] [.resolve "d"])])] [.resolve "z"])
#guard obs case_deconPrefix_z__n0 == "ok raw=0 n=1"

-- deconPrefix_z__n1: p..., z = 1 \n z
def case_deconPrefix_z__n1 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.num 1)]), privateProp "z" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .variadic }, .capture { name := "z" }]] [] [] [.param "z"])) (alg [] [] [] [.resolve "d"])])] [.resolve "z"])
#guard obs case_deconPrefix_z__n1 == "ok raw=1 n=1"

-- deconPrefix_z__p1: p..., z = (1) \n z
def case_deconPrefix_z__p1 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.block (alg [] [] [] [(.num 1)]))]), privateProp "z" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .variadic }, .capture { name := "z" }]] [] [] [.param "z"])) (alg [] [] [] [.resolve "d"])])] [.resolve "z"])
#guard obs case_deconPrefix_z__p1 == "ok raw=1 n=1"

-- deconPrefix_z__p12: p..., z = (1, 2) \n z
def case_deconPrefix_z__p12 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)]))]), privateProp "z" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .variadic }, .capture { name := "z" }]] [] [] [.param "z"])) (alg [] [] [] [.resolve "d"])])] [.resolve "z"])
#guard obs case_deconPrefix_z__p12 == "ok raw=2 n=1"

-- deconPrefix_z__p123: p..., z = (1, 2, 3) \n z
def case_deconPrefix_z__p123 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2), (.num 3)]))]), privateProp "z" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .variadic }, .capture { name := "z" }]] [] [] [.param "z"])) (alg [] [] [] [.resolve "d"])])] [.resolve "z"])
#guard obs case_deconPrefix_z__p123 == "ok raw=3 n=1"

-- deconPrefix_z__pee: p..., z = ((), ()) \n z
def case_deconPrefix_z__pee : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.emptySequence 0)]))]), privateProp "z" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .variadic }, .capture { name := "z" }]] [] [] [.param "z"])) (alg [] [] [] [.resolve "d"])])] [.resolve "z"])
#guard obs case_deconPrefix_z__pee == "ok raw=S[] n=1"

-- deconPrefix_z__pe1: p..., z = ((), 1) \n z
def case_deconPrefix_z__pe1 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.num 1)]))]), privateProp "z" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .variadic }, .capture { name := "z" }]] [] [] [.param "z"])) (alg [] [] [] [.resolve "d"])])] [.resolve "z"])
#guard obs case_deconPrefix_z__pe1 == "ok raw=1 n=1"

-- deconPrefix_z__p1e: p..., z = (1, ()) \n z
def case_deconPrefix_z__p1e : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.emptySequence 0)]))]), privateProp "z" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .variadic }, .capture { name := "z" }]] [] [] [.param "z"])) (alg [] [] [] [.resolve "d"])])] [.resolve "z"])
#guard obs case_deconPrefix_z__p1e == "ok raw=S[] n=1"

-- deconPrefix_z__p12_3: p..., z = ((1, 2), 3) \n z
def case_deconPrefix_z__p12_3 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.num 3)]))]), privateProp "z" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .variadic }, .capture { name := "z" }]] [] [] [.param "z"])) (alg [] [] [] [.resolve "d"])])] [.resolve "z"])
#guard obs case_deconPrefix_z__p12_3 == "ok raw=3 n=1"

-- deconPrefix_z__p12_34: p..., z = ((1, 2), (3, 4)) \n z
def case_deconPrefix_z__p12_34 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.block (alg [] [] [] [(.num 3), (.num 4)]))]))]), privateProp "z" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .variadic }, .capture { name := "z" }]] [] [] [.param "z"])) (alg [] [] [] [.resolve "d"])])] [.resolve "z"])
#guard obs case_deconPrefix_z__p12_34 == "ok raw=S[3, 4] n=1"

-- deconPrefix_z__pe_12: p..., z = ((), (1, 2)) \n z
def case_deconPrefix_z__pe_12 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.block (alg [] [] [] [(.num 1), (.num 2)]))]))]), privateProp "z" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .variadic }, .capture { name := "z" }]] [] [] [.param "z"])) (alg [] [] [] [.resolve "d"])])] [.resolve "z"])
#guard obs case_deconPrefix_z__pe_12 == "ok raw=S[1, 2] n=1"

-- deconPrefix_z__ppe1_2: p..., z = (((), 1), 2) \n z
def case_deconPrefix_z__ppe1_2 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.num 1)])), (.num 2)]))]), privateProp "z" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .variadic }, .capture { name := "z" }]] [] [] [.param "z"])) (alg [] [] [] [.resolve "d"])])] [.resolve "z"])
#guard obs case_deconPrefix_z__ppe1_2 == "ok raw=2 n=1"

-- deconPrefix_z__p12_e: p..., z = ((1, 2), ()) \n z
def case_deconPrefix_z__p12_e : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.emptySequence 0)]))]), privateProp "z" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .variadic }, .capture { name := "z" }]] [] [] [.param "z"])) (alg [] [] [] [.resolve "d"])])] [.resolve "z"])
#guard obs case_deconPrefix_z__p12_e == "ok raw=S[] n=1"

-- deconPrefix_z__ppe: p..., z = (()) \n z
def case_deconPrefix_z__ppe : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0)]))]), privateProp "z" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .variadic }, .capture { name := "z" }]] [] [] [.param "z"])) (alg [] [] [] [.resolve "d"])])] [.resolve "z"])
#guard obs case_deconPrefix_z__ppe == "err arity"

-- deconPrefix_z__pp1: p..., z = ((1)) \n z
def case_deconPrefix_z__pp1 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1)]))]))]), privateProp "z" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .variadic }, .capture { name := "z" }]] [] [] [.param "z"])) (alg [] [] [] [.resolve "d"])])] [.resolve "z"])
#guard obs case_deconPrefix_z__pp1 == "ok raw=1 n=1"

-- deconPrefix_z__ppp12: p..., z = (((1, 2))) \n z
def case_deconPrefix_z__ppp12 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)]))]))]))]), privateProp "z" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .variadic }, .capture { name := "z" }]] [] [] [.param "z"])) (alg [] [] [] [.resolve "d"])])] [.resolve "z"])
#guard obs case_deconPrefix_z__ppp12 == "ok raw=2 n=1"

-- deconPrefix_z__le: p..., z = [] \n z
def case_deconPrefix_z__le : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.listLiteral [])]), privateProp "z" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .variadic }, .capture { name := "z" }]] [] [] [.param "z"])) (alg [] [] [] [.resolve "d"])])] [.resolve "z"])
#guard obs case_deconPrefix_z__le == "err arity"

-- deconPrefix_z__l7: p..., z = [7] \n z
def case_deconPrefix_z__l7 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.listLiteral [(.num 7)])]), privateProp "z" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .variadic }, .capture { name := "z" }]] [] [] [.param "z"])) (alg [] [] [] [.resolve "d"])])] [.resolve "z"])
#guard obs case_deconPrefix_z__l7 == "ok raw=7 n=1"

-- deconPrefix_z__l12: p..., z = [1, 2] \n z
def case_deconPrefix_z__l12 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.listLiteral [(.num 1), (.num 2)])]), privateProp "z" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .variadic }, .capture { name := "z" }]] [] [] [.param "z"])) (alg [] [] [] [.resolve "d"])])] [.resolve "z"])
#guard obs case_deconPrefix_z__l12 == "ok raw=2 n=1"

-- deconPrefix_z__l12_3: p..., z = [[1, 2], 3] \n z
def case_deconPrefix_z__l12_3 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.listLiteral [(.listLiteral [(.num 1), (.num 2)]), (.num 3)])]), privateProp "z" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .variadic }, .capture { name := "z" }]] [] [] [.param "z"])) (alg [] [] [] [.resolve "d"])])] [.resolve "z"])
#guard obs case_deconPrefix_z__l12_3 == "ok raw=3 n=1"

-- deconPrefix_z__lle: p..., z = [[]] \n z
def case_deconPrefix_z__lle : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.listLiteral [(.listLiteral [])])]), privateProp "z" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .variadic }, .capture { name := "z" }]] [] [] [.param "z"])) (alg [] [] [] [.resolve "d"])])] [.resolve "z"])
#guard obs case_deconPrefix_z__lle == "ok raw=L[] n=1"

-- deconPrefix_z__l_e: p..., z = [()] \n z
def case_deconPrefix_z__l_e : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.listLiteral [(.emptySequence 0)])]), privateProp "z" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .variadic }, .capture { name := "z" }]] [] [] [.param "z"])) (alg [] [] [] [.resolve "d"])])] [.resolve "z"])
#guard obs case_deconPrefix_z__l_e == "ok raw=S[] n=1"

-- deconPrefix_z__l_p12: p..., z = [(1, 2)] \n z
def case_deconPrefix_z__l_p12 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.listLiteral [(.block (alg [] [] [] [(.num 1), (.num 2)]))])]), privateProp "z" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .variadic }, .capture { name := "z" }]] [] [] [.param "z"])) (alg [] [] [] [.resolve "d"])])] [.resolve "z"])
#guard obs case_deconPrefix_z__l_p12 == "ok raw=S[1, 2] n=1"

-- deconPrefix_z__p_l12: p..., z = ([1, 2], 3) \n z
def case_deconPrefix_z__p_l12 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.block (alg [] [] [] [(.listLiteral [(.num 1), (.num 2)]), (.num 3)]))]), privateProp "z" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .variadic }, .capture { name := "z" }]] [] [] [.param "z"])) (alg [] [] [] [.resolve "d"])])] [.resolve "z"])
#guard obs case_deconPrefix_z__p_l12 == "ok raw=3 n=1"

-- deconPrefix_z__pl1: p..., z = ([1]) \n z
def case_deconPrefix_z__pl1 : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.block (alg [] [] [] [(.listLiteral [(.num 1)])]))]), privateProp "z" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .variadic }, .capture { name := "z" }]] [] [] [.param "z"])) (alg [] [] [] [.resolve "d"])])] [.resolve "z"])
#guard obs case_deconPrefix_z__pl1 == "ok raw=1 n=1"

-- seqWrapPair__e: ((), 99)
def case_seqWrapPair__e : Expr :=
  .block (alg [] [] [] [.block (alg [] [] [] [(.emptySequence 0), .num 99])])
#guard obs case_seqWrapPair__e == "ok raw=S[S[], 99] n=1"

-- seqWrapPair__n0: (0, 99)
def case_seqWrapPair__n0 : Expr :=
  .block (alg [] [] [] [.block (alg [] [] [] [(.num 0), .num 99])])
#guard obs case_seqWrapPair__n0 == "ok raw=S[0, 99] n=1"

-- seqWrapPair__n1: (1, 99)
def case_seqWrapPair__n1 : Expr :=
  .block (alg [] [] [] [.block (alg [] [] [] [(.num 1), .num 99])])
#guard obs case_seqWrapPair__n1 == "ok raw=S[1, 99] n=1"

-- seqWrapPair__p1: ((1), 99)
def case_seqWrapPair__p1 : Expr :=
  .block (alg [] [] [] [.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1)])), .num 99])])
#guard obs case_seqWrapPair__p1 == "ok raw=S[1, 99] n=1"

-- seqWrapPair__p12: ((1, 2), 99)
def case_seqWrapPair__p12 : Expr :=
  .block (alg [] [] [] [.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), .num 99])])
#guard obs case_seqWrapPair__p12 == "ok raw=S[S[1, 2], 99] n=1"

-- seqWrapPair__p123: ((1, 2, 3), 99)
def case_seqWrapPair__p123 : Expr :=
  .block (alg [] [] [] [.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2), (.num 3)])), .num 99])])
#guard obs case_seqWrapPair__p123 == "ok raw=S[S[1, 2, 3], 99] n=1"

-- seqWrapPair__pee: (((), ()), 99)
def case_seqWrapPair__pee : Expr :=
  .block (alg [] [] [] [.block (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.emptySequence 0)])), .num 99])])
#guard obs case_seqWrapPair__pee == "ok raw=S[S[S[], S[]], 99] n=1"

-- seqWrapPair__pe1: (((), 1), 99)
def case_seqWrapPair__pe1 : Expr :=
  .block (alg [] [] [] [.block (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.num 1)])), .num 99])])
#guard obs case_seqWrapPair__pe1 == "ok raw=S[S[S[], 1], 99] n=1"

-- seqWrapPair__p1e: ((1, ()), 99)
def case_seqWrapPair__p1e : Expr :=
  .block (alg [] [] [] [.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.emptySequence 0)])), .num 99])])
#guard obs case_seqWrapPair__p1e == "ok raw=S[S[1, S[]], 99] n=1"

-- seqWrapPair__p12_3: (((1, 2), 3), 99)
def case_seqWrapPair__p12_3 : Expr :=
  .block (alg [] [] [] [.block (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.num 3)])), .num 99])])
#guard obs case_seqWrapPair__p12_3 == "ok raw=S[S[S[1, 2], 3], 99] n=1"

-- seqWrapPair__p12_34: (((1, 2), (3, 4)), 99)
def case_seqWrapPair__p12_34 : Expr :=
  .block (alg [] [] [] [.block (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.block (alg [] [] [] [(.num 3), (.num 4)]))])), .num 99])])
#guard obs case_seqWrapPair__p12_34 == "ok raw=S[S[S[1, 2], S[3, 4]], 99] n=1"

-- seqWrapPair__pe_12: (((), (1, 2)), 99)
def case_seqWrapPair__pe_12 : Expr :=
  .block (alg [] [] [] [.block (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.block (alg [] [] [] [(.num 1), (.num 2)]))])), .num 99])])
#guard obs case_seqWrapPair__pe_12 == "ok raw=S[S[S[], S[1, 2]], 99] n=1"

-- seqWrapPair__ppe1_2: ((((), 1), 2), 99)
def case_seqWrapPair__ppe1_2 : Expr :=
  .block (alg [] [] [] [.block (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.num 1)])), (.num 2)])), .num 99])])
#guard obs case_seqWrapPair__ppe1_2 == "ok raw=S[S[S[S[], 1], 2], 99] n=1"

-- seqWrapPair__p12_e: (((1, 2), ()), 99)
def case_seqWrapPair__p12_e : Expr :=
  .block (alg [] [] [] [.block (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.emptySequence 0)])), .num 99])])
#guard obs case_seqWrapPair__p12_e == "ok raw=S[S[S[1, 2], S[]], 99] n=1"

-- seqWrapPair__ppe: ((()), 99)
def case_seqWrapPair__ppe : Expr :=
  .block (alg [] [] [] [.block (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0)])), .num 99])])
#guard obs case_seqWrapPair__ppe == "ok raw=S[S[], 99] n=1"

-- seqWrapPair__pp1: (((1)), 99)
def case_seqWrapPair__pp1 : Expr :=
  .block (alg [] [] [] [.block (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1)]))])), .num 99])])
#guard obs case_seqWrapPair__pp1 == "ok raw=S[1, 99] n=1"

-- seqWrapPair__ppp12: ((((1, 2))), 99)
def case_seqWrapPair__ppp12 : Expr :=
  .block (alg [] [] [] [.block (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)]))]))])), .num 99])])
#guard obs case_seqWrapPair__ppp12 == "ok raw=S[S[1, 2], 99] n=1"

-- seqWrapPair__le: ([], 99)
def case_seqWrapPair__le : Expr :=
  .block (alg [] [] [] [.block (alg [] [] [] [(.listLiteral []), .num 99])])
#guard obs case_seqWrapPair__le == "ok raw=S[L[], 99] n=1"

-- seqWrapPair__l7: ([7], 99)
def case_seqWrapPair__l7 : Expr :=
  .block (alg [] [] [] [.block (alg [] [] [] [(.listLiteral [(.num 7)]), .num 99])])
#guard obs case_seqWrapPair__l7 == "ok raw=S[L[7], 99] n=1"

-- seqWrapPair__l12: ([1, 2], 99)
def case_seqWrapPair__l12 : Expr :=
  .block (alg [] [] [] [.block (alg [] [] [] [(.listLiteral [(.num 1), (.num 2)]), .num 99])])
#guard obs case_seqWrapPair__l12 == "ok raw=S[L[1, 2], 99] n=1"

-- seqWrapPair__l12_3: ([[1, 2], 3], 99)
def case_seqWrapPair__l12_3 : Expr :=
  .block (alg [] [] [] [.block (alg [] [] [] [(.listLiteral [(.listLiteral [(.num 1), (.num 2)]), (.num 3)]), .num 99])])
#guard obs case_seqWrapPair__l12_3 == "ok raw=S[L[L[1, 2], 3], 99] n=1"

-- seqWrapPair__lle: ([[]], 99)
def case_seqWrapPair__lle : Expr :=
  .block (alg [] [] [] [.block (alg [] [] [] [(.listLiteral [(.listLiteral [])]), .num 99])])
#guard obs case_seqWrapPair__lle == "ok raw=S[L[L[]], 99] n=1"

-- seqWrapPair__l_e: ([()], 99)
def case_seqWrapPair__l_e : Expr :=
  .block (alg [] [] [] [.block (alg [] [] [] [(.listLiteral [(.emptySequence 0)]), .num 99])])
#guard obs case_seqWrapPair__l_e == "ok raw=S[L[S[]], 99] n=1"

-- seqWrapPair__l_p12: ([(1, 2)], 99)
def case_seqWrapPair__l_p12 : Expr :=
  .block (alg [] [] [] [.block (alg [] [] [] [(.listLiteral [(.block (alg [] [] [] [(.num 1), (.num 2)]))]), .num 99])])
#guard obs case_seqWrapPair__l_p12 == "ok raw=S[L[S[1, 2]], 99] n=1"

-- seqWrapPair__p_l12: (([1, 2], 3), 99)
def case_seqWrapPair__p_l12 : Expr :=
  .block (alg [] [] [] [.block (alg [] [] [] [(.block (alg [] [] [] [(.listLiteral [(.num 1), (.num 2)]), (.num 3)])), .num 99])])
#guard obs case_seqWrapPair__p_l12 == "ok raw=S[S[L[1, 2], 3], 99] n=1"

-- seqWrapPair__pl1: (([1]), 99)
def case_seqWrapPair__pl1 : Expr :=
  .block (alg [] [] [] [.block (alg [] [] [] [(.block (alg [] [] [] [(.listLiteral [(.num 1)])])), .num 99])])
#guard obs case_seqWrapPair__pl1 == "ok raw=S[L[1], 99] n=1"

-- seqWrapSolo__e: (())
def case_seqWrapSolo__e : Expr :=
  .block (alg [] [] [] [.block (alg [] [] [] [(.emptySequence 0)])])
#guard obs case_seqWrapSolo__e == "ok raw=S[] n=1"

-- seqWrapSolo__n0: (0)
def case_seqWrapSolo__n0 : Expr :=
  .block (alg [] [] [] [.block (alg [] [] [] [(.num 0)])])
#guard obs case_seqWrapSolo__n0 == "ok raw=0 n=1"

-- seqWrapSolo__n1: (1)
def case_seqWrapSolo__n1 : Expr :=
  .block (alg [] [] [] [.block (alg [] [] [] [(.num 1)])])
#guard obs case_seqWrapSolo__n1 == "ok raw=1 n=1"

-- seqWrapSolo__p1: ((1))
def case_seqWrapSolo__p1 : Expr :=
  .block (alg [] [] [] [.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1)]))])])
#guard obs case_seqWrapSolo__p1 == "ok raw=1 n=1"

-- seqWrapSolo__p12: ((1, 2))
def case_seqWrapSolo__p12 : Expr :=
  .block (alg [] [] [] [.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)]))])])
#guard obs case_seqWrapSolo__p12 == "ok raw=S[1, 2] n=1"

-- seqWrapSolo__p123: ((1, 2, 3))
def case_seqWrapSolo__p123 : Expr :=
  .block (alg [] [] [] [.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2), (.num 3)]))])])
#guard obs case_seqWrapSolo__p123 == "ok raw=S[1, 2, 3] n=1"

-- seqWrapSolo__pee: (((), ()))
def case_seqWrapSolo__pee : Expr :=
  .block (alg [] [] [] [.block (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.emptySequence 0)]))])])
#guard obs case_seqWrapSolo__pee == "ok raw=S[S[], S[]] n=1"

-- seqWrapSolo__pe1: (((), 1))
def case_seqWrapSolo__pe1 : Expr :=
  .block (alg [] [] [] [.block (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.num 1)]))])])
#guard obs case_seqWrapSolo__pe1 == "ok raw=S[S[], 1] n=1"

-- seqWrapSolo__p1e: ((1, ()))
def case_seqWrapSolo__p1e : Expr :=
  .block (alg [] [] [] [.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.emptySequence 0)]))])])
#guard obs case_seqWrapSolo__p1e == "ok raw=S[1, S[]] n=1"

-- seqWrapSolo__p12_3: (((1, 2), 3))
def case_seqWrapSolo__p12_3 : Expr :=
  .block (alg [] [] [] [.block (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.num 3)]))])])
#guard obs case_seqWrapSolo__p12_3 == "ok raw=S[S[1, 2], 3] n=1"

-- seqWrapSolo__p12_34: (((1, 2), (3, 4)))
def case_seqWrapSolo__p12_34 : Expr :=
  .block (alg [] [] [] [.block (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.block (alg [] [] [] [(.num 3), (.num 4)]))]))])])
#guard obs case_seqWrapSolo__p12_34 == "ok raw=S[S[1, 2], S[3, 4]] n=1"

-- seqWrapSolo__pe_12: (((), (1, 2)))
def case_seqWrapSolo__pe_12 : Expr :=
  .block (alg [] [] [] [.block (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.block (alg [] [] [] [(.num 1), (.num 2)]))]))])])
#guard obs case_seqWrapSolo__pe_12 == "ok raw=S[S[], S[1, 2]] n=1"

-- seqWrapSolo__ppe1_2: ((((), 1), 2))
def case_seqWrapSolo__ppe1_2 : Expr :=
  .block (alg [] [] [] [.block (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.num 1)])), (.num 2)]))])])
#guard obs case_seqWrapSolo__ppe1_2 == "ok raw=S[S[S[], 1], 2] n=1"

-- seqWrapSolo__p12_e: (((1, 2), ()))
def case_seqWrapSolo__p12_e : Expr :=
  .block (alg [] [] [] [.block (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.emptySequence 0)]))])])
#guard obs case_seqWrapSolo__p12_e == "ok raw=S[S[1, 2], S[]] n=1"

-- seqWrapSolo__ppe: ((()))
def case_seqWrapSolo__ppe : Expr :=
  .block (alg [] [] [] [.block (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0)]))])])
#guard obs case_seqWrapSolo__ppe == "ok raw=S[] n=1"

-- seqWrapSolo__pp1: (((1)))
def case_seqWrapSolo__pp1 : Expr :=
  .block (alg [] [] [] [.block (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1)]))]))])])
#guard obs case_seqWrapSolo__pp1 == "ok raw=1 n=1"

-- seqWrapSolo__ppp12: ((((1, 2))))
def case_seqWrapSolo__ppp12 : Expr :=
  .block (alg [] [] [] [.block (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)]))]))]))])])
#guard obs case_seqWrapSolo__ppp12 == "ok raw=S[1, 2] n=1"

-- seqWrapSolo__le: ([])
def case_seqWrapSolo__le : Expr :=
  .block (alg [] [] [] [.block (alg [] [] [] [(.listLiteral [])])])
#guard obs case_seqWrapSolo__le == "ok raw=L[] n=1"

-- seqWrapSolo__l7: ([7])
def case_seqWrapSolo__l7 : Expr :=
  .block (alg [] [] [] [.block (alg [] [] [] [(.listLiteral [(.num 7)])])])
#guard obs case_seqWrapSolo__l7 == "ok raw=L[7] n=1"

-- seqWrapSolo__l12: ([1, 2])
def case_seqWrapSolo__l12 : Expr :=
  .block (alg [] [] [] [.block (alg [] [] [] [(.listLiteral [(.num 1), (.num 2)])])])
#guard obs case_seqWrapSolo__l12 == "ok raw=L[1, 2] n=1"

-- seqWrapSolo__l12_3: ([[1, 2], 3])
def case_seqWrapSolo__l12_3 : Expr :=
  .block (alg [] [] [] [.block (alg [] [] [] [(.listLiteral [(.listLiteral [(.num 1), (.num 2)]), (.num 3)])])])
#guard obs case_seqWrapSolo__l12_3 == "ok raw=L[L[1, 2], 3] n=1"

-- seqWrapSolo__lle: ([[]])
def case_seqWrapSolo__lle : Expr :=
  .block (alg [] [] [] [.block (alg [] [] [] [(.listLiteral [(.listLiteral [])])])])
#guard obs case_seqWrapSolo__lle == "ok raw=L[L[]] n=1"

-- seqWrapSolo__l_e: ([()])
def case_seqWrapSolo__l_e : Expr :=
  .block (alg [] [] [] [.block (alg [] [] [] [(.listLiteral [(.emptySequence 0)])])])
#guard obs case_seqWrapSolo__l_e == "ok raw=L[S[]] n=1"

-- seqWrapSolo__l_p12: ([(1, 2)])
def case_seqWrapSolo__l_p12 : Expr :=
  .block (alg [] [] [] [.block (alg [] [] [] [(.listLiteral [(.block (alg [] [] [] [(.num 1), (.num 2)]))])])])
#guard obs case_seqWrapSolo__l_p12 == "ok raw=L[S[1, 2]] n=1"

-- seqWrapSolo__p_l12: (([1, 2], 3))
def case_seqWrapSolo__p_l12 : Expr :=
  .block (alg [] [] [] [.block (alg [] [] [] [(.block (alg [] [] [] [(.listLiteral [(.num 1), (.num 2)]), (.num 3)]))])])
#guard obs case_seqWrapSolo__p_l12 == "ok raw=S[L[1, 2], 3] n=1"

-- seqWrapSolo__pl1: (([1]))
def case_seqWrapSolo__pl1 : Expr :=
  .block (alg [] [] [] [.block (alg [] [] [] [(.block (alg [] [] [] [(.listLiteral [(.num 1)])]))])])
#guard obs case_seqWrapSolo__pl1 == "ok raw=L[1] n=1"

-- spreadRoot__e: spread(())
def case_spreadRoot__e : Expr :=
  .block (alg [] [] [] [.sequenceSpread (.emptySequence 0)])
#guard obs case_spreadRoot__e == "ok raw=S[] n=0"

-- spreadRoot__n0: spread(0)
def case_spreadRoot__n0 : Expr :=
  .block (alg [] [] [] [.sequenceSpread (.num 0)])
#guard obs case_spreadRoot__n0 == "ok raw=0 n=1"

-- spreadRoot__n1: spread(1)
def case_spreadRoot__n1 : Expr :=
  .block (alg [] [] [] [.sequenceSpread (.num 1)])
#guard obs case_spreadRoot__n1 == "ok raw=1 n=1"

-- spreadRoot__p1: spread((1))
def case_spreadRoot__p1 : Expr :=
  .block (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.num 1)]))])
#guard obs case_spreadRoot__p1 == "ok raw=1 n=1"

-- spreadRoot__p12: spread((1, 2))
def case_spreadRoot__p12 : Expr :=
  .block (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.num 1), (.num 2)]))])
#guard obs case_spreadRoot__p12 == "ok raw=S[1, 2] n=2"

-- spreadRoot__p123: spread((1, 2, 3))
def case_spreadRoot__p123 : Expr :=
  .block (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.num 1), (.num 2), (.num 3)]))])
#guard obs case_spreadRoot__p123 == "ok raw=S[1, 2, 3] n=3"

-- spreadRoot__pee: spread(((), ()))
def case_spreadRoot__pee : Expr :=
  .block (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.emptySequence 0), (.emptySequence 0)]))])
#guard obs case_spreadRoot__pee == "ok raw=S[S[], S[]] n=2"

-- spreadRoot__pe1: spread(((), 1))
def case_spreadRoot__pe1 : Expr :=
  .block (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.emptySequence 0), (.num 1)]))])
#guard obs case_spreadRoot__pe1 == "ok raw=S[S[], 1] n=2"

-- spreadRoot__p1e: spread((1, ()))
def case_spreadRoot__p1e : Expr :=
  .block (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.num 1), (.emptySequence 0)]))])
#guard obs case_spreadRoot__p1e == "ok raw=S[1, S[]] n=2"

-- spreadRoot__p12_3: spread(((1, 2), 3))
def case_spreadRoot__p12_3 : Expr :=
  .block (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.num 3)]))])
#guard obs case_spreadRoot__p12_3 == "ok raw=S[S[1, 2], 3] n=2"

-- spreadRoot__p12_34: spread(((1, 2), (3, 4)))
def case_spreadRoot__p12_34 : Expr :=
  .block (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.block (alg [] [] [] [(.num 3), (.num 4)]))]))])
#guard obs case_spreadRoot__p12_34 == "ok raw=S[S[1, 2], S[3, 4]] n=2"

-- spreadRoot__pe_12: spread(((), (1, 2)))
def case_spreadRoot__pe_12 : Expr :=
  .block (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.emptySequence 0), (.block (alg [] [] [] [(.num 1), (.num 2)]))]))])
#guard obs case_spreadRoot__pe_12 == "ok raw=S[S[], S[1, 2]] n=2"

-- spreadRoot__ppe1_2: spread((((), 1), 2))
def case_spreadRoot__ppe1_2 : Expr :=
  .block (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.num 1)])), (.num 2)]))])
#guard obs case_spreadRoot__ppe1_2 == "ok raw=S[S[S[], 1], 2] n=2"

-- spreadRoot__p12_e: spread(((1, 2), ()))
def case_spreadRoot__p12_e : Expr :=
  .block (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.emptySequence 0)]))])
#guard obs case_spreadRoot__p12_e == "ok raw=S[S[1, 2], S[]] n=2"

-- spreadRoot__ppe: spread((()))
def case_spreadRoot__ppe : Expr :=
  .block (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.emptySequence 0)]))])
#guard obs case_spreadRoot__ppe == "ok raw=S[] n=0"

-- spreadRoot__pp1: spread(((1)))
def case_spreadRoot__pp1 : Expr :=
  .block (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1)]))]))])
#guard obs case_spreadRoot__pp1 == "ok raw=1 n=1"

-- spreadRoot__ppp12: spread((((1, 2))))
def case_spreadRoot__ppp12 : Expr :=
  .block (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)]))]))]))])
#guard obs case_spreadRoot__ppp12 == "ok raw=S[1, 2] n=2"

-- spreadRoot__le: spread([])
def case_spreadRoot__le : Expr :=
  .block (alg [] [] [] [.sequenceSpread (.listLiteral [])])
#guard obs case_spreadRoot__le == "ok raw=S[] n=0"

-- spreadRoot__l7: spread([7])
def case_spreadRoot__l7 : Expr :=
  .block (alg [] [] [] [.sequenceSpread (.listLiteral [(.num 7)])])
#guard obs case_spreadRoot__l7 == "ok raw=7 n=1"

-- spreadRoot__l12: spread([1, 2])
def case_spreadRoot__l12 : Expr :=
  .block (alg [] [] [] [.sequenceSpread (.listLiteral [(.num 1), (.num 2)])])
#guard obs case_spreadRoot__l12 == "ok raw=S[1, 2] n=2"

-- spreadRoot__l12_3: spread([[1, 2], 3])
def case_spreadRoot__l12_3 : Expr :=
  .block (alg [] [] [] [.sequenceSpread (.listLiteral [(.listLiteral [(.num 1), (.num 2)]), (.num 3)])])
#guard obs case_spreadRoot__l12_3 == "ok raw=S[L[1, 2], 3] n=2"

-- spreadRoot__lle: spread([[]])
def case_spreadRoot__lle : Expr :=
  .block (alg [] [] [] [.sequenceSpread (.listLiteral [(.listLiteral [])])])
#guard obs case_spreadRoot__lle == "ok raw=L[] n=1"

-- spreadRoot__l_e: spread([()])
def case_spreadRoot__l_e : Expr :=
  .block (alg [] [] [] [.sequenceSpread (.listLiteral [(.emptySequence 0)])])
#guard obs case_spreadRoot__l_e == "ok raw=S[] n=1"

-- spreadRoot__l_p12: spread([(1, 2)])
def case_spreadRoot__l_p12 : Expr :=
  .block (alg [] [] [] [.sequenceSpread (.listLiteral [(.block (alg [] [] [] [(.num 1), (.num 2)]))])])
#guard obs case_spreadRoot__l_p12 == "ok raw=S[1, 2] n=1"

-- spreadRoot__p_l12: spread(([1, 2], 3))
def case_spreadRoot__p_l12 : Expr :=
  .block (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.listLiteral [(.num 1), (.num 2)]), (.num 3)]))])
#guard obs case_spreadRoot__p_l12 == "ok raw=S[L[1, 2], 3] n=2"

-- spreadRoot__pl1: spread(([1]))
def case_spreadRoot__pl1 : Expr :=
  .block (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.listLiteral [(.num 1)])]))])
#guard obs case_spreadRoot__pl1 == "ok raw=1 n=1"

-- spreadInSeq__e: (spread(()), 99)
def case_spreadInSeq__e : Expr :=
  .block (alg [] [] [] [.block (alg [] [] [] [.sequenceSpread (.emptySequence 0), .num 99])])
#guard obs case_spreadInSeq__e == "ok raw=99 n=1"

-- spreadInSeq__n0: (spread(0), 99)
def case_spreadInSeq__n0 : Expr :=
  .block (alg [] [] [] [.block (alg [] [] [] [.sequenceSpread (.num 0), .num 99])])
#guard obs case_spreadInSeq__n0 == "ok raw=S[0, 99] n=1"

-- spreadInSeq__n1: (spread(1), 99)
def case_spreadInSeq__n1 : Expr :=
  .block (alg [] [] [] [.block (alg [] [] [] [.sequenceSpread (.num 1), .num 99])])
#guard obs case_spreadInSeq__n1 == "ok raw=S[1, 99] n=1"

-- spreadInSeq__p1: (spread((1)), 99)
def case_spreadInSeq__p1 : Expr :=
  .block (alg [] [] [] [.block (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.num 1)])), .num 99])])
#guard obs case_spreadInSeq__p1 == "ok raw=S[1, 99] n=1"

-- spreadInSeq__p12: (spread((1, 2)), 99)
def case_spreadInSeq__p12 : Expr :=
  .block (alg [] [] [] [.block (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.num 1), (.num 2)])), .num 99])])
#guard obs case_spreadInSeq__p12 == "ok raw=S[1, 2, 99] n=1"

-- spreadInSeq__p123: (spread((1, 2, 3)), 99)
def case_spreadInSeq__p123 : Expr :=
  .block (alg [] [] [] [.block (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.num 1), (.num 2), (.num 3)])), .num 99])])
#guard obs case_spreadInSeq__p123 == "ok raw=S[1, 2, 3, 99] n=1"

-- spreadInSeq__pee: (spread(((), ())), 99)
def case_spreadInSeq__pee : Expr :=
  .block (alg [] [] [] [.block (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.emptySequence 0), (.emptySequence 0)])), .num 99])])
#guard obs case_spreadInSeq__pee == "ok raw=S[S[], S[], 99] n=1"

-- spreadInSeq__pe1: (spread(((), 1)), 99)
def case_spreadInSeq__pe1 : Expr :=
  .block (alg [] [] [] [.block (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.emptySequence 0), (.num 1)])), .num 99])])
#guard obs case_spreadInSeq__pe1 == "ok raw=S[S[], 1, 99] n=1"

-- spreadInSeq__p1e: (spread((1, ())), 99)
def case_spreadInSeq__p1e : Expr :=
  .block (alg [] [] [] [.block (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.num 1), (.emptySequence 0)])), .num 99])])
#guard obs case_spreadInSeq__p1e == "ok raw=S[1, S[], 99] n=1"

-- spreadInSeq__p12_3: (spread(((1, 2), 3)), 99)
def case_spreadInSeq__p12_3 : Expr :=
  .block (alg [] [] [] [.block (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.num 3)])), .num 99])])
#guard obs case_spreadInSeq__p12_3 == "ok raw=S[S[1, 2], 3, 99] n=1"

-- spreadInSeq__p12_34: (spread(((1, 2), (3, 4))), 99)
def case_spreadInSeq__p12_34 : Expr :=
  .block (alg [] [] [] [.block (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.block (alg [] [] [] [(.num 3), (.num 4)]))])), .num 99])])
#guard obs case_spreadInSeq__p12_34 == "ok raw=S[S[1, 2], S[3, 4], 99] n=1"

-- spreadInSeq__pe_12: (spread(((), (1, 2))), 99)
def case_spreadInSeq__pe_12 : Expr :=
  .block (alg [] [] [] [.block (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.emptySequence 0), (.block (alg [] [] [] [(.num 1), (.num 2)]))])), .num 99])])
#guard obs case_spreadInSeq__pe_12 == "ok raw=S[S[], S[1, 2], 99] n=1"

-- spreadInSeq__ppe1_2: (spread((((), 1), 2)), 99)
def case_spreadInSeq__ppe1_2 : Expr :=
  .block (alg [] [] [] [.block (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.num 1)])), (.num 2)])), .num 99])])
#guard obs case_spreadInSeq__ppe1_2 == "ok raw=S[S[S[], 1], 2, 99] n=1"

-- spreadInSeq__p12_e: (spread(((1, 2), ())), 99)
def case_spreadInSeq__p12_e : Expr :=
  .block (alg [] [] [] [.block (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.emptySequence 0)])), .num 99])])
#guard obs case_spreadInSeq__p12_e == "ok raw=S[S[1, 2], S[], 99] n=1"

-- spreadInSeq__ppe: (spread((())), 99)
def case_spreadInSeq__ppe : Expr :=
  .block (alg [] [] [] [.block (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.emptySequence 0)])), .num 99])])
#guard obs case_spreadInSeq__ppe == "ok raw=99 n=1"

-- spreadInSeq__pp1: (spread(((1))), 99)
def case_spreadInSeq__pp1 : Expr :=
  .block (alg [] [] [] [.block (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1)]))])), .num 99])])
#guard obs case_spreadInSeq__pp1 == "ok raw=S[1, 99] n=1"

-- spreadInSeq__ppp12: (spread((((1, 2)))), 99)
def case_spreadInSeq__ppp12 : Expr :=
  .block (alg [] [] [] [.block (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)]))]))])), .num 99])])
#guard obs case_spreadInSeq__ppp12 == "ok raw=S[1, 2, 99] n=1"

-- spreadInSeq__le: (spread([]), 99)
def case_spreadInSeq__le : Expr :=
  .block (alg [] [] [] [.block (alg [] [] [] [.sequenceSpread (.listLiteral []), .num 99])])
#guard obs case_spreadInSeq__le == "ok raw=99 n=1"

-- spreadInSeq__l7: (spread([7]), 99)
def case_spreadInSeq__l7 : Expr :=
  .block (alg [] [] [] [.block (alg [] [] [] [.sequenceSpread (.listLiteral [(.num 7)]), .num 99])])
#guard obs case_spreadInSeq__l7 == "ok raw=S[7, 99] n=1"

-- spreadInSeq__l12: (spread([1, 2]), 99)
def case_spreadInSeq__l12 : Expr :=
  .block (alg [] [] [] [.block (alg [] [] [] [.sequenceSpread (.listLiteral [(.num 1), (.num 2)]), .num 99])])
#guard obs case_spreadInSeq__l12 == "ok raw=S[1, 2, 99] n=1"

-- spreadInSeq__l12_3: (spread([[1, 2], 3]), 99)
def case_spreadInSeq__l12_3 : Expr :=
  .block (alg [] [] [] [.block (alg [] [] [] [.sequenceSpread (.listLiteral [(.listLiteral [(.num 1), (.num 2)]), (.num 3)]), .num 99])])
#guard obs case_spreadInSeq__l12_3 == "ok raw=S[L[1, 2], 3, 99] n=1"

-- spreadInSeq__lle: (spread([[]]), 99)
def case_spreadInSeq__lle : Expr :=
  .block (alg [] [] [] [.block (alg [] [] [] [.sequenceSpread (.listLiteral [(.listLiteral [])]), .num 99])])
#guard obs case_spreadInSeq__lle == "ok raw=S[L[], 99] n=1"

-- spreadInSeq__l_e: (spread([()]), 99)
def case_spreadInSeq__l_e : Expr :=
  .block (alg [] [] [] [.block (alg [] [] [] [.sequenceSpread (.listLiteral [(.emptySequence 0)]), .num 99])])
#guard obs case_spreadInSeq__l_e == "ok raw=S[S[], 99] n=1"

-- spreadInSeq__l_p12: (spread([(1, 2)]), 99)
def case_spreadInSeq__l_p12 : Expr :=
  .block (alg [] [] [] [.block (alg [] [] [] [.sequenceSpread (.listLiteral [(.block (alg [] [] [] [(.num 1), (.num 2)]))]), .num 99])])
#guard obs case_spreadInSeq__l_p12 == "ok raw=S[S[1, 2], 99] n=1"

-- spreadInSeq__p_l12: (spread(([1, 2], 3)), 99)
def case_spreadInSeq__p_l12 : Expr :=
  .block (alg [] [] [] [.block (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.listLiteral [(.num 1), (.num 2)]), (.num 3)])), .num 99])])
#guard obs case_spreadInSeq__p_l12 == "ok raw=S[L[1, 2], 3, 99] n=1"

-- spreadInSeq__pl1: (spread(([1])), 99)
def case_spreadInSeq__pl1 : Expr :=
  .block (alg [] [] [] [.block (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.listLiteral [(.num 1)])])), .num 99])])
#guard obs case_spreadInSeq__pl1 == "ok raw=S[1, 99] n=1"

-- count__e: count(())
def case_count__e : Expr :=
  .block (alg [] [] [] [.call (.resolve "count") (alg [] [] [] [(.emptySequence 0)])])
#guard obs case_count__e == "ok raw=0 n=1"

-- count__n0: count(0)
def case_count__n0 : Expr :=
  .block (alg [] [] [] [.call (.resolve "count") (alg [] [] [] [(.num 0)])])
#guard obs case_count__n0 == "ok raw=1 n=1"

-- count__n1: count(1)
def case_count__n1 : Expr :=
  .block (alg [] [] [] [.call (.resolve "count") (alg [] [] [] [(.num 1)])])
#guard obs case_count__n1 == "ok raw=1 n=1"

-- count__p1: count((1))
def case_count__p1 : Expr :=
  .block (alg [] [] [] [.call (.resolve "count") (alg [] [] [] [(.block (alg [] [] [] [(.num 1)]))])])
#guard obs case_count__p1 == "ok raw=1 n=1"

-- count__p12: count((1, 2))
def case_count__p12 : Expr :=
  .block (alg [] [] [] [.call (.resolve "count") (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)]))])])
#guard obs case_count__p12 == "ok raw=2 n=1"

-- count__p123: count((1, 2, 3))
def case_count__p123 : Expr :=
  .block (alg [] [] [] [.call (.resolve "count") (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2), (.num 3)]))])])
#guard obs case_count__p123 == "ok raw=3 n=1"

-- count__pee: count(((), ()))
def case_count__pee : Expr :=
  .block (alg [] [] [] [.call (.resolve "count") (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.emptySequence 0)]))])])
#guard obs case_count__pee == "ok raw=2 n=1"

-- count__pe1: count(((), 1))
def case_count__pe1 : Expr :=
  .block (alg [] [] [] [.call (.resolve "count") (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.num 1)]))])])
#guard obs case_count__pe1 == "ok raw=2 n=1"

-- count__p1e: count((1, ()))
def case_count__p1e : Expr :=
  .block (alg [] [] [] [.call (.resolve "count") (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.emptySequence 0)]))])])
#guard obs case_count__p1e == "ok raw=2 n=1"

-- count__p12_3: count(((1, 2), 3))
def case_count__p12_3 : Expr :=
  .block (alg [] [] [] [.call (.resolve "count") (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.num 3)]))])])
#guard obs case_count__p12_3 == "ok raw=2 n=1"

-- count__p12_34: count(((1, 2), (3, 4)))
def case_count__p12_34 : Expr :=
  .block (alg [] [] [] [.call (.resolve "count") (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.block (alg [] [] [] [(.num 3), (.num 4)]))]))])])
#guard obs case_count__p12_34 == "ok raw=2 n=1"

-- count__pe_12: count(((), (1, 2)))
def case_count__pe_12 : Expr :=
  .block (alg [] [] [] [.call (.resolve "count") (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.block (alg [] [] [] [(.num 1), (.num 2)]))]))])])
#guard obs case_count__pe_12 == "ok raw=2 n=1"

-- count__ppe1_2: count((((), 1), 2))
def case_count__ppe1_2 : Expr :=
  .block (alg [] [] [] [.call (.resolve "count") (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.num 1)])), (.num 2)]))])])
#guard obs case_count__ppe1_2 == "ok raw=2 n=1"

-- count__p12_e: count(((1, 2), ()))
def case_count__p12_e : Expr :=
  .block (alg [] [] [] [.call (.resolve "count") (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.emptySequence 0)]))])])
#guard obs case_count__p12_e == "ok raw=2 n=1"

-- count__ppe: count((()))
def case_count__ppe : Expr :=
  .block (alg [] [] [] [.call (.resolve "count") (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0)]))])])
#guard obs case_count__ppe == "ok raw=0 n=1"

-- count__pp1: count(((1)))
def case_count__pp1 : Expr :=
  .block (alg [] [] [] [.call (.resolve "count") (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1)]))]))])])
#guard obs case_count__pp1 == "ok raw=1 n=1"

-- count__ppp12: count((((1, 2))))
def case_count__ppp12 : Expr :=
  .block (alg [] [] [] [.call (.resolve "count") (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)]))]))]))])])
#guard obs case_count__ppp12 == "ok raw=2 n=1"

-- count__le: count([])
def case_count__le : Expr :=
  .block (alg [] [] [] [.call (.resolve "count") (alg [] [] [] [(.listLiteral [])])])
#guard obs case_count__le == "ok raw=0 n=1"

-- count__l7: count([7])
def case_count__l7 : Expr :=
  .block (alg [] [] [] [.call (.resolve "count") (alg [] [] [] [(.listLiteral [(.num 7)])])])
#guard obs case_count__l7 == "ok raw=1 n=1"

-- count__l12: count([1, 2])
def case_count__l12 : Expr :=
  .block (alg [] [] [] [.call (.resolve "count") (alg [] [] [] [(.listLiteral [(.num 1), (.num 2)])])])
#guard obs case_count__l12 == "ok raw=2 n=1"

-- count__l12_3: count([[1, 2], 3])
def case_count__l12_3 : Expr :=
  .block (alg [] [] [] [.call (.resolve "count") (alg [] [] [] [(.listLiteral [(.listLiteral [(.num 1), (.num 2)]), (.num 3)])])])
#guard obs case_count__l12_3 == "ok raw=2 n=1"

-- count__lle: count([[]])
def case_count__lle : Expr :=
  .block (alg [] [] [] [.call (.resolve "count") (alg [] [] [] [(.listLiteral [(.listLiteral [])])])])
#guard obs case_count__lle == "ok raw=1 n=1"

-- count__l_e: count([()])
def case_count__l_e : Expr :=
  .block (alg [] [] [] [.call (.resolve "count") (alg [] [] [] [(.listLiteral [(.emptySequence 0)])])])
#guard obs case_count__l_e == "ok raw=1 n=1"

-- count__l_p12: count([(1, 2)])
def case_count__l_p12 : Expr :=
  .block (alg [] [] [] [.call (.resolve "count") (alg [] [] [] [(.listLiteral [(.block (alg [] [] [] [(.num 1), (.num 2)]))])])])
#guard obs case_count__l_p12 == "ok raw=1 n=1"

-- count__p_l12: count(([1, 2], 3))
def case_count__p_l12 : Expr :=
  .block (alg [] [] [] [.call (.resolve "count") (alg [] [] [] [(.block (alg [] [] [] [(.listLiteral [(.num 1), (.num 2)]), (.num 3)]))])])
#guard obs case_count__p_l12 == "ok raw=2 n=1"

-- count__pl1: count(([1]))
def case_count__pl1 : Expr :=
  .block (alg [] [] [] [.call (.resolve "count") (alg [] [] [] [(.block (alg [] [] [] [(.listLiteral [(.num 1)])]))])])
#guard obs case_count__pl1 == "ok raw=1 n=1"

-- countSpread__e: count(spread(()))
def case_countSpread__e : Expr :=
  .block (alg [] [] [] [.call (.resolve "count") (alg [] [] [] [.sequenceSpread (.emptySequence 0)])])
#guard obs case_countSpread__e == "err arity"

-- countSpread__n0: count(spread(0))
def case_countSpread__n0 : Expr :=
  .block (alg [] [] [] [.call (.resolve "count") (alg [] [] [] [.sequenceSpread (.num 0)])])
#guard obs case_countSpread__n0 == "ok raw=1 n=1"

-- countSpread__n1: count(spread(1))
def case_countSpread__n1 : Expr :=
  .block (alg [] [] [] [.call (.resolve "count") (alg [] [] [] [.sequenceSpread (.num 1)])])
#guard obs case_countSpread__n1 == "ok raw=1 n=1"

-- countSpread__p1: count(spread((1)))
def case_countSpread__p1 : Expr :=
  .block (alg [] [] [] [.call (.resolve "count") (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.num 1)]))])])
#guard obs case_countSpread__p1 == "ok raw=1 n=1"

-- countSpread__p12: count(spread((1, 2)))
def case_countSpread__p12 : Expr :=
  .block (alg [] [] [] [.call (.resolve "count") (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.num 1), (.num 2)]))])])
#guard obs case_countSpread__p12 == "err arity"

-- countSpread__p123: count(spread((1, 2, 3)))
def case_countSpread__p123 : Expr :=
  .block (alg [] [] [] [.call (.resolve "count") (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.num 1), (.num 2), (.num 3)]))])])
#guard obs case_countSpread__p123 == "err arity"

-- countSpread__pee: count(spread(((), ())))
def case_countSpread__pee : Expr :=
  .block (alg [] [] [] [.call (.resolve "count") (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.emptySequence 0), (.emptySequence 0)]))])])
#guard obs case_countSpread__pee == "err arity"

-- countSpread__pe1: count(spread(((), 1)))
def case_countSpread__pe1 : Expr :=
  .block (alg [] [] [] [.call (.resolve "count") (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.emptySequence 0), (.num 1)]))])])
#guard obs case_countSpread__pe1 == "err arity"

-- countSpread__p1e: count(spread((1, ())))
def case_countSpread__p1e : Expr :=
  .block (alg [] [] [] [.call (.resolve "count") (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.num 1), (.emptySequence 0)]))])])
#guard obs case_countSpread__p1e == "err arity"

-- countSpread__p12_3: count(spread(((1, 2), 3)))
def case_countSpread__p12_3 : Expr :=
  .block (alg [] [] [] [.call (.resolve "count") (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.num 3)]))])])
#guard obs case_countSpread__p12_3 == "err arity"

-- countSpread__p12_34: count(spread(((1, 2), (3, 4))))
def case_countSpread__p12_34 : Expr :=
  .block (alg [] [] [] [.call (.resolve "count") (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.block (alg [] [] [] [(.num 3), (.num 4)]))]))])])
#guard obs case_countSpread__p12_34 == "err arity"

-- countSpread__pe_12: count(spread(((), (1, 2))))
def case_countSpread__pe_12 : Expr :=
  .block (alg [] [] [] [.call (.resolve "count") (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.emptySequence 0), (.block (alg [] [] [] [(.num 1), (.num 2)]))]))])])
#guard obs case_countSpread__pe_12 == "err arity"

-- countSpread__ppe1_2: count(spread((((), 1), 2)))
def case_countSpread__ppe1_2 : Expr :=
  .block (alg [] [] [] [.call (.resolve "count") (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.num 1)])), (.num 2)]))])])
#guard obs case_countSpread__ppe1_2 == "err arity"

-- countSpread__p12_e: count(spread(((1, 2), ())))
def case_countSpread__p12_e : Expr :=
  .block (alg [] [] [] [.call (.resolve "count") (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.emptySequence 0)]))])])
#guard obs case_countSpread__p12_e == "err arity"

-- countSpread__ppe: count(spread((())))
def case_countSpread__ppe : Expr :=
  .block (alg [] [] [] [.call (.resolve "count") (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.emptySequence 0)]))])])
#guard obs case_countSpread__ppe == "err arity"

-- countSpread__pp1: count(spread(((1))))
def case_countSpread__pp1 : Expr :=
  .block (alg [] [] [] [.call (.resolve "count") (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1)]))]))])])
#guard obs case_countSpread__pp1 == "ok raw=1 n=1"

-- countSpread__ppp12: count(spread((((1, 2)))))
def case_countSpread__ppp12 : Expr :=
  .block (alg [] [] [] [.call (.resolve "count") (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)]))]))]))])])
#guard obs case_countSpread__ppp12 == "err arity"

-- countSpread__le: count(spread([]))
def case_countSpread__le : Expr :=
  .block (alg [] [] [] [.call (.resolve "count") (alg [] [] [] [.sequenceSpread (.listLiteral [])])])
#guard obs case_countSpread__le == "err arity"

-- countSpread__l7: count(spread([7]))
def case_countSpread__l7 : Expr :=
  .block (alg [] [] [] [.call (.resolve "count") (alg [] [] [] [.sequenceSpread (.listLiteral [(.num 7)])])])
#guard obs case_countSpread__l7 == "ok raw=1 n=1"

-- countSpread__l12: count(spread([1, 2]))
def case_countSpread__l12 : Expr :=
  .block (alg [] [] [] [.call (.resolve "count") (alg [] [] [] [.sequenceSpread (.listLiteral [(.num 1), (.num 2)])])])
#guard obs case_countSpread__l12 == "err arity"

-- countSpread__l12_3: count(spread([[1, 2], 3]))
def case_countSpread__l12_3 : Expr :=
  .block (alg [] [] [] [.call (.resolve "count") (alg [] [] [] [.sequenceSpread (.listLiteral [(.listLiteral [(.num 1), (.num 2)]), (.num 3)])])])
#guard obs case_countSpread__l12_3 == "err arity"

-- countSpread__lle: count(spread([[]]))
def case_countSpread__lle : Expr :=
  .block (alg [] [] [] [.call (.resolve "count") (alg [] [] [] [.sequenceSpread (.listLiteral [(.listLiteral [])])])])
#guard obs case_countSpread__lle == "ok raw=0 n=1"

-- countSpread__l_e: count(spread([()]))
def case_countSpread__l_e : Expr :=
  .block (alg [] [] [] [.call (.resolve "count") (alg [] [] [] [.sequenceSpread (.listLiteral [(.emptySequence 0)])])])
#guard obs case_countSpread__l_e == "ok raw=0 n=1"

-- countSpread__l_p12: count(spread([(1, 2)]))
def case_countSpread__l_p12 : Expr :=
  .block (alg [] [] [] [.call (.resolve "count") (alg [] [] [] [.sequenceSpread (.listLiteral [(.block (alg [] [] [] [(.num 1), (.num 2)]))])])])
#guard obs case_countSpread__l_p12 == "ok raw=2 n=1"

-- countSpread__p_l12: count(spread(([1, 2], 3)))
def case_countSpread__p_l12 : Expr :=
  .block (alg [] [] [] [.call (.resolve "count") (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.listLiteral [(.num 1), (.num 2)]), (.num 3)]))])])
#guard obs case_countSpread__p_l12 == "err arity"

-- countSpread__pl1: count(spread(([1])))
def case_countSpread__pl1 : Expr :=
  .block (alg [] [] [] [.call (.resolve "count") (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [(.listLiteral [(.num 1)])]))])])
#guard obs case_countSpread__pl1 == "ok raw=1 n=1"

-- dotCount__e: x = () \n x.count
def case_dotCount__e : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.emptySequence 0)])] [.dotCall (.resolve "x") "count" none])
#guard obs case_dotCount__e == "ok raw=0 n=1"

-- dotCount__n0: x = 0 \n x.count
def case_dotCount__n0 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.num 0)])] [.dotCall (.resolve "x") "count" none])
#guard obs case_dotCount__n0 == "ok raw=1 n=1"

-- dotCount__n1: x = 1 \n x.count
def case_dotCount__n1 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.num 1)])] [.dotCall (.resolve "x") "count" none])
#guard obs case_dotCount__n1 == "ok raw=1 n=1"

-- dotCount__p1: x = (1) \n x.count
def case_dotCount__p1 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.num 1)]))])] [.dotCall (.resolve "x") "count" none])
#guard obs case_dotCount__p1 == "ok raw=1 n=1"

-- dotCount__p12: x = (1, 2) \n x.count
def case_dotCount__p12 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)]))])] [.dotCall (.resolve "x") "count" none])
#guard obs case_dotCount__p12 == "ok raw=2 n=1"

-- dotCount__p123: x = (1, 2, 3) \n x.count
def case_dotCount__p123 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2), (.num 3)]))])] [.dotCall (.resolve "x") "count" none])
#guard obs case_dotCount__p123 == "ok raw=3 n=1"

-- dotCount__pee: x = ((), ()) \n x.count
def case_dotCount__pee : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.emptySequence 0)]))])] [.dotCall (.resolve "x") "count" none])
#guard obs case_dotCount__pee == "ok raw=2 n=1"

-- dotCount__pe1: x = ((), 1) \n x.count
def case_dotCount__pe1 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.num 1)]))])] [.dotCall (.resolve "x") "count" none])
#guard obs case_dotCount__pe1 == "ok raw=2 n=1"

-- dotCount__p1e: x = (1, ()) \n x.count
def case_dotCount__p1e : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.emptySequence 0)]))])] [.dotCall (.resolve "x") "count" none])
#guard obs case_dotCount__p1e == "ok raw=2 n=1"

-- dotCount__p12_3: x = ((1, 2), 3) \n x.count
def case_dotCount__p12_3 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.num 3)]))])] [.dotCall (.resolve "x") "count" none])
#guard obs case_dotCount__p12_3 == "ok raw=2 n=1"

-- dotCount__p12_34: x = ((1, 2), (3, 4)) \n x.count
def case_dotCount__p12_34 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.block (alg [] [] [] [(.num 3), (.num 4)]))]))])] [.dotCall (.resolve "x") "count" none])
#guard obs case_dotCount__p12_34 == "ok raw=2 n=1"

-- dotCount__pe_12: x = ((), (1, 2)) \n x.count
def case_dotCount__pe_12 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.block (alg [] [] [] [(.num 1), (.num 2)]))]))])] [.dotCall (.resolve "x") "count" none])
#guard obs case_dotCount__pe_12 == "ok raw=2 n=1"

-- dotCount__ppe1_2: x = (((), 1), 2) \n x.count
def case_dotCount__ppe1_2 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.num 1)])), (.num 2)]))])] [.dotCall (.resolve "x") "count" none])
#guard obs case_dotCount__ppe1_2 == "ok raw=2 n=1"

-- dotCount__p12_e: x = ((1, 2), ()) \n x.count
def case_dotCount__p12_e : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.emptySequence 0)]))])] [.dotCall (.resolve "x") "count" none])
#guard obs case_dotCount__p12_e == "ok raw=2 n=1"

-- dotCount__ppe: x = (()) \n x.count
def case_dotCount__ppe : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0)]))])] [.dotCall (.resolve "x") "count" none])
#guard obs case_dotCount__ppe == "ok raw=0 n=1"

-- dotCount__pp1: x = ((1)) \n x.count
def case_dotCount__pp1 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1)]))]))])] [.dotCall (.resolve "x") "count" none])
#guard obs case_dotCount__pp1 == "ok raw=1 n=1"

-- dotCount__ppp12: x = (((1, 2))) \n x.count
def case_dotCount__ppp12 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)]))]))]))])] [.dotCall (.resolve "x") "count" none])
#guard obs case_dotCount__ppp12 == "ok raw=2 n=1"

-- dotCount__le: x = [] \n x.count
def case_dotCount__le : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [])])] [.dotCall (.resolve "x") "count" none])
#guard obs case_dotCount__le == "ok raw=0 n=1"

-- dotCount__l7: x = [7] \n x.count
def case_dotCount__l7 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [(.num 7)])])] [.dotCall (.resolve "x") "count" none])
#guard obs case_dotCount__l7 == "ok raw=1 n=1"

-- dotCount__l12: x = [1, 2] \n x.count
def case_dotCount__l12 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [(.num 1), (.num 2)])])] [.dotCall (.resolve "x") "count" none])
#guard obs case_dotCount__l12 == "ok raw=2 n=1"

-- dotCount__l12_3: x = [[1, 2], 3] \n x.count
def case_dotCount__l12_3 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [(.listLiteral [(.num 1), (.num 2)]), (.num 3)])])] [.dotCall (.resolve "x") "count" none])
#guard obs case_dotCount__l12_3 == "ok raw=2 n=1"

-- dotCount__lle: x = [[]] \n x.count
def case_dotCount__lle : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [(.listLiteral [])])])] [.dotCall (.resolve "x") "count" none])
#guard obs case_dotCount__lle == "ok raw=1 n=1"

-- dotCount__l_e: x = [()] \n x.count
def case_dotCount__l_e : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [(.emptySequence 0)])])] [.dotCall (.resolve "x") "count" none])
#guard obs case_dotCount__l_e == "ok raw=1 n=1"

-- dotCount__l_p12: x = [(1, 2)] \n x.count
def case_dotCount__l_p12 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [(.block (alg [] [] [] [(.num 1), (.num 2)]))])])] [.dotCall (.resolve "x") "count" none])
#guard obs case_dotCount__l_p12 == "ok raw=1 n=1"

-- dotCount__p_l12: x = ([1, 2], 3) \n x.count
def case_dotCount__p_l12 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.listLiteral [(.num 1), (.num 2)]), (.num 3)]))])] [.dotCall (.resolve "x") "count" none])
#guard obs case_dotCount__p_l12 == "ok raw=2 n=1"

-- dotCount__pl1: x = ([1]) \n x.count
def case_dotCount__pl1 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.listLiteral [(.num 1)])]))])] [.dotCall (.resolve "x") "count" none])
#guard obs case_dotCount__pl1 == "ok raw=1 n=1"

-- literalDotCount__e: (()).count
def case_literalDotCount__e : Expr :=
  .block (alg [] [] [] [.dotCall (.block (alg [] [] [] [(.emptySequence 0)])) "count" none])
#guard obs case_literalDotCount__e == "ok raw=0 n=1"

-- literalDotCount__n0: (0).count
def case_literalDotCount__n0 : Expr :=
  .block (alg [] [] [] [.dotCall (.block (alg [] [] [] [(.num 0)])) "count" none])
#guard obs case_literalDotCount__n0 == "ok raw=1 n=1"

-- literalDotCount__n1: (1).count
def case_literalDotCount__n1 : Expr :=
  .block (alg [] [] [] [.dotCall (.block (alg [] [] [] [(.num 1)])) "count" none])
#guard obs case_literalDotCount__n1 == "ok raw=1 n=1"

-- literalDotCount__p1: ((1)).count
def case_literalDotCount__p1 : Expr :=
  .block (alg [] [] [] [.dotCall (.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1)]))])) "count" none])
#guard obs case_literalDotCount__p1 == "ok raw=1 n=1"

-- literalDotCount__p12: ((1, 2)).count
def case_literalDotCount__p12 : Expr :=
  .block (alg [] [] [] [.dotCall (.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)]))])) "count" none])
#guard obs case_literalDotCount__p12 == "ok raw=2 n=1"

-- literalDotCount__p123: ((1, 2, 3)).count
def case_literalDotCount__p123 : Expr :=
  .block (alg [] [] [] [.dotCall (.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2), (.num 3)]))])) "count" none])
#guard obs case_literalDotCount__p123 == "ok raw=3 n=1"

-- literalDotCount__pee: (((), ())).count
def case_literalDotCount__pee : Expr :=
  .block (alg [] [] [] [.dotCall (.block (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.emptySequence 0)]))])) "count" none])
#guard obs case_literalDotCount__pee == "ok raw=2 n=1"

-- literalDotCount__pe1: (((), 1)).count
def case_literalDotCount__pe1 : Expr :=
  .block (alg [] [] [] [.dotCall (.block (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.num 1)]))])) "count" none])
#guard obs case_literalDotCount__pe1 == "ok raw=2 n=1"

-- literalDotCount__p1e: ((1, ())).count
def case_literalDotCount__p1e : Expr :=
  .block (alg [] [] [] [.dotCall (.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.emptySequence 0)]))])) "count" none])
#guard obs case_literalDotCount__p1e == "ok raw=2 n=1"

-- literalDotCount__p12_3: (((1, 2), 3)).count
def case_literalDotCount__p12_3 : Expr :=
  .block (alg [] [] [] [.dotCall (.block (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.num 3)]))])) "count" none])
#guard obs case_literalDotCount__p12_3 == "ok raw=2 n=1"

-- literalDotCount__p12_34: (((1, 2), (3, 4))).count
def case_literalDotCount__p12_34 : Expr :=
  .block (alg [] [] [] [.dotCall (.block (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.block (alg [] [] [] [(.num 3), (.num 4)]))]))])) "count" none])
#guard obs case_literalDotCount__p12_34 == "ok raw=2 n=1"

-- literalDotCount__pe_12: (((), (1, 2))).count
def case_literalDotCount__pe_12 : Expr :=
  .block (alg [] [] [] [.dotCall (.block (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.block (alg [] [] [] [(.num 1), (.num 2)]))]))])) "count" none])
#guard obs case_literalDotCount__pe_12 == "ok raw=2 n=1"

-- literalDotCount__ppe1_2: ((((), 1), 2)).count
def case_literalDotCount__ppe1_2 : Expr :=
  .block (alg [] [] [] [.dotCall (.block (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.num 1)])), (.num 2)]))])) "count" none])
#guard obs case_literalDotCount__ppe1_2 == "ok raw=2 n=1"

-- literalDotCount__p12_e: (((1, 2), ())).count
def case_literalDotCount__p12_e : Expr :=
  .block (alg [] [] [] [.dotCall (.block (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.emptySequence 0)]))])) "count" none])
#guard obs case_literalDotCount__p12_e == "ok raw=2 n=1"

-- literalDotCount__ppe: ((())).count
def case_literalDotCount__ppe : Expr :=
  .block (alg [] [] [] [.dotCall (.block (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0)]))])) "count" none])
#guard obs case_literalDotCount__ppe == "ok raw=0 n=1"

-- literalDotCount__pp1: (((1))).count
def case_literalDotCount__pp1 : Expr :=
  .block (alg [] [] [] [.dotCall (.block (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1)]))]))])) "count" none])
#guard obs case_literalDotCount__pp1 == "ok raw=1 n=1"

-- literalDotCount__ppp12: ((((1, 2)))).count
def case_literalDotCount__ppp12 : Expr :=
  .block (alg [] [] [] [.dotCall (.block (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)]))]))]))])) "count" none])
#guard obs case_literalDotCount__ppp12 == "ok raw=2 n=1"

-- literalDotCount__le: ([]).count
def case_literalDotCount__le : Expr :=
  .block (alg [] [] [] [.dotCall (.block (alg [] [] [] [(.listLiteral [])])) "count" none])
#guard obs case_literalDotCount__le == "ok raw=0 n=1"

-- literalDotCount__l7: ([7]).count
def case_literalDotCount__l7 : Expr :=
  .block (alg [] [] [] [.dotCall (.block (alg [] [] [] [(.listLiteral [(.num 7)])])) "count" none])
#guard obs case_literalDotCount__l7 == "ok raw=1 n=1"

-- literalDotCount__l12: ([1, 2]).count
def case_literalDotCount__l12 : Expr :=
  .block (alg [] [] [] [.dotCall (.block (alg [] [] [] [(.listLiteral [(.num 1), (.num 2)])])) "count" none])
#guard obs case_literalDotCount__l12 == "ok raw=2 n=1"

-- literalDotCount__l12_3: ([[1, 2], 3]).count
def case_literalDotCount__l12_3 : Expr :=
  .block (alg [] [] [] [.dotCall (.block (alg [] [] [] [(.listLiteral [(.listLiteral [(.num 1), (.num 2)]), (.num 3)])])) "count" none])
#guard obs case_literalDotCount__l12_3 == "ok raw=2 n=1"

-- literalDotCount__lle: ([[]]).count
def case_literalDotCount__lle : Expr :=
  .block (alg [] [] [] [.dotCall (.block (alg [] [] [] [(.listLiteral [(.listLiteral [])])])) "count" none])
#guard obs case_literalDotCount__lle == "ok raw=1 n=1"

-- literalDotCount__l_e: ([()]).count
def case_literalDotCount__l_e : Expr :=
  .block (alg [] [] [] [.dotCall (.block (alg [] [] [] [(.listLiteral [(.emptySequence 0)])])) "count" none])
#guard obs case_literalDotCount__l_e == "ok raw=1 n=1"

-- literalDotCount__l_p12: ([(1, 2)]).count
def case_literalDotCount__l_p12 : Expr :=
  .block (alg [] [] [] [.dotCall (.block (alg [] [] [] [(.listLiteral [(.block (alg [] [] [] [(.num 1), (.num 2)]))])])) "count" none])
#guard obs case_literalDotCount__l_p12 == "ok raw=1 n=1"

-- literalDotCount__p_l12: (([1, 2], 3)).count
def case_literalDotCount__p_l12 : Expr :=
  .block (alg [] [] [] [.dotCall (.block (alg [] [] [] [(.block (alg [] [] [] [(.listLiteral [(.num 1), (.num 2)]), (.num 3)]))])) "count" none])
#guard obs case_literalDotCount__p_l12 == "ok raw=2 n=1"

-- literalDotCount__pl1: (([1])).count
def case_literalDotCount__pl1 : Expr :=
  .block (alg [] [] [] [.dotCall (.block (alg [] [] [] [(.block (alg [] [] [] [(.listLiteral [(.num 1)])]))])) "count" none])
#guard obs case_literalDotCount__pl1 == "ok raw=1 n=1"

-- index0__e: x = () \n x:0
def case_index0__e : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.emptySequence 0)])] [.index (.resolve "x") (.num 0)])
#guard obs case_index0__e == "err index"

-- index0__n0: x = 0 \n x:0
def case_index0__n0 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.num 0)])] [.index (.resolve "x") (.num 0)])
#guard obs case_index0__n0 == "ok raw=0 n=1"

-- index0__n1: x = 1 \n x:0
def case_index0__n1 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.num 1)])] [.index (.resolve "x") (.num 0)])
#guard obs case_index0__n1 == "ok raw=1 n=1"

-- index0__p1: x = (1) \n x:0
def case_index0__p1 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.num 1)]))])] [.index (.resolve "x") (.num 0)])
#guard obs case_index0__p1 == "ok raw=1 n=1"

-- index0__p12: x = (1, 2) \n x:0
def case_index0__p12 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)]))])] [.index (.resolve "x") (.num 0)])
#guard obs case_index0__p12 == "ok raw=1 n=1"

-- index0__p123: x = (1, 2, 3) \n x:0
def case_index0__p123 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2), (.num 3)]))])] [.index (.resolve "x") (.num 0)])
#guard obs case_index0__p123 == "ok raw=1 n=1"

-- index0__pee: x = ((), ()) \n x:0
def case_index0__pee : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.emptySequence 0)]))])] [.index (.resolve "x") (.num 0)])
#guard obs case_index0__pee == "ok raw=S[] n=1"

-- index0__pe1: x = ((), 1) \n x:0
def case_index0__pe1 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.num 1)]))])] [.index (.resolve "x") (.num 0)])
#guard obs case_index0__pe1 == "ok raw=S[] n=1"

-- index0__p1e: x = (1, ()) \n x:0
def case_index0__p1e : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.emptySequence 0)]))])] [.index (.resolve "x") (.num 0)])
#guard obs case_index0__p1e == "ok raw=1 n=1"

-- index0__p12_3: x = ((1, 2), 3) \n x:0
def case_index0__p12_3 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.num 3)]))])] [.index (.resolve "x") (.num 0)])
#guard obs case_index0__p12_3 == "ok raw=S[1, 2] n=2"

-- index0__p12_34: x = ((1, 2), (3, 4)) \n x:0
def case_index0__p12_34 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.block (alg [] [] [] [(.num 3), (.num 4)]))]))])] [.index (.resolve "x") (.num 0)])
#guard obs case_index0__p12_34 == "ok raw=S[1, 2] n=2"

-- index0__pe_12: x = ((), (1, 2)) \n x:0
def case_index0__pe_12 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.block (alg [] [] [] [(.num 1), (.num 2)]))]))])] [.index (.resolve "x") (.num 0)])
#guard obs case_index0__pe_12 == "ok raw=S[] n=1"

-- index0__ppe1_2: x = (((), 1), 2) \n x:0
def case_index0__ppe1_2 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.num 1)])), (.num 2)]))])] [.index (.resolve "x") (.num 0)])
#guard obs case_index0__ppe1_2 == "ok raw=S[S[], 1] n=2"

-- index0__p12_e: x = ((1, 2), ()) \n x:0
def case_index0__p12_e : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.emptySequence 0)]))])] [.index (.resolve "x") (.num 0)])
#guard obs case_index0__p12_e == "ok raw=S[1, 2] n=2"

-- index0__ppe: x = (()) \n x:0
def case_index0__ppe : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0)]))])] [.index (.resolve "x") (.num 0)])
#guard obs case_index0__ppe == "err index"

-- index0__pp1: x = ((1)) \n x:0
def case_index0__pp1 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1)]))]))])] [.index (.resolve "x") (.num 0)])
#guard obs case_index0__pp1 == "ok raw=1 n=1"

-- index0__ppp12: x = (((1, 2))) \n x:0
def case_index0__ppp12 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)]))]))]))])] [.index (.resolve "x") (.num 0)])
#guard obs case_index0__ppp12 == "ok raw=1 n=1"

-- index0__le: x = [] \n x:0
def case_index0__le : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [])])] [.index (.resolve "x") (.num 0)])
#guard obs case_index0__le == "err index"

-- index0__l7: x = [7] \n x:0
def case_index0__l7 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [(.num 7)])])] [.index (.resolve "x") (.num 0)])
#guard obs case_index0__l7 == "ok raw=7 n=1"

-- index0__l12: x = [1, 2] \n x:0
def case_index0__l12 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [(.num 1), (.num 2)])])] [.index (.resolve "x") (.num 0)])
#guard obs case_index0__l12 == "ok raw=1 n=1"

-- index0__l12_3: x = [[1, 2], 3] \n x:0
def case_index0__l12_3 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [(.listLiteral [(.num 1), (.num 2)]), (.num 3)])])] [.index (.resolve "x") (.num 0)])
#guard obs case_index0__l12_3 == "ok raw=L[1, 2] n=1"

-- index0__lle: x = [[]] \n x:0
def case_index0__lle : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [(.listLiteral [])])])] [.index (.resolve "x") (.num 0)])
#guard obs case_index0__lle == "ok raw=L[] n=1"

-- index0__l_e: x = [()] \n x:0
def case_index0__l_e : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [(.emptySequence 0)])])] [.index (.resolve "x") (.num 0)])
#guard obs case_index0__l_e == "ok raw=S[] n=1"

-- index0__l_p12: x = [(1, 2)] \n x:0
def case_index0__l_p12 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [(.block (alg [] [] [] [(.num 1), (.num 2)]))])])] [.index (.resolve "x") (.num 0)])
#guard obs case_index0__l_p12 == "ok raw=S[1, 2] n=2"

-- index0__p_l12: x = ([1, 2], 3) \n x:0
def case_index0__p_l12 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.listLiteral [(.num 1), (.num 2)]), (.num 3)]))])] [.index (.resolve "x") (.num 0)])
#guard obs case_index0__p_l12 == "ok raw=L[1, 2] n=1"

-- index0__pl1: x = ([1]) \n x:0
def case_index0__pl1 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.listLiteral [(.num 1)])]))])] [.index (.resolve "x") (.num 0)])
#guard obs case_index0__pl1 == "ok raw=1 n=1"

-- index1__e: x = () \n x:1
def case_index1__e : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.emptySequence 0)])] [.index (.resolve "x") (.num 1)])
#guard obs case_index1__e == "err index"

-- index1__n0: x = 0 \n x:1
def case_index1__n0 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.num 0)])] [.index (.resolve "x") (.num 1)])
#guard obs case_index1__n0 == "err index"

-- index1__n1: x = 1 \n x:1
def case_index1__n1 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.num 1)])] [.index (.resolve "x") (.num 1)])
#guard obs case_index1__n1 == "err index"

-- index1__p1: x = (1) \n x:1
def case_index1__p1 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.num 1)]))])] [.index (.resolve "x") (.num 1)])
#guard obs case_index1__p1 == "err index"

-- index1__p12: x = (1, 2) \n x:1
def case_index1__p12 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)]))])] [.index (.resolve "x") (.num 1)])
#guard obs case_index1__p12 == "ok raw=2 n=1"

-- index1__p123: x = (1, 2, 3) \n x:1
def case_index1__p123 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2), (.num 3)]))])] [.index (.resolve "x") (.num 1)])
#guard obs case_index1__p123 == "ok raw=2 n=1"

-- index1__pee: x = ((), ()) \n x:1
def case_index1__pee : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.emptySequence 0)]))])] [.index (.resolve "x") (.num 1)])
#guard obs case_index1__pee == "ok raw=S[] n=1"

-- index1__pe1: x = ((), 1) \n x:1
def case_index1__pe1 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.num 1)]))])] [.index (.resolve "x") (.num 1)])
#guard obs case_index1__pe1 == "ok raw=1 n=1"

-- index1__p1e: x = (1, ()) \n x:1
def case_index1__p1e : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.emptySequence 0)]))])] [.index (.resolve "x") (.num 1)])
#guard obs case_index1__p1e == "ok raw=S[] n=1"

-- index1__p12_3: x = ((1, 2), 3) \n x:1
def case_index1__p12_3 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.num 3)]))])] [.index (.resolve "x") (.num 1)])
#guard obs case_index1__p12_3 == "ok raw=3 n=1"

-- index1__p12_34: x = ((1, 2), (3, 4)) \n x:1
def case_index1__p12_34 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.block (alg [] [] [] [(.num 3), (.num 4)]))]))])] [.index (.resolve "x") (.num 1)])
#guard obs case_index1__p12_34 == "ok raw=S[3, 4] n=2"

-- index1__pe_12: x = ((), (1, 2)) \n x:1
def case_index1__pe_12 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.block (alg [] [] [] [(.num 1), (.num 2)]))]))])] [.index (.resolve "x") (.num 1)])
#guard obs case_index1__pe_12 == "ok raw=S[1, 2] n=2"

-- index1__ppe1_2: x = (((), 1), 2) \n x:1
def case_index1__ppe1_2 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.num 1)])), (.num 2)]))])] [.index (.resolve "x") (.num 1)])
#guard obs case_index1__ppe1_2 == "ok raw=2 n=1"

-- index1__p12_e: x = ((1, 2), ()) \n x:1
def case_index1__p12_e : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.emptySequence 0)]))])] [.index (.resolve "x") (.num 1)])
#guard obs case_index1__p12_e == "ok raw=S[] n=1"

-- index1__ppe: x = (()) \n x:1
def case_index1__ppe : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0)]))])] [.index (.resolve "x") (.num 1)])
#guard obs case_index1__ppe == "err index"

-- index1__pp1: x = ((1)) \n x:1
def case_index1__pp1 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1)]))]))])] [.index (.resolve "x") (.num 1)])
#guard obs case_index1__pp1 == "err index"

-- index1__ppp12: x = (((1, 2))) \n x:1
def case_index1__ppp12 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)]))]))]))])] [.index (.resolve "x") (.num 1)])
#guard obs case_index1__ppp12 == "ok raw=2 n=1"

-- index1__le: x = [] \n x:1
def case_index1__le : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [])])] [.index (.resolve "x") (.num 1)])
#guard obs case_index1__le == "err index"

-- index1__l7: x = [7] \n x:1
def case_index1__l7 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [(.num 7)])])] [.index (.resolve "x") (.num 1)])
#guard obs case_index1__l7 == "err index"

-- index1__l12: x = [1, 2] \n x:1
def case_index1__l12 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [(.num 1), (.num 2)])])] [.index (.resolve "x") (.num 1)])
#guard obs case_index1__l12 == "ok raw=2 n=1"

-- index1__l12_3: x = [[1, 2], 3] \n x:1
def case_index1__l12_3 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [(.listLiteral [(.num 1), (.num 2)]), (.num 3)])])] [.index (.resolve "x") (.num 1)])
#guard obs case_index1__l12_3 == "ok raw=3 n=1"

-- index1__lle: x = [[]] \n x:1
def case_index1__lle : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [(.listLiteral [])])])] [.index (.resolve "x") (.num 1)])
#guard obs case_index1__lle == "err index"

-- index1__l_e: x = [()] \n x:1
def case_index1__l_e : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [(.emptySequence 0)])])] [.index (.resolve "x") (.num 1)])
#guard obs case_index1__l_e == "err index"

-- index1__l_p12: x = [(1, 2)] \n x:1
def case_index1__l_p12 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [(.block (alg [] [] [] [(.num 1), (.num 2)]))])])] [.index (.resolve "x") (.num 1)])
#guard obs case_index1__l_p12 == "err index"

-- index1__p_l12: x = ([1, 2], 3) \n x:1
def case_index1__p_l12 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.listLiteral [(.num 1), (.num 2)]), (.num 3)]))])] [.index (.resolve "x") (.num 1)])
#guard obs case_index1__p_l12 == "ok raw=3 n=1"

-- index1__pl1: x = ([1]) \n x:1
def case_index1__pl1 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.listLiteral [(.num 1)])]))])] [.index (.resolve "x") (.num 1)])
#guard obs case_index1__pl1 == "err index"

-- indexBig__e: x = () \n x:9
def case_indexBig__e : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.emptySequence 0)])] [.index (.resolve "x") (.num 9)])
#guard obs case_indexBig__e == "err index"

-- indexBig__n0: x = 0 \n x:9
def case_indexBig__n0 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.num 0)])] [.index (.resolve "x") (.num 9)])
#guard obs case_indexBig__n0 == "err index"

-- indexBig__n1: x = 1 \n x:9
def case_indexBig__n1 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.num 1)])] [.index (.resolve "x") (.num 9)])
#guard obs case_indexBig__n1 == "err index"

-- indexBig__p1: x = (1) \n x:9
def case_indexBig__p1 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.num 1)]))])] [.index (.resolve "x") (.num 9)])
#guard obs case_indexBig__p1 == "err index"

-- indexBig__p12: x = (1, 2) \n x:9
def case_indexBig__p12 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)]))])] [.index (.resolve "x") (.num 9)])
#guard obs case_indexBig__p12 == "err index"

-- indexBig__p123: x = (1, 2, 3) \n x:9
def case_indexBig__p123 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2), (.num 3)]))])] [.index (.resolve "x") (.num 9)])
#guard obs case_indexBig__p123 == "err index"

-- indexBig__pee: x = ((), ()) \n x:9
def case_indexBig__pee : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.emptySequence 0)]))])] [.index (.resolve "x") (.num 9)])
#guard obs case_indexBig__pee == "err index"

-- indexBig__pe1: x = ((), 1) \n x:9
def case_indexBig__pe1 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.num 1)]))])] [.index (.resolve "x") (.num 9)])
#guard obs case_indexBig__pe1 == "err index"

-- indexBig__p1e: x = (1, ()) \n x:9
def case_indexBig__p1e : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.emptySequence 0)]))])] [.index (.resolve "x") (.num 9)])
#guard obs case_indexBig__p1e == "err index"

-- indexBig__p12_3: x = ((1, 2), 3) \n x:9
def case_indexBig__p12_3 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.num 3)]))])] [.index (.resolve "x") (.num 9)])
#guard obs case_indexBig__p12_3 == "err index"

-- indexBig__p12_34: x = ((1, 2), (3, 4)) \n x:9
def case_indexBig__p12_34 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.block (alg [] [] [] [(.num 3), (.num 4)]))]))])] [.index (.resolve "x") (.num 9)])
#guard obs case_indexBig__p12_34 == "err index"

-- indexBig__pe_12: x = ((), (1, 2)) \n x:9
def case_indexBig__pe_12 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.block (alg [] [] [] [(.num 1), (.num 2)]))]))])] [.index (.resolve "x") (.num 9)])
#guard obs case_indexBig__pe_12 == "err index"

-- indexBig__ppe1_2: x = (((), 1), 2) \n x:9
def case_indexBig__ppe1_2 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.num 1)])), (.num 2)]))])] [.index (.resolve "x") (.num 9)])
#guard obs case_indexBig__ppe1_2 == "err index"

-- indexBig__p12_e: x = ((1, 2), ()) \n x:9
def case_indexBig__p12_e : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.emptySequence 0)]))])] [.index (.resolve "x") (.num 9)])
#guard obs case_indexBig__p12_e == "err index"

-- indexBig__ppe: x = (()) \n x:9
def case_indexBig__ppe : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0)]))])] [.index (.resolve "x") (.num 9)])
#guard obs case_indexBig__ppe == "err index"

-- indexBig__pp1: x = ((1)) \n x:9
def case_indexBig__pp1 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1)]))]))])] [.index (.resolve "x") (.num 9)])
#guard obs case_indexBig__pp1 == "err index"

-- indexBig__ppp12: x = (((1, 2))) \n x:9
def case_indexBig__ppp12 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)]))]))]))])] [.index (.resolve "x") (.num 9)])
#guard obs case_indexBig__ppp12 == "err index"

-- indexBig__le: x = [] \n x:9
def case_indexBig__le : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [])])] [.index (.resolve "x") (.num 9)])
#guard obs case_indexBig__le == "err index"

-- indexBig__l7: x = [7] \n x:9
def case_indexBig__l7 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [(.num 7)])])] [.index (.resolve "x") (.num 9)])
#guard obs case_indexBig__l7 == "err index"

-- indexBig__l12: x = [1, 2] \n x:9
def case_indexBig__l12 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [(.num 1), (.num 2)])])] [.index (.resolve "x") (.num 9)])
#guard obs case_indexBig__l12 == "err index"

-- indexBig__l12_3: x = [[1, 2], 3] \n x:9
def case_indexBig__l12_3 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [(.listLiteral [(.num 1), (.num 2)]), (.num 3)])])] [.index (.resolve "x") (.num 9)])
#guard obs case_indexBig__l12_3 == "err index"

-- indexBig__lle: x = [[]] \n x:9
def case_indexBig__lle : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [(.listLiteral [])])])] [.index (.resolve "x") (.num 9)])
#guard obs case_indexBig__lle == "err index"

-- indexBig__l_e: x = [()] \n x:9
def case_indexBig__l_e : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [(.emptySequence 0)])])] [.index (.resolve "x") (.num 9)])
#guard obs case_indexBig__l_e == "err index"

-- indexBig__l_p12: x = [(1, 2)] \n x:9
def case_indexBig__l_p12 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [(.block (alg [] [] [] [(.num 1), (.num 2)]))])])] [.index (.resolve "x") (.num 9)])
#guard obs case_indexBig__l_p12 == "err index"

-- indexBig__p_l12: x = ([1, 2], 3) \n x:9
def case_indexBig__p_l12 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.listLiteral [(.num 1), (.num 2)]), (.num 3)]))])] [.index (.resolve "x") (.num 9)])
#guard obs case_indexBig__p_l12 == "err index"

-- indexBig__pl1: x = ([1]) \n x:9
def case_indexBig__pl1 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.listLiteral [(.num 1)])]))])] [.index (.resolve "x") (.num 9)])
#guard obs case_indexBig__pl1 == "err index"

-- eqSelf__e: x = () \n x == x
def case_eqSelf__e : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.emptySequence 0)])] [.binary .eq (.resolve "x") (.resolve "x")])
#guard obs case_eqSelf__e == "ok raw=1 n=1"

-- eqSelf__n0: x = 0 \n x == x
def case_eqSelf__n0 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.num 0)])] [.binary .eq (.resolve "x") (.resolve "x")])
#guard obs case_eqSelf__n0 == "ok raw=1 n=1"

-- eqSelf__n1: x = 1 \n x == x
def case_eqSelf__n1 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.num 1)])] [.binary .eq (.resolve "x") (.resolve "x")])
#guard obs case_eqSelf__n1 == "ok raw=1 n=1"

-- eqSelf__p1: x = (1) \n x == x
def case_eqSelf__p1 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.num 1)]))])] [.binary .eq (.resolve "x") (.resolve "x")])
#guard obs case_eqSelf__p1 == "ok raw=1 n=1"

-- eqSelf__p12: x = (1, 2) \n x == x
def case_eqSelf__p12 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)]))])] [.binary .eq (.resolve "x") (.resolve "x")])
#guard obs case_eqSelf__p12 == "ok raw=1 n=1"

-- eqSelf__p123: x = (1, 2, 3) \n x == x
def case_eqSelf__p123 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2), (.num 3)]))])] [.binary .eq (.resolve "x") (.resolve "x")])
#guard obs case_eqSelf__p123 == "ok raw=1 n=1"

-- eqSelf__pee: x = ((), ()) \n x == x
def case_eqSelf__pee : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.emptySequence 0)]))])] [.binary .eq (.resolve "x") (.resolve "x")])
#guard obs case_eqSelf__pee == "ok raw=1 n=1"

-- eqSelf__pe1: x = ((), 1) \n x == x
def case_eqSelf__pe1 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.num 1)]))])] [.binary .eq (.resolve "x") (.resolve "x")])
#guard obs case_eqSelf__pe1 == "ok raw=1 n=1"

-- eqSelf__p1e: x = (1, ()) \n x == x
def case_eqSelf__p1e : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.emptySequence 0)]))])] [.binary .eq (.resolve "x") (.resolve "x")])
#guard obs case_eqSelf__p1e == "ok raw=1 n=1"

-- eqSelf__p12_3: x = ((1, 2), 3) \n x == x
def case_eqSelf__p12_3 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.num 3)]))])] [.binary .eq (.resolve "x") (.resolve "x")])
#guard obs case_eqSelf__p12_3 == "ok raw=1 n=1"

-- eqSelf__p12_34: x = ((1, 2), (3, 4)) \n x == x
def case_eqSelf__p12_34 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.block (alg [] [] [] [(.num 3), (.num 4)]))]))])] [.binary .eq (.resolve "x") (.resolve "x")])
#guard obs case_eqSelf__p12_34 == "ok raw=1 n=1"

-- eqSelf__pe_12: x = ((), (1, 2)) \n x == x
def case_eqSelf__pe_12 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.block (alg [] [] [] [(.num 1), (.num 2)]))]))])] [.binary .eq (.resolve "x") (.resolve "x")])
#guard obs case_eqSelf__pe_12 == "ok raw=1 n=1"

-- eqSelf__ppe1_2: x = (((), 1), 2) \n x == x
def case_eqSelf__ppe1_2 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.num 1)])), (.num 2)]))])] [.binary .eq (.resolve "x") (.resolve "x")])
#guard obs case_eqSelf__ppe1_2 == "ok raw=1 n=1"

-- eqSelf__p12_e: x = ((1, 2), ()) \n x == x
def case_eqSelf__p12_e : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.emptySequence 0)]))])] [.binary .eq (.resolve "x") (.resolve "x")])
#guard obs case_eqSelf__p12_e == "ok raw=1 n=1"

-- eqSelf__ppe: x = (()) \n x == x
def case_eqSelf__ppe : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0)]))])] [.binary .eq (.resolve "x") (.resolve "x")])
#guard obs case_eqSelf__ppe == "ok raw=1 n=1"

-- eqSelf__pp1: x = ((1)) \n x == x
def case_eqSelf__pp1 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1)]))]))])] [.binary .eq (.resolve "x") (.resolve "x")])
#guard obs case_eqSelf__pp1 == "ok raw=1 n=1"

-- eqSelf__ppp12: x = (((1, 2))) \n x == x
def case_eqSelf__ppp12 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)]))]))]))])] [.binary .eq (.resolve "x") (.resolve "x")])
#guard obs case_eqSelf__ppp12 == "ok raw=1 n=1"

-- eqSelf__le: x = [] \n x == x
def case_eqSelf__le : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [])])] [.binary .eq (.resolve "x") (.resolve "x")])
#guard obs case_eqSelf__le == "ok raw=1 n=1"

-- eqSelf__l7: x = [7] \n x == x
def case_eqSelf__l7 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [(.num 7)])])] [.binary .eq (.resolve "x") (.resolve "x")])
#guard obs case_eqSelf__l7 == "ok raw=1 n=1"

-- eqSelf__l12: x = [1, 2] \n x == x
def case_eqSelf__l12 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [(.num 1), (.num 2)])])] [.binary .eq (.resolve "x") (.resolve "x")])
#guard obs case_eqSelf__l12 == "ok raw=1 n=1"

-- eqSelf__l12_3: x = [[1, 2], 3] \n x == x
def case_eqSelf__l12_3 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [(.listLiteral [(.num 1), (.num 2)]), (.num 3)])])] [.binary .eq (.resolve "x") (.resolve "x")])
#guard obs case_eqSelf__l12_3 == "ok raw=1 n=1"

-- eqSelf__lle: x = [[]] \n x == x
def case_eqSelf__lle : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [(.listLiteral [])])])] [.binary .eq (.resolve "x") (.resolve "x")])
#guard obs case_eqSelf__lle == "ok raw=1 n=1"

-- eqSelf__l_e: x = [()] \n x == x
def case_eqSelf__l_e : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [(.emptySequence 0)])])] [.binary .eq (.resolve "x") (.resolve "x")])
#guard obs case_eqSelf__l_e == "ok raw=1 n=1"

-- eqSelf__l_p12: x = [(1, 2)] \n x == x
def case_eqSelf__l_p12 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [(.block (alg [] [] [] [(.num 1), (.num 2)]))])])] [.binary .eq (.resolve "x") (.resolve "x")])
#guard obs case_eqSelf__l_p12 == "ok raw=1 n=1"

-- eqSelf__p_l12: x = ([1, 2], 3) \n x == x
def case_eqSelf__p_l12 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.listLiteral [(.num 1), (.num 2)]), (.num 3)]))])] [.binary .eq (.resolve "x") (.resolve "x")])
#guard obs case_eqSelf__p_l12 == "ok raw=1 n=1"

-- eqSelf__pl1: x = ([1]) \n x == x
def case_eqSelf__pl1 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.listLiteral [(.num 1)])]))])] [.binary .eq (.resolve "x") (.resolve "x")])
#guard obs case_eqSelf__pl1 == "ok raw=1 n=1"

-- neqSelf__e: x = () \n x != x
def case_neqSelf__e : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.emptySequence 0)])] [.binary .ne (.resolve "x") (.resolve "x")])
#guard obs case_neqSelf__e == "ok raw=0 n=1"

-- neqSelf__n0: x = 0 \n x != x
def case_neqSelf__n0 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.num 0)])] [.binary .ne (.resolve "x") (.resolve "x")])
#guard obs case_neqSelf__n0 == "ok raw=0 n=1"

-- neqSelf__n1: x = 1 \n x != x
def case_neqSelf__n1 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.num 1)])] [.binary .ne (.resolve "x") (.resolve "x")])
#guard obs case_neqSelf__n1 == "ok raw=0 n=1"

-- neqSelf__p1: x = (1) \n x != x
def case_neqSelf__p1 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.num 1)]))])] [.binary .ne (.resolve "x") (.resolve "x")])
#guard obs case_neqSelf__p1 == "ok raw=0 n=1"

-- neqSelf__p12: x = (1, 2) \n x != x
def case_neqSelf__p12 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)]))])] [.binary .ne (.resolve "x") (.resolve "x")])
#guard obs case_neqSelf__p12 == "ok raw=0 n=1"

-- neqSelf__p123: x = (1, 2, 3) \n x != x
def case_neqSelf__p123 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2), (.num 3)]))])] [.binary .ne (.resolve "x") (.resolve "x")])
#guard obs case_neqSelf__p123 == "ok raw=0 n=1"

-- neqSelf__pee: x = ((), ()) \n x != x
def case_neqSelf__pee : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.emptySequence 0)]))])] [.binary .ne (.resolve "x") (.resolve "x")])
#guard obs case_neqSelf__pee == "ok raw=0 n=1"

-- neqSelf__pe1: x = ((), 1) \n x != x
def case_neqSelf__pe1 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.num 1)]))])] [.binary .ne (.resolve "x") (.resolve "x")])
#guard obs case_neqSelf__pe1 == "ok raw=0 n=1"

-- neqSelf__p1e: x = (1, ()) \n x != x
def case_neqSelf__p1e : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.emptySequence 0)]))])] [.binary .ne (.resolve "x") (.resolve "x")])
#guard obs case_neqSelf__p1e == "ok raw=0 n=1"

-- neqSelf__p12_3: x = ((1, 2), 3) \n x != x
def case_neqSelf__p12_3 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.num 3)]))])] [.binary .ne (.resolve "x") (.resolve "x")])
#guard obs case_neqSelf__p12_3 == "ok raw=0 n=1"

-- neqSelf__p12_34: x = ((1, 2), (3, 4)) \n x != x
def case_neqSelf__p12_34 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.block (alg [] [] [] [(.num 3), (.num 4)]))]))])] [.binary .ne (.resolve "x") (.resolve "x")])
#guard obs case_neqSelf__p12_34 == "ok raw=0 n=1"

-- neqSelf__pe_12: x = ((), (1, 2)) \n x != x
def case_neqSelf__pe_12 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.block (alg [] [] [] [(.num 1), (.num 2)]))]))])] [.binary .ne (.resolve "x") (.resolve "x")])
#guard obs case_neqSelf__pe_12 == "ok raw=0 n=1"

-- neqSelf__ppe1_2: x = (((), 1), 2) \n x != x
def case_neqSelf__ppe1_2 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.num 1)])), (.num 2)]))])] [.binary .ne (.resolve "x") (.resolve "x")])
#guard obs case_neqSelf__ppe1_2 == "ok raw=0 n=1"

-- neqSelf__p12_e: x = ((1, 2), ()) \n x != x
def case_neqSelf__p12_e : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.emptySequence 0)]))])] [.binary .ne (.resolve "x") (.resolve "x")])
#guard obs case_neqSelf__p12_e == "ok raw=0 n=1"

-- neqSelf__ppe: x = (()) \n x != x
def case_neqSelf__ppe : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0)]))])] [.binary .ne (.resolve "x") (.resolve "x")])
#guard obs case_neqSelf__ppe == "ok raw=0 n=1"

-- neqSelf__pp1: x = ((1)) \n x != x
def case_neqSelf__pp1 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1)]))]))])] [.binary .ne (.resolve "x") (.resolve "x")])
#guard obs case_neqSelf__pp1 == "ok raw=0 n=1"

-- neqSelf__ppp12: x = (((1, 2))) \n x != x
def case_neqSelf__ppp12 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)]))]))]))])] [.binary .ne (.resolve "x") (.resolve "x")])
#guard obs case_neqSelf__ppp12 == "ok raw=0 n=1"

-- neqSelf__le: x = [] \n x != x
def case_neqSelf__le : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [])])] [.binary .ne (.resolve "x") (.resolve "x")])
#guard obs case_neqSelf__le == "ok raw=0 n=1"

-- neqSelf__l7: x = [7] \n x != x
def case_neqSelf__l7 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [(.num 7)])])] [.binary .ne (.resolve "x") (.resolve "x")])
#guard obs case_neqSelf__l7 == "ok raw=0 n=1"

-- neqSelf__l12: x = [1, 2] \n x != x
def case_neqSelf__l12 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [(.num 1), (.num 2)])])] [.binary .ne (.resolve "x") (.resolve "x")])
#guard obs case_neqSelf__l12 == "ok raw=0 n=1"

-- neqSelf__l12_3: x = [[1, 2], 3] \n x != x
def case_neqSelf__l12_3 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [(.listLiteral [(.num 1), (.num 2)]), (.num 3)])])] [.binary .ne (.resolve "x") (.resolve "x")])
#guard obs case_neqSelf__l12_3 == "ok raw=0 n=1"

-- neqSelf__lle: x = [[]] \n x != x
def case_neqSelf__lle : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [(.listLiteral [])])])] [.binary .ne (.resolve "x") (.resolve "x")])
#guard obs case_neqSelf__lle == "ok raw=0 n=1"

-- neqSelf__l_e: x = [()] \n x != x
def case_neqSelf__l_e : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [(.emptySequence 0)])])] [.binary .ne (.resolve "x") (.resolve "x")])
#guard obs case_neqSelf__l_e == "ok raw=0 n=1"

-- neqSelf__l_p12: x = [(1, 2)] \n x != x
def case_neqSelf__l_p12 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [(.block (alg [] [] [] [(.num 1), (.num 2)]))])])] [.binary .ne (.resolve "x") (.resolve "x")])
#guard obs case_neqSelf__l_p12 == "ok raw=0 n=1"

-- neqSelf__p_l12: x = ([1, 2], 3) \n x != x
def case_neqSelf__p_l12 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.listLiteral [(.num 1), (.num 2)]), (.num 3)]))])] [.binary .ne (.resolve "x") (.resolve "x")])
#guard obs case_neqSelf__p_l12 == "ok raw=0 n=1"

-- neqSelf__pl1: x = ([1]) \n x != x
def case_neqSelf__pl1 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.listLiteral [(.num 1)])]))])] [.binary .ne (.resolve "x") (.resolve "x")])
#guard obs case_neqSelf__pl1 == "ok raw=0 n=1"

-- eqIdentity__e: I(a) = a \n x = () \n x == I(x)
def case_eqIdentity__e : Expr :=
  .block (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"]), privateProp "x" (alg [] [] [] [(.emptySequence 0)])] [.binary .eq (.resolve "x") (.call (.resolve "I") (alg [] [] [] [.resolve "x"]))])
#guard obs case_eqIdentity__e == "ok raw=1 n=1"

-- eqIdentity__n0: I(a) = a \n x = 0 \n x == I(x)
def case_eqIdentity__n0 : Expr :=
  .block (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"]), privateProp "x" (alg [] [] [] [(.num 0)])] [.binary .eq (.resolve "x") (.call (.resolve "I") (alg [] [] [] [.resolve "x"]))])
#guard obs case_eqIdentity__n0 == "ok raw=1 n=1"

-- eqIdentity__n1: I(a) = a \n x = 1 \n x == I(x)
def case_eqIdentity__n1 : Expr :=
  .block (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"]), privateProp "x" (alg [] [] [] [(.num 1)])] [.binary .eq (.resolve "x") (.call (.resolve "I") (alg [] [] [] [.resolve "x"]))])
#guard obs case_eqIdentity__n1 == "ok raw=1 n=1"

-- eqIdentity__p1: I(a) = a \n x = (1) \n x == I(x)
def case_eqIdentity__p1 : Expr :=
  .block (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"]), privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.num 1)]))])] [.binary .eq (.resolve "x") (.call (.resolve "I") (alg [] [] [] [.resolve "x"]))])
#guard obs case_eqIdentity__p1 == "ok raw=1 n=1"

-- eqIdentity__p12: I(a) = a \n x = (1, 2) \n x == I(x)
def case_eqIdentity__p12 : Expr :=
  .block (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"]), privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)]))])] [.binary .eq (.resolve "x") (.call (.resolve "I") (alg [] [] [] [.resolve "x"]))])
#guard obs case_eqIdentity__p12 == "ok raw=1 n=1"

-- eqIdentity__p123: I(a) = a \n x = (1, 2, 3) \n x == I(x)
def case_eqIdentity__p123 : Expr :=
  .block (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"]), privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2), (.num 3)]))])] [.binary .eq (.resolve "x") (.call (.resolve "I") (alg [] [] [] [.resolve "x"]))])
#guard obs case_eqIdentity__p123 == "ok raw=1 n=1"

-- eqIdentity__pee: I(a) = a \n x = ((), ()) \n x == I(x)
def case_eqIdentity__pee : Expr :=
  .block (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"]), privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.emptySequence 0)]))])] [.binary .eq (.resolve "x") (.call (.resolve "I") (alg [] [] [] [.resolve "x"]))])
#guard obs case_eqIdentity__pee == "ok raw=1 n=1"

-- eqIdentity__pe1: I(a) = a \n x = ((), 1) \n x == I(x)
def case_eqIdentity__pe1 : Expr :=
  .block (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"]), privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.num 1)]))])] [.binary .eq (.resolve "x") (.call (.resolve "I") (alg [] [] [] [.resolve "x"]))])
#guard obs case_eqIdentity__pe1 == "ok raw=1 n=1"

-- eqIdentity__p1e: I(a) = a \n x = (1, ()) \n x == I(x)
def case_eqIdentity__p1e : Expr :=
  .block (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"]), privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.emptySequence 0)]))])] [.binary .eq (.resolve "x") (.call (.resolve "I") (alg [] [] [] [.resolve "x"]))])
#guard obs case_eqIdentity__p1e == "ok raw=1 n=1"

-- eqIdentity__p12_3: I(a) = a \n x = ((1, 2), 3) \n x == I(x)
def case_eqIdentity__p12_3 : Expr :=
  .block (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"]), privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.num 3)]))])] [.binary .eq (.resolve "x") (.call (.resolve "I") (alg [] [] [] [.resolve "x"]))])
#guard obs case_eqIdentity__p12_3 == "ok raw=1 n=1"

-- eqIdentity__p12_34: I(a) = a \n x = ((1, 2), (3, 4)) \n x == I(x)
def case_eqIdentity__p12_34 : Expr :=
  .block (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"]), privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.block (alg [] [] [] [(.num 3), (.num 4)]))]))])] [.binary .eq (.resolve "x") (.call (.resolve "I") (alg [] [] [] [.resolve "x"]))])
#guard obs case_eqIdentity__p12_34 == "ok raw=1 n=1"

-- eqIdentity__pe_12: I(a) = a \n x = ((), (1, 2)) \n x == I(x)
def case_eqIdentity__pe_12 : Expr :=
  .block (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"]), privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.block (alg [] [] [] [(.num 1), (.num 2)]))]))])] [.binary .eq (.resolve "x") (.call (.resolve "I") (alg [] [] [] [.resolve "x"]))])
#guard obs case_eqIdentity__pe_12 == "ok raw=1 n=1"

-- eqIdentity__ppe1_2: I(a) = a \n x = (((), 1), 2) \n x == I(x)
def case_eqIdentity__ppe1_2 : Expr :=
  .block (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"]), privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.num 1)])), (.num 2)]))])] [.binary .eq (.resolve "x") (.call (.resolve "I") (alg [] [] [] [.resolve "x"]))])
#guard obs case_eqIdentity__ppe1_2 == "ok raw=1 n=1"

-- eqIdentity__p12_e: I(a) = a \n x = ((1, 2), ()) \n x == I(x)
def case_eqIdentity__p12_e : Expr :=
  .block (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"]), privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.emptySequence 0)]))])] [.binary .eq (.resolve "x") (.call (.resolve "I") (alg [] [] [] [.resolve "x"]))])
#guard obs case_eqIdentity__p12_e == "ok raw=1 n=1"

-- eqIdentity__ppe: I(a) = a \n x = (()) \n x == I(x)
def case_eqIdentity__ppe : Expr :=
  .block (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"]), privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0)]))])] [.binary .eq (.resolve "x") (.call (.resolve "I") (alg [] [] [] [.resolve "x"]))])
#guard obs case_eqIdentity__ppe == "ok raw=1 n=1"

-- eqIdentity__pp1: I(a) = a \n x = ((1)) \n x == I(x)
def case_eqIdentity__pp1 : Expr :=
  .block (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"]), privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1)]))]))])] [.binary .eq (.resolve "x") (.call (.resolve "I") (alg [] [] [] [.resolve "x"]))])
#guard obs case_eqIdentity__pp1 == "ok raw=1 n=1"

-- eqIdentity__ppp12: I(a) = a \n x = (((1, 2))) \n x == I(x)
def case_eqIdentity__ppp12 : Expr :=
  .block (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"]), privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)]))]))]))])] [.binary .eq (.resolve "x") (.call (.resolve "I") (alg [] [] [] [.resolve "x"]))])
#guard obs case_eqIdentity__ppp12 == "ok raw=1 n=1"

-- eqIdentity__le: I(a) = a \n x = [] \n x == I(x)
def case_eqIdentity__le : Expr :=
  .block (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"]), privateProp "x" (alg [] [] [] [(.listLiteral [])])] [.binary .eq (.resolve "x") (.call (.resolve "I") (alg [] [] [] [.resolve "x"]))])
#guard obs case_eqIdentity__le == "ok raw=1 n=1"

-- eqIdentity__l7: I(a) = a \n x = [7] \n x == I(x)
def case_eqIdentity__l7 : Expr :=
  .block (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"]), privateProp "x" (alg [] [] [] [(.listLiteral [(.num 7)])])] [.binary .eq (.resolve "x") (.call (.resolve "I") (alg [] [] [] [.resolve "x"]))])
#guard obs case_eqIdentity__l7 == "ok raw=1 n=1"

-- eqIdentity__l12: I(a) = a \n x = [1, 2] \n x == I(x)
def case_eqIdentity__l12 : Expr :=
  .block (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"]), privateProp "x" (alg [] [] [] [(.listLiteral [(.num 1), (.num 2)])])] [.binary .eq (.resolve "x") (.call (.resolve "I") (alg [] [] [] [.resolve "x"]))])
#guard obs case_eqIdentity__l12 == "ok raw=1 n=1"

-- eqIdentity__l12_3: I(a) = a \n x = [[1, 2], 3] \n x == I(x)
def case_eqIdentity__l12_3 : Expr :=
  .block (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"]), privateProp "x" (alg [] [] [] [(.listLiteral [(.listLiteral [(.num 1), (.num 2)]), (.num 3)])])] [.binary .eq (.resolve "x") (.call (.resolve "I") (alg [] [] [] [.resolve "x"]))])
#guard obs case_eqIdentity__l12_3 == "ok raw=1 n=1"

-- eqIdentity__lle: I(a) = a \n x = [[]] \n x == I(x)
def case_eqIdentity__lle : Expr :=
  .block (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"]), privateProp "x" (alg [] [] [] [(.listLiteral [(.listLiteral [])])])] [.binary .eq (.resolve "x") (.call (.resolve "I") (alg [] [] [] [.resolve "x"]))])
#guard obs case_eqIdentity__lle == "ok raw=1 n=1"

-- eqIdentity__l_e: I(a) = a \n x = [()] \n x == I(x)
def case_eqIdentity__l_e : Expr :=
  .block (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"]), privateProp "x" (alg [] [] [] [(.listLiteral [(.emptySequence 0)])])] [.binary .eq (.resolve "x") (.call (.resolve "I") (alg [] [] [] [.resolve "x"]))])
#guard obs case_eqIdentity__l_e == "ok raw=1 n=1"

-- eqIdentity__l_p12: I(a) = a \n x = [(1, 2)] \n x == I(x)
def case_eqIdentity__l_p12 : Expr :=
  .block (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"]), privateProp "x" (alg [] [] [] [(.listLiteral [(.block (alg [] [] [] [(.num 1), (.num 2)]))])])] [.binary .eq (.resolve "x") (.call (.resolve "I") (alg [] [] [] [.resolve "x"]))])
#guard obs case_eqIdentity__l_p12 == "ok raw=1 n=1"

-- eqIdentity__p_l12: I(a) = a \n x = ([1, 2], 3) \n x == I(x)
def case_eqIdentity__p_l12 : Expr :=
  .block (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"]), privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.listLiteral [(.num 1), (.num 2)]), (.num 3)]))])] [.binary .eq (.resolve "x") (.call (.resolve "I") (alg [] [] [] [.resolve "x"]))])
#guard obs case_eqIdentity__p_l12 == "ok raw=1 n=1"

-- eqIdentity__pl1: I(a) = a \n x = ([1]) \n x == I(x)
def case_eqIdentity__pl1 : Expr :=
  .block (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"]), privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.listLiteral [(.num 1)])]))])] [.binary .eq (.resolve "x") (.call (.resolve "I") (alg [] [] [] [.resolve "x"]))])
#guard obs case_eqIdentity__pl1 == "ok raw=1 n=1"

-- identity__e: I(a) = a \n x = () \n I(x)
def case_identity__e : Expr :=
  .block (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"]), privateProp "x" (alg [] [] [] [(.emptySequence 0)])] [.call (.resolve "I") (alg [] [] [] [.resolve "x"])])
#guard obs case_identity__e == "ok raw=S[] n=1"

-- identity__n0: I(a) = a \n x = 0 \n I(x)
def case_identity__n0 : Expr :=
  .block (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"]), privateProp "x" (alg [] [] [] [(.num 0)])] [.call (.resolve "I") (alg [] [] [] [.resolve "x"])])
#guard obs case_identity__n0 == "ok raw=0 n=1"

-- identity__n1: I(a) = a \n x = 1 \n I(x)
def case_identity__n1 : Expr :=
  .block (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"]), privateProp "x" (alg [] [] [] [(.num 1)])] [.call (.resolve "I") (alg [] [] [] [.resolve "x"])])
#guard obs case_identity__n1 == "ok raw=1 n=1"

-- identity__p1: I(a) = a \n x = (1) \n I(x)
def case_identity__p1 : Expr :=
  .block (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"]), privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.num 1)]))])] [.call (.resolve "I") (alg [] [] [] [.resolve "x"])])
#guard obs case_identity__p1 == "ok raw=1 n=1"

-- identity__p12: I(a) = a \n x = (1, 2) \n I(x)
def case_identity__p12 : Expr :=
  .block (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"]), privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)]))])] [.call (.resolve "I") (alg [] [] [] [.resolve "x"])])
#guard obs case_identity__p12 == "ok raw=S[1, 2] n=1"

-- identity__p123: I(a) = a \n x = (1, 2, 3) \n I(x)
def case_identity__p123 : Expr :=
  .block (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"]), privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2), (.num 3)]))])] [.call (.resolve "I") (alg [] [] [] [.resolve "x"])])
#guard obs case_identity__p123 == "ok raw=S[1, 2, 3] n=1"

-- identity__pee: I(a) = a \n x = ((), ()) \n I(x)
def case_identity__pee : Expr :=
  .block (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"]), privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.emptySequence 0)]))])] [.call (.resolve "I") (alg [] [] [] [.resolve "x"])])
#guard obs case_identity__pee == "ok raw=S[S[], S[]] n=1"

-- identity__pe1: I(a) = a \n x = ((), 1) \n I(x)
def case_identity__pe1 : Expr :=
  .block (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"]), privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.num 1)]))])] [.call (.resolve "I") (alg [] [] [] [.resolve "x"])])
#guard obs case_identity__pe1 == "ok raw=S[S[], 1] n=1"

-- identity__p1e: I(a) = a \n x = (1, ()) \n I(x)
def case_identity__p1e : Expr :=
  .block (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"]), privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.emptySequence 0)]))])] [.call (.resolve "I") (alg [] [] [] [.resolve "x"])])
#guard obs case_identity__p1e == "ok raw=S[1, S[]] n=1"

-- identity__p12_3: I(a) = a \n x = ((1, 2), 3) \n I(x)
def case_identity__p12_3 : Expr :=
  .block (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"]), privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.num 3)]))])] [.call (.resolve "I") (alg [] [] [] [.resolve "x"])])
#guard obs case_identity__p12_3 == "ok raw=S[S[1, 2], 3] n=1"

-- identity__p12_34: I(a) = a \n x = ((1, 2), (3, 4)) \n I(x)
def case_identity__p12_34 : Expr :=
  .block (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"]), privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.block (alg [] [] [] [(.num 3), (.num 4)]))]))])] [.call (.resolve "I") (alg [] [] [] [.resolve "x"])])
#guard obs case_identity__p12_34 == "ok raw=S[S[1, 2], S[3, 4]] n=1"

-- identity__pe_12: I(a) = a \n x = ((), (1, 2)) \n I(x)
def case_identity__pe_12 : Expr :=
  .block (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"]), privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.block (alg [] [] [] [(.num 1), (.num 2)]))]))])] [.call (.resolve "I") (alg [] [] [] [.resolve "x"])])
#guard obs case_identity__pe_12 == "ok raw=S[S[], S[1, 2]] n=1"

-- identity__ppe1_2: I(a) = a \n x = (((), 1), 2) \n I(x)
def case_identity__ppe1_2 : Expr :=
  .block (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"]), privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.num 1)])), (.num 2)]))])] [.call (.resolve "I") (alg [] [] [] [.resolve "x"])])
#guard obs case_identity__ppe1_2 == "ok raw=S[S[S[], 1], 2] n=1"

-- identity__p12_e: I(a) = a \n x = ((1, 2), ()) \n I(x)
def case_identity__p12_e : Expr :=
  .block (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"]), privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.emptySequence 0)]))])] [.call (.resolve "I") (alg [] [] [] [.resolve "x"])])
#guard obs case_identity__p12_e == "ok raw=S[S[1, 2], S[]] n=1"

-- identity__ppe: I(a) = a \n x = (()) \n I(x)
def case_identity__ppe : Expr :=
  .block (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"]), privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0)]))])] [.call (.resolve "I") (alg [] [] [] [.resolve "x"])])
#guard obs case_identity__ppe == "ok raw=S[] n=1"

-- identity__pp1: I(a) = a \n x = ((1)) \n I(x)
def case_identity__pp1 : Expr :=
  .block (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"]), privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1)]))]))])] [.call (.resolve "I") (alg [] [] [] [.resolve "x"])])
#guard obs case_identity__pp1 == "ok raw=1 n=1"

-- identity__ppp12: I(a) = a \n x = (((1, 2))) \n I(x)
def case_identity__ppp12 : Expr :=
  .block (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"]), privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)]))]))]))])] [.call (.resolve "I") (alg [] [] [] [.resolve "x"])])
#guard obs case_identity__ppp12 == "ok raw=S[1, 2] n=1"

-- identity__le: I(a) = a \n x = [] \n I(x)
def case_identity__le : Expr :=
  .block (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"]), privateProp "x" (alg [] [] [] [(.listLiteral [])])] [.call (.resolve "I") (alg [] [] [] [.resolve "x"])])
#guard obs case_identity__le == "ok raw=L[] n=1"

-- identity__l7: I(a) = a \n x = [7] \n I(x)
def case_identity__l7 : Expr :=
  .block (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"]), privateProp "x" (alg [] [] [] [(.listLiteral [(.num 7)])])] [.call (.resolve "I") (alg [] [] [] [.resolve "x"])])
#guard obs case_identity__l7 == "ok raw=L[7] n=1"

-- identity__l12: I(a) = a \n x = [1, 2] \n I(x)
def case_identity__l12 : Expr :=
  .block (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"]), privateProp "x" (alg [] [] [] [(.listLiteral [(.num 1), (.num 2)])])] [.call (.resolve "I") (alg [] [] [] [.resolve "x"])])
#guard obs case_identity__l12 == "ok raw=L[1, 2] n=1"

-- identity__l12_3: I(a) = a \n x = [[1, 2], 3] \n I(x)
def case_identity__l12_3 : Expr :=
  .block (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"]), privateProp "x" (alg [] [] [] [(.listLiteral [(.listLiteral [(.num 1), (.num 2)]), (.num 3)])])] [.call (.resolve "I") (alg [] [] [] [.resolve "x"])])
#guard obs case_identity__l12_3 == "ok raw=L[L[1, 2], 3] n=1"

-- identity__lle: I(a) = a \n x = [[]] \n I(x)
def case_identity__lle : Expr :=
  .block (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"]), privateProp "x" (alg [] [] [] [(.listLiteral [(.listLiteral [])])])] [.call (.resolve "I") (alg [] [] [] [.resolve "x"])])
#guard obs case_identity__lle == "ok raw=L[L[]] n=1"

-- identity__l_e: I(a) = a \n x = [()] \n I(x)
def case_identity__l_e : Expr :=
  .block (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"]), privateProp "x" (alg [] [] [] [(.listLiteral [(.emptySequence 0)])])] [.call (.resolve "I") (alg [] [] [] [.resolve "x"])])
#guard obs case_identity__l_e == "ok raw=L[S[]] n=1"

-- identity__l_p12: I(a) = a \n x = [(1, 2)] \n I(x)
def case_identity__l_p12 : Expr :=
  .block (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"]), privateProp "x" (alg [] [] [] [(.listLiteral [(.block (alg [] [] [] [(.num 1), (.num 2)]))])])] [.call (.resolve "I") (alg [] [] [] [.resolve "x"])])
#guard obs case_identity__l_p12 == "ok raw=L[S[1, 2]] n=1"

-- identity__p_l12: I(a) = a \n x = ([1, 2], 3) \n I(x)
def case_identity__p_l12 : Expr :=
  .block (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"]), privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.listLiteral [(.num 1), (.num 2)]), (.num 3)]))])] [.call (.resolve "I") (alg [] [] [] [.resolve "x"])])
#guard obs case_identity__p_l12 == "ok raw=S[L[1, 2], 3] n=1"

-- identity__pl1: I(a) = a \n x = ([1]) \n I(x)
def case_identity__pl1 : Expr :=
  .block (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"]), privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.listLiteral [(.num 1)])]))])] [.call (.resolve "I") (alg [] [] [] [.resolve "x"])])
#guard obs case_identity__pl1 == "ok raw=L[1] n=1"

-- identityTwice__e: I(a) = a \n x = () \n I(I(x))
def case_identityTwice__e : Expr :=
  .block (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"]), privateProp "x" (alg [] [] [] [(.emptySequence 0)])] [.call (.resolve "I") (alg [] [] [] [.call (.resolve "I") (alg [] [] [] [.resolve "x"])])])
#guard obs case_identityTwice__e == "ok raw=S[] n=1"

-- identityTwice__n0: I(a) = a \n x = 0 \n I(I(x))
def case_identityTwice__n0 : Expr :=
  .block (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"]), privateProp "x" (alg [] [] [] [(.num 0)])] [.call (.resolve "I") (alg [] [] [] [.call (.resolve "I") (alg [] [] [] [.resolve "x"])])])
#guard obs case_identityTwice__n0 == "ok raw=0 n=1"

-- identityTwice__n1: I(a) = a \n x = 1 \n I(I(x))
def case_identityTwice__n1 : Expr :=
  .block (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"]), privateProp "x" (alg [] [] [] [(.num 1)])] [.call (.resolve "I") (alg [] [] [] [.call (.resolve "I") (alg [] [] [] [.resolve "x"])])])
#guard obs case_identityTwice__n1 == "ok raw=1 n=1"

-- identityTwice__p1: I(a) = a \n x = (1) \n I(I(x))
def case_identityTwice__p1 : Expr :=
  .block (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"]), privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.num 1)]))])] [.call (.resolve "I") (alg [] [] [] [.call (.resolve "I") (alg [] [] [] [.resolve "x"])])])
#guard obs case_identityTwice__p1 == "ok raw=1 n=1"

-- identityTwice__p12: I(a) = a \n x = (1, 2) \n I(I(x))
def case_identityTwice__p12 : Expr :=
  .block (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"]), privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)]))])] [.call (.resolve "I") (alg [] [] [] [.call (.resolve "I") (alg [] [] [] [.resolve "x"])])])
#guard obs case_identityTwice__p12 == "ok raw=S[1, 2] n=1"

-- identityTwice__p123: I(a) = a \n x = (1, 2, 3) \n I(I(x))
def case_identityTwice__p123 : Expr :=
  .block (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"]), privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2), (.num 3)]))])] [.call (.resolve "I") (alg [] [] [] [.call (.resolve "I") (alg [] [] [] [.resolve "x"])])])
#guard obs case_identityTwice__p123 == "ok raw=S[1, 2, 3] n=1"

-- identityTwice__pee: I(a) = a \n x = ((), ()) \n I(I(x))
def case_identityTwice__pee : Expr :=
  .block (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"]), privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.emptySequence 0)]))])] [.call (.resolve "I") (alg [] [] [] [.call (.resolve "I") (alg [] [] [] [.resolve "x"])])])
#guard obs case_identityTwice__pee == "ok raw=S[S[], S[]] n=1"

-- identityTwice__pe1: I(a) = a \n x = ((), 1) \n I(I(x))
def case_identityTwice__pe1 : Expr :=
  .block (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"]), privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.num 1)]))])] [.call (.resolve "I") (alg [] [] [] [.call (.resolve "I") (alg [] [] [] [.resolve "x"])])])
#guard obs case_identityTwice__pe1 == "ok raw=S[S[], 1] n=1"

-- identityTwice__p1e: I(a) = a \n x = (1, ()) \n I(I(x))
def case_identityTwice__p1e : Expr :=
  .block (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"]), privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.emptySequence 0)]))])] [.call (.resolve "I") (alg [] [] [] [.call (.resolve "I") (alg [] [] [] [.resolve "x"])])])
#guard obs case_identityTwice__p1e == "ok raw=S[1, S[]] n=1"

-- identityTwice__p12_3: I(a) = a \n x = ((1, 2), 3) \n I(I(x))
def case_identityTwice__p12_3 : Expr :=
  .block (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"]), privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.num 3)]))])] [.call (.resolve "I") (alg [] [] [] [.call (.resolve "I") (alg [] [] [] [.resolve "x"])])])
#guard obs case_identityTwice__p12_3 == "ok raw=S[S[1, 2], 3] n=1"

-- identityTwice__p12_34: I(a) = a \n x = ((1, 2), (3, 4)) \n I(I(x))
def case_identityTwice__p12_34 : Expr :=
  .block (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"]), privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.block (alg [] [] [] [(.num 3), (.num 4)]))]))])] [.call (.resolve "I") (alg [] [] [] [.call (.resolve "I") (alg [] [] [] [.resolve "x"])])])
#guard obs case_identityTwice__p12_34 == "ok raw=S[S[1, 2], S[3, 4]] n=1"

-- identityTwice__pe_12: I(a) = a \n x = ((), (1, 2)) \n I(I(x))
def case_identityTwice__pe_12 : Expr :=
  .block (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"]), privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.block (alg [] [] [] [(.num 1), (.num 2)]))]))])] [.call (.resolve "I") (alg [] [] [] [.call (.resolve "I") (alg [] [] [] [.resolve "x"])])])
#guard obs case_identityTwice__pe_12 == "ok raw=S[S[], S[1, 2]] n=1"

-- identityTwice__ppe1_2: I(a) = a \n x = (((), 1), 2) \n I(I(x))
def case_identityTwice__ppe1_2 : Expr :=
  .block (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"]), privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.num 1)])), (.num 2)]))])] [.call (.resolve "I") (alg [] [] [] [.call (.resolve "I") (alg [] [] [] [.resolve "x"])])])
#guard obs case_identityTwice__ppe1_2 == "ok raw=S[S[S[], 1], 2] n=1"

-- identityTwice__p12_e: I(a) = a \n x = ((1, 2), ()) \n I(I(x))
def case_identityTwice__p12_e : Expr :=
  .block (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"]), privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.emptySequence 0)]))])] [.call (.resolve "I") (alg [] [] [] [.call (.resolve "I") (alg [] [] [] [.resolve "x"])])])
#guard obs case_identityTwice__p12_e == "ok raw=S[S[1, 2], S[]] n=1"

-- identityTwice__ppe: I(a) = a \n x = (()) \n I(I(x))
def case_identityTwice__ppe : Expr :=
  .block (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"]), privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0)]))])] [.call (.resolve "I") (alg [] [] [] [.call (.resolve "I") (alg [] [] [] [.resolve "x"])])])
#guard obs case_identityTwice__ppe == "ok raw=S[] n=1"

-- identityTwice__pp1: I(a) = a \n x = ((1)) \n I(I(x))
def case_identityTwice__pp1 : Expr :=
  .block (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"]), privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1)]))]))])] [.call (.resolve "I") (alg [] [] [] [.call (.resolve "I") (alg [] [] [] [.resolve "x"])])])
#guard obs case_identityTwice__pp1 == "ok raw=1 n=1"

-- identityTwice__ppp12: I(a) = a \n x = (((1, 2))) \n I(I(x))
def case_identityTwice__ppp12 : Expr :=
  .block (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"]), privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)]))]))]))])] [.call (.resolve "I") (alg [] [] [] [.call (.resolve "I") (alg [] [] [] [.resolve "x"])])])
#guard obs case_identityTwice__ppp12 == "ok raw=S[1, 2] n=1"

-- identityTwice__le: I(a) = a \n x = [] \n I(I(x))
def case_identityTwice__le : Expr :=
  .block (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"]), privateProp "x" (alg [] [] [] [(.listLiteral [])])] [.call (.resolve "I") (alg [] [] [] [.call (.resolve "I") (alg [] [] [] [.resolve "x"])])])
#guard obs case_identityTwice__le == "ok raw=L[] n=1"

-- identityTwice__l7: I(a) = a \n x = [7] \n I(I(x))
def case_identityTwice__l7 : Expr :=
  .block (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"]), privateProp "x" (alg [] [] [] [(.listLiteral [(.num 7)])])] [.call (.resolve "I") (alg [] [] [] [.call (.resolve "I") (alg [] [] [] [.resolve "x"])])])
#guard obs case_identityTwice__l7 == "ok raw=L[7] n=1"

-- identityTwice__l12: I(a) = a \n x = [1, 2] \n I(I(x))
def case_identityTwice__l12 : Expr :=
  .block (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"]), privateProp "x" (alg [] [] [] [(.listLiteral [(.num 1), (.num 2)])])] [.call (.resolve "I") (alg [] [] [] [.call (.resolve "I") (alg [] [] [] [.resolve "x"])])])
#guard obs case_identityTwice__l12 == "ok raw=L[1, 2] n=1"

-- identityTwice__l12_3: I(a) = a \n x = [[1, 2], 3] \n I(I(x))
def case_identityTwice__l12_3 : Expr :=
  .block (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"]), privateProp "x" (alg [] [] [] [(.listLiteral [(.listLiteral [(.num 1), (.num 2)]), (.num 3)])])] [.call (.resolve "I") (alg [] [] [] [.call (.resolve "I") (alg [] [] [] [.resolve "x"])])])
#guard obs case_identityTwice__l12_3 == "ok raw=L[L[1, 2], 3] n=1"

-- identityTwice__lle: I(a) = a \n x = [[]] \n I(I(x))
def case_identityTwice__lle : Expr :=
  .block (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"]), privateProp "x" (alg [] [] [] [(.listLiteral [(.listLiteral [])])])] [.call (.resolve "I") (alg [] [] [] [.call (.resolve "I") (alg [] [] [] [.resolve "x"])])])
#guard obs case_identityTwice__lle == "ok raw=L[L[]] n=1"

-- identityTwice__l_e: I(a) = a \n x = [()] \n I(I(x))
def case_identityTwice__l_e : Expr :=
  .block (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"]), privateProp "x" (alg [] [] [] [(.listLiteral [(.emptySequence 0)])])] [.call (.resolve "I") (alg [] [] [] [.call (.resolve "I") (alg [] [] [] [.resolve "x"])])])
#guard obs case_identityTwice__l_e == "ok raw=L[S[]] n=1"

-- identityTwice__l_p12: I(a) = a \n x = [(1, 2)] \n I(I(x))
def case_identityTwice__l_p12 : Expr :=
  .block (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"]), privateProp "x" (alg [] [] [] [(.listLiteral [(.block (alg [] [] [] [(.num 1), (.num 2)]))])])] [.call (.resolve "I") (alg [] [] [] [.call (.resolve "I") (alg [] [] [] [.resolve "x"])])])
#guard obs case_identityTwice__l_p12 == "ok raw=L[S[1, 2]] n=1"

-- identityTwice__p_l12: I(a) = a \n x = ([1, 2], 3) \n I(I(x))
def case_identityTwice__p_l12 : Expr :=
  .block (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"]), privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.listLiteral [(.num 1), (.num 2)]), (.num 3)]))])] [.call (.resolve "I") (alg [] [] [] [.call (.resolve "I") (alg [] [] [] [.resolve "x"])])])
#guard obs case_identityTwice__p_l12 == "ok raw=S[L[1, 2], 3] n=1"

-- identityTwice__pl1: I(a) = a \n x = ([1]) \n I(I(x))
def case_identityTwice__pl1 : Expr :=
  .block (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"]), privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.listLiteral [(.num 1)])]))])] [.call (.resolve "I") (alg [] [] [] [.call (.resolve "I") (alg [] [] [] [.resolve "x"])])])
#guard obs case_identityTwice__pl1 == "ok raw=L[1] n=1"

-- propChain__e: P = () \n Q = P \n Q
def case_propChain__e : Expr :=
  .block (alg [] [] [privateProp "P" (alg [] [] [] [(.emptySequence 0)]), privateProp "Q" (alg [] [] [] [.resolve "P"])] [.resolve "Q"])
#guard obs case_propChain__e == "ok raw=S[] n=1"

-- propChain__n0: P = 0 \n Q = P \n Q
def case_propChain__n0 : Expr :=
  .block (alg [] [] [privateProp "P" (alg [] [] [] [(.num 0)]), privateProp "Q" (alg [] [] [] [.resolve "P"])] [.resolve "Q"])
#guard obs case_propChain__n0 == "ok raw=0 n=1"

-- propChain__n1: P = 1 \n Q = P \n Q
def case_propChain__n1 : Expr :=
  .block (alg [] [] [privateProp "P" (alg [] [] [] [(.num 1)]), privateProp "Q" (alg [] [] [] [.resolve "P"])] [.resolve "Q"])
#guard obs case_propChain__n1 == "ok raw=1 n=1"

-- propChain__p1: P = (1) \n Q = P \n Q
def case_propChain__p1 : Expr :=
  .block (alg [] [] [privateProp "P" (alg [] [] [] [(.block (alg [] [] [] [(.num 1)]))]), privateProp "Q" (alg [] [] [] [.resolve "P"])] [.resolve "Q"])
#guard obs case_propChain__p1 == "ok raw=1 n=1"

-- propChain__p12: P = (1, 2) \n Q = P \n Q
def case_propChain__p12 : Expr :=
  .block (alg [] [] [privateProp "P" (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)]))]), privateProp "Q" (alg [] [] [] [.resolve "P"])] [.resolve "Q"])
#guard obs case_propChain__p12 == "ok raw=S[1, 2] n=1"

-- propChain__p123: P = (1, 2, 3) \n Q = P \n Q
def case_propChain__p123 : Expr :=
  .block (alg [] [] [privateProp "P" (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2), (.num 3)]))]), privateProp "Q" (alg [] [] [] [.resolve "P"])] [.resolve "Q"])
#guard obs case_propChain__p123 == "ok raw=S[1, 2, 3] n=1"

-- propChain__pee: P = ((), ()) \n Q = P \n Q
def case_propChain__pee : Expr :=
  .block (alg [] [] [privateProp "P" (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.emptySequence 0)]))]), privateProp "Q" (alg [] [] [] [.resolve "P"])] [.resolve "Q"])
#guard obs case_propChain__pee == "ok raw=S[S[], S[]] n=1"

-- propChain__pe1: P = ((), 1) \n Q = P \n Q
def case_propChain__pe1 : Expr :=
  .block (alg [] [] [privateProp "P" (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.num 1)]))]), privateProp "Q" (alg [] [] [] [.resolve "P"])] [.resolve "Q"])
#guard obs case_propChain__pe1 == "ok raw=S[S[], 1] n=1"

-- propChain__p1e: P = (1, ()) \n Q = P \n Q
def case_propChain__p1e : Expr :=
  .block (alg [] [] [privateProp "P" (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.emptySequence 0)]))]), privateProp "Q" (alg [] [] [] [.resolve "P"])] [.resolve "Q"])
#guard obs case_propChain__p1e == "ok raw=S[1, S[]] n=1"

-- propChain__p12_3: P = ((1, 2), 3) \n Q = P \n Q
def case_propChain__p12_3 : Expr :=
  .block (alg [] [] [privateProp "P" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.num 3)]))]), privateProp "Q" (alg [] [] [] [.resolve "P"])] [.resolve "Q"])
#guard obs case_propChain__p12_3 == "ok raw=S[S[1, 2], 3] n=1"

-- propChain__p12_34: P = ((1, 2), (3, 4)) \n Q = P \n Q
def case_propChain__p12_34 : Expr :=
  .block (alg [] [] [privateProp "P" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.block (alg [] [] [] [(.num 3), (.num 4)]))]))]), privateProp "Q" (alg [] [] [] [.resolve "P"])] [.resolve "Q"])
#guard obs case_propChain__p12_34 == "ok raw=S[S[1, 2], S[3, 4]] n=1"

-- propChain__pe_12: P = ((), (1, 2)) \n Q = P \n Q
def case_propChain__pe_12 : Expr :=
  .block (alg [] [] [privateProp "P" (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.block (alg [] [] [] [(.num 1), (.num 2)]))]))]), privateProp "Q" (alg [] [] [] [.resolve "P"])] [.resolve "Q"])
#guard obs case_propChain__pe_12 == "ok raw=S[S[], S[1, 2]] n=1"

-- propChain__ppe1_2: P = (((), 1), 2) \n Q = P \n Q
def case_propChain__ppe1_2 : Expr :=
  .block (alg [] [] [privateProp "P" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.num 1)])), (.num 2)]))]), privateProp "Q" (alg [] [] [] [.resolve "P"])] [.resolve "Q"])
#guard obs case_propChain__ppe1_2 == "ok raw=S[S[S[], 1], 2] n=1"

-- propChain__p12_e: P = ((1, 2), ()) \n Q = P \n Q
def case_propChain__p12_e : Expr :=
  .block (alg [] [] [privateProp "P" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.emptySequence 0)]))]), privateProp "Q" (alg [] [] [] [.resolve "P"])] [.resolve "Q"])
#guard obs case_propChain__p12_e == "ok raw=S[S[1, 2], S[]] n=1"

-- propChain__ppe: P = (()) \n Q = P \n Q
def case_propChain__ppe : Expr :=
  .block (alg [] [] [privateProp "P" (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0)]))]), privateProp "Q" (alg [] [] [] [.resolve "P"])] [.resolve "Q"])
#guard obs case_propChain__ppe == "ok raw=S[] n=1"

-- propChain__pp1: P = ((1)) \n Q = P \n Q
def case_propChain__pp1 : Expr :=
  .block (alg [] [] [privateProp "P" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1)]))]))]), privateProp "Q" (alg [] [] [] [.resolve "P"])] [.resolve "Q"])
#guard obs case_propChain__pp1 == "ok raw=1 n=1"

-- propChain__ppp12: P = (((1, 2))) \n Q = P \n Q
def case_propChain__ppp12 : Expr :=
  .block (alg [] [] [privateProp "P" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)]))]))]))]), privateProp "Q" (alg [] [] [] [.resolve "P"])] [.resolve "Q"])
#guard obs case_propChain__ppp12 == "ok raw=S[1, 2] n=1"

-- propChain__le: P = [] \n Q = P \n Q
def case_propChain__le : Expr :=
  .block (alg [] [] [privateProp "P" (alg [] [] [] [(.listLiteral [])]), privateProp "Q" (alg [] [] [] [.resolve "P"])] [.resolve "Q"])
#guard obs case_propChain__le == "ok raw=L[] n=1"

-- propChain__l7: P = [7] \n Q = P \n Q
def case_propChain__l7 : Expr :=
  .block (alg [] [] [privateProp "P" (alg [] [] [] [(.listLiteral [(.num 7)])]), privateProp "Q" (alg [] [] [] [.resolve "P"])] [.resolve "Q"])
#guard obs case_propChain__l7 == "ok raw=L[7] n=1"

-- propChain__l12: P = [1, 2] \n Q = P \n Q
def case_propChain__l12 : Expr :=
  .block (alg [] [] [privateProp "P" (alg [] [] [] [(.listLiteral [(.num 1), (.num 2)])]), privateProp "Q" (alg [] [] [] [.resolve "P"])] [.resolve "Q"])
#guard obs case_propChain__l12 == "ok raw=L[1, 2] n=1"

-- propChain__l12_3: P = [[1, 2], 3] \n Q = P \n Q
def case_propChain__l12_3 : Expr :=
  .block (alg [] [] [privateProp "P" (alg [] [] [] [(.listLiteral [(.listLiteral [(.num 1), (.num 2)]), (.num 3)])]), privateProp "Q" (alg [] [] [] [.resolve "P"])] [.resolve "Q"])
#guard obs case_propChain__l12_3 == "ok raw=L[L[1, 2], 3] n=1"

-- propChain__lle: P = [[]] \n Q = P \n Q
def case_propChain__lle : Expr :=
  .block (alg [] [] [privateProp "P" (alg [] [] [] [(.listLiteral [(.listLiteral [])])]), privateProp "Q" (alg [] [] [] [.resolve "P"])] [.resolve "Q"])
#guard obs case_propChain__lle == "ok raw=L[L[]] n=1"

-- propChain__l_e: P = [()] \n Q = P \n Q
def case_propChain__l_e : Expr :=
  .block (alg [] [] [privateProp "P" (alg [] [] [] [(.listLiteral [(.emptySequence 0)])]), privateProp "Q" (alg [] [] [] [.resolve "P"])] [.resolve "Q"])
#guard obs case_propChain__l_e == "ok raw=L[S[]] n=1"

-- propChain__l_p12: P = [(1, 2)] \n Q = P \n Q
def case_propChain__l_p12 : Expr :=
  .block (alg [] [] [privateProp "P" (alg [] [] [] [(.listLiteral [(.block (alg [] [] [] [(.num 1), (.num 2)]))])]), privateProp "Q" (alg [] [] [] [.resolve "P"])] [.resolve "Q"])
#guard obs case_propChain__l_p12 == "ok raw=L[S[1, 2]] n=1"

-- propChain__p_l12: P = ([1, 2], 3) \n Q = P \n Q
def case_propChain__p_l12 : Expr :=
  .block (alg [] [] [privateProp "P" (alg [] [] [] [(.block (alg [] [] [] [(.listLiteral [(.num 1), (.num 2)]), (.num 3)]))]), privateProp "Q" (alg [] [] [] [.resolve "P"])] [.resolve "Q"])
#guard obs case_propChain__p_l12 == "ok raw=S[L[1, 2], 3] n=1"

-- propChain__pl1: P = ([1]) \n Q = P \n Q
def case_propChain__pl1 : Expr :=
  .block (alg [] [] [privateProp "P" (alg [] [] [] [(.block (alg [] [] [] [(.listLiteral [(.num 1)])]))]), privateProp "Q" (alg [] [] [] [.resolve "P"])] [.resolve "Q"])
#guard obs case_propChain__pl1 == "ok raw=L[1] n=1"

-- take1__e: take((), 1)
def case_take1__e : Expr :=
  .block (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.emptySequence 0), .num 1])])
#guard obs case_take1__e == "ok raw=L[] n=1"

-- take1__n0: take(0, 1)
def case_take1__n0 : Expr :=
  .block (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.num 0), .num 1])])
#guard obs case_take1__n0 == "ok raw=L[0] n=1"

-- take1__n1: take(1, 1)
def case_take1__n1 : Expr :=
  .block (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.num 1), .num 1])])
#guard obs case_take1__n1 == "ok raw=L[1] n=1"

-- take1__p1: take((1), 1)
def case_take1__p1 : Expr :=
  .block (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.block (alg [] [] [] [(.num 1)])), .num 1])])
#guard obs case_take1__p1 == "ok raw=L[1] n=1"

-- take1__p12: take((1, 2), 1)
def case_take1__p12 : Expr :=
  .block (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), .num 1])])
#guard obs case_take1__p12 == "ok raw=L[1] n=1"

-- take1__p123: take((1, 2, 3), 1)
def case_take1__p123 : Expr :=
  .block (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2), (.num 3)])), .num 1])])
#guard obs case_take1__p123 == "ok raw=L[1] n=1"

-- take1__pee: take(((), ()), 1)
def case_take1__pee : Expr :=
  .block (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.emptySequence 0)])), .num 1])])
#guard obs case_take1__pee == "ok raw=L[S[]] n=1"

-- take1__pe1: take(((), 1), 1)
def case_take1__pe1 : Expr :=
  .block (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.num 1)])), .num 1])])
#guard obs case_take1__pe1 == "ok raw=L[S[]] n=1"

-- take1__p1e: take((1, ()), 1)
def case_take1__p1e : Expr :=
  .block (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.emptySequence 0)])), .num 1])])
#guard obs case_take1__p1e == "ok raw=L[1] n=1"

-- take1__p12_3: take(((1, 2), 3), 1)
def case_take1__p12_3 : Expr :=
  .block (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.num 3)])), .num 1])])
#guard obs case_take1__p12_3 == "ok raw=L[S[1, 2]] n=1"

-- take1__p12_34: take(((1, 2), (3, 4)), 1)
def case_take1__p12_34 : Expr :=
  .block (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.block (alg [] [] [] [(.num 3), (.num 4)]))])), .num 1])])
#guard obs case_take1__p12_34 == "ok raw=L[S[1, 2]] n=1"

-- take1__pe_12: take(((), (1, 2)), 1)
def case_take1__pe_12 : Expr :=
  .block (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.block (alg [] [] [] [(.num 1), (.num 2)]))])), .num 1])])
#guard obs case_take1__pe_12 == "ok raw=L[S[]] n=1"

-- take1__ppe1_2: take((((), 1), 2), 1)
def case_take1__ppe1_2 : Expr :=
  .block (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.num 1)])), (.num 2)])), .num 1])])
#guard obs case_take1__ppe1_2 == "ok raw=L[S[S[], 1]] n=1"

-- take1__p12_e: take(((1, 2), ()), 1)
def case_take1__p12_e : Expr :=
  .block (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.emptySequence 0)])), .num 1])])
#guard obs case_take1__p12_e == "ok raw=L[S[1, 2]] n=1"

-- take1__ppe: take((()), 1)
def case_take1__ppe : Expr :=
  .block (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0)])), .num 1])])
#guard obs case_take1__ppe == "ok raw=L[] n=1"

-- take1__pp1: take(((1)), 1)
def case_take1__pp1 : Expr :=
  .block (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1)]))])), .num 1])])
#guard obs case_take1__pp1 == "ok raw=L[1] n=1"

-- take1__ppp12: take((((1, 2))), 1)
def case_take1__ppp12 : Expr :=
  .block (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)]))]))])), .num 1])])
#guard obs case_take1__ppp12 == "ok raw=L[1] n=1"

-- take1__le: take([], 1)
def case_take1__le : Expr :=
  .block (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.listLiteral []), .num 1])])
#guard obs case_take1__le == "ok raw=L[] n=1"

-- take1__l7: take([7], 1)
def case_take1__l7 : Expr :=
  .block (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.listLiteral [(.num 7)]), .num 1])])
#guard obs case_take1__l7 == "ok raw=L[7] n=1"

-- take1__l12: take([1, 2], 1)
def case_take1__l12 : Expr :=
  .block (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.listLiteral [(.num 1), (.num 2)]), .num 1])])
#guard obs case_take1__l12 == "ok raw=L[1] n=1"

-- take1__l12_3: take([[1, 2], 3], 1)
def case_take1__l12_3 : Expr :=
  .block (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.listLiteral [(.listLiteral [(.num 1), (.num 2)]), (.num 3)]), .num 1])])
#guard obs case_take1__l12_3 == "ok raw=L[L[1, 2]] n=1"

-- take1__lle: take([[]], 1)
def case_take1__lle : Expr :=
  .block (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.listLiteral [(.listLiteral [])]), .num 1])])
#guard obs case_take1__lle == "ok raw=L[L[]] n=1"

-- take1__l_e: take([()], 1)
def case_take1__l_e : Expr :=
  .block (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.listLiteral [(.emptySequence 0)]), .num 1])])
#guard obs case_take1__l_e == "ok raw=L[S[]] n=1"

-- take1__l_p12: take([(1, 2)], 1)
def case_take1__l_p12 : Expr :=
  .block (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.listLiteral [(.block (alg [] [] [] [(.num 1), (.num 2)]))]), .num 1])])
#guard obs case_take1__l_p12 == "ok raw=L[S[1, 2]] n=1"

-- take1__p_l12: take(([1, 2], 3), 1)
def case_take1__p_l12 : Expr :=
  .block (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.block (alg [] [] [] [(.listLiteral [(.num 1), (.num 2)]), (.num 3)])), .num 1])])
#guard obs case_take1__p_l12 == "ok raw=L[L[1, 2]] n=1"

-- take1__pl1: take(([1]), 1)
def case_take1__pl1 : Expr :=
  .block (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.block (alg [] [] [] [(.listLiteral [(.num 1)])])), .num 1])])
#guard obs case_take1__pl1 == "ok raw=L[1] n=1"

-- take9__e: take((), 9)
def case_take9__e : Expr :=
  .block (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.emptySequence 0), .num 9])])
#guard obs case_take9__e == "ok raw=L[] n=1"

-- take9__n0: take(0, 9)
def case_take9__n0 : Expr :=
  .block (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.num 0), .num 9])])
#guard obs case_take9__n0 == "ok raw=L[0] n=1"

-- take9__n1: take(1, 9)
def case_take9__n1 : Expr :=
  .block (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.num 1), .num 9])])
#guard obs case_take9__n1 == "ok raw=L[1] n=1"

-- take9__p1: take((1), 9)
def case_take9__p1 : Expr :=
  .block (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.block (alg [] [] [] [(.num 1)])), .num 9])])
#guard obs case_take9__p1 == "ok raw=L[1] n=1"

-- take9__p12: take((1, 2), 9)
def case_take9__p12 : Expr :=
  .block (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), .num 9])])
#guard obs case_take9__p12 == "ok raw=L[1, 2] n=1"

-- take9__p123: take((1, 2, 3), 9)
def case_take9__p123 : Expr :=
  .block (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2), (.num 3)])), .num 9])])
#guard obs case_take9__p123 == "ok raw=L[1, 2, 3] n=1"

-- take9__pee: take(((), ()), 9)
def case_take9__pee : Expr :=
  .block (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.emptySequence 0)])), .num 9])])
#guard obs case_take9__pee == "ok raw=L[S[], S[]] n=1"

-- take9__pe1: take(((), 1), 9)
def case_take9__pe1 : Expr :=
  .block (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.num 1)])), .num 9])])
#guard obs case_take9__pe1 == "ok raw=L[S[], 1] n=1"

-- take9__p1e: take((1, ()), 9)
def case_take9__p1e : Expr :=
  .block (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.emptySequence 0)])), .num 9])])
#guard obs case_take9__p1e == "ok raw=L[1, S[]] n=1"

-- take9__p12_3: take(((1, 2), 3), 9)
def case_take9__p12_3 : Expr :=
  .block (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.num 3)])), .num 9])])
#guard obs case_take9__p12_3 == "ok raw=L[S[1, 2], 3] n=1"

-- take9__p12_34: take(((1, 2), (3, 4)), 9)
def case_take9__p12_34 : Expr :=
  .block (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.block (alg [] [] [] [(.num 3), (.num 4)]))])), .num 9])])
#guard obs case_take9__p12_34 == "ok raw=L[S[1, 2], S[3, 4]] n=1"

-- take9__pe_12: take(((), (1, 2)), 9)
def case_take9__pe_12 : Expr :=
  .block (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.block (alg [] [] [] [(.num 1), (.num 2)]))])), .num 9])])
#guard obs case_take9__pe_12 == "ok raw=L[S[], S[1, 2]] n=1"

-- take9__ppe1_2: take((((), 1), 2), 9)
def case_take9__ppe1_2 : Expr :=
  .block (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.num 1)])), (.num 2)])), .num 9])])
#guard obs case_take9__ppe1_2 == "ok raw=L[S[S[], 1], 2] n=1"

-- take9__p12_e: take(((1, 2), ()), 9)
def case_take9__p12_e : Expr :=
  .block (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.emptySequence 0)])), .num 9])])
#guard obs case_take9__p12_e == "ok raw=L[S[1, 2], S[]] n=1"

-- take9__ppe: take((()), 9)
def case_take9__ppe : Expr :=
  .block (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0)])), .num 9])])
#guard obs case_take9__ppe == "ok raw=L[] n=1"

-- take9__pp1: take(((1)), 9)
def case_take9__pp1 : Expr :=
  .block (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1)]))])), .num 9])])
#guard obs case_take9__pp1 == "ok raw=L[1] n=1"

-- take9__ppp12: take((((1, 2))), 9)
def case_take9__ppp12 : Expr :=
  .block (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)]))]))])), .num 9])])
#guard obs case_take9__ppp12 == "ok raw=L[1, 2] n=1"

-- take9__le: take([], 9)
def case_take9__le : Expr :=
  .block (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.listLiteral []), .num 9])])
#guard obs case_take9__le == "ok raw=L[] n=1"

-- take9__l7: take([7], 9)
def case_take9__l7 : Expr :=
  .block (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.listLiteral [(.num 7)]), .num 9])])
#guard obs case_take9__l7 == "ok raw=L[7] n=1"

-- take9__l12: take([1, 2], 9)
def case_take9__l12 : Expr :=
  .block (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.listLiteral [(.num 1), (.num 2)]), .num 9])])
#guard obs case_take9__l12 == "ok raw=L[1, 2] n=1"

-- take9__l12_3: take([[1, 2], 3], 9)
def case_take9__l12_3 : Expr :=
  .block (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.listLiteral [(.listLiteral [(.num 1), (.num 2)]), (.num 3)]), .num 9])])
#guard obs case_take9__l12_3 == "ok raw=L[L[1, 2], 3] n=1"

-- take9__lle: take([[]], 9)
def case_take9__lle : Expr :=
  .block (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.listLiteral [(.listLiteral [])]), .num 9])])
#guard obs case_take9__lle == "ok raw=L[L[]] n=1"

-- take9__l_e: take([()], 9)
def case_take9__l_e : Expr :=
  .block (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.listLiteral [(.emptySequence 0)]), .num 9])])
#guard obs case_take9__l_e == "ok raw=L[S[]] n=1"

-- take9__l_p12: take([(1, 2)], 9)
def case_take9__l_p12 : Expr :=
  .block (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.listLiteral [(.block (alg [] [] [] [(.num 1), (.num 2)]))]), .num 9])])
#guard obs case_take9__l_p12 == "ok raw=L[S[1, 2]] n=1"

-- take9__p_l12: take(([1, 2], 3), 9)
def case_take9__p_l12 : Expr :=
  .block (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.block (alg [] [] [] [(.listLiteral [(.num 1), (.num 2)]), (.num 3)])), .num 9])])
#guard obs case_take9__p_l12 == "ok raw=L[L[1, 2], 3] n=1"

-- take9__pl1: take(([1]), 9)
def case_take9__pl1 : Expr :=
  .block (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.block (alg [] [] [] [(.listLiteral [(.num 1)])])), .num 9])])
#guard obs case_take9__pl1 == "ok raw=L[1] n=1"

-- skip1__e: skip((), 1)
def case_skip1__e : Expr :=
  .block (alg [] [] [] [.call (.resolve "skip") (alg [] [] [] [(.emptySequence 0), .num 1])])
#guard obs case_skip1__e == "ok raw=L[] n=1"

-- skip1__n0: skip(0, 1)
def case_skip1__n0 : Expr :=
  .block (alg [] [] [] [.call (.resolve "skip") (alg [] [] [] [(.num 0), .num 1])])
#guard obs case_skip1__n0 == "ok raw=L[] n=1"

-- skip1__n1: skip(1, 1)
def case_skip1__n1 : Expr :=
  .block (alg [] [] [] [.call (.resolve "skip") (alg [] [] [] [(.num 1), .num 1])])
#guard obs case_skip1__n1 == "ok raw=L[] n=1"

-- skip1__p1: skip((1), 1)
def case_skip1__p1 : Expr :=
  .block (alg [] [] [] [.call (.resolve "skip") (alg [] [] [] [(.block (alg [] [] [] [(.num 1)])), .num 1])])
#guard obs case_skip1__p1 == "ok raw=L[] n=1"

-- skip1__p12: skip((1, 2), 1)
def case_skip1__p12 : Expr :=
  .block (alg [] [] [] [.call (.resolve "skip") (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), .num 1])])
#guard obs case_skip1__p12 == "ok raw=L[2] n=1"

-- skip1__p123: skip((1, 2, 3), 1)
def case_skip1__p123 : Expr :=
  .block (alg [] [] [] [.call (.resolve "skip") (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2), (.num 3)])), .num 1])])
#guard obs case_skip1__p123 == "ok raw=L[2, 3] n=1"

-- skip1__pee: skip(((), ()), 1)
def case_skip1__pee : Expr :=
  .block (alg [] [] [] [.call (.resolve "skip") (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.emptySequence 0)])), .num 1])])
#guard obs case_skip1__pee == "ok raw=L[S[]] n=1"

-- skip1__pe1: skip(((), 1), 1)
def case_skip1__pe1 : Expr :=
  .block (alg [] [] [] [.call (.resolve "skip") (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.num 1)])), .num 1])])
#guard obs case_skip1__pe1 == "ok raw=L[1] n=1"

-- skip1__p1e: skip((1, ()), 1)
def case_skip1__p1e : Expr :=
  .block (alg [] [] [] [.call (.resolve "skip") (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.emptySequence 0)])), .num 1])])
#guard obs case_skip1__p1e == "ok raw=L[S[]] n=1"

-- skip1__p12_3: skip(((1, 2), 3), 1)
def case_skip1__p12_3 : Expr :=
  .block (alg [] [] [] [.call (.resolve "skip") (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.num 3)])), .num 1])])
#guard obs case_skip1__p12_3 == "ok raw=L[3] n=1"

-- skip1__p12_34: skip(((1, 2), (3, 4)), 1)
def case_skip1__p12_34 : Expr :=
  .block (alg [] [] [] [.call (.resolve "skip") (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.block (alg [] [] [] [(.num 3), (.num 4)]))])), .num 1])])
#guard obs case_skip1__p12_34 == "ok raw=L[S[3, 4]] n=1"

-- skip1__pe_12: skip(((), (1, 2)), 1)
def case_skip1__pe_12 : Expr :=
  .block (alg [] [] [] [.call (.resolve "skip") (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.block (alg [] [] [] [(.num 1), (.num 2)]))])), .num 1])])
#guard obs case_skip1__pe_12 == "ok raw=L[S[1, 2]] n=1"

-- skip1__ppe1_2: skip((((), 1), 2), 1)
def case_skip1__ppe1_2 : Expr :=
  .block (alg [] [] [] [.call (.resolve "skip") (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.num 1)])), (.num 2)])), .num 1])])
#guard obs case_skip1__ppe1_2 == "ok raw=L[2] n=1"

-- skip1__p12_e: skip(((1, 2), ()), 1)
def case_skip1__p12_e : Expr :=
  .block (alg [] [] [] [.call (.resolve "skip") (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.emptySequence 0)])), .num 1])])
#guard obs case_skip1__p12_e == "ok raw=L[S[]] n=1"

-- skip1__ppe: skip((()), 1)
def case_skip1__ppe : Expr :=
  .block (alg [] [] [] [.call (.resolve "skip") (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0)])), .num 1])])
#guard obs case_skip1__ppe == "ok raw=L[] n=1"

-- skip1__pp1: skip(((1)), 1)
def case_skip1__pp1 : Expr :=
  .block (alg [] [] [] [.call (.resolve "skip") (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1)]))])), .num 1])])
#guard obs case_skip1__pp1 == "ok raw=L[] n=1"

-- skip1__ppp12: skip((((1, 2))), 1)
def case_skip1__ppp12 : Expr :=
  .block (alg [] [] [] [.call (.resolve "skip") (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)]))]))])), .num 1])])
#guard obs case_skip1__ppp12 == "ok raw=L[2] n=1"

-- skip1__le: skip([], 1)
def case_skip1__le : Expr :=
  .block (alg [] [] [] [.call (.resolve "skip") (alg [] [] [] [(.listLiteral []), .num 1])])
#guard obs case_skip1__le == "ok raw=L[] n=1"

-- skip1__l7: skip([7], 1)
def case_skip1__l7 : Expr :=
  .block (alg [] [] [] [.call (.resolve "skip") (alg [] [] [] [(.listLiteral [(.num 7)]), .num 1])])
#guard obs case_skip1__l7 == "ok raw=L[] n=1"

-- skip1__l12: skip([1, 2], 1)
def case_skip1__l12 : Expr :=
  .block (alg [] [] [] [.call (.resolve "skip") (alg [] [] [] [(.listLiteral [(.num 1), (.num 2)]), .num 1])])
#guard obs case_skip1__l12 == "ok raw=L[2] n=1"

-- skip1__l12_3: skip([[1, 2], 3], 1)
def case_skip1__l12_3 : Expr :=
  .block (alg [] [] [] [.call (.resolve "skip") (alg [] [] [] [(.listLiteral [(.listLiteral [(.num 1), (.num 2)]), (.num 3)]), .num 1])])
#guard obs case_skip1__l12_3 == "ok raw=L[3] n=1"

-- skip1__lle: skip([[]], 1)
def case_skip1__lle : Expr :=
  .block (alg [] [] [] [.call (.resolve "skip") (alg [] [] [] [(.listLiteral [(.listLiteral [])]), .num 1])])
#guard obs case_skip1__lle == "ok raw=L[] n=1"

-- skip1__l_e: skip([()], 1)
def case_skip1__l_e : Expr :=
  .block (alg [] [] [] [.call (.resolve "skip") (alg [] [] [] [(.listLiteral [(.emptySequence 0)]), .num 1])])
#guard obs case_skip1__l_e == "ok raw=L[] n=1"

-- skip1__l_p12: skip([(1, 2)], 1)
def case_skip1__l_p12 : Expr :=
  .block (alg [] [] [] [.call (.resolve "skip") (alg [] [] [] [(.listLiteral [(.block (alg [] [] [] [(.num 1), (.num 2)]))]), .num 1])])
#guard obs case_skip1__l_p12 == "ok raw=L[] n=1"

-- skip1__p_l12: skip(([1, 2], 3), 1)
def case_skip1__p_l12 : Expr :=
  .block (alg [] [] [] [.call (.resolve "skip") (alg [] [] [] [(.block (alg [] [] [] [(.listLiteral [(.num 1), (.num 2)]), (.num 3)])), .num 1])])
#guard obs case_skip1__p_l12 == "ok raw=L[3] n=1"

-- skip1__pl1: skip(([1]), 1)
def case_skip1__pl1 : Expr :=
  .block (alg [] [] [] [.call (.resolve "skip") (alg [] [] [] [(.block (alg [] [] [] [(.listLiteral [(.num 1)])])), .num 1])])
#guard obs case_skip1__pl1 == "ok raw=L[] n=1"

-- distinct__e: distinct(())
def case_distinct__e : Expr :=
  .block (alg [] [] [] [.call (.resolve "distinct") (alg [] [] [] [(.emptySequence 0)])])
#guard obs case_distinct__e == "ok raw=L[] n=1"

-- distinct__n0: distinct(0)
def case_distinct__n0 : Expr :=
  .block (alg [] [] [] [.call (.resolve "distinct") (alg [] [] [] [(.num 0)])])
#guard obs case_distinct__n0 == "ok raw=L[0] n=1"

-- distinct__n1: distinct(1)
def case_distinct__n1 : Expr :=
  .block (alg [] [] [] [.call (.resolve "distinct") (alg [] [] [] [(.num 1)])])
#guard obs case_distinct__n1 == "ok raw=L[1] n=1"

-- distinct__p1: distinct((1))
def case_distinct__p1 : Expr :=
  .block (alg [] [] [] [.call (.resolve "distinct") (alg [] [] [] [(.block (alg [] [] [] [(.num 1)]))])])
#guard obs case_distinct__p1 == "ok raw=L[1] n=1"

-- distinct__p12: distinct((1, 2))
def case_distinct__p12 : Expr :=
  .block (alg [] [] [] [.call (.resolve "distinct") (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)]))])])
#guard obs case_distinct__p12 == "ok raw=L[1, 2] n=1"

-- distinct__p123: distinct((1, 2, 3))
def case_distinct__p123 : Expr :=
  .block (alg [] [] [] [.call (.resolve "distinct") (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2), (.num 3)]))])])
#guard obs case_distinct__p123 == "ok raw=L[1, 2, 3] n=1"

-- distinct__pee: distinct(((), ()))
def case_distinct__pee : Expr :=
  .block (alg [] [] [] [.call (.resolve "distinct") (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.emptySequence 0)]))])])
#guard obs case_distinct__pee == "ok raw=L[S[]] n=1"

-- distinct__pe1: distinct(((), 1))
def case_distinct__pe1 : Expr :=
  .block (alg [] [] [] [.call (.resolve "distinct") (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.num 1)]))])])
#guard obs case_distinct__pe1 == "ok raw=L[S[], 1] n=1"

-- distinct__p1e: distinct((1, ()))
def case_distinct__p1e : Expr :=
  .block (alg [] [] [] [.call (.resolve "distinct") (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.emptySequence 0)]))])])
#guard obs case_distinct__p1e == "ok raw=L[1, S[]] n=1"

-- distinct__p12_3: distinct(((1, 2), 3))
def case_distinct__p12_3 : Expr :=
  .block (alg [] [] [] [.call (.resolve "distinct") (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.num 3)]))])])
#guard obs case_distinct__p12_3 == "ok raw=L[S[1, 2], 3] n=1"

-- distinct__p12_34: distinct(((1, 2), (3, 4)))
def case_distinct__p12_34 : Expr :=
  .block (alg [] [] [] [.call (.resolve "distinct") (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.block (alg [] [] [] [(.num 3), (.num 4)]))]))])])
#guard obs case_distinct__p12_34 == "ok raw=L[S[1, 2], S[3, 4]] n=1"

-- distinct__pe_12: distinct(((), (1, 2)))
def case_distinct__pe_12 : Expr :=
  .block (alg [] [] [] [.call (.resolve "distinct") (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.block (alg [] [] [] [(.num 1), (.num 2)]))]))])])
#guard obs case_distinct__pe_12 == "ok raw=L[S[], S[1, 2]] n=1"

-- distinct__ppe1_2: distinct((((), 1), 2))
def case_distinct__ppe1_2 : Expr :=
  .block (alg [] [] [] [.call (.resolve "distinct") (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.num 1)])), (.num 2)]))])])
#guard obs case_distinct__ppe1_2 == "ok raw=L[S[S[], 1], 2] n=1"

-- distinct__p12_e: distinct(((1, 2), ()))
def case_distinct__p12_e : Expr :=
  .block (alg [] [] [] [.call (.resolve "distinct") (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.emptySequence 0)]))])])
#guard obs case_distinct__p12_e == "ok raw=L[S[1, 2], S[]] n=1"

-- distinct__ppe: distinct((()))
def case_distinct__ppe : Expr :=
  .block (alg [] [] [] [.call (.resolve "distinct") (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0)]))])])
#guard obs case_distinct__ppe == "ok raw=L[] n=1"

-- distinct__pp1: distinct(((1)))
def case_distinct__pp1 : Expr :=
  .block (alg [] [] [] [.call (.resolve "distinct") (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1)]))]))])])
#guard obs case_distinct__pp1 == "ok raw=L[1] n=1"

-- distinct__ppp12: distinct((((1, 2))))
def case_distinct__ppp12 : Expr :=
  .block (alg [] [] [] [.call (.resolve "distinct") (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)]))]))]))])])
#guard obs case_distinct__ppp12 == "ok raw=L[1, 2] n=1"

-- distinct__le: distinct([])
def case_distinct__le : Expr :=
  .block (alg [] [] [] [.call (.resolve "distinct") (alg [] [] [] [(.listLiteral [])])])
#guard obs case_distinct__le == "ok raw=L[] n=1"

-- distinct__l7: distinct([7])
def case_distinct__l7 : Expr :=
  .block (alg [] [] [] [.call (.resolve "distinct") (alg [] [] [] [(.listLiteral [(.num 7)])])])
#guard obs case_distinct__l7 == "ok raw=L[7] n=1"

-- distinct__l12: distinct([1, 2])
def case_distinct__l12 : Expr :=
  .block (alg [] [] [] [.call (.resolve "distinct") (alg [] [] [] [(.listLiteral [(.num 1), (.num 2)])])])
#guard obs case_distinct__l12 == "ok raw=L[1, 2] n=1"

-- distinct__l12_3: distinct([[1, 2], 3])
def case_distinct__l12_3 : Expr :=
  .block (alg [] [] [] [.call (.resolve "distinct") (alg [] [] [] [(.listLiteral [(.listLiteral [(.num 1), (.num 2)]), (.num 3)])])])
#guard obs case_distinct__l12_3 == "ok raw=L[L[1, 2], 3] n=1"

-- distinct__lle: distinct([[]])
def case_distinct__lle : Expr :=
  .block (alg [] [] [] [.call (.resolve "distinct") (alg [] [] [] [(.listLiteral [(.listLiteral [])])])])
#guard obs case_distinct__lle == "ok raw=L[L[]] n=1"

-- distinct__l_e: distinct([()])
def case_distinct__l_e : Expr :=
  .block (alg [] [] [] [.call (.resolve "distinct") (alg [] [] [] [(.listLiteral [(.emptySequence 0)])])])
#guard obs case_distinct__l_e == "ok raw=L[S[]] n=1"

-- distinct__l_p12: distinct([(1, 2)])
def case_distinct__l_p12 : Expr :=
  .block (alg [] [] [] [.call (.resolve "distinct") (alg [] [] [] [(.listLiteral [(.block (alg [] [] [] [(.num 1), (.num 2)]))])])])
#guard obs case_distinct__l_p12 == "ok raw=L[S[1, 2]] n=1"

-- distinct__p_l12: distinct(([1, 2], 3))
def case_distinct__p_l12 : Expr :=
  .block (alg [] [] [] [.call (.resolve "distinct") (alg [] [] [] [(.block (alg [] [] [] [(.listLiteral [(.num 1), (.num 2)]), (.num 3)]))])])
#guard obs case_distinct__p_l12 == "ok raw=L[L[1, 2], 3] n=1"

-- distinct__pl1: distinct(([1]))
def case_distinct__pl1 : Expr :=
  .block (alg [] [] [] [.call (.resolve "distinct") (alg [] [] [] [(.block (alg [] [] [] [(.listLiteral [(.num 1)])]))])])
#guard obs case_distinct__pl1 == "ok raw=L[1] n=1"

-- order__e: order(())
def case_order__e : Expr :=
  .block (alg [] [] [] [.call (.resolve "order") (alg [] [] [] [(.emptySequence 0)])])
#guard obs case_order__e == "ok raw=L[] n=1"

-- order__n0: order(0)
def case_order__n0 : Expr :=
  .block (alg [] [] [] [.call (.resolve "order") (alg [] [] [] [(.num 0)])])
#guard obs case_order__n0 == "ok raw=L[0] n=1"

-- order__n1: order(1)
def case_order__n1 : Expr :=
  .block (alg [] [] [] [.call (.resolve "order") (alg [] [] [] [(.num 1)])])
#guard obs case_order__n1 == "ok raw=L[1] n=1"

-- order__p1: order((1))
def case_order__p1 : Expr :=
  .block (alg [] [] [] [.call (.resolve "order") (alg [] [] [] [(.block (alg [] [] [] [(.num 1)]))])])
#guard obs case_order__p1 == "ok raw=L[1] n=1"

-- order__p12: order((1, 2))
def case_order__p12 : Expr :=
  .block (alg [] [] [] [.call (.resolve "order") (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)]))])])
#guard obs case_order__p12 == "ok raw=L[1, 2] n=1"

-- order__p123: order((1, 2, 3))
def case_order__p123 : Expr :=
  .block (alg [] [] [] [.call (.resolve "order") (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2), (.num 3)]))])])
#guard obs case_order__p123 == "ok raw=L[1, 2, 3] n=1"

-- order__pee: order(((), ()))
def case_order__pee : Expr :=
  .block (alg [] [] [] [.call (.resolve "order") (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.emptySequence 0)]))])])
#guard obs case_order__pee == "err arity"

-- order__pe1: order(((), 1))
def case_order__pe1 : Expr :=
  .block (alg [] [] [] [.call (.resolve "order") (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.num 1)]))])])
#guard obs case_order__pe1 == "err arity"

-- order__p1e: order((1, ()))
def case_order__p1e : Expr :=
  .block (alg [] [] [] [.call (.resolve "order") (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.emptySequence 0)]))])])
#guard obs case_order__p1e == "err arity"

-- order__p12_3: order(((1, 2), 3))
def case_order__p12_3 : Expr :=
  .block (alg [] [] [] [.call (.resolve "order") (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.num 3)]))])])
#guard obs case_order__p12_3 == "err arity"

-- order__p12_34: order(((1, 2), (3, 4)))
def case_order__p12_34 : Expr :=
  .block (alg [] [] [] [.call (.resolve "order") (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.block (alg [] [] [] [(.num 3), (.num 4)]))]))])])
#guard obs case_order__p12_34 == "err arity"

-- order__pe_12: order(((), (1, 2)))
def case_order__pe_12 : Expr :=
  .block (alg [] [] [] [.call (.resolve "order") (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.block (alg [] [] [] [(.num 1), (.num 2)]))]))])])
#guard obs case_order__pe_12 == "err arity"

-- order__ppe1_2: order((((), 1), 2))
def case_order__ppe1_2 : Expr :=
  .block (alg [] [] [] [.call (.resolve "order") (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.num 1)])), (.num 2)]))])])
#guard obs case_order__ppe1_2 == "err arity"

-- order__p12_e: order(((1, 2), ()))
def case_order__p12_e : Expr :=
  .block (alg [] [] [] [.call (.resolve "order") (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.emptySequence 0)]))])])
#guard obs case_order__p12_e == "err arity"

-- order__ppe: order((()))
def case_order__ppe : Expr :=
  .block (alg [] [] [] [.call (.resolve "order") (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0)]))])])
#guard obs case_order__ppe == "ok raw=L[] n=1"

-- order__pp1: order(((1)))
def case_order__pp1 : Expr :=
  .block (alg [] [] [] [.call (.resolve "order") (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1)]))]))])])
#guard obs case_order__pp1 == "ok raw=L[1] n=1"

-- order__ppp12: order((((1, 2))))
def case_order__ppp12 : Expr :=
  .block (alg [] [] [] [.call (.resolve "order") (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)]))]))]))])])
#guard obs case_order__ppp12 == "ok raw=L[1, 2] n=1"

-- order__le: order([])
def case_order__le : Expr :=
  .block (alg [] [] [] [.call (.resolve "order") (alg [] [] [] [(.listLiteral [])])])
#guard obs case_order__le == "ok raw=L[] n=1"

-- order__l7: order([7])
def case_order__l7 : Expr :=
  .block (alg [] [] [] [.call (.resolve "order") (alg [] [] [] [(.listLiteral [(.num 7)])])])
#guard obs case_order__l7 == "ok raw=L[7] n=1"

-- order__l12: order([1, 2])
def case_order__l12 : Expr :=
  .block (alg [] [] [] [.call (.resolve "order") (alg [] [] [] [(.listLiteral [(.num 1), (.num 2)])])])
#guard obs case_order__l12 == "ok raw=L[1, 2] n=1"

-- order__l12_3: order([[1, 2], 3])
def case_order__l12_3 : Expr :=
  .block (alg [] [] [] [.call (.resolve "order") (alg [] [] [] [(.listLiteral [(.listLiteral [(.num 1), (.num 2)]), (.num 3)])])])
#guard obs case_order__l12_3 == "err arity"

-- order__lle: order([[]])
def case_order__lle : Expr :=
  .block (alg [] [] [] [.call (.resolve "order") (alg [] [] [] [(.listLiteral [(.listLiteral [])])])])
#guard obs case_order__lle == "err arity"

-- order__l_e: order([()])
def case_order__l_e : Expr :=
  .block (alg [] [] [] [.call (.resolve "order") (alg [] [] [] [(.listLiteral [(.emptySequence 0)])])])
#guard obs case_order__l_e == "err arity"

-- order__l_p12: order([(1, 2)])
def case_order__l_p12 : Expr :=
  .block (alg [] [] [] [.call (.resolve "order") (alg [] [] [] [(.listLiteral [(.block (alg [] [] [] [(.num 1), (.num 2)]))])])])
#guard obs case_order__l_p12 == "err arity"

-- order__p_l12: order(([1, 2], 3))
def case_order__p_l12 : Expr :=
  .block (alg [] [] [] [.call (.resolve "order") (alg [] [] [] [(.block (alg [] [] [] [(.listLiteral [(.num 1), (.num 2)]), (.num 3)]))])])
#guard obs case_order__p_l12 == "err arity"

-- order__pl1: order(([1]))
def case_order__pl1 : Expr :=
  .block (alg [] [] [] [.call (.resolve "order") (alg [] [] [] [(.block (alg [] [] [] [(.listLiteral [(.num 1)])]))])])
#guard obs case_order__pl1 == "ok raw=L[1] n=1"

-- mapId__e: M(a) = a \n map((), M)
def case_mapId__e : Expr :=
  .block (alg [] [] [privateProp "M" (alg ["a"] [] [] [.param "a"])] [.call (.resolve "map") (alg [] [] [] [(.emptySequence 0), .resolve "M"])])
#guard obs case_mapId__e == "ok raw=L[] n=1"

-- mapId__n0: M(a) = a \n map(0, M)
def case_mapId__n0 : Expr :=
  .block (alg [] [] [privateProp "M" (alg ["a"] [] [] [.param "a"])] [.call (.resolve "map") (alg [] [] [] [(.num 0), .resolve "M"])])
#guard obs case_mapId__n0 == "ok raw=L[0] n=1"

-- mapId__n1: M(a) = a \n map(1, M)
def case_mapId__n1 : Expr :=
  .block (alg [] [] [privateProp "M" (alg ["a"] [] [] [.param "a"])] [.call (.resolve "map") (alg [] [] [] [(.num 1), .resolve "M"])])
#guard obs case_mapId__n1 == "ok raw=L[1] n=1"

-- mapId__p1: M(a) = a \n map((1), M)
def case_mapId__p1 : Expr :=
  .block (alg [] [] [privateProp "M" (alg ["a"] [] [] [.param "a"])] [.call (.resolve "map") (alg [] [] [] [(.block (alg [] [] [] [(.num 1)])), .resolve "M"])])
#guard obs case_mapId__p1 == "ok raw=L[1] n=1"

-- mapId__p12: M(a) = a \n map((1, 2), M)
def case_mapId__p12 : Expr :=
  .block (alg [] [] [privateProp "M" (alg ["a"] [] [] [.param "a"])] [.call (.resolve "map") (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), .resolve "M"])])
#guard obs case_mapId__p12 == "ok raw=L[1, 2] n=1"

-- mapId__p123: M(a) = a \n map((1, 2, 3), M)
def case_mapId__p123 : Expr :=
  .block (alg [] [] [privateProp "M" (alg ["a"] [] [] [.param "a"])] [.call (.resolve "map") (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2), (.num 3)])), .resolve "M"])])
#guard obs case_mapId__p123 == "ok raw=L[1, 2, 3] n=1"

-- mapId__pee: M(a) = a \n map(((), ()), M)
def case_mapId__pee : Expr :=
  .block (alg [] [] [privateProp "M" (alg ["a"] [] [] [.param "a"])] [.call (.resolve "map") (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.emptySequence 0)])), .resolve "M"])])
#guard obs case_mapId__pee == "err arity"

-- mapId__pe1: M(a) = a \n map(((), 1), M)
def case_mapId__pe1 : Expr :=
  .block (alg [] [] [privateProp "M" (alg ["a"] [] [] [.param "a"])] [.call (.resolve "map") (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.num 1)])), .resolve "M"])])
#guard obs case_mapId__pe1 == "err arity"

-- mapId__p1e: M(a) = a \n map((1, ()), M)
def case_mapId__p1e : Expr :=
  .block (alg [] [] [privateProp "M" (alg ["a"] [] [] [.param "a"])] [.call (.resolve "map") (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.emptySequence 0)])), .resolve "M"])])
#guard obs case_mapId__p1e == "err arity"

-- mapId__p12_3: M(a) = a \n map(((1, 2), 3), M)
def case_mapId__p12_3 : Expr :=
  .block (alg [] [] [privateProp "M" (alg ["a"] [] [] [.param "a"])] [.call (.resolve "map") (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.num 3)])), .resolve "M"])])
#guard obs case_mapId__p12_3 == "err arity"

-- mapId__p12_34: M(a) = a \n map(((1, 2), (3, 4)), M)
def case_mapId__p12_34 : Expr :=
  .block (alg [] [] [privateProp "M" (alg ["a"] [] [] [.param "a"])] [.call (.resolve "map") (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.block (alg [] [] [] [(.num 3), (.num 4)]))])), .resolve "M"])])
#guard obs case_mapId__p12_34 == "err arity"

-- mapId__pe_12: M(a) = a \n map(((), (1, 2)), M)
def case_mapId__pe_12 : Expr :=
  .block (alg [] [] [privateProp "M" (alg ["a"] [] [] [.param "a"])] [.call (.resolve "map") (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.block (alg [] [] [] [(.num 1), (.num 2)]))])), .resolve "M"])])
#guard obs case_mapId__pe_12 == "err arity"

-- mapId__ppe1_2: M(a) = a \n map((((), 1), 2), M)
def case_mapId__ppe1_2 : Expr :=
  .block (alg [] [] [privateProp "M" (alg ["a"] [] [] [.param "a"])] [.call (.resolve "map") (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.num 1)])), (.num 2)])), .resolve "M"])])
#guard obs case_mapId__ppe1_2 == "err arity"

-- mapId__p12_e: M(a) = a \n map(((1, 2), ()), M)
def case_mapId__p12_e : Expr :=
  .block (alg [] [] [privateProp "M" (alg ["a"] [] [] [.param "a"])] [.call (.resolve "map") (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.emptySequence 0)])), .resolve "M"])])
#guard obs case_mapId__p12_e == "err arity"

-- mapId__ppe: M(a) = a \n map((()), M)
def case_mapId__ppe : Expr :=
  .block (alg [] [] [privateProp "M" (alg ["a"] [] [] [.param "a"])] [.call (.resolve "map") (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0)])), .resolve "M"])])
#guard obs case_mapId__ppe == "ok raw=L[] n=1"

-- mapId__pp1: M(a) = a \n map(((1)), M)
def case_mapId__pp1 : Expr :=
  .block (alg [] [] [privateProp "M" (alg ["a"] [] [] [.param "a"])] [.call (.resolve "map") (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1)]))])), .resolve "M"])])
#guard obs case_mapId__pp1 == "ok raw=L[1] n=1"

-- mapId__ppp12: M(a) = a \n map((((1, 2))), M)
def case_mapId__ppp12 : Expr :=
  .block (alg [] [] [privateProp "M" (alg ["a"] [] [] [.param "a"])] [.call (.resolve "map") (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)]))]))])), .resolve "M"])])
#guard obs case_mapId__ppp12 == "ok raw=L[1, 2] n=1"

-- mapId__le: M(a) = a \n map([], M)
def case_mapId__le : Expr :=
  .block (alg [] [] [privateProp "M" (alg ["a"] [] [] [.param "a"])] [.call (.resolve "map") (alg [] [] [] [(.listLiteral []), .resolve "M"])])
#guard obs case_mapId__le == "ok raw=L[] n=1"

-- mapId__l7: M(a) = a \n map([7], M)
def case_mapId__l7 : Expr :=
  .block (alg [] [] [privateProp "M" (alg ["a"] [] [] [.param "a"])] [.call (.resolve "map") (alg [] [] [] [(.listLiteral [(.num 7)]), .resolve "M"])])
#guard obs case_mapId__l7 == "ok raw=L[7] n=1"

-- mapId__l12: M(a) = a \n map([1, 2], M)
def case_mapId__l12 : Expr :=
  .block (alg [] [] [privateProp "M" (alg ["a"] [] [] [.param "a"])] [.call (.resolve "map") (alg [] [] [] [(.listLiteral [(.num 1), (.num 2)]), .resolve "M"])])
#guard obs case_mapId__l12 == "ok raw=L[1, 2] n=1"

-- mapId__l12_3: M(a) = a \n map([[1, 2], 3], M)
def case_mapId__l12_3 : Expr :=
  .block (alg [] [] [privateProp "M" (alg ["a"] [] [] [.param "a"])] [.call (.resolve "map") (alg [] [] [] [(.listLiteral [(.listLiteral [(.num 1), (.num 2)]), (.num 3)]), .resolve "M"])])
#guard obs case_mapId__l12_3 == "ok raw=L[L[1, 2], 3] n=1"

-- mapId__lle: M(a) = a \n map([[]], M)
def case_mapId__lle : Expr :=
  .block (alg [] [] [privateProp "M" (alg ["a"] [] [] [.param "a"])] [.call (.resolve "map") (alg [] [] [] [(.listLiteral [(.listLiteral [])]), .resolve "M"])])
#guard obs case_mapId__lle == "ok raw=L[L[]] n=1"

-- mapId__l_e: M(a) = a \n map([()], M)
def case_mapId__l_e : Expr :=
  .block (alg [] [] [privateProp "M" (alg ["a"] [] [] [.param "a"])] [.call (.resolve "map") (alg [] [] [] [(.listLiteral [(.emptySequence 0)]), .resolve "M"])])
#guard obs case_mapId__l_e == "err arity"

-- mapId__l_p12: M(a) = a \n map([(1, 2)], M)
def case_mapId__l_p12 : Expr :=
  .block (alg [] [] [privateProp "M" (alg ["a"] [] [] [.param "a"])] [.call (.resolve "map") (alg [] [] [] [(.listLiteral [(.block (alg [] [] [] [(.num 1), (.num 2)]))]), .resolve "M"])])
#guard obs case_mapId__l_p12 == "err arity"

-- mapId__p_l12: M(a) = a \n map(([1, 2], 3), M)
def case_mapId__p_l12 : Expr :=
  .block (alg [] [] [privateProp "M" (alg ["a"] [] [] [.param "a"])] [.call (.resolve "map") (alg [] [] [] [(.block (alg [] [] [] [(.listLiteral [(.num 1), (.num 2)]), (.num 3)])), .resolve "M"])])
#guard obs case_mapId__p_l12 == "ok raw=L[L[1, 2], 3] n=1"

-- mapId__pl1: M(a) = a \n map(([1]), M)
def case_mapId__pl1 : Expr :=
  .block (alg [] [] [privateProp "M" (alg ["a"] [] [] [.param "a"])] [.call (.resolve "map") (alg [] [] [] [(.block (alg [] [] [] [(.listLiteral [(.num 1)])])), .resolve "M"])])
#guard obs case_mapId__pl1 == "ok raw=L[1] n=1"

-- filterKeep__e: T(a) = 1 \n filter((), T)
def case_filterKeep__e : Expr :=
  .block (alg [] [] [privateProp "T" (alg ["a"] [] [] [.num 1])] [.call (.resolve "filter") (alg [] [] [] [(.emptySequence 0), .resolve "T"])])
#guard obs case_filterKeep__e == "ok raw=L[] n=1"

-- filterKeep__n0: T(a) = 1 \n filter(0, T)
def case_filterKeep__n0 : Expr :=
  .block (alg [] [] [privateProp "T" (alg ["a"] [] [] [.num 1])] [.call (.resolve "filter") (alg [] [] [] [(.num 0), .resolve "T"])])
#guard obs case_filterKeep__n0 == "ok raw=L[0] n=1"

-- filterKeep__n1: T(a) = 1 \n filter(1, T)
def case_filterKeep__n1 : Expr :=
  .block (alg [] [] [privateProp "T" (alg ["a"] [] [] [.num 1])] [.call (.resolve "filter") (alg [] [] [] [(.num 1), .resolve "T"])])
#guard obs case_filterKeep__n1 == "ok raw=L[1] n=1"

-- filterKeep__p1: T(a) = 1 \n filter((1), T)
def case_filterKeep__p1 : Expr :=
  .block (alg [] [] [privateProp "T" (alg ["a"] [] [] [.num 1])] [.call (.resolve "filter") (alg [] [] [] [(.block (alg [] [] [] [(.num 1)])), .resolve "T"])])
#guard obs case_filterKeep__p1 == "ok raw=L[1] n=1"

-- filterKeep__p12: T(a) = 1 \n filter((1, 2), T)
def case_filterKeep__p12 : Expr :=
  .block (alg [] [] [privateProp "T" (alg ["a"] [] [] [.num 1])] [.call (.resolve "filter") (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), .resolve "T"])])
#guard obs case_filterKeep__p12 == "ok raw=L[1, 2] n=1"

-- filterKeep__p123: T(a) = 1 \n filter((1, 2, 3), T)
def case_filterKeep__p123 : Expr :=
  .block (alg [] [] [privateProp "T" (alg ["a"] [] [] [.num 1])] [.call (.resolve "filter") (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2), (.num 3)])), .resolve "T"])])
#guard obs case_filterKeep__p123 == "ok raw=L[1, 2, 3] n=1"

-- filterKeep__pee: T(a) = 1 \n filter(((), ()), T)
def case_filterKeep__pee : Expr :=
  .block (alg [] [] [privateProp "T" (alg ["a"] [] [] [.num 1])] [.call (.resolve "filter") (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.emptySequence 0)])), .resolve "T"])])
#guard obs case_filterKeep__pee == "ok raw=L[S[], S[]] n=1"

-- filterKeep__pe1: T(a) = 1 \n filter(((), 1), T)
def case_filterKeep__pe1 : Expr :=
  .block (alg [] [] [privateProp "T" (alg ["a"] [] [] [.num 1])] [.call (.resolve "filter") (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.num 1)])), .resolve "T"])])
#guard obs case_filterKeep__pe1 == "ok raw=L[S[], 1] n=1"

-- filterKeep__p1e: T(a) = 1 \n filter((1, ()), T)
def case_filterKeep__p1e : Expr :=
  .block (alg [] [] [privateProp "T" (alg ["a"] [] [] [.num 1])] [.call (.resolve "filter") (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.emptySequence 0)])), .resolve "T"])])
#guard obs case_filterKeep__p1e == "ok raw=L[1, S[]] n=1"

-- filterKeep__p12_3: T(a) = 1 \n filter(((1, 2), 3), T)
def case_filterKeep__p12_3 : Expr :=
  .block (alg [] [] [privateProp "T" (alg ["a"] [] [] [.num 1])] [.call (.resolve "filter") (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.num 3)])), .resolve "T"])])
#guard obs case_filterKeep__p12_3 == "ok raw=L[S[1, 2], 3] n=1"

-- filterKeep__p12_34: T(a) = 1 \n filter(((1, 2), (3, 4)), T)
def case_filterKeep__p12_34 : Expr :=
  .block (alg [] [] [privateProp "T" (alg ["a"] [] [] [.num 1])] [.call (.resolve "filter") (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.block (alg [] [] [] [(.num 3), (.num 4)]))])), .resolve "T"])])
#guard obs case_filterKeep__p12_34 == "ok raw=L[S[1, 2], S[3, 4]] n=1"

-- filterKeep__pe_12: T(a) = 1 \n filter(((), (1, 2)), T)
def case_filterKeep__pe_12 : Expr :=
  .block (alg [] [] [privateProp "T" (alg ["a"] [] [] [.num 1])] [.call (.resolve "filter") (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.block (alg [] [] [] [(.num 1), (.num 2)]))])), .resolve "T"])])
#guard obs case_filterKeep__pe_12 == "ok raw=L[S[], S[1, 2]] n=1"

-- filterKeep__ppe1_2: T(a) = 1 \n filter((((), 1), 2), T)
def case_filterKeep__ppe1_2 : Expr :=
  .block (alg [] [] [privateProp "T" (alg ["a"] [] [] [.num 1])] [.call (.resolve "filter") (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.num 1)])), (.num 2)])), .resolve "T"])])
#guard obs case_filterKeep__ppe1_2 == "ok raw=L[S[S[], 1], 2] n=1"

-- filterKeep__p12_e: T(a) = 1 \n filter(((1, 2), ()), T)
def case_filterKeep__p12_e : Expr :=
  .block (alg [] [] [privateProp "T" (alg ["a"] [] [] [.num 1])] [.call (.resolve "filter") (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.emptySequence 0)])), .resolve "T"])])
#guard obs case_filterKeep__p12_e == "ok raw=L[S[1, 2], S[]] n=1"

-- filterKeep__ppe: T(a) = 1 \n filter((()), T)
def case_filterKeep__ppe : Expr :=
  .block (alg [] [] [privateProp "T" (alg ["a"] [] [] [.num 1])] [.call (.resolve "filter") (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0)])), .resolve "T"])])
#guard obs case_filterKeep__ppe == "ok raw=L[] n=1"

-- filterKeep__pp1: T(a) = 1 \n filter(((1)), T)
def case_filterKeep__pp1 : Expr :=
  .block (alg [] [] [privateProp "T" (alg ["a"] [] [] [.num 1])] [.call (.resolve "filter") (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1)]))])), .resolve "T"])])
#guard obs case_filterKeep__pp1 == "ok raw=L[1] n=1"

-- filterKeep__ppp12: T(a) = 1 \n filter((((1, 2))), T)
def case_filterKeep__ppp12 : Expr :=
  .block (alg [] [] [privateProp "T" (alg ["a"] [] [] [.num 1])] [.call (.resolve "filter") (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)]))]))])), .resolve "T"])])
#guard obs case_filterKeep__ppp12 == "ok raw=L[1, 2] n=1"

-- filterKeep__le: T(a) = 1 \n filter([], T)
def case_filterKeep__le : Expr :=
  .block (alg [] [] [privateProp "T" (alg ["a"] [] [] [.num 1])] [.call (.resolve "filter") (alg [] [] [] [(.listLiteral []), .resolve "T"])])
#guard obs case_filterKeep__le == "ok raw=L[] n=1"

-- filterKeep__l7: T(a) = 1 \n filter([7], T)
def case_filterKeep__l7 : Expr :=
  .block (alg [] [] [privateProp "T" (alg ["a"] [] [] [.num 1])] [.call (.resolve "filter") (alg [] [] [] [(.listLiteral [(.num 7)]), .resolve "T"])])
#guard obs case_filterKeep__l7 == "ok raw=L[7] n=1"

-- filterKeep__l12: T(a) = 1 \n filter([1, 2], T)
def case_filterKeep__l12 : Expr :=
  .block (alg [] [] [privateProp "T" (alg ["a"] [] [] [.num 1])] [.call (.resolve "filter") (alg [] [] [] [(.listLiteral [(.num 1), (.num 2)]), .resolve "T"])])
#guard obs case_filterKeep__l12 == "ok raw=L[1, 2] n=1"

-- filterKeep__l12_3: T(a) = 1 \n filter([[1, 2], 3], T)
def case_filterKeep__l12_3 : Expr :=
  .block (alg [] [] [privateProp "T" (alg ["a"] [] [] [.num 1])] [.call (.resolve "filter") (alg [] [] [] [(.listLiteral [(.listLiteral [(.num 1), (.num 2)]), (.num 3)]), .resolve "T"])])
#guard obs case_filterKeep__l12_3 == "ok raw=L[L[1, 2], 3] n=1"

-- filterKeep__lle: T(a) = 1 \n filter([[]], T)
def case_filterKeep__lle : Expr :=
  .block (alg [] [] [privateProp "T" (alg ["a"] [] [] [.num 1])] [.call (.resolve "filter") (alg [] [] [] [(.listLiteral [(.listLiteral [])]), .resolve "T"])])
#guard obs case_filterKeep__lle == "ok raw=L[L[]] n=1"

-- filterKeep__l_e: T(a) = 1 \n filter([()], T)
def case_filterKeep__l_e : Expr :=
  .block (alg [] [] [privateProp "T" (alg ["a"] [] [] [.num 1])] [.call (.resolve "filter") (alg [] [] [] [(.listLiteral [(.emptySequence 0)]), .resolve "T"])])
#guard obs case_filterKeep__l_e == "ok raw=L[S[]] n=1"

-- filterKeep__l_p12: T(a) = 1 \n filter([(1, 2)], T)
def case_filterKeep__l_p12 : Expr :=
  .block (alg [] [] [privateProp "T" (alg ["a"] [] [] [.num 1])] [.call (.resolve "filter") (alg [] [] [] [(.listLiteral [(.block (alg [] [] [] [(.num 1), (.num 2)]))]), .resolve "T"])])
#guard obs case_filterKeep__l_p12 == "ok raw=L[S[1, 2]] n=1"

-- filterKeep__p_l12: T(a) = 1 \n filter(([1, 2], 3), T)
def case_filterKeep__p_l12 : Expr :=
  .block (alg [] [] [privateProp "T" (alg ["a"] [] [] [.num 1])] [.call (.resolve "filter") (alg [] [] [] [(.block (alg [] [] [] [(.listLiteral [(.num 1), (.num 2)]), (.num 3)])), .resolve "T"])])
#guard obs case_filterKeep__p_l12 == "ok raw=L[L[1, 2], 3] n=1"

-- filterKeep__pl1: T(a) = 1 \n filter(([1]), T)
def case_filterKeep__pl1 : Expr :=
  .block (alg [] [] [privateProp "T" (alg ["a"] [] [] [.num 1])] [.call (.resolve "filter") (alg [] [] [] [(.block (alg [] [] [] [(.listLiteral [(.num 1)])])), .resolve "T"])])
#guard obs case_filterKeep__pl1 == "ok raw=L[1] n=1"

-- atoms__e: atoms(())
def case_atoms__e : Expr :=
  .block (alg [] [] [] [.call (.resolve "atoms") (alg [] [] [] [(.emptySequence 0)])])
#guard obs case_atoms__e == "ok raw=L[] n=1"

-- atoms__n0: atoms(0)
def case_atoms__n0 : Expr :=
  .block (alg [] [] [] [.call (.resolve "atoms") (alg [] [] [] [(.num 0)])])
#guard obs case_atoms__n0 == "ok raw=L[0] n=1"

-- atoms__n1: atoms(1)
def case_atoms__n1 : Expr :=
  .block (alg [] [] [] [.call (.resolve "atoms") (alg [] [] [] [(.num 1)])])
#guard obs case_atoms__n1 == "ok raw=L[1] n=1"

-- atoms__p1: atoms((1))
def case_atoms__p1 : Expr :=
  .block (alg [] [] [] [.call (.resolve "atoms") (alg [] [] [] [(.block (alg [] [] [] [(.num 1)]))])])
#guard obs case_atoms__p1 == "ok raw=L[1] n=1"

-- atoms__p12: atoms((1, 2))
def case_atoms__p12 : Expr :=
  .block (alg [] [] [] [.call (.resolve "atoms") (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)]))])])
#guard obs case_atoms__p12 == "ok raw=L[1, 2] n=1"

-- atoms__p123: atoms((1, 2, 3))
def case_atoms__p123 : Expr :=
  .block (alg [] [] [] [.call (.resolve "atoms") (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2), (.num 3)]))])])
#guard obs case_atoms__p123 == "ok raw=L[1, 2, 3] n=1"

-- atoms__pee: atoms(((), ()))
def case_atoms__pee : Expr :=
  .block (alg [] [] [] [.call (.resolve "atoms") (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.emptySequence 0)]))])])
#guard obs case_atoms__pee == "ok raw=L[] n=1"

-- atoms__pe1: atoms(((), 1))
def case_atoms__pe1 : Expr :=
  .block (alg [] [] [] [.call (.resolve "atoms") (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.num 1)]))])])
#guard obs case_atoms__pe1 == "ok raw=L[1] n=1"

-- atoms__p1e: atoms((1, ()))
def case_atoms__p1e : Expr :=
  .block (alg [] [] [] [.call (.resolve "atoms") (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.emptySequence 0)]))])])
#guard obs case_atoms__p1e == "ok raw=L[1] n=1"

-- atoms__p12_3: atoms(((1, 2), 3))
def case_atoms__p12_3 : Expr :=
  .block (alg [] [] [] [.call (.resolve "atoms") (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.num 3)]))])])
#guard obs case_atoms__p12_3 == "ok raw=L[1, 2, 3] n=1"

-- atoms__p12_34: atoms(((1, 2), (3, 4)))
def case_atoms__p12_34 : Expr :=
  .block (alg [] [] [] [.call (.resolve "atoms") (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.block (alg [] [] [] [(.num 3), (.num 4)]))]))])])
#guard obs case_atoms__p12_34 == "ok raw=L[1, 2, 3, 4] n=1"

-- atoms__pe_12: atoms(((), (1, 2)))
def case_atoms__pe_12 : Expr :=
  .block (alg [] [] [] [.call (.resolve "atoms") (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.block (alg [] [] [] [(.num 1), (.num 2)]))]))])])
#guard obs case_atoms__pe_12 == "ok raw=L[1, 2] n=1"

-- atoms__ppe1_2: atoms((((), 1), 2))
def case_atoms__ppe1_2 : Expr :=
  .block (alg [] [] [] [.call (.resolve "atoms") (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.num 1)])), (.num 2)]))])])
#guard obs case_atoms__ppe1_2 == "ok raw=L[1, 2] n=1"

-- atoms__p12_e: atoms(((1, 2), ()))
def case_atoms__p12_e : Expr :=
  .block (alg [] [] [] [.call (.resolve "atoms") (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.emptySequence 0)]))])])
#guard obs case_atoms__p12_e == "ok raw=L[1, 2] n=1"

-- atoms__ppe: atoms((()))
def case_atoms__ppe : Expr :=
  .block (alg [] [] [] [.call (.resolve "atoms") (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0)]))])])
#guard obs case_atoms__ppe == "ok raw=L[] n=1"

-- atoms__pp1: atoms(((1)))
def case_atoms__pp1 : Expr :=
  .block (alg [] [] [] [.call (.resolve "atoms") (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1)]))]))])])
#guard obs case_atoms__pp1 == "ok raw=L[1] n=1"

-- atoms__ppp12: atoms((((1, 2))))
def case_atoms__ppp12 : Expr :=
  .block (alg [] [] [] [.call (.resolve "atoms") (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)]))]))]))])])
#guard obs case_atoms__ppp12 == "ok raw=L[1, 2] n=1"

-- atoms__le: atoms([])
def case_atoms__le : Expr :=
  .block (alg [] [] [] [.call (.resolve "atoms") (alg [] [] [] [(.listLiteral [])])])
#guard obs case_atoms__le == "ok raw=L[] n=1"

-- atoms__l7: atoms([7])
def case_atoms__l7 : Expr :=
  .block (alg [] [] [] [.call (.resolve "atoms") (alg [] [] [] [(.listLiteral [(.num 7)])])])
#guard obs case_atoms__l7 == "ok raw=L[7] n=1"

-- atoms__l12: atoms([1, 2])
def case_atoms__l12 : Expr :=
  .block (alg [] [] [] [.call (.resolve "atoms") (alg [] [] [] [(.listLiteral [(.num 1), (.num 2)])])])
#guard obs case_atoms__l12 == "ok raw=L[1, 2] n=1"

-- atoms__l12_3: atoms([[1, 2], 3])
def case_atoms__l12_3 : Expr :=
  .block (alg [] [] [] [.call (.resolve "atoms") (alg [] [] [] [(.listLiteral [(.listLiteral [(.num 1), (.num 2)]), (.num 3)])])])
#guard obs case_atoms__l12_3 == "ok raw=L[1, 2, 3] n=1"

-- atoms__lle: atoms([[]])
def case_atoms__lle : Expr :=
  .block (alg [] [] [] [.call (.resolve "atoms") (alg [] [] [] [(.listLiteral [(.listLiteral [])])])])
#guard obs case_atoms__lle == "ok raw=L[] n=1"

-- atoms__l_e: atoms([()])
def case_atoms__l_e : Expr :=
  .block (alg [] [] [] [.call (.resolve "atoms") (alg [] [] [] [(.listLiteral [(.emptySequence 0)])])])
#guard obs case_atoms__l_e == "ok raw=L[] n=1"

-- atoms__l_p12: atoms([(1, 2)])
def case_atoms__l_p12 : Expr :=
  .block (alg [] [] [] [.call (.resolve "atoms") (alg [] [] [] [(.listLiteral [(.block (alg [] [] [] [(.num 1), (.num 2)]))])])])
#guard obs case_atoms__l_p12 == "ok raw=L[1, 2] n=1"

-- atoms__p_l12: atoms(([1, 2], 3))
def case_atoms__p_l12 : Expr :=
  .block (alg [] [] [] [.call (.resolve "atoms") (alg [] [] [] [(.block (alg [] [] [] [(.listLiteral [(.num 1), (.num 2)]), (.num 3)]))])])
#guard obs case_atoms__p_l12 == "ok raw=L[1, 2, 3] n=1"

-- atoms__pl1: atoms(([1]))
def case_atoms__pl1 : Expr :=
  .block (alg [] [] [] [.call (.resolve "atoms") (alg [] [] [] [(.block (alg [] [] [] [(.listLiteral [(.num 1)])]))])])
#guard obs case_atoms__pl1 == "ok raw=L[1] n=1"

-- takeCapture__e: x = take((), 1) \n x
def case_takeCapture__e : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.emptySequence 0), .num 1])])] [.resolve "x"])
#guard obs case_takeCapture__e == "ok raw=L[] n=1"

-- takeCapture__n0: x = take(0, 1) \n x
def case_takeCapture__n0 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.num 0), .num 1])])] [.resolve "x"])
#guard obs case_takeCapture__n0 == "ok raw=L[0] n=1"

-- takeCapture__n1: x = take(1, 1) \n x
def case_takeCapture__n1 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.num 1), .num 1])])] [.resolve "x"])
#guard obs case_takeCapture__n1 == "ok raw=L[1] n=1"

-- takeCapture__p1: x = take((1), 1) \n x
def case_takeCapture__p1 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.block (alg [] [] [] [(.num 1)])), .num 1])])] [.resolve "x"])
#guard obs case_takeCapture__p1 == "ok raw=L[1] n=1"

-- takeCapture__p12: x = take((1, 2), 1) \n x
def case_takeCapture__p12 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), .num 1])])] [.resolve "x"])
#guard obs case_takeCapture__p12 == "ok raw=L[1] n=1"

-- takeCapture__p123: x = take((1, 2, 3), 1) \n x
def case_takeCapture__p123 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2), (.num 3)])), .num 1])])] [.resolve "x"])
#guard obs case_takeCapture__p123 == "ok raw=L[1] n=1"

-- takeCapture__pee: x = take(((), ()), 1) \n x
def case_takeCapture__pee : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.emptySequence 0)])), .num 1])])] [.resolve "x"])
#guard obs case_takeCapture__pee == "ok raw=L[S[]] n=1"

-- takeCapture__pe1: x = take(((), 1), 1) \n x
def case_takeCapture__pe1 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.num 1)])), .num 1])])] [.resolve "x"])
#guard obs case_takeCapture__pe1 == "ok raw=L[S[]] n=1"

-- takeCapture__p1e: x = take((1, ()), 1) \n x
def case_takeCapture__p1e : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.emptySequence 0)])), .num 1])])] [.resolve "x"])
#guard obs case_takeCapture__p1e == "ok raw=L[1] n=1"

-- takeCapture__p12_3: x = take(((1, 2), 3), 1) \n x
def case_takeCapture__p12_3 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.num 3)])), .num 1])])] [.resolve "x"])
#guard obs case_takeCapture__p12_3 == "ok raw=L[S[1, 2]] n=1"

-- takeCapture__p12_34: x = take(((1, 2), (3, 4)), 1) \n x
def case_takeCapture__p12_34 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.block (alg [] [] [] [(.num 3), (.num 4)]))])), .num 1])])] [.resolve "x"])
#guard obs case_takeCapture__p12_34 == "ok raw=L[S[1, 2]] n=1"

-- takeCapture__pe_12: x = take(((), (1, 2)), 1) \n x
def case_takeCapture__pe_12 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.block (alg [] [] [] [(.num 1), (.num 2)]))])), .num 1])])] [.resolve "x"])
#guard obs case_takeCapture__pe_12 == "ok raw=L[S[]] n=1"

-- takeCapture__ppe1_2: x = take((((), 1), 2), 1) \n x
def case_takeCapture__ppe1_2 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.num 1)])), (.num 2)])), .num 1])])] [.resolve "x"])
#guard obs case_takeCapture__ppe1_2 == "ok raw=L[S[S[], 1]] n=1"

-- takeCapture__p12_e: x = take(((1, 2), ()), 1) \n x
def case_takeCapture__p12_e : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.emptySequence 0)])), .num 1])])] [.resolve "x"])
#guard obs case_takeCapture__p12_e == "ok raw=L[S[1, 2]] n=1"

-- takeCapture__ppe: x = take((()), 1) \n x
def case_takeCapture__ppe : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0)])), .num 1])])] [.resolve "x"])
#guard obs case_takeCapture__ppe == "ok raw=L[] n=1"

-- takeCapture__pp1: x = take(((1)), 1) \n x
def case_takeCapture__pp1 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1)]))])), .num 1])])] [.resolve "x"])
#guard obs case_takeCapture__pp1 == "ok raw=L[1] n=1"

-- takeCapture__ppp12: x = take((((1, 2))), 1) \n x
def case_takeCapture__ppp12 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)]))]))])), .num 1])])] [.resolve "x"])
#guard obs case_takeCapture__ppp12 == "ok raw=L[1] n=1"

-- takeCapture__le: x = take([], 1) \n x
def case_takeCapture__le : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.listLiteral []), .num 1])])] [.resolve "x"])
#guard obs case_takeCapture__le == "ok raw=L[] n=1"

-- takeCapture__l7: x = take([7], 1) \n x
def case_takeCapture__l7 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.listLiteral [(.num 7)]), .num 1])])] [.resolve "x"])
#guard obs case_takeCapture__l7 == "ok raw=L[7] n=1"

-- takeCapture__l12: x = take([1, 2], 1) \n x
def case_takeCapture__l12 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.listLiteral [(.num 1), (.num 2)]), .num 1])])] [.resolve "x"])
#guard obs case_takeCapture__l12 == "ok raw=L[1] n=1"

-- takeCapture__l12_3: x = take([[1, 2], 3], 1) \n x
def case_takeCapture__l12_3 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.listLiteral [(.listLiteral [(.num 1), (.num 2)]), (.num 3)]), .num 1])])] [.resolve "x"])
#guard obs case_takeCapture__l12_3 == "ok raw=L[L[1, 2]] n=1"

-- takeCapture__lle: x = take([[]], 1) \n x
def case_takeCapture__lle : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.listLiteral [(.listLiteral [])]), .num 1])])] [.resolve "x"])
#guard obs case_takeCapture__lle == "ok raw=L[L[]] n=1"

-- takeCapture__l_e: x = take([()], 1) \n x
def case_takeCapture__l_e : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.listLiteral [(.emptySequence 0)]), .num 1])])] [.resolve "x"])
#guard obs case_takeCapture__l_e == "ok raw=L[S[]] n=1"

-- takeCapture__l_p12: x = take([(1, 2)], 1) \n x
def case_takeCapture__l_p12 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.listLiteral [(.block (alg [] [] [] [(.num 1), (.num 2)]))]), .num 1])])] [.resolve "x"])
#guard obs case_takeCapture__l_p12 == "ok raw=L[S[1, 2]] n=1"

-- takeCapture__p_l12: x = take(([1, 2], 3), 1) \n x
def case_takeCapture__p_l12 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.block (alg [] [] [] [(.listLiteral [(.num 1), (.num 2)]), (.num 3)])), .num 1])])] [.resolve "x"])
#guard obs case_takeCapture__p_l12 == "ok raw=L[L[1, 2]] n=1"

-- takeCapture__pl1: x = take(([1]), 1) \n x
def case_takeCapture__pl1 : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.block (alg [] [] [] [(.listLiteral [(.num 1)])])), .num 1])])] [.resolve "x"])
#guard obs case_takeCapture__pl1 == "ok raw=L[1] n=1"

-- takeIdentity__e: I(a) = a \n I(take((), 1))
def case_takeIdentity__e : Expr :=
  .block (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"])] [.call (.resolve "I") (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.emptySequence 0), .num 1])])])
#guard obs case_takeIdentity__e == "ok raw=L[] n=1"

-- takeIdentity__n0: I(a) = a \n I(take(0, 1))
def case_takeIdentity__n0 : Expr :=
  .block (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"])] [.call (.resolve "I") (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.num 0), .num 1])])])
#guard obs case_takeIdentity__n0 == "ok raw=L[0] n=1"

-- takeIdentity__n1: I(a) = a \n I(take(1, 1))
def case_takeIdentity__n1 : Expr :=
  .block (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"])] [.call (.resolve "I") (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.num 1), .num 1])])])
#guard obs case_takeIdentity__n1 == "ok raw=L[1] n=1"

-- takeIdentity__p1: I(a) = a \n I(take((1), 1))
def case_takeIdentity__p1 : Expr :=
  .block (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"])] [.call (.resolve "I") (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.block (alg [] [] [] [(.num 1)])), .num 1])])])
#guard obs case_takeIdentity__p1 == "ok raw=L[1] n=1"

-- takeIdentity__p12: I(a) = a \n I(take((1, 2), 1))
def case_takeIdentity__p12 : Expr :=
  .block (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"])] [.call (.resolve "I") (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), .num 1])])])
#guard obs case_takeIdentity__p12 == "ok raw=L[1] n=1"

-- takeIdentity__p123: I(a) = a \n I(take((1, 2, 3), 1))
def case_takeIdentity__p123 : Expr :=
  .block (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"])] [.call (.resolve "I") (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2), (.num 3)])), .num 1])])])
#guard obs case_takeIdentity__p123 == "ok raw=L[1] n=1"

-- takeIdentity__pee: I(a) = a \n I(take(((), ()), 1))
def case_takeIdentity__pee : Expr :=
  .block (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"])] [.call (.resolve "I") (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.emptySequence 0)])), .num 1])])])
#guard obs case_takeIdentity__pee == "ok raw=L[S[]] n=1"

-- takeIdentity__pe1: I(a) = a \n I(take(((), 1), 1))
def case_takeIdentity__pe1 : Expr :=
  .block (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"])] [.call (.resolve "I") (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.num 1)])), .num 1])])])
#guard obs case_takeIdentity__pe1 == "ok raw=L[S[]] n=1"

-- takeIdentity__p1e: I(a) = a \n I(take((1, ()), 1))
def case_takeIdentity__p1e : Expr :=
  .block (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"])] [.call (.resolve "I") (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.emptySequence 0)])), .num 1])])])
#guard obs case_takeIdentity__p1e == "ok raw=L[1] n=1"

-- takeIdentity__p12_3: I(a) = a \n I(take(((1, 2), 3), 1))
def case_takeIdentity__p12_3 : Expr :=
  .block (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"])] [.call (.resolve "I") (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.num 3)])), .num 1])])])
#guard obs case_takeIdentity__p12_3 == "ok raw=L[S[1, 2]] n=1"

-- takeIdentity__p12_34: I(a) = a \n I(take(((1, 2), (3, 4)), 1))
def case_takeIdentity__p12_34 : Expr :=
  .block (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"])] [.call (.resolve "I") (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.block (alg [] [] [] [(.num 3), (.num 4)]))])), .num 1])])])
#guard obs case_takeIdentity__p12_34 == "ok raw=L[S[1, 2]] n=1"

-- takeIdentity__pe_12: I(a) = a \n I(take(((), (1, 2)), 1))
def case_takeIdentity__pe_12 : Expr :=
  .block (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"])] [.call (.resolve "I") (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.block (alg [] [] [] [(.num 1), (.num 2)]))])), .num 1])])])
#guard obs case_takeIdentity__pe_12 == "ok raw=L[S[]] n=1"

-- takeIdentity__ppe1_2: I(a) = a \n I(take((((), 1), 2), 1))
def case_takeIdentity__ppe1_2 : Expr :=
  .block (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"])] [.call (.resolve "I") (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.num 1)])), (.num 2)])), .num 1])])])
#guard obs case_takeIdentity__ppe1_2 == "ok raw=L[S[S[], 1]] n=1"

-- takeIdentity__p12_e: I(a) = a \n I(take(((1, 2), ()), 1))
def case_takeIdentity__p12_e : Expr :=
  .block (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"])] [.call (.resolve "I") (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.emptySequence 0)])), .num 1])])])
#guard obs case_takeIdentity__p12_e == "ok raw=L[S[1, 2]] n=1"

-- takeIdentity__ppe: I(a) = a \n I(take((()), 1))
def case_takeIdentity__ppe : Expr :=
  .block (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"])] [.call (.resolve "I") (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0)])), .num 1])])])
#guard obs case_takeIdentity__ppe == "ok raw=L[] n=1"

-- takeIdentity__pp1: I(a) = a \n I(take(((1)), 1))
def case_takeIdentity__pp1 : Expr :=
  .block (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"])] [.call (.resolve "I") (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1)]))])), .num 1])])])
#guard obs case_takeIdentity__pp1 == "ok raw=L[1] n=1"

-- takeIdentity__ppp12: I(a) = a \n I(take((((1, 2))), 1))
def case_takeIdentity__ppp12 : Expr :=
  .block (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"])] [.call (.resolve "I") (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)]))]))])), .num 1])])])
#guard obs case_takeIdentity__ppp12 == "ok raw=L[1] n=1"

-- takeIdentity__le: I(a) = a \n I(take([], 1))
def case_takeIdentity__le : Expr :=
  .block (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"])] [.call (.resolve "I") (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.listLiteral []), .num 1])])])
#guard obs case_takeIdentity__le == "ok raw=L[] n=1"

-- takeIdentity__l7: I(a) = a \n I(take([7], 1))
def case_takeIdentity__l7 : Expr :=
  .block (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"])] [.call (.resolve "I") (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.listLiteral [(.num 7)]), .num 1])])])
#guard obs case_takeIdentity__l7 == "ok raw=L[7] n=1"

-- takeIdentity__l12: I(a) = a \n I(take([1, 2], 1))
def case_takeIdentity__l12 : Expr :=
  .block (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"])] [.call (.resolve "I") (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.listLiteral [(.num 1), (.num 2)]), .num 1])])])
#guard obs case_takeIdentity__l12 == "ok raw=L[1] n=1"

-- takeIdentity__l12_3: I(a) = a \n I(take([[1, 2], 3], 1))
def case_takeIdentity__l12_3 : Expr :=
  .block (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"])] [.call (.resolve "I") (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.listLiteral [(.listLiteral [(.num 1), (.num 2)]), (.num 3)]), .num 1])])])
#guard obs case_takeIdentity__l12_3 == "ok raw=L[L[1, 2]] n=1"

-- takeIdentity__lle: I(a) = a \n I(take([[]], 1))
def case_takeIdentity__lle : Expr :=
  .block (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"])] [.call (.resolve "I") (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.listLiteral [(.listLiteral [])]), .num 1])])])
#guard obs case_takeIdentity__lle == "ok raw=L[L[]] n=1"

-- takeIdentity__l_e: I(a) = a \n I(take([()], 1))
def case_takeIdentity__l_e : Expr :=
  .block (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"])] [.call (.resolve "I") (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.listLiteral [(.emptySequence 0)]), .num 1])])])
#guard obs case_takeIdentity__l_e == "ok raw=L[S[]] n=1"

-- takeIdentity__l_p12: I(a) = a \n I(take([(1, 2)], 1))
def case_takeIdentity__l_p12 : Expr :=
  .block (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"])] [.call (.resolve "I") (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.listLiteral [(.block (alg [] [] [] [(.num 1), (.num 2)]))]), .num 1])])])
#guard obs case_takeIdentity__l_p12 == "ok raw=L[S[1, 2]] n=1"

-- takeIdentity__p_l12: I(a) = a \n I(take(([1, 2], 3), 1))
def case_takeIdentity__p_l12 : Expr :=
  .block (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"])] [.call (.resolve "I") (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.block (alg [] [] [] [(.listLiteral [(.num 1), (.num 2)]), (.num 3)])), .num 1])])])
#guard obs case_takeIdentity__p_l12 == "ok raw=L[L[1, 2]] n=1"

-- takeIdentity__pl1: I(a) = a \n I(take(([1]), 1))
def case_takeIdentity__pl1 : Expr :=
  .block (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"])] [.call (.resolve "I") (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.block (alg [] [] [] [(.listLiteral [(.num 1)])])), .num 1])])])
#guard obs case_takeIdentity__pl1 == "ok raw=L[1] n=1"

-- takeCount__e: count(take((), 1))
def case_takeCount__e : Expr :=
  .block (alg [] [] [] [.call (.resolve "count") (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.emptySequence 0), .num 1])])])
#guard obs case_takeCount__e == "ok raw=0 n=1"

-- takeCount__n0: count(take(0, 1))
def case_takeCount__n0 : Expr :=
  .block (alg [] [] [] [.call (.resolve "count") (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.num 0), .num 1])])])
#guard obs case_takeCount__n0 == "ok raw=1 n=1"

-- takeCount__n1: count(take(1, 1))
def case_takeCount__n1 : Expr :=
  .block (alg [] [] [] [.call (.resolve "count") (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.num 1), .num 1])])])
#guard obs case_takeCount__n1 == "ok raw=1 n=1"

-- takeCount__p1: count(take((1), 1))
def case_takeCount__p1 : Expr :=
  .block (alg [] [] [] [.call (.resolve "count") (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.block (alg [] [] [] [(.num 1)])), .num 1])])])
#guard obs case_takeCount__p1 == "ok raw=1 n=1"

-- takeCount__p12: count(take((1, 2), 1))
def case_takeCount__p12 : Expr :=
  .block (alg [] [] [] [.call (.resolve "count") (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), .num 1])])])
#guard obs case_takeCount__p12 == "ok raw=1 n=1"

-- takeCount__p123: count(take((1, 2, 3), 1))
def case_takeCount__p123 : Expr :=
  .block (alg [] [] [] [.call (.resolve "count") (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2), (.num 3)])), .num 1])])])
#guard obs case_takeCount__p123 == "ok raw=1 n=1"

-- takeCount__pee: count(take(((), ()), 1))
def case_takeCount__pee : Expr :=
  .block (alg [] [] [] [.call (.resolve "count") (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.emptySequence 0)])), .num 1])])])
#guard obs case_takeCount__pee == "ok raw=1 n=1"

-- takeCount__pe1: count(take(((), 1), 1))
def case_takeCount__pe1 : Expr :=
  .block (alg [] [] [] [.call (.resolve "count") (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.num 1)])), .num 1])])])
#guard obs case_takeCount__pe1 == "ok raw=1 n=1"

-- takeCount__p1e: count(take((1, ()), 1))
def case_takeCount__p1e : Expr :=
  .block (alg [] [] [] [.call (.resolve "count") (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.emptySequence 0)])), .num 1])])])
#guard obs case_takeCount__p1e == "ok raw=1 n=1"

-- takeCount__p12_3: count(take(((1, 2), 3), 1))
def case_takeCount__p12_3 : Expr :=
  .block (alg [] [] [] [.call (.resolve "count") (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.num 3)])), .num 1])])])
#guard obs case_takeCount__p12_3 == "ok raw=1 n=1"

-- takeCount__p12_34: count(take(((1, 2), (3, 4)), 1))
def case_takeCount__p12_34 : Expr :=
  .block (alg [] [] [] [.call (.resolve "count") (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.block (alg [] [] [] [(.num 3), (.num 4)]))])), .num 1])])])
#guard obs case_takeCount__p12_34 == "ok raw=1 n=1"

-- takeCount__pe_12: count(take(((), (1, 2)), 1))
def case_takeCount__pe_12 : Expr :=
  .block (alg [] [] [] [.call (.resolve "count") (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.block (alg [] [] [] [(.num 1), (.num 2)]))])), .num 1])])])
#guard obs case_takeCount__pe_12 == "ok raw=1 n=1"

-- takeCount__ppe1_2: count(take((((), 1), 2), 1))
def case_takeCount__ppe1_2 : Expr :=
  .block (alg [] [] [] [.call (.resolve "count") (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.num 1)])), (.num 2)])), .num 1])])])
#guard obs case_takeCount__ppe1_2 == "ok raw=1 n=1"

-- takeCount__p12_e: count(take(((1, 2), ()), 1))
def case_takeCount__p12_e : Expr :=
  .block (alg [] [] [] [.call (.resolve "count") (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.emptySequence 0)])), .num 1])])])
#guard obs case_takeCount__p12_e == "ok raw=1 n=1"

-- takeCount__ppe: count(take((()), 1))
def case_takeCount__ppe : Expr :=
  .block (alg [] [] [] [.call (.resolve "count") (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0)])), .num 1])])])
#guard obs case_takeCount__ppe == "ok raw=0 n=1"

-- takeCount__pp1: count(take(((1)), 1))
def case_takeCount__pp1 : Expr :=
  .block (alg [] [] [] [.call (.resolve "count") (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1)]))])), .num 1])])])
#guard obs case_takeCount__pp1 == "ok raw=1 n=1"

-- takeCount__ppp12: count(take((((1, 2))), 1))
def case_takeCount__ppp12 : Expr :=
  .block (alg [] [] [] [.call (.resolve "count") (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)]))]))])), .num 1])])])
#guard obs case_takeCount__ppp12 == "ok raw=1 n=1"

-- takeCount__le: count(take([], 1))
def case_takeCount__le : Expr :=
  .block (alg [] [] [] [.call (.resolve "count") (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.listLiteral []), .num 1])])])
#guard obs case_takeCount__le == "ok raw=0 n=1"

-- takeCount__l7: count(take([7], 1))
def case_takeCount__l7 : Expr :=
  .block (alg [] [] [] [.call (.resolve "count") (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.listLiteral [(.num 7)]), .num 1])])])
#guard obs case_takeCount__l7 == "ok raw=1 n=1"

-- takeCount__l12: count(take([1, 2], 1))
def case_takeCount__l12 : Expr :=
  .block (alg [] [] [] [.call (.resolve "count") (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.listLiteral [(.num 1), (.num 2)]), .num 1])])])
#guard obs case_takeCount__l12 == "ok raw=1 n=1"

-- takeCount__l12_3: count(take([[1, 2], 3], 1))
def case_takeCount__l12_3 : Expr :=
  .block (alg [] [] [] [.call (.resolve "count") (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.listLiteral [(.listLiteral [(.num 1), (.num 2)]), (.num 3)]), .num 1])])])
#guard obs case_takeCount__l12_3 == "ok raw=1 n=1"

-- takeCount__lle: count(take([[]], 1))
def case_takeCount__lle : Expr :=
  .block (alg [] [] [] [.call (.resolve "count") (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.listLiteral [(.listLiteral [])]), .num 1])])])
#guard obs case_takeCount__lle == "ok raw=1 n=1"

-- takeCount__l_e: count(take([()], 1))
def case_takeCount__l_e : Expr :=
  .block (alg [] [] [] [.call (.resolve "count") (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.listLiteral [(.emptySequence 0)]), .num 1])])])
#guard obs case_takeCount__l_e == "ok raw=1 n=1"

-- takeCount__l_p12: count(take([(1, 2)], 1))
def case_takeCount__l_p12 : Expr :=
  .block (alg [] [] [] [.call (.resolve "count") (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.listLiteral [(.block (alg [] [] [] [(.num 1), (.num 2)]))]), .num 1])])])
#guard obs case_takeCount__l_p12 == "ok raw=1 n=1"

-- takeCount__p_l12: count(take(([1, 2], 3), 1))
def case_takeCount__p_l12 : Expr :=
  .block (alg [] [] [] [.call (.resolve "count") (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.block (alg [] [] [] [(.listLiteral [(.num 1), (.num 2)]), (.num 3)])), .num 1])])])
#guard obs case_takeCount__p_l12 == "ok raw=1 n=1"

-- takeCount__pl1: count(take(([1]), 1))
def case_takeCount__pl1 : Expr :=
  .block (alg [] [] [] [.call (.resolve "count") (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.block (alg [] [] [] [(.listLiteral [(.num 1)])])), .num 1])])])
#guard obs case_takeCount__pl1 == "ok raw=1 n=1"

-- takeVariadic__e: G(a...) = a \n G(take((), 1))
def case_takeVariadic__e : Expr :=
  .block (alg [] [] [privateProp "G" (algWithParameters [{ name := "a", kind := .variadic }] [] [] [.param "a"])] [.call (.resolve "G") (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.emptySequence 0), .num 1])])])
#guard obs case_takeVariadic__e == "ok raw=L[L[]] n=1"

-- takeVariadic__n0: G(a...) = a \n G(take(0, 1))
def case_takeVariadic__n0 : Expr :=
  .block (alg [] [] [privateProp "G" (algWithParameters [{ name := "a", kind := .variadic }] [] [] [.param "a"])] [.call (.resolve "G") (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.num 0), .num 1])])])
#guard obs case_takeVariadic__n0 == "ok raw=L[L[0]] n=1"

-- takeVariadic__n1: G(a...) = a \n G(take(1, 1))
def case_takeVariadic__n1 : Expr :=
  .block (alg [] [] [privateProp "G" (algWithParameters [{ name := "a", kind := .variadic }] [] [] [.param "a"])] [.call (.resolve "G") (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.num 1), .num 1])])])
#guard obs case_takeVariadic__n1 == "ok raw=L[L[1]] n=1"

-- takeVariadic__p1: G(a...) = a \n G(take((1), 1))
def case_takeVariadic__p1 : Expr :=
  .block (alg [] [] [privateProp "G" (algWithParameters [{ name := "a", kind := .variadic }] [] [] [.param "a"])] [.call (.resolve "G") (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.block (alg [] [] [] [(.num 1)])), .num 1])])])
#guard obs case_takeVariadic__p1 == "ok raw=L[L[1]] n=1"

-- takeVariadic__p12: G(a...) = a \n G(take((1, 2), 1))
def case_takeVariadic__p12 : Expr :=
  .block (alg [] [] [privateProp "G" (algWithParameters [{ name := "a", kind := .variadic }] [] [] [.param "a"])] [.call (.resolve "G") (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), .num 1])])])
#guard obs case_takeVariadic__p12 == "ok raw=L[L[1]] n=1"

-- takeVariadic__p123: G(a...) = a \n G(take((1, 2, 3), 1))
def case_takeVariadic__p123 : Expr :=
  .block (alg [] [] [privateProp "G" (algWithParameters [{ name := "a", kind := .variadic }] [] [] [.param "a"])] [.call (.resolve "G") (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2), (.num 3)])), .num 1])])])
#guard obs case_takeVariadic__p123 == "ok raw=L[L[1]] n=1"

-- takeVariadic__pee: G(a...) = a \n G(take(((), ()), 1))
def case_takeVariadic__pee : Expr :=
  .block (alg [] [] [privateProp "G" (algWithParameters [{ name := "a", kind := .variadic }] [] [] [.param "a"])] [.call (.resolve "G") (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.emptySequence 0)])), .num 1])])])
#guard obs case_takeVariadic__pee == "ok raw=L[L[S[]]] n=1"

-- takeVariadic__pe1: G(a...) = a \n G(take(((), 1), 1))
def case_takeVariadic__pe1 : Expr :=
  .block (alg [] [] [privateProp "G" (algWithParameters [{ name := "a", kind := .variadic }] [] [] [.param "a"])] [.call (.resolve "G") (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.num 1)])), .num 1])])])
#guard obs case_takeVariadic__pe1 == "ok raw=L[L[S[]]] n=1"

-- takeVariadic__p1e: G(a...) = a \n G(take((1, ()), 1))
def case_takeVariadic__p1e : Expr :=
  .block (alg [] [] [privateProp "G" (algWithParameters [{ name := "a", kind := .variadic }] [] [] [.param "a"])] [.call (.resolve "G") (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.emptySequence 0)])), .num 1])])])
#guard obs case_takeVariadic__p1e == "ok raw=L[L[1]] n=1"

-- takeVariadic__p12_3: G(a...) = a \n G(take(((1, 2), 3), 1))
def case_takeVariadic__p12_3 : Expr :=
  .block (alg [] [] [privateProp "G" (algWithParameters [{ name := "a", kind := .variadic }] [] [] [.param "a"])] [.call (.resolve "G") (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.num 3)])), .num 1])])])
#guard obs case_takeVariadic__p12_3 == "ok raw=L[L[S[1, 2]]] n=1"

-- takeVariadic__p12_34: G(a...) = a \n G(take(((1, 2), (3, 4)), 1))
def case_takeVariadic__p12_34 : Expr :=
  .block (alg [] [] [privateProp "G" (algWithParameters [{ name := "a", kind := .variadic }] [] [] [.param "a"])] [.call (.resolve "G") (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.block (alg [] [] [] [(.num 3), (.num 4)]))])), .num 1])])])
#guard obs case_takeVariadic__p12_34 == "ok raw=L[L[S[1, 2]]] n=1"

-- takeVariadic__pe_12: G(a...) = a \n G(take(((), (1, 2)), 1))
def case_takeVariadic__pe_12 : Expr :=
  .block (alg [] [] [privateProp "G" (algWithParameters [{ name := "a", kind := .variadic }] [] [] [.param "a"])] [.call (.resolve "G") (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.block (alg [] [] [] [(.num 1), (.num 2)]))])), .num 1])])])
#guard obs case_takeVariadic__pe_12 == "ok raw=L[L[S[]]] n=1"

-- takeVariadic__ppe1_2: G(a...) = a \n G(take((((), 1), 2), 1))
def case_takeVariadic__ppe1_2 : Expr :=
  .block (alg [] [] [privateProp "G" (algWithParameters [{ name := "a", kind := .variadic }] [] [] [.param "a"])] [.call (.resolve "G") (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0), (.num 1)])), (.num 2)])), .num 1])])])
#guard obs case_takeVariadic__ppe1_2 == "ok raw=L[L[S[S[], 1]]] n=1"

-- takeVariadic__p12_e: G(a...) = a \n G(take(((1, 2), ()), 1))
def case_takeVariadic__p12_e : Expr :=
  .block (alg [] [] [privateProp "G" (algWithParameters [{ name := "a", kind := .variadic }] [] [] [.param "a"])] [.call (.resolve "G") (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)])), (.emptySequence 0)])), .num 1])])])
#guard obs case_takeVariadic__p12_e == "ok raw=L[L[S[1, 2]]] n=1"

-- takeVariadic__ppe: G(a...) = a \n G(take((()), 1))
def case_takeVariadic__ppe : Expr :=
  .block (alg [] [] [privateProp "G" (algWithParameters [{ name := "a", kind := .variadic }] [] [] [.param "a"])] [.call (.resolve "G") (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.block (alg [] [] [] [(.emptySequence 0)])), .num 1])])])
#guard obs case_takeVariadic__ppe == "ok raw=L[L[]] n=1"

-- takeVariadic__pp1: G(a...) = a \n G(take(((1)), 1))
def case_takeVariadic__pp1 : Expr :=
  .block (alg [] [] [privateProp "G" (algWithParameters [{ name := "a", kind := .variadic }] [] [] [.param "a"])] [.call (.resolve "G") (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1)]))])), .num 1])])])
#guard obs case_takeVariadic__pp1 == "ok raw=L[L[1]] n=1"

-- takeVariadic__ppp12: G(a...) = a \n G(take((((1, 2))), 1))
def case_takeVariadic__ppp12 : Expr :=
  .block (alg [] [] [privateProp "G" (algWithParameters [{ name := "a", kind := .variadic }] [] [] [.param "a"])] [.call (.resolve "G") (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [(.num 1), (.num 2)]))]))])), .num 1])])])
#guard obs case_takeVariadic__ppp12 == "ok raw=L[L[1]] n=1"

-- takeVariadic__le: G(a...) = a \n G(take([], 1))
def case_takeVariadic__le : Expr :=
  .block (alg [] [] [privateProp "G" (algWithParameters [{ name := "a", kind := .variadic }] [] [] [.param "a"])] [.call (.resolve "G") (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.listLiteral []), .num 1])])])
#guard obs case_takeVariadic__le == "ok raw=L[L[]] n=1"

-- takeVariadic__l7: G(a...) = a \n G(take([7], 1))
def case_takeVariadic__l7 : Expr :=
  .block (alg [] [] [privateProp "G" (algWithParameters [{ name := "a", kind := .variadic }] [] [] [.param "a"])] [.call (.resolve "G") (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.listLiteral [(.num 7)]), .num 1])])])
#guard obs case_takeVariadic__l7 == "ok raw=L[L[7]] n=1"

-- takeVariadic__l12: G(a...) = a \n G(take([1, 2], 1))
def case_takeVariadic__l12 : Expr :=
  .block (alg [] [] [privateProp "G" (algWithParameters [{ name := "a", kind := .variadic }] [] [] [.param "a"])] [.call (.resolve "G") (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.listLiteral [(.num 1), (.num 2)]), .num 1])])])
#guard obs case_takeVariadic__l12 == "ok raw=L[L[1]] n=1"

-- takeVariadic__l12_3: G(a...) = a \n G(take([[1, 2], 3], 1))
def case_takeVariadic__l12_3 : Expr :=
  .block (alg [] [] [privateProp "G" (algWithParameters [{ name := "a", kind := .variadic }] [] [] [.param "a"])] [.call (.resolve "G") (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.listLiteral [(.listLiteral [(.num 1), (.num 2)]), (.num 3)]), .num 1])])])
#guard obs case_takeVariadic__l12_3 == "ok raw=L[L[L[1, 2]]] n=1"

-- takeVariadic__lle: G(a...) = a \n G(take([[]], 1))
def case_takeVariadic__lle : Expr :=
  .block (alg [] [] [privateProp "G" (algWithParameters [{ name := "a", kind := .variadic }] [] [] [.param "a"])] [.call (.resolve "G") (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.listLiteral [(.listLiteral [])]), .num 1])])])
#guard obs case_takeVariadic__lle == "ok raw=L[L[L[]]] n=1"

-- takeVariadic__l_e: G(a...) = a \n G(take([()], 1))
def case_takeVariadic__l_e : Expr :=
  .block (alg [] [] [privateProp "G" (algWithParameters [{ name := "a", kind := .variadic }] [] [] [.param "a"])] [.call (.resolve "G") (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.listLiteral [(.emptySequence 0)]), .num 1])])])
#guard obs case_takeVariadic__l_e == "ok raw=L[L[S[]]] n=1"

-- takeVariadic__l_p12: G(a...) = a \n G(take([(1, 2)], 1))
def case_takeVariadic__l_p12 : Expr :=
  .block (alg [] [] [privateProp "G" (algWithParameters [{ name := "a", kind := .variadic }] [] [] [.param "a"])] [.call (.resolve "G") (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.listLiteral [(.block (alg [] [] [] [(.num 1), (.num 2)]))]), .num 1])])])
#guard obs case_takeVariadic__l_p12 == "ok raw=L[L[S[1, 2]]] n=1"

-- takeVariadic__p_l12: G(a...) = a \n G(take(([1, 2], 3), 1))
def case_takeVariadic__p_l12 : Expr :=
  .block (alg [] [] [privateProp "G" (algWithParameters [{ name := "a", kind := .variadic }] [] [] [.param "a"])] [.call (.resolve "G") (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.block (alg [] [] [] [(.listLiteral [(.num 1), (.num 2)]), (.num 3)])), .num 1])])])
#guard obs case_takeVariadic__p_l12 == "ok raw=L[L[L[1, 2]]] n=1"

-- takeVariadic__pl1: G(a...) = a \n G(take(([1]), 1))
def case_takeVariadic__pl1 : Expr :=
  .block (alg [] [] [privateProp "G" (algWithParameters [{ name := "a", kind := .variadic }] [] [] [.param "a"])] [.call (.resolve "G") (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.block (alg [] [] [] [(.listLiteral [(.num 1)])])), .num 1])])])
#guard obs case_takeVariadic__pl1 == "ok raw=L[L[1]] n=1"

-- special__multiProp: P = 1, 2, 3 \n P
def case_special__multiProp : Expr :=
  .block (alg [] [] [privateProp "P" (alg [] [] [] [.num 1, .num 2, .num 3])] [.resolve "P"])
#guard obs case_special__multiProp == "ok raw=S[1, 2, 3] n=1"

-- special__multiPropCall: P = 1, 2, 3 \n P()
def case_special__multiPropCall : Expr :=
  .block (alg [] [] [privateProp "P" (alg [] [] [] [.num 1, .num 2, .num 3])] [.call (.resolve "P") (alg [] [] [] [])])
#guard obs case_special__multiPropCall == "ok raw=S[1, 2, 3] n=1"

-- special__multiPropCount: P = 1, 2, 3 \n count(P)
def case_special__multiPropCount : Expr :=
  .block (alg [] [] [privateProp "P" (alg [] [] [] [.num 1, .num 2, .num 3])] [.call (.resolve "count") (alg [] [] [] [.resolve "P"])])
#guard obs case_special__multiPropCount == "ok raw=3 n=1"

-- special__multiPropDotCount: P = 1, 2, 3 \n P.count
def case_special__multiPropDotCount : Expr :=
  .block (alg [] [] [privateProp "P" (alg [] [] [] [.num 1, .num 2, .num 3])] [.dotCall (.resolve "P") "count" none])
#guard obs case_special__multiPropDotCount == "ok raw=3 n=1"

-- special__multiPropDot: A = { \n     X = 1, 2, 3 \n } \n A.X
def case_special__multiPropDot : Expr :=
  .block (alg [] [] [privateProp "A" (alg [] [] [publicProp "X" (alg [] [] [] [.num 1, .num 2, .num 3])] [])] [.dotCall (.resolve "A") "X" none])
#guard obs case_special__multiPropDot == "ok raw=S[1, 2, 3] n=1"

-- special__multiPropIndex0: P = 1, 2, 3 \n P:0
def case_special__multiPropIndex0 : Expr :=
  .block (alg [] [] [privateProp "P" (alg [] [] [] [.num 1, .num 2, .num 3])] [.index (.resolve "P") (.num 0)])
#guard obs case_special__multiPropIndex0 == "ok raw=1 n=1"

-- special__multiPropEq: P = 1, 2, 3 \n P == (1, 2, 3)
def case_special__multiPropEq : Expr :=
  .block (alg [] [] [privateProp "P" (alg [] [] [] [.num 1, .num 2, .num 3])] [.binary .eq (.resolve "P") (.block (alg [] [] [] [.num 1, .num 2, .num 3]))])
#guard obs case_special__multiPropEq == "ok raw=1 n=1"

-- special__multiVariadic: F(a...) = a \n F(1, 2, 3)
def case_special__multiVariadic : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .variadic }] [] [] [.param "a"])] [.call (.resolve "F") (alg [] [] [] [.num 1, .num 2, .num 3])])
#guard obs case_special__multiVariadic == "ok raw=L[1, 2, 3] n=1"

-- special__multiVariadicCount: F(a...) = a \n count(F(1, 2, 3))
def case_special__multiVariadicCount : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .variadic }] [] [] [.param "a"])] [.call (.resolve "count") (alg [] [] [] [.call (.resolve "F") (alg [] [] [] [.num 1, .num 2, .num 3])])])
#guard obs case_special__multiVariadicCount == "ok raw=3 n=1"

-- special__variadicEmptyCall: F(a...) = a \n F()
def case_special__variadicEmptyCall : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .variadic }] [] [] [.param "a"])] [.call (.resolve "F") (alg [] [] [] [])])
#guard obs case_special__variadicEmptyCall == "ok raw=L[] n=1"

-- special__variadicFwdSum: F(a...) = sum(a) \n F(1, 2, 3)
def case_special__variadicFwdSum : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .variadic }] [] [] [.call (.resolve "sum") (alg [] [] [] [.param "a"])])] [.call (.resolve "F") (alg [] [] [] [.num 1, .num 2, .num 3])])
#guard obs case_special__variadicFwdSum == "ok raw=6 n=1"

-- special__variadicFwdSpread: F(a...) = G(a.spread) \n G(b...) = b \n F(1, 2, 3)
def case_special__variadicFwdSpread : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .variadic }] [] [] [.call (.resolve "G") (alg [] [] [] [.sequenceSpread (.param "a")])]), privateProp "G" (algWithParameters [{ name := "b", kind := .variadic }] [] [] [.param "b"])] [.call (.resolve "F") (alg [] [] [] [.num 1, .num 2, .num 3])])
#guard obs case_special__variadicFwdSpread == "ok raw=L[1, 2, 3] n=1"

-- special__variadicJoin: F(a...) = a \n F((1, 2).spread, (3, 4).spread)
def case_special__variadicJoin : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .variadic }] [] [] [.param "a"])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.block (alg [] [] [] [.num 1, .num 2])), .sequenceSpread (.block (alg [] [] [] [.num 3, .num 4]))])])
#guard obs case_special__variadicJoin == "ok raw=L[1, 2, 3, 4] n=1"

-- special__range13: range(1, 3)
def case_special__range13 : Expr :=
  .block (alg [] [] [] [.call (.resolve "range") (alg [] [] [] [.num 1, .num 3])])
#guard obs case_special__range13 == "ok raw=L[1, 2, 3] n=1"

-- special__rangeCapture: x = range(1, 3) \n x
def case_special__rangeCapture : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [.call (.resolve "range") (alg [] [] [] [.num 1, .num 3])])] [.resolve "x"])
#guard obs case_special__rangeCapture == "ok raw=L[1, 2, 3] n=1"

-- special__rangeCount: count(range(1, 3))
def case_special__rangeCount : Expr :=
  .block (alg [] [] [] [.call (.resolve "count") (alg [] [] [] [.call (.resolve "range") (alg [] [] [] [.num 1, .num 3])])])
#guard obs case_special__rangeCount == "ok raw=3 n=1"

-- special__rangeIndex0: range(1, 3):0
def case_special__rangeIndex0 : Expr :=
  .block (alg [] [] [] [.index (.call (.resolve "range") (alg [] [] [] [.num 1, .num 3])) (.num 0)])
#guard obs case_special__rangeIndex0 == "ok raw=1 n=1"

-- special__takeOneSurvivorPair: take(((1, 2), (3, 4)), 1)
def case_special__takeOneSurvivorPair : Expr :=
  .block (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [.num 1, .num 2])), (.block (alg [] [] [] [.num 3, .num 4]))])), .num 1])])
#guard obs case_special__takeOneSurvivorPair == "ok raw=L[S[1, 2]] n=1"

-- special__takeOneSurvivorPairCount: count(take(((1, 2), (3, 4)), 1))
def case_special__takeOneSurvivorPairCount : Expr :=
  .block (alg [] [] [] [.call (.resolve "count") (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [.num 1, .num 2])), (.block (alg [] [] [] [.num 3, .num 4]))])), .num 1])])])
#guard obs case_special__takeOneSurvivorPairCount == "ok raw=1 n=1"

-- special__takeOneSurvivorPairEq: take(((1, 2), (3, 4)), 1) == (1, 2)
def case_special__takeOneSurvivorPairEq : Expr :=
  .block (alg [] [] [] [.binary .eq (.call (.resolve "take") (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [.num 1, .num 2])), (.block (alg [] [] [] [.num 3, .num 4]))])), .num 1])) (.block (alg [] [] [] [.num 1, .num 2]))])
#guard obs case_special__takeOneSurvivorPairEq == "ok raw=0 n=1"

-- special__skipToOnePair: skip(((1, 2), (3, 4)), 1)
def case_special__skipToOnePair : Expr :=
  .block (alg [] [] [] [.call (.resolve "skip") (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [.num 1, .num 2])), (.block (alg [] [] [] [.num 3, .num 4]))])), .num 1])])
#guard obs case_special__skipToOnePair == "ok raw=L[S[3, 4]] n=1"

-- special__distinctEmpties: distinct((), ())
def case_special__distinctEmpties : Expr :=
  .block (alg [] [] [] [.call (.resolve "distinct") (alg [] [] [] [.emptySequence 0, .emptySequence 0])])
#guard obs case_special__distinctEmpties == "err arity"

-- special__distinctPairsToOne: distinct((1, 2), (1, 2))
def case_special__distinctPairsToOne : Expr :=
  .block (alg [] [] [] [.call (.resolve "distinct") (alg [] [] [] [(.block (alg [] [] [] [.num 1, .num 2])), (.block (alg [] [] [] [.num 1, .num 2]))])])
#guard obs case_special__distinctPairsToOne == "err arity"

-- special__takeEmpties: take((), (), 2)
def case_special__takeEmpties : Expr :=
  .block (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [.emptySequence 0, .emptySequence 0, .num 2])])
#guard obs case_special__takeEmpties == "err arity"

-- special__filterOneSurvivor: Big(a) = a > 2 \n filter((1, 2, 3), Big)
def case_special__filterOneSurvivor : Expr :=
  .block (alg [] [] [privateProp "Big" (alg ["a"] [] [] [.binary .gt (.param "a") (.num 2)])] [.call (.resolve "filter") (alg [] [] [] [(.block (alg [] [] [] [.num 1, .num 2, .num 3])), .resolve "Big"])])
#guard obs case_special__filterOneSurvivor == "ok raw=L[3] n=1"

-- special__filterOneSurvivorCount: Big(a) = a > 2 \n count(filter((1, 2, 3), Big))
def case_special__filterOneSurvivorCount : Expr :=
  .block (alg [] [] [privateProp "Big" (alg ["a"] [] [] [.binary .gt (.param "a") (.num 2)])] [.call (.resolve "count") (alg [] [] [] [.call (.resolve "filter") (alg [] [] [] [(.block (alg [] [] [] [.num 1, .num 2, .num 3])), .resolve "Big"])])])
#guard obs case_special__filterOneSurvivorCount == "ok raw=1 n=1"

-- special__filterZeroSurvivors: No(a) = 0 \n filter((1, 2, 3), No)
def case_special__filterZeroSurvivors : Expr :=
  .block (alg [] [] [privateProp "No" (alg ["a"] [] [] [.num 0])] [.call (.resolve "filter") (alg [] [] [] [(.block (alg [] [] [] [.num 1, .num 2, .num 3])), .resolve "No"])])
#guard obs case_special__filterZeroSurvivors == "ok raw=L[] n=1"

-- special__mapPairSwap: Swap(a, b) = b, a \n map(((1, 2), (3, 4)), Swap)
def case_special__mapPairSwap : Expr :=
  .block (alg [] [] [privateProp "Swap" (alg ["a", "b"] [] [] [.param "b", .param "a"])] [.call (.resolve "map") (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [.num 1, .num 2])), (.block (alg [] [] [] [.num 3, .num 4]))])), .resolve "Swap"])])
#guard obs case_special__mapPairSwap == "err arity"

-- special__mapPairSwapOk: Swap(a, b) = (b, a) \n map(((1, 2), (3, 4)), Swap)
def case_special__mapPairSwapOk : Expr :=
  .block (alg [] [] [privateProp "Swap" (alg ["a", "b"] [] [] [.block (alg [] [] [] [.param "b", .param "a"])])] [.call (.resolve "map") (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [.num 1, .num 2])), (.block (alg [] [] [] [.num 3, .num 4]))])), .resolve "Swap"])])
#guard obs case_special__mapPairSwapOk == "ok raw=L[S[2, 1], S[4, 3]] n=1"

-- special__mapToOne: M(a) = a \n map((7), M)
def case_special__mapToOne : Expr :=
  .block (alg [] [] [privateProp "M" (alg ["a"] [] [] [.param "a"])] [.call (.resolve "map") (alg [] [] [] [(.block (alg [] [] [] [.num 7])), .resolve "M"])])
#guard obs case_special__mapToOne == "ok raw=L[7] n=1"

-- special__orderSingle: order(5)
def case_special__orderSingle : Expr :=
  .block (alg [] [] [] [.call (.resolve "order") (alg [] [] [] [.num 5])])
#guard obs case_special__orderSingle == "ok raw=L[5] n=1"

-- special__orderEmpty: order(())
def case_special__orderEmpty : Expr :=
  .block (alg [] [] [] [.call (.resolve "order") (alg [] [] [] [.emptySequence 0])])
#guard obs case_special__orderEmpty == "ok raw=L[] n=1"

-- special__atomsNested: atoms(((1, 2), (3, 4)))
def case_special__atomsNested : Expr :=
  .block (alg [] [] [] [.call (.resolve "atoms") (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [.num 1, .num 2])), (.block (alg [] [] [] [.num 3, .num 4]))]))])])
#guard obs case_special__atomsNested == "ok raw=L[1, 2, 3, 4] n=1"

-- special__emptyOpGreater: () > 1
def case_special__emptyOpGreater : Expr :=
  .block (alg [] [] [] [.binary .gt (.emptySequence 0) (.num 1)])
#guard obs case_special__emptyOpGreater == "ok raw=1 n=1"

-- special__emptyOpPlus: () + 1
def case_special__emptyOpPlus : Expr :=
  .block (alg [] [] [] [.binary .add (.emptySequence 0) (.num 1)])
#guard obs case_special__emptyOpPlus == "ok raw=1 n=1"

-- special__emptyOpBoth: () + ()
def case_special__emptyOpBoth : Expr :=
  .block (alg [] [] [] [.binary .add (.emptySequence 0) (.emptySequence 0)])
#guard obs case_special__emptyOpBoth == "ok raw=S[] n=1"

-- special__emptyEqEmpty: () == ()
def case_special__emptyEqEmpty : Expr :=
  .block (alg [] [] [] [.binary .eq (.emptySequence 0) (.emptySequence 0)])
#guard obs case_special__emptyEqEmpty == "ok raw=1 n=1"

-- special__emptyEqNestedEmpty: () == (())
def case_special__emptyEqNestedEmpty : Expr :=
  .block (alg [] [] [] [.binary .eq (.emptySequence 0) (.block (alg [] [] [] [.emptySequence 0]))])
#guard obs case_special__emptyEqNestedEmpty == "ok raw=1 n=1"

-- special__emptyNeNestedEmpty: () != (())
def case_special__emptyNeNestedEmpty : Expr :=
  .block (alg [] [] [] [.binary .ne (.emptySequence 0) (.block (alg [] [] [] [.emptySequence 0]))])
#guard obs case_special__emptyNeNestedEmpty == "ok raw=0 n=1"

-- special__propBodyEmptySlot: P = (), 99 \n P
def case_special__propBodyEmptySlot : Expr :=
  .block (alg [] [] [privateProp "P" (alg [] [] [] [.emptySequence 0, .num 99])] [.resolve "P"])
#guard obs case_special__propBodyEmptySlot == "ok raw=S[S[], 99] n=1"

-- special__rootEmptySlots: (), 99
def case_special__rootEmptySlots : Expr :=
  .block (alg [] [] [] [.emptySequence 0, .num 99])
#guard obs case_special__rootEmptySlots == "ok raw=S[S[], 99] n=2"

-- special__seqOfSpreadEmpty: ((().spread), 1)
def case_special__seqOfSpreadEmpty : Expr :=
  .block (alg [] [] [] [.block (alg [] [] [] [.block (alg [] [] [] [.sequenceSpread (.emptySequence 0)]), .num 1])])
#guard obs case_special__seqOfSpreadEmpty == "ok raw=S[S[], 1] n=1"

-- special__indexPairInSeq: x = ((1, 2), (3, 4)) \n (x:0, 99)
def case_special__indexPairInSeq : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [.num 1, .num 2])), (.block (alg [] [] [] [.num 3, .num 4]))]))])] [.block (alg [] [] [] [.index (.resolve "x") (.num 0), .num 99])])
#guard obs case_special__indexPairInSeq == "ok raw=S[S[1, 2], 99] n=1"

-- special__indexEmptyItemRoot: x = ((), ()) \n x:0
def case_special__indexEmptyItemRoot : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [.emptySequence 0, .emptySequence 0]))])] [.index (.resolve "x") (.num 0)])
#guard obs case_special__indexEmptyItemRoot == "ok raw=S[] n=1"

-- special__indexCapturedEq: x = ((1, 2), (3, 4)) \n y = x:0 \n y == (1, 2)
def case_special__indexCapturedEq : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [.num 1, .num 2])), (.block (alg [] [] [] [.num 3, .num 4]))]))]), privateProp "y" (alg [] [] [] [.index (.resolve "x") (.num 0)])] [.binary .eq (.resolve "y") (.block (alg [] [] [] [.num 1, .num 2]))])
#guard obs case_special__indexCapturedEq == "ok raw=1 n=1"

-- special__chainedListIndex: x = [[1, 2], [3, 4]] \n x:1:0
def case_special__chainedListIndex : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [.listLiteral [.num 1, .num 2], .listLiteral [.num 3, .num 4]])])] [.index (.index (.resolve "x") (.num 1)) (.num 0)])
#guard obs case_special__chainedListIndex == "ok raw=3 n=1"

-- special__listIndexCapturedEq: x = [[1, 2]] \n y = x:0 \n y == [1, 2]
def case_special__listIndexCapturedEq : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [.listLiteral [.num 1, .num 2]])]), privateProp "y" (alg [] [] [] [.index (.resolve "x") (.num 0)])] [.binary .eq (.resolve "y") (.listLiteral [.num 1, .num 2])])
#guard obs case_special__listIndexCapturedEq == "ok raw=1 n=1"

-- special__listIndexSelectedKindEqFalse: [[1, 2]]:0 == (1, 2)
def case_special__listIndexSelectedKindEqFalse : Expr :=
  .block (alg [] [] [] [.binary .eq (.index (.listLiteral [.listLiteral [.num 1, .num 2]]) (.num 0)) (.block (alg [] [] [] [.num 1, .num 2]))])
#guard obs case_special__listIndexSelectedKindEqFalse == "ok raw=0 n=1"

-- special__orderIndex0: [3, 1, 2].order:0
def case_special__orderIndex0 : Expr :=
  .block (alg [] [] [] [.index (.dotCall (.listLiteral [.num 3, .num 1, .num 2]) "order" none) (.num 0)])
#guard obs case_special__orderIndex0 == "ok raw=1 n=1"

-- special__nestedWrittenArg: F(a, b) = a \n F(((1, 2)), 3)
def case_special__nestedWrittenArg : Expr :=
  .block (alg [] [] [privateProp "F" (alg ["a", "b"] [] [] [.param "a"])] [.call (.resolve "F") (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [.num 1, .num 2]))])), .num 3])])
#guard obs case_special__nestedWrittenArg == "ok raw=S[1, 2] n=1"

-- special__writtenSlotArity: F(a, b) = a + b \n F(((1, 2)))
def case_special__writtenSlotArity : Expr :=
  .block (alg [] [] [privateProp "F" (alg ["a", "b"] [] [] [.binary .add (.param "a") (.param "b")])] [.call (.resolve "F") (alg [] [] [] [(.block (alg [] [] [] [(.block (alg [] [] [] [.num 1, .num 2]))]))])])
#guard obs case_special__writtenSlotArity == "err arity"

-- special__mixedSingleGrouped: F(x, y..., z) = y \n A = (1, 2, 3, 4) \n F(A)
def case_special__mixedSingleGrouped : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "x" }, { name := "y", kind := .variadic }, { name := "z" }] [] [] [.param "y"]), privateProp "A" (alg [] [] [] [(.block (alg [] [] [] [.num 1, .num 2, .num 3, .num 4]))])] [.call (.resolve "F") (alg [] [] [] [.resolve "A"])])
#guard obs case_special__mixedSingleGrouped == "err arity"

-- special__sumEmpty: sum(())
def case_special__sumEmpty : Expr :=
  .block (alg [] [] [] [.call (.resolve "sum") (alg [] [] [] [.emptySequence 0])])
#guard obs case_special__sumEmpty == "ok raw=0 n=1"

-- special__spreadWithSiblingSeqLiteral: x = (1, 2) \n (x.spread, 99)
def case_special__spreadWithSiblingSeqLiteral : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.block (alg [] [] [] [.num 1, .num 2]))])] [.block (alg [] [] [] [.sequenceSpread (.resolve "x"), .num 99])])
#guard obs case_special__spreadWithSiblingSeqLiteral == "ok raw=S[1, 2, 99] n=1"

-- special__spreadEmptyBetween: (1.spread, (), 2.spread)
def case_special__spreadEmptyBetween : Expr :=
  .block (alg [] [] [] [.block (alg [] [] [] [.sequenceSpread (.num 1), .emptySequence 0, .sequenceSpread (.num 2)])])
#guard obs case_special__spreadEmptyBetween == "ok raw=S[1, S[], 2] n=1"

-- special__rootSpreadExtra: A = (1, 2) \n A.spread, 99
def case_special__rootSpreadExtra : Expr :=
  .block (alg [] [] [privateProp "A" (alg [] [] [] [(.block (alg [] [] [] [.num 1, .num 2]))])] [.sequenceSpread (.resolve "A"), .num 99])
#guard obs case_special__rootSpreadExtra == "ok raw=S[1, 2, 99] n=3"

-- special__spreadOfSpreadSeqLiteral: A = (1, 2) \n ((A.spread, 99)).spread
def case_special__spreadOfSpreadSeqLiteral : Expr :=
  .block (alg [] [] [privateProp "A" (alg [] [] [] [(.block (alg [] [] [] [.num 1, .num 2]))])] [.sequenceSpread (.block (alg [] [] [] [(.block (alg [] [] [] [.sequenceSpread (.resolve "A"), .num 99]))]))])
#guard obs case_special__spreadOfSpreadSeqLiteral == "ok raw=S[1, 2, 99] n=3"

-- special__eqSpreadSeqLiteral: P = (1, 2) \n (P.spread, 99) == (1, 2, 99)
def case_special__eqSpreadSeqLiteral : Expr :=
  .block (alg [] [] [privateProp "P" (alg [] [] [] [(.block (alg [] [] [] [.num 1, .num 2]))])] [.binary .eq (.block (alg [] [] [] [.sequenceSpread (.resolve "P"), .num 99])) (.block (alg [] [] [] [.num 1, .num 2, .num 99]))])
#guard obs case_special__eqSpreadSeqLiteral == "ok raw=1 n=1"

-- special__loopSpreadHistoryFlat: Step((history...), previous) = (history.spread, previous + 1), previous + 1 \n Step.repeat(2, (1, 2), 2):0
def case_special__loopSpreadHistoryFlat : Expr :=
  .block (alg [] [] [privateProp "Step" (algWithParameterPatterns [.sequenceValue [.capture { name := "history", kind := .variadic }], .capture { name := "previous" }] [] [] [.block (alg [] [] [] [.sequenceSpread (.param "history"), .binary .add (.param "previous") (.num 1)]), .binary .add (.param "previous") (.num 1)])] [.index (.dotCall (.resolve "Step") "repeat" (some (alg [] [] [] [.num 2, (.block (alg [] [] [] [.num 1, .num 2])), .num 2]))) (.num 0)])
#guard obs case_special__loopSpreadHistoryFlat == "ok raw=S[1, 2, 3, 4] n=4"

-- special__ifBranchSeq: if(1, (1, 2), 3)
def case_special__ifBranchSeq : Expr :=
  .block (alg [] [] [] [.call (.resolve "if") (alg [] [] [] [.num 1, (.block (alg [] [] [] [.num 1, .num 2])), .num 3])])
#guard obs case_special__ifBranchSeq == "ok raw=S[1, 2] n=1"

-- special__divZero: 1 / 0
def case_special__divZero : Expr :=
  .block (alg [] [] [] [.binary .div (.num 1) (.num 0)])
#guard obs case_special__divZero == "err div0"

-- special__negativeResult: 0 - 1
def case_special__negativeResult : Expr :=
  .block (alg [] [] [] [.binary .sub (.num 0) (.num 1)])
#guard obs case_special__negativeResult == "ok raw=-1 n=1"

-- special__strEq: 'ab' == 'ab'
def case_special__strEq : Expr :=
  .block (alg [] [] [] [.binary .eq (.stringLiteral "ab") (.stringLiteral "ab")])
#guard obs case_special__strEq == "ok raw=1 n=1"

-- special__strCount: count('ab')
def case_special__strCount : Expr :=
  .block (alg [] [] [] [.call (.resolve "count") (alg [] [] [] [(.stringLiteral "ab")])])
#guard obs case_special__strCount == "ok raw=1 n=1"

-- special__strCapture: x = 'ab' \n x
def case_special__strCapture : Expr :=
  .block (alg [] [] [privateProp "x" (alg [] [] [] [(.stringLiteral "ab")])] [.resolve "x"])
#guard obs case_special__strCapture == "ok raw='ab' n=1"

-- special__listSpreadOfSeqProp: A = 1, 2, 3 \n [A.spread]
def case_special__listSpreadOfSeqProp : Expr :=
  .block (alg [] [] [privateProp "A" (alg [] [] [] [.num 1, .num 2, .num 3])] [.listLiteral [.sequenceSpread (.resolve "A")]])
#guard obs case_special__listSpreadOfSeqProp == "ok raw=L[1, 2, 3] n=1"

-- special__listSpreadBetween: A = 1, 2, 3 \n [0, A.spread, 4]
def case_special__listSpreadBetween : Expr :=
  .block (alg [] [] [privateProp "A" (alg [] [] [] [.num 1, .num 2, .num 3])] [.listLiteral [.num 0, .sequenceSpread (.resolve "A"), .num 4]])
#guard obs case_special__listSpreadBetween == "ok raw=L[0, 1, 2, 3, 4] n=1"

-- special__listOfLists: A = [1, 2] \n B = [3, 4] \n [A, B]
def case_special__listOfLists : Expr :=
  .block (alg [] [] [privateProp "A" (alg [] [] [] [(.listLiteral [.num 1, .num 2])]), privateProp "B" (alg [] [] [] [(.listLiteral [.num 3, .num 4])])] [.listLiteral [.resolve "A", .resolve "B"]])
#guard obs case_special__listOfLists == "ok raw=L[L[1, 2], L[3, 4]] n=1"

-- special__listSpreadConcat: A = [1, 2] \n B = [3, 4] \n [A.spread, B.spread]
def case_special__listSpreadConcat : Expr :=
  .block (alg [] [] [privateProp "A" (alg [] [] [] [(.listLiteral [.num 1, .num 2])]), privateProp "B" (alg [] [] [] [(.listLiteral [.num 3, .num 4])])] [.listLiteral [.sequenceSpread (.resolve "A"), .sequenceSpread (.resolve "B")]])
#guard obs case_special__listSpreadConcat == "ok raw=L[1, 2, 3, 4] n=1"

-- special__listMixedSpread: A = [1, 2] \n B = [3, 4] \n [A, B.spread]
def case_special__listMixedSpread : Expr :=
  .block (alg [] [] [privateProp "A" (alg [] [] [] [(.listLiteral [.num 1, .num 2])]), privateProp "B" (alg [] [] [] [(.listLiteral [.num 3, .num 4])])] [.listLiteral [.resolve "A", .sequenceSpread (.resolve "B")]])
#guard obs case_special__listMixedSpread == "ok raw=L[L[1, 2], 3, 4] n=1"

-- special__listEmptyListSpreadBetween: [1, [].spread, 2]
def case_special__listEmptyListSpreadBetween : Expr :=
  .block (alg [] [] [] [.listLiteral [.num 1, .sequenceSpread (.listLiteral []), .num 2]])
#guard obs case_special__listEmptyListSpreadBetween == "ok raw=L[1, 2] n=1"

-- special__listEmptySeqSpreadBetween: [1, ().spread, 2]
def case_special__listEmptySeqSpreadBetween : Expr :=
  .block (alg [] [] [] [.listLiteral [.num 1, .sequenceSpread (.emptySequence 0), .num 2]])
#guard obs case_special__listEmptySeqSpreadBetween == "ok raw=L[1, 2] n=1"

-- special__listNeSeq: [1, 2] == (1, 2)
def case_special__listNeSeq : Expr :=
  .block (alg [] [] [] [.binary .eq (.listLiteral [.num 1, .num 2]) (.block (alg [] [] [] [.num 1, .num 2]))])
#guard obs case_special__listNeSeq == "ok raw=0 n=1"

-- special__listEmptyNeEmptySeq: [] == ()
def case_special__listEmptyNeEmptySeq : Expr :=
  .block (alg [] [] [] [.binary .eq (.listLiteral []) (.emptySequence 0)])
#guard obs case_special__listEmptyNeEmptySeq == "ok raw=0 n=1"

-- special__listSingletonNeItem: [7] == 7
def case_special__listSingletonNeItem : Expr :=
  .block (alg [] [] [] [.binary .eq (.listLiteral [.num 7]) (.num 7)])
#guard obs case_special__listSingletonNeItem == "ok raw=0 n=1"

-- special__listWrapCanonicalizes: ([1, 2]) == [1, 2]
def case_special__listWrapCanonicalizes : Expr :=
  .block (alg [] [] [] [.binary .eq (.block (alg [] [] [] [.listLiteral [.num 1, .num 2]])) (.listLiteral [.num 1, .num 2])])
#guard obs case_special__listWrapCanonicalizes == "ok raw=1 n=1"

-- special__listSpreadCaptureRoundTrip: A = [1, 2, 3] \n B = A.spread \n B == (1, 2, 3)
def case_special__listSpreadCaptureRoundTrip : Expr :=
  .block (alg [] [] [privateProp "A" (alg [] [] [] [(.listLiteral [.num 1, .num 2, .num 3])]), privateProp "B" (alg [] [] [] [.sequenceSpread (.resolve "A")])] [.binary .eq (.resolve "B") (.block (alg [] [] [] [.num 1, .num 2, .num 3]))])
#guard obs case_special__listSpreadCaptureRoundTrip == "ok raw=1 n=1"

-- special__listCollectingNotSequenceKind: x, rest... = [1, 2, 3] \n rest == (2, 3)
def case_special__listCollectingNotSequenceKind : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.listLiteral [.num 1, .num 2, .num 3])]), privateProp "rest" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "rest", kind := .variadic }]] [] [] [.param "rest"])) (alg [] [] [] [.resolve "d"])])] [.binary .eq (.resolve "rest") (.block (alg [] [] [] [.num 2, .num 3]))])
#guard obs case_special__listCollectingNotSequenceKind == "ok raw=0 n=1"

-- special__listCollectingCollectsExactList: x, rest... = [1, 2, 3] \n rest == [2, 3]
def case_special__listCollectingCollectsExactList : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.listLiteral [.num 1, .num 2, .num 3])]), privateProp "rest" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "rest", kind := .variadic }]] [] [] [.param "rest"])) (alg [] [] [] [.resolve "d"])])] [.binary .eq (.resolve "rest") (.listLiteral [.num 2, .num 3])])
#guard obs case_special__listCollectingCollectsExactList == "ok raw=1 n=1"

-- special__implicitForwardOrdinarySource: Target(items...) = items \n Use(items) = Target \n Use([1, 2])
def case_special__implicitForwardOrdinarySource : Expr :=
  .block (alg [] [] [privateProp "Target" (algWithParameters [{ name := "items", kind := .variadic }] [] [] [.param "items"]), privateProp "Use" (alg ["items"] [] [] [.call (.resolve "Target") (alg [] [] [] [.param "items"])])] [.call (.resolve "Use") (alg [] [] [] [(.listLiteral [.num 1, .num 2])])])
#guard obs case_special__implicitForwardOrdinarySource == "ok raw=L[L[1, 2]] n=1"

-- special__callbackSingleVariadicMap: Collect(items...) = items \n [7].map(Collect)
def case_special__callbackSingleVariadicMap : Expr :=
  .block (alg [] [] [privateProp "Collect" (algWithParameters [{ name := "items", kind := .variadic }] [] [] [.param "items"])] [.dotCall (.listLiteral [.num 7]) "map" (some (alg [] [] [] [.resolve "Collect"]))])
#guard obs case_special__callbackSingleVariadicMap == "ok raw=L[L[7]] n=1"

-- special__callbackMixedVariadicRow: F(first, middle..., last) = middle \n [(1, 2, 3, 4)].map(F)
def case_special__callbackMixedVariadicRow : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "first" }, { name := "middle", kind := .variadic }, { name := "last" }] [] [] [.param "middle"])] [.dotCall (.listLiteral [.block (alg [] [] [] [.num 1, .num 2, .num 3, .num 4])]) "map" (some (alg [] [] [] [.resolve "F"]))])
#guard obs case_special__callbackMixedVariadicRow == "ok raw=L[L[2, 3]] n=1"

-- special__listInSeqSpreadKeepsList: A = [1, 2] \n (A, 9).spread
def case_special__listInSeqSpreadKeepsList : Expr :=
  .block (alg [] [] [privateProp "A" (alg [] [] [] [(.listLiteral [.num 1, .num 2])])] [.sequenceSpread (.block (alg [] [] [] [.resolve "A", .num 9]))])
#guard obs case_special__listInSeqSpreadKeepsList == "ok raw=S[L[1, 2], 9] n=2"

-- special__listFixedCallBoundary: F(a, b) = a \n F([1, 2], 3)
def case_special__listFixedCallBoundary : Expr :=
  .block (alg [] [] [privateProp "F" (alg ["a", "b"] [] [] [.param "a"])] [.call (.resolve "F") (alg [] [] [] [(.listLiteral [.num 1, .num 2]), .num 3])])
#guard obs case_special__listFixedCallBoundary == "ok raw=L[1, 2] n=1"

-- special__listVariadicSpreadCall: F(a...) = a \n A = [1, 2] \n F(A.spread, 9)
def case_special__listVariadicSpreadCall : Expr :=
  .block (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .variadic }] [] [] [.param "a"]), privateProp "A" (alg [] [] [] [(.listLiteral [.num 1, .num 2])])] [.call (.resolve "F") (alg [] [] [] [.sequenceSpread (.resolve "A"), .num 9])])
#guard obs case_special__listVariadicSpreadCall == "ok raw=L[1, 2, 9] n=1"

-- special__listLoneCollectingAssignment: items... = [1, 2, 3]
def case_special__listLoneCollectingAssignment : Expr :=
  .block (alg [] [] [privateProp "d" (alg [] [] [] [(.listLiteral [.num 1, .num 2, .num 3])]), privateProp "items" (alg [] [] [] [.call (.block (algWithParameterPatterns [.sequenceValue [.capture { name := "items", kind := .variadic }]] [] [] [.param "items"])) (alg [] [] [] [.resolve "d"])])] [])
#guard obs case_special__listLoneCollectingAssignment == "err missingOutput"

-- 1386 differential cases.

/--
Machine-checked surface partition count: the id list is built by the same
loop that emits the guards above, while the expected total is computed
independently from the corpus partition, so a generation bug fails `lake build`.
-/
def surfaceCaseIds : List String := [
  "root__e",
  "root__n0",
  "root__n1",
  "root__p1",
  "root__p12",
  "root__p123",
  "root__pee",
  "root__pe1",
  "root__p1e",
  "root__p12_3",
  "root__p12_34",
  "root__pe_12",
  "root__ppe1_2",
  "root__p12_e",
  "root__ppe",
  "root__pp1",
  "root__ppp12",
  "root__le",
  "root__l7",
  "root__l12",
  "root__l12_3",
  "root__lle",
  "root__l_e",
  "root__l_p12",
  "root__p_l12",
  "root__pl1",
  "capture__e",
  "capture__n0",
  "capture__n1",
  "capture__p1",
  "capture__p12",
  "capture__p123",
  "capture__pee",
  "capture__pe1",
  "capture__p1e",
  "capture__p12_3",
  "capture__p12_34",
  "capture__pe_12",
  "capture__ppe1_2",
  "capture__p12_e",
  "capture__ppe",
  "capture__pp1",
  "capture__ppp12",
  "capture__le",
  "capture__l7",
  "capture__l12",
  "capture__l12_3",
  "capture__lle",
  "capture__l_e",
  "capture__l_p12",
  "capture__p_l12",
  "capture__pl1",
  "captureCall__e",
  "captureCall__n0",
  "captureCall__n1",
  "captureCall__p1",
  "captureCall__p12",
  "captureCall__p123",
  "captureCall__pee",
  "captureCall__pe1",
  "captureCall__p1e",
  "captureCall__p12_3",
  "captureCall__p12_34",
  "captureCall__pe_12",
  "captureCall__ppe1_2",
  "captureCall__p12_e",
  "captureCall__ppe",
  "captureCall__pp1",
  "captureCall__ppp12",
  "captureCall__le",
  "captureCall__l7",
  "captureCall__l12",
  "captureCall__l12_3",
  "captureCall__lle",
  "captureCall__l_e",
  "captureCall__l_p12",
  "captureCall__p_l12",
  "captureCall__pl1",
  "dotAccess__e",
  "dotAccess__n0",
  "dotAccess__n1",
  "dotAccess__p1",
  "dotAccess__p12",
  "dotAccess__p123",
  "dotAccess__pee",
  "dotAccess__pe1",
  "dotAccess__p1e",
  "dotAccess__p12_3",
  "dotAccess__p12_34",
  "dotAccess__pe_12",
  "dotAccess__ppe1_2",
  "dotAccess__p12_e",
  "dotAccess__ppe",
  "dotAccess__pp1",
  "dotAccess__ppp12",
  "dotAccess__le",
  "dotAccess__l7",
  "dotAccess__l12",
  "dotAccess__l12_3",
  "dotAccess__lle",
  "dotAccess__l_e",
  "dotAccess__l_p12",
  "dotAccess__p_l12",
  "dotAccess__pl1",
  "dotAccessCall__e",
  "dotAccessCall__n0",
  "dotAccessCall__n1",
  "dotAccessCall__p1",
  "dotAccessCall__p12",
  "dotAccessCall__p123",
  "dotAccessCall__pee",
  "dotAccessCall__pe1",
  "dotAccessCall__p1e",
  "dotAccessCall__p12_3",
  "dotAccessCall__p12_34",
  "dotAccessCall__pe_12",
  "dotAccessCall__ppe1_2",
  "dotAccessCall__p12_e",
  "dotAccessCall__ppe",
  "dotAccessCall__pp1",
  "dotAccessCall__ppp12",
  "dotAccessCall__le",
  "dotAccessCall__l7",
  "dotAccessCall__l12",
  "dotAccessCall__l12_3",
  "dotAccessCall__lle",
  "dotAccessCall__l_e",
  "dotAccessCall__l_p12",
  "dotAccessCall__p_l12",
  "dotAccessCall__pl1",
  "fixed__e",
  "fixed__n0",
  "fixed__n1",
  "fixed__p1",
  "fixed__p12",
  "fixed__p123",
  "fixed__pee",
  "fixed__pe1",
  "fixed__p1e",
  "fixed__p12_3",
  "fixed__p12_34",
  "fixed__pe_12",
  "fixed__ppe1_2",
  "fixed__p12_e",
  "fixed__ppe",
  "fixed__pp1",
  "fixed__ppp12",
  "fixed__le",
  "fixed__l7",
  "fixed__l12",
  "fixed__l12_3",
  "fixed__lle",
  "fixed__l_e",
  "fixed__l_p12",
  "fixed__p_l12",
  "fixed__pl1",
  "fixedSpread__e",
  "fixedSpread__n0",
  "fixedSpread__n1",
  "fixedSpread__p1",
  "fixedSpread__p12",
  "fixedSpread__p123",
  "fixedSpread__pee",
  "fixedSpread__pe1",
  "fixedSpread__p1e",
  "fixedSpread__p12_3",
  "fixedSpread__p12_34",
  "fixedSpread__pe_12",
  "fixedSpread__ppe1_2",
  "fixedSpread__p12_e",
  "fixedSpread__ppe",
  "fixedSpread__pp1",
  "fixedSpread__ppp12",
  "fixedSpread__le",
  "fixedSpread__l7",
  "fixedSpread__l12",
  "fixedSpread__l12_3",
  "fixedSpread__lle",
  "fixedSpread__l_e",
  "fixedSpread__l_p12",
  "fixedSpread__p_l12",
  "fixedSpread__pl1",
  "variadic__e",
  "variadic__n0",
  "variadic__n1",
  "variadic__p1",
  "variadic__p12",
  "variadic__p123",
  "variadic__pee",
  "variadic__pe1",
  "variadic__p1e",
  "variadic__p12_3",
  "variadic__p12_34",
  "variadic__pe_12",
  "variadic__ppe1_2",
  "variadic__p12_e",
  "variadic__ppe",
  "variadic__pp1",
  "variadic__ppp12",
  "variadic__le",
  "variadic__l7",
  "variadic__l12",
  "variadic__l12_3",
  "variadic__lle",
  "variadic__l_e",
  "variadic__l_p12",
  "variadic__p_l12",
  "variadic__pl1",
  "variadicSpread__e",
  "variadicSpread__n0",
  "variadicSpread__n1",
  "variadicSpread__p1",
  "variadicSpread__p12",
  "variadicSpread__p123",
  "variadicSpread__pee",
  "variadicSpread__pe1",
  "variadicSpread__p1e",
  "variadicSpread__p12_3",
  "variadicSpread__p12_34",
  "variadicSpread__pe_12",
  "variadicSpread__ppe1_2",
  "variadicSpread__p12_e",
  "variadicSpread__ppe",
  "variadicSpread__pp1",
  "variadicSpread__ppp12",
  "variadicSpread__le",
  "variadicSpread__l7",
  "variadicSpread__l12",
  "variadicSpread__l12_3",
  "variadicSpread__lle",
  "variadicSpread__l_e",
  "variadicSpread__l_p12",
  "variadicSpread__p_l12",
  "variadicSpread__pl1",
  "variadicViaProp__e",
  "variadicViaProp__n0",
  "variadicViaProp__n1",
  "variadicViaProp__p1",
  "variadicViaProp__p12",
  "variadicViaProp__p123",
  "variadicViaProp__pee",
  "variadicViaProp__pe1",
  "variadicViaProp__p1e",
  "variadicViaProp__p12_3",
  "variadicViaProp__p12_34",
  "variadicViaProp__pe_12",
  "variadicViaProp__ppe1_2",
  "variadicViaProp__p12_e",
  "variadicViaProp__ppe",
  "variadicViaProp__pp1",
  "variadicViaProp__ppp12",
  "variadicViaProp__le",
  "variadicViaProp__l7",
  "variadicViaProp__l12",
  "variadicViaProp__l12_3",
  "variadicViaProp__lle",
  "variadicViaProp__l_e",
  "variadicViaProp__l_p12",
  "variadicViaProp__p_l12",
  "variadicViaProp__pl1",
  "mixed_h__e",
  "mixed_h__n0",
  "mixed_h__n1",
  "mixed_h__p1",
  "mixed_h__p12",
  "mixed_h__p123",
  "mixed_h__pee",
  "mixed_h__pe1",
  "mixed_h__p1e",
  "mixed_h__p12_3",
  "mixed_h__p12_34",
  "mixed_h__pe_12",
  "mixed_h__ppe1_2",
  "mixed_h__p12_e",
  "mixed_h__ppe",
  "mixed_h__pp1",
  "mixed_h__ppp12",
  "mixed_h__le",
  "mixed_h__l7",
  "mixed_h__l12",
  "mixed_h__l12_3",
  "mixed_h__lle",
  "mixed_h__l_e",
  "mixed_h__l_p12",
  "mixed_h__p_l12",
  "mixed_h__pl1",
  "mixed_t__e",
  "mixed_t__n0",
  "mixed_t__n1",
  "mixed_t__p1",
  "mixed_t__p12",
  "mixed_t__p123",
  "mixed_t__pee",
  "mixed_t__pe1",
  "mixed_t__p1e",
  "mixed_t__p12_3",
  "mixed_t__p12_34",
  "mixed_t__pe_12",
  "mixed_t__ppe1_2",
  "mixed_t__p12_e",
  "mixed_t__ppe",
  "mixed_t__pp1",
  "mixed_t__ppp12",
  "mixed_t__le",
  "mixed_t__l7",
  "mixed_t__l12",
  "mixed_t__l12_3",
  "mixed_t__lle",
  "mixed_t__l_e",
  "mixed_t__l_p12",
  "mixed_t__p_l12",
  "mixed_t__pl1",
  "mixedBack_t__e",
  "mixedBack_t__n0",
  "mixedBack_t__n1",
  "mixedBack_t__p1",
  "mixedBack_t__p12",
  "mixedBack_t__p123",
  "mixedBack_t__pee",
  "mixedBack_t__pe1",
  "mixedBack_t__p1e",
  "mixedBack_t__p12_3",
  "mixedBack_t__p12_34",
  "mixedBack_t__pe_12",
  "mixedBack_t__ppe1_2",
  "mixedBack_t__p12_e",
  "mixedBack_t__ppe",
  "mixedBack_t__pp1",
  "mixedBack_t__ppp12",
  "mixedBack_t__le",
  "mixedBack_t__l7",
  "mixedBack_t__l12",
  "mixedBack_t__l12_3",
  "mixedBack_t__lle",
  "mixedBack_t__l_e",
  "mixedBack_t__l_p12",
  "mixedBack_t__p_l12",
  "mixedBack_t__pl1",
  "mixedBack_z__e",
  "mixedBack_z__n0",
  "mixedBack_z__n1",
  "mixedBack_z__p1",
  "mixedBack_z__p12",
  "mixedBack_z__p123",
  "mixedBack_z__pee",
  "mixedBack_z__pe1",
  "mixedBack_z__p1e",
  "mixedBack_z__p12_3",
  "mixedBack_z__p12_34",
  "mixedBack_z__pe_12",
  "mixedBack_z__ppe1_2",
  "mixedBack_z__p12_e",
  "mixedBack_z__ppe",
  "mixedBack_z__pp1",
  "mixedBack_z__ppp12",
  "mixedBack_z__le",
  "mixedBack_z__l7",
  "mixedBack_z__l12",
  "mixedBack_z__l12_3",
  "mixedBack_z__lle",
  "mixedBack_z__l_e",
  "mixedBack_z__l_p12",
  "mixedBack_z__p_l12",
  "mixedBack_z__pl1",
  "deconPair_x__e",
  "deconPair_x__n0",
  "deconPair_x__n1",
  "deconPair_x__p1",
  "deconPair_x__p12",
  "deconPair_x__p123",
  "deconPair_x__pee",
  "deconPair_x__pe1",
  "deconPair_x__p1e",
  "deconPair_x__p12_3",
  "deconPair_x__p12_34",
  "deconPair_x__pe_12",
  "deconPair_x__ppe1_2",
  "deconPair_x__p12_e",
  "deconPair_x__ppe",
  "deconPair_x__pp1",
  "deconPair_x__ppp12",
  "deconPair_x__le",
  "deconPair_x__l7",
  "deconPair_x__l12",
  "deconPair_x__l12_3",
  "deconPair_x__lle",
  "deconPair_x__l_e",
  "deconPair_x__l_p12",
  "deconPair_x__p_l12",
  "deconPair_x__pl1",
  "deconPair_y__e",
  "deconPair_y__n0",
  "deconPair_y__n1",
  "deconPair_y__p1",
  "deconPair_y__p12",
  "deconPair_y__p123",
  "deconPair_y__pee",
  "deconPair_y__pe1",
  "deconPair_y__p1e",
  "deconPair_y__p12_3",
  "deconPair_y__p12_34",
  "deconPair_y__pe_12",
  "deconPair_y__ppe1_2",
  "deconPair_y__p12_e",
  "deconPair_y__ppe",
  "deconPair_y__pp1",
  "deconPair_y__ppp12",
  "deconPair_y__le",
  "deconPair_y__l7",
  "deconPair_y__l12",
  "deconPair_y__l12_3",
  "deconPair_y__lle",
  "deconPair_y__l_e",
  "deconPair_y__l_p12",
  "deconPair_y__p_l12",
  "deconPair_y__pl1",
  "deconPairSpread_x__e",
  "deconPairSpread_x__n0",
  "deconPairSpread_x__n1",
  "deconPairSpread_x__p1",
  "deconPairSpread_x__p12",
  "deconPairSpread_x__p123",
  "deconPairSpread_x__pee",
  "deconPairSpread_x__pe1",
  "deconPairSpread_x__p1e",
  "deconPairSpread_x__p12_3",
  "deconPairSpread_x__p12_34",
  "deconPairSpread_x__pe_12",
  "deconPairSpread_x__ppe1_2",
  "deconPairSpread_x__p12_e",
  "deconPairSpread_x__ppe",
  "deconPairSpread_x__pp1",
  "deconPairSpread_x__ppp12",
  "deconPairSpread_x__le",
  "deconPairSpread_x__l7",
  "deconPairSpread_x__l12",
  "deconPairSpread_x__l12_3",
  "deconPairSpread_x__lle",
  "deconPairSpread_x__l_e",
  "deconPairSpread_x__l_p12",
  "deconPairSpread_x__p_l12",
  "deconPairSpread_x__pl1",
  "deconCollect_t__e",
  "deconCollect_t__n0",
  "deconCollect_t__n1",
  "deconCollect_t__p1",
  "deconCollect_t__p12",
  "deconCollect_t__p123",
  "deconCollect_t__pee",
  "deconCollect_t__pe1",
  "deconCollect_t__p1e",
  "deconCollect_t__p12_3",
  "deconCollect_t__p12_34",
  "deconCollect_t__pe_12",
  "deconCollect_t__ppe1_2",
  "deconCollect_t__p12_e",
  "deconCollect_t__ppe",
  "deconCollect_t__pp1",
  "deconCollect_t__ppp12",
  "deconCollect_t__le",
  "deconCollect_t__l7",
  "deconCollect_t__l12",
  "deconCollect_t__l12_3",
  "deconCollect_t__lle",
  "deconCollect_t__l_e",
  "deconCollect_t__l_p12",
  "deconCollect_t__p_l12",
  "deconCollect_t__pl1",
  "deconCollectSpread_t__e",
  "deconCollectSpread_t__n0",
  "deconCollectSpread_t__n1",
  "deconCollectSpread_t__p1",
  "deconCollectSpread_t__p12",
  "deconCollectSpread_t__p123",
  "deconCollectSpread_t__pee",
  "deconCollectSpread_t__pe1",
  "deconCollectSpread_t__p1e",
  "deconCollectSpread_t__p12_3",
  "deconCollectSpread_t__p12_34",
  "deconCollectSpread_t__pe_12",
  "deconCollectSpread_t__ppe1_2",
  "deconCollectSpread_t__p12_e",
  "deconCollectSpread_t__ppe",
  "deconCollectSpread_t__pp1",
  "deconCollectSpread_t__ppp12",
  "deconCollectSpread_t__le",
  "deconCollectSpread_t__l7",
  "deconCollectSpread_t__l12",
  "deconCollectSpread_t__l12_3",
  "deconCollectSpread_t__lle",
  "deconCollectSpread_t__l_e",
  "deconCollectSpread_t__l_p12",
  "deconCollectSpread_t__p_l12",
  "deconCollectSpread_t__pl1",
  "deconPrefix_p__e",
  "deconPrefix_p__n0",
  "deconPrefix_p__n1",
  "deconPrefix_p__p1",
  "deconPrefix_p__p12",
  "deconPrefix_p__p123",
  "deconPrefix_p__pee",
  "deconPrefix_p__pe1",
  "deconPrefix_p__p1e",
  "deconPrefix_p__p12_3",
  "deconPrefix_p__p12_34",
  "deconPrefix_p__pe_12",
  "deconPrefix_p__ppe1_2",
  "deconPrefix_p__p12_e",
  "deconPrefix_p__ppe",
  "deconPrefix_p__pp1",
  "deconPrefix_p__ppp12",
  "deconPrefix_p__le",
  "deconPrefix_p__l7",
  "deconPrefix_p__l12",
  "deconPrefix_p__l12_3",
  "deconPrefix_p__lle",
  "deconPrefix_p__l_e",
  "deconPrefix_p__l_p12",
  "deconPrefix_p__p_l12",
  "deconPrefix_p__pl1",
  "deconPrefix_z__e",
  "deconPrefix_z__n0",
  "deconPrefix_z__n1",
  "deconPrefix_z__p1",
  "deconPrefix_z__p12",
  "deconPrefix_z__p123",
  "deconPrefix_z__pee",
  "deconPrefix_z__pe1",
  "deconPrefix_z__p1e",
  "deconPrefix_z__p12_3",
  "deconPrefix_z__p12_34",
  "deconPrefix_z__pe_12",
  "deconPrefix_z__ppe1_2",
  "deconPrefix_z__p12_e",
  "deconPrefix_z__ppe",
  "deconPrefix_z__pp1",
  "deconPrefix_z__ppp12",
  "deconPrefix_z__le",
  "deconPrefix_z__l7",
  "deconPrefix_z__l12",
  "deconPrefix_z__l12_3",
  "deconPrefix_z__lle",
  "deconPrefix_z__l_e",
  "deconPrefix_z__l_p12",
  "deconPrefix_z__p_l12",
  "deconPrefix_z__pl1",
  "seqWrapPair__e",
  "seqWrapPair__n0",
  "seqWrapPair__n1",
  "seqWrapPair__p1",
  "seqWrapPair__p12",
  "seqWrapPair__p123",
  "seqWrapPair__pee",
  "seqWrapPair__pe1",
  "seqWrapPair__p1e",
  "seqWrapPair__p12_3",
  "seqWrapPair__p12_34",
  "seqWrapPair__pe_12",
  "seqWrapPair__ppe1_2",
  "seqWrapPair__p12_e",
  "seqWrapPair__ppe",
  "seqWrapPair__pp1",
  "seqWrapPair__ppp12",
  "seqWrapPair__le",
  "seqWrapPair__l7",
  "seqWrapPair__l12",
  "seqWrapPair__l12_3",
  "seqWrapPair__lle",
  "seqWrapPair__l_e",
  "seqWrapPair__l_p12",
  "seqWrapPair__p_l12",
  "seqWrapPair__pl1",
  "seqWrapSolo__e",
  "seqWrapSolo__n0",
  "seqWrapSolo__n1",
  "seqWrapSolo__p1",
  "seqWrapSolo__p12",
  "seqWrapSolo__p123",
  "seqWrapSolo__pee",
  "seqWrapSolo__pe1",
  "seqWrapSolo__p1e",
  "seqWrapSolo__p12_3",
  "seqWrapSolo__p12_34",
  "seqWrapSolo__pe_12",
  "seqWrapSolo__ppe1_2",
  "seqWrapSolo__p12_e",
  "seqWrapSolo__ppe",
  "seqWrapSolo__pp1",
  "seqWrapSolo__ppp12",
  "seqWrapSolo__le",
  "seqWrapSolo__l7",
  "seqWrapSolo__l12",
  "seqWrapSolo__l12_3",
  "seqWrapSolo__lle",
  "seqWrapSolo__l_e",
  "seqWrapSolo__l_p12",
  "seqWrapSolo__p_l12",
  "seqWrapSolo__pl1",
  "spreadRoot__e",
  "spreadRoot__n0",
  "spreadRoot__n1",
  "spreadRoot__p1",
  "spreadRoot__p12",
  "spreadRoot__p123",
  "spreadRoot__pee",
  "spreadRoot__pe1",
  "spreadRoot__p1e",
  "spreadRoot__p12_3",
  "spreadRoot__p12_34",
  "spreadRoot__pe_12",
  "spreadRoot__ppe1_2",
  "spreadRoot__p12_e",
  "spreadRoot__ppe",
  "spreadRoot__pp1",
  "spreadRoot__ppp12",
  "spreadRoot__le",
  "spreadRoot__l7",
  "spreadRoot__l12",
  "spreadRoot__l12_3",
  "spreadRoot__lle",
  "spreadRoot__l_e",
  "spreadRoot__l_p12",
  "spreadRoot__p_l12",
  "spreadRoot__pl1",
  "spreadInSeq__e",
  "spreadInSeq__n0",
  "spreadInSeq__n1",
  "spreadInSeq__p1",
  "spreadInSeq__p12",
  "spreadInSeq__p123",
  "spreadInSeq__pee",
  "spreadInSeq__pe1",
  "spreadInSeq__p1e",
  "spreadInSeq__p12_3",
  "spreadInSeq__p12_34",
  "spreadInSeq__pe_12",
  "spreadInSeq__ppe1_2",
  "spreadInSeq__p12_e",
  "spreadInSeq__ppe",
  "spreadInSeq__pp1",
  "spreadInSeq__ppp12",
  "spreadInSeq__le",
  "spreadInSeq__l7",
  "spreadInSeq__l12",
  "spreadInSeq__l12_3",
  "spreadInSeq__lle",
  "spreadInSeq__l_e",
  "spreadInSeq__l_p12",
  "spreadInSeq__p_l12",
  "spreadInSeq__pl1",
  "count__e",
  "count__n0",
  "count__n1",
  "count__p1",
  "count__p12",
  "count__p123",
  "count__pee",
  "count__pe1",
  "count__p1e",
  "count__p12_3",
  "count__p12_34",
  "count__pe_12",
  "count__ppe1_2",
  "count__p12_e",
  "count__ppe",
  "count__pp1",
  "count__ppp12",
  "count__le",
  "count__l7",
  "count__l12",
  "count__l12_3",
  "count__lle",
  "count__l_e",
  "count__l_p12",
  "count__p_l12",
  "count__pl1",
  "countSpread__e",
  "countSpread__n0",
  "countSpread__n1",
  "countSpread__p1",
  "countSpread__p12",
  "countSpread__p123",
  "countSpread__pee",
  "countSpread__pe1",
  "countSpread__p1e",
  "countSpread__p12_3",
  "countSpread__p12_34",
  "countSpread__pe_12",
  "countSpread__ppe1_2",
  "countSpread__p12_e",
  "countSpread__ppe",
  "countSpread__pp1",
  "countSpread__ppp12",
  "countSpread__le",
  "countSpread__l7",
  "countSpread__l12",
  "countSpread__l12_3",
  "countSpread__lle",
  "countSpread__l_e",
  "countSpread__l_p12",
  "countSpread__p_l12",
  "countSpread__pl1",
  "dotCount__e",
  "dotCount__n0",
  "dotCount__n1",
  "dotCount__p1",
  "dotCount__p12",
  "dotCount__p123",
  "dotCount__pee",
  "dotCount__pe1",
  "dotCount__p1e",
  "dotCount__p12_3",
  "dotCount__p12_34",
  "dotCount__pe_12",
  "dotCount__ppe1_2",
  "dotCount__p12_e",
  "dotCount__ppe",
  "dotCount__pp1",
  "dotCount__ppp12",
  "dotCount__le",
  "dotCount__l7",
  "dotCount__l12",
  "dotCount__l12_3",
  "dotCount__lle",
  "dotCount__l_e",
  "dotCount__l_p12",
  "dotCount__p_l12",
  "dotCount__pl1",
  "literalDotCount__e",
  "literalDotCount__n0",
  "literalDotCount__n1",
  "literalDotCount__p1",
  "literalDotCount__p12",
  "literalDotCount__p123",
  "literalDotCount__pee",
  "literalDotCount__pe1",
  "literalDotCount__p1e",
  "literalDotCount__p12_3",
  "literalDotCount__p12_34",
  "literalDotCount__pe_12",
  "literalDotCount__ppe1_2",
  "literalDotCount__p12_e",
  "literalDotCount__ppe",
  "literalDotCount__pp1",
  "literalDotCount__ppp12",
  "literalDotCount__le",
  "literalDotCount__l7",
  "literalDotCount__l12",
  "literalDotCount__l12_3",
  "literalDotCount__lle",
  "literalDotCount__l_e",
  "literalDotCount__l_p12",
  "literalDotCount__p_l12",
  "literalDotCount__pl1",
  "index0__e",
  "index0__n0",
  "index0__n1",
  "index0__p1",
  "index0__p12",
  "index0__p123",
  "index0__pee",
  "index0__pe1",
  "index0__p1e",
  "index0__p12_3",
  "index0__p12_34",
  "index0__pe_12",
  "index0__ppe1_2",
  "index0__p12_e",
  "index0__ppe",
  "index0__pp1",
  "index0__ppp12",
  "index0__le",
  "index0__l7",
  "index0__l12",
  "index0__l12_3",
  "index0__lle",
  "index0__l_e",
  "index0__l_p12",
  "index0__p_l12",
  "index0__pl1",
  "index1__e",
  "index1__n0",
  "index1__n1",
  "index1__p1",
  "index1__p12",
  "index1__p123",
  "index1__pee",
  "index1__pe1",
  "index1__p1e",
  "index1__p12_3",
  "index1__p12_34",
  "index1__pe_12",
  "index1__ppe1_2",
  "index1__p12_e",
  "index1__ppe",
  "index1__pp1",
  "index1__ppp12",
  "index1__le",
  "index1__l7",
  "index1__l12",
  "index1__l12_3",
  "index1__lle",
  "index1__l_e",
  "index1__l_p12",
  "index1__p_l12",
  "index1__pl1",
  "indexBig__e",
  "indexBig__n0",
  "indexBig__n1",
  "indexBig__p1",
  "indexBig__p12",
  "indexBig__p123",
  "indexBig__pee",
  "indexBig__pe1",
  "indexBig__p1e",
  "indexBig__p12_3",
  "indexBig__p12_34",
  "indexBig__pe_12",
  "indexBig__ppe1_2",
  "indexBig__p12_e",
  "indexBig__ppe",
  "indexBig__pp1",
  "indexBig__ppp12",
  "indexBig__le",
  "indexBig__l7",
  "indexBig__l12",
  "indexBig__l12_3",
  "indexBig__lle",
  "indexBig__l_e",
  "indexBig__l_p12",
  "indexBig__p_l12",
  "indexBig__pl1",
  "eqSelf__e",
  "eqSelf__n0",
  "eqSelf__n1",
  "eqSelf__p1",
  "eqSelf__p12",
  "eqSelf__p123",
  "eqSelf__pee",
  "eqSelf__pe1",
  "eqSelf__p1e",
  "eqSelf__p12_3",
  "eqSelf__p12_34",
  "eqSelf__pe_12",
  "eqSelf__ppe1_2",
  "eqSelf__p12_e",
  "eqSelf__ppe",
  "eqSelf__pp1",
  "eqSelf__ppp12",
  "eqSelf__le",
  "eqSelf__l7",
  "eqSelf__l12",
  "eqSelf__l12_3",
  "eqSelf__lle",
  "eqSelf__l_e",
  "eqSelf__l_p12",
  "eqSelf__p_l12",
  "eqSelf__pl1",
  "neqSelf__e",
  "neqSelf__n0",
  "neqSelf__n1",
  "neqSelf__p1",
  "neqSelf__p12",
  "neqSelf__p123",
  "neqSelf__pee",
  "neqSelf__pe1",
  "neqSelf__p1e",
  "neqSelf__p12_3",
  "neqSelf__p12_34",
  "neqSelf__pe_12",
  "neqSelf__ppe1_2",
  "neqSelf__p12_e",
  "neqSelf__ppe",
  "neqSelf__pp1",
  "neqSelf__ppp12",
  "neqSelf__le",
  "neqSelf__l7",
  "neqSelf__l12",
  "neqSelf__l12_3",
  "neqSelf__lle",
  "neqSelf__l_e",
  "neqSelf__l_p12",
  "neqSelf__p_l12",
  "neqSelf__pl1",
  "eqIdentity__e",
  "eqIdentity__n0",
  "eqIdentity__n1",
  "eqIdentity__p1",
  "eqIdentity__p12",
  "eqIdentity__p123",
  "eqIdentity__pee",
  "eqIdentity__pe1",
  "eqIdentity__p1e",
  "eqIdentity__p12_3",
  "eqIdentity__p12_34",
  "eqIdentity__pe_12",
  "eqIdentity__ppe1_2",
  "eqIdentity__p12_e",
  "eqIdentity__ppe",
  "eqIdentity__pp1",
  "eqIdentity__ppp12",
  "eqIdentity__le",
  "eqIdentity__l7",
  "eqIdentity__l12",
  "eqIdentity__l12_3",
  "eqIdentity__lle",
  "eqIdentity__l_e",
  "eqIdentity__l_p12",
  "eqIdentity__p_l12",
  "eqIdentity__pl1",
  "identity__e",
  "identity__n0",
  "identity__n1",
  "identity__p1",
  "identity__p12",
  "identity__p123",
  "identity__pee",
  "identity__pe1",
  "identity__p1e",
  "identity__p12_3",
  "identity__p12_34",
  "identity__pe_12",
  "identity__ppe1_2",
  "identity__p12_e",
  "identity__ppe",
  "identity__pp1",
  "identity__ppp12",
  "identity__le",
  "identity__l7",
  "identity__l12",
  "identity__l12_3",
  "identity__lle",
  "identity__l_e",
  "identity__l_p12",
  "identity__p_l12",
  "identity__pl1",
  "identityTwice__e",
  "identityTwice__n0",
  "identityTwice__n1",
  "identityTwice__p1",
  "identityTwice__p12",
  "identityTwice__p123",
  "identityTwice__pee",
  "identityTwice__pe1",
  "identityTwice__p1e",
  "identityTwice__p12_3",
  "identityTwice__p12_34",
  "identityTwice__pe_12",
  "identityTwice__ppe1_2",
  "identityTwice__p12_e",
  "identityTwice__ppe",
  "identityTwice__pp1",
  "identityTwice__ppp12",
  "identityTwice__le",
  "identityTwice__l7",
  "identityTwice__l12",
  "identityTwice__l12_3",
  "identityTwice__lle",
  "identityTwice__l_e",
  "identityTwice__l_p12",
  "identityTwice__p_l12",
  "identityTwice__pl1",
  "propChain__e",
  "propChain__n0",
  "propChain__n1",
  "propChain__p1",
  "propChain__p12",
  "propChain__p123",
  "propChain__pee",
  "propChain__pe1",
  "propChain__p1e",
  "propChain__p12_3",
  "propChain__p12_34",
  "propChain__pe_12",
  "propChain__ppe1_2",
  "propChain__p12_e",
  "propChain__ppe",
  "propChain__pp1",
  "propChain__ppp12",
  "propChain__le",
  "propChain__l7",
  "propChain__l12",
  "propChain__l12_3",
  "propChain__lle",
  "propChain__l_e",
  "propChain__l_p12",
  "propChain__p_l12",
  "propChain__pl1",
  "take1__e",
  "take1__n0",
  "take1__n1",
  "take1__p1",
  "take1__p12",
  "take1__p123",
  "take1__pee",
  "take1__pe1",
  "take1__p1e",
  "take1__p12_3",
  "take1__p12_34",
  "take1__pe_12",
  "take1__ppe1_2",
  "take1__p12_e",
  "take1__ppe",
  "take1__pp1",
  "take1__ppp12",
  "take1__le",
  "take1__l7",
  "take1__l12",
  "take1__l12_3",
  "take1__lle",
  "take1__l_e",
  "take1__l_p12",
  "take1__p_l12",
  "take1__pl1",
  "take9__e",
  "take9__n0",
  "take9__n1",
  "take9__p1",
  "take9__p12",
  "take9__p123",
  "take9__pee",
  "take9__pe1",
  "take9__p1e",
  "take9__p12_3",
  "take9__p12_34",
  "take9__pe_12",
  "take9__ppe1_2",
  "take9__p12_e",
  "take9__ppe",
  "take9__pp1",
  "take9__ppp12",
  "take9__le",
  "take9__l7",
  "take9__l12",
  "take9__l12_3",
  "take9__lle",
  "take9__l_e",
  "take9__l_p12",
  "take9__p_l12",
  "take9__pl1",
  "skip1__e",
  "skip1__n0",
  "skip1__n1",
  "skip1__p1",
  "skip1__p12",
  "skip1__p123",
  "skip1__pee",
  "skip1__pe1",
  "skip1__p1e",
  "skip1__p12_3",
  "skip1__p12_34",
  "skip1__pe_12",
  "skip1__ppe1_2",
  "skip1__p12_e",
  "skip1__ppe",
  "skip1__pp1",
  "skip1__ppp12",
  "skip1__le",
  "skip1__l7",
  "skip1__l12",
  "skip1__l12_3",
  "skip1__lle",
  "skip1__l_e",
  "skip1__l_p12",
  "skip1__p_l12",
  "skip1__pl1",
  "distinct__e",
  "distinct__n0",
  "distinct__n1",
  "distinct__p1",
  "distinct__p12",
  "distinct__p123",
  "distinct__pee",
  "distinct__pe1",
  "distinct__p1e",
  "distinct__p12_3",
  "distinct__p12_34",
  "distinct__pe_12",
  "distinct__ppe1_2",
  "distinct__p12_e",
  "distinct__ppe",
  "distinct__pp1",
  "distinct__ppp12",
  "distinct__le",
  "distinct__l7",
  "distinct__l12",
  "distinct__l12_3",
  "distinct__lle",
  "distinct__l_e",
  "distinct__l_p12",
  "distinct__p_l12",
  "distinct__pl1",
  "order__e",
  "order__n0",
  "order__n1",
  "order__p1",
  "order__p12",
  "order__p123",
  "order__pee",
  "order__pe1",
  "order__p1e",
  "order__p12_3",
  "order__p12_34",
  "order__pe_12",
  "order__ppe1_2",
  "order__p12_e",
  "order__ppe",
  "order__pp1",
  "order__ppp12",
  "order__le",
  "order__l7",
  "order__l12",
  "order__l12_3",
  "order__lle",
  "order__l_e",
  "order__l_p12",
  "order__p_l12",
  "order__pl1",
  "mapId__e",
  "mapId__n0",
  "mapId__n1",
  "mapId__p1",
  "mapId__p12",
  "mapId__p123",
  "mapId__pee",
  "mapId__pe1",
  "mapId__p1e",
  "mapId__p12_3",
  "mapId__p12_34",
  "mapId__pe_12",
  "mapId__ppe1_2",
  "mapId__p12_e",
  "mapId__ppe",
  "mapId__pp1",
  "mapId__ppp12",
  "mapId__le",
  "mapId__l7",
  "mapId__l12",
  "mapId__l12_3",
  "mapId__lle",
  "mapId__l_e",
  "mapId__l_p12",
  "mapId__p_l12",
  "mapId__pl1",
  "filterKeep__e",
  "filterKeep__n0",
  "filterKeep__n1",
  "filterKeep__p1",
  "filterKeep__p12",
  "filterKeep__p123",
  "filterKeep__pee",
  "filterKeep__pe1",
  "filterKeep__p1e",
  "filterKeep__p12_3",
  "filterKeep__p12_34",
  "filterKeep__pe_12",
  "filterKeep__ppe1_2",
  "filterKeep__p12_e",
  "filterKeep__ppe",
  "filterKeep__pp1",
  "filterKeep__ppp12",
  "filterKeep__le",
  "filterKeep__l7",
  "filterKeep__l12",
  "filterKeep__l12_3",
  "filterKeep__lle",
  "filterKeep__l_e",
  "filterKeep__l_p12",
  "filterKeep__p_l12",
  "filterKeep__pl1",
  "atoms__e",
  "atoms__n0",
  "atoms__n1",
  "atoms__p1",
  "atoms__p12",
  "atoms__p123",
  "atoms__pee",
  "atoms__pe1",
  "atoms__p1e",
  "atoms__p12_3",
  "atoms__p12_34",
  "atoms__pe_12",
  "atoms__ppe1_2",
  "atoms__p12_e",
  "atoms__ppe",
  "atoms__pp1",
  "atoms__ppp12",
  "atoms__le",
  "atoms__l7",
  "atoms__l12",
  "atoms__l12_3",
  "atoms__lle",
  "atoms__l_e",
  "atoms__l_p12",
  "atoms__p_l12",
  "atoms__pl1",
  "takeCapture__e",
  "takeCapture__n0",
  "takeCapture__n1",
  "takeCapture__p1",
  "takeCapture__p12",
  "takeCapture__p123",
  "takeCapture__pee",
  "takeCapture__pe1",
  "takeCapture__p1e",
  "takeCapture__p12_3",
  "takeCapture__p12_34",
  "takeCapture__pe_12",
  "takeCapture__ppe1_2",
  "takeCapture__p12_e",
  "takeCapture__ppe",
  "takeCapture__pp1",
  "takeCapture__ppp12",
  "takeCapture__le",
  "takeCapture__l7",
  "takeCapture__l12",
  "takeCapture__l12_3",
  "takeCapture__lle",
  "takeCapture__l_e",
  "takeCapture__l_p12",
  "takeCapture__p_l12",
  "takeCapture__pl1",
  "takeIdentity__e",
  "takeIdentity__n0",
  "takeIdentity__n1",
  "takeIdentity__p1",
  "takeIdentity__p12",
  "takeIdentity__p123",
  "takeIdentity__pee",
  "takeIdentity__pe1",
  "takeIdentity__p1e",
  "takeIdentity__p12_3",
  "takeIdentity__p12_34",
  "takeIdentity__pe_12",
  "takeIdentity__ppe1_2",
  "takeIdentity__p12_e",
  "takeIdentity__ppe",
  "takeIdentity__pp1",
  "takeIdentity__ppp12",
  "takeIdentity__le",
  "takeIdentity__l7",
  "takeIdentity__l12",
  "takeIdentity__l12_3",
  "takeIdentity__lle",
  "takeIdentity__l_e",
  "takeIdentity__l_p12",
  "takeIdentity__p_l12",
  "takeIdentity__pl1",
  "takeCount__e",
  "takeCount__n0",
  "takeCount__n1",
  "takeCount__p1",
  "takeCount__p12",
  "takeCount__p123",
  "takeCount__pee",
  "takeCount__pe1",
  "takeCount__p1e",
  "takeCount__p12_3",
  "takeCount__p12_34",
  "takeCount__pe_12",
  "takeCount__ppe1_2",
  "takeCount__p12_e",
  "takeCount__ppe",
  "takeCount__pp1",
  "takeCount__ppp12",
  "takeCount__le",
  "takeCount__l7",
  "takeCount__l12",
  "takeCount__l12_3",
  "takeCount__lle",
  "takeCount__l_e",
  "takeCount__l_p12",
  "takeCount__p_l12",
  "takeCount__pl1",
  "takeVariadic__e",
  "takeVariadic__n0",
  "takeVariadic__n1",
  "takeVariadic__p1",
  "takeVariadic__p12",
  "takeVariadic__p123",
  "takeVariadic__pee",
  "takeVariadic__pe1",
  "takeVariadic__p1e",
  "takeVariadic__p12_3",
  "takeVariadic__p12_34",
  "takeVariadic__pe_12",
  "takeVariadic__ppe1_2",
  "takeVariadic__p12_e",
  "takeVariadic__ppe",
  "takeVariadic__pp1",
  "takeVariadic__ppp12",
  "takeVariadic__le",
  "takeVariadic__l7",
  "takeVariadic__l12",
  "takeVariadic__l12_3",
  "takeVariadic__lle",
  "takeVariadic__l_e",
  "takeVariadic__l_p12",
  "takeVariadic__p_l12",
  "takeVariadic__pl1",
  "special__multiProp",
  "special__multiPropCall",
  "special__multiPropCount",
  "special__multiPropDotCount",
  "special__multiPropDot",
  "special__multiPropIndex0",
  "special__multiPropEq",
  "special__multiVariadic",
  "special__multiVariadicCount",
  "special__variadicEmptyCall",
  "special__variadicFwdSum",
  "special__variadicFwdSpread",
  "special__variadicJoin",
  "special__range13",
  "special__rangeCapture",
  "special__rangeCount",
  "special__rangeIndex0",
  "special__takeOneSurvivorPair",
  "special__takeOneSurvivorPairCount",
  "special__takeOneSurvivorPairEq",
  "special__skipToOnePair",
  "special__distinctEmpties",
  "special__distinctPairsToOne",
  "special__takeEmpties",
  "special__filterOneSurvivor",
  "special__filterOneSurvivorCount",
  "special__filterZeroSurvivors",
  "special__mapPairSwap",
  "special__mapPairSwapOk",
  "special__mapToOne",
  "special__orderSingle",
  "special__orderEmpty",
  "special__atomsNested",
  "special__emptyOpGreater",
  "special__emptyOpPlus",
  "special__emptyOpBoth",
  "special__emptyEqEmpty",
  "special__emptyEqNestedEmpty",
  "special__emptyNeNestedEmpty",
  "special__propBodyEmptySlot",
  "special__rootEmptySlots",
  "special__seqOfSpreadEmpty",
  "special__indexPairInSeq",
  "special__indexEmptyItemRoot",
  "special__indexCapturedEq",
  "special__chainedListIndex",
  "special__listIndexCapturedEq",
  "special__listIndexSelectedKindEqFalse",
  "special__orderIndex0",
  "special__nestedWrittenArg",
  "special__writtenSlotArity",
  "special__mixedSingleGrouped",
  "special__sumEmpty",
  "special__spreadWithSiblingSeqLiteral",
  "special__spreadEmptyBetween",
  "special__rootSpreadExtra",
  "special__spreadOfSpreadSeqLiteral",
  "special__eqSpreadSeqLiteral",
  "special__loopSpreadHistoryFlat",
  "special__ifBranchSeq",
  "special__divZero",
  "special__negativeResult",
  "special__strEq",
  "special__strCount",
  "special__strCapture",
  "special__listSpreadOfSeqProp",
  "special__listSpreadBetween",
  "special__listOfLists",
  "special__listSpreadConcat",
  "special__listMixedSpread",
  "special__listEmptyListSpreadBetween",
  "special__listEmptySeqSpreadBetween",
  "special__listNeSeq",
  "special__listEmptyNeEmptySeq",
  "special__listSingletonNeItem",
  "special__listWrapCanonicalizes",
  "special__listSpreadCaptureRoundTrip",
  "special__listCollectingNotSequenceKind",
  "special__listCollectingCollectsExactList",
  "special__implicitForwardOrdinarySource",
  "special__callbackSingleVariadicMap",
  "special__callbackMixedVariadicRow",
  "special__listInSeqSpreadKeepsList",
  "special__listFixedCallBoundary",
  "special__listVariadicSpreadCall",
  "special__listLoneCollectingAssignment"
]
#guard surfaceCaseIds.length == 1386

/-!
Direct internal-node cases: `Expr.sequenceConstruct` is an INTERNAL node —
the surface parser never produces it and its value evaluation drops `()`
leaves, unlike written parentheses. These cases pin that internal behavior
against the C# evaluator's observations of the same hand-constructed ASTs
(see tests/KatLang.Tests/SequenceConstructContainmentTests.cs and
SemanticExplorerCorpus.InternalNodeCases).
-/
-- internal__sc_e_1: SequenceConstruct[(), 1] drops the () leaf and singleton-collapses
def case_internal__sc_e_1 : Expr :=
  .block (alg [] [] [] [.sequenceConstruct (.emptySequence 0) (.num 1)])
#guard obs case_internal__sc_e_1 == "ok raw=1 n=1"

-- internal__sc_1_e: SequenceConstruct[1, ()] drops the () leaf and singleton-collapses
def case_internal__sc_1_e : Expr :=
  .block (alg [] [] [] [.sequenceConstruct (.num 1) (.emptySequence 0)])
#guard obs case_internal__sc_1_e == "ok raw=1 n=1"

-- internal__sc_e_e: SequenceConstruct[(), ()] drops both () leaves to the empty sequence
def case_internal__sc_e_e : Expr :=
  .block (alg [] [] [] [.sequenceConstruct (.emptySequence 0) (.emptySequence 0)])
#guard obs case_internal__sc_e_e == "ok raw=S[] n=1"

-- internal__sc_p12_e: SequenceConstruct[(1,2), ()] drops () and collapses to the pair
def case_internal__sc_p12_e : Expr :=
  .block (alg [] [] [] [.sequenceConstruct (.block (alg [] [] [] [.num 1, .num 2])) (.emptySequence 0)])
#guard obs case_internal__sc_p12_e == "ok raw=S[1, 2] n=1"

-- internal__sc_e_p12: SequenceConstruct[(), (1,2)] drops () and collapses to the pair
def case_internal__sc_e_p12 : Expr :=
  .block (alg [] [] [] [.sequenceConstruct (.emptySequence 0) (.block (alg [] [] [] [.num 1, .num 2]))])
#guard obs case_internal__sc_e_p12 == "ok raw=S[1, 2] n=1"

-- internal__sc_1_2: SequenceConstruct[1, 2] matches written (1, 2)
def case_internal__sc_1_2 : Expr :=
  .block (alg [] [] [] [.sequenceConstruct (.num 1) (.num 2)])
#guard obs case_internal__sc_1_2 == "ok raw=S[1, 2] n=1"

-- internal__sc_p12_p34: SequenceConstruct of two pairs preserves nested structure
def case_internal__sc_p12_p34 : Expr :=
  .block (alg [] [] [] [.sequenceConstruct (.block (alg [] [] [] [.num 1, .num 2])) (.block (alg [] [] [] [.num 3, .num 4]))])
#guard obs case_internal__sc_p12_p34 == "ok raw=S[S[1, 2], S[3, 4]] n=1"

-- internal__sc_spread_3: SequenceConstruct[(1,2).spread, 3] splices the spread leaf
def case_internal__sc_spread_3 : Expr :=
  .block (alg [] [] [] [.sequenceConstruct (.sequenceSpread (.block (alg [] [] [] [.num 1, .num 2]))) (.num 3)])
#guard obs case_internal__sc_spread_3 == "ok raw=S[1, 2, 3] n=1"

-- internal__sc_count_arg: count of the internal node observes the ()-dropped value
def case_internal__sc_count_arg : Expr :=
  .block (alg [] [] [] [.call (.resolve "count") (alg [] [] [] [.sequenceConstruct (.emptySequence 0) (.num 1)])])
#guard obs case_internal__sc_count_arg == "ok raw=1 n=1"

-- internal__sc_take_collection: a SequenceConstruct collection argument binds like the grouped surface form
def case_internal__sc_take_collection : Expr :=
  .block (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [.sequenceConstruct (.sequenceConstruct (.num 1) (.num 2)) (.num 5), .num 2])])
#guard obs case_internal__sc_take_collection == "ok raw=L[1, 2] n=1"

-- internal__sc_take_collection_empty: () leaf vanishes from a SequenceConstruct collection argument (written parens keep it)
def case_internal__sc_take_collection_empty : Expr :=
  .block (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [.sequenceConstruct (.sequenceConstruct (.emptySequence 0) (.num 1)) (.num 2), .num 2])])
#guard obs case_internal__sc_take_collection_empty == "ok raw=L[1, 2] n=1"

-- internal__sc_take_block_leaf: a nested pair inside a SequenceConstruct collection argument stays one item
def case_internal__sc_take_block_leaf : Expr :=
  .block (alg [] [] [] [.call (.resolve "take") (alg [] [] [] [.sequenceConstruct (.num 1) (.block (alg [] [] [] [.num 2, .num 5])), .num 2])])
#guard obs case_internal__sc_take_block_leaf == "ok raw=L[1, S[2, 5]] n=1"

-- internal__sc_sum_arg: sum of the internal node matches the grouped surface form
def case_internal__sc_sum_arg : Expr :=
  .block (alg [] [] [] [.call (.resolve "sum") (alg [] [] [] [.sequenceConstruct (.num 1) (.num 2)])])
#guard obs case_internal__sc_sum_arg == "ok raw=3 n=1"

/--
Machine-checked internal-node partition count (see the surfaceCaseIds note).
-/
def internalNodeCaseIds : List String := [
  "internal__sc_e_1",
  "internal__sc_1_e",
  "internal__sc_e_e",
  "internal__sc_p12_e",
  "internal__sc_e_p12",
  "internal__sc_1_2",
  "internal__sc_p12_p34",
  "internal__sc_spread_3",
  "internal__sc_count_arg",
  "internal__sc_take_collection",
  "internal__sc_take_collection_empty",
  "internal__sc_take_block_leaf",
  "internal__sc_sum_arg"
]
#guard internalNodeCaseIds.length == 13

-- 13 internal-node cases.
-- Total: 1399 case guards (1386 surface + 13 internal-node).
end SemanticExplorerCases
