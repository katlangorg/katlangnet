import KatLang

/-!
GENERATED FILE - DO NOT EDIT BY HAND.

Differential corpus for the small-state semantic explorer
(tests/KatLang.Tests/SemanticExplorerCorpus.cs). Each case is the Lean AST
construction equivalent to a KatLang source program, and each `#guard` pins
the neutral observation recorded from the C# evaluator. A failing guard is a
Lean/C# divergence on that case.

Partition (machine-checked by the `*CaseIds.length` guards below):
- surface corpus cases: 2286
- excluded parse-level cases (Lean has no surface parser): 42
- Lean-representable surface cases: 2244
- internal-node cases: 14
- total generated guards: 2258 case guards + 2 count guards

Regenerate from the repo root with:
  $env:KATLANG_REGENERATE_SEMANTIC_EXPLORER = "1"
  dotnet test .\KatLang.slnx --filter SemanticExplorerLeanArtifact
-/

namespace SemanticExplorerCases
open KatLang

/-- Neutral raw-structure encoding shared with the C# harness:
    atom -> `1`, string -> `'x'`, Boolean -> `true` / `false`,
    sequence -> `S[a, b]`, empty -> `S[]`, exact list -> `L[a, b]`. -/
partial def neutral : Result -> String
  | .atom n => toString n
  | .str s => "'" ++ s ++ "'"
  | .bool b => Result.boolText b
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
  | .explicitParamsRequireOutput => "explicitParamsRequireOutput"
  | .unresolvedImplicitParams _ => "unresolvedImplicitParams"

/-- Counted variant of `runResultM`: the same declaration identification and root wiring, but keeping the
    root emitted count (`evalAlgOutputCounted` / `evalCounted`), matching the
    C# `Evaluator.RunCounted` observation. -/
def runCountedM (e : Expr) : EvalM CountedResult := do
  let e := (identifyPropertyExpr e).run' 0
  validateExplicitParamOutputInvariantExpr e
  let ctx := { callStack := [preludeAlg], algEnv := [] }
  match e with
  | .algorithmExpr a =>
      let wired := wireToCaller ctx a
      if Algorithm.acceptsZeroSuppliedArguments wired then
        evalZeroArgumentDemandOutputCounted wired ctx []
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
  .algorithmExpr (alg [] [] [] [(.emptySequence 0)])
#guard obs case_root__e == "ok raw=S[] n=1"

-- root__n0: 0
def case_root__n0 : Expr :=
  .algorithmExpr (alg [] [] [] [.num 0])
#guard obs case_root__n0 == "ok raw=0 n=1"

-- root__n1: 1
def case_root__n1 : Expr :=
  .algorithmExpr (alg [] [] [] [.num 1])
#guard obs case_root__n1 == "ok raw=1 n=1"

-- root__bt: true
def case_root__bt : Expr :=
  .algorithmExpr (alg [] [] [] [.boolLiteral true])
#guard obs case_root__bt == "ok raw=true n=1"

-- root__bf: false
def case_root__bf : Expr :=
  .algorithmExpr (alg [] [] [] [.boolLiteral false])
#guard obs case_root__bf == "ok raw=false n=1"

-- root__pbt: (true)
def case_root__pbt : Expr :=
  .algorithmExpr (alg [] [] [] [.boolLiteral true])
#guard obs case_root__pbt == "ok raw=true n=1"

-- root__pbt_e: (true, ())
def case_root__pbt_e : Expr :=
  .algorithmExpr (alg [] [] [] [(.capture [.boolLiteral true, (.emptySequence 0)])])
#guard obs case_root__pbt_e == "ok raw=S[true, S[]] n=1"

-- root__pbt_1: (true, 1)
def case_root__pbt_1 : Expr :=
  .algorithmExpr (alg [] [] [] [(.capture [.boolLiteral true, .num 1])])
#guard obs case_root__pbt_1 == "ok raw=S[true, 1] n=1"

-- root__lbt: [true]
def case_root__lbt : Expr :=
  .algorithmExpr (alg [] [] [] [(.listLiteral [.boolLiteral true])])
#guard obs case_root__lbt == "ok raw=L[true] n=1"

-- root__lbt_bf: [true, false]
def case_root__lbt_bf : Expr :=
  .algorithmExpr (alg [] [] [] [(.listLiteral [.boolLiteral true, .boolLiteral false])])
#guard obs case_root__lbt_bf == "ok raw=L[true, false] n=1"

-- root__lpbt_1: [(true, 1)]
def case_root__lpbt_1 : Expr :=
  .algorithmExpr (alg [] [] [] [(.listLiteral [(.capture [.boolLiteral true, .num 1])])])
#guard obs case_root__lpbt_1 == "ok raw=L[S[true, 1]] n=1"

-- root__p1: (1)
def case_root__p1 : Expr :=
  .algorithmExpr (alg [] [] [] [.num 1])
#guard obs case_root__p1 == "ok raw=1 n=1"

-- root__p12: (1, 2)
def case_root__p12 : Expr :=
  .algorithmExpr (alg [] [] [] [(.capture [.num 1, .num 2])])
#guard obs case_root__p12 == "ok raw=S[1, 2] n=1"

-- root__p123: (1, 2, 3)
def case_root__p123 : Expr :=
  .algorithmExpr (alg [] [] [] [(.capture [.num 1, .num 2, .num 3])])
#guard obs case_root__p123 == "ok raw=S[1, 2, 3] n=1"

-- root__pee: ((), ())
def case_root__pee : Expr :=
  .algorithmExpr (alg [] [] [] [(.capture [(.emptySequence 0), (.emptySequence 0)])])
#guard obs case_root__pee == "ok raw=S[S[], S[]] n=1"

-- root__pe1: ((), 1)
def case_root__pe1 : Expr :=
  .algorithmExpr (alg [] [] [] [(.capture [(.emptySequence 0), .num 1])])
#guard obs case_root__pe1 == "ok raw=S[S[], 1] n=1"

-- root__p1e: (1, ())
def case_root__p1e : Expr :=
  .algorithmExpr (alg [] [] [] [(.capture [.num 1, (.emptySequence 0)])])
#guard obs case_root__p1e == "ok raw=S[1, S[]] n=1"

-- root__p12_3: ((1, 2), 3)
def case_root__p12_3 : Expr :=
  .algorithmExpr (alg [] [] [] [(.capture [(.capture [.num 1, .num 2]), .num 3])])
#guard obs case_root__p12_3 == "ok raw=S[S[1, 2], 3] n=1"

-- root__p12_34: ((1, 2), (3, 4))
def case_root__p12_34 : Expr :=
  .algorithmExpr (alg [] [] [] [(.capture [(.capture [.num 1, .num 2]), (.capture [.num 3, .num 4])])])
#guard obs case_root__p12_34 == "ok raw=S[S[1, 2], S[3, 4]] n=1"

-- root__pe_12: ((), (1, 2))
def case_root__pe_12 : Expr :=
  .algorithmExpr (alg [] [] [] [(.capture [(.emptySequence 0), (.capture [.num 1, .num 2])])])
#guard obs case_root__pe_12 == "ok raw=S[S[], S[1, 2]] n=1"

-- root__ppe1_2: (((), 1), 2)
def case_root__ppe1_2 : Expr :=
  .algorithmExpr (alg [] [] [] [(.capture [(.capture [(.emptySequence 0), .num 1]), .num 2])])
#guard obs case_root__ppe1_2 == "ok raw=S[S[S[], 1], 2] n=1"

-- root__p12_e: ((1, 2), ())
def case_root__p12_e : Expr :=
  .algorithmExpr (alg [] [] [] [(.capture [(.capture [.num 1, .num 2]), (.emptySequence 0)])])
#guard obs case_root__p12_e == "ok raw=S[S[1, 2], S[]] n=1"

-- root__ppe: (())
def case_root__ppe : Expr :=
  .algorithmExpr (alg [] [] [] [(.emptySequence 0)])
#guard obs case_root__ppe == "ok raw=S[] n=1"

-- root__pp1: ((1))
def case_root__pp1 : Expr :=
  .algorithmExpr (alg [] [] [] [.num 1])
#guard obs case_root__pp1 == "ok raw=1 n=1"

-- root__ppp12: (((1, 2)))
def case_root__ppp12 : Expr :=
  .algorithmExpr (alg [] [] [] [(.capture [.num 1, .num 2])])
#guard obs case_root__ppp12 == "ok raw=S[1, 2] n=1"

-- root__le: []
def case_root__le : Expr :=
  .algorithmExpr (alg [] [] [] [(.listLiteral [])])
#guard obs case_root__le == "ok raw=L[] n=1"

-- root__l7: [7]
def case_root__l7 : Expr :=
  .algorithmExpr (alg [] [] [] [(.listLiteral [.num 7])])
#guard obs case_root__l7 == "ok raw=L[7] n=1"

-- root__l12: [1, 2]
def case_root__l12 : Expr :=
  .algorithmExpr (alg [] [] [] [(.listLiteral [.num 1, .num 2])])
#guard obs case_root__l12 == "ok raw=L[1, 2] n=1"

-- root__l12_3: [[1, 2], 3]
def case_root__l12_3 : Expr :=
  .algorithmExpr (alg [] [] [] [(.listLiteral [(.listLiteral [.num 1, .num 2]), .num 3])])
#guard obs case_root__l12_3 == "ok raw=L[L[1, 2], 3] n=1"

-- root__lle: [[]]
def case_root__lle : Expr :=
  .algorithmExpr (alg [] [] [] [(.listLiteral [(.listLiteral [])])])
#guard obs case_root__lle == "ok raw=L[L[]] n=1"

-- root__l_e: [()]
def case_root__l_e : Expr :=
  .algorithmExpr (alg [] [] [] [(.listLiteral [(.emptySequence 0)])])
#guard obs case_root__l_e == "ok raw=L[S[]] n=1"

-- root__l_p12: [(1, 2)]
def case_root__l_p12 : Expr :=
  .algorithmExpr (alg [] [] [] [(.listLiteral [(.capture [.num 1, .num 2])])])
#guard obs case_root__l_p12 == "ok raw=L[S[1, 2]] n=1"

-- root__p_l12: ([1, 2], 3)
def case_root__p_l12 : Expr :=
  .algorithmExpr (alg [] [] [] [(.capture [(.listLiteral [.num 1, .num 2]), .num 3])])
#guard obs case_root__p_l12 == "ok raw=S[L[1, 2], 3] n=1"

-- root__pl1: ([1])
def case_root__pl1 : Expr :=
  .algorithmExpr (alg [] [] [] [(.listLiteral [.num 1])])
#guard obs case_root__pl1 == "ok raw=L[1] n=1"

-- capture__e: x = () \n x
def case_capture__e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.emptySequence 0)])] [.resolve "x"])
#guard obs case_capture__e == "ok raw=S[] n=1"

-- capture__n0: x = 0 \n x
def case_capture__n0 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [.num 0])] [.resolve "x"])
#guard obs case_capture__n0 == "ok raw=0 n=1"

-- capture__n1: x = 1 \n x
def case_capture__n1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [.num 1])] [.resolve "x"])
#guard obs case_capture__n1 == "ok raw=1 n=1"

-- capture__bt: x = true \n x
def case_capture__bt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [.boolLiteral true])] [.resolve "x"])
#guard obs case_capture__bt == "ok raw=true n=1"

-- capture__bf: x = false \n x
def case_capture__bf : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [.boolLiteral false])] [.resolve "x"])
#guard obs case_capture__bf == "ok raw=false n=1"

-- capture__pbt: x = (true) \n x
def case_capture__pbt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [.boolLiteral true])] [.resolve "x"])
#guard obs case_capture__pbt == "ok raw=true n=1"

-- capture__pbt_e: x = (true, ()) \n x
def case_capture__pbt_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [.boolLiteral true, (.emptySequence 0)])])] [.resolve "x"])
#guard obs case_capture__pbt_e == "ok raw=S[true, S[]] n=1"

-- capture__pbt_1: x = (true, 1) \n x
def case_capture__pbt_1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [.boolLiteral true, .num 1])])] [.resolve "x"])
#guard obs case_capture__pbt_1 == "ok raw=S[true, 1] n=1"

-- capture__lbt: x = [true] \n x
def case_capture__lbt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [.boolLiteral true])])] [.resolve "x"])
#guard obs case_capture__lbt == "ok raw=L[true] n=1"

-- capture__lbt_bf: x = [true, false] \n x
def case_capture__lbt_bf : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [.boolLiteral true, .boolLiteral false])])] [.resolve "x"])
#guard obs case_capture__lbt_bf == "ok raw=L[true, false] n=1"

-- capture__lpbt_1: x = [(true, 1)] \n x
def case_capture__lpbt_1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [(.capture [.boolLiteral true, .num 1])])])] [.resolve "x"])
#guard obs case_capture__lpbt_1 == "ok raw=L[S[true, 1]] n=1"

-- capture__p1: x = (1) \n x
def case_capture__p1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [.num 1])] [.resolve "x"])
#guard obs case_capture__p1 == "ok raw=1 n=1"

-- capture__p12: x = (1, 2) \n x
def case_capture__p12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [.num 1, .num 2])])] [.resolve "x"])
#guard obs case_capture__p12 == "ok raw=S[1, 2] n=1"

-- capture__p123: x = (1, 2, 3) \n x
def case_capture__p123 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [.num 1, .num 2, .num 3])])] [.resolve "x"])
#guard obs case_capture__p123 == "ok raw=S[1, 2, 3] n=1"

-- capture__pee: x = ((), ()) \n x
def case_capture__pee : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.emptySequence 0), (.emptySequence 0)])])] [.resolve "x"])
#guard obs case_capture__pee == "ok raw=S[S[], S[]] n=1"

-- capture__pe1: x = ((), 1) \n x
def case_capture__pe1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.emptySequence 0), .num 1])])] [.resolve "x"])
#guard obs case_capture__pe1 == "ok raw=S[S[], 1] n=1"

-- capture__p1e: x = (1, ()) \n x
def case_capture__p1e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [.num 1, (.emptySequence 0)])])] [.resolve "x"])
#guard obs case_capture__p1e == "ok raw=S[1, S[]] n=1"

-- capture__p12_3: x = ((1, 2), 3) \n x
def case_capture__p12_3 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.capture [.num 1, .num 2]), .num 3])])] [.resolve "x"])
#guard obs case_capture__p12_3 == "ok raw=S[S[1, 2], 3] n=1"

-- capture__p12_34: x = ((1, 2), (3, 4)) \n x
def case_capture__p12_34 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.capture [.num 1, .num 2]), (.capture [.num 3, .num 4])])])] [.resolve "x"])
#guard obs case_capture__p12_34 == "ok raw=S[S[1, 2], S[3, 4]] n=1"

-- capture__pe_12: x = ((), (1, 2)) \n x
def case_capture__pe_12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.emptySequence 0), (.capture [.num 1, .num 2])])])] [.resolve "x"])
#guard obs case_capture__pe_12 == "ok raw=S[S[], S[1, 2]] n=1"

-- capture__ppe1_2: x = (((), 1), 2) \n x
def case_capture__ppe1_2 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.capture [(.emptySequence 0), .num 1]), .num 2])])] [.resolve "x"])
#guard obs case_capture__ppe1_2 == "ok raw=S[S[S[], 1], 2] n=1"

-- capture__p12_e: x = ((1, 2), ()) \n x
def case_capture__p12_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.capture [.num 1, .num 2]), (.emptySequence 0)])])] [.resolve "x"])
#guard obs case_capture__p12_e == "ok raw=S[S[1, 2], S[]] n=1"

-- capture__ppe: x = (()) \n x
def case_capture__ppe : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.emptySequence 0)])] [.resolve "x"])
#guard obs case_capture__ppe == "ok raw=S[] n=1"

-- capture__pp1: x = ((1)) \n x
def case_capture__pp1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [.num 1])] [.resolve "x"])
#guard obs case_capture__pp1 == "ok raw=1 n=1"

-- capture__ppp12: x = (((1, 2))) \n x
def case_capture__ppp12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [.num 1, .num 2])])] [.resolve "x"])
#guard obs case_capture__ppp12 == "ok raw=S[1, 2] n=1"

-- capture__le: x = [] \n x
def case_capture__le : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [])])] [.resolve "x"])
#guard obs case_capture__le == "ok raw=L[] n=1"

-- capture__l7: x = [7] \n x
def case_capture__l7 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [.num 7])])] [.resolve "x"])
#guard obs case_capture__l7 == "ok raw=L[7] n=1"

-- capture__l12: x = [1, 2] \n x
def case_capture__l12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [.num 1, .num 2])])] [.resolve "x"])
#guard obs case_capture__l12 == "ok raw=L[1, 2] n=1"

-- capture__l12_3: x = [[1, 2], 3] \n x
def case_capture__l12_3 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [(.listLiteral [.num 1, .num 2]), .num 3])])] [.resolve "x"])
#guard obs case_capture__l12_3 == "ok raw=L[L[1, 2], 3] n=1"

-- capture__lle: x = [[]] \n x
def case_capture__lle : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [(.listLiteral [])])])] [.resolve "x"])
#guard obs case_capture__lle == "ok raw=L[L[]] n=1"

-- capture__l_e: x = [()] \n x
def case_capture__l_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [(.emptySequence 0)])])] [.resolve "x"])
#guard obs case_capture__l_e == "ok raw=L[S[]] n=1"

-- capture__l_p12: x = [(1, 2)] \n x
def case_capture__l_p12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [(.capture [.num 1, .num 2])])])] [.resolve "x"])
#guard obs case_capture__l_p12 == "ok raw=L[S[1, 2]] n=1"

-- capture__p_l12: x = ([1, 2], 3) \n x
def case_capture__p_l12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.listLiteral [.num 1, .num 2]), .num 3])])] [.resolve "x"])
#guard obs case_capture__p_l12 == "ok raw=S[L[1, 2], 3] n=1"

-- capture__pl1: x = ([1]) \n x
def case_capture__pl1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [.num 1])])] [.resolve "x"])
#guard obs case_capture__pl1 == "ok raw=L[1] n=1"

-- captureCall__e: x = () \n x()
def case_captureCall__e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.emptySequence 0)])] [(.call (.resolve "x") [])])
#guard obs case_captureCall__e == "ok raw=S[] n=1"

-- captureCall__n0: x = 0 \n x()
def case_captureCall__n0 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [.num 0])] [(.call (.resolve "x") [])])
#guard obs case_captureCall__n0 == "ok raw=0 n=1"

-- captureCall__n1: x = 1 \n x()
def case_captureCall__n1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [.num 1])] [(.call (.resolve "x") [])])
#guard obs case_captureCall__n1 == "ok raw=1 n=1"

-- captureCall__bt: x = true \n x()
def case_captureCall__bt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [.boolLiteral true])] [(.call (.resolve "x") [])])
#guard obs case_captureCall__bt == "ok raw=true n=1"

-- captureCall__bf: x = false \n x()
def case_captureCall__bf : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [.boolLiteral false])] [(.call (.resolve "x") [])])
#guard obs case_captureCall__bf == "ok raw=false n=1"

-- captureCall__pbt: x = (true) \n x()
def case_captureCall__pbt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [.boolLiteral true])] [(.call (.resolve "x") [])])
#guard obs case_captureCall__pbt == "ok raw=true n=1"

-- captureCall__pbt_e: x = (true, ()) \n x()
def case_captureCall__pbt_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [.boolLiteral true, (.emptySequence 0)])])] [(.call (.resolve "x") [])])
#guard obs case_captureCall__pbt_e == "ok raw=S[true, S[]] n=1"

-- captureCall__pbt_1: x = (true, 1) \n x()
def case_captureCall__pbt_1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [.boolLiteral true, .num 1])])] [(.call (.resolve "x") [])])
#guard obs case_captureCall__pbt_1 == "ok raw=S[true, 1] n=1"

-- captureCall__lbt: x = [true] \n x()
def case_captureCall__lbt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [.boolLiteral true])])] [(.call (.resolve "x") [])])
#guard obs case_captureCall__lbt == "ok raw=L[true] n=1"

-- captureCall__lbt_bf: x = [true, false] \n x()
def case_captureCall__lbt_bf : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [.boolLiteral true, .boolLiteral false])])] [(.call (.resolve "x") [])])
#guard obs case_captureCall__lbt_bf == "ok raw=L[true, false] n=1"

-- captureCall__lpbt_1: x = [(true, 1)] \n x()
def case_captureCall__lpbt_1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [(.capture [.boolLiteral true, .num 1])])])] [(.call (.resolve "x") [])])
#guard obs case_captureCall__lpbt_1 == "ok raw=L[S[true, 1]] n=1"

-- captureCall__p1: x = (1) \n x()
def case_captureCall__p1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [.num 1])] [(.call (.resolve "x") [])])
#guard obs case_captureCall__p1 == "ok raw=1 n=1"

-- captureCall__p12: x = (1, 2) \n x()
def case_captureCall__p12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [.num 1, .num 2])])] [(.call (.resolve "x") [])])
#guard obs case_captureCall__p12 == "ok raw=S[1, 2] n=1"

-- captureCall__p123: x = (1, 2, 3) \n x()
def case_captureCall__p123 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [.num 1, .num 2, .num 3])])] [(.call (.resolve "x") [])])
#guard obs case_captureCall__p123 == "ok raw=S[1, 2, 3] n=1"

-- captureCall__pee: x = ((), ()) \n x()
def case_captureCall__pee : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.emptySequence 0), (.emptySequence 0)])])] [(.call (.resolve "x") [])])
#guard obs case_captureCall__pee == "ok raw=S[S[], S[]] n=1"

-- captureCall__pe1: x = ((), 1) \n x()
def case_captureCall__pe1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.emptySequence 0), .num 1])])] [(.call (.resolve "x") [])])
#guard obs case_captureCall__pe1 == "ok raw=S[S[], 1] n=1"

-- captureCall__p1e: x = (1, ()) \n x()
def case_captureCall__p1e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [.num 1, (.emptySequence 0)])])] [(.call (.resolve "x") [])])
#guard obs case_captureCall__p1e == "ok raw=S[1, S[]] n=1"

-- captureCall__p12_3: x = ((1, 2), 3) \n x()
def case_captureCall__p12_3 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.capture [.num 1, .num 2]), .num 3])])] [(.call (.resolve "x") [])])
#guard obs case_captureCall__p12_3 == "ok raw=S[S[1, 2], 3] n=1"

-- captureCall__p12_34: x = ((1, 2), (3, 4)) \n x()
def case_captureCall__p12_34 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.capture [.num 1, .num 2]), (.capture [.num 3, .num 4])])])] [(.call (.resolve "x") [])])
#guard obs case_captureCall__p12_34 == "ok raw=S[S[1, 2], S[3, 4]] n=1"

-- captureCall__pe_12: x = ((), (1, 2)) \n x()
def case_captureCall__pe_12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.emptySequence 0), (.capture [.num 1, .num 2])])])] [(.call (.resolve "x") [])])
#guard obs case_captureCall__pe_12 == "ok raw=S[S[], S[1, 2]] n=1"

-- captureCall__ppe1_2: x = (((), 1), 2) \n x()
def case_captureCall__ppe1_2 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.capture [(.emptySequence 0), .num 1]), .num 2])])] [(.call (.resolve "x") [])])
#guard obs case_captureCall__ppe1_2 == "ok raw=S[S[S[], 1], 2] n=1"

-- captureCall__p12_e: x = ((1, 2), ()) \n x()
def case_captureCall__p12_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.capture [.num 1, .num 2]), (.emptySequence 0)])])] [(.call (.resolve "x") [])])
#guard obs case_captureCall__p12_e == "ok raw=S[S[1, 2], S[]] n=1"

-- captureCall__ppe: x = (()) \n x()
def case_captureCall__ppe : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.emptySequence 0)])] [(.call (.resolve "x") [])])
#guard obs case_captureCall__ppe == "ok raw=S[] n=1"

-- captureCall__pp1: x = ((1)) \n x()
def case_captureCall__pp1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [.num 1])] [(.call (.resolve "x") [])])
#guard obs case_captureCall__pp1 == "ok raw=1 n=1"

-- captureCall__ppp12: x = (((1, 2))) \n x()
def case_captureCall__ppp12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [.num 1, .num 2])])] [(.call (.resolve "x") [])])
#guard obs case_captureCall__ppp12 == "ok raw=S[1, 2] n=1"

-- captureCall__le: x = [] \n x()
def case_captureCall__le : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [])])] [(.call (.resolve "x") [])])
#guard obs case_captureCall__le == "ok raw=L[] n=1"

-- captureCall__l7: x = [7] \n x()
def case_captureCall__l7 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [.num 7])])] [(.call (.resolve "x") [])])
#guard obs case_captureCall__l7 == "ok raw=L[7] n=1"

-- captureCall__l12: x = [1, 2] \n x()
def case_captureCall__l12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [.num 1, .num 2])])] [(.call (.resolve "x") [])])
#guard obs case_captureCall__l12 == "ok raw=L[1, 2] n=1"

-- captureCall__l12_3: x = [[1, 2], 3] \n x()
def case_captureCall__l12_3 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [(.listLiteral [.num 1, .num 2]), .num 3])])] [(.call (.resolve "x") [])])
#guard obs case_captureCall__l12_3 == "ok raw=L[L[1, 2], 3] n=1"

-- captureCall__lle: x = [[]] \n x()
def case_captureCall__lle : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [(.listLiteral [])])])] [(.call (.resolve "x") [])])
#guard obs case_captureCall__lle == "ok raw=L[L[]] n=1"

-- captureCall__l_e: x = [()] \n x()
def case_captureCall__l_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [(.emptySequence 0)])])] [(.call (.resolve "x") [])])
#guard obs case_captureCall__l_e == "ok raw=L[S[]] n=1"

-- captureCall__l_p12: x = [(1, 2)] \n x()
def case_captureCall__l_p12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [(.capture [.num 1, .num 2])])])] [(.call (.resolve "x") [])])
#guard obs case_captureCall__l_p12 == "ok raw=L[S[1, 2]] n=1"

-- captureCall__p_l12: x = ([1, 2], 3) \n x()
def case_captureCall__p_l12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.listLiteral [.num 1, .num 2]), .num 3])])] [(.call (.resolve "x") [])])
#guard obs case_captureCall__p_l12 == "ok raw=S[L[1, 2], 3] n=1"

-- captureCall__pl1: x = ([1]) \n x()
def case_captureCall__pl1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [.num 1])])] [(.call (.resolve "x") [])])
#guard obs case_captureCall__pl1 == "ok raw=L[1] n=1"

-- dotAccess__e: A = { \n     X = () \n } \n A.X
def case_dotAccess__e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [privateProp "X" (alg [] [] [] [(.emptySequence 0)])] [])] [(.dotCall (.resolve "A") "X" none)])
#guard obs case_dotAccess__e == "ok raw=S[] n=1"

-- dotAccess__n0: A = { \n     X = 0 \n } \n A.X
def case_dotAccess__n0 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [privateProp "X" (alg [] [] [] [.num 0])] [])] [(.dotCall (.resolve "A") "X" none)])
#guard obs case_dotAccess__n0 == "ok raw=0 n=1"

-- dotAccess__n1: A = { \n     X = 1 \n } \n A.X
def case_dotAccess__n1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [privateProp "X" (alg [] [] [] [.num 1])] [])] [(.dotCall (.resolve "A") "X" none)])
#guard obs case_dotAccess__n1 == "ok raw=1 n=1"

-- dotAccess__bt: A = { \n     X = true \n } \n A.X
def case_dotAccess__bt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [privateProp "X" (alg [] [] [] [.boolLiteral true])] [])] [(.dotCall (.resolve "A") "X" none)])
#guard obs case_dotAccess__bt == "ok raw=true n=1"

-- dotAccess__bf: A = { \n     X = false \n } \n A.X
def case_dotAccess__bf : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [privateProp "X" (alg [] [] [] [.boolLiteral false])] [])] [(.dotCall (.resolve "A") "X" none)])
#guard obs case_dotAccess__bf == "ok raw=false n=1"

-- dotAccess__pbt: A = { \n     X = (true) \n } \n A.X
def case_dotAccess__pbt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [privateProp "X" (alg [] [] [] [.boolLiteral true])] [])] [(.dotCall (.resolve "A") "X" none)])
#guard obs case_dotAccess__pbt == "ok raw=true n=1"

-- dotAccess__pbt_e: A = { \n     X = (true, ()) \n } \n A.X
def case_dotAccess__pbt_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [privateProp "X" (alg [] [] [] [(.capture [.boolLiteral true, (.emptySequence 0)])])] [])] [(.dotCall (.resolve "A") "X" none)])
#guard obs case_dotAccess__pbt_e == "ok raw=S[true, S[]] n=1"

-- dotAccess__pbt_1: A = { \n     X = (true, 1) \n } \n A.X
def case_dotAccess__pbt_1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [privateProp "X" (alg [] [] [] [(.capture [.boolLiteral true, .num 1])])] [])] [(.dotCall (.resolve "A") "X" none)])
#guard obs case_dotAccess__pbt_1 == "ok raw=S[true, 1] n=1"

-- dotAccess__lbt: A = { \n     X = [true] \n } \n A.X
def case_dotAccess__lbt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [privateProp "X" (alg [] [] [] [(.listLiteral [.boolLiteral true])])] [])] [(.dotCall (.resolve "A") "X" none)])
#guard obs case_dotAccess__lbt == "ok raw=L[true] n=1"

-- dotAccess__lbt_bf: A = { \n     X = [true, false] \n } \n A.X
def case_dotAccess__lbt_bf : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [privateProp "X" (alg [] [] [] [(.listLiteral [.boolLiteral true, .boolLiteral false])])] [])] [(.dotCall (.resolve "A") "X" none)])
#guard obs case_dotAccess__lbt_bf == "ok raw=L[true, false] n=1"

-- dotAccess__lpbt_1: A = { \n     X = [(true, 1)] \n } \n A.X
def case_dotAccess__lpbt_1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [privateProp "X" (alg [] [] [] [(.listLiteral [(.capture [.boolLiteral true, .num 1])])])] [])] [(.dotCall (.resolve "A") "X" none)])
#guard obs case_dotAccess__lpbt_1 == "ok raw=L[S[true, 1]] n=1"

-- dotAccess__p1: A = { \n     X = (1) \n } \n A.X
def case_dotAccess__p1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [privateProp "X" (alg [] [] [] [.num 1])] [])] [(.dotCall (.resolve "A") "X" none)])
#guard obs case_dotAccess__p1 == "ok raw=1 n=1"

-- dotAccess__p12: A = { \n     X = (1, 2) \n } \n A.X
def case_dotAccess__p12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [privateProp "X" (alg [] [] [] [(.capture [.num 1, .num 2])])] [])] [(.dotCall (.resolve "A") "X" none)])
#guard obs case_dotAccess__p12 == "ok raw=S[1, 2] n=1"

-- dotAccess__p123: A = { \n     X = (1, 2, 3) \n } \n A.X
def case_dotAccess__p123 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [privateProp "X" (alg [] [] [] [(.capture [.num 1, .num 2, .num 3])])] [])] [(.dotCall (.resolve "A") "X" none)])
#guard obs case_dotAccess__p123 == "ok raw=S[1, 2, 3] n=1"

-- dotAccess__pee: A = { \n     X = ((), ()) \n } \n A.X
def case_dotAccess__pee : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [privateProp "X" (alg [] [] [] [(.capture [(.emptySequence 0), (.emptySequence 0)])])] [])] [(.dotCall (.resolve "A") "X" none)])
#guard obs case_dotAccess__pee == "ok raw=S[S[], S[]] n=1"

-- dotAccess__pe1: A = { \n     X = ((), 1) \n } \n A.X
def case_dotAccess__pe1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [privateProp "X" (alg [] [] [] [(.capture [(.emptySequence 0), .num 1])])] [])] [(.dotCall (.resolve "A") "X" none)])
#guard obs case_dotAccess__pe1 == "ok raw=S[S[], 1] n=1"

-- dotAccess__p1e: A = { \n     X = (1, ()) \n } \n A.X
def case_dotAccess__p1e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [privateProp "X" (alg [] [] [] [(.capture [.num 1, (.emptySequence 0)])])] [])] [(.dotCall (.resolve "A") "X" none)])
#guard obs case_dotAccess__p1e == "ok raw=S[1, S[]] n=1"

-- dotAccess__p12_3: A = { \n     X = ((1, 2), 3) \n } \n A.X
def case_dotAccess__p12_3 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [privateProp "X" (alg [] [] [] [(.capture [(.capture [.num 1, .num 2]), .num 3])])] [])] [(.dotCall (.resolve "A") "X" none)])
#guard obs case_dotAccess__p12_3 == "ok raw=S[S[1, 2], 3] n=1"

-- dotAccess__p12_34: A = { \n     X = ((1, 2), (3, 4)) \n } \n A.X
def case_dotAccess__p12_34 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [privateProp "X" (alg [] [] [] [(.capture [(.capture [.num 1, .num 2]), (.capture [.num 3, .num 4])])])] [])] [(.dotCall (.resolve "A") "X" none)])
#guard obs case_dotAccess__p12_34 == "ok raw=S[S[1, 2], S[3, 4]] n=1"

-- dotAccess__pe_12: A = { \n     X = ((), (1, 2)) \n } \n A.X
def case_dotAccess__pe_12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [privateProp "X" (alg [] [] [] [(.capture [(.emptySequence 0), (.capture [.num 1, .num 2])])])] [])] [(.dotCall (.resolve "A") "X" none)])
#guard obs case_dotAccess__pe_12 == "ok raw=S[S[], S[1, 2]] n=1"

-- dotAccess__ppe1_2: A = { \n     X = (((), 1), 2) \n } \n A.X
def case_dotAccess__ppe1_2 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [privateProp "X" (alg [] [] [] [(.capture [(.capture [(.emptySequence 0), .num 1]), .num 2])])] [])] [(.dotCall (.resolve "A") "X" none)])
#guard obs case_dotAccess__ppe1_2 == "ok raw=S[S[S[], 1], 2] n=1"

-- dotAccess__p12_e: A = { \n     X = ((1, 2), ()) \n } \n A.X
def case_dotAccess__p12_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [privateProp "X" (alg [] [] [] [(.capture [(.capture [.num 1, .num 2]), (.emptySequence 0)])])] [])] [(.dotCall (.resolve "A") "X" none)])
#guard obs case_dotAccess__p12_e == "ok raw=S[S[1, 2], S[]] n=1"

-- dotAccess__ppe: A = { \n     X = (()) \n } \n A.X
def case_dotAccess__ppe : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [privateProp "X" (alg [] [] [] [(.emptySequence 0)])] [])] [(.dotCall (.resolve "A") "X" none)])
#guard obs case_dotAccess__ppe == "ok raw=S[] n=1"

-- dotAccess__pp1: A = { \n     X = ((1)) \n } \n A.X
def case_dotAccess__pp1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [privateProp "X" (alg [] [] [] [.num 1])] [])] [(.dotCall (.resolve "A") "X" none)])
#guard obs case_dotAccess__pp1 == "ok raw=1 n=1"

-- dotAccess__ppp12: A = { \n     X = (((1, 2))) \n } \n A.X
def case_dotAccess__ppp12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [privateProp "X" (alg [] [] [] [(.capture [.num 1, .num 2])])] [])] [(.dotCall (.resolve "A") "X" none)])
#guard obs case_dotAccess__ppp12 == "ok raw=S[1, 2] n=1"

-- dotAccess__le: A = { \n     X = [] \n } \n A.X
def case_dotAccess__le : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [privateProp "X" (alg [] [] [] [(.listLiteral [])])] [])] [(.dotCall (.resolve "A") "X" none)])
#guard obs case_dotAccess__le == "ok raw=L[] n=1"

-- dotAccess__l7: A = { \n     X = [7] \n } \n A.X
def case_dotAccess__l7 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [privateProp "X" (alg [] [] [] [(.listLiteral [.num 7])])] [])] [(.dotCall (.resolve "A") "X" none)])
#guard obs case_dotAccess__l7 == "ok raw=L[7] n=1"

-- dotAccess__l12: A = { \n     X = [1, 2] \n } \n A.X
def case_dotAccess__l12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [privateProp "X" (alg [] [] [] [(.listLiteral [.num 1, .num 2])])] [])] [(.dotCall (.resolve "A") "X" none)])
#guard obs case_dotAccess__l12 == "ok raw=L[1, 2] n=1"

-- dotAccess__l12_3: A = { \n     X = [[1, 2], 3] \n } \n A.X
def case_dotAccess__l12_3 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [privateProp "X" (alg [] [] [] [(.listLiteral [(.listLiteral [.num 1, .num 2]), .num 3])])] [])] [(.dotCall (.resolve "A") "X" none)])
#guard obs case_dotAccess__l12_3 == "ok raw=L[L[1, 2], 3] n=1"

-- dotAccess__lle: A = { \n     X = [[]] \n } \n A.X
def case_dotAccess__lle : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [privateProp "X" (alg [] [] [] [(.listLiteral [(.listLiteral [])])])] [])] [(.dotCall (.resolve "A") "X" none)])
#guard obs case_dotAccess__lle == "ok raw=L[L[]] n=1"

-- dotAccess__l_e: A = { \n     X = [()] \n } \n A.X
def case_dotAccess__l_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [privateProp "X" (alg [] [] [] [(.listLiteral [(.emptySequence 0)])])] [])] [(.dotCall (.resolve "A") "X" none)])
#guard obs case_dotAccess__l_e == "ok raw=L[S[]] n=1"

-- dotAccess__l_p12: A = { \n     X = [(1, 2)] \n } \n A.X
def case_dotAccess__l_p12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [privateProp "X" (alg [] [] [] [(.listLiteral [(.capture [.num 1, .num 2])])])] [])] [(.dotCall (.resolve "A") "X" none)])
#guard obs case_dotAccess__l_p12 == "ok raw=L[S[1, 2]] n=1"

-- dotAccess__p_l12: A = { \n     X = ([1, 2], 3) \n } \n A.X
def case_dotAccess__p_l12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [privateProp "X" (alg [] [] [] [(.capture [(.listLiteral [.num 1, .num 2]), .num 3])])] [])] [(.dotCall (.resolve "A") "X" none)])
#guard obs case_dotAccess__p_l12 == "ok raw=S[L[1, 2], 3] n=1"

-- dotAccess__pl1: A = { \n     X = ([1]) \n } \n A.X
def case_dotAccess__pl1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [privateProp "X" (alg [] [] [] [(.listLiteral [.num 1])])] [])] [(.dotCall (.resolve "A") "X" none)])
#guard obs case_dotAccess__pl1 == "ok raw=L[1] n=1"

-- dotAccessCall__e: A = { \n     X = () \n } \n A.X()
def case_dotAccessCall__e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [privateProp "X" (alg [] [] [] [(.emptySequence 0)])] [])] [(.dotCall (.resolve "A") "X" (some []))])
#guard obs case_dotAccessCall__e == "ok raw=S[] n=1"

-- dotAccessCall__n0: A = { \n     X = 0 \n } \n A.X()
def case_dotAccessCall__n0 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [privateProp "X" (alg [] [] [] [.num 0])] [])] [(.dotCall (.resolve "A") "X" (some []))])
#guard obs case_dotAccessCall__n0 == "ok raw=0 n=1"

-- dotAccessCall__n1: A = { \n     X = 1 \n } \n A.X()
def case_dotAccessCall__n1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [privateProp "X" (alg [] [] [] [.num 1])] [])] [(.dotCall (.resolve "A") "X" (some []))])
#guard obs case_dotAccessCall__n1 == "ok raw=1 n=1"

-- dotAccessCall__bt: A = { \n     X = true \n } \n A.X()
def case_dotAccessCall__bt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [privateProp "X" (alg [] [] [] [.boolLiteral true])] [])] [(.dotCall (.resolve "A") "X" (some []))])
#guard obs case_dotAccessCall__bt == "ok raw=true n=1"

-- dotAccessCall__bf: A = { \n     X = false \n } \n A.X()
def case_dotAccessCall__bf : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [privateProp "X" (alg [] [] [] [.boolLiteral false])] [])] [(.dotCall (.resolve "A") "X" (some []))])
#guard obs case_dotAccessCall__bf == "ok raw=false n=1"

-- dotAccessCall__pbt: A = { \n     X = (true) \n } \n A.X()
def case_dotAccessCall__pbt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [privateProp "X" (alg [] [] [] [.boolLiteral true])] [])] [(.dotCall (.resolve "A") "X" (some []))])
#guard obs case_dotAccessCall__pbt == "ok raw=true n=1"

-- dotAccessCall__pbt_e: A = { \n     X = (true, ()) \n } \n A.X()
def case_dotAccessCall__pbt_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [privateProp "X" (alg [] [] [] [(.capture [.boolLiteral true, (.emptySequence 0)])])] [])] [(.dotCall (.resolve "A") "X" (some []))])
#guard obs case_dotAccessCall__pbt_e == "ok raw=S[true, S[]] n=1"

-- dotAccessCall__pbt_1: A = { \n     X = (true, 1) \n } \n A.X()
def case_dotAccessCall__pbt_1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [privateProp "X" (alg [] [] [] [(.capture [.boolLiteral true, .num 1])])] [])] [(.dotCall (.resolve "A") "X" (some []))])
#guard obs case_dotAccessCall__pbt_1 == "ok raw=S[true, 1] n=1"

-- dotAccessCall__lbt: A = { \n     X = [true] \n } \n A.X()
def case_dotAccessCall__lbt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [privateProp "X" (alg [] [] [] [(.listLiteral [.boolLiteral true])])] [])] [(.dotCall (.resolve "A") "X" (some []))])
#guard obs case_dotAccessCall__lbt == "ok raw=L[true] n=1"

-- dotAccessCall__lbt_bf: A = { \n     X = [true, false] \n } \n A.X()
def case_dotAccessCall__lbt_bf : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [privateProp "X" (alg [] [] [] [(.listLiteral [.boolLiteral true, .boolLiteral false])])] [])] [(.dotCall (.resolve "A") "X" (some []))])
#guard obs case_dotAccessCall__lbt_bf == "ok raw=L[true, false] n=1"

-- dotAccessCall__lpbt_1: A = { \n     X = [(true, 1)] \n } \n A.X()
def case_dotAccessCall__lpbt_1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [privateProp "X" (alg [] [] [] [(.listLiteral [(.capture [.boolLiteral true, .num 1])])])] [])] [(.dotCall (.resolve "A") "X" (some []))])
#guard obs case_dotAccessCall__lpbt_1 == "ok raw=L[S[true, 1]] n=1"

-- dotAccessCall__p1: A = { \n     X = (1) \n } \n A.X()
def case_dotAccessCall__p1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [privateProp "X" (alg [] [] [] [.num 1])] [])] [(.dotCall (.resolve "A") "X" (some []))])
#guard obs case_dotAccessCall__p1 == "ok raw=1 n=1"

-- dotAccessCall__p12: A = { \n     X = (1, 2) \n } \n A.X()
def case_dotAccessCall__p12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [privateProp "X" (alg [] [] [] [(.capture [.num 1, .num 2])])] [])] [(.dotCall (.resolve "A") "X" (some []))])
#guard obs case_dotAccessCall__p12 == "ok raw=S[1, 2] n=1"

-- dotAccessCall__p123: A = { \n     X = (1, 2, 3) \n } \n A.X()
def case_dotAccessCall__p123 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [privateProp "X" (alg [] [] [] [(.capture [.num 1, .num 2, .num 3])])] [])] [(.dotCall (.resolve "A") "X" (some []))])
#guard obs case_dotAccessCall__p123 == "ok raw=S[1, 2, 3] n=1"

-- dotAccessCall__pee: A = { \n     X = ((), ()) \n } \n A.X()
def case_dotAccessCall__pee : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [privateProp "X" (alg [] [] [] [(.capture [(.emptySequence 0), (.emptySequence 0)])])] [])] [(.dotCall (.resolve "A") "X" (some []))])
#guard obs case_dotAccessCall__pee == "ok raw=S[S[], S[]] n=1"

-- dotAccessCall__pe1: A = { \n     X = ((), 1) \n } \n A.X()
def case_dotAccessCall__pe1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [privateProp "X" (alg [] [] [] [(.capture [(.emptySequence 0), .num 1])])] [])] [(.dotCall (.resolve "A") "X" (some []))])
#guard obs case_dotAccessCall__pe1 == "ok raw=S[S[], 1] n=1"

-- dotAccessCall__p1e: A = { \n     X = (1, ()) \n } \n A.X()
def case_dotAccessCall__p1e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [privateProp "X" (alg [] [] [] [(.capture [.num 1, (.emptySequence 0)])])] [])] [(.dotCall (.resolve "A") "X" (some []))])
#guard obs case_dotAccessCall__p1e == "ok raw=S[1, S[]] n=1"

-- dotAccessCall__p12_3: A = { \n     X = ((1, 2), 3) \n } \n A.X()
def case_dotAccessCall__p12_3 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [privateProp "X" (alg [] [] [] [(.capture [(.capture [.num 1, .num 2]), .num 3])])] [])] [(.dotCall (.resolve "A") "X" (some []))])
#guard obs case_dotAccessCall__p12_3 == "ok raw=S[S[1, 2], 3] n=1"

-- dotAccessCall__p12_34: A = { \n     X = ((1, 2), (3, 4)) \n } \n A.X()
def case_dotAccessCall__p12_34 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [privateProp "X" (alg [] [] [] [(.capture [(.capture [.num 1, .num 2]), (.capture [.num 3, .num 4])])])] [])] [(.dotCall (.resolve "A") "X" (some []))])
#guard obs case_dotAccessCall__p12_34 == "ok raw=S[S[1, 2], S[3, 4]] n=1"

-- dotAccessCall__pe_12: A = { \n     X = ((), (1, 2)) \n } \n A.X()
def case_dotAccessCall__pe_12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [privateProp "X" (alg [] [] [] [(.capture [(.emptySequence 0), (.capture [.num 1, .num 2])])])] [])] [(.dotCall (.resolve "A") "X" (some []))])
#guard obs case_dotAccessCall__pe_12 == "ok raw=S[S[], S[1, 2]] n=1"

-- dotAccessCall__ppe1_2: A = { \n     X = (((), 1), 2) \n } \n A.X()
def case_dotAccessCall__ppe1_2 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [privateProp "X" (alg [] [] [] [(.capture [(.capture [(.emptySequence 0), .num 1]), .num 2])])] [])] [(.dotCall (.resolve "A") "X" (some []))])
#guard obs case_dotAccessCall__ppe1_2 == "ok raw=S[S[S[], 1], 2] n=1"

-- dotAccessCall__p12_e: A = { \n     X = ((1, 2), ()) \n } \n A.X()
def case_dotAccessCall__p12_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [privateProp "X" (alg [] [] [] [(.capture [(.capture [.num 1, .num 2]), (.emptySequence 0)])])] [])] [(.dotCall (.resolve "A") "X" (some []))])
#guard obs case_dotAccessCall__p12_e == "ok raw=S[S[1, 2], S[]] n=1"

-- dotAccessCall__ppe: A = { \n     X = (()) \n } \n A.X()
def case_dotAccessCall__ppe : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [privateProp "X" (alg [] [] [] [(.emptySequence 0)])] [])] [(.dotCall (.resolve "A") "X" (some []))])
#guard obs case_dotAccessCall__ppe == "ok raw=S[] n=1"

-- dotAccessCall__pp1: A = { \n     X = ((1)) \n } \n A.X()
def case_dotAccessCall__pp1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [privateProp "X" (alg [] [] [] [.num 1])] [])] [(.dotCall (.resolve "A") "X" (some []))])
#guard obs case_dotAccessCall__pp1 == "ok raw=1 n=1"

-- dotAccessCall__ppp12: A = { \n     X = (((1, 2))) \n } \n A.X()
def case_dotAccessCall__ppp12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [privateProp "X" (alg [] [] [] [(.capture [.num 1, .num 2])])] [])] [(.dotCall (.resolve "A") "X" (some []))])
#guard obs case_dotAccessCall__ppp12 == "ok raw=S[1, 2] n=1"

-- dotAccessCall__le: A = { \n     X = [] \n } \n A.X()
def case_dotAccessCall__le : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [privateProp "X" (alg [] [] [] [(.listLiteral [])])] [])] [(.dotCall (.resolve "A") "X" (some []))])
#guard obs case_dotAccessCall__le == "ok raw=L[] n=1"

-- dotAccessCall__l7: A = { \n     X = [7] \n } \n A.X()
def case_dotAccessCall__l7 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [privateProp "X" (alg [] [] [] [(.listLiteral [.num 7])])] [])] [(.dotCall (.resolve "A") "X" (some []))])
#guard obs case_dotAccessCall__l7 == "ok raw=L[7] n=1"

-- dotAccessCall__l12: A = { \n     X = [1, 2] \n } \n A.X()
def case_dotAccessCall__l12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [privateProp "X" (alg [] [] [] [(.listLiteral [.num 1, .num 2])])] [])] [(.dotCall (.resolve "A") "X" (some []))])
#guard obs case_dotAccessCall__l12 == "ok raw=L[1, 2] n=1"

-- dotAccessCall__l12_3: A = { \n     X = [[1, 2], 3] \n } \n A.X()
def case_dotAccessCall__l12_3 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [privateProp "X" (alg [] [] [] [(.listLiteral [(.listLiteral [.num 1, .num 2]), .num 3])])] [])] [(.dotCall (.resolve "A") "X" (some []))])
#guard obs case_dotAccessCall__l12_3 == "ok raw=L[L[1, 2], 3] n=1"

-- dotAccessCall__lle: A = { \n     X = [[]] \n } \n A.X()
def case_dotAccessCall__lle : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [privateProp "X" (alg [] [] [] [(.listLiteral [(.listLiteral [])])])] [])] [(.dotCall (.resolve "A") "X" (some []))])
#guard obs case_dotAccessCall__lle == "ok raw=L[L[]] n=1"

-- dotAccessCall__l_e: A = { \n     X = [()] \n } \n A.X()
def case_dotAccessCall__l_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [privateProp "X" (alg [] [] [] [(.listLiteral [(.emptySequence 0)])])] [])] [(.dotCall (.resolve "A") "X" (some []))])
#guard obs case_dotAccessCall__l_e == "ok raw=L[S[]] n=1"

-- dotAccessCall__l_p12: A = { \n     X = [(1, 2)] \n } \n A.X()
def case_dotAccessCall__l_p12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [privateProp "X" (alg [] [] [] [(.listLiteral [(.capture [.num 1, .num 2])])])] [])] [(.dotCall (.resolve "A") "X" (some []))])
#guard obs case_dotAccessCall__l_p12 == "ok raw=L[S[1, 2]] n=1"

-- dotAccessCall__p_l12: A = { \n     X = ([1, 2], 3) \n } \n A.X()
def case_dotAccessCall__p_l12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [privateProp "X" (alg [] [] [] [(.capture [(.listLiteral [.num 1, .num 2]), .num 3])])] [])] [(.dotCall (.resolve "A") "X" (some []))])
#guard obs case_dotAccessCall__p_l12 == "ok raw=S[L[1, 2], 3] n=1"

-- dotAccessCall__pl1: A = { \n     X = ([1]) \n } \n A.X()
def case_dotAccessCall__pl1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [privateProp "X" (alg [] [] [] [(.listLiteral [.num 1])])] [])] [(.dotCall (.resolve "A") "X" (some []))])
#guard obs case_dotAccessCall__pl1 == "ok raw=L[1] n=1"

-- fixed__e: F(a) = a \n F(())
def case_fixed__e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "F") [(.emptySequence 0)])])
#guard obs case_fixed__e == "ok raw=S[] n=1"

-- fixed__n0: F(a) = a \n F(0)
def case_fixed__n0 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "F") [.num 0])])
#guard obs case_fixed__n0 == "ok raw=0 n=1"

-- fixed__n1: F(a) = a \n F(1)
def case_fixed__n1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "F") [.num 1])])
#guard obs case_fixed__n1 == "ok raw=1 n=1"

-- fixed__bt: F(a) = a \n F(true)
def case_fixed__bt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "F") [.boolLiteral true])])
#guard obs case_fixed__bt == "ok raw=true n=1"

-- fixed__bf: F(a) = a \n F(false)
def case_fixed__bf : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "F") [.boolLiteral false])])
#guard obs case_fixed__bf == "ok raw=false n=1"

-- fixed__pbt: F(a) = a \n F((true))
def case_fixed__pbt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "F") [.boolLiteral true])])
#guard obs case_fixed__pbt == "ok raw=true n=1"

-- fixed__pbt_e: F(a) = a \n F((true, ()))
def case_fixed__pbt_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "F") [(.capture [.boolLiteral true, (.emptySequence 0)])])])
#guard obs case_fixed__pbt_e == "ok raw=S[true, S[]] n=1"

-- fixed__pbt_1: F(a) = a \n F((true, 1))
def case_fixed__pbt_1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "F") [(.capture [.boolLiteral true, .num 1])])])
#guard obs case_fixed__pbt_1 == "ok raw=S[true, 1] n=1"

-- fixed__lbt: F(a) = a \n F([true])
def case_fixed__lbt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "F") [(.listLiteral [.boolLiteral true])])])
#guard obs case_fixed__lbt == "ok raw=L[true] n=1"

-- fixed__lbt_bf: F(a) = a \n F([true, false])
def case_fixed__lbt_bf : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "F") [(.listLiteral [.boolLiteral true, .boolLiteral false])])])
#guard obs case_fixed__lbt_bf == "ok raw=L[true, false] n=1"

-- fixed__lpbt_1: F(a) = a \n F([(true, 1)])
def case_fixed__lpbt_1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "F") [(.listLiteral [(.capture [.boolLiteral true, .num 1])])])])
#guard obs case_fixed__lpbt_1 == "ok raw=L[S[true, 1]] n=1"

-- fixed__p1: F(a) = a \n F((1))
def case_fixed__p1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "F") [.num 1])])
#guard obs case_fixed__p1 == "ok raw=1 n=1"

-- fixed__p12: F(a) = a \n F((1, 2))
def case_fixed__p12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "F") [(.capture [.num 1, .num 2])])])
#guard obs case_fixed__p12 == "ok raw=S[1, 2] n=1"

-- fixed__p123: F(a) = a \n F((1, 2, 3))
def case_fixed__p123 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "F") [(.capture [.num 1, .num 2, .num 3])])])
#guard obs case_fixed__p123 == "ok raw=S[1, 2, 3] n=1"

-- fixed__pee: F(a) = a \n F(((), ()))
def case_fixed__pee : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "F") [(.capture [(.emptySequence 0), (.emptySequence 0)])])])
#guard obs case_fixed__pee == "ok raw=S[S[], S[]] n=1"

-- fixed__pe1: F(a) = a \n F(((), 1))
def case_fixed__pe1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "F") [(.capture [(.emptySequence 0), .num 1])])])
#guard obs case_fixed__pe1 == "ok raw=S[S[], 1] n=1"

-- fixed__p1e: F(a) = a \n F((1, ()))
def case_fixed__p1e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "F") [(.capture [.num 1, (.emptySequence 0)])])])
#guard obs case_fixed__p1e == "ok raw=S[1, S[]] n=1"

-- fixed__p12_3: F(a) = a \n F(((1, 2), 3))
def case_fixed__p12_3 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "F") [(.capture [(.capture [.num 1, .num 2]), .num 3])])])
#guard obs case_fixed__p12_3 == "ok raw=S[S[1, 2], 3] n=1"

-- fixed__p12_34: F(a) = a \n F(((1, 2), (3, 4)))
def case_fixed__p12_34 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "F") [(.capture [(.capture [.num 1, .num 2]), (.capture [.num 3, .num 4])])])])
#guard obs case_fixed__p12_34 == "ok raw=S[S[1, 2], S[3, 4]] n=1"

-- fixed__pe_12: F(a) = a \n F(((), (1, 2)))
def case_fixed__pe_12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "F") [(.capture [(.emptySequence 0), (.capture [.num 1, .num 2])])])])
#guard obs case_fixed__pe_12 == "ok raw=S[S[], S[1, 2]] n=1"

-- fixed__ppe1_2: F(a) = a \n F((((), 1), 2))
def case_fixed__ppe1_2 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "F") [(.capture [(.capture [(.emptySequence 0), .num 1]), .num 2])])])
#guard obs case_fixed__ppe1_2 == "ok raw=S[S[S[], 1], 2] n=1"

-- fixed__p12_e: F(a) = a \n F(((1, 2), ()))
def case_fixed__p12_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "F") [(.capture [(.capture [.num 1, .num 2]), (.emptySequence 0)])])])
#guard obs case_fixed__p12_e == "ok raw=S[S[1, 2], S[]] n=1"

-- fixed__ppe: F(a) = a \n F((()))
def case_fixed__ppe : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "F") [(.emptySequence 0)])])
#guard obs case_fixed__ppe == "ok raw=S[] n=1"

-- fixed__pp1: F(a) = a \n F(((1)))
def case_fixed__pp1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "F") [.num 1])])
#guard obs case_fixed__pp1 == "ok raw=1 n=1"

-- fixed__ppp12: F(a) = a \n F((((1, 2))))
def case_fixed__ppp12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "F") [(.capture [.num 1, .num 2])])])
#guard obs case_fixed__ppp12 == "ok raw=S[1, 2] n=1"

-- fixed__le: F(a) = a \n F([])
def case_fixed__le : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "F") [(.listLiteral [])])])
#guard obs case_fixed__le == "ok raw=L[] n=1"

-- fixed__l7: F(a) = a \n F([7])
def case_fixed__l7 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "F") [(.listLiteral [.num 7])])])
#guard obs case_fixed__l7 == "ok raw=L[7] n=1"

-- fixed__l12: F(a) = a \n F([1, 2])
def case_fixed__l12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "F") [(.listLiteral [.num 1, .num 2])])])
#guard obs case_fixed__l12 == "ok raw=L[1, 2] n=1"

-- fixed__l12_3: F(a) = a \n F([[1, 2], 3])
def case_fixed__l12_3 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "F") [(.listLiteral [(.listLiteral [.num 1, .num 2]), .num 3])])])
#guard obs case_fixed__l12_3 == "ok raw=L[L[1, 2], 3] n=1"

-- fixed__lle: F(a) = a \n F([[]])
def case_fixed__lle : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "F") [(.listLiteral [(.listLiteral [])])])])
#guard obs case_fixed__lle == "ok raw=L[L[]] n=1"

-- fixed__l_e: F(a) = a \n F([()])
def case_fixed__l_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "F") [(.listLiteral [(.emptySequence 0)])])])
#guard obs case_fixed__l_e == "ok raw=L[S[]] n=1"

-- fixed__l_p12: F(a) = a \n F([(1, 2)])
def case_fixed__l_p12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "F") [(.listLiteral [(.capture [.num 1, .num 2])])])])
#guard obs case_fixed__l_p12 == "ok raw=L[S[1, 2]] n=1"

-- fixed__p_l12: F(a) = a \n F(([1, 2], 3))
def case_fixed__p_l12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "F") [(.capture [(.listLiteral [.num 1, .num 2]), .num 3])])])
#guard obs case_fixed__p_l12 == "ok raw=S[L[1, 2], 3] n=1"

-- fixed__pl1: F(a) = a \n F(([1]))
def case_fixed__pl1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "F") [(.listLiteral [.num 1])])])
#guard obs case_fixed__pl1 == "ok raw=L[1] n=1"

-- fixedSpread__e: F(a) = a \n F(()*)
def case_fixedSpread__e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.emptySequence 0))])])
#guard obs case_fixedSpread__e == "err arity"

-- fixedSpread__n0: F(a) = a \n F(0*)
def case_fixedSpread__n0 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.num 0))])])
#guard obs case_fixedSpread__n0 == "ok raw=0 n=1"

-- fixedSpread__n1: F(a) = a \n F(1*)
def case_fixedSpread__n1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.num 1))])])
#guard obs case_fixedSpread__n1 == "ok raw=1 n=1"

-- fixedSpread__bt: F(a) = a \n F(true*)
def case_fixedSpread__bt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.boolLiteral true))])])
#guard obs case_fixedSpread__bt == "ok raw=true n=1"

-- fixedSpread__bf: F(a) = a \n F(false*)
def case_fixedSpread__bf : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.boolLiteral false))])])
#guard obs case_fixedSpread__bf == "ok raw=false n=1"

-- fixedSpread__pbt: F(a) = a \n F((true)*)
def case_fixedSpread__pbt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.boolLiteral true))])])
#guard obs case_fixedSpread__pbt == "ok raw=true n=1"

-- fixedSpread__pbt_e: F(a) = a \n F((true, ())*)
def case_fixedSpread__pbt_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.capture [.boolLiteral true, (.emptySequence 0)]))])])
#guard obs case_fixedSpread__pbt_e == "err arity"

-- fixedSpread__pbt_1: F(a) = a \n F((true, 1)*)
def case_fixedSpread__pbt_1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.capture [.boolLiteral true, .num 1]))])])
#guard obs case_fixedSpread__pbt_1 == "err arity"

-- fixedSpread__lbt: F(a) = a \n F([true]*)
def case_fixedSpread__lbt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.listLiteral [.boolLiteral true]))])])
#guard obs case_fixedSpread__lbt == "ok raw=true n=1"

-- fixedSpread__lbt_bf: F(a) = a \n F([true, false]*)
def case_fixedSpread__lbt_bf : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.listLiteral [.boolLiteral true, .boolLiteral false]))])])
#guard obs case_fixedSpread__lbt_bf == "err arity"

-- fixedSpread__lpbt_1: F(a) = a \n F([(true, 1)]*)
def case_fixedSpread__lpbt_1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.listLiteral [(.capture [.boolLiteral true, .num 1])]))])])
#guard obs case_fixedSpread__lpbt_1 == "ok raw=S[true, 1] n=1"

-- fixedSpread__p1: F(a) = a \n F((1)*)
def case_fixedSpread__p1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.num 1))])])
#guard obs case_fixedSpread__p1 == "ok raw=1 n=1"

-- fixedSpread__p12: F(a) = a \n F((1, 2)*)
def case_fixedSpread__p12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.capture [.num 1, .num 2]))])])
#guard obs case_fixedSpread__p12 == "err arity"

-- fixedSpread__p123: F(a) = a \n F((1, 2, 3)*)
def case_fixedSpread__p123 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.capture [.num 1, .num 2, .num 3]))])])
#guard obs case_fixedSpread__p123 == "err arity"

-- fixedSpread__pee: F(a) = a \n F(((), ())*)
def case_fixedSpread__pee : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.capture [(.emptySequence 0), (.emptySequence 0)]))])])
#guard obs case_fixedSpread__pee == "err arity"

-- fixedSpread__pe1: F(a) = a \n F(((), 1)*)
def case_fixedSpread__pe1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.capture [(.emptySequence 0), .num 1]))])])
#guard obs case_fixedSpread__pe1 == "err arity"

-- fixedSpread__p1e: F(a) = a \n F((1, ())*)
def case_fixedSpread__p1e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.capture [.num 1, (.emptySequence 0)]))])])
#guard obs case_fixedSpread__p1e == "err arity"

-- fixedSpread__p12_3: F(a) = a \n F(((1, 2), 3)*)
def case_fixedSpread__p12_3 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.capture [(.capture [.num 1, .num 2]), .num 3]))])])
#guard obs case_fixedSpread__p12_3 == "err arity"

-- fixedSpread__p12_34: F(a) = a \n F(((1, 2), (3, 4))*)
def case_fixedSpread__p12_34 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.capture [(.capture [.num 1, .num 2]), (.capture [.num 3, .num 4])]))])])
#guard obs case_fixedSpread__p12_34 == "err arity"

-- fixedSpread__pe_12: F(a) = a \n F(((), (1, 2))*)
def case_fixedSpread__pe_12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.capture [(.emptySequence 0), (.capture [.num 1, .num 2])]))])])
#guard obs case_fixedSpread__pe_12 == "err arity"

-- fixedSpread__ppe1_2: F(a) = a \n F((((), 1), 2)*)
def case_fixedSpread__ppe1_2 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.capture [(.capture [(.emptySequence 0), .num 1]), .num 2]))])])
#guard obs case_fixedSpread__ppe1_2 == "err arity"

-- fixedSpread__p12_e: F(a) = a \n F(((1, 2), ())*)
def case_fixedSpread__p12_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.capture [(.capture [.num 1, .num 2]), (.emptySequence 0)]))])])
#guard obs case_fixedSpread__p12_e == "err arity"

-- fixedSpread__ppe: F(a) = a \n F((())*)
def case_fixedSpread__ppe : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.emptySequence 0))])])
#guard obs case_fixedSpread__ppe == "err arity"

-- fixedSpread__pp1: F(a) = a \n F(((1))*)
def case_fixedSpread__pp1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.num 1))])])
#guard obs case_fixedSpread__pp1 == "ok raw=1 n=1"

-- fixedSpread__ppp12: F(a) = a \n F((((1, 2)))*)
def case_fixedSpread__ppp12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.capture [.num 1, .num 2]))])])
#guard obs case_fixedSpread__ppp12 == "err arity"

-- fixedSpread__le: F(a) = a \n F([]*)
def case_fixedSpread__le : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.listLiteral []))])])
#guard obs case_fixedSpread__le == "err arity"

-- fixedSpread__l7: F(a) = a \n F([7]*)
def case_fixedSpread__l7 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.listLiteral [.num 7]))])])
#guard obs case_fixedSpread__l7 == "ok raw=7 n=1"

-- fixedSpread__l12: F(a) = a \n F([1, 2]*)
def case_fixedSpread__l12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.listLiteral [.num 1, .num 2]))])])
#guard obs case_fixedSpread__l12 == "err arity"

-- fixedSpread__l12_3: F(a) = a \n F([[1, 2], 3]*)
def case_fixedSpread__l12_3 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.listLiteral [(.listLiteral [.num 1, .num 2]), .num 3]))])])
#guard obs case_fixedSpread__l12_3 == "err arity"

-- fixedSpread__lle: F(a) = a \n F([[]]*)
def case_fixedSpread__lle : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.listLiteral [(.listLiteral [])]))])])
#guard obs case_fixedSpread__lle == "ok raw=L[] n=1"

-- fixedSpread__l_e: F(a) = a \n F([()]*)
def case_fixedSpread__l_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.listLiteral [(.emptySequence 0)]))])])
#guard obs case_fixedSpread__l_e == "ok raw=S[] n=1"

-- fixedSpread__l_p12: F(a) = a \n F([(1, 2)]*)
def case_fixedSpread__l_p12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.listLiteral [(.capture [.num 1, .num 2])]))])])
#guard obs case_fixedSpread__l_p12 == "ok raw=S[1, 2] n=1"

-- fixedSpread__p_l12: F(a) = a \n F(([1, 2], 3)*)
def case_fixedSpread__p_l12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.capture [(.listLiteral [.num 1, .num 2]), .num 3]))])])
#guard obs case_fixedSpread__p_l12 == "err arity"

-- fixedSpread__pl1: F(a) = a \n F(([1])*)
def case_fixedSpread__pl1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.listLiteral [.num 1]))])])
#guard obs case_fixedSpread__pl1 == "ok raw=1 n=1"

-- collecting__e: F(*a) = a \n F(())
def case_collecting__e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.emptySequence 0)])])
#guard obs case_collecting__e == "ok raw=L[S[]] n=1"

-- collecting__n0: F(*a) = a \n F(0)
def case_collecting__n0 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [.num 0])])
#guard obs case_collecting__n0 == "ok raw=L[0] n=1"

-- collecting__n1: F(*a) = a \n F(1)
def case_collecting__n1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [.num 1])])
#guard obs case_collecting__n1 == "ok raw=L[1] n=1"

-- collecting__bt: F(*a) = a \n F(true)
def case_collecting__bt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [.boolLiteral true])])
#guard obs case_collecting__bt == "ok raw=L[true] n=1"

-- collecting__bf: F(*a) = a \n F(false)
def case_collecting__bf : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [.boolLiteral false])])
#guard obs case_collecting__bf == "ok raw=L[false] n=1"

-- collecting__pbt: F(*a) = a \n F((true))
def case_collecting__pbt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [.boolLiteral true])])
#guard obs case_collecting__pbt == "ok raw=L[true] n=1"

-- collecting__pbt_e: F(*a) = a \n F((true, ()))
def case_collecting__pbt_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.capture [.boolLiteral true, (.emptySequence 0)])])])
#guard obs case_collecting__pbt_e == "ok raw=L[S[true, S[]]] n=1"

-- collecting__pbt_1: F(*a) = a \n F((true, 1))
def case_collecting__pbt_1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.capture [.boolLiteral true, .num 1])])])
#guard obs case_collecting__pbt_1 == "ok raw=L[S[true, 1]] n=1"

-- collecting__lbt: F(*a) = a \n F([true])
def case_collecting__lbt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.listLiteral [.boolLiteral true])])])
#guard obs case_collecting__lbt == "ok raw=L[L[true]] n=1"

-- collecting__lbt_bf: F(*a) = a \n F([true, false])
def case_collecting__lbt_bf : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.listLiteral [.boolLiteral true, .boolLiteral false])])])
#guard obs case_collecting__lbt_bf == "ok raw=L[L[true, false]] n=1"

-- collecting__lpbt_1: F(*a) = a \n F([(true, 1)])
def case_collecting__lpbt_1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.listLiteral [(.capture [.boolLiteral true, .num 1])])])])
#guard obs case_collecting__lpbt_1 == "ok raw=L[L[S[true, 1]]] n=1"

-- collecting__p1: F(*a) = a \n F((1))
def case_collecting__p1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [.num 1])])
#guard obs case_collecting__p1 == "ok raw=L[1] n=1"

-- collecting__p12: F(*a) = a \n F((1, 2))
def case_collecting__p12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.capture [.num 1, .num 2])])])
#guard obs case_collecting__p12 == "ok raw=L[S[1, 2]] n=1"

-- collecting__p123: F(*a) = a \n F((1, 2, 3))
def case_collecting__p123 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.capture [.num 1, .num 2, .num 3])])])
#guard obs case_collecting__p123 == "ok raw=L[S[1, 2, 3]] n=1"

-- collecting__pee: F(*a) = a \n F(((), ()))
def case_collecting__pee : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.capture [(.emptySequence 0), (.emptySequence 0)])])])
#guard obs case_collecting__pee == "ok raw=L[S[S[], S[]]] n=1"

-- collecting__pe1: F(*a) = a \n F(((), 1))
def case_collecting__pe1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.capture [(.emptySequence 0), .num 1])])])
#guard obs case_collecting__pe1 == "ok raw=L[S[S[], 1]] n=1"

-- collecting__p1e: F(*a) = a \n F((1, ()))
def case_collecting__p1e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.capture [.num 1, (.emptySequence 0)])])])
#guard obs case_collecting__p1e == "ok raw=L[S[1, S[]]] n=1"

-- collecting__p12_3: F(*a) = a \n F(((1, 2), 3))
def case_collecting__p12_3 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.capture [(.capture [.num 1, .num 2]), .num 3])])])
#guard obs case_collecting__p12_3 == "ok raw=L[S[S[1, 2], 3]] n=1"

-- collecting__p12_34: F(*a) = a \n F(((1, 2), (3, 4)))
def case_collecting__p12_34 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.capture [(.capture [.num 1, .num 2]), (.capture [.num 3, .num 4])])])])
#guard obs case_collecting__p12_34 == "ok raw=L[S[S[1, 2], S[3, 4]]] n=1"

-- collecting__pe_12: F(*a) = a \n F(((), (1, 2)))
def case_collecting__pe_12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.capture [(.emptySequence 0), (.capture [.num 1, .num 2])])])])
#guard obs case_collecting__pe_12 == "ok raw=L[S[S[], S[1, 2]]] n=1"

-- collecting__ppe1_2: F(*a) = a \n F((((), 1), 2))
def case_collecting__ppe1_2 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.capture [(.capture [(.emptySequence 0), .num 1]), .num 2])])])
#guard obs case_collecting__ppe1_2 == "ok raw=L[S[S[S[], 1], 2]] n=1"

-- collecting__p12_e: F(*a) = a \n F(((1, 2), ()))
def case_collecting__p12_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.capture [(.capture [.num 1, .num 2]), (.emptySequence 0)])])])
#guard obs case_collecting__p12_e == "ok raw=L[S[S[1, 2], S[]]] n=1"

-- collecting__ppe: F(*a) = a \n F((()))
def case_collecting__ppe : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.emptySequence 0)])])
#guard obs case_collecting__ppe == "ok raw=L[S[]] n=1"

-- collecting__pp1: F(*a) = a \n F(((1)))
def case_collecting__pp1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [.num 1])])
#guard obs case_collecting__pp1 == "ok raw=L[1] n=1"

-- collecting__ppp12: F(*a) = a \n F((((1, 2))))
def case_collecting__ppp12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.capture [.num 1, .num 2])])])
#guard obs case_collecting__ppp12 == "ok raw=L[S[1, 2]] n=1"

-- collecting__le: F(*a) = a \n F([])
def case_collecting__le : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.listLiteral [])])])
#guard obs case_collecting__le == "ok raw=L[L[]] n=1"

-- collecting__l7: F(*a) = a \n F([7])
def case_collecting__l7 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.listLiteral [.num 7])])])
#guard obs case_collecting__l7 == "ok raw=L[L[7]] n=1"

-- collecting__l12: F(*a) = a \n F([1, 2])
def case_collecting__l12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.listLiteral [.num 1, .num 2])])])
#guard obs case_collecting__l12 == "ok raw=L[L[1, 2]] n=1"

-- collecting__l12_3: F(*a) = a \n F([[1, 2], 3])
def case_collecting__l12_3 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.listLiteral [(.listLiteral [.num 1, .num 2]), .num 3])])])
#guard obs case_collecting__l12_3 == "ok raw=L[L[L[1, 2], 3]] n=1"

-- collecting__lle: F(*a) = a \n F([[]])
def case_collecting__lle : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.listLiteral [(.listLiteral [])])])])
#guard obs case_collecting__lle == "ok raw=L[L[L[]]] n=1"

-- collecting__l_e: F(*a) = a \n F([()])
def case_collecting__l_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.listLiteral [(.emptySequence 0)])])])
#guard obs case_collecting__l_e == "ok raw=L[L[S[]]] n=1"

-- collecting__l_p12: F(*a) = a \n F([(1, 2)])
def case_collecting__l_p12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.listLiteral [(.capture [.num 1, .num 2])])])])
#guard obs case_collecting__l_p12 == "ok raw=L[L[S[1, 2]]] n=1"

-- collecting__p_l12: F(*a) = a \n F(([1, 2], 3))
def case_collecting__p_l12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.capture [(.listLiteral [.num 1, .num 2]), .num 3])])])
#guard obs case_collecting__p_l12 == "ok raw=L[S[L[1, 2], 3]] n=1"

-- collecting__pl1: F(*a) = a \n F(([1]))
def case_collecting__pl1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.listLiteral [.num 1])])])
#guard obs case_collecting__pl1 == "ok raw=L[L[1]] n=1"

-- collectingSpread__e: F(*a) = a \n F(()*)
def case_collectingSpread__e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.emptySequence 0))])])
#guard obs case_collectingSpread__e == "ok raw=L[] n=1"

-- collectingSpread__n0: F(*a) = a \n F(0*)
def case_collectingSpread__n0 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.num 0))])])
#guard obs case_collectingSpread__n0 == "ok raw=L[0] n=1"

-- collectingSpread__n1: F(*a) = a \n F(1*)
def case_collectingSpread__n1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.num 1))])])
#guard obs case_collectingSpread__n1 == "ok raw=L[1] n=1"

-- collectingSpread__bt: F(*a) = a \n F(true*)
def case_collectingSpread__bt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.boolLiteral true))])])
#guard obs case_collectingSpread__bt == "ok raw=L[true] n=1"

-- collectingSpread__bf: F(*a) = a \n F(false*)
def case_collectingSpread__bf : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.boolLiteral false))])])
#guard obs case_collectingSpread__bf == "ok raw=L[false] n=1"

-- collectingSpread__pbt: F(*a) = a \n F((true)*)
def case_collectingSpread__pbt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.boolLiteral true))])])
#guard obs case_collectingSpread__pbt == "ok raw=L[true] n=1"

-- collectingSpread__pbt_e: F(*a) = a \n F((true, ())*)
def case_collectingSpread__pbt_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.capture [.boolLiteral true, (.emptySequence 0)]))])])
#guard obs case_collectingSpread__pbt_e == "ok raw=L[true, S[]] n=1"

-- collectingSpread__pbt_1: F(*a) = a \n F((true, 1)*)
def case_collectingSpread__pbt_1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.capture [.boolLiteral true, .num 1]))])])
#guard obs case_collectingSpread__pbt_1 == "ok raw=L[true, 1] n=1"

-- collectingSpread__lbt: F(*a) = a \n F([true]*)
def case_collectingSpread__lbt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.listLiteral [.boolLiteral true]))])])
#guard obs case_collectingSpread__lbt == "ok raw=L[true] n=1"

-- collectingSpread__lbt_bf: F(*a) = a \n F([true, false]*)
def case_collectingSpread__lbt_bf : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.listLiteral [.boolLiteral true, .boolLiteral false]))])])
#guard obs case_collectingSpread__lbt_bf == "ok raw=L[true, false] n=1"

-- collectingSpread__lpbt_1: F(*a) = a \n F([(true, 1)]*)
def case_collectingSpread__lpbt_1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.listLiteral [(.capture [.boolLiteral true, .num 1])]))])])
#guard obs case_collectingSpread__lpbt_1 == "ok raw=L[S[true, 1]] n=1"

-- collectingSpread__p1: F(*a) = a \n F((1)*)
def case_collectingSpread__p1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.num 1))])])
#guard obs case_collectingSpread__p1 == "ok raw=L[1] n=1"

-- collectingSpread__p12: F(*a) = a \n F((1, 2)*)
def case_collectingSpread__p12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.capture [.num 1, .num 2]))])])
#guard obs case_collectingSpread__p12 == "ok raw=L[1, 2] n=1"

-- collectingSpread__p123: F(*a) = a \n F((1, 2, 3)*)
def case_collectingSpread__p123 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.capture [.num 1, .num 2, .num 3]))])])
#guard obs case_collectingSpread__p123 == "ok raw=L[1, 2, 3] n=1"

-- collectingSpread__pee: F(*a) = a \n F(((), ())*)
def case_collectingSpread__pee : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.capture [(.emptySequence 0), (.emptySequence 0)]))])])
#guard obs case_collectingSpread__pee == "ok raw=L[S[], S[]] n=1"

-- collectingSpread__pe1: F(*a) = a \n F(((), 1)*)
def case_collectingSpread__pe1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.capture [(.emptySequence 0), .num 1]))])])
#guard obs case_collectingSpread__pe1 == "ok raw=L[S[], 1] n=1"

-- collectingSpread__p1e: F(*a) = a \n F((1, ())*)
def case_collectingSpread__p1e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.capture [.num 1, (.emptySequence 0)]))])])
#guard obs case_collectingSpread__p1e == "ok raw=L[1, S[]] n=1"

-- collectingSpread__p12_3: F(*a) = a \n F(((1, 2), 3)*)
def case_collectingSpread__p12_3 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.capture [(.capture [.num 1, .num 2]), .num 3]))])])
#guard obs case_collectingSpread__p12_3 == "ok raw=L[S[1, 2], 3] n=1"

-- collectingSpread__p12_34: F(*a) = a \n F(((1, 2), (3, 4))*)
def case_collectingSpread__p12_34 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.capture [(.capture [.num 1, .num 2]), (.capture [.num 3, .num 4])]))])])
#guard obs case_collectingSpread__p12_34 == "ok raw=L[S[1, 2], S[3, 4]] n=1"

-- collectingSpread__pe_12: F(*a) = a \n F(((), (1, 2))*)
def case_collectingSpread__pe_12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.capture [(.emptySequence 0), (.capture [.num 1, .num 2])]))])])
#guard obs case_collectingSpread__pe_12 == "ok raw=L[S[], S[1, 2]] n=1"

-- collectingSpread__ppe1_2: F(*a) = a \n F((((), 1), 2)*)
def case_collectingSpread__ppe1_2 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.capture [(.capture [(.emptySequence 0), .num 1]), .num 2]))])])
#guard obs case_collectingSpread__ppe1_2 == "ok raw=L[S[S[], 1], 2] n=1"

-- collectingSpread__p12_e: F(*a) = a \n F(((1, 2), ())*)
def case_collectingSpread__p12_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.capture [(.capture [.num 1, .num 2]), (.emptySequence 0)]))])])
#guard obs case_collectingSpread__p12_e == "ok raw=L[S[1, 2], S[]] n=1"

-- collectingSpread__ppe: F(*a) = a \n F((())*)
def case_collectingSpread__ppe : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.emptySequence 0))])])
#guard obs case_collectingSpread__ppe == "ok raw=L[] n=1"

-- collectingSpread__pp1: F(*a) = a \n F(((1))*)
def case_collectingSpread__pp1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.num 1))])])
#guard obs case_collectingSpread__pp1 == "ok raw=L[1] n=1"

-- collectingSpread__ppp12: F(*a) = a \n F((((1, 2)))*)
def case_collectingSpread__ppp12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.capture [.num 1, .num 2]))])])
#guard obs case_collectingSpread__ppp12 == "ok raw=L[1, 2] n=1"

-- collectingSpread__le: F(*a) = a \n F([]*)
def case_collectingSpread__le : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.listLiteral []))])])
#guard obs case_collectingSpread__le == "ok raw=L[] n=1"

-- collectingSpread__l7: F(*a) = a \n F([7]*)
def case_collectingSpread__l7 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.listLiteral [.num 7]))])])
#guard obs case_collectingSpread__l7 == "ok raw=L[7] n=1"

-- collectingSpread__l12: F(*a) = a \n F([1, 2]*)
def case_collectingSpread__l12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.listLiteral [.num 1, .num 2]))])])
#guard obs case_collectingSpread__l12 == "ok raw=L[1, 2] n=1"

-- collectingSpread__l12_3: F(*a) = a \n F([[1, 2], 3]*)
def case_collectingSpread__l12_3 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.listLiteral [(.listLiteral [.num 1, .num 2]), .num 3]))])])
#guard obs case_collectingSpread__l12_3 == "ok raw=L[L[1, 2], 3] n=1"

-- collectingSpread__lle: F(*a) = a \n F([[]]*)
def case_collectingSpread__lle : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.listLiteral [(.listLiteral [])]))])])
#guard obs case_collectingSpread__lle == "ok raw=L[L[]] n=1"

-- collectingSpread__l_e: F(*a) = a \n F([()]*)
def case_collectingSpread__l_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.listLiteral [(.emptySequence 0)]))])])
#guard obs case_collectingSpread__l_e == "ok raw=L[S[]] n=1"

-- collectingSpread__l_p12: F(*a) = a \n F([(1, 2)]*)
def case_collectingSpread__l_p12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.listLiteral [(.capture [.num 1, .num 2])]))])])
#guard obs case_collectingSpread__l_p12 == "ok raw=L[S[1, 2]] n=1"

-- collectingSpread__p_l12: F(*a) = a \n F(([1, 2], 3)*)
def case_collectingSpread__p_l12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.capture [(.listLiteral [.num 1, .num 2]), .num 3]))])])
#guard obs case_collectingSpread__p_l12 == "ok raw=L[L[1, 2], 3] n=1"

-- collectingSpread__pl1: F(*a) = a \n F(([1])*)
def case_collectingSpread__pl1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.listLiteral [.num 1]))])])
#guard obs case_collectingSpread__pl1 == "ok raw=L[1] n=1"

-- collectingViaProp__e: F(*a) = a \n x = () \n F(x)
def case_collectingViaProp__e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.emptySequence 0)]), privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [.resolve "x"])])
#guard obs case_collectingViaProp__e == "ok raw=L[S[]] n=1"

-- collectingViaProp__n0: F(*a) = a \n x = 0 \n F(x)
def case_collectingViaProp__n0 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [.num 0]), privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [.resolve "x"])])
#guard obs case_collectingViaProp__n0 == "ok raw=L[0] n=1"

-- collectingViaProp__n1: F(*a) = a \n x = 1 \n F(x)
def case_collectingViaProp__n1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [.num 1]), privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [.resolve "x"])])
#guard obs case_collectingViaProp__n1 == "ok raw=L[1] n=1"

-- collectingViaProp__bt: F(*a) = a \n x = true \n F(x)
def case_collectingViaProp__bt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [.boolLiteral true]), privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [.resolve "x"])])
#guard obs case_collectingViaProp__bt == "ok raw=L[true] n=1"

-- collectingViaProp__bf: F(*a) = a \n x = false \n F(x)
def case_collectingViaProp__bf : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [.boolLiteral false]), privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [.resolve "x"])])
#guard obs case_collectingViaProp__bf == "ok raw=L[false] n=1"

-- collectingViaProp__pbt: F(*a) = a \n x = (true) \n F(x)
def case_collectingViaProp__pbt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [.boolLiteral true]), privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [.resolve "x"])])
#guard obs case_collectingViaProp__pbt == "ok raw=L[true] n=1"

-- collectingViaProp__pbt_e: F(*a) = a \n x = (true, ()) \n F(x)
def case_collectingViaProp__pbt_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [.boolLiteral true, (.emptySequence 0)])]), privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [.resolve "x"])])
#guard obs case_collectingViaProp__pbt_e == "ok raw=L[S[true, S[]]] n=1"

-- collectingViaProp__pbt_1: F(*a) = a \n x = (true, 1) \n F(x)
def case_collectingViaProp__pbt_1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [.boolLiteral true, .num 1])]), privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [.resolve "x"])])
#guard obs case_collectingViaProp__pbt_1 == "ok raw=L[S[true, 1]] n=1"

-- collectingViaProp__lbt: F(*a) = a \n x = [true] \n F(x)
def case_collectingViaProp__lbt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [.boolLiteral true])]), privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [.resolve "x"])])
#guard obs case_collectingViaProp__lbt == "ok raw=L[L[true]] n=1"

-- collectingViaProp__lbt_bf: F(*a) = a \n x = [true, false] \n F(x)
def case_collectingViaProp__lbt_bf : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [.boolLiteral true, .boolLiteral false])]), privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [.resolve "x"])])
#guard obs case_collectingViaProp__lbt_bf == "ok raw=L[L[true, false]] n=1"

-- collectingViaProp__lpbt_1: F(*a) = a \n x = [(true, 1)] \n F(x)
def case_collectingViaProp__lpbt_1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [(.capture [.boolLiteral true, .num 1])])]), privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [.resolve "x"])])
#guard obs case_collectingViaProp__lpbt_1 == "ok raw=L[L[S[true, 1]]] n=1"

-- collectingViaProp__p1: F(*a) = a \n x = (1) \n F(x)
def case_collectingViaProp__p1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [.num 1]), privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [.resolve "x"])])
#guard obs case_collectingViaProp__p1 == "ok raw=L[1] n=1"

-- collectingViaProp__p12: F(*a) = a \n x = (1, 2) \n F(x)
def case_collectingViaProp__p12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [.num 1, .num 2])]), privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [.resolve "x"])])
#guard obs case_collectingViaProp__p12 == "ok raw=L[S[1, 2]] n=1"

-- collectingViaProp__p123: F(*a) = a \n x = (1, 2, 3) \n F(x)
def case_collectingViaProp__p123 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [.num 1, .num 2, .num 3])]), privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [.resolve "x"])])
#guard obs case_collectingViaProp__p123 == "ok raw=L[S[1, 2, 3]] n=1"

-- collectingViaProp__pee: F(*a) = a \n x = ((), ()) \n F(x)
def case_collectingViaProp__pee : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.emptySequence 0), (.emptySequence 0)])]), privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [.resolve "x"])])
#guard obs case_collectingViaProp__pee == "ok raw=L[S[S[], S[]]] n=1"

-- collectingViaProp__pe1: F(*a) = a \n x = ((), 1) \n F(x)
def case_collectingViaProp__pe1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.emptySequence 0), .num 1])]), privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [.resolve "x"])])
#guard obs case_collectingViaProp__pe1 == "ok raw=L[S[S[], 1]] n=1"

-- collectingViaProp__p1e: F(*a) = a \n x = (1, ()) \n F(x)
def case_collectingViaProp__p1e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [.num 1, (.emptySequence 0)])]), privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [.resolve "x"])])
#guard obs case_collectingViaProp__p1e == "ok raw=L[S[1, S[]]] n=1"

-- collectingViaProp__p12_3: F(*a) = a \n x = ((1, 2), 3) \n F(x)
def case_collectingViaProp__p12_3 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.capture [.num 1, .num 2]), .num 3])]), privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [.resolve "x"])])
#guard obs case_collectingViaProp__p12_3 == "ok raw=L[S[S[1, 2], 3]] n=1"

-- collectingViaProp__p12_34: F(*a) = a \n x = ((1, 2), (3, 4)) \n F(x)
def case_collectingViaProp__p12_34 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.capture [.num 1, .num 2]), (.capture [.num 3, .num 4])])]), privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [.resolve "x"])])
#guard obs case_collectingViaProp__p12_34 == "ok raw=L[S[S[1, 2], S[3, 4]]] n=1"

-- collectingViaProp__pe_12: F(*a) = a \n x = ((), (1, 2)) \n F(x)
def case_collectingViaProp__pe_12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.emptySequence 0), (.capture [.num 1, .num 2])])]), privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [.resolve "x"])])
#guard obs case_collectingViaProp__pe_12 == "ok raw=L[S[S[], S[1, 2]]] n=1"

-- collectingViaProp__ppe1_2: F(*a) = a \n x = (((), 1), 2) \n F(x)
def case_collectingViaProp__ppe1_2 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.capture [(.emptySequence 0), .num 1]), .num 2])]), privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [.resolve "x"])])
#guard obs case_collectingViaProp__ppe1_2 == "ok raw=L[S[S[S[], 1], 2]] n=1"

-- collectingViaProp__p12_e: F(*a) = a \n x = ((1, 2), ()) \n F(x)
def case_collectingViaProp__p12_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.capture [.num 1, .num 2]), (.emptySequence 0)])]), privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [.resolve "x"])])
#guard obs case_collectingViaProp__p12_e == "ok raw=L[S[S[1, 2], S[]]] n=1"

-- collectingViaProp__ppe: F(*a) = a \n x = (()) \n F(x)
def case_collectingViaProp__ppe : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.emptySequence 0)]), privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [.resolve "x"])])
#guard obs case_collectingViaProp__ppe == "ok raw=L[S[]] n=1"

-- collectingViaProp__pp1: F(*a) = a \n x = ((1)) \n F(x)
def case_collectingViaProp__pp1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [.num 1]), privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [.resolve "x"])])
#guard obs case_collectingViaProp__pp1 == "ok raw=L[1] n=1"

-- collectingViaProp__ppp12: F(*a) = a \n x = (((1, 2))) \n F(x)
def case_collectingViaProp__ppp12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [.num 1, .num 2])]), privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [.resolve "x"])])
#guard obs case_collectingViaProp__ppp12 == "ok raw=L[S[1, 2]] n=1"

-- collectingViaProp__le: F(*a) = a \n x = [] \n F(x)
def case_collectingViaProp__le : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [])]), privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [.resolve "x"])])
#guard obs case_collectingViaProp__le == "ok raw=L[L[]] n=1"

-- collectingViaProp__l7: F(*a) = a \n x = [7] \n F(x)
def case_collectingViaProp__l7 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [.num 7])]), privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [.resolve "x"])])
#guard obs case_collectingViaProp__l7 == "ok raw=L[L[7]] n=1"

-- collectingViaProp__l12: F(*a) = a \n x = [1, 2] \n F(x)
def case_collectingViaProp__l12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [.num 1, .num 2])]), privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [.resolve "x"])])
#guard obs case_collectingViaProp__l12 == "ok raw=L[L[1, 2]] n=1"

-- collectingViaProp__l12_3: F(*a) = a \n x = [[1, 2], 3] \n F(x)
def case_collectingViaProp__l12_3 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [(.listLiteral [.num 1, .num 2]), .num 3])]), privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [.resolve "x"])])
#guard obs case_collectingViaProp__l12_3 == "ok raw=L[L[L[1, 2], 3]] n=1"

-- collectingViaProp__lle: F(*a) = a \n x = [[]] \n F(x)
def case_collectingViaProp__lle : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [(.listLiteral [])])]), privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [.resolve "x"])])
#guard obs case_collectingViaProp__lle == "ok raw=L[L[L[]]] n=1"

-- collectingViaProp__l_e: F(*a) = a \n x = [()] \n F(x)
def case_collectingViaProp__l_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [(.emptySequence 0)])]), privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [.resolve "x"])])
#guard obs case_collectingViaProp__l_e == "ok raw=L[L[S[]]] n=1"

-- collectingViaProp__l_p12: F(*a) = a \n x = [(1, 2)] \n F(x)
def case_collectingViaProp__l_p12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [(.capture [.num 1, .num 2])])]), privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [.resolve "x"])])
#guard obs case_collectingViaProp__l_p12 == "ok raw=L[L[S[1, 2]]] n=1"

-- collectingViaProp__p_l12: F(*a) = a \n x = ([1, 2], 3) \n F(x)
def case_collectingViaProp__p_l12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.listLiteral [.num 1, .num 2]), .num 3])]), privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [.resolve "x"])])
#guard obs case_collectingViaProp__p_l12 == "ok raw=L[S[L[1, 2], 3]] n=1"

-- collectingViaProp__pl1: F(*a) = a \n x = ([1]) \n F(x)
def case_collectingViaProp__pl1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [.num 1])]), privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [.resolve "x"])])
#guard obs case_collectingViaProp__pl1 == "ok raw=L[L[1]] n=1"

-- dotCollectingViaProp__e: F(*a) = a \n x = () \n x.F
def case_dotCollectingViaProp__e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.emptySequence 0)]), privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.dotCall (.resolve "x") "F" none)])
#guard obs case_dotCollectingViaProp__e == "ok raw=L[S[]] n=1"

-- dotCollectingViaProp__n0: F(*a) = a \n x = 0 \n x.F
def case_dotCollectingViaProp__n0 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [.num 0]), privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.dotCall (.resolve "x") "F" none)])
#guard obs case_dotCollectingViaProp__n0 == "ok raw=L[0] n=1"

-- dotCollectingViaProp__n1: F(*a) = a \n x = 1 \n x.F
def case_dotCollectingViaProp__n1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [.num 1]), privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.dotCall (.resolve "x") "F" none)])
#guard obs case_dotCollectingViaProp__n1 == "ok raw=L[1] n=1"

-- dotCollectingViaProp__bt: F(*a) = a \n x = true \n x.F
def case_dotCollectingViaProp__bt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [.boolLiteral true]), privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.dotCall (.resolve "x") "F" none)])
#guard obs case_dotCollectingViaProp__bt == "ok raw=L[true] n=1"

-- dotCollectingViaProp__bf: F(*a) = a \n x = false \n x.F
def case_dotCollectingViaProp__bf : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [.boolLiteral false]), privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.dotCall (.resolve "x") "F" none)])
#guard obs case_dotCollectingViaProp__bf == "ok raw=L[false] n=1"

-- dotCollectingViaProp__pbt: F(*a) = a \n x = (true) \n x.F
def case_dotCollectingViaProp__pbt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [.boolLiteral true]), privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.dotCall (.resolve "x") "F" none)])
#guard obs case_dotCollectingViaProp__pbt == "ok raw=L[true] n=1"

-- dotCollectingViaProp__pbt_e: F(*a) = a \n x = (true, ()) \n x.F
def case_dotCollectingViaProp__pbt_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [.boolLiteral true, (.emptySequence 0)])]), privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.dotCall (.resolve "x") "F" none)])
#guard obs case_dotCollectingViaProp__pbt_e == "ok raw=L[S[true, S[]]] n=1"

-- dotCollectingViaProp__pbt_1: F(*a) = a \n x = (true, 1) \n x.F
def case_dotCollectingViaProp__pbt_1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [.boolLiteral true, .num 1])]), privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.dotCall (.resolve "x") "F" none)])
#guard obs case_dotCollectingViaProp__pbt_1 == "ok raw=L[S[true, 1]] n=1"

-- dotCollectingViaProp__lbt: F(*a) = a \n x = [true] \n x.F
def case_dotCollectingViaProp__lbt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [.boolLiteral true])]), privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.dotCall (.resolve "x") "F" none)])
#guard obs case_dotCollectingViaProp__lbt == "ok raw=L[L[true]] n=1"

-- dotCollectingViaProp__lbt_bf: F(*a) = a \n x = [true, false] \n x.F
def case_dotCollectingViaProp__lbt_bf : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [.boolLiteral true, .boolLiteral false])]), privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.dotCall (.resolve "x") "F" none)])
#guard obs case_dotCollectingViaProp__lbt_bf == "ok raw=L[L[true, false]] n=1"

-- dotCollectingViaProp__lpbt_1: F(*a) = a \n x = [(true, 1)] \n x.F
def case_dotCollectingViaProp__lpbt_1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [(.capture [.boolLiteral true, .num 1])])]), privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.dotCall (.resolve "x") "F" none)])
#guard obs case_dotCollectingViaProp__lpbt_1 == "ok raw=L[L[S[true, 1]]] n=1"

-- dotCollectingViaProp__p1: F(*a) = a \n x = (1) \n x.F
def case_dotCollectingViaProp__p1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [.num 1]), privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.dotCall (.resolve "x") "F" none)])
#guard obs case_dotCollectingViaProp__p1 == "ok raw=L[1] n=1"

-- dotCollectingViaProp__p12: F(*a) = a \n x = (1, 2) \n x.F
def case_dotCollectingViaProp__p12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [.num 1, .num 2])]), privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.dotCall (.resolve "x") "F" none)])
#guard obs case_dotCollectingViaProp__p12 == "ok raw=L[S[1, 2]] n=1"

-- dotCollectingViaProp__p123: F(*a) = a \n x = (1, 2, 3) \n x.F
def case_dotCollectingViaProp__p123 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [.num 1, .num 2, .num 3])]), privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.dotCall (.resolve "x") "F" none)])
#guard obs case_dotCollectingViaProp__p123 == "ok raw=L[S[1, 2, 3]] n=1"

-- dotCollectingViaProp__pee: F(*a) = a \n x = ((), ()) \n x.F
def case_dotCollectingViaProp__pee : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.emptySequence 0), (.emptySequence 0)])]), privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.dotCall (.resolve "x") "F" none)])
#guard obs case_dotCollectingViaProp__pee == "ok raw=L[S[S[], S[]]] n=1"

-- dotCollectingViaProp__pe1: F(*a) = a \n x = ((), 1) \n x.F
def case_dotCollectingViaProp__pe1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.emptySequence 0), .num 1])]), privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.dotCall (.resolve "x") "F" none)])
#guard obs case_dotCollectingViaProp__pe1 == "ok raw=L[S[S[], 1]] n=1"

-- dotCollectingViaProp__p1e: F(*a) = a \n x = (1, ()) \n x.F
def case_dotCollectingViaProp__p1e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [.num 1, (.emptySequence 0)])]), privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.dotCall (.resolve "x") "F" none)])
#guard obs case_dotCollectingViaProp__p1e == "ok raw=L[S[1, S[]]] n=1"

-- dotCollectingViaProp__p12_3: F(*a) = a \n x = ((1, 2), 3) \n x.F
def case_dotCollectingViaProp__p12_3 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.capture [.num 1, .num 2]), .num 3])]), privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.dotCall (.resolve "x") "F" none)])
#guard obs case_dotCollectingViaProp__p12_3 == "ok raw=L[S[S[1, 2], 3]] n=1"

-- dotCollectingViaProp__p12_34: F(*a) = a \n x = ((1, 2), (3, 4)) \n x.F
def case_dotCollectingViaProp__p12_34 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.capture [.num 1, .num 2]), (.capture [.num 3, .num 4])])]), privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.dotCall (.resolve "x") "F" none)])
#guard obs case_dotCollectingViaProp__p12_34 == "ok raw=L[S[S[1, 2], S[3, 4]]] n=1"

-- dotCollectingViaProp__pe_12: F(*a) = a \n x = ((), (1, 2)) \n x.F
def case_dotCollectingViaProp__pe_12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.emptySequence 0), (.capture [.num 1, .num 2])])]), privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.dotCall (.resolve "x") "F" none)])
#guard obs case_dotCollectingViaProp__pe_12 == "ok raw=L[S[S[], S[1, 2]]] n=1"

-- dotCollectingViaProp__ppe1_2: F(*a) = a \n x = (((), 1), 2) \n x.F
def case_dotCollectingViaProp__ppe1_2 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.capture [(.emptySequence 0), .num 1]), .num 2])]), privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.dotCall (.resolve "x") "F" none)])
#guard obs case_dotCollectingViaProp__ppe1_2 == "ok raw=L[S[S[S[], 1], 2]] n=1"

-- dotCollectingViaProp__p12_e: F(*a) = a \n x = ((1, 2), ()) \n x.F
def case_dotCollectingViaProp__p12_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.capture [.num 1, .num 2]), (.emptySequence 0)])]), privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.dotCall (.resolve "x") "F" none)])
#guard obs case_dotCollectingViaProp__p12_e == "ok raw=L[S[S[1, 2], S[]]] n=1"

-- dotCollectingViaProp__ppe: F(*a) = a \n x = (()) \n x.F
def case_dotCollectingViaProp__ppe : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.emptySequence 0)]), privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.dotCall (.resolve "x") "F" none)])
#guard obs case_dotCollectingViaProp__ppe == "ok raw=L[S[]] n=1"

-- dotCollectingViaProp__pp1: F(*a) = a \n x = ((1)) \n x.F
def case_dotCollectingViaProp__pp1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [.num 1]), privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.dotCall (.resolve "x") "F" none)])
#guard obs case_dotCollectingViaProp__pp1 == "ok raw=L[1] n=1"

-- dotCollectingViaProp__ppp12: F(*a) = a \n x = (((1, 2))) \n x.F
def case_dotCollectingViaProp__ppp12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [.num 1, .num 2])]), privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.dotCall (.resolve "x") "F" none)])
#guard obs case_dotCollectingViaProp__ppp12 == "ok raw=L[S[1, 2]] n=1"

-- dotCollectingViaProp__le: F(*a) = a \n x = [] \n x.F
def case_dotCollectingViaProp__le : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [])]), privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.dotCall (.resolve "x") "F" none)])
#guard obs case_dotCollectingViaProp__le == "ok raw=L[L[]] n=1"

-- dotCollectingViaProp__l7: F(*a) = a \n x = [7] \n x.F
def case_dotCollectingViaProp__l7 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [.num 7])]), privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.dotCall (.resolve "x") "F" none)])
#guard obs case_dotCollectingViaProp__l7 == "ok raw=L[L[7]] n=1"

-- dotCollectingViaProp__l12: F(*a) = a \n x = [1, 2] \n x.F
def case_dotCollectingViaProp__l12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [.num 1, .num 2])]), privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.dotCall (.resolve "x") "F" none)])
#guard obs case_dotCollectingViaProp__l12 == "ok raw=L[L[1, 2]] n=1"

-- dotCollectingViaProp__l12_3: F(*a) = a \n x = [[1, 2], 3] \n x.F
def case_dotCollectingViaProp__l12_3 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [(.listLiteral [.num 1, .num 2]), .num 3])]), privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.dotCall (.resolve "x") "F" none)])
#guard obs case_dotCollectingViaProp__l12_3 == "ok raw=L[L[L[1, 2], 3]] n=1"

-- dotCollectingViaProp__lle: F(*a) = a \n x = [[]] \n x.F
def case_dotCollectingViaProp__lle : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [(.listLiteral [])])]), privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.dotCall (.resolve "x") "F" none)])
#guard obs case_dotCollectingViaProp__lle == "ok raw=L[L[L[]]] n=1"

-- dotCollectingViaProp__l_e: F(*a) = a \n x = [()] \n x.F
def case_dotCollectingViaProp__l_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [(.emptySequence 0)])]), privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.dotCall (.resolve "x") "F" none)])
#guard obs case_dotCollectingViaProp__l_e == "ok raw=L[L[S[]]] n=1"

-- dotCollectingViaProp__l_p12: F(*a) = a \n x = [(1, 2)] \n x.F
def case_dotCollectingViaProp__l_p12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [(.capture [.num 1, .num 2])])]), privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.dotCall (.resolve "x") "F" none)])
#guard obs case_dotCollectingViaProp__l_p12 == "ok raw=L[L[S[1, 2]]] n=1"

-- dotCollectingViaProp__p_l12: F(*a) = a \n x = ([1, 2], 3) \n x.F
def case_dotCollectingViaProp__p_l12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.listLiteral [.num 1, .num 2]), .num 3])]), privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.dotCall (.resolve "x") "F" none)])
#guard obs case_dotCollectingViaProp__p_l12 == "ok raw=L[S[L[1, 2], 3]] n=1"

-- dotCollectingViaProp__pl1: F(*a) = a \n x = ([1]) \n x.F
def case_dotCollectingViaProp__pl1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [.num 1])]), privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.dotCall (.resolve "x") "F" none)])
#guard obs case_dotCollectingViaProp__pl1 == "ok raw=L[L[1]] n=1"

-- literalDotCollecting__e: F(*a) = a \n (()).F
def case_literalDotCollecting__e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.dotCall (.emptySequence 0) "F" none)])
#guard obs case_literalDotCollecting__e == "ok raw=L[S[]] n=1"

-- literalDotCollecting__n0: F(*a) = a \n (0).F
def case_literalDotCollecting__n0 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.dotCall (.num 0) "F" none)])
#guard obs case_literalDotCollecting__n0 == "ok raw=L[0] n=1"

-- literalDotCollecting__n1: F(*a) = a \n (1).F
def case_literalDotCollecting__n1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.dotCall (.num 1) "F" none)])
#guard obs case_literalDotCollecting__n1 == "ok raw=L[1] n=1"

-- literalDotCollecting__bt: F(*a) = a \n (true).F
def case_literalDotCollecting__bt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.dotCall (.boolLiteral true) "F" none)])
#guard obs case_literalDotCollecting__bt == "ok raw=L[true] n=1"

-- literalDotCollecting__bf: F(*a) = a \n (false).F
def case_literalDotCollecting__bf : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.dotCall (.boolLiteral false) "F" none)])
#guard obs case_literalDotCollecting__bf == "ok raw=L[false] n=1"

-- literalDotCollecting__pbt: F(*a) = a \n ((true)).F
def case_literalDotCollecting__pbt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.dotCall (.boolLiteral true) "F" none)])
#guard obs case_literalDotCollecting__pbt == "ok raw=L[true] n=1"

-- literalDotCollecting__pbt_e: F(*a) = a \n ((true, ())).F
def case_literalDotCollecting__pbt_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.dotCall (.capture [.boolLiteral true, (.emptySequence 0)]) "F" none)])
#guard obs case_literalDotCollecting__pbt_e == "ok raw=L[S[true, S[]]] n=1"

-- literalDotCollecting__pbt_1: F(*a) = a \n ((true, 1)).F
def case_literalDotCollecting__pbt_1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.dotCall (.capture [.boolLiteral true, .num 1]) "F" none)])
#guard obs case_literalDotCollecting__pbt_1 == "ok raw=L[S[true, 1]] n=1"

-- literalDotCollecting__lbt: F(*a) = a \n ([true]).F
def case_literalDotCollecting__lbt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.dotCall (.listLiteral [.boolLiteral true]) "F" none)])
#guard obs case_literalDotCollecting__lbt == "ok raw=L[L[true]] n=1"

-- literalDotCollecting__lbt_bf: F(*a) = a \n ([true, false]).F
def case_literalDotCollecting__lbt_bf : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.dotCall (.listLiteral [.boolLiteral true, .boolLiteral false]) "F" none)])
#guard obs case_literalDotCollecting__lbt_bf == "ok raw=L[L[true, false]] n=1"

-- literalDotCollecting__lpbt_1: F(*a) = a \n ([(true, 1)]).F
def case_literalDotCollecting__lpbt_1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.dotCall (.listLiteral [(.capture [.boolLiteral true, .num 1])]) "F" none)])
#guard obs case_literalDotCollecting__lpbt_1 == "ok raw=L[L[S[true, 1]]] n=1"

-- literalDotCollecting__p1: F(*a) = a \n ((1)).F
def case_literalDotCollecting__p1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.dotCall (.num 1) "F" none)])
#guard obs case_literalDotCollecting__p1 == "ok raw=L[1] n=1"

-- literalDotCollecting__p12: F(*a) = a \n ((1, 2)).F
def case_literalDotCollecting__p12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.dotCall (.capture [.num 1, .num 2]) "F" none)])
#guard obs case_literalDotCollecting__p12 == "ok raw=L[S[1, 2]] n=1"

-- literalDotCollecting__p123: F(*a) = a \n ((1, 2, 3)).F
def case_literalDotCollecting__p123 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.dotCall (.capture [.num 1, .num 2, .num 3]) "F" none)])
#guard obs case_literalDotCollecting__p123 == "ok raw=L[S[1, 2, 3]] n=1"

-- literalDotCollecting__pee: F(*a) = a \n (((), ())).F
def case_literalDotCollecting__pee : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.dotCall (.capture [(.emptySequence 0), (.emptySequence 0)]) "F" none)])
#guard obs case_literalDotCollecting__pee == "ok raw=L[S[S[], S[]]] n=1"

-- literalDotCollecting__pe1: F(*a) = a \n (((), 1)).F
def case_literalDotCollecting__pe1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.dotCall (.capture [(.emptySequence 0), .num 1]) "F" none)])
#guard obs case_literalDotCollecting__pe1 == "ok raw=L[S[S[], 1]] n=1"

-- literalDotCollecting__p1e: F(*a) = a \n ((1, ())).F
def case_literalDotCollecting__p1e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.dotCall (.capture [.num 1, (.emptySequence 0)]) "F" none)])
#guard obs case_literalDotCollecting__p1e == "ok raw=L[S[1, S[]]] n=1"

-- literalDotCollecting__p12_3: F(*a) = a \n (((1, 2), 3)).F
def case_literalDotCollecting__p12_3 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.dotCall (.capture [(.capture [.num 1, .num 2]), .num 3]) "F" none)])
#guard obs case_literalDotCollecting__p12_3 == "ok raw=L[S[S[1, 2], 3]] n=1"

-- literalDotCollecting__p12_34: F(*a) = a \n (((1, 2), (3, 4))).F
def case_literalDotCollecting__p12_34 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.dotCall (.capture [(.capture [.num 1, .num 2]), (.capture [.num 3, .num 4])]) "F" none)])
#guard obs case_literalDotCollecting__p12_34 == "ok raw=L[S[S[1, 2], S[3, 4]]] n=1"

-- literalDotCollecting__pe_12: F(*a) = a \n (((), (1, 2))).F
def case_literalDotCollecting__pe_12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.dotCall (.capture [(.emptySequence 0), (.capture [.num 1, .num 2])]) "F" none)])
#guard obs case_literalDotCollecting__pe_12 == "ok raw=L[S[S[], S[1, 2]]] n=1"

-- literalDotCollecting__ppe1_2: F(*a) = a \n ((((), 1), 2)).F
def case_literalDotCollecting__ppe1_2 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.dotCall (.capture [(.capture [(.emptySequence 0), .num 1]), .num 2]) "F" none)])
#guard obs case_literalDotCollecting__ppe1_2 == "ok raw=L[S[S[S[], 1], 2]] n=1"

-- literalDotCollecting__p12_e: F(*a) = a \n (((1, 2), ())).F
def case_literalDotCollecting__p12_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.dotCall (.capture [(.capture [.num 1, .num 2]), (.emptySequence 0)]) "F" none)])
#guard obs case_literalDotCollecting__p12_e == "ok raw=L[S[S[1, 2], S[]]] n=1"

-- literalDotCollecting__ppe: F(*a) = a \n ((())).F
def case_literalDotCollecting__ppe : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.dotCall (.emptySequence 0) "F" none)])
#guard obs case_literalDotCollecting__ppe == "ok raw=L[S[]] n=1"

-- literalDotCollecting__pp1: F(*a) = a \n (((1))).F
def case_literalDotCollecting__pp1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.dotCall (.num 1) "F" none)])
#guard obs case_literalDotCollecting__pp1 == "ok raw=L[1] n=1"

-- literalDotCollecting__ppp12: F(*a) = a \n ((((1, 2)))).F
def case_literalDotCollecting__ppp12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.dotCall (.capture [.num 1, .num 2]) "F" none)])
#guard obs case_literalDotCollecting__ppp12 == "ok raw=L[S[1, 2]] n=1"

-- literalDotCollecting__le: F(*a) = a \n ([]).F
def case_literalDotCollecting__le : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.dotCall (.listLiteral []) "F" none)])
#guard obs case_literalDotCollecting__le == "ok raw=L[L[]] n=1"

-- literalDotCollecting__l7: F(*a) = a \n ([7]).F
def case_literalDotCollecting__l7 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.dotCall (.listLiteral [.num 7]) "F" none)])
#guard obs case_literalDotCollecting__l7 == "ok raw=L[L[7]] n=1"

-- literalDotCollecting__l12: F(*a) = a \n ([1, 2]).F
def case_literalDotCollecting__l12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.dotCall (.listLiteral [.num 1, .num 2]) "F" none)])
#guard obs case_literalDotCollecting__l12 == "ok raw=L[L[1, 2]] n=1"

-- literalDotCollecting__l12_3: F(*a) = a \n ([[1, 2], 3]).F
def case_literalDotCollecting__l12_3 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.dotCall (.listLiteral [(.listLiteral [.num 1, .num 2]), .num 3]) "F" none)])
#guard obs case_literalDotCollecting__l12_3 == "ok raw=L[L[L[1, 2], 3]] n=1"

-- literalDotCollecting__lle: F(*a) = a \n ([[]]).F
def case_literalDotCollecting__lle : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.dotCall (.listLiteral [(.listLiteral [])]) "F" none)])
#guard obs case_literalDotCollecting__lle == "ok raw=L[L[L[]]] n=1"

-- literalDotCollecting__l_e: F(*a) = a \n ([()]).F
def case_literalDotCollecting__l_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.dotCall (.listLiteral [(.emptySequence 0)]) "F" none)])
#guard obs case_literalDotCollecting__l_e == "ok raw=L[L[S[]]] n=1"

-- literalDotCollecting__l_p12: F(*a) = a \n ([(1, 2)]).F
def case_literalDotCollecting__l_p12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.dotCall (.listLiteral [(.capture [.num 1, .num 2])]) "F" none)])
#guard obs case_literalDotCollecting__l_p12 == "ok raw=L[L[S[1, 2]]] n=1"

-- literalDotCollecting__p_l12: F(*a) = a \n (([1, 2], 3)).F
def case_literalDotCollecting__p_l12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.dotCall (.capture [(.listLiteral [.num 1, .num 2]), .num 3]) "F" none)])
#guard obs case_literalDotCollecting__p_l12 == "ok raw=L[S[L[1, 2], 3]] n=1"

-- literalDotCollecting__pl1: F(*a) = a \n (([1])).F
def case_literalDotCollecting__pl1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.dotCall (.listLiteral [.num 1]) "F" none)])
#guard obs case_literalDotCollecting__pl1 == "ok raw=L[L[1]] n=1"

-- fluentSpreadCollecting__e: F(*a) = a \n x = () \n x*.F
def case_fluentSpreadCollecting__e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.emptySequence 0)]), privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.resolve "x"))])])
#guard obs case_fluentSpreadCollecting__e == "ok raw=L[] n=1"

-- fluentSpreadCollecting__n0: F(*a) = a \n x = 0 \n x*.F
def case_fluentSpreadCollecting__n0 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [.num 0]), privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.resolve "x"))])])
#guard obs case_fluentSpreadCollecting__n0 == "ok raw=L[0] n=1"

-- fluentSpreadCollecting__n1: F(*a) = a \n x = 1 \n x*.F
def case_fluentSpreadCollecting__n1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [.num 1]), privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.resolve "x"))])])
#guard obs case_fluentSpreadCollecting__n1 == "ok raw=L[1] n=1"

-- fluentSpreadCollecting__bt: F(*a) = a \n x = true \n x*.F
def case_fluentSpreadCollecting__bt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [.boolLiteral true]), privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.resolve "x"))])])
#guard obs case_fluentSpreadCollecting__bt == "ok raw=L[true] n=1"

-- fluentSpreadCollecting__bf: F(*a) = a \n x = false \n x*.F
def case_fluentSpreadCollecting__bf : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [.boolLiteral false]), privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.resolve "x"))])])
#guard obs case_fluentSpreadCollecting__bf == "ok raw=L[false] n=1"

-- fluentSpreadCollecting__pbt: F(*a) = a \n x = (true) \n x*.F
def case_fluentSpreadCollecting__pbt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [.boolLiteral true]), privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.resolve "x"))])])
#guard obs case_fluentSpreadCollecting__pbt == "ok raw=L[true] n=1"

-- fluentSpreadCollecting__pbt_e: F(*a) = a \n x = (true, ()) \n x*.F
def case_fluentSpreadCollecting__pbt_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [.boolLiteral true, (.emptySequence 0)])]), privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.resolve "x"))])])
#guard obs case_fluentSpreadCollecting__pbt_e == "ok raw=L[true, S[]] n=1"

-- fluentSpreadCollecting__pbt_1: F(*a) = a \n x = (true, 1) \n x*.F
def case_fluentSpreadCollecting__pbt_1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [.boolLiteral true, .num 1])]), privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.resolve "x"))])])
#guard obs case_fluentSpreadCollecting__pbt_1 == "ok raw=L[true, 1] n=1"

-- fluentSpreadCollecting__lbt: F(*a) = a \n x = [true] \n x*.F
def case_fluentSpreadCollecting__lbt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [.boolLiteral true])]), privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.resolve "x"))])])
#guard obs case_fluentSpreadCollecting__lbt == "ok raw=L[true] n=1"

-- fluentSpreadCollecting__lbt_bf: F(*a) = a \n x = [true, false] \n x*.F
def case_fluentSpreadCollecting__lbt_bf : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [.boolLiteral true, .boolLiteral false])]), privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.resolve "x"))])])
#guard obs case_fluentSpreadCollecting__lbt_bf == "ok raw=L[true, false] n=1"

-- fluentSpreadCollecting__lpbt_1: F(*a) = a \n x = [(true, 1)] \n x*.F
def case_fluentSpreadCollecting__lpbt_1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [(.capture [.boolLiteral true, .num 1])])]), privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.resolve "x"))])])
#guard obs case_fluentSpreadCollecting__lpbt_1 == "ok raw=L[S[true, 1]] n=1"

-- fluentSpreadCollecting__p1: F(*a) = a \n x = (1) \n x*.F
def case_fluentSpreadCollecting__p1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [.num 1]), privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.resolve "x"))])])
#guard obs case_fluentSpreadCollecting__p1 == "ok raw=L[1] n=1"

-- fluentSpreadCollecting__p12: F(*a) = a \n x = (1, 2) \n x*.F
def case_fluentSpreadCollecting__p12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [.num 1, .num 2])]), privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.resolve "x"))])])
#guard obs case_fluentSpreadCollecting__p12 == "ok raw=L[1, 2] n=1"

-- fluentSpreadCollecting__p123: F(*a) = a \n x = (1, 2, 3) \n x*.F
def case_fluentSpreadCollecting__p123 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [.num 1, .num 2, .num 3])]), privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.resolve "x"))])])
#guard obs case_fluentSpreadCollecting__p123 == "ok raw=L[1, 2, 3] n=1"

-- fluentSpreadCollecting__pee: F(*a) = a \n x = ((), ()) \n x*.F
def case_fluentSpreadCollecting__pee : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.emptySequence 0), (.emptySequence 0)])]), privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.resolve "x"))])])
#guard obs case_fluentSpreadCollecting__pee == "ok raw=L[S[], S[]] n=1"

-- fluentSpreadCollecting__pe1: F(*a) = a \n x = ((), 1) \n x*.F
def case_fluentSpreadCollecting__pe1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.emptySequence 0), .num 1])]), privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.resolve "x"))])])
#guard obs case_fluentSpreadCollecting__pe1 == "ok raw=L[S[], 1] n=1"

-- fluentSpreadCollecting__p1e: F(*a) = a \n x = (1, ()) \n x*.F
def case_fluentSpreadCollecting__p1e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [.num 1, (.emptySequence 0)])]), privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.resolve "x"))])])
#guard obs case_fluentSpreadCollecting__p1e == "ok raw=L[1, S[]] n=1"

-- fluentSpreadCollecting__p12_3: F(*a) = a \n x = ((1, 2), 3) \n x*.F
def case_fluentSpreadCollecting__p12_3 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.capture [.num 1, .num 2]), .num 3])]), privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.resolve "x"))])])
#guard obs case_fluentSpreadCollecting__p12_3 == "ok raw=L[S[1, 2], 3] n=1"

-- fluentSpreadCollecting__p12_34: F(*a) = a \n x = ((1, 2), (3, 4)) \n x*.F
def case_fluentSpreadCollecting__p12_34 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.capture [.num 1, .num 2]), (.capture [.num 3, .num 4])])]), privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.resolve "x"))])])
#guard obs case_fluentSpreadCollecting__p12_34 == "ok raw=L[S[1, 2], S[3, 4]] n=1"

-- fluentSpreadCollecting__pe_12: F(*a) = a \n x = ((), (1, 2)) \n x*.F
def case_fluentSpreadCollecting__pe_12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.emptySequence 0), (.capture [.num 1, .num 2])])]), privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.resolve "x"))])])
#guard obs case_fluentSpreadCollecting__pe_12 == "ok raw=L[S[], S[1, 2]] n=1"

-- fluentSpreadCollecting__ppe1_2: F(*a) = a \n x = (((), 1), 2) \n x*.F
def case_fluentSpreadCollecting__ppe1_2 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.capture [(.emptySequence 0), .num 1]), .num 2])]), privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.resolve "x"))])])
#guard obs case_fluentSpreadCollecting__ppe1_2 == "ok raw=L[S[S[], 1], 2] n=1"

-- fluentSpreadCollecting__p12_e: F(*a) = a \n x = ((1, 2), ()) \n x*.F
def case_fluentSpreadCollecting__p12_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.capture [.num 1, .num 2]), (.emptySequence 0)])]), privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.resolve "x"))])])
#guard obs case_fluentSpreadCollecting__p12_e == "ok raw=L[S[1, 2], S[]] n=1"

-- fluentSpreadCollecting__ppe: F(*a) = a \n x = (()) \n x*.F
def case_fluentSpreadCollecting__ppe : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.emptySequence 0)]), privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.resolve "x"))])])
#guard obs case_fluentSpreadCollecting__ppe == "ok raw=L[] n=1"

-- fluentSpreadCollecting__pp1: F(*a) = a \n x = ((1)) \n x*.F
def case_fluentSpreadCollecting__pp1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [.num 1]), privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.resolve "x"))])])
#guard obs case_fluentSpreadCollecting__pp1 == "ok raw=L[1] n=1"

-- fluentSpreadCollecting__ppp12: F(*a) = a \n x = (((1, 2))) \n x*.F
def case_fluentSpreadCollecting__ppp12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [.num 1, .num 2])]), privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.resolve "x"))])])
#guard obs case_fluentSpreadCollecting__ppp12 == "ok raw=L[1, 2] n=1"

-- fluentSpreadCollecting__le: F(*a) = a \n x = [] \n x*.F
def case_fluentSpreadCollecting__le : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [])]), privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.resolve "x"))])])
#guard obs case_fluentSpreadCollecting__le == "ok raw=L[] n=1"

-- fluentSpreadCollecting__l7: F(*a) = a \n x = [7] \n x*.F
def case_fluentSpreadCollecting__l7 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [.num 7])]), privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.resolve "x"))])])
#guard obs case_fluentSpreadCollecting__l7 == "ok raw=L[7] n=1"

-- fluentSpreadCollecting__l12: F(*a) = a \n x = [1, 2] \n x*.F
def case_fluentSpreadCollecting__l12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [.num 1, .num 2])]), privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.resolve "x"))])])
#guard obs case_fluentSpreadCollecting__l12 == "ok raw=L[1, 2] n=1"

-- fluentSpreadCollecting__l12_3: F(*a) = a \n x = [[1, 2], 3] \n x*.F
def case_fluentSpreadCollecting__l12_3 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [(.listLiteral [.num 1, .num 2]), .num 3])]), privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.resolve "x"))])])
#guard obs case_fluentSpreadCollecting__l12_3 == "ok raw=L[L[1, 2], 3] n=1"

-- fluentSpreadCollecting__lle: F(*a) = a \n x = [[]] \n x*.F
def case_fluentSpreadCollecting__lle : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [(.listLiteral [])])]), privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.resolve "x"))])])
#guard obs case_fluentSpreadCollecting__lle == "ok raw=L[L[]] n=1"

-- fluentSpreadCollecting__l_e: F(*a) = a \n x = [()] \n x*.F
def case_fluentSpreadCollecting__l_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [(.emptySequence 0)])]), privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.resolve "x"))])])
#guard obs case_fluentSpreadCollecting__l_e == "ok raw=L[S[]] n=1"

-- fluentSpreadCollecting__l_p12: F(*a) = a \n x = [(1, 2)] \n x*.F
def case_fluentSpreadCollecting__l_p12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [(.capture [.num 1, .num 2])])]), privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.resolve "x"))])])
#guard obs case_fluentSpreadCollecting__l_p12 == "ok raw=L[S[1, 2]] n=1"

-- fluentSpreadCollecting__p_l12: F(*a) = a \n x = ([1, 2], 3) \n x*.F
def case_fluentSpreadCollecting__p_l12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.listLiteral [.num 1, .num 2]), .num 3])]), privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.resolve "x"))])])
#guard obs case_fluentSpreadCollecting__p_l12 == "ok raw=L[L[1, 2], 3] n=1"

-- fluentSpreadCollecting__pl1: F(*a) = a \n x = ([1]) \n x*.F
def case_fluentSpreadCollecting__pl1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [.num 1])]), privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.resolve "x"))])])
#guard obs case_fluentSpreadCollecting__pl1 == "ok raw=L[1] n=1"

-- mixed_h__e: F(h, *t) = h \n F(()*)
def case_mixed_h__e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "h" }, { name := "t", kind := .collecting }] [] [] [.param "h"])] [(.call (.resolve "F") [(.sequenceSpread (.emptySequence 0))])])
#guard obs case_mixed_h__e == "err arity"

-- mixed_h__n0: F(h, *t) = h \n F(0*)
def case_mixed_h__n0 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "h" }, { name := "t", kind := .collecting }] [] [] [.param "h"])] [(.call (.resolve "F") [(.sequenceSpread (.num 0))])])
#guard obs case_mixed_h__n0 == "ok raw=0 n=1"

-- mixed_h__n1: F(h, *t) = h \n F(1*)
def case_mixed_h__n1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "h" }, { name := "t", kind := .collecting }] [] [] [.param "h"])] [(.call (.resolve "F") [(.sequenceSpread (.num 1))])])
#guard obs case_mixed_h__n1 == "ok raw=1 n=1"

-- mixed_h__bt: F(h, *t) = h \n F(true*)
def case_mixed_h__bt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "h" }, { name := "t", kind := .collecting }] [] [] [.param "h"])] [(.call (.resolve "F") [(.sequenceSpread (.boolLiteral true))])])
#guard obs case_mixed_h__bt == "ok raw=true n=1"

-- mixed_h__bf: F(h, *t) = h \n F(false*)
def case_mixed_h__bf : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "h" }, { name := "t", kind := .collecting }] [] [] [.param "h"])] [(.call (.resolve "F") [(.sequenceSpread (.boolLiteral false))])])
#guard obs case_mixed_h__bf == "ok raw=false n=1"

-- mixed_h__pbt: F(h, *t) = h \n F((true)*)
def case_mixed_h__pbt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "h" }, { name := "t", kind := .collecting }] [] [] [.param "h"])] [(.call (.resolve "F") [(.sequenceSpread (.boolLiteral true))])])
#guard obs case_mixed_h__pbt == "ok raw=true n=1"

-- mixed_h__pbt_e: F(h, *t) = h \n F((true, ())*)
def case_mixed_h__pbt_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "h" }, { name := "t", kind := .collecting }] [] [] [.param "h"])] [(.call (.resolve "F") [(.sequenceSpread (.capture [.boolLiteral true, (.emptySequence 0)]))])])
#guard obs case_mixed_h__pbt_e == "ok raw=true n=1"

-- mixed_h__pbt_1: F(h, *t) = h \n F((true, 1)*)
def case_mixed_h__pbt_1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "h" }, { name := "t", kind := .collecting }] [] [] [.param "h"])] [(.call (.resolve "F") [(.sequenceSpread (.capture [.boolLiteral true, .num 1]))])])
#guard obs case_mixed_h__pbt_1 == "ok raw=true n=1"

-- mixed_h__lbt: F(h, *t) = h \n F([true]*)
def case_mixed_h__lbt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "h" }, { name := "t", kind := .collecting }] [] [] [.param "h"])] [(.call (.resolve "F") [(.sequenceSpread (.listLiteral [.boolLiteral true]))])])
#guard obs case_mixed_h__lbt == "ok raw=true n=1"

-- mixed_h__lbt_bf: F(h, *t) = h \n F([true, false]*)
def case_mixed_h__lbt_bf : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "h" }, { name := "t", kind := .collecting }] [] [] [.param "h"])] [(.call (.resolve "F") [(.sequenceSpread (.listLiteral [.boolLiteral true, .boolLiteral false]))])])
#guard obs case_mixed_h__lbt_bf == "ok raw=true n=1"

-- mixed_h__lpbt_1: F(h, *t) = h \n F([(true, 1)]*)
def case_mixed_h__lpbt_1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "h" }, { name := "t", kind := .collecting }] [] [] [.param "h"])] [(.call (.resolve "F") [(.sequenceSpread (.listLiteral [(.capture [.boolLiteral true, .num 1])]))])])
#guard obs case_mixed_h__lpbt_1 == "ok raw=S[true, 1] n=1"

-- mixed_h__p1: F(h, *t) = h \n F((1)*)
def case_mixed_h__p1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "h" }, { name := "t", kind := .collecting }] [] [] [.param "h"])] [(.call (.resolve "F") [(.sequenceSpread (.num 1))])])
#guard obs case_mixed_h__p1 == "ok raw=1 n=1"

-- mixed_h__p12: F(h, *t) = h \n F((1, 2)*)
def case_mixed_h__p12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "h" }, { name := "t", kind := .collecting }] [] [] [.param "h"])] [(.call (.resolve "F") [(.sequenceSpread (.capture [.num 1, .num 2]))])])
#guard obs case_mixed_h__p12 == "ok raw=1 n=1"

-- mixed_h__p123: F(h, *t) = h \n F((1, 2, 3)*)
def case_mixed_h__p123 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "h" }, { name := "t", kind := .collecting }] [] [] [.param "h"])] [(.call (.resolve "F") [(.sequenceSpread (.capture [.num 1, .num 2, .num 3]))])])
#guard obs case_mixed_h__p123 == "ok raw=1 n=1"

-- mixed_h__pee: F(h, *t) = h \n F(((), ())*)
def case_mixed_h__pee : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "h" }, { name := "t", kind := .collecting }] [] [] [.param "h"])] [(.call (.resolve "F") [(.sequenceSpread (.capture [(.emptySequence 0), (.emptySequence 0)]))])])
#guard obs case_mixed_h__pee == "ok raw=S[] n=1"

-- mixed_h__pe1: F(h, *t) = h \n F(((), 1)*)
def case_mixed_h__pe1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "h" }, { name := "t", kind := .collecting }] [] [] [.param "h"])] [(.call (.resolve "F") [(.sequenceSpread (.capture [(.emptySequence 0), .num 1]))])])
#guard obs case_mixed_h__pe1 == "ok raw=S[] n=1"

-- mixed_h__p1e: F(h, *t) = h \n F((1, ())*)
def case_mixed_h__p1e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "h" }, { name := "t", kind := .collecting }] [] [] [.param "h"])] [(.call (.resolve "F") [(.sequenceSpread (.capture [.num 1, (.emptySequence 0)]))])])
#guard obs case_mixed_h__p1e == "ok raw=1 n=1"

-- mixed_h__p12_3: F(h, *t) = h \n F(((1, 2), 3)*)
def case_mixed_h__p12_3 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "h" }, { name := "t", kind := .collecting }] [] [] [.param "h"])] [(.call (.resolve "F") [(.sequenceSpread (.capture [(.capture [.num 1, .num 2]), .num 3]))])])
#guard obs case_mixed_h__p12_3 == "ok raw=S[1, 2] n=1"

-- mixed_h__p12_34: F(h, *t) = h \n F(((1, 2), (3, 4))*)
def case_mixed_h__p12_34 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "h" }, { name := "t", kind := .collecting }] [] [] [.param "h"])] [(.call (.resolve "F") [(.sequenceSpread (.capture [(.capture [.num 1, .num 2]), (.capture [.num 3, .num 4])]))])])
#guard obs case_mixed_h__p12_34 == "ok raw=S[1, 2] n=1"

-- mixed_h__pe_12: F(h, *t) = h \n F(((), (1, 2))*)
def case_mixed_h__pe_12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "h" }, { name := "t", kind := .collecting }] [] [] [.param "h"])] [(.call (.resolve "F") [(.sequenceSpread (.capture [(.emptySequence 0), (.capture [.num 1, .num 2])]))])])
#guard obs case_mixed_h__pe_12 == "ok raw=S[] n=1"

-- mixed_h__ppe1_2: F(h, *t) = h \n F((((), 1), 2)*)
def case_mixed_h__ppe1_2 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "h" }, { name := "t", kind := .collecting }] [] [] [.param "h"])] [(.call (.resolve "F") [(.sequenceSpread (.capture [(.capture [(.emptySequence 0), .num 1]), .num 2]))])])
#guard obs case_mixed_h__ppe1_2 == "ok raw=S[S[], 1] n=1"

-- mixed_h__p12_e: F(h, *t) = h \n F(((1, 2), ())*)
def case_mixed_h__p12_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "h" }, { name := "t", kind := .collecting }] [] [] [.param "h"])] [(.call (.resolve "F") [(.sequenceSpread (.capture [(.capture [.num 1, .num 2]), (.emptySequence 0)]))])])
#guard obs case_mixed_h__p12_e == "ok raw=S[1, 2] n=1"

-- mixed_h__ppe: F(h, *t) = h \n F((())*)
def case_mixed_h__ppe : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "h" }, { name := "t", kind := .collecting }] [] [] [.param "h"])] [(.call (.resolve "F") [(.sequenceSpread (.emptySequence 0))])])
#guard obs case_mixed_h__ppe == "err arity"

-- mixed_h__pp1: F(h, *t) = h \n F(((1))*)
def case_mixed_h__pp1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "h" }, { name := "t", kind := .collecting }] [] [] [.param "h"])] [(.call (.resolve "F") [(.sequenceSpread (.num 1))])])
#guard obs case_mixed_h__pp1 == "ok raw=1 n=1"

-- mixed_h__ppp12: F(h, *t) = h \n F((((1, 2)))*)
def case_mixed_h__ppp12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "h" }, { name := "t", kind := .collecting }] [] [] [.param "h"])] [(.call (.resolve "F") [(.sequenceSpread (.capture [.num 1, .num 2]))])])
#guard obs case_mixed_h__ppp12 == "ok raw=1 n=1"

-- mixed_h__le: F(h, *t) = h \n F([]*)
def case_mixed_h__le : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "h" }, { name := "t", kind := .collecting }] [] [] [.param "h"])] [(.call (.resolve "F") [(.sequenceSpread (.listLiteral []))])])
#guard obs case_mixed_h__le == "err arity"

-- mixed_h__l7: F(h, *t) = h \n F([7]*)
def case_mixed_h__l7 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "h" }, { name := "t", kind := .collecting }] [] [] [.param "h"])] [(.call (.resolve "F") [(.sequenceSpread (.listLiteral [.num 7]))])])
#guard obs case_mixed_h__l7 == "ok raw=7 n=1"

-- mixed_h__l12: F(h, *t) = h \n F([1, 2]*)
def case_mixed_h__l12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "h" }, { name := "t", kind := .collecting }] [] [] [.param "h"])] [(.call (.resolve "F") [(.sequenceSpread (.listLiteral [.num 1, .num 2]))])])
#guard obs case_mixed_h__l12 == "ok raw=1 n=1"

-- mixed_h__l12_3: F(h, *t) = h \n F([[1, 2], 3]*)
def case_mixed_h__l12_3 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "h" }, { name := "t", kind := .collecting }] [] [] [.param "h"])] [(.call (.resolve "F") [(.sequenceSpread (.listLiteral [(.listLiteral [.num 1, .num 2]), .num 3]))])])
#guard obs case_mixed_h__l12_3 == "ok raw=L[1, 2] n=1"

-- mixed_h__lle: F(h, *t) = h \n F([[]]*)
def case_mixed_h__lle : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "h" }, { name := "t", kind := .collecting }] [] [] [.param "h"])] [(.call (.resolve "F") [(.sequenceSpread (.listLiteral [(.listLiteral [])]))])])
#guard obs case_mixed_h__lle == "ok raw=L[] n=1"

-- mixed_h__l_e: F(h, *t) = h \n F([()]*)
def case_mixed_h__l_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "h" }, { name := "t", kind := .collecting }] [] [] [.param "h"])] [(.call (.resolve "F") [(.sequenceSpread (.listLiteral [(.emptySequence 0)]))])])
#guard obs case_mixed_h__l_e == "ok raw=S[] n=1"

-- mixed_h__l_p12: F(h, *t) = h \n F([(1, 2)]*)
def case_mixed_h__l_p12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "h" }, { name := "t", kind := .collecting }] [] [] [.param "h"])] [(.call (.resolve "F") [(.sequenceSpread (.listLiteral [(.capture [.num 1, .num 2])]))])])
#guard obs case_mixed_h__l_p12 == "ok raw=S[1, 2] n=1"

-- mixed_h__p_l12: F(h, *t) = h \n F(([1, 2], 3)*)
def case_mixed_h__p_l12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "h" }, { name := "t", kind := .collecting }] [] [] [.param "h"])] [(.call (.resolve "F") [(.sequenceSpread (.capture [(.listLiteral [.num 1, .num 2]), .num 3]))])])
#guard obs case_mixed_h__p_l12 == "ok raw=L[1, 2] n=1"

-- mixed_h__pl1: F(h, *t) = h \n F(([1])*)
def case_mixed_h__pl1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "h" }, { name := "t", kind := .collecting }] [] [] [.param "h"])] [(.call (.resolve "F") [(.sequenceSpread (.listLiteral [.num 1]))])])
#guard obs case_mixed_h__pl1 == "ok raw=1 n=1"

-- mixed_t__e: F(h, *t) = t \n F(()*)
def case_mixed_t__e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "h" }, { name := "t", kind := .collecting }] [] [] [.param "t"])] [(.call (.resolve "F") [(.sequenceSpread (.emptySequence 0))])])
#guard obs case_mixed_t__e == "err arity"

-- mixed_t__n0: F(h, *t) = t \n F(0*)
def case_mixed_t__n0 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "h" }, { name := "t", kind := .collecting }] [] [] [.param "t"])] [(.call (.resolve "F") [(.sequenceSpread (.num 0))])])
#guard obs case_mixed_t__n0 == "ok raw=L[] n=1"

-- mixed_t__n1: F(h, *t) = t \n F(1*)
def case_mixed_t__n1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "h" }, { name := "t", kind := .collecting }] [] [] [.param "t"])] [(.call (.resolve "F") [(.sequenceSpread (.num 1))])])
#guard obs case_mixed_t__n1 == "ok raw=L[] n=1"

-- mixed_t__bt: F(h, *t) = t \n F(true*)
def case_mixed_t__bt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "h" }, { name := "t", kind := .collecting }] [] [] [.param "t"])] [(.call (.resolve "F") [(.sequenceSpread (.boolLiteral true))])])
#guard obs case_mixed_t__bt == "ok raw=L[] n=1"

-- mixed_t__bf: F(h, *t) = t \n F(false*)
def case_mixed_t__bf : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "h" }, { name := "t", kind := .collecting }] [] [] [.param "t"])] [(.call (.resolve "F") [(.sequenceSpread (.boolLiteral false))])])
#guard obs case_mixed_t__bf == "ok raw=L[] n=1"

-- mixed_t__pbt: F(h, *t) = t \n F((true)*)
def case_mixed_t__pbt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "h" }, { name := "t", kind := .collecting }] [] [] [.param "t"])] [(.call (.resolve "F") [(.sequenceSpread (.boolLiteral true))])])
#guard obs case_mixed_t__pbt == "ok raw=L[] n=1"

-- mixed_t__pbt_e: F(h, *t) = t \n F((true, ())*)
def case_mixed_t__pbt_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "h" }, { name := "t", kind := .collecting }] [] [] [.param "t"])] [(.call (.resolve "F") [(.sequenceSpread (.capture [.boolLiteral true, (.emptySequence 0)]))])])
#guard obs case_mixed_t__pbt_e == "ok raw=L[S[]] n=1"

-- mixed_t__pbt_1: F(h, *t) = t \n F((true, 1)*)
def case_mixed_t__pbt_1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "h" }, { name := "t", kind := .collecting }] [] [] [.param "t"])] [(.call (.resolve "F") [(.sequenceSpread (.capture [.boolLiteral true, .num 1]))])])
#guard obs case_mixed_t__pbt_1 == "ok raw=L[1] n=1"

-- mixed_t__lbt: F(h, *t) = t \n F([true]*)
def case_mixed_t__lbt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "h" }, { name := "t", kind := .collecting }] [] [] [.param "t"])] [(.call (.resolve "F") [(.sequenceSpread (.listLiteral [.boolLiteral true]))])])
#guard obs case_mixed_t__lbt == "ok raw=L[] n=1"

-- mixed_t__lbt_bf: F(h, *t) = t \n F([true, false]*)
def case_mixed_t__lbt_bf : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "h" }, { name := "t", kind := .collecting }] [] [] [.param "t"])] [(.call (.resolve "F") [(.sequenceSpread (.listLiteral [.boolLiteral true, .boolLiteral false]))])])
#guard obs case_mixed_t__lbt_bf == "ok raw=L[false] n=1"

-- mixed_t__lpbt_1: F(h, *t) = t \n F([(true, 1)]*)
def case_mixed_t__lpbt_1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "h" }, { name := "t", kind := .collecting }] [] [] [.param "t"])] [(.call (.resolve "F") [(.sequenceSpread (.listLiteral [(.capture [.boolLiteral true, .num 1])]))])])
#guard obs case_mixed_t__lpbt_1 == "ok raw=L[] n=1"

-- mixed_t__p1: F(h, *t) = t \n F((1)*)
def case_mixed_t__p1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "h" }, { name := "t", kind := .collecting }] [] [] [.param "t"])] [(.call (.resolve "F") [(.sequenceSpread (.num 1))])])
#guard obs case_mixed_t__p1 == "ok raw=L[] n=1"

-- mixed_t__p12: F(h, *t) = t \n F((1, 2)*)
def case_mixed_t__p12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "h" }, { name := "t", kind := .collecting }] [] [] [.param "t"])] [(.call (.resolve "F") [(.sequenceSpread (.capture [.num 1, .num 2]))])])
#guard obs case_mixed_t__p12 == "ok raw=L[2] n=1"

-- mixed_t__p123: F(h, *t) = t \n F((1, 2, 3)*)
def case_mixed_t__p123 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "h" }, { name := "t", kind := .collecting }] [] [] [.param "t"])] [(.call (.resolve "F") [(.sequenceSpread (.capture [.num 1, .num 2, .num 3]))])])
#guard obs case_mixed_t__p123 == "ok raw=L[2, 3] n=1"

-- mixed_t__pee: F(h, *t) = t \n F(((), ())*)
def case_mixed_t__pee : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "h" }, { name := "t", kind := .collecting }] [] [] [.param "t"])] [(.call (.resolve "F") [(.sequenceSpread (.capture [(.emptySequence 0), (.emptySequence 0)]))])])
#guard obs case_mixed_t__pee == "ok raw=L[S[]] n=1"

-- mixed_t__pe1: F(h, *t) = t \n F(((), 1)*)
def case_mixed_t__pe1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "h" }, { name := "t", kind := .collecting }] [] [] [.param "t"])] [(.call (.resolve "F") [(.sequenceSpread (.capture [(.emptySequence 0), .num 1]))])])
#guard obs case_mixed_t__pe1 == "ok raw=L[1] n=1"

-- mixed_t__p1e: F(h, *t) = t \n F((1, ())*)
def case_mixed_t__p1e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "h" }, { name := "t", kind := .collecting }] [] [] [.param "t"])] [(.call (.resolve "F") [(.sequenceSpread (.capture [.num 1, (.emptySequence 0)]))])])
#guard obs case_mixed_t__p1e == "ok raw=L[S[]] n=1"

-- mixed_t__p12_3: F(h, *t) = t \n F(((1, 2), 3)*)
def case_mixed_t__p12_3 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "h" }, { name := "t", kind := .collecting }] [] [] [.param "t"])] [(.call (.resolve "F") [(.sequenceSpread (.capture [(.capture [.num 1, .num 2]), .num 3]))])])
#guard obs case_mixed_t__p12_3 == "ok raw=L[3] n=1"

-- mixed_t__p12_34: F(h, *t) = t \n F(((1, 2), (3, 4))*)
def case_mixed_t__p12_34 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "h" }, { name := "t", kind := .collecting }] [] [] [.param "t"])] [(.call (.resolve "F") [(.sequenceSpread (.capture [(.capture [.num 1, .num 2]), (.capture [.num 3, .num 4])]))])])
#guard obs case_mixed_t__p12_34 == "ok raw=L[S[3, 4]] n=1"

-- mixed_t__pe_12: F(h, *t) = t \n F(((), (1, 2))*)
def case_mixed_t__pe_12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "h" }, { name := "t", kind := .collecting }] [] [] [.param "t"])] [(.call (.resolve "F") [(.sequenceSpread (.capture [(.emptySequence 0), (.capture [.num 1, .num 2])]))])])
#guard obs case_mixed_t__pe_12 == "ok raw=L[S[1, 2]] n=1"

-- mixed_t__ppe1_2: F(h, *t) = t \n F((((), 1), 2)*)
def case_mixed_t__ppe1_2 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "h" }, { name := "t", kind := .collecting }] [] [] [.param "t"])] [(.call (.resolve "F") [(.sequenceSpread (.capture [(.capture [(.emptySequence 0), .num 1]), .num 2]))])])
#guard obs case_mixed_t__ppe1_2 == "ok raw=L[2] n=1"

-- mixed_t__p12_e: F(h, *t) = t \n F(((1, 2), ())*)
def case_mixed_t__p12_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "h" }, { name := "t", kind := .collecting }] [] [] [.param "t"])] [(.call (.resolve "F") [(.sequenceSpread (.capture [(.capture [.num 1, .num 2]), (.emptySequence 0)]))])])
#guard obs case_mixed_t__p12_e == "ok raw=L[S[]] n=1"

-- mixed_t__ppe: F(h, *t) = t \n F((())*)
def case_mixed_t__ppe : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "h" }, { name := "t", kind := .collecting }] [] [] [.param "t"])] [(.call (.resolve "F") [(.sequenceSpread (.emptySequence 0))])])
#guard obs case_mixed_t__ppe == "err arity"

-- mixed_t__pp1: F(h, *t) = t \n F(((1))*)
def case_mixed_t__pp1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "h" }, { name := "t", kind := .collecting }] [] [] [.param "t"])] [(.call (.resolve "F") [(.sequenceSpread (.num 1))])])
#guard obs case_mixed_t__pp1 == "ok raw=L[] n=1"

-- mixed_t__ppp12: F(h, *t) = t \n F((((1, 2)))*)
def case_mixed_t__ppp12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "h" }, { name := "t", kind := .collecting }] [] [] [.param "t"])] [(.call (.resolve "F") [(.sequenceSpread (.capture [.num 1, .num 2]))])])
#guard obs case_mixed_t__ppp12 == "ok raw=L[2] n=1"

-- mixed_t__le: F(h, *t) = t \n F([]*)
def case_mixed_t__le : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "h" }, { name := "t", kind := .collecting }] [] [] [.param "t"])] [(.call (.resolve "F") [(.sequenceSpread (.listLiteral []))])])
#guard obs case_mixed_t__le == "err arity"

-- mixed_t__l7: F(h, *t) = t \n F([7]*)
def case_mixed_t__l7 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "h" }, { name := "t", kind := .collecting }] [] [] [.param "t"])] [(.call (.resolve "F") [(.sequenceSpread (.listLiteral [.num 7]))])])
#guard obs case_mixed_t__l7 == "ok raw=L[] n=1"

-- mixed_t__l12: F(h, *t) = t \n F([1, 2]*)
def case_mixed_t__l12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "h" }, { name := "t", kind := .collecting }] [] [] [.param "t"])] [(.call (.resolve "F") [(.sequenceSpread (.listLiteral [.num 1, .num 2]))])])
#guard obs case_mixed_t__l12 == "ok raw=L[2] n=1"

-- mixed_t__l12_3: F(h, *t) = t \n F([[1, 2], 3]*)
def case_mixed_t__l12_3 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "h" }, { name := "t", kind := .collecting }] [] [] [.param "t"])] [(.call (.resolve "F") [(.sequenceSpread (.listLiteral [(.listLiteral [.num 1, .num 2]), .num 3]))])])
#guard obs case_mixed_t__l12_3 == "ok raw=L[3] n=1"

-- mixed_t__lle: F(h, *t) = t \n F([[]]*)
def case_mixed_t__lle : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "h" }, { name := "t", kind := .collecting }] [] [] [.param "t"])] [(.call (.resolve "F") [(.sequenceSpread (.listLiteral [(.listLiteral [])]))])])
#guard obs case_mixed_t__lle == "ok raw=L[] n=1"

-- mixed_t__l_e: F(h, *t) = t \n F([()]*)
def case_mixed_t__l_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "h" }, { name := "t", kind := .collecting }] [] [] [.param "t"])] [(.call (.resolve "F") [(.sequenceSpread (.listLiteral [(.emptySequence 0)]))])])
#guard obs case_mixed_t__l_e == "ok raw=L[] n=1"

-- mixed_t__l_p12: F(h, *t) = t \n F([(1, 2)]*)
def case_mixed_t__l_p12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "h" }, { name := "t", kind := .collecting }] [] [] [.param "t"])] [(.call (.resolve "F") [(.sequenceSpread (.listLiteral [(.capture [.num 1, .num 2])]))])])
#guard obs case_mixed_t__l_p12 == "ok raw=L[] n=1"

-- mixed_t__p_l12: F(h, *t) = t \n F(([1, 2], 3)*)
def case_mixed_t__p_l12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "h" }, { name := "t", kind := .collecting }] [] [] [.param "t"])] [(.call (.resolve "F") [(.sequenceSpread (.capture [(.listLiteral [.num 1, .num 2]), .num 3]))])])
#guard obs case_mixed_t__p_l12 == "ok raw=L[3] n=1"

-- mixed_t__pl1: F(h, *t) = t \n F(([1])*)
def case_mixed_t__pl1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "h" }, { name := "t", kind := .collecting }] [] [] [.param "t"])] [(.call (.resolve "F") [(.sequenceSpread (.listLiteral [.num 1]))])])
#guard obs case_mixed_t__pl1 == "ok raw=L[] n=1"

-- mixedBack_t__e: F(*t, z) = t \n F(()*)
def case_mixedBack_t__e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "t", kind := .collecting }, { name := "z" }] [] [] [.param "t"])] [(.call (.resolve "F") [(.sequenceSpread (.emptySequence 0))])])
#guard obs case_mixedBack_t__e == "err arity"

-- mixedBack_t__n0: F(*t, z) = t \n F(0*)
def case_mixedBack_t__n0 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "t", kind := .collecting }, { name := "z" }] [] [] [.param "t"])] [(.call (.resolve "F") [(.sequenceSpread (.num 0))])])
#guard obs case_mixedBack_t__n0 == "ok raw=L[] n=1"

-- mixedBack_t__n1: F(*t, z) = t \n F(1*)
def case_mixedBack_t__n1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "t", kind := .collecting }, { name := "z" }] [] [] [.param "t"])] [(.call (.resolve "F") [(.sequenceSpread (.num 1))])])
#guard obs case_mixedBack_t__n1 == "ok raw=L[] n=1"

-- mixedBack_t__bt: F(*t, z) = t \n F(true*)
def case_mixedBack_t__bt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "t", kind := .collecting }, { name := "z" }] [] [] [.param "t"])] [(.call (.resolve "F") [(.sequenceSpread (.boolLiteral true))])])
#guard obs case_mixedBack_t__bt == "ok raw=L[] n=1"

-- mixedBack_t__bf: F(*t, z) = t \n F(false*)
def case_mixedBack_t__bf : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "t", kind := .collecting }, { name := "z" }] [] [] [.param "t"])] [(.call (.resolve "F") [(.sequenceSpread (.boolLiteral false))])])
#guard obs case_mixedBack_t__bf == "ok raw=L[] n=1"

-- mixedBack_t__pbt: F(*t, z) = t \n F((true)*)
def case_mixedBack_t__pbt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "t", kind := .collecting }, { name := "z" }] [] [] [.param "t"])] [(.call (.resolve "F") [(.sequenceSpread (.boolLiteral true))])])
#guard obs case_mixedBack_t__pbt == "ok raw=L[] n=1"

-- mixedBack_t__pbt_e: F(*t, z) = t \n F((true, ())*)
def case_mixedBack_t__pbt_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "t", kind := .collecting }, { name := "z" }] [] [] [.param "t"])] [(.call (.resolve "F") [(.sequenceSpread (.capture [.boolLiteral true, (.emptySequence 0)]))])])
#guard obs case_mixedBack_t__pbt_e == "ok raw=L[true] n=1"

-- mixedBack_t__pbt_1: F(*t, z) = t \n F((true, 1)*)
def case_mixedBack_t__pbt_1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "t", kind := .collecting }, { name := "z" }] [] [] [.param "t"])] [(.call (.resolve "F") [(.sequenceSpread (.capture [.boolLiteral true, .num 1]))])])
#guard obs case_mixedBack_t__pbt_1 == "ok raw=L[true] n=1"

-- mixedBack_t__lbt: F(*t, z) = t \n F([true]*)
def case_mixedBack_t__lbt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "t", kind := .collecting }, { name := "z" }] [] [] [.param "t"])] [(.call (.resolve "F") [(.sequenceSpread (.listLiteral [.boolLiteral true]))])])
#guard obs case_mixedBack_t__lbt == "ok raw=L[] n=1"

-- mixedBack_t__lbt_bf: F(*t, z) = t \n F([true, false]*)
def case_mixedBack_t__lbt_bf : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "t", kind := .collecting }, { name := "z" }] [] [] [.param "t"])] [(.call (.resolve "F") [(.sequenceSpread (.listLiteral [.boolLiteral true, .boolLiteral false]))])])
#guard obs case_mixedBack_t__lbt_bf == "ok raw=L[true] n=1"

-- mixedBack_t__lpbt_1: F(*t, z) = t \n F([(true, 1)]*)
def case_mixedBack_t__lpbt_1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "t", kind := .collecting }, { name := "z" }] [] [] [.param "t"])] [(.call (.resolve "F") [(.sequenceSpread (.listLiteral [(.capture [.boolLiteral true, .num 1])]))])])
#guard obs case_mixedBack_t__lpbt_1 == "ok raw=L[] n=1"

-- mixedBack_t__p1: F(*t, z) = t \n F((1)*)
def case_mixedBack_t__p1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "t", kind := .collecting }, { name := "z" }] [] [] [.param "t"])] [(.call (.resolve "F") [(.sequenceSpread (.num 1))])])
#guard obs case_mixedBack_t__p1 == "ok raw=L[] n=1"

-- mixedBack_t__p12: F(*t, z) = t \n F((1, 2)*)
def case_mixedBack_t__p12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "t", kind := .collecting }, { name := "z" }] [] [] [.param "t"])] [(.call (.resolve "F") [(.sequenceSpread (.capture [.num 1, .num 2]))])])
#guard obs case_mixedBack_t__p12 == "ok raw=L[1] n=1"

-- mixedBack_t__p123: F(*t, z) = t \n F((1, 2, 3)*)
def case_mixedBack_t__p123 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "t", kind := .collecting }, { name := "z" }] [] [] [.param "t"])] [(.call (.resolve "F") [(.sequenceSpread (.capture [.num 1, .num 2, .num 3]))])])
#guard obs case_mixedBack_t__p123 == "ok raw=L[1, 2] n=1"

-- mixedBack_t__pee: F(*t, z) = t \n F(((), ())*)
def case_mixedBack_t__pee : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "t", kind := .collecting }, { name := "z" }] [] [] [.param "t"])] [(.call (.resolve "F") [(.sequenceSpread (.capture [(.emptySequence 0), (.emptySequence 0)]))])])
#guard obs case_mixedBack_t__pee == "ok raw=L[S[]] n=1"

-- mixedBack_t__pe1: F(*t, z) = t \n F(((), 1)*)
def case_mixedBack_t__pe1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "t", kind := .collecting }, { name := "z" }] [] [] [.param "t"])] [(.call (.resolve "F") [(.sequenceSpread (.capture [(.emptySequence 0), .num 1]))])])
#guard obs case_mixedBack_t__pe1 == "ok raw=L[S[]] n=1"

-- mixedBack_t__p1e: F(*t, z) = t \n F((1, ())*)
def case_mixedBack_t__p1e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "t", kind := .collecting }, { name := "z" }] [] [] [.param "t"])] [(.call (.resolve "F") [(.sequenceSpread (.capture [.num 1, (.emptySequence 0)]))])])
#guard obs case_mixedBack_t__p1e == "ok raw=L[1] n=1"

-- mixedBack_t__p12_3: F(*t, z) = t \n F(((1, 2), 3)*)
def case_mixedBack_t__p12_3 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "t", kind := .collecting }, { name := "z" }] [] [] [.param "t"])] [(.call (.resolve "F") [(.sequenceSpread (.capture [(.capture [.num 1, .num 2]), .num 3]))])])
#guard obs case_mixedBack_t__p12_3 == "ok raw=L[S[1, 2]] n=1"

-- mixedBack_t__p12_34: F(*t, z) = t \n F(((1, 2), (3, 4))*)
def case_mixedBack_t__p12_34 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "t", kind := .collecting }, { name := "z" }] [] [] [.param "t"])] [(.call (.resolve "F") [(.sequenceSpread (.capture [(.capture [.num 1, .num 2]), (.capture [.num 3, .num 4])]))])])
#guard obs case_mixedBack_t__p12_34 == "ok raw=L[S[1, 2]] n=1"

-- mixedBack_t__pe_12: F(*t, z) = t \n F(((), (1, 2))*)
def case_mixedBack_t__pe_12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "t", kind := .collecting }, { name := "z" }] [] [] [.param "t"])] [(.call (.resolve "F") [(.sequenceSpread (.capture [(.emptySequence 0), (.capture [.num 1, .num 2])]))])])
#guard obs case_mixedBack_t__pe_12 == "ok raw=L[S[]] n=1"

-- mixedBack_t__ppe1_2: F(*t, z) = t \n F((((), 1), 2)*)
def case_mixedBack_t__ppe1_2 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "t", kind := .collecting }, { name := "z" }] [] [] [.param "t"])] [(.call (.resolve "F") [(.sequenceSpread (.capture [(.capture [(.emptySequence 0), .num 1]), .num 2]))])])
#guard obs case_mixedBack_t__ppe1_2 == "ok raw=L[S[S[], 1]] n=1"

-- mixedBack_t__p12_e: F(*t, z) = t \n F(((1, 2), ())*)
def case_mixedBack_t__p12_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "t", kind := .collecting }, { name := "z" }] [] [] [.param "t"])] [(.call (.resolve "F") [(.sequenceSpread (.capture [(.capture [.num 1, .num 2]), (.emptySequence 0)]))])])
#guard obs case_mixedBack_t__p12_e == "ok raw=L[S[1, 2]] n=1"

-- mixedBack_t__ppe: F(*t, z) = t \n F((())*)
def case_mixedBack_t__ppe : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "t", kind := .collecting }, { name := "z" }] [] [] [.param "t"])] [(.call (.resolve "F") [(.sequenceSpread (.emptySequence 0))])])
#guard obs case_mixedBack_t__ppe == "err arity"

-- mixedBack_t__pp1: F(*t, z) = t \n F(((1))*)
def case_mixedBack_t__pp1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "t", kind := .collecting }, { name := "z" }] [] [] [.param "t"])] [(.call (.resolve "F") [(.sequenceSpread (.num 1))])])
#guard obs case_mixedBack_t__pp1 == "ok raw=L[] n=1"

-- mixedBack_t__ppp12: F(*t, z) = t \n F((((1, 2)))*)
def case_mixedBack_t__ppp12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "t", kind := .collecting }, { name := "z" }] [] [] [.param "t"])] [(.call (.resolve "F") [(.sequenceSpread (.capture [.num 1, .num 2]))])])
#guard obs case_mixedBack_t__ppp12 == "ok raw=L[1] n=1"

-- mixedBack_t__le: F(*t, z) = t \n F([]*)
def case_mixedBack_t__le : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "t", kind := .collecting }, { name := "z" }] [] [] [.param "t"])] [(.call (.resolve "F") [(.sequenceSpread (.listLiteral []))])])
#guard obs case_mixedBack_t__le == "err arity"

-- mixedBack_t__l7: F(*t, z) = t \n F([7]*)
def case_mixedBack_t__l7 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "t", kind := .collecting }, { name := "z" }] [] [] [.param "t"])] [(.call (.resolve "F") [(.sequenceSpread (.listLiteral [.num 7]))])])
#guard obs case_mixedBack_t__l7 == "ok raw=L[] n=1"

-- mixedBack_t__l12: F(*t, z) = t \n F([1, 2]*)
def case_mixedBack_t__l12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "t", kind := .collecting }, { name := "z" }] [] [] [.param "t"])] [(.call (.resolve "F") [(.sequenceSpread (.listLiteral [.num 1, .num 2]))])])
#guard obs case_mixedBack_t__l12 == "ok raw=L[1] n=1"

-- mixedBack_t__l12_3: F(*t, z) = t \n F([[1, 2], 3]*)
def case_mixedBack_t__l12_3 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "t", kind := .collecting }, { name := "z" }] [] [] [.param "t"])] [(.call (.resolve "F") [(.sequenceSpread (.listLiteral [(.listLiteral [.num 1, .num 2]), .num 3]))])])
#guard obs case_mixedBack_t__l12_3 == "ok raw=L[L[1, 2]] n=1"

-- mixedBack_t__lle: F(*t, z) = t \n F([[]]*)
def case_mixedBack_t__lle : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "t", kind := .collecting }, { name := "z" }] [] [] [.param "t"])] [(.call (.resolve "F") [(.sequenceSpread (.listLiteral [(.listLiteral [])]))])])
#guard obs case_mixedBack_t__lle == "ok raw=L[] n=1"

-- mixedBack_t__l_e: F(*t, z) = t \n F([()]*)
def case_mixedBack_t__l_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "t", kind := .collecting }, { name := "z" }] [] [] [.param "t"])] [(.call (.resolve "F") [(.sequenceSpread (.listLiteral [(.emptySequence 0)]))])])
#guard obs case_mixedBack_t__l_e == "ok raw=L[] n=1"

-- mixedBack_t__l_p12: F(*t, z) = t \n F([(1, 2)]*)
def case_mixedBack_t__l_p12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "t", kind := .collecting }, { name := "z" }] [] [] [.param "t"])] [(.call (.resolve "F") [(.sequenceSpread (.listLiteral [(.capture [.num 1, .num 2])]))])])
#guard obs case_mixedBack_t__l_p12 == "ok raw=L[] n=1"

-- mixedBack_t__p_l12: F(*t, z) = t \n F(([1, 2], 3)*)
def case_mixedBack_t__p_l12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "t", kind := .collecting }, { name := "z" }] [] [] [.param "t"])] [(.call (.resolve "F") [(.sequenceSpread (.capture [(.listLiteral [.num 1, .num 2]), .num 3]))])])
#guard obs case_mixedBack_t__p_l12 == "ok raw=L[L[1, 2]] n=1"

-- mixedBack_t__pl1: F(*t, z) = t \n F(([1])*)
def case_mixedBack_t__pl1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "t", kind := .collecting }, { name := "z" }] [] [] [.param "t"])] [(.call (.resolve "F") [(.sequenceSpread (.listLiteral [.num 1]))])])
#guard obs case_mixedBack_t__pl1 == "ok raw=L[] n=1"

-- mixedBack_z__e: F(*t, z) = z \n F(()*)
def case_mixedBack_z__e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "t", kind := .collecting }, { name := "z" }] [] [] [.param "z"])] [(.call (.resolve "F") [(.sequenceSpread (.emptySequence 0))])])
#guard obs case_mixedBack_z__e == "err arity"

-- mixedBack_z__n0: F(*t, z) = z \n F(0*)
def case_mixedBack_z__n0 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "t", kind := .collecting }, { name := "z" }] [] [] [.param "z"])] [(.call (.resolve "F") [(.sequenceSpread (.num 0))])])
#guard obs case_mixedBack_z__n0 == "ok raw=0 n=1"

-- mixedBack_z__n1: F(*t, z) = z \n F(1*)
def case_mixedBack_z__n1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "t", kind := .collecting }, { name := "z" }] [] [] [.param "z"])] [(.call (.resolve "F") [(.sequenceSpread (.num 1))])])
#guard obs case_mixedBack_z__n1 == "ok raw=1 n=1"

-- mixedBack_z__bt: F(*t, z) = z \n F(true*)
def case_mixedBack_z__bt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "t", kind := .collecting }, { name := "z" }] [] [] [.param "z"])] [(.call (.resolve "F") [(.sequenceSpread (.boolLiteral true))])])
#guard obs case_mixedBack_z__bt == "ok raw=true n=1"

-- mixedBack_z__bf: F(*t, z) = z \n F(false*)
def case_mixedBack_z__bf : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "t", kind := .collecting }, { name := "z" }] [] [] [.param "z"])] [(.call (.resolve "F") [(.sequenceSpread (.boolLiteral false))])])
#guard obs case_mixedBack_z__bf == "ok raw=false n=1"

-- mixedBack_z__pbt: F(*t, z) = z \n F((true)*)
def case_mixedBack_z__pbt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "t", kind := .collecting }, { name := "z" }] [] [] [.param "z"])] [(.call (.resolve "F") [(.sequenceSpread (.boolLiteral true))])])
#guard obs case_mixedBack_z__pbt == "ok raw=true n=1"

-- mixedBack_z__pbt_e: F(*t, z) = z \n F((true, ())*)
def case_mixedBack_z__pbt_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "t", kind := .collecting }, { name := "z" }] [] [] [.param "z"])] [(.call (.resolve "F") [(.sequenceSpread (.capture [.boolLiteral true, (.emptySequence 0)]))])])
#guard obs case_mixedBack_z__pbt_e == "ok raw=S[] n=1"

-- mixedBack_z__pbt_1: F(*t, z) = z \n F((true, 1)*)
def case_mixedBack_z__pbt_1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "t", kind := .collecting }, { name := "z" }] [] [] [.param "z"])] [(.call (.resolve "F") [(.sequenceSpread (.capture [.boolLiteral true, .num 1]))])])
#guard obs case_mixedBack_z__pbt_1 == "ok raw=1 n=1"

-- mixedBack_z__lbt: F(*t, z) = z \n F([true]*)
def case_mixedBack_z__lbt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "t", kind := .collecting }, { name := "z" }] [] [] [.param "z"])] [(.call (.resolve "F") [(.sequenceSpread (.listLiteral [.boolLiteral true]))])])
#guard obs case_mixedBack_z__lbt == "ok raw=true n=1"

-- mixedBack_z__lbt_bf: F(*t, z) = z \n F([true, false]*)
def case_mixedBack_z__lbt_bf : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "t", kind := .collecting }, { name := "z" }] [] [] [.param "z"])] [(.call (.resolve "F") [(.sequenceSpread (.listLiteral [.boolLiteral true, .boolLiteral false]))])])
#guard obs case_mixedBack_z__lbt_bf == "ok raw=false n=1"

-- mixedBack_z__lpbt_1: F(*t, z) = z \n F([(true, 1)]*)
def case_mixedBack_z__lpbt_1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "t", kind := .collecting }, { name := "z" }] [] [] [.param "z"])] [(.call (.resolve "F") [(.sequenceSpread (.listLiteral [(.capture [.boolLiteral true, .num 1])]))])])
#guard obs case_mixedBack_z__lpbt_1 == "ok raw=S[true, 1] n=1"

-- mixedBack_z__p1: F(*t, z) = z \n F((1)*)
def case_mixedBack_z__p1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "t", kind := .collecting }, { name := "z" }] [] [] [.param "z"])] [(.call (.resolve "F") [(.sequenceSpread (.num 1))])])
#guard obs case_mixedBack_z__p1 == "ok raw=1 n=1"

-- mixedBack_z__p12: F(*t, z) = z \n F((1, 2)*)
def case_mixedBack_z__p12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "t", kind := .collecting }, { name := "z" }] [] [] [.param "z"])] [(.call (.resolve "F") [(.sequenceSpread (.capture [.num 1, .num 2]))])])
#guard obs case_mixedBack_z__p12 == "ok raw=2 n=1"

-- mixedBack_z__p123: F(*t, z) = z \n F((1, 2, 3)*)
def case_mixedBack_z__p123 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "t", kind := .collecting }, { name := "z" }] [] [] [.param "z"])] [(.call (.resolve "F") [(.sequenceSpread (.capture [.num 1, .num 2, .num 3]))])])
#guard obs case_mixedBack_z__p123 == "ok raw=3 n=1"

-- mixedBack_z__pee: F(*t, z) = z \n F(((), ())*)
def case_mixedBack_z__pee : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "t", kind := .collecting }, { name := "z" }] [] [] [.param "z"])] [(.call (.resolve "F") [(.sequenceSpread (.capture [(.emptySequence 0), (.emptySequence 0)]))])])
#guard obs case_mixedBack_z__pee == "ok raw=S[] n=1"

-- mixedBack_z__pe1: F(*t, z) = z \n F(((), 1)*)
def case_mixedBack_z__pe1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "t", kind := .collecting }, { name := "z" }] [] [] [.param "z"])] [(.call (.resolve "F") [(.sequenceSpread (.capture [(.emptySequence 0), .num 1]))])])
#guard obs case_mixedBack_z__pe1 == "ok raw=1 n=1"

-- mixedBack_z__p1e: F(*t, z) = z \n F((1, ())*)
def case_mixedBack_z__p1e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "t", kind := .collecting }, { name := "z" }] [] [] [.param "z"])] [(.call (.resolve "F") [(.sequenceSpread (.capture [.num 1, (.emptySequence 0)]))])])
#guard obs case_mixedBack_z__p1e == "ok raw=S[] n=1"

-- mixedBack_z__p12_3: F(*t, z) = z \n F(((1, 2), 3)*)
def case_mixedBack_z__p12_3 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "t", kind := .collecting }, { name := "z" }] [] [] [.param "z"])] [(.call (.resolve "F") [(.sequenceSpread (.capture [(.capture [.num 1, .num 2]), .num 3]))])])
#guard obs case_mixedBack_z__p12_3 == "ok raw=3 n=1"

-- mixedBack_z__p12_34: F(*t, z) = z \n F(((1, 2), (3, 4))*)
def case_mixedBack_z__p12_34 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "t", kind := .collecting }, { name := "z" }] [] [] [.param "z"])] [(.call (.resolve "F") [(.sequenceSpread (.capture [(.capture [.num 1, .num 2]), (.capture [.num 3, .num 4])]))])])
#guard obs case_mixedBack_z__p12_34 == "ok raw=S[3, 4] n=1"

-- mixedBack_z__pe_12: F(*t, z) = z \n F(((), (1, 2))*)
def case_mixedBack_z__pe_12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "t", kind := .collecting }, { name := "z" }] [] [] [.param "z"])] [(.call (.resolve "F") [(.sequenceSpread (.capture [(.emptySequence 0), (.capture [.num 1, .num 2])]))])])
#guard obs case_mixedBack_z__pe_12 == "ok raw=S[1, 2] n=1"

-- mixedBack_z__ppe1_2: F(*t, z) = z \n F((((), 1), 2)*)
def case_mixedBack_z__ppe1_2 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "t", kind := .collecting }, { name := "z" }] [] [] [.param "z"])] [(.call (.resolve "F") [(.sequenceSpread (.capture [(.capture [(.emptySequence 0), .num 1]), .num 2]))])])
#guard obs case_mixedBack_z__ppe1_2 == "ok raw=2 n=1"

-- mixedBack_z__p12_e: F(*t, z) = z \n F(((1, 2), ())*)
def case_mixedBack_z__p12_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "t", kind := .collecting }, { name := "z" }] [] [] [.param "z"])] [(.call (.resolve "F") [(.sequenceSpread (.capture [(.capture [.num 1, .num 2]), (.emptySequence 0)]))])])
#guard obs case_mixedBack_z__p12_e == "ok raw=S[] n=1"

-- mixedBack_z__ppe: F(*t, z) = z \n F((())*)
def case_mixedBack_z__ppe : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "t", kind := .collecting }, { name := "z" }] [] [] [.param "z"])] [(.call (.resolve "F") [(.sequenceSpread (.emptySequence 0))])])
#guard obs case_mixedBack_z__ppe == "err arity"

-- mixedBack_z__pp1: F(*t, z) = z \n F(((1))*)
def case_mixedBack_z__pp1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "t", kind := .collecting }, { name := "z" }] [] [] [.param "z"])] [(.call (.resolve "F") [(.sequenceSpread (.num 1))])])
#guard obs case_mixedBack_z__pp1 == "ok raw=1 n=1"

-- mixedBack_z__ppp12: F(*t, z) = z \n F((((1, 2)))*)
def case_mixedBack_z__ppp12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "t", kind := .collecting }, { name := "z" }] [] [] [.param "z"])] [(.call (.resolve "F") [(.sequenceSpread (.capture [.num 1, .num 2]))])])
#guard obs case_mixedBack_z__ppp12 == "ok raw=2 n=1"

-- mixedBack_z__le: F(*t, z) = z \n F([]*)
def case_mixedBack_z__le : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "t", kind := .collecting }, { name := "z" }] [] [] [.param "z"])] [(.call (.resolve "F") [(.sequenceSpread (.listLiteral []))])])
#guard obs case_mixedBack_z__le == "err arity"

-- mixedBack_z__l7: F(*t, z) = z \n F([7]*)
def case_mixedBack_z__l7 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "t", kind := .collecting }, { name := "z" }] [] [] [.param "z"])] [(.call (.resolve "F") [(.sequenceSpread (.listLiteral [.num 7]))])])
#guard obs case_mixedBack_z__l7 == "ok raw=7 n=1"

-- mixedBack_z__l12: F(*t, z) = z \n F([1, 2]*)
def case_mixedBack_z__l12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "t", kind := .collecting }, { name := "z" }] [] [] [.param "z"])] [(.call (.resolve "F") [(.sequenceSpread (.listLiteral [.num 1, .num 2]))])])
#guard obs case_mixedBack_z__l12 == "ok raw=2 n=1"

-- mixedBack_z__l12_3: F(*t, z) = z \n F([[1, 2], 3]*)
def case_mixedBack_z__l12_3 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "t", kind := .collecting }, { name := "z" }] [] [] [.param "z"])] [(.call (.resolve "F") [(.sequenceSpread (.listLiteral [(.listLiteral [.num 1, .num 2]), .num 3]))])])
#guard obs case_mixedBack_z__l12_3 == "ok raw=3 n=1"

-- mixedBack_z__lle: F(*t, z) = z \n F([[]]*)
def case_mixedBack_z__lle : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "t", kind := .collecting }, { name := "z" }] [] [] [.param "z"])] [(.call (.resolve "F") [(.sequenceSpread (.listLiteral [(.listLiteral [])]))])])
#guard obs case_mixedBack_z__lle == "ok raw=L[] n=1"

-- mixedBack_z__l_e: F(*t, z) = z \n F([()]*)
def case_mixedBack_z__l_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "t", kind := .collecting }, { name := "z" }] [] [] [.param "z"])] [(.call (.resolve "F") [(.sequenceSpread (.listLiteral [(.emptySequence 0)]))])])
#guard obs case_mixedBack_z__l_e == "ok raw=S[] n=1"

-- mixedBack_z__l_p12: F(*t, z) = z \n F([(1, 2)]*)
def case_mixedBack_z__l_p12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "t", kind := .collecting }, { name := "z" }] [] [] [.param "z"])] [(.call (.resolve "F") [(.sequenceSpread (.listLiteral [(.capture [.num 1, .num 2])]))])])
#guard obs case_mixedBack_z__l_p12 == "ok raw=S[1, 2] n=1"

-- mixedBack_z__p_l12: F(*t, z) = z \n F(([1, 2], 3)*)
def case_mixedBack_z__p_l12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "t", kind := .collecting }, { name := "z" }] [] [] [.param "z"])] [(.call (.resolve "F") [(.sequenceSpread (.capture [(.listLiteral [.num 1, .num 2]), .num 3]))])])
#guard obs case_mixedBack_z__p_l12 == "ok raw=3 n=1"

-- mixedBack_z__pl1: F(*t, z) = z \n F(([1])*)
def case_mixedBack_z__pl1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "t", kind := .collecting }, { name := "z" }] [] [] [.param "z"])] [(.call (.resolve "F") [(.sequenceSpread (.listLiteral [.num 1]))])])
#guard obs case_mixedBack_z__pl1 == "ok raw=1 n=1"

-- deconPair_x__e: x, y = () \n x
def case_deconPair_x__e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.emptySequence 0)]), privateProp "x" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) [.resolve "$deconstruct$0"])]), privateProp "y" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) [.resolve "$deconstruct$0"])])] [.resolve "x"])
#guard obs case_deconPair_x__e == "err arity"

-- deconPair_x__n0: x, y = 0 \n x
def case_deconPair_x__n0 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [.num 0]), privateProp "x" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) [.resolve "$deconstruct$0"])]), privateProp "y" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) [.resolve "$deconstruct$0"])])] [.resolve "x"])
#guard obs case_deconPair_x__n0 == "err arity"

-- deconPair_x__n1: x, y = 1 \n x
def case_deconPair_x__n1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [.num 1]), privateProp "x" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) [.resolve "$deconstruct$0"])]), privateProp "y" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) [.resolve "$deconstruct$0"])])] [.resolve "x"])
#guard obs case_deconPair_x__n1 == "err arity"

-- deconPair_x__bt: x, y = true \n x
def case_deconPair_x__bt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [.boolLiteral true]), privateProp "x" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) [.resolve "$deconstruct$0"])]), privateProp "y" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) [.resolve "$deconstruct$0"])])] [.resolve "x"])
#guard obs case_deconPair_x__bt == "err arity"

-- deconPair_x__bf: x, y = false \n x
def case_deconPair_x__bf : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [.boolLiteral false]), privateProp "x" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) [.resolve "$deconstruct$0"])]), privateProp "y" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) [.resolve "$deconstruct$0"])])] [.resolve "x"])
#guard obs case_deconPair_x__bf == "err arity"

-- deconPair_x__pbt: x, y = (true) \n x
def case_deconPair_x__pbt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [.boolLiteral true]), privateProp "x" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) [.resolve "$deconstruct$0"])]), privateProp "y" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) [.resolve "$deconstruct$0"])])] [.resolve "x"])
#guard obs case_deconPair_x__pbt == "err arity"

-- deconPair_x__pbt_e: x, y = (true, ()) \n x
def case_deconPair_x__pbt_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [.boolLiteral true, (.emptySequence 0)])]), privateProp "x" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) [.resolve "$deconstruct$0"])]), privateProp "y" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) [.resolve "$deconstruct$0"])])] [.resolve "x"])
#guard obs case_deconPair_x__pbt_e == "ok raw=true n=1"

-- deconPair_x__pbt_1: x, y = (true, 1) \n x
def case_deconPair_x__pbt_1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [.boolLiteral true, .num 1])]), privateProp "x" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) [.resolve "$deconstruct$0"])]), privateProp "y" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) [.resolve "$deconstruct$0"])])] [.resolve "x"])
#guard obs case_deconPair_x__pbt_1 == "ok raw=true n=1"

-- deconPair_x__lbt: x, y = [true] \n x
def case_deconPair_x__lbt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.listLiteral [.boolLiteral true])]), privateProp "x" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) [.resolve "$deconstruct$0"])]), privateProp "y" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) [.resolve "$deconstruct$0"])])] [.resolve "x"])
#guard obs case_deconPair_x__lbt == "err arity"

-- deconPair_x__lbt_bf: x, y = [true, false] \n x
def case_deconPair_x__lbt_bf : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.listLiteral [.boolLiteral true, .boolLiteral false])]), privateProp "x" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) [.resolve "$deconstruct$0"])]), privateProp "y" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) [.resolve "$deconstruct$0"])])] [.resolve "x"])
#guard obs case_deconPair_x__lbt_bf == "ok raw=true n=1"

-- deconPair_x__lpbt_1: x, y = [(true, 1)] \n x
def case_deconPair_x__lpbt_1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.listLiteral [(.capture [.boolLiteral true, .num 1])])]), privateProp "x" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) [.resolve "$deconstruct$0"])]), privateProp "y" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) [.resolve "$deconstruct$0"])])] [.resolve "x"])
#guard obs case_deconPair_x__lpbt_1 == "err arity"

-- deconPair_x__p1: x, y = (1) \n x
def case_deconPair_x__p1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [.num 1]), privateProp "x" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) [.resolve "$deconstruct$0"])]), privateProp "y" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) [.resolve "$deconstruct$0"])])] [.resolve "x"])
#guard obs case_deconPair_x__p1 == "err arity"

-- deconPair_x__p12: x, y = (1, 2) \n x
def case_deconPair_x__p12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [.num 1, .num 2])]), privateProp "x" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) [.resolve "$deconstruct$0"])]), privateProp "y" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) [.resolve "$deconstruct$0"])])] [.resolve "x"])
#guard obs case_deconPair_x__p12 == "ok raw=1 n=1"

-- deconPair_x__p123: x, y = (1, 2, 3) \n x
def case_deconPair_x__p123 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [.num 1, .num 2, .num 3])]), privateProp "x" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) [.resolve "$deconstruct$0"])]), privateProp "y" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) [.resolve "$deconstruct$0"])])] [.resolve "x"])
#guard obs case_deconPair_x__p123 == "err arity"

-- deconPair_x__pee: x, y = ((), ()) \n x
def case_deconPair_x__pee : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [(.emptySequence 0), (.emptySequence 0)])]), privateProp "x" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) [.resolve "$deconstruct$0"])]), privateProp "y" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) [.resolve "$deconstruct$0"])])] [.resolve "x"])
#guard obs case_deconPair_x__pee == "ok raw=S[] n=1"

-- deconPair_x__pe1: x, y = ((), 1) \n x
def case_deconPair_x__pe1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [(.emptySequence 0), .num 1])]), privateProp "x" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) [.resolve "$deconstruct$0"])]), privateProp "y" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) [.resolve "$deconstruct$0"])])] [.resolve "x"])
#guard obs case_deconPair_x__pe1 == "ok raw=S[] n=1"

-- deconPair_x__p1e: x, y = (1, ()) \n x
def case_deconPair_x__p1e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [.num 1, (.emptySequence 0)])]), privateProp "x" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) [.resolve "$deconstruct$0"])]), privateProp "y" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) [.resolve "$deconstruct$0"])])] [.resolve "x"])
#guard obs case_deconPair_x__p1e == "ok raw=1 n=1"

-- deconPair_x__p12_3: x, y = ((1, 2), 3) \n x
def case_deconPair_x__p12_3 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [(.capture [.num 1, .num 2]), .num 3])]), privateProp "x" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) [.resolve "$deconstruct$0"])]), privateProp "y" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) [.resolve "$deconstruct$0"])])] [.resolve "x"])
#guard obs case_deconPair_x__p12_3 == "ok raw=S[1, 2] n=1"

-- deconPair_x__p12_34: x, y = ((1, 2), (3, 4)) \n x
def case_deconPair_x__p12_34 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [(.capture [.num 1, .num 2]), (.capture [.num 3, .num 4])])]), privateProp "x" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) [.resolve "$deconstruct$0"])]), privateProp "y" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) [.resolve "$deconstruct$0"])])] [.resolve "x"])
#guard obs case_deconPair_x__p12_34 == "ok raw=S[1, 2] n=1"

-- deconPair_x__pe_12: x, y = ((), (1, 2)) \n x
def case_deconPair_x__pe_12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [(.emptySequence 0), (.capture [.num 1, .num 2])])]), privateProp "x" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) [.resolve "$deconstruct$0"])]), privateProp "y" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) [.resolve "$deconstruct$0"])])] [.resolve "x"])
#guard obs case_deconPair_x__pe_12 == "ok raw=S[] n=1"

-- deconPair_x__ppe1_2: x, y = (((), 1), 2) \n x
def case_deconPair_x__ppe1_2 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [(.capture [(.emptySequence 0), .num 1]), .num 2])]), privateProp "x" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) [.resolve "$deconstruct$0"])]), privateProp "y" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) [.resolve "$deconstruct$0"])])] [.resolve "x"])
#guard obs case_deconPair_x__ppe1_2 == "ok raw=S[S[], 1] n=1"

-- deconPair_x__p12_e: x, y = ((1, 2), ()) \n x
def case_deconPair_x__p12_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [(.capture [.num 1, .num 2]), (.emptySequence 0)])]), privateProp "x" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) [.resolve "$deconstruct$0"])]), privateProp "y" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) [.resolve "$deconstruct$0"])])] [.resolve "x"])
#guard obs case_deconPair_x__p12_e == "ok raw=S[1, 2] n=1"

-- deconPair_x__ppe: x, y = (()) \n x
def case_deconPair_x__ppe : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.emptySequence 0)]), privateProp "x" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) [.resolve "$deconstruct$0"])]), privateProp "y" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) [.resolve "$deconstruct$0"])])] [.resolve "x"])
#guard obs case_deconPair_x__ppe == "err arity"

-- deconPair_x__pp1: x, y = ((1)) \n x
def case_deconPair_x__pp1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [.num 1]), privateProp "x" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) [.resolve "$deconstruct$0"])]), privateProp "y" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) [.resolve "$deconstruct$0"])])] [.resolve "x"])
#guard obs case_deconPair_x__pp1 == "err arity"

-- deconPair_x__ppp12: x, y = (((1, 2))) \n x
def case_deconPair_x__ppp12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [.num 1, .num 2])]), privateProp "x" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) [.resolve "$deconstruct$0"])]), privateProp "y" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) [.resolve "$deconstruct$0"])])] [.resolve "x"])
#guard obs case_deconPair_x__ppp12 == "ok raw=1 n=1"

-- deconPair_x__le: x, y = [] \n x
def case_deconPair_x__le : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.listLiteral [])]), privateProp "x" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) [.resolve "$deconstruct$0"])]), privateProp "y" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) [.resolve "$deconstruct$0"])])] [.resolve "x"])
#guard obs case_deconPair_x__le == "err arity"

-- deconPair_x__l7: x, y = [7] \n x
def case_deconPair_x__l7 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.listLiteral [.num 7])]), privateProp "x" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) [.resolve "$deconstruct$0"])]), privateProp "y" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) [.resolve "$deconstruct$0"])])] [.resolve "x"])
#guard obs case_deconPair_x__l7 == "err arity"

-- deconPair_x__l12: x, y = [1, 2] \n x
def case_deconPair_x__l12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.listLiteral [.num 1, .num 2])]), privateProp "x" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) [.resolve "$deconstruct$0"])]), privateProp "y" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) [.resolve "$deconstruct$0"])])] [.resolve "x"])
#guard obs case_deconPair_x__l12 == "ok raw=1 n=1"

-- deconPair_x__l12_3: x, y = [[1, 2], 3] \n x
def case_deconPair_x__l12_3 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.listLiteral [(.listLiteral [.num 1, .num 2]), .num 3])]), privateProp "x" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) [.resolve "$deconstruct$0"])]), privateProp "y" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) [.resolve "$deconstruct$0"])])] [.resolve "x"])
#guard obs case_deconPair_x__l12_3 == "ok raw=L[1, 2] n=1"

-- deconPair_x__lle: x, y = [[]] \n x
def case_deconPair_x__lle : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.listLiteral [(.listLiteral [])])]), privateProp "x" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) [.resolve "$deconstruct$0"])]), privateProp "y" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) [.resolve "$deconstruct$0"])])] [.resolve "x"])
#guard obs case_deconPair_x__lle == "err arity"

-- deconPair_x__l_e: x, y = [()] \n x
def case_deconPair_x__l_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.listLiteral [(.emptySequence 0)])]), privateProp "x" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) [.resolve "$deconstruct$0"])]), privateProp "y" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) [.resolve "$deconstruct$0"])])] [.resolve "x"])
#guard obs case_deconPair_x__l_e == "err arity"

-- deconPair_x__l_p12: x, y = [(1, 2)] \n x
def case_deconPair_x__l_p12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.listLiteral [(.capture [.num 1, .num 2])])]), privateProp "x" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) [.resolve "$deconstruct$0"])]), privateProp "y" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) [.resolve "$deconstruct$0"])])] [.resolve "x"])
#guard obs case_deconPair_x__l_p12 == "err arity"

-- deconPair_x__p_l12: x, y = ([1, 2], 3) \n x
def case_deconPair_x__p_l12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [(.listLiteral [.num 1, .num 2]), .num 3])]), privateProp "x" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) [.resolve "$deconstruct$0"])]), privateProp "y" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) [.resolve "$deconstruct$0"])])] [.resolve "x"])
#guard obs case_deconPair_x__p_l12 == "ok raw=L[1, 2] n=1"

-- deconPair_x__pl1: x, y = ([1]) \n x
def case_deconPair_x__pl1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.listLiteral [.num 1])]), privateProp "x" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) [.resolve "$deconstruct$0"])]), privateProp "y" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) [.resolve "$deconstruct$0"])])] [.resolve "x"])
#guard obs case_deconPair_x__pl1 == "err arity"

-- deconPair_y__e: x, y = () \n y
def case_deconPair_y__e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.emptySequence 0)]), privateProp "x" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) [.resolve "$deconstruct$0"])]), privateProp "y" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) [.resolve "$deconstruct$0"])])] [.resolve "y"])
#guard obs case_deconPair_y__e == "err arity"

-- deconPair_y__n0: x, y = 0 \n y
def case_deconPair_y__n0 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [.num 0]), privateProp "x" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) [.resolve "$deconstruct$0"])]), privateProp "y" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) [.resolve "$deconstruct$0"])])] [.resolve "y"])
#guard obs case_deconPair_y__n0 == "err arity"

-- deconPair_y__n1: x, y = 1 \n y
def case_deconPair_y__n1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [.num 1]), privateProp "x" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) [.resolve "$deconstruct$0"])]), privateProp "y" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) [.resolve "$deconstruct$0"])])] [.resolve "y"])
#guard obs case_deconPair_y__n1 == "err arity"

-- deconPair_y__bt: x, y = true \n y
def case_deconPair_y__bt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [.boolLiteral true]), privateProp "x" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) [.resolve "$deconstruct$0"])]), privateProp "y" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) [.resolve "$deconstruct$0"])])] [.resolve "y"])
#guard obs case_deconPair_y__bt == "err arity"

-- deconPair_y__bf: x, y = false \n y
def case_deconPair_y__bf : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [.boolLiteral false]), privateProp "x" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) [.resolve "$deconstruct$0"])]), privateProp "y" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) [.resolve "$deconstruct$0"])])] [.resolve "y"])
#guard obs case_deconPair_y__bf == "err arity"

-- deconPair_y__pbt: x, y = (true) \n y
def case_deconPair_y__pbt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [.boolLiteral true]), privateProp "x" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) [.resolve "$deconstruct$0"])]), privateProp "y" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) [.resolve "$deconstruct$0"])])] [.resolve "y"])
#guard obs case_deconPair_y__pbt == "err arity"

-- deconPair_y__pbt_e: x, y = (true, ()) \n y
def case_deconPair_y__pbt_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [.boolLiteral true, (.emptySequence 0)])]), privateProp "x" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) [.resolve "$deconstruct$0"])]), privateProp "y" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) [.resolve "$deconstruct$0"])])] [.resolve "y"])
#guard obs case_deconPair_y__pbt_e == "ok raw=S[] n=1"

-- deconPair_y__pbt_1: x, y = (true, 1) \n y
def case_deconPair_y__pbt_1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [.boolLiteral true, .num 1])]), privateProp "x" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) [.resolve "$deconstruct$0"])]), privateProp "y" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) [.resolve "$deconstruct$0"])])] [.resolve "y"])
#guard obs case_deconPair_y__pbt_1 == "ok raw=1 n=1"

-- deconPair_y__lbt: x, y = [true] \n y
def case_deconPair_y__lbt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.listLiteral [.boolLiteral true])]), privateProp "x" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) [.resolve "$deconstruct$0"])]), privateProp "y" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) [.resolve "$deconstruct$0"])])] [.resolve "y"])
#guard obs case_deconPair_y__lbt == "err arity"

-- deconPair_y__lbt_bf: x, y = [true, false] \n y
def case_deconPair_y__lbt_bf : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.listLiteral [.boolLiteral true, .boolLiteral false])]), privateProp "x" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) [.resolve "$deconstruct$0"])]), privateProp "y" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) [.resolve "$deconstruct$0"])])] [.resolve "y"])
#guard obs case_deconPair_y__lbt_bf == "ok raw=false n=1"

-- deconPair_y__lpbt_1: x, y = [(true, 1)] \n y
def case_deconPair_y__lpbt_1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.listLiteral [(.capture [.boolLiteral true, .num 1])])]), privateProp "x" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) [.resolve "$deconstruct$0"])]), privateProp "y" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) [.resolve "$deconstruct$0"])])] [.resolve "y"])
#guard obs case_deconPair_y__lpbt_1 == "err arity"

-- deconPair_y__p1: x, y = (1) \n y
def case_deconPair_y__p1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [.num 1]), privateProp "x" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) [.resolve "$deconstruct$0"])]), privateProp "y" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) [.resolve "$deconstruct$0"])])] [.resolve "y"])
#guard obs case_deconPair_y__p1 == "err arity"

-- deconPair_y__p12: x, y = (1, 2) \n y
def case_deconPair_y__p12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [.num 1, .num 2])]), privateProp "x" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) [.resolve "$deconstruct$0"])]), privateProp "y" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) [.resolve "$deconstruct$0"])])] [.resolve "y"])
#guard obs case_deconPair_y__p12 == "ok raw=2 n=1"

-- deconPair_y__p123: x, y = (1, 2, 3) \n y
def case_deconPair_y__p123 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [.num 1, .num 2, .num 3])]), privateProp "x" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) [.resolve "$deconstruct$0"])]), privateProp "y" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) [.resolve "$deconstruct$0"])])] [.resolve "y"])
#guard obs case_deconPair_y__p123 == "err arity"

-- deconPair_y__pee: x, y = ((), ()) \n y
def case_deconPair_y__pee : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [(.emptySequence 0), (.emptySequence 0)])]), privateProp "x" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) [.resolve "$deconstruct$0"])]), privateProp "y" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) [.resolve "$deconstruct$0"])])] [.resolve "y"])
#guard obs case_deconPair_y__pee == "ok raw=S[] n=1"

-- deconPair_y__pe1: x, y = ((), 1) \n y
def case_deconPair_y__pe1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [(.emptySequence 0), .num 1])]), privateProp "x" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) [.resolve "$deconstruct$0"])]), privateProp "y" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) [.resolve "$deconstruct$0"])])] [.resolve "y"])
#guard obs case_deconPair_y__pe1 == "ok raw=1 n=1"

-- deconPair_y__p1e: x, y = (1, ()) \n y
def case_deconPair_y__p1e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [.num 1, (.emptySequence 0)])]), privateProp "x" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) [.resolve "$deconstruct$0"])]), privateProp "y" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) [.resolve "$deconstruct$0"])])] [.resolve "y"])
#guard obs case_deconPair_y__p1e == "ok raw=S[] n=1"

-- deconPair_y__p12_3: x, y = ((1, 2), 3) \n y
def case_deconPair_y__p12_3 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [(.capture [.num 1, .num 2]), .num 3])]), privateProp "x" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) [.resolve "$deconstruct$0"])]), privateProp "y" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) [.resolve "$deconstruct$0"])])] [.resolve "y"])
#guard obs case_deconPair_y__p12_3 == "ok raw=3 n=1"

-- deconPair_y__p12_34: x, y = ((1, 2), (3, 4)) \n y
def case_deconPair_y__p12_34 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [(.capture [.num 1, .num 2]), (.capture [.num 3, .num 4])])]), privateProp "x" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) [.resolve "$deconstruct$0"])]), privateProp "y" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) [.resolve "$deconstruct$0"])])] [.resolve "y"])
#guard obs case_deconPair_y__p12_34 == "ok raw=S[3, 4] n=1"

-- deconPair_y__pe_12: x, y = ((), (1, 2)) \n y
def case_deconPair_y__pe_12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [(.emptySequence 0), (.capture [.num 1, .num 2])])]), privateProp "x" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) [.resolve "$deconstruct$0"])]), privateProp "y" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) [.resolve "$deconstruct$0"])])] [.resolve "y"])
#guard obs case_deconPair_y__pe_12 == "ok raw=S[1, 2] n=1"

-- deconPair_y__ppe1_2: x, y = (((), 1), 2) \n y
def case_deconPair_y__ppe1_2 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [(.capture [(.emptySequence 0), .num 1]), .num 2])]), privateProp "x" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) [.resolve "$deconstruct$0"])]), privateProp "y" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) [.resolve "$deconstruct$0"])])] [.resolve "y"])
#guard obs case_deconPair_y__ppe1_2 == "ok raw=2 n=1"

-- deconPair_y__p12_e: x, y = ((1, 2), ()) \n y
def case_deconPair_y__p12_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [(.capture [.num 1, .num 2]), (.emptySequence 0)])]), privateProp "x" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) [.resolve "$deconstruct$0"])]), privateProp "y" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) [.resolve "$deconstruct$0"])])] [.resolve "y"])
#guard obs case_deconPair_y__p12_e == "ok raw=S[] n=1"

-- deconPair_y__ppe: x, y = (()) \n y
def case_deconPair_y__ppe : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.emptySequence 0)]), privateProp "x" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) [.resolve "$deconstruct$0"])]), privateProp "y" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) [.resolve "$deconstruct$0"])])] [.resolve "y"])
#guard obs case_deconPair_y__ppe == "err arity"

-- deconPair_y__pp1: x, y = ((1)) \n y
def case_deconPair_y__pp1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [.num 1]), privateProp "x" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) [.resolve "$deconstruct$0"])]), privateProp "y" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) [.resolve "$deconstruct$0"])])] [.resolve "y"])
#guard obs case_deconPair_y__pp1 == "err arity"

-- deconPair_y__ppp12: x, y = (((1, 2))) \n y
def case_deconPair_y__ppp12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [.num 1, .num 2])]), privateProp "x" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) [.resolve "$deconstruct$0"])]), privateProp "y" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) [.resolve "$deconstruct$0"])])] [.resolve "y"])
#guard obs case_deconPair_y__ppp12 == "ok raw=2 n=1"

-- deconPair_y__le: x, y = [] \n y
def case_deconPair_y__le : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.listLiteral [])]), privateProp "x" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) [.resolve "$deconstruct$0"])]), privateProp "y" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) [.resolve "$deconstruct$0"])])] [.resolve "y"])
#guard obs case_deconPair_y__le == "err arity"

-- deconPair_y__l7: x, y = [7] \n y
def case_deconPair_y__l7 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.listLiteral [.num 7])]), privateProp "x" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) [.resolve "$deconstruct$0"])]), privateProp "y" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) [.resolve "$deconstruct$0"])])] [.resolve "y"])
#guard obs case_deconPair_y__l7 == "err arity"

-- deconPair_y__l12: x, y = [1, 2] \n y
def case_deconPair_y__l12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.listLiteral [.num 1, .num 2])]), privateProp "x" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) [.resolve "$deconstruct$0"])]), privateProp "y" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) [.resolve "$deconstruct$0"])])] [.resolve "y"])
#guard obs case_deconPair_y__l12 == "ok raw=2 n=1"

-- deconPair_y__l12_3: x, y = [[1, 2], 3] \n y
def case_deconPair_y__l12_3 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.listLiteral [(.listLiteral [.num 1, .num 2]), .num 3])]), privateProp "x" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) [.resolve "$deconstruct$0"])]), privateProp "y" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) [.resolve "$deconstruct$0"])])] [.resolve "y"])
#guard obs case_deconPair_y__l12_3 == "ok raw=3 n=1"

-- deconPair_y__lle: x, y = [[]] \n y
def case_deconPair_y__lle : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.listLiteral [(.listLiteral [])])]), privateProp "x" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) [.resolve "$deconstruct$0"])]), privateProp "y" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) [.resolve "$deconstruct$0"])])] [.resolve "y"])
#guard obs case_deconPair_y__lle == "err arity"

-- deconPair_y__l_e: x, y = [()] \n y
def case_deconPair_y__l_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.listLiteral [(.emptySequence 0)])]), privateProp "x" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) [.resolve "$deconstruct$0"])]), privateProp "y" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) [.resolve "$deconstruct$0"])])] [.resolve "y"])
#guard obs case_deconPair_y__l_e == "err arity"

-- deconPair_y__l_p12: x, y = [(1, 2)] \n y
def case_deconPair_y__l_p12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.listLiteral [(.capture [.num 1, .num 2])])]), privateProp "x" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) [.resolve "$deconstruct$0"])]), privateProp "y" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) [.resolve "$deconstruct$0"])])] [.resolve "y"])
#guard obs case_deconPair_y__l_p12 == "err arity"

-- deconPair_y__p_l12: x, y = ([1, 2], 3) \n y
def case_deconPair_y__p_l12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [(.listLiteral [.num 1, .num 2]), .num 3])]), privateProp "x" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) [.resolve "$deconstruct$0"])]), privateProp "y" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) [.resolve "$deconstruct$0"])])] [.resolve "y"])
#guard obs case_deconPair_y__p_l12 == "ok raw=3 n=1"

-- deconPair_y__pl1: x, y = ([1]) \n y
def case_deconPair_y__pl1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.listLiteral [.num 1])]), privateProp "x" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) [.resolve "$deconstruct$0"])]), privateProp "y" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) [.resolve "$deconstruct$0"])])] [.resolve "y"])
#guard obs case_deconPair_y__pl1 == "err arity"

-- deconPairSpread_x__e: x, y = (()*) \n x
def case_deconPairSpread_x__e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [(.sequenceSpread (.emptySequence 0))])]), privateProp "x" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) [.resolve "$deconstruct$0"])]), privateProp "y" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) [.resolve "$deconstruct$0"])])] [.resolve "x"])
#guard obs case_deconPairSpread_x__e == "err arity"

-- deconPairSpread_x__n0: x, y = (0*) \n x
def case_deconPairSpread_x__n0 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [(.sequenceSpread (.num 0))])]), privateProp "x" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) [.resolve "$deconstruct$0"])]), privateProp "y" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) [.resolve "$deconstruct$0"])])] [.resolve "x"])
#guard obs case_deconPairSpread_x__n0 == "err arity"

-- deconPairSpread_x__n1: x, y = (1*) \n x
def case_deconPairSpread_x__n1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [(.sequenceSpread (.num 1))])]), privateProp "x" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) [.resolve "$deconstruct$0"])]), privateProp "y" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) [.resolve "$deconstruct$0"])])] [.resolve "x"])
#guard obs case_deconPairSpread_x__n1 == "err arity"

-- deconPairSpread_x__bt: x, y = (true*) \n x
def case_deconPairSpread_x__bt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [(.sequenceSpread (.boolLiteral true))])]), privateProp "x" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) [.resolve "$deconstruct$0"])]), privateProp "y" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) [.resolve "$deconstruct$0"])])] [.resolve "x"])
#guard obs case_deconPairSpread_x__bt == "err arity"

-- deconPairSpread_x__bf: x, y = (false*) \n x
def case_deconPairSpread_x__bf : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [(.sequenceSpread (.boolLiteral false))])]), privateProp "x" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) [.resolve "$deconstruct$0"])]), privateProp "y" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) [.resolve "$deconstruct$0"])])] [.resolve "x"])
#guard obs case_deconPairSpread_x__bf == "err arity"

-- deconPairSpread_x__pbt: x, y = ((true)*) \n x
def case_deconPairSpread_x__pbt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [(.sequenceSpread (.boolLiteral true))])]), privateProp "x" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) [.resolve "$deconstruct$0"])]), privateProp "y" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) [.resolve "$deconstruct$0"])])] [.resolve "x"])
#guard obs case_deconPairSpread_x__pbt == "err arity"

-- deconPairSpread_x__pbt_e: x, y = ((true, ())*) \n x
def case_deconPairSpread_x__pbt_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [(.sequenceSpread (.capture [.boolLiteral true, (.emptySequence 0)]))])]), privateProp "x" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) [.resolve "$deconstruct$0"])]), privateProp "y" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) [.resolve "$deconstruct$0"])])] [.resolve "x"])
#guard obs case_deconPairSpread_x__pbt_e == "ok raw=true n=1"

-- deconPairSpread_x__pbt_1: x, y = ((true, 1)*) \n x
def case_deconPairSpread_x__pbt_1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [(.sequenceSpread (.capture [.boolLiteral true, .num 1]))])]), privateProp "x" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) [.resolve "$deconstruct$0"])]), privateProp "y" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) [.resolve "$deconstruct$0"])])] [.resolve "x"])
#guard obs case_deconPairSpread_x__pbt_1 == "ok raw=true n=1"

-- deconPairSpread_x__lbt: x, y = ([true]*) \n x
def case_deconPairSpread_x__lbt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [(.sequenceSpread (.listLiteral [.boolLiteral true]))])]), privateProp "x" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) [.resolve "$deconstruct$0"])]), privateProp "y" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) [.resolve "$deconstruct$0"])])] [.resolve "x"])
#guard obs case_deconPairSpread_x__lbt == "err arity"

-- deconPairSpread_x__lbt_bf: x, y = ([true, false]*) \n x
def case_deconPairSpread_x__lbt_bf : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [(.sequenceSpread (.listLiteral [.boolLiteral true, .boolLiteral false]))])]), privateProp "x" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) [.resolve "$deconstruct$0"])]), privateProp "y" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) [.resolve "$deconstruct$0"])])] [.resolve "x"])
#guard obs case_deconPairSpread_x__lbt_bf == "ok raw=true n=1"

-- deconPairSpread_x__lpbt_1: x, y = ([(true, 1)]*) \n x
def case_deconPairSpread_x__lpbt_1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [(.sequenceSpread (.listLiteral [(.capture [.boolLiteral true, .num 1])]))])]), privateProp "x" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) [.resolve "$deconstruct$0"])]), privateProp "y" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) [.resolve "$deconstruct$0"])])] [.resolve "x"])
#guard obs case_deconPairSpread_x__lpbt_1 == "ok raw=true n=1"

-- deconPairSpread_x__p1: x, y = ((1)*) \n x
def case_deconPairSpread_x__p1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [(.sequenceSpread (.num 1))])]), privateProp "x" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) [.resolve "$deconstruct$0"])]), privateProp "y" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) [.resolve "$deconstruct$0"])])] [.resolve "x"])
#guard obs case_deconPairSpread_x__p1 == "err arity"

-- deconPairSpread_x__p12: x, y = ((1, 2)*) \n x
def case_deconPairSpread_x__p12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [(.sequenceSpread (.capture [.num 1, .num 2]))])]), privateProp "x" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) [.resolve "$deconstruct$0"])]), privateProp "y" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) [.resolve "$deconstruct$0"])])] [.resolve "x"])
#guard obs case_deconPairSpread_x__p12 == "ok raw=1 n=1"

-- deconPairSpread_x__p123: x, y = ((1, 2, 3)*) \n x
def case_deconPairSpread_x__p123 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [(.sequenceSpread (.capture [.num 1, .num 2, .num 3]))])]), privateProp "x" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) [.resolve "$deconstruct$0"])]), privateProp "y" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) [.resolve "$deconstruct$0"])])] [.resolve "x"])
#guard obs case_deconPairSpread_x__p123 == "err arity"

-- deconPairSpread_x__pee: x, y = (((), ())*) \n x
def case_deconPairSpread_x__pee : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [(.sequenceSpread (.capture [(.emptySequence 0), (.emptySequence 0)]))])]), privateProp "x" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) [.resolve "$deconstruct$0"])]), privateProp "y" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) [.resolve "$deconstruct$0"])])] [.resolve "x"])
#guard obs case_deconPairSpread_x__pee == "ok raw=S[] n=1"

-- deconPairSpread_x__pe1: x, y = (((), 1)*) \n x
def case_deconPairSpread_x__pe1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [(.sequenceSpread (.capture [(.emptySequence 0), .num 1]))])]), privateProp "x" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) [.resolve "$deconstruct$0"])]), privateProp "y" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) [.resolve "$deconstruct$0"])])] [.resolve "x"])
#guard obs case_deconPairSpread_x__pe1 == "ok raw=S[] n=1"

-- deconPairSpread_x__p1e: x, y = ((1, ())*) \n x
def case_deconPairSpread_x__p1e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [(.sequenceSpread (.capture [.num 1, (.emptySequence 0)]))])]), privateProp "x" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) [.resolve "$deconstruct$0"])]), privateProp "y" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) [.resolve "$deconstruct$0"])])] [.resolve "x"])
#guard obs case_deconPairSpread_x__p1e == "ok raw=1 n=1"

-- deconPairSpread_x__p12_3: x, y = (((1, 2), 3)*) \n x
def case_deconPairSpread_x__p12_3 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [(.sequenceSpread (.capture [(.capture [.num 1, .num 2]), .num 3]))])]), privateProp "x" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) [.resolve "$deconstruct$0"])]), privateProp "y" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) [.resolve "$deconstruct$0"])])] [.resolve "x"])
#guard obs case_deconPairSpread_x__p12_3 == "ok raw=S[1, 2] n=1"

-- deconPairSpread_x__p12_34: x, y = (((1, 2), (3, 4))*) \n x
def case_deconPairSpread_x__p12_34 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [(.sequenceSpread (.capture [(.capture [.num 1, .num 2]), (.capture [.num 3, .num 4])]))])]), privateProp "x" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) [.resolve "$deconstruct$0"])]), privateProp "y" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) [.resolve "$deconstruct$0"])])] [.resolve "x"])
#guard obs case_deconPairSpread_x__p12_34 == "ok raw=S[1, 2] n=1"

-- deconPairSpread_x__pe_12: x, y = (((), (1, 2))*) \n x
def case_deconPairSpread_x__pe_12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [(.sequenceSpread (.capture [(.emptySequence 0), (.capture [.num 1, .num 2])]))])]), privateProp "x" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) [.resolve "$deconstruct$0"])]), privateProp "y" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) [.resolve "$deconstruct$0"])])] [.resolve "x"])
#guard obs case_deconPairSpread_x__pe_12 == "ok raw=S[] n=1"

-- deconPairSpread_x__ppe1_2: x, y = ((((), 1), 2)*) \n x
def case_deconPairSpread_x__ppe1_2 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [(.sequenceSpread (.capture [(.capture [(.emptySequence 0), .num 1]), .num 2]))])]), privateProp "x" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) [.resolve "$deconstruct$0"])]), privateProp "y" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) [.resolve "$deconstruct$0"])])] [.resolve "x"])
#guard obs case_deconPairSpread_x__ppe1_2 == "ok raw=S[S[], 1] n=1"

-- deconPairSpread_x__p12_e: x, y = (((1, 2), ())*) \n x
def case_deconPairSpread_x__p12_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [(.sequenceSpread (.capture [(.capture [.num 1, .num 2]), (.emptySequence 0)]))])]), privateProp "x" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) [.resolve "$deconstruct$0"])]), privateProp "y" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) [.resolve "$deconstruct$0"])])] [.resolve "x"])
#guard obs case_deconPairSpread_x__p12_e == "ok raw=S[1, 2] n=1"

-- deconPairSpread_x__ppe: x, y = ((())*) \n x
def case_deconPairSpread_x__ppe : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [(.sequenceSpread (.emptySequence 0))])]), privateProp "x" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) [.resolve "$deconstruct$0"])]), privateProp "y" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) [.resolve "$deconstruct$0"])])] [.resolve "x"])
#guard obs case_deconPairSpread_x__ppe == "err arity"

-- deconPairSpread_x__pp1: x, y = (((1))*) \n x
def case_deconPairSpread_x__pp1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [(.sequenceSpread (.num 1))])]), privateProp "x" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) [.resolve "$deconstruct$0"])]), privateProp "y" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) [.resolve "$deconstruct$0"])])] [.resolve "x"])
#guard obs case_deconPairSpread_x__pp1 == "err arity"

-- deconPairSpread_x__ppp12: x, y = ((((1, 2)))*) \n x
def case_deconPairSpread_x__ppp12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [(.sequenceSpread (.capture [.num 1, .num 2]))])]), privateProp "x" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) [.resolve "$deconstruct$0"])]), privateProp "y" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) [.resolve "$deconstruct$0"])])] [.resolve "x"])
#guard obs case_deconPairSpread_x__ppp12 == "ok raw=1 n=1"

-- deconPairSpread_x__le: x, y = ([]*) \n x
def case_deconPairSpread_x__le : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [(.sequenceSpread (.listLiteral []))])]), privateProp "x" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) [.resolve "$deconstruct$0"])]), privateProp "y" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) [.resolve "$deconstruct$0"])])] [.resolve "x"])
#guard obs case_deconPairSpread_x__le == "err arity"

-- deconPairSpread_x__l7: x, y = ([7]*) \n x
def case_deconPairSpread_x__l7 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [(.sequenceSpread (.listLiteral [.num 7]))])]), privateProp "x" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) [.resolve "$deconstruct$0"])]), privateProp "y" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) [.resolve "$deconstruct$0"])])] [.resolve "x"])
#guard obs case_deconPairSpread_x__l7 == "err arity"

-- deconPairSpread_x__l12: x, y = ([1, 2]*) \n x
def case_deconPairSpread_x__l12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [(.sequenceSpread (.listLiteral [.num 1, .num 2]))])]), privateProp "x" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) [.resolve "$deconstruct$0"])]), privateProp "y" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) [.resolve "$deconstruct$0"])])] [.resolve "x"])
#guard obs case_deconPairSpread_x__l12 == "ok raw=1 n=1"

-- deconPairSpread_x__l12_3: x, y = ([[1, 2], 3]*) \n x
def case_deconPairSpread_x__l12_3 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [(.sequenceSpread (.listLiteral [(.listLiteral [.num 1, .num 2]), .num 3]))])]), privateProp "x" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) [.resolve "$deconstruct$0"])]), privateProp "y" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) [.resolve "$deconstruct$0"])])] [.resolve "x"])
#guard obs case_deconPairSpread_x__l12_3 == "ok raw=L[1, 2] n=1"

-- deconPairSpread_x__lle: x, y = ([[]]*) \n x
def case_deconPairSpread_x__lle : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [(.sequenceSpread (.listLiteral [(.listLiteral [])]))])]), privateProp "x" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) [.resolve "$deconstruct$0"])]), privateProp "y" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) [.resolve "$deconstruct$0"])])] [.resolve "x"])
#guard obs case_deconPairSpread_x__lle == "err arity"

-- deconPairSpread_x__l_e: x, y = ([()]*) \n x
def case_deconPairSpread_x__l_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [(.sequenceSpread (.listLiteral [(.emptySequence 0)]))])]), privateProp "x" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) [.resolve "$deconstruct$0"])]), privateProp "y" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) [.resolve "$deconstruct$0"])])] [.resolve "x"])
#guard obs case_deconPairSpread_x__l_e == "err arity"

-- deconPairSpread_x__l_p12: x, y = ([(1, 2)]*) \n x
def case_deconPairSpread_x__l_p12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [(.sequenceSpread (.listLiteral [(.capture [.num 1, .num 2])]))])]), privateProp "x" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) [.resolve "$deconstruct$0"])]), privateProp "y" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) [.resolve "$deconstruct$0"])])] [.resolve "x"])
#guard obs case_deconPairSpread_x__l_p12 == "ok raw=1 n=1"

-- deconPairSpread_x__p_l12: x, y = (([1, 2], 3)*) \n x
def case_deconPairSpread_x__p_l12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [(.sequenceSpread (.capture [(.listLiteral [.num 1, .num 2]), .num 3]))])]), privateProp "x" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) [.resolve "$deconstruct$0"])]), privateProp "y" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) [.resolve "$deconstruct$0"])])] [.resolve "x"])
#guard obs case_deconPairSpread_x__p_l12 == "ok raw=L[1, 2] n=1"

-- deconPairSpread_x__pl1: x, y = (([1])*) \n x
def case_deconPairSpread_x__pl1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [(.sequenceSpread (.listLiteral [.num 1]))])]), privateProp "x" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "x"])) [.resolve "$deconstruct$0"])]), privateProp "y" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [.param "y"])) [.resolve "$deconstruct$0"])])] [.resolve "x"])
#guard obs case_deconPairSpread_x__pl1 == "err arity"

-- deconCollect_t__e: h, *t = () \n t
def case_deconCollect_t__e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.emptySequence 0)]), privateProp "h" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "h"])) [.resolve "$deconstruct$0"])]), privateProp "t" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "t"])) [.resolve "$deconstruct$0"])])] [.resolve "t"])
#guard obs case_deconCollect_t__e == "err arity"

-- deconCollect_t__n0: h, *t = 0 \n t
def case_deconCollect_t__n0 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [.num 0]), privateProp "h" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "h"])) [.resolve "$deconstruct$0"])]), privateProp "t" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "t"])) [.resolve "$deconstruct$0"])])] [.resolve "t"])
#guard obs case_deconCollect_t__n0 == "ok raw=L[] n=1"

-- deconCollect_t__n1: h, *t = 1 \n t
def case_deconCollect_t__n1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [.num 1]), privateProp "h" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "h"])) [.resolve "$deconstruct$0"])]), privateProp "t" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "t"])) [.resolve "$deconstruct$0"])])] [.resolve "t"])
#guard obs case_deconCollect_t__n1 == "ok raw=L[] n=1"

-- deconCollect_t__bt: h, *t = true \n t
def case_deconCollect_t__bt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [.boolLiteral true]), privateProp "h" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "h"])) [.resolve "$deconstruct$0"])]), privateProp "t" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "t"])) [.resolve "$deconstruct$0"])])] [.resolve "t"])
#guard obs case_deconCollect_t__bt == "ok raw=L[] n=1"

-- deconCollect_t__bf: h, *t = false \n t
def case_deconCollect_t__bf : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [.boolLiteral false]), privateProp "h" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "h"])) [.resolve "$deconstruct$0"])]), privateProp "t" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "t"])) [.resolve "$deconstruct$0"])])] [.resolve "t"])
#guard obs case_deconCollect_t__bf == "ok raw=L[] n=1"

-- deconCollect_t__pbt: h, *t = (true) \n t
def case_deconCollect_t__pbt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [.boolLiteral true]), privateProp "h" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "h"])) [.resolve "$deconstruct$0"])]), privateProp "t" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "t"])) [.resolve "$deconstruct$0"])])] [.resolve "t"])
#guard obs case_deconCollect_t__pbt == "ok raw=L[] n=1"

-- deconCollect_t__pbt_e: h, *t = (true, ()) \n t
def case_deconCollect_t__pbt_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [.boolLiteral true, (.emptySequence 0)])]), privateProp "h" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "h"])) [.resolve "$deconstruct$0"])]), privateProp "t" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "t"])) [.resolve "$deconstruct$0"])])] [.resolve "t"])
#guard obs case_deconCollect_t__pbt_e == "ok raw=L[S[]] n=1"

-- deconCollect_t__pbt_1: h, *t = (true, 1) \n t
def case_deconCollect_t__pbt_1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [.boolLiteral true, .num 1])]), privateProp "h" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "h"])) [.resolve "$deconstruct$0"])]), privateProp "t" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "t"])) [.resolve "$deconstruct$0"])])] [.resolve "t"])
#guard obs case_deconCollect_t__pbt_1 == "ok raw=L[1] n=1"

-- deconCollect_t__lbt: h, *t = [true] \n t
def case_deconCollect_t__lbt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.listLiteral [.boolLiteral true])]), privateProp "h" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "h"])) [.resolve "$deconstruct$0"])]), privateProp "t" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "t"])) [.resolve "$deconstruct$0"])])] [.resolve "t"])
#guard obs case_deconCollect_t__lbt == "ok raw=L[] n=1"

-- deconCollect_t__lbt_bf: h, *t = [true, false] \n t
def case_deconCollect_t__lbt_bf : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.listLiteral [.boolLiteral true, .boolLiteral false])]), privateProp "h" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "h"])) [.resolve "$deconstruct$0"])]), privateProp "t" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "t"])) [.resolve "$deconstruct$0"])])] [.resolve "t"])
#guard obs case_deconCollect_t__lbt_bf == "ok raw=L[false] n=1"

-- deconCollect_t__lpbt_1: h, *t = [(true, 1)] \n t
def case_deconCollect_t__lpbt_1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.listLiteral [(.capture [.boolLiteral true, .num 1])])]), privateProp "h" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "h"])) [.resolve "$deconstruct$0"])]), privateProp "t" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "t"])) [.resolve "$deconstruct$0"])])] [.resolve "t"])
#guard obs case_deconCollect_t__lpbt_1 == "ok raw=L[] n=1"

-- deconCollect_t__p1: h, *t = (1) \n t
def case_deconCollect_t__p1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [.num 1]), privateProp "h" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "h"])) [.resolve "$deconstruct$0"])]), privateProp "t" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "t"])) [.resolve "$deconstruct$0"])])] [.resolve "t"])
#guard obs case_deconCollect_t__p1 == "ok raw=L[] n=1"

-- deconCollect_t__p12: h, *t = (1, 2) \n t
def case_deconCollect_t__p12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [.num 1, .num 2])]), privateProp "h" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "h"])) [.resolve "$deconstruct$0"])]), privateProp "t" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "t"])) [.resolve "$deconstruct$0"])])] [.resolve "t"])
#guard obs case_deconCollect_t__p12 == "ok raw=L[2] n=1"

-- deconCollect_t__p123: h, *t = (1, 2, 3) \n t
def case_deconCollect_t__p123 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [.num 1, .num 2, .num 3])]), privateProp "h" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "h"])) [.resolve "$deconstruct$0"])]), privateProp "t" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "t"])) [.resolve "$deconstruct$0"])])] [.resolve "t"])
#guard obs case_deconCollect_t__p123 == "ok raw=L[2, 3] n=1"

-- deconCollect_t__pee: h, *t = ((), ()) \n t
def case_deconCollect_t__pee : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [(.emptySequence 0), (.emptySequence 0)])]), privateProp "h" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "h"])) [.resolve "$deconstruct$0"])]), privateProp "t" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "t"])) [.resolve "$deconstruct$0"])])] [.resolve "t"])
#guard obs case_deconCollect_t__pee == "ok raw=L[S[]] n=1"

-- deconCollect_t__pe1: h, *t = ((), 1) \n t
def case_deconCollect_t__pe1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [(.emptySequence 0), .num 1])]), privateProp "h" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "h"])) [.resolve "$deconstruct$0"])]), privateProp "t" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "t"])) [.resolve "$deconstruct$0"])])] [.resolve "t"])
#guard obs case_deconCollect_t__pe1 == "ok raw=L[1] n=1"

-- deconCollect_t__p1e: h, *t = (1, ()) \n t
def case_deconCollect_t__p1e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [.num 1, (.emptySequence 0)])]), privateProp "h" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "h"])) [.resolve "$deconstruct$0"])]), privateProp "t" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "t"])) [.resolve "$deconstruct$0"])])] [.resolve "t"])
#guard obs case_deconCollect_t__p1e == "ok raw=L[S[]] n=1"

-- deconCollect_t__p12_3: h, *t = ((1, 2), 3) \n t
def case_deconCollect_t__p12_3 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [(.capture [.num 1, .num 2]), .num 3])]), privateProp "h" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "h"])) [.resolve "$deconstruct$0"])]), privateProp "t" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "t"])) [.resolve "$deconstruct$0"])])] [.resolve "t"])
#guard obs case_deconCollect_t__p12_3 == "ok raw=L[3] n=1"

-- deconCollect_t__p12_34: h, *t = ((1, 2), (3, 4)) \n t
def case_deconCollect_t__p12_34 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [(.capture [.num 1, .num 2]), (.capture [.num 3, .num 4])])]), privateProp "h" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "h"])) [.resolve "$deconstruct$0"])]), privateProp "t" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "t"])) [.resolve "$deconstruct$0"])])] [.resolve "t"])
#guard obs case_deconCollect_t__p12_34 == "ok raw=L[S[3, 4]] n=1"

-- deconCollect_t__pe_12: h, *t = ((), (1, 2)) \n t
def case_deconCollect_t__pe_12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [(.emptySequence 0), (.capture [.num 1, .num 2])])]), privateProp "h" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "h"])) [.resolve "$deconstruct$0"])]), privateProp "t" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "t"])) [.resolve "$deconstruct$0"])])] [.resolve "t"])
#guard obs case_deconCollect_t__pe_12 == "ok raw=L[S[1, 2]] n=1"

-- deconCollect_t__ppe1_2: h, *t = (((), 1), 2) \n t
def case_deconCollect_t__ppe1_2 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [(.capture [(.emptySequence 0), .num 1]), .num 2])]), privateProp "h" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "h"])) [.resolve "$deconstruct$0"])]), privateProp "t" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "t"])) [.resolve "$deconstruct$0"])])] [.resolve "t"])
#guard obs case_deconCollect_t__ppe1_2 == "ok raw=L[2] n=1"

-- deconCollect_t__p12_e: h, *t = ((1, 2), ()) \n t
def case_deconCollect_t__p12_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [(.capture [.num 1, .num 2]), (.emptySequence 0)])]), privateProp "h" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "h"])) [.resolve "$deconstruct$0"])]), privateProp "t" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "t"])) [.resolve "$deconstruct$0"])])] [.resolve "t"])
#guard obs case_deconCollect_t__p12_e == "ok raw=L[S[]] n=1"

-- deconCollect_t__ppe: h, *t = (()) \n t
def case_deconCollect_t__ppe : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.emptySequence 0)]), privateProp "h" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "h"])) [.resolve "$deconstruct$0"])]), privateProp "t" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "t"])) [.resolve "$deconstruct$0"])])] [.resolve "t"])
#guard obs case_deconCollect_t__ppe == "err arity"

-- deconCollect_t__pp1: h, *t = ((1)) \n t
def case_deconCollect_t__pp1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [.num 1]), privateProp "h" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "h"])) [.resolve "$deconstruct$0"])]), privateProp "t" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "t"])) [.resolve "$deconstruct$0"])])] [.resolve "t"])
#guard obs case_deconCollect_t__pp1 == "ok raw=L[] n=1"

-- deconCollect_t__ppp12: h, *t = (((1, 2))) \n t
def case_deconCollect_t__ppp12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [.num 1, .num 2])]), privateProp "h" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "h"])) [.resolve "$deconstruct$0"])]), privateProp "t" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "t"])) [.resolve "$deconstruct$0"])])] [.resolve "t"])
#guard obs case_deconCollect_t__ppp12 == "ok raw=L[2] n=1"

-- deconCollect_t__le: h, *t = [] \n t
def case_deconCollect_t__le : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.listLiteral [])]), privateProp "h" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "h"])) [.resolve "$deconstruct$0"])]), privateProp "t" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "t"])) [.resolve "$deconstruct$0"])])] [.resolve "t"])
#guard obs case_deconCollect_t__le == "err arity"

-- deconCollect_t__l7: h, *t = [7] \n t
def case_deconCollect_t__l7 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.listLiteral [.num 7])]), privateProp "h" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "h"])) [.resolve "$deconstruct$0"])]), privateProp "t" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "t"])) [.resolve "$deconstruct$0"])])] [.resolve "t"])
#guard obs case_deconCollect_t__l7 == "ok raw=L[] n=1"

-- deconCollect_t__l12: h, *t = [1, 2] \n t
def case_deconCollect_t__l12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.listLiteral [.num 1, .num 2])]), privateProp "h" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "h"])) [.resolve "$deconstruct$0"])]), privateProp "t" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "t"])) [.resolve "$deconstruct$0"])])] [.resolve "t"])
#guard obs case_deconCollect_t__l12 == "ok raw=L[2] n=1"

-- deconCollect_t__l12_3: h, *t = [[1, 2], 3] \n t
def case_deconCollect_t__l12_3 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.listLiteral [(.listLiteral [.num 1, .num 2]), .num 3])]), privateProp "h" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "h"])) [.resolve "$deconstruct$0"])]), privateProp "t" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "t"])) [.resolve "$deconstruct$0"])])] [.resolve "t"])
#guard obs case_deconCollect_t__l12_3 == "ok raw=L[3] n=1"

-- deconCollect_t__lle: h, *t = [[]] \n t
def case_deconCollect_t__lle : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.listLiteral [(.listLiteral [])])]), privateProp "h" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "h"])) [.resolve "$deconstruct$0"])]), privateProp "t" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "t"])) [.resolve "$deconstruct$0"])])] [.resolve "t"])
#guard obs case_deconCollect_t__lle == "ok raw=L[] n=1"

-- deconCollect_t__l_e: h, *t = [()] \n t
def case_deconCollect_t__l_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.listLiteral [(.emptySequence 0)])]), privateProp "h" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "h"])) [.resolve "$deconstruct$0"])]), privateProp "t" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "t"])) [.resolve "$deconstruct$0"])])] [.resolve "t"])
#guard obs case_deconCollect_t__l_e == "ok raw=L[] n=1"

-- deconCollect_t__l_p12: h, *t = [(1, 2)] \n t
def case_deconCollect_t__l_p12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.listLiteral [(.capture [.num 1, .num 2])])]), privateProp "h" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "h"])) [.resolve "$deconstruct$0"])]), privateProp "t" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "t"])) [.resolve "$deconstruct$0"])])] [.resolve "t"])
#guard obs case_deconCollect_t__l_p12 == "ok raw=L[] n=1"

-- deconCollect_t__p_l12: h, *t = ([1, 2], 3) \n t
def case_deconCollect_t__p_l12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [(.listLiteral [.num 1, .num 2]), .num 3])]), privateProp "h" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "h"])) [.resolve "$deconstruct$0"])]), privateProp "t" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "t"])) [.resolve "$deconstruct$0"])])] [.resolve "t"])
#guard obs case_deconCollect_t__p_l12 == "ok raw=L[3] n=1"

-- deconCollect_t__pl1: h, *t = ([1]) \n t
def case_deconCollect_t__pl1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.listLiteral [.num 1])]), privateProp "h" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "h"])) [.resolve "$deconstruct$0"])]), privateProp "t" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "t"])) [.resolve "$deconstruct$0"])])] [.resolve "t"])
#guard obs case_deconCollect_t__pl1 == "ok raw=L[] n=1"

-- deconCollectSpread_t__e: h, *t = (()*) \n t
def case_deconCollectSpread_t__e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [(.sequenceSpread (.emptySequence 0))])]), privateProp "h" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "h"])) [.resolve "$deconstruct$0"])]), privateProp "t" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "t"])) [.resolve "$deconstruct$0"])])] [.resolve "t"])
#guard obs case_deconCollectSpread_t__e == "err arity"

-- deconCollectSpread_t__n0: h, *t = (0*) \n t
def case_deconCollectSpread_t__n0 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [(.sequenceSpread (.num 0))])]), privateProp "h" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "h"])) [.resolve "$deconstruct$0"])]), privateProp "t" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "t"])) [.resolve "$deconstruct$0"])])] [.resolve "t"])
#guard obs case_deconCollectSpread_t__n0 == "ok raw=L[] n=1"

-- deconCollectSpread_t__n1: h, *t = (1*) \n t
def case_deconCollectSpread_t__n1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [(.sequenceSpread (.num 1))])]), privateProp "h" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "h"])) [.resolve "$deconstruct$0"])]), privateProp "t" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "t"])) [.resolve "$deconstruct$0"])])] [.resolve "t"])
#guard obs case_deconCollectSpread_t__n1 == "ok raw=L[] n=1"

-- deconCollectSpread_t__bt: h, *t = (true*) \n t
def case_deconCollectSpread_t__bt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [(.sequenceSpread (.boolLiteral true))])]), privateProp "h" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "h"])) [.resolve "$deconstruct$0"])]), privateProp "t" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "t"])) [.resolve "$deconstruct$0"])])] [.resolve "t"])
#guard obs case_deconCollectSpread_t__bt == "ok raw=L[] n=1"

-- deconCollectSpread_t__bf: h, *t = (false*) \n t
def case_deconCollectSpread_t__bf : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [(.sequenceSpread (.boolLiteral false))])]), privateProp "h" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "h"])) [.resolve "$deconstruct$0"])]), privateProp "t" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "t"])) [.resolve "$deconstruct$0"])])] [.resolve "t"])
#guard obs case_deconCollectSpread_t__bf == "ok raw=L[] n=1"

-- deconCollectSpread_t__pbt: h, *t = ((true)*) \n t
def case_deconCollectSpread_t__pbt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [(.sequenceSpread (.boolLiteral true))])]), privateProp "h" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "h"])) [.resolve "$deconstruct$0"])]), privateProp "t" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "t"])) [.resolve "$deconstruct$0"])])] [.resolve "t"])
#guard obs case_deconCollectSpread_t__pbt == "ok raw=L[] n=1"

-- deconCollectSpread_t__pbt_e: h, *t = ((true, ())*) \n t
def case_deconCollectSpread_t__pbt_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [(.sequenceSpread (.capture [.boolLiteral true, (.emptySequence 0)]))])]), privateProp "h" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "h"])) [.resolve "$deconstruct$0"])]), privateProp "t" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "t"])) [.resolve "$deconstruct$0"])])] [.resolve "t"])
#guard obs case_deconCollectSpread_t__pbt_e == "ok raw=L[S[]] n=1"

-- deconCollectSpread_t__pbt_1: h, *t = ((true, 1)*) \n t
def case_deconCollectSpread_t__pbt_1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [(.sequenceSpread (.capture [.boolLiteral true, .num 1]))])]), privateProp "h" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "h"])) [.resolve "$deconstruct$0"])]), privateProp "t" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "t"])) [.resolve "$deconstruct$0"])])] [.resolve "t"])
#guard obs case_deconCollectSpread_t__pbt_1 == "ok raw=L[1] n=1"

-- deconCollectSpread_t__lbt: h, *t = ([true]*) \n t
def case_deconCollectSpread_t__lbt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [(.sequenceSpread (.listLiteral [.boolLiteral true]))])]), privateProp "h" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "h"])) [.resolve "$deconstruct$0"])]), privateProp "t" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "t"])) [.resolve "$deconstruct$0"])])] [.resolve "t"])
#guard obs case_deconCollectSpread_t__lbt == "ok raw=L[] n=1"

-- deconCollectSpread_t__lbt_bf: h, *t = ([true, false]*) \n t
def case_deconCollectSpread_t__lbt_bf : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [(.sequenceSpread (.listLiteral [.boolLiteral true, .boolLiteral false]))])]), privateProp "h" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "h"])) [.resolve "$deconstruct$0"])]), privateProp "t" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "t"])) [.resolve "$deconstruct$0"])])] [.resolve "t"])
#guard obs case_deconCollectSpread_t__lbt_bf == "ok raw=L[false] n=1"

-- deconCollectSpread_t__lpbt_1: h, *t = ([(true, 1)]*) \n t
def case_deconCollectSpread_t__lpbt_1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [(.sequenceSpread (.listLiteral [(.capture [.boolLiteral true, .num 1])]))])]), privateProp "h" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "h"])) [.resolve "$deconstruct$0"])]), privateProp "t" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "t"])) [.resolve "$deconstruct$0"])])] [.resolve "t"])
#guard obs case_deconCollectSpread_t__lpbt_1 == "ok raw=L[1] n=1"

-- deconCollectSpread_t__p1: h, *t = ((1)*) \n t
def case_deconCollectSpread_t__p1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [(.sequenceSpread (.num 1))])]), privateProp "h" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "h"])) [.resolve "$deconstruct$0"])]), privateProp "t" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "t"])) [.resolve "$deconstruct$0"])])] [.resolve "t"])
#guard obs case_deconCollectSpread_t__p1 == "ok raw=L[] n=1"

-- deconCollectSpread_t__p12: h, *t = ((1, 2)*) \n t
def case_deconCollectSpread_t__p12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [(.sequenceSpread (.capture [.num 1, .num 2]))])]), privateProp "h" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "h"])) [.resolve "$deconstruct$0"])]), privateProp "t" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "t"])) [.resolve "$deconstruct$0"])])] [.resolve "t"])
#guard obs case_deconCollectSpread_t__p12 == "ok raw=L[2] n=1"

-- deconCollectSpread_t__p123: h, *t = ((1, 2, 3)*) \n t
def case_deconCollectSpread_t__p123 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [(.sequenceSpread (.capture [.num 1, .num 2, .num 3]))])]), privateProp "h" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "h"])) [.resolve "$deconstruct$0"])]), privateProp "t" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "t"])) [.resolve "$deconstruct$0"])])] [.resolve "t"])
#guard obs case_deconCollectSpread_t__p123 == "ok raw=L[2, 3] n=1"

-- deconCollectSpread_t__pee: h, *t = (((), ())*) \n t
def case_deconCollectSpread_t__pee : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [(.sequenceSpread (.capture [(.emptySequence 0), (.emptySequence 0)]))])]), privateProp "h" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "h"])) [.resolve "$deconstruct$0"])]), privateProp "t" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "t"])) [.resolve "$deconstruct$0"])])] [.resolve "t"])
#guard obs case_deconCollectSpread_t__pee == "ok raw=L[S[]] n=1"

-- deconCollectSpread_t__pe1: h, *t = (((), 1)*) \n t
def case_deconCollectSpread_t__pe1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [(.sequenceSpread (.capture [(.emptySequence 0), .num 1]))])]), privateProp "h" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "h"])) [.resolve "$deconstruct$0"])]), privateProp "t" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "t"])) [.resolve "$deconstruct$0"])])] [.resolve "t"])
#guard obs case_deconCollectSpread_t__pe1 == "ok raw=L[1] n=1"

-- deconCollectSpread_t__p1e: h, *t = ((1, ())*) \n t
def case_deconCollectSpread_t__p1e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [(.sequenceSpread (.capture [.num 1, (.emptySequence 0)]))])]), privateProp "h" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "h"])) [.resolve "$deconstruct$0"])]), privateProp "t" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "t"])) [.resolve "$deconstruct$0"])])] [.resolve "t"])
#guard obs case_deconCollectSpread_t__p1e == "ok raw=L[S[]] n=1"

-- deconCollectSpread_t__p12_3: h, *t = (((1, 2), 3)*) \n t
def case_deconCollectSpread_t__p12_3 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [(.sequenceSpread (.capture [(.capture [.num 1, .num 2]), .num 3]))])]), privateProp "h" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "h"])) [.resolve "$deconstruct$0"])]), privateProp "t" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "t"])) [.resolve "$deconstruct$0"])])] [.resolve "t"])
#guard obs case_deconCollectSpread_t__p12_3 == "ok raw=L[3] n=1"

-- deconCollectSpread_t__p12_34: h, *t = (((1, 2), (3, 4))*) \n t
def case_deconCollectSpread_t__p12_34 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [(.sequenceSpread (.capture [(.capture [.num 1, .num 2]), (.capture [.num 3, .num 4])]))])]), privateProp "h" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "h"])) [.resolve "$deconstruct$0"])]), privateProp "t" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "t"])) [.resolve "$deconstruct$0"])])] [.resolve "t"])
#guard obs case_deconCollectSpread_t__p12_34 == "ok raw=L[S[3, 4]] n=1"

-- deconCollectSpread_t__pe_12: h, *t = (((), (1, 2))*) \n t
def case_deconCollectSpread_t__pe_12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [(.sequenceSpread (.capture [(.emptySequence 0), (.capture [.num 1, .num 2])]))])]), privateProp "h" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "h"])) [.resolve "$deconstruct$0"])]), privateProp "t" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "t"])) [.resolve "$deconstruct$0"])])] [.resolve "t"])
#guard obs case_deconCollectSpread_t__pe_12 == "ok raw=L[S[1, 2]] n=1"

-- deconCollectSpread_t__ppe1_2: h, *t = ((((), 1), 2)*) \n t
def case_deconCollectSpread_t__ppe1_2 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [(.sequenceSpread (.capture [(.capture [(.emptySequence 0), .num 1]), .num 2]))])]), privateProp "h" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "h"])) [.resolve "$deconstruct$0"])]), privateProp "t" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "t"])) [.resolve "$deconstruct$0"])])] [.resolve "t"])
#guard obs case_deconCollectSpread_t__ppe1_2 == "ok raw=L[2] n=1"

-- deconCollectSpread_t__p12_e: h, *t = (((1, 2), ())*) \n t
def case_deconCollectSpread_t__p12_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [(.sequenceSpread (.capture [(.capture [.num 1, .num 2]), (.emptySequence 0)]))])]), privateProp "h" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "h"])) [.resolve "$deconstruct$0"])]), privateProp "t" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "t"])) [.resolve "$deconstruct$0"])])] [.resolve "t"])
#guard obs case_deconCollectSpread_t__p12_e == "ok raw=L[S[]] n=1"

-- deconCollectSpread_t__ppe: h, *t = ((())*) \n t
def case_deconCollectSpread_t__ppe : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [(.sequenceSpread (.emptySequence 0))])]), privateProp "h" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "h"])) [.resolve "$deconstruct$0"])]), privateProp "t" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "t"])) [.resolve "$deconstruct$0"])])] [.resolve "t"])
#guard obs case_deconCollectSpread_t__ppe == "err arity"

-- deconCollectSpread_t__pp1: h, *t = (((1))*) \n t
def case_deconCollectSpread_t__pp1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [(.sequenceSpread (.num 1))])]), privateProp "h" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "h"])) [.resolve "$deconstruct$0"])]), privateProp "t" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "t"])) [.resolve "$deconstruct$0"])])] [.resolve "t"])
#guard obs case_deconCollectSpread_t__pp1 == "ok raw=L[] n=1"

-- deconCollectSpread_t__ppp12: h, *t = ((((1, 2)))*) \n t
def case_deconCollectSpread_t__ppp12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [(.sequenceSpread (.capture [.num 1, .num 2]))])]), privateProp "h" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "h"])) [.resolve "$deconstruct$0"])]), privateProp "t" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "t"])) [.resolve "$deconstruct$0"])])] [.resolve "t"])
#guard obs case_deconCollectSpread_t__ppp12 == "ok raw=L[2] n=1"

-- deconCollectSpread_t__le: h, *t = ([]*) \n t
def case_deconCollectSpread_t__le : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [(.sequenceSpread (.listLiteral []))])]), privateProp "h" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "h"])) [.resolve "$deconstruct$0"])]), privateProp "t" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "t"])) [.resolve "$deconstruct$0"])])] [.resolve "t"])
#guard obs case_deconCollectSpread_t__le == "err arity"

-- deconCollectSpread_t__l7: h, *t = ([7]*) \n t
def case_deconCollectSpread_t__l7 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [(.sequenceSpread (.listLiteral [.num 7]))])]), privateProp "h" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "h"])) [.resolve "$deconstruct$0"])]), privateProp "t" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "t"])) [.resolve "$deconstruct$0"])])] [.resolve "t"])
#guard obs case_deconCollectSpread_t__l7 == "ok raw=L[] n=1"

-- deconCollectSpread_t__l12: h, *t = ([1, 2]*) \n t
def case_deconCollectSpread_t__l12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [(.sequenceSpread (.listLiteral [.num 1, .num 2]))])]), privateProp "h" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "h"])) [.resolve "$deconstruct$0"])]), privateProp "t" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "t"])) [.resolve "$deconstruct$0"])])] [.resolve "t"])
#guard obs case_deconCollectSpread_t__l12 == "ok raw=L[2] n=1"

-- deconCollectSpread_t__l12_3: h, *t = ([[1, 2], 3]*) \n t
def case_deconCollectSpread_t__l12_3 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [(.sequenceSpread (.listLiteral [(.listLiteral [.num 1, .num 2]), .num 3]))])]), privateProp "h" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "h"])) [.resolve "$deconstruct$0"])]), privateProp "t" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "t"])) [.resolve "$deconstruct$0"])])] [.resolve "t"])
#guard obs case_deconCollectSpread_t__l12_3 == "ok raw=L[3] n=1"

-- deconCollectSpread_t__lle: h, *t = ([[]]*) \n t
def case_deconCollectSpread_t__lle : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [(.sequenceSpread (.listLiteral [(.listLiteral [])]))])]), privateProp "h" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "h"])) [.resolve "$deconstruct$0"])]), privateProp "t" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "t"])) [.resolve "$deconstruct$0"])])] [.resolve "t"])
#guard obs case_deconCollectSpread_t__lle == "err arity"

-- deconCollectSpread_t__l_e: h, *t = ([()]*) \n t
def case_deconCollectSpread_t__l_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [(.sequenceSpread (.listLiteral [(.emptySequence 0)]))])]), privateProp "h" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "h"])) [.resolve "$deconstruct$0"])]), privateProp "t" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "t"])) [.resolve "$deconstruct$0"])])] [.resolve "t"])
#guard obs case_deconCollectSpread_t__l_e == "err arity"

-- deconCollectSpread_t__l_p12: h, *t = ([(1, 2)]*) \n t
def case_deconCollectSpread_t__l_p12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [(.sequenceSpread (.listLiteral [(.capture [.num 1, .num 2])]))])]), privateProp "h" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "h"])) [.resolve "$deconstruct$0"])]), privateProp "t" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "t"])) [.resolve "$deconstruct$0"])])] [.resolve "t"])
#guard obs case_deconCollectSpread_t__l_p12 == "ok raw=L[2] n=1"

-- deconCollectSpread_t__p_l12: h, *t = (([1, 2], 3)*) \n t
def case_deconCollectSpread_t__p_l12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [(.sequenceSpread (.capture [(.listLiteral [.num 1, .num 2]), .num 3]))])]), privateProp "h" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "h"])) [.resolve "$deconstruct$0"])]), privateProp "t" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "t"])) [.resolve "$deconstruct$0"])])] [.resolve "t"])
#guard obs case_deconCollectSpread_t__p_l12 == "ok raw=L[3] n=1"

-- deconCollectSpread_t__pl1: h, *t = (([1])*) \n t
def case_deconCollectSpread_t__pl1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [(.sequenceSpread (.listLiteral [.num 1]))])]), privateProp "h" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "h"])) [.resolve "$deconstruct$0"])]), privateProp "t" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [.param "t"])) [.resolve "$deconstruct$0"])])] [.resolve "t"])
#guard obs case_deconCollectSpread_t__pl1 == "ok raw=L[] n=1"

-- deconPrefix_p__e: *p, z = () \n p
def case_deconPrefix_p__e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.emptySequence 0)]), privateProp "p" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "p"])) [.resolve "$deconstruct$0"])]), privateProp "z" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "z"])) [.resolve "$deconstruct$0"])])] [.resolve "p"])
#guard obs case_deconPrefix_p__e == "err arity"

-- deconPrefix_p__n0: *p, z = 0 \n p
def case_deconPrefix_p__n0 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [.num 0]), privateProp "p" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "p"])) [.resolve "$deconstruct$0"])]), privateProp "z" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "z"])) [.resolve "$deconstruct$0"])])] [.resolve "p"])
#guard obs case_deconPrefix_p__n0 == "ok raw=L[] n=1"

-- deconPrefix_p__n1: *p, z = 1 \n p
def case_deconPrefix_p__n1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [.num 1]), privateProp "p" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "p"])) [.resolve "$deconstruct$0"])]), privateProp "z" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "z"])) [.resolve "$deconstruct$0"])])] [.resolve "p"])
#guard obs case_deconPrefix_p__n1 == "ok raw=L[] n=1"

-- deconPrefix_p__bt: *p, z = true \n p
def case_deconPrefix_p__bt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [.boolLiteral true]), privateProp "p" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "p"])) [.resolve "$deconstruct$0"])]), privateProp "z" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "z"])) [.resolve "$deconstruct$0"])])] [.resolve "p"])
#guard obs case_deconPrefix_p__bt == "ok raw=L[] n=1"

-- deconPrefix_p__bf: *p, z = false \n p
def case_deconPrefix_p__bf : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [.boolLiteral false]), privateProp "p" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "p"])) [.resolve "$deconstruct$0"])]), privateProp "z" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "z"])) [.resolve "$deconstruct$0"])])] [.resolve "p"])
#guard obs case_deconPrefix_p__bf == "ok raw=L[] n=1"

-- deconPrefix_p__pbt: *p, z = (true) \n p
def case_deconPrefix_p__pbt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [.boolLiteral true]), privateProp "p" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "p"])) [.resolve "$deconstruct$0"])]), privateProp "z" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "z"])) [.resolve "$deconstruct$0"])])] [.resolve "p"])
#guard obs case_deconPrefix_p__pbt == "ok raw=L[] n=1"

-- deconPrefix_p__pbt_e: *p, z = (true, ()) \n p
def case_deconPrefix_p__pbt_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [.boolLiteral true, (.emptySequence 0)])]), privateProp "p" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "p"])) [.resolve "$deconstruct$0"])]), privateProp "z" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "z"])) [.resolve "$deconstruct$0"])])] [.resolve "p"])
#guard obs case_deconPrefix_p__pbt_e == "ok raw=L[true] n=1"

-- deconPrefix_p__pbt_1: *p, z = (true, 1) \n p
def case_deconPrefix_p__pbt_1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [.boolLiteral true, .num 1])]), privateProp "p" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "p"])) [.resolve "$deconstruct$0"])]), privateProp "z" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "z"])) [.resolve "$deconstruct$0"])])] [.resolve "p"])
#guard obs case_deconPrefix_p__pbt_1 == "ok raw=L[true] n=1"

-- deconPrefix_p__lbt: *p, z = [true] \n p
def case_deconPrefix_p__lbt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.listLiteral [.boolLiteral true])]), privateProp "p" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "p"])) [.resolve "$deconstruct$0"])]), privateProp "z" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "z"])) [.resolve "$deconstruct$0"])])] [.resolve "p"])
#guard obs case_deconPrefix_p__lbt == "ok raw=L[] n=1"

-- deconPrefix_p__lbt_bf: *p, z = [true, false] \n p
def case_deconPrefix_p__lbt_bf : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.listLiteral [.boolLiteral true, .boolLiteral false])]), privateProp "p" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "p"])) [.resolve "$deconstruct$0"])]), privateProp "z" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "z"])) [.resolve "$deconstruct$0"])])] [.resolve "p"])
#guard obs case_deconPrefix_p__lbt_bf == "ok raw=L[true] n=1"

-- deconPrefix_p__lpbt_1: *p, z = [(true, 1)] \n p
def case_deconPrefix_p__lpbt_1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.listLiteral [(.capture [.boolLiteral true, .num 1])])]), privateProp "p" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "p"])) [.resolve "$deconstruct$0"])]), privateProp "z" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "z"])) [.resolve "$deconstruct$0"])])] [.resolve "p"])
#guard obs case_deconPrefix_p__lpbt_1 == "ok raw=L[] n=1"

-- deconPrefix_p__p1: *p, z = (1) \n p
def case_deconPrefix_p__p1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [.num 1]), privateProp "p" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "p"])) [.resolve "$deconstruct$0"])]), privateProp "z" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "z"])) [.resolve "$deconstruct$0"])])] [.resolve "p"])
#guard obs case_deconPrefix_p__p1 == "ok raw=L[] n=1"

-- deconPrefix_p__p12: *p, z = (1, 2) \n p
def case_deconPrefix_p__p12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [.num 1, .num 2])]), privateProp "p" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "p"])) [.resolve "$deconstruct$0"])]), privateProp "z" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "z"])) [.resolve "$deconstruct$0"])])] [.resolve "p"])
#guard obs case_deconPrefix_p__p12 == "ok raw=L[1] n=1"

-- deconPrefix_p__p123: *p, z = (1, 2, 3) \n p
def case_deconPrefix_p__p123 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [.num 1, .num 2, .num 3])]), privateProp "p" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "p"])) [.resolve "$deconstruct$0"])]), privateProp "z" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "z"])) [.resolve "$deconstruct$0"])])] [.resolve "p"])
#guard obs case_deconPrefix_p__p123 == "ok raw=L[1, 2] n=1"

-- deconPrefix_p__pee: *p, z = ((), ()) \n p
def case_deconPrefix_p__pee : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [(.emptySequence 0), (.emptySequence 0)])]), privateProp "p" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "p"])) [.resolve "$deconstruct$0"])]), privateProp "z" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "z"])) [.resolve "$deconstruct$0"])])] [.resolve "p"])
#guard obs case_deconPrefix_p__pee == "ok raw=L[S[]] n=1"

-- deconPrefix_p__pe1: *p, z = ((), 1) \n p
def case_deconPrefix_p__pe1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [(.emptySequence 0), .num 1])]), privateProp "p" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "p"])) [.resolve "$deconstruct$0"])]), privateProp "z" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "z"])) [.resolve "$deconstruct$0"])])] [.resolve "p"])
#guard obs case_deconPrefix_p__pe1 == "ok raw=L[S[]] n=1"

-- deconPrefix_p__p1e: *p, z = (1, ()) \n p
def case_deconPrefix_p__p1e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [.num 1, (.emptySequence 0)])]), privateProp "p" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "p"])) [.resolve "$deconstruct$0"])]), privateProp "z" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "z"])) [.resolve "$deconstruct$0"])])] [.resolve "p"])
#guard obs case_deconPrefix_p__p1e == "ok raw=L[1] n=1"

-- deconPrefix_p__p12_3: *p, z = ((1, 2), 3) \n p
def case_deconPrefix_p__p12_3 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [(.capture [.num 1, .num 2]), .num 3])]), privateProp "p" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "p"])) [.resolve "$deconstruct$0"])]), privateProp "z" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "z"])) [.resolve "$deconstruct$0"])])] [.resolve "p"])
#guard obs case_deconPrefix_p__p12_3 == "ok raw=L[S[1, 2]] n=1"

-- deconPrefix_p__p12_34: *p, z = ((1, 2), (3, 4)) \n p
def case_deconPrefix_p__p12_34 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [(.capture [.num 1, .num 2]), (.capture [.num 3, .num 4])])]), privateProp "p" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "p"])) [.resolve "$deconstruct$0"])]), privateProp "z" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "z"])) [.resolve "$deconstruct$0"])])] [.resolve "p"])
#guard obs case_deconPrefix_p__p12_34 == "ok raw=L[S[1, 2]] n=1"

-- deconPrefix_p__pe_12: *p, z = ((), (1, 2)) \n p
def case_deconPrefix_p__pe_12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [(.emptySequence 0), (.capture [.num 1, .num 2])])]), privateProp "p" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "p"])) [.resolve "$deconstruct$0"])]), privateProp "z" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "z"])) [.resolve "$deconstruct$0"])])] [.resolve "p"])
#guard obs case_deconPrefix_p__pe_12 == "ok raw=L[S[]] n=1"

-- deconPrefix_p__ppe1_2: *p, z = (((), 1), 2) \n p
def case_deconPrefix_p__ppe1_2 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [(.capture [(.emptySequence 0), .num 1]), .num 2])]), privateProp "p" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "p"])) [.resolve "$deconstruct$0"])]), privateProp "z" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "z"])) [.resolve "$deconstruct$0"])])] [.resolve "p"])
#guard obs case_deconPrefix_p__ppe1_2 == "ok raw=L[S[S[], 1]] n=1"

-- deconPrefix_p__p12_e: *p, z = ((1, 2), ()) \n p
def case_deconPrefix_p__p12_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [(.capture [.num 1, .num 2]), (.emptySequence 0)])]), privateProp "p" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "p"])) [.resolve "$deconstruct$0"])]), privateProp "z" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "z"])) [.resolve "$deconstruct$0"])])] [.resolve "p"])
#guard obs case_deconPrefix_p__p12_e == "ok raw=L[S[1, 2]] n=1"

-- deconPrefix_p__ppe: *p, z = (()) \n p
def case_deconPrefix_p__ppe : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.emptySequence 0)]), privateProp "p" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "p"])) [.resolve "$deconstruct$0"])]), privateProp "z" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "z"])) [.resolve "$deconstruct$0"])])] [.resolve "p"])
#guard obs case_deconPrefix_p__ppe == "err arity"

-- deconPrefix_p__pp1: *p, z = ((1)) \n p
def case_deconPrefix_p__pp1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [.num 1]), privateProp "p" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "p"])) [.resolve "$deconstruct$0"])]), privateProp "z" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "z"])) [.resolve "$deconstruct$0"])])] [.resolve "p"])
#guard obs case_deconPrefix_p__pp1 == "ok raw=L[] n=1"

-- deconPrefix_p__ppp12: *p, z = (((1, 2))) \n p
def case_deconPrefix_p__ppp12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [.num 1, .num 2])]), privateProp "p" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "p"])) [.resolve "$deconstruct$0"])]), privateProp "z" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "z"])) [.resolve "$deconstruct$0"])])] [.resolve "p"])
#guard obs case_deconPrefix_p__ppp12 == "ok raw=L[1] n=1"

-- deconPrefix_p__le: *p, z = [] \n p
def case_deconPrefix_p__le : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.listLiteral [])]), privateProp "p" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "p"])) [.resolve "$deconstruct$0"])]), privateProp "z" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "z"])) [.resolve "$deconstruct$0"])])] [.resolve "p"])
#guard obs case_deconPrefix_p__le == "err arity"

-- deconPrefix_p__l7: *p, z = [7] \n p
def case_deconPrefix_p__l7 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.listLiteral [.num 7])]), privateProp "p" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "p"])) [.resolve "$deconstruct$0"])]), privateProp "z" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "z"])) [.resolve "$deconstruct$0"])])] [.resolve "p"])
#guard obs case_deconPrefix_p__l7 == "ok raw=L[] n=1"

-- deconPrefix_p__l12: *p, z = [1, 2] \n p
def case_deconPrefix_p__l12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.listLiteral [.num 1, .num 2])]), privateProp "p" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "p"])) [.resolve "$deconstruct$0"])]), privateProp "z" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "z"])) [.resolve "$deconstruct$0"])])] [.resolve "p"])
#guard obs case_deconPrefix_p__l12 == "ok raw=L[1] n=1"

-- deconPrefix_p__l12_3: *p, z = [[1, 2], 3] \n p
def case_deconPrefix_p__l12_3 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.listLiteral [(.listLiteral [.num 1, .num 2]), .num 3])]), privateProp "p" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "p"])) [.resolve "$deconstruct$0"])]), privateProp "z" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "z"])) [.resolve "$deconstruct$0"])])] [.resolve "p"])
#guard obs case_deconPrefix_p__l12_3 == "ok raw=L[L[1, 2]] n=1"

-- deconPrefix_p__lle: *p, z = [[]] \n p
def case_deconPrefix_p__lle : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.listLiteral [(.listLiteral [])])]), privateProp "p" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "p"])) [.resolve "$deconstruct$0"])]), privateProp "z" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "z"])) [.resolve "$deconstruct$0"])])] [.resolve "p"])
#guard obs case_deconPrefix_p__lle == "ok raw=L[] n=1"

-- deconPrefix_p__l_e: *p, z = [()] \n p
def case_deconPrefix_p__l_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.listLiteral [(.emptySequence 0)])]), privateProp "p" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "p"])) [.resolve "$deconstruct$0"])]), privateProp "z" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "z"])) [.resolve "$deconstruct$0"])])] [.resolve "p"])
#guard obs case_deconPrefix_p__l_e == "ok raw=L[] n=1"

-- deconPrefix_p__l_p12: *p, z = [(1, 2)] \n p
def case_deconPrefix_p__l_p12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.listLiteral [(.capture [.num 1, .num 2])])]), privateProp "p" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "p"])) [.resolve "$deconstruct$0"])]), privateProp "z" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "z"])) [.resolve "$deconstruct$0"])])] [.resolve "p"])
#guard obs case_deconPrefix_p__l_p12 == "ok raw=L[] n=1"

-- deconPrefix_p__p_l12: *p, z = ([1, 2], 3) \n p
def case_deconPrefix_p__p_l12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [(.listLiteral [.num 1, .num 2]), .num 3])]), privateProp "p" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "p"])) [.resolve "$deconstruct$0"])]), privateProp "z" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "z"])) [.resolve "$deconstruct$0"])])] [.resolve "p"])
#guard obs case_deconPrefix_p__p_l12 == "ok raw=L[L[1, 2]] n=1"

-- deconPrefix_p__pl1: *p, z = ([1]) \n p
def case_deconPrefix_p__pl1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.listLiteral [.num 1])]), privateProp "p" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "p"])) [.resolve "$deconstruct$0"])]), privateProp "z" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "z"])) [.resolve "$deconstruct$0"])])] [.resolve "p"])
#guard obs case_deconPrefix_p__pl1 == "ok raw=L[] n=1"

-- deconPrefix_z__e: *p, z = () \n z
def case_deconPrefix_z__e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.emptySequence 0)]), privateProp "p" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "p"])) [.resolve "$deconstruct$0"])]), privateProp "z" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "z"])) [.resolve "$deconstruct$0"])])] [.resolve "z"])
#guard obs case_deconPrefix_z__e == "err arity"

-- deconPrefix_z__n0: *p, z = 0 \n z
def case_deconPrefix_z__n0 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [.num 0]), privateProp "p" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "p"])) [.resolve "$deconstruct$0"])]), privateProp "z" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "z"])) [.resolve "$deconstruct$0"])])] [.resolve "z"])
#guard obs case_deconPrefix_z__n0 == "ok raw=0 n=1"

-- deconPrefix_z__n1: *p, z = 1 \n z
def case_deconPrefix_z__n1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [.num 1]), privateProp "p" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "p"])) [.resolve "$deconstruct$0"])]), privateProp "z" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "z"])) [.resolve "$deconstruct$0"])])] [.resolve "z"])
#guard obs case_deconPrefix_z__n1 == "ok raw=1 n=1"

-- deconPrefix_z__bt: *p, z = true \n z
def case_deconPrefix_z__bt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [.boolLiteral true]), privateProp "p" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "p"])) [.resolve "$deconstruct$0"])]), privateProp "z" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "z"])) [.resolve "$deconstruct$0"])])] [.resolve "z"])
#guard obs case_deconPrefix_z__bt == "ok raw=true n=1"

-- deconPrefix_z__bf: *p, z = false \n z
def case_deconPrefix_z__bf : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [.boolLiteral false]), privateProp "p" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "p"])) [.resolve "$deconstruct$0"])]), privateProp "z" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "z"])) [.resolve "$deconstruct$0"])])] [.resolve "z"])
#guard obs case_deconPrefix_z__bf == "ok raw=false n=1"

-- deconPrefix_z__pbt: *p, z = (true) \n z
def case_deconPrefix_z__pbt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [.boolLiteral true]), privateProp "p" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "p"])) [.resolve "$deconstruct$0"])]), privateProp "z" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "z"])) [.resolve "$deconstruct$0"])])] [.resolve "z"])
#guard obs case_deconPrefix_z__pbt == "ok raw=true n=1"

-- deconPrefix_z__pbt_e: *p, z = (true, ()) \n z
def case_deconPrefix_z__pbt_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [.boolLiteral true, (.emptySequence 0)])]), privateProp "p" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "p"])) [.resolve "$deconstruct$0"])]), privateProp "z" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "z"])) [.resolve "$deconstruct$0"])])] [.resolve "z"])
#guard obs case_deconPrefix_z__pbt_e == "ok raw=S[] n=1"

-- deconPrefix_z__pbt_1: *p, z = (true, 1) \n z
def case_deconPrefix_z__pbt_1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [.boolLiteral true, .num 1])]), privateProp "p" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "p"])) [.resolve "$deconstruct$0"])]), privateProp "z" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "z"])) [.resolve "$deconstruct$0"])])] [.resolve "z"])
#guard obs case_deconPrefix_z__pbt_1 == "ok raw=1 n=1"

-- deconPrefix_z__lbt: *p, z = [true] \n z
def case_deconPrefix_z__lbt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.listLiteral [.boolLiteral true])]), privateProp "p" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "p"])) [.resolve "$deconstruct$0"])]), privateProp "z" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "z"])) [.resolve "$deconstruct$0"])])] [.resolve "z"])
#guard obs case_deconPrefix_z__lbt == "ok raw=true n=1"

-- deconPrefix_z__lbt_bf: *p, z = [true, false] \n z
def case_deconPrefix_z__lbt_bf : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.listLiteral [.boolLiteral true, .boolLiteral false])]), privateProp "p" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "p"])) [.resolve "$deconstruct$0"])]), privateProp "z" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "z"])) [.resolve "$deconstruct$0"])])] [.resolve "z"])
#guard obs case_deconPrefix_z__lbt_bf == "ok raw=false n=1"

-- deconPrefix_z__lpbt_1: *p, z = [(true, 1)] \n z
def case_deconPrefix_z__lpbt_1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.listLiteral [(.capture [.boolLiteral true, .num 1])])]), privateProp "p" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "p"])) [.resolve "$deconstruct$0"])]), privateProp "z" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "z"])) [.resolve "$deconstruct$0"])])] [.resolve "z"])
#guard obs case_deconPrefix_z__lpbt_1 == "ok raw=S[true, 1] n=1"

-- deconPrefix_z__p1: *p, z = (1) \n z
def case_deconPrefix_z__p1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [.num 1]), privateProp "p" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "p"])) [.resolve "$deconstruct$0"])]), privateProp "z" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "z"])) [.resolve "$deconstruct$0"])])] [.resolve "z"])
#guard obs case_deconPrefix_z__p1 == "ok raw=1 n=1"

-- deconPrefix_z__p12: *p, z = (1, 2) \n z
def case_deconPrefix_z__p12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [.num 1, .num 2])]), privateProp "p" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "p"])) [.resolve "$deconstruct$0"])]), privateProp "z" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "z"])) [.resolve "$deconstruct$0"])])] [.resolve "z"])
#guard obs case_deconPrefix_z__p12 == "ok raw=2 n=1"

-- deconPrefix_z__p123: *p, z = (1, 2, 3) \n z
def case_deconPrefix_z__p123 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [.num 1, .num 2, .num 3])]), privateProp "p" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "p"])) [.resolve "$deconstruct$0"])]), privateProp "z" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "z"])) [.resolve "$deconstruct$0"])])] [.resolve "z"])
#guard obs case_deconPrefix_z__p123 == "ok raw=3 n=1"

-- deconPrefix_z__pee: *p, z = ((), ()) \n z
def case_deconPrefix_z__pee : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [(.emptySequence 0), (.emptySequence 0)])]), privateProp "p" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "p"])) [.resolve "$deconstruct$0"])]), privateProp "z" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "z"])) [.resolve "$deconstruct$0"])])] [.resolve "z"])
#guard obs case_deconPrefix_z__pee == "ok raw=S[] n=1"

-- deconPrefix_z__pe1: *p, z = ((), 1) \n z
def case_deconPrefix_z__pe1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [(.emptySequence 0), .num 1])]), privateProp "p" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "p"])) [.resolve "$deconstruct$0"])]), privateProp "z" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "z"])) [.resolve "$deconstruct$0"])])] [.resolve "z"])
#guard obs case_deconPrefix_z__pe1 == "ok raw=1 n=1"

-- deconPrefix_z__p1e: *p, z = (1, ()) \n z
def case_deconPrefix_z__p1e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [.num 1, (.emptySequence 0)])]), privateProp "p" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "p"])) [.resolve "$deconstruct$0"])]), privateProp "z" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "z"])) [.resolve "$deconstruct$0"])])] [.resolve "z"])
#guard obs case_deconPrefix_z__p1e == "ok raw=S[] n=1"

-- deconPrefix_z__p12_3: *p, z = ((1, 2), 3) \n z
def case_deconPrefix_z__p12_3 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [(.capture [.num 1, .num 2]), .num 3])]), privateProp "p" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "p"])) [.resolve "$deconstruct$0"])]), privateProp "z" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "z"])) [.resolve "$deconstruct$0"])])] [.resolve "z"])
#guard obs case_deconPrefix_z__p12_3 == "ok raw=3 n=1"

-- deconPrefix_z__p12_34: *p, z = ((1, 2), (3, 4)) \n z
def case_deconPrefix_z__p12_34 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [(.capture [.num 1, .num 2]), (.capture [.num 3, .num 4])])]), privateProp "p" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "p"])) [.resolve "$deconstruct$0"])]), privateProp "z" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "z"])) [.resolve "$deconstruct$0"])])] [.resolve "z"])
#guard obs case_deconPrefix_z__p12_34 == "ok raw=S[3, 4] n=1"

-- deconPrefix_z__pe_12: *p, z = ((), (1, 2)) \n z
def case_deconPrefix_z__pe_12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [(.emptySequence 0), (.capture [.num 1, .num 2])])]), privateProp "p" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "p"])) [.resolve "$deconstruct$0"])]), privateProp "z" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "z"])) [.resolve "$deconstruct$0"])])] [.resolve "z"])
#guard obs case_deconPrefix_z__pe_12 == "ok raw=S[1, 2] n=1"

-- deconPrefix_z__ppe1_2: *p, z = (((), 1), 2) \n z
def case_deconPrefix_z__ppe1_2 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [(.capture [(.emptySequence 0), .num 1]), .num 2])]), privateProp "p" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "p"])) [.resolve "$deconstruct$0"])]), privateProp "z" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "z"])) [.resolve "$deconstruct$0"])])] [.resolve "z"])
#guard obs case_deconPrefix_z__ppe1_2 == "ok raw=2 n=1"

-- deconPrefix_z__p12_e: *p, z = ((1, 2), ()) \n z
def case_deconPrefix_z__p12_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [(.capture [.num 1, .num 2]), (.emptySequence 0)])]), privateProp "p" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "p"])) [.resolve "$deconstruct$0"])]), privateProp "z" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "z"])) [.resolve "$deconstruct$0"])])] [.resolve "z"])
#guard obs case_deconPrefix_z__p12_e == "ok raw=S[] n=1"

-- deconPrefix_z__ppe: *p, z = (()) \n z
def case_deconPrefix_z__ppe : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.emptySequence 0)]), privateProp "p" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "p"])) [.resolve "$deconstruct$0"])]), privateProp "z" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "z"])) [.resolve "$deconstruct$0"])])] [.resolve "z"])
#guard obs case_deconPrefix_z__ppe == "err arity"

-- deconPrefix_z__pp1: *p, z = ((1)) \n z
def case_deconPrefix_z__pp1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [.num 1]), privateProp "p" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "p"])) [.resolve "$deconstruct$0"])]), privateProp "z" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "z"])) [.resolve "$deconstruct$0"])])] [.resolve "z"])
#guard obs case_deconPrefix_z__pp1 == "ok raw=1 n=1"

-- deconPrefix_z__ppp12: *p, z = (((1, 2))) \n z
def case_deconPrefix_z__ppp12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [.num 1, .num 2])]), privateProp "p" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "p"])) [.resolve "$deconstruct$0"])]), privateProp "z" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "z"])) [.resolve "$deconstruct$0"])])] [.resolve "z"])
#guard obs case_deconPrefix_z__ppp12 == "ok raw=2 n=1"

-- deconPrefix_z__le: *p, z = [] \n z
def case_deconPrefix_z__le : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.listLiteral [])]), privateProp "p" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "p"])) [.resolve "$deconstruct$0"])]), privateProp "z" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "z"])) [.resolve "$deconstruct$0"])])] [.resolve "z"])
#guard obs case_deconPrefix_z__le == "err arity"

-- deconPrefix_z__l7: *p, z = [7] \n z
def case_deconPrefix_z__l7 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.listLiteral [.num 7])]), privateProp "p" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "p"])) [.resolve "$deconstruct$0"])]), privateProp "z" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "z"])) [.resolve "$deconstruct$0"])])] [.resolve "z"])
#guard obs case_deconPrefix_z__l7 == "ok raw=7 n=1"

-- deconPrefix_z__l12: *p, z = [1, 2] \n z
def case_deconPrefix_z__l12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.listLiteral [.num 1, .num 2])]), privateProp "p" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "p"])) [.resolve "$deconstruct$0"])]), privateProp "z" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "z"])) [.resolve "$deconstruct$0"])])] [.resolve "z"])
#guard obs case_deconPrefix_z__l12 == "ok raw=2 n=1"

-- deconPrefix_z__l12_3: *p, z = [[1, 2], 3] \n z
def case_deconPrefix_z__l12_3 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.listLiteral [(.listLiteral [.num 1, .num 2]), .num 3])]), privateProp "p" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "p"])) [.resolve "$deconstruct$0"])]), privateProp "z" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "z"])) [.resolve "$deconstruct$0"])])] [.resolve "z"])
#guard obs case_deconPrefix_z__l12_3 == "ok raw=3 n=1"

-- deconPrefix_z__lle: *p, z = [[]] \n z
def case_deconPrefix_z__lle : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.listLiteral [(.listLiteral [])])]), privateProp "p" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "p"])) [.resolve "$deconstruct$0"])]), privateProp "z" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "z"])) [.resolve "$deconstruct$0"])])] [.resolve "z"])
#guard obs case_deconPrefix_z__lle == "ok raw=L[] n=1"

-- deconPrefix_z__l_e: *p, z = [()] \n z
def case_deconPrefix_z__l_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.listLiteral [(.emptySequence 0)])]), privateProp "p" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "p"])) [.resolve "$deconstruct$0"])]), privateProp "z" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "z"])) [.resolve "$deconstruct$0"])])] [.resolve "z"])
#guard obs case_deconPrefix_z__l_e == "ok raw=S[] n=1"

-- deconPrefix_z__l_p12: *p, z = [(1, 2)] \n z
def case_deconPrefix_z__l_p12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.listLiteral [(.capture [.num 1, .num 2])])]), privateProp "p" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "p"])) [.resolve "$deconstruct$0"])]), privateProp "z" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "z"])) [.resolve "$deconstruct$0"])])] [.resolve "z"])
#guard obs case_deconPrefix_z__l_p12 == "ok raw=S[1, 2] n=1"

-- deconPrefix_z__p_l12: *p, z = ([1, 2], 3) \n z
def case_deconPrefix_z__p_l12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.capture [(.listLiteral [.num 1, .num 2]), .num 3])]), privateProp "p" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "p"])) [.resolve "$deconstruct$0"])]), privateProp "z" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "z"])) [.resolve "$deconstruct$0"])])] [.resolve "z"])
#guard obs case_deconPrefix_z__p_l12 == "ok raw=3 n=1"

-- deconPrefix_z__pl1: *p, z = ([1]) \n z
def case_deconPrefix_z__pl1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.listLiteral [.num 1])]), privateProp "p" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "p"])) [.resolve "$deconstruct$0"])]), privateProp "z" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "p", kind := .collecting }, .capture { name := "z" }]] [] [] [.param "z"])) [.resolve "$deconstruct$0"])])] [.resolve "z"])
#guard obs case_deconPrefix_z__pl1 == "ok raw=1 n=1"

-- seqWrapPair__e: ((), 99)
def case_seqWrapPair__e : Expr :=
  .algorithmExpr (alg [] [] [] [(.capture [(.emptySequence 0), .num 99])])
#guard obs case_seqWrapPair__e == "ok raw=S[S[], 99] n=1"

-- seqWrapPair__n0: (0, 99)
def case_seqWrapPair__n0 : Expr :=
  .algorithmExpr (alg [] [] [] [(.capture [.num 0, .num 99])])
#guard obs case_seqWrapPair__n0 == "ok raw=S[0, 99] n=1"

-- seqWrapPair__n1: (1, 99)
def case_seqWrapPair__n1 : Expr :=
  .algorithmExpr (alg [] [] [] [(.capture [.num 1, .num 99])])
#guard obs case_seqWrapPair__n1 == "ok raw=S[1, 99] n=1"

-- seqWrapPair__bt: (true, 99)
def case_seqWrapPair__bt : Expr :=
  .algorithmExpr (alg [] [] [] [(.capture [.boolLiteral true, .num 99])])
#guard obs case_seqWrapPair__bt == "ok raw=S[true, 99] n=1"

-- seqWrapPair__bf: (false, 99)
def case_seqWrapPair__bf : Expr :=
  .algorithmExpr (alg [] [] [] [(.capture [.boolLiteral false, .num 99])])
#guard obs case_seqWrapPair__bf == "ok raw=S[false, 99] n=1"

-- seqWrapPair__pbt: ((true), 99)
def case_seqWrapPair__pbt : Expr :=
  .algorithmExpr (alg [] [] [] [(.capture [.boolLiteral true, .num 99])])
#guard obs case_seqWrapPair__pbt == "ok raw=S[true, 99] n=1"

-- seqWrapPair__pbt_e: ((true, ()), 99)
def case_seqWrapPair__pbt_e : Expr :=
  .algorithmExpr (alg [] [] [] [(.capture [(.capture [.boolLiteral true, (.emptySequence 0)]), .num 99])])
#guard obs case_seqWrapPair__pbt_e == "ok raw=S[S[true, S[]], 99] n=1"

-- seqWrapPair__pbt_1: ((true, 1), 99)
def case_seqWrapPair__pbt_1 : Expr :=
  .algorithmExpr (alg [] [] [] [(.capture [(.capture [.boolLiteral true, .num 1]), .num 99])])
#guard obs case_seqWrapPair__pbt_1 == "ok raw=S[S[true, 1], 99] n=1"

-- seqWrapPair__lbt: ([true], 99)
def case_seqWrapPair__lbt : Expr :=
  .algorithmExpr (alg [] [] [] [(.capture [(.listLiteral [.boolLiteral true]), .num 99])])
#guard obs case_seqWrapPair__lbt == "ok raw=S[L[true], 99] n=1"

-- seqWrapPair__lbt_bf: ([true, false], 99)
def case_seqWrapPair__lbt_bf : Expr :=
  .algorithmExpr (alg [] [] [] [(.capture [(.listLiteral [.boolLiteral true, .boolLiteral false]), .num 99])])
#guard obs case_seqWrapPair__lbt_bf == "ok raw=S[L[true, false], 99] n=1"

-- seqWrapPair__lpbt_1: ([(true, 1)], 99)
def case_seqWrapPair__lpbt_1 : Expr :=
  .algorithmExpr (alg [] [] [] [(.capture [(.listLiteral [(.capture [.boolLiteral true, .num 1])]), .num 99])])
#guard obs case_seqWrapPair__lpbt_1 == "ok raw=S[L[S[true, 1]], 99] n=1"

-- seqWrapPair__p1: ((1), 99)
def case_seqWrapPair__p1 : Expr :=
  .algorithmExpr (alg [] [] [] [(.capture [.num 1, .num 99])])
#guard obs case_seqWrapPair__p1 == "ok raw=S[1, 99] n=1"

-- seqWrapPair__p12: ((1, 2), 99)
def case_seqWrapPair__p12 : Expr :=
  .algorithmExpr (alg [] [] [] [(.capture [(.capture [.num 1, .num 2]), .num 99])])
#guard obs case_seqWrapPair__p12 == "ok raw=S[S[1, 2], 99] n=1"

-- seqWrapPair__p123: ((1, 2, 3), 99)
def case_seqWrapPair__p123 : Expr :=
  .algorithmExpr (alg [] [] [] [(.capture [(.capture [.num 1, .num 2, .num 3]), .num 99])])
#guard obs case_seqWrapPair__p123 == "ok raw=S[S[1, 2, 3], 99] n=1"

-- seqWrapPair__pee: (((), ()), 99)
def case_seqWrapPair__pee : Expr :=
  .algorithmExpr (alg [] [] [] [(.capture [(.capture [(.emptySequence 0), (.emptySequence 0)]), .num 99])])
#guard obs case_seqWrapPair__pee == "ok raw=S[S[S[], S[]], 99] n=1"

-- seqWrapPair__pe1: (((), 1), 99)
def case_seqWrapPair__pe1 : Expr :=
  .algorithmExpr (alg [] [] [] [(.capture [(.capture [(.emptySequence 0), .num 1]), .num 99])])
#guard obs case_seqWrapPair__pe1 == "ok raw=S[S[S[], 1], 99] n=1"

-- seqWrapPair__p1e: ((1, ()), 99)
def case_seqWrapPair__p1e : Expr :=
  .algorithmExpr (alg [] [] [] [(.capture [(.capture [.num 1, (.emptySequence 0)]), .num 99])])
#guard obs case_seqWrapPair__p1e == "ok raw=S[S[1, S[]], 99] n=1"

-- seqWrapPair__p12_3: (((1, 2), 3), 99)
def case_seqWrapPair__p12_3 : Expr :=
  .algorithmExpr (alg [] [] [] [(.capture [(.capture [(.capture [.num 1, .num 2]), .num 3]), .num 99])])
#guard obs case_seqWrapPair__p12_3 == "ok raw=S[S[S[1, 2], 3], 99] n=1"

-- seqWrapPair__p12_34: (((1, 2), (3, 4)), 99)
def case_seqWrapPair__p12_34 : Expr :=
  .algorithmExpr (alg [] [] [] [(.capture [(.capture [(.capture [.num 1, .num 2]), (.capture [.num 3, .num 4])]), .num 99])])
#guard obs case_seqWrapPair__p12_34 == "ok raw=S[S[S[1, 2], S[3, 4]], 99] n=1"

-- seqWrapPair__pe_12: (((), (1, 2)), 99)
def case_seqWrapPair__pe_12 : Expr :=
  .algorithmExpr (alg [] [] [] [(.capture [(.capture [(.emptySequence 0), (.capture [.num 1, .num 2])]), .num 99])])
#guard obs case_seqWrapPair__pe_12 == "ok raw=S[S[S[], S[1, 2]], 99] n=1"

-- seqWrapPair__ppe1_2: ((((), 1), 2), 99)
def case_seqWrapPair__ppe1_2 : Expr :=
  .algorithmExpr (alg [] [] [] [(.capture [(.capture [(.capture [(.emptySequence 0), .num 1]), .num 2]), .num 99])])
#guard obs case_seqWrapPair__ppe1_2 == "ok raw=S[S[S[S[], 1], 2], 99] n=1"

-- seqWrapPair__p12_e: (((1, 2), ()), 99)
def case_seqWrapPair__p12_e : Expr :=
  .algorithmExpr (alg [] [] [] [(.capture [(.capture [(.capture [.num 1, .num 2]), (.emptySequence 0)]), .num 99])])
#guard obs case_seqWrapPair__p12_e == "ok raw=S[S[S[1, 2], S[]], 99] n=1"

-- seqWrapPair__ppe: ((()), 99)
def case_seqWrapPair__ppe : Expr :=
  .algorithmExpr (alg [] [] [] [(.capture [(.emptySequence 0), .num 99])])
#guard obs case_seqWrapPair__ppe == "ok raw=S[S[], 99] n=1"

-- seqWrapPair__pp1: (((1)), 99)
def case_seqWrapPair__pp1 : Expr :=
  .algorithmExpr (alg [] [] [] [(.capture [.num 1, .num 99])])
#guard obs case_seqWrapPair__pp1 == "ok raw=S[1, 99] n=1"

-- seqWrapPair__ppp12: ((((1, 2))), 99)
def case_seqWrapPair__ppp12 : Expr :=
  .algorithmExpr (alg [] [] [] [(.capture [(.capture [.num 1, .num 2]), .num 99])])
#guard obs case_seqWrapPair__ppp12 == "ok raw=S[S[1, 2], 99] n=1"

-- seqWrapPair__le: ([], 99)
def case_seqWrapPair__le : Expr :=
  .algorithmExpr (alg [] [] [] [(.capture [(.listLiteral []), .num 99])])
#guard obs case_seqWrapPair__le == "ok raw=S[L[], 99] n=1"

-- seqWrapPair__l7: ([7], 99)
def case_seqWrapPair__l7 : Expr :=
  .algorithmExpr (alg [] [] [] [(.capture [(.listLiteral [.num 7]), .num 99])])
#guard obs case_seqWrapPair__l7 == "ok raw=S[L[7], 99] n=1"

-- seqWrapPair__l12: ([1, 2], 99)
def case_seqWrapPair__l12 : Expr :=
  .algorithmExpr (alg [] [] [] [(.capture [(.listLiteral [.num 1, .num 2]), .num 99])])
#guard obs case_seqWrapPair__l12 == "ok raw=S[L[1, 2], 99] n=1"

-- seqWrapPair__l12_3: ([[1, 2], 3], 99)
def case_seqWrapPair__l12_3 : Expr :=
  .algorithmExpr (alg [] [] [] [(.capture [(.listLiteral [(.listLiteral [.num 1, .num 2]), .num 3]), .num 99])])
#guard obs case_seqWrapPair__l12_3 == "ok raw=S[L[L[1, 2], 3], 99] n=1"

-- seqWrapPair__lle: ([[]], 99)
def case_seqWrapPair__lle : Expr :=
  .algorithmExpr (alg [] [] [] [(.capture [(.listLiteral [(.listLiteral [])]), .num 99])])
#guard obs case_seqWrapPair__lle == "ok raw=S[L[L[]], 99] n=1"

-- seqWrapPair__l_e: ([()], 99)
def case_seqWrapPair__l_e : Expr :=
  .algorithmExpr (alg [] [] [] [(.capture [(.listLiteral [(.emptySequence 0)]), .num 99])])
#guard obs case_seqWrapPair__l_e == "ok raw=S[L[S[]], 99] n=1"

-- seqWrapPair__l_p12: ([(1, 2)], 99)
def case_seqWrapPair__l_p12 : Expr :=
  .algorithmExpr (alg [] [] [] [(.capture [(.listLiteral [(.capture [.num 1, .num 2])]), .num 99])])
#guard obs case_seqWrapPair__l_p12 == "ok raw=S[L[S[1, 2]], 99] n=1"

-- seqWrapPair__p_l12: (([1, 2], 3), 99)
def case_seqWrapPair__p_l12 : Expr :=
  .algorithmExpr (alg [] [] [] [(.capture [(.capture [(.listLiteral [.num 1, .num 2]), .num 3]), .num 99])])
#guard obs case_seqWrapPair__p_l12 == "ok raw=S[S[L[1, 2], 3], 99] n=1"

-- seqWrapPair__pl1: (([1]), 99)
def case_seqWrapPair__pl1 : Expr :=
  .algorithmExpr (alg [] [] [] [(.capture [(.listLiteral [.num 1]), .num 99])])
#guard obs case_seqWrapPair__pl1 == "ok raw=S[L[1], 99] n=1"

-- seqWrapSolo__e: (())
def case_seqWrapSolo__e : Expr :=
  .algorithmExpr (alg [] [] [] [(.emptySequence 0)])
#guard obs case_seqWrapSolo__e == "ok raw=S[] n=1"

-- seqWrapSolo__n0: (0)
def case_seqWrapSolo__n0 : Expr :=
  .algorithmExpr (alg [] [] [] [.num 0])
#guard obs case_seqWrapSolo__n0 == "ok raw=0 n=1"

-- seqWrapSolo__n1: (1)
def case_seqWrapSolo__n1 : Expr :=
  .algorithmExpr (alg [] [] [] [.num 1])
#guard obs case_seqWrapSolo__n1 == "ok raw=1 n=1"

-- seqWrapSolo__bt: (true)
def case_seqWrapSolo__bt : Expr :=
  .algorithmExpr (alg [] [] [] [.boolLiteral true])
#guard obs case_seqWrapSolo__bt == "ok raw=true n=1"

-- seqWrapSolo__bf: (false)
def case_seqWrapSolo__bf : Expr :=
  .algorithmExpr (alg [] [] [] [.boolLiteral false])
#guard obs case_seqWrapSolo__bf == "ok raw=false n=1"

-- seqWrapSolo__pbt: ((true))
def case_seqWrapSolo__pbt : Expr :=
  .algorithmExpr (alg [] [] [] [.boolLiteral true])
#guard obs case_seqWrapSolo__pbt == "ok raw=true n=1"

-- seqWrapSolo__pbt_e: ((true, ()))
def case_seqWrapSolo__pbt_e : Expr :=
  .algorithmExpr (alg [] [] [] [(.capture [.boolLiteral true, (.emptySequence 0)])])
#guard obs case_seqWrapSolo__pbt_e == "ok raw=S[true, S[]] n=1"

-- seqWrapSolo__pbt_1: ((true, 1))
def case_seqWrapSolo__pbt_1 : Expr :=
  .algorithmExpr (alg [] [] [] [(.capture [.boolLiteral true, .num 1])])
#guard obs case_seqWrapSolo__pbt_1 == "ok raw=S[true, 1] n=1"

-- seqWrapSolo__lbt: ([true])
def case_seqWrapSolo__lbt : Expr :=
  .algorithmExpr (alg [] [] [] [(.listLiteral [.boolLiteral true])])
#guard obs case_seqWrapSolo__lbt == "ok raw=L[true] n=1"

-- seqWrapSolo__lbt_bf: ([true, false])
def case_seqWrapSolo__lbt_bf : Expr :=
  .algorithmExpr (alg [] [] [] [(.listLiteral [.boolLiteral true, .boolLiteral false])])
#guard obs case_seqWrapSolo__lbt_bf == "ok raw=L[true, false] n=1"

-- seqWrapSolo__lpbt_1: ([(true, 1)])
def case_seqWrapSolo__lpbt_1 : Expr :=
  .algorithmExpr (alg [] [] [] [(.listLiteral [(.capture [.boolLiteral true, .num 1])])])
#guard obs case_seqWrapSolo__lpbt_1 == "ok raw=L[S[true, 1]] n=1"

-- seqWrapSolo__p1: ((1))
def case_seqWrapSolo__p1 : Expr :=
  .algorithmExpr (alg [] [] [] [.num 1])
#guard obs case_seqWrapSolo__p1 == "ok raw=1 n=1"

-- seqWrapSolo__p12: ((1, 2))
def case_seqWrapSolo__p12 : Expr :=
  .algorithmExpr (alg [] [] [] [(.capture [.num 1, .num 2])])
#guard obs case_seqWrapSolo__p12 == "ok raw=S[1, 2] n=1"

-- seqWrapSolo__p123: ((1, 2, 3))
def case_seqWrapSolo__p123 : Expr :=
  .algorithmExpr (alg [] [] [] [(.capture [.num 1, .num 2, .num 3])])
#guard obs case_seqWrapSolo__p123 == "ok raw=S[1, 2, 3] n=1"

-- seqWrapSolo__pee: (((), ()))
def case_seqWrapSolo__pee : Expr :=
  .algorithmExpr (alg [] [] [] [(.capture [(.emptySequence 0), (.emptySequence 0)])])
#guard obs case_seqWrapSolo__pee == "ok raw=S[S[], S[]] n=1"

-- seqWrapSolo__pe1: (((), 1))
def case_seqWrapSolo__pe1 : Expr :=
  .algorithmExpr (alg [] [] [] [(.capture [(.emptySequence 0), .num 1])])
#guard obs case_seqWrapSolo__pe1 == "ok raw=S[S[], 1] n=1"

-- seqWrapSolo__p1e: ((1, ()))
def case_seqWrapSolo__p1e : Expr :=
  .algorithmExpr (alg [] [] [] [(.capture [.num 1, (.emptySequence 0)])])
#guard obs case_seqWrapSolo__p1e == "ok raw=S[1, S[]] n=1"

-- seqWrapSolo__p12_3: (((1, 2), 3))
def case_seqWrapSolo__p12_3 : Expr :=
  .algorithmExpr (alg [] [] [] [(.capture [(.capture [.num 1, .num 2]), .num 3])])
#guard obs case_seqWrapSolo__p12_3 == "ok raw=S[S[1, 2], 3] n=1"

-- seqWrapSolo__p12_34: (((1, 2), (3, 4)))
def case_seqWrapSolo__p12_34 : Expr :=
  .algorithmExpr (alg [] [] [] [(.capture [(.capture [.num 1, .num 2]), (.capture [.num 3, .num 4])])])
#guard obs case_seqWrapSolo__p12_34 == "ok raw=S[S[1, 2], S[3, 4]] n=1"

-- seqWrapSolo__pe_12: (((), (1, 2)))
def case_seqWrapSolo__pe_12 : Expr :=
  .algorithmExpr (alg [] [] [] [(.capture [(.emptySequence 0), (.capture [.num 1, .num 2])])])
#guard obs case_seqWrapSolo__pe_12 == "ok raw=S[S[], S[1, 2]] n=1"

-- seqWrapSolo__ppe1_2: ((((), 1), 2))
def case_seqWrapSolo__ppe1_2 : Expr :=
  .algorithmExpr (alg [] [] [] [(.capture [(.capture [(.emptySequence 0), .num 1]), .num 2])])
#guard obs case_seqWrapSolo__ppe1_2 == "ok raw=S[S[S[], 1], 2] n=1"

-- seqWrapSolo__p12_e: (((1, 2), ()))
def case_seqWrapSolo__p12_e : Expr :=
  .algorithmExpr (alg [] [] [] [(.capture [(.capture [.num 1, .num 2]), (.emptySequence 0)])])
#guard obs case_seqWrapSolo__p12_e == "ok raw=S[S[1, 2], S[]] n=1"

-- seqWrapSolo__ppe: ((()))
def case_seqWrapSolo__ppe : Expr :=
  .algorithmExpr (alg [] [] [] [(.emptySequence 0)])
#guard obs case_seqWrapSolo__ppe == "ok raw=S[] n=1"

-- seqWrapSolo__pp1: (((1)))
def case_seqWrapSolo__pp1 : Expr :=
  .algorithmExpr (alg [] [] [] [.num 1])
#guard obs case_seqWrapSolo__pp1 == "ok raw=1 n=1"

-- seqWrapSolo__ppp12: ((((1, 2))))
def case_seqWrapSolo__ppp12 : Expr :=
  .algorithmExpr (alg [] [] [] [(.capture [.num 1, .num 2])])
#guard obs case_seqWrapSolo__ppp12 == "ok raw=S[1, 2] n=1"

-- seqWrapSolo__le: ([])
def case_seqWrapSolo__le : Expr :=
  .algorithmExpr (alg [] [] [] [(.listLiteral [])])
#guard obs case_seqWrapSolo__le == "ok raw=L[] n=1"

-- seqWrapSolo__l7: ([7])
def case_seqWrapSolo__l7 : Expr :=
  .algorithmExpr (alg [] [] [] [(.listLiteral [.num 7])])
#guard obs case_seqWrapSolo__l7 == "ok raw=L[7] n=1"

-- seqWrapSolo__l12: ([1, 2])
def case_seqWrapSolo__l12 : Expr :=
  .algorithmExpr (alg [] [] [] [(.listLiteral [.num 1, .num 2])])
#guard obs case_seqWrapSolo__l12 == "ok raw=L[1, 2] n=1"

-- seqWrapSolo__l12_3: ([[1, 2], 3])
def case_seqWrapSolo__l12_3 : Expr :=
  .algorithmExpr (alg [] [] [] [(.listLiteral [(.listLiteral [.num 1, .num 2]), .num 3])])
#guard obs case_seqWrapSolo__l12_3 == "ok raw=L[L[1, 2], 3] n=1"

-- seqWrapSolo__lle: ([[]])
def case_seqWrapSolo__lle : Expr :=
  .algorithmExpr (alg [] [] [] [(.listLiteral [(.listLiteral [])])])
#guard obs case_seqWrapSolo__lle == "ok raw=L[L[]] n=1"

-- seqWrapSolo__l_e: ([()])
def case_seqWrapSolo__l_e : Expr :=
  .algorithmExpr (alg [] [] [] [(.listLiteral [(.emptySequence 0)])])
#guard obs case_seqWrapSolo__l_e == "ok raw=L[S[]] n=1"

-- seqWrapSolo__l_p12: ([(1, 2)])
def case_seqWrapSolo__l_p12 : Expr :=
  .algorithmExpr (alg [] [] [] [(.listLiteral [(.capture [.num 1, .num 2])])])
#guard obs case_seqWrapSolo__l_p12 == "ok raw=L[S[1, 2]] n=1"

-- seqWrapSolo__p_l12: (([1, 2], 3))
def case_seqWrapSolo__p_l12 : Expr :=
  .algorithmExpr (alg [] [] [] [(.capture [(.listLiteral [.num 1, .num 2]), .num 3])])
#guard obs case_seqWrapSolo__p_l12 == "ok raw=S[L[1, 2], 3] n=1"

-- seqWrapSolo__pl1: (([1]))
def case_seqWrapSolo__pl1 : Expr :=
  .algorithmExpr (alg [] [] [] [(.listLiteral [.num 1])])
#guard obs case_seqWrapSolo__pl1 == "ok raw=L[1] n=1"

-- spreadRoot__e: ()*
def case_spreadRoot__e : Expr :=
  .algorithmExpr (alg [] [] [] [(.sequenceSpread (.emptySequence 0))])
#guard obs case_spreadRoot__e == "ok raw=S[] n=0"

-- spreadRoot__n0: 0*
def case_spreadRoot__n0 : Expr :=
  .algorithmExpr (alg [] [] [] [(.sequenceSpread (.num 0))])
#guard obs case_spreadRoot__n0 == "ok raw=0 n=1"

-- spreadRoot__n1: 1*
def case_spreadRoot__n1 : Expr :=
  .algorithmExpr (alg [] [] [] [(.sequenceSpread (.num 1))])
#guard obs case_spreadRoot__n1 == "ok raw=1 n=1"

-- spreadRoot__bt: true*
def case_spreadRoot__bt : Expr :=
  .algorithmExpr (alg [] [] [] [(.sequenceSpread (.boolLiteral true))])
#guard obs case_spreadRoot__bt == "ok raw=true n=1"

-- spreadRoot__bf: false*
def case_spreadRoot__bf : Expr :=
  .algorithmExpr (alg [] [] [] [(.sequenceSpread (.boolLiteral false))])
#guard obs case_spreadRoot__bf == "ok raw=false n=1"

-- spreadRoot__pbt: (true)*
def case_spreadRoot__pbt : Expr :=
  .algorithmExpr (alg [] [] [] [(.sequenceSpread (.boolLiteral true))])
#guard obs case_spreadRoot__pbt == "ok raw=true n=1"

-- spreadRoot__pbt_e: (true, ())*
def case_spreadRoot__pbt_e : Expr :=
  .algorithmExpr (alg [] [] [] [(.sequenceSpread (.capture [.boolLiteral true, (.emptySequence 0)]))])
#guard obs case_spreadRoot__pbt_e == "ok raw=S[true, S[]] n=2"

-- spreadRoot__pbt_1: (true, 1)*
def case_spreadRoot__pbt_1 : Expr :=
  .algorithmExpr (alg [] [] [] [(.sequenceSpread (.capture [.boolLiteral true, .num 1]))])
#guard obs case_spreadRoot__pbt_1 == "ok raw=S[true, 1] n=2"

-- spreadRoot__lbt: [true]*
def case_spreadRoot__lbt : Expr :=
  .algorithmExpr (alg [] [] [] [(.sequenceSpread (.listLiteral [.boolLiteral true]))])
#guard obs case_spreadRoot__lbt == "ok raw=true n=1"

-- spreadRoot__lbt_bf: [true, false]*
def case_spreadRoot__lbt_bf : Expr :=
  .algorithmExpr (alg [] [] [] [(.sequenceSpread (.listLiteral [.boolLiteral true, .boolLiteral false]))])
#guard obs case_spreadRoot__lbt_bf == "ok raw=S[true, false] n=2"

-- spreadRoot__lpbt_1: [(true, 1)]*
def case_spreadRoot__lpbt_1 : Expr :=
  .algorithmExpr (alg [] [] [] [(.sequenceSpread (.listLiteral [(.capture [.boolLiteral true, .num 1])]))])
#guard obs case_spreadRoot__lpbt_1 == "ok raw=S[true, 1] n=1"

-- spreadRoot__p1: (1)*
def case_spreadRoot__p1 : Expr :=
  .algorithmExpr (alg [] [] [] [(.sequenceSpread (.num 1))])
#guard obs case_spreadRoot__p1 == "ok raw=1 n=1"

-- spreadRoot__p12: (1, 2)*
def case_spreadRoot__p12 : Expr :=
  .algorithmExpr (alg [] [] [] [(.sequenceSpread (.capture [.num 1, .num 2]))])
#guard obs case_spreadRoot__p12 == "ok raw=S[1, 2] n=2"

-- spreadRoot__p123: (1, 2, 3)*
def case_spreadRoot__p123 : Expr :=
  .algorithmExpr (alg [] [] [] [(.sequenceSpread (.capture [.num 1, .num 2, .num 3]))])
#guard obs case_spreadRoot__p123 == "ok raw=S[1, 2, 3] n=3"

-- spreadRoot__pee: ((), ())*
def case_spreadRoot__pee : Expr :=
  .algorithmExpr (alg [] [] [] [(.sequenceSpread (.capture [(.emptySequence 0), (.emptySequence 0)]))])
#guard obs case_spreadRoot__pee == "ok raw=S[S[], S[]] n=2"

-- spreadRoot__pe1: ((), 1)*
def case_spreadRoot__pe1 : Expr :=
  .algorithmExpr (alg [] [] [] [(.sequenceSpread (.capture [(.emptySequence 0), .num 1]))])
#guard obs case_spreadRoot__pe1 == "ok raw=S[S[], 1] n=2"

-- spreadRoot__p1e: (1, ())*
def case_spreadRoot__p1e : Expr :=
  .algorithmExpr (alg [] [] [] [(.sequenceSpread (.capture [.num 1, (.emptySequence 0)]))])
#guard obs case_spreadRoot__p1e == "ok raw=S[1, S[]] n=2"

-- spreadRoot__p12_3: ((1, 2), 3)*
def case_spreadRoot__p12_3 : Expr :=
  .algorithmExpr (alg [] [] [] [(.sequenceSpread (.capture [(.capture [.num 1, .num 2]), .num 3]))])
#guard obs case_spreadRoot__p12_3 == "ok raw=S[S[1, 2], 3] n=2"

-- spreadRoot__p12_34: ((1, 2), (3, 4))*
def case_spreadRoot__p12_34 : Expr :=
  .algorithmExpr (alg [] [] [] [(.sequenceSpread (.capture [(.capture [.num 1, .num 2]), (.capture [.num 3, .num 4])]))])
#guard obs case_spreadRoot__p12_34 == "ok raw=S[S[1, 2], S[3, 4]] n=2"

-- spreadRoot__pe_12: ((), (1, 2))*
def case_spreadRoot__pe_12 : Expr :=
  .algorithmExpr (alg [] [] [] [(.sequenceSpread (.capture [(.emptySequence 0), (.capture [.num 1, .num 2])]))])
#guard obs case_spreadRoot__pe_12 == "ok raw=S[S[], S[1, 2]] n=2"

-- spreadRoot__ppe1_2: (((), 1), 2)*
def case_spreadRoot__ppe1_2 : Expr :=
  .algorithmExpr (alg [] [] [] [(.sequenceSpread (.capture [(.capture [(.emptySequence 0), .num 1]), .num 2]))])
#guard obs case_spreadRoot__ppe1_2 == "ok raw=S[S[S[], 1], 2] n=2"

-- spreadRoot__p12_e: ((1, 2), ())*
def case_spreadRoot__p12_e : Expr :=
  .algorithmExpr (alg [] [] [] [(.sequenceSpread (.capture [(.capture [.num 1, .num 2]), (.emptySequence 0)]))])
#guard obs case_spreadRoot__p12_e == "ok raw=S[S[1, 2], S[]] n=2"

-- spreadRoot__ppe: (())*
def case_spreadRoot__ppe : Expr :=
  .algorithmExpr (alg [] [] [] [(.sequenceSpread (.emptySequence 0))])
#guard obs case_spreadRoot__ppe == "ok raw=S[] n=0"

-- spreadRoot__pp1: ((1))*
def case_spreadRoot__pp1 : Expr :=
  .algorithmExpr (alg [] [] [] [(.sequenceSpread (.num 1))])
#guard obs case_spreadRoot__pp1 == "ok raw=1 n=1"

-- spreadRoot__ppp12: (((1, 2)))*
def case_spreadRoot__ppp12 : Expr :=
  .algorithmExpr (alg [] [] [] [(.sequenceSpread (.capture [.num 1, .num 2]))])
#guard obs case_spreadRoot__ppp12 == "ok raw=S[1, 2] n=2"

-- spreadRoot__le: []*
def case_spreadRoot__le : Expr :=
  .algorithmExpr (alg [] [] [] [(.sequenceSpread (.listLiteral []))])
#guard obs case_spreadRoot__le == "ok raw=S[] n=0"

-- spreadRoot__l7: [7]*
def case_spreadRoot__l7 : Expr :=
  .algorithmExpr (alg [] [] [] [(.sequenceSpread (.listLiteral [.num 7]))])
#guard obs case_spreadRoot__l7 == "ok raw=7 n=1"

-- spreadRoot__l12: [1, 2]*
def case_spreadRoot__l12 : Expr :=
  .algorithmExpr (alg [] [] [] [(.sequenceSpread (.listLiteral [.num 1, .num 2]))])
#guard obs case_spreadRoot__l12 == "ok raw=S[1, 2] n=2"

-- spreadRoot__l12_3: [[1, 2], 3]*
def case_spreadRoot__l12_3 : Expr :=
  .algorithmExpr (alg [] [] [] [(.sequenceSpread (.listLiteral [(.listLiteral [.num 1, .num 2]), .num 3]))])
#guard obs case_spreadRoot__l12_3 == "ok raw=S[L[1, 2], 3] n=2"

-- spreadRoot__lle: [[]]*
def case_spreadRoot__lle : Expr :=
  .algorithmExpr (alg [] [] [] [(.sequenceSpread (.listLiteral [(.listLiteral [])]))])
#guard obs case_spreadRoot__lle == "ok raw=L[] n=1"

-- spreadRoot__l_e: [()]*
def case_spreadRoot__l_e : Expr :=
  .algorithmExpr (alg [] [] [] [(.sequenceSpread (.listLiteral [(.emptySequence 0)]))])
#guard obs case_spreadRoot__l_e == "ok raw=S[] n=1"

-- spreadRoot__l_p12: [(1, 2)]*
def case_spreadRoot__l_p12 : Expr :=
  .algorithmExpr (alg [] [] [] [(.sequenceSpread (.listLiteral [(.capture [.num 1, .num 2])]))])
#guard obs case_spreadRoot__l_p12 == "ok raw=S[1, 2] n=1"

-- spreadRoot__p_l12: ([1, 2], 3)*
def case_spreadRoot__p_l12 : Expr :=
  .algorithmExpr (alg [] [] [] [(.sequenceSpread (.capture [(.listLiteral [.num 1, .num 2]), .num 3]))])
#guard obs case_spreadRoot__p_l12 == "ok raw=S[L[1, 2], 3] n=2"

-- spreadRoot__pl1: ([1])*
def case_spreadRoot__pl1 : Expr :=
  .algorithmExpr (alg [] [] [] [(.sequenceSpread (.listLiteral [.num 1]))])
#guard obs case_spreadRoot__pl1 == "ok raw=1 n=1"

-- spreadInSeq__e: (()*, 99)
def case_spreadInSeq__e : Expr :=
  .algorithmExpr (alg [] [] [] [(.capture [(.sequenceSpread (.emptySequence 0)), .num 99])])
#guard obs case_spreadInSeq__e == "ok raw=99 n=1"

-- spreadInSeq__n0: (0*, 99)
def case_spreadInSeq__n0 : Expr :=
  .algorithmExpr (alg [] [] [] [(.capture [(.sequenceSpread (.num 0)), .num 99])])
#guard obs case_spreadInSeq__n0 == "ok raw=S[0, 99] n=1"

-- spreadInSeq__n1: (1*, 99)
def case_spreadInSeq__n1 : Expr :=
  .algorithmExpr (alg [] [] [] [(.capture [(.sequenceSpread (.num 1)), .num 99])])
#guard obs case_spreadInSeq__n1 == "ok raw=S[1, 99] n=1"

-- spreadInSeq__bt: (true*, 99)
def case_spreadInSeq__bt : Expr :=
  .algorithmExpr (alg [] [] [] [(.capture [(.sequenceSpread (.boolLiteral true)), .num 99])])
#guard obs case_spreadInSeq__bt == "ok raw=S[true, 99] n=1"

-- spreadInSeq__bf: (false*, 99)
def case_spreadInSeq__bf : Expr :=
  .algorithmExpr (alg [] [] [] [(.capture [(.sequenceSpread (.boolLiteral false)), .num 99])])
#guard obs case_spreadInSeq__bf == "ok raw=S[false, 99] n=1"

-- spreadInSeq__pbt: ((true)*, 99)
def case_spreadInSeq__pbt : Expr :=
  .algorithmExpr (alg [] [] [] [(.capture [(.sequenceSpread (.boolLiteral true)), .num 99])])
#guard obs case_spreadInSeq__pbt == "ok raw=S[true, 99] n=1"

-- spreadInSeq__pbt_e: ((true, ())*, 99)
def case_spreadInSeq__pbt_e : Expr :=
  .algorithmExpr (alg [] [] [] [(.capture [(.sequenceSpread (.capture [.boolLiteral true, (.emptySequence 0)])), .num 99])])
#guard obs case_spreadInSeq__pbt_e == "ok raw=S[true, S[], 99] n=1"

-- spreadInSeq__pbt_1: ((true, 1)*, 99)
def case_spreadInSeq__pbt_1 : Expr :=
  .algorithmExpr (alg [] [] [] [(.capture [(.sequenceSpread (.capture [.boolLiteral true, .num 1])), .num 99])])
#guard obs case_spreadInSeq__pbt_1 == "ok raw=S[true, 1, 99] n=1"

-- spreadInSeq__lbt: ([true]*, 99)
def case_spreadInSeq__lbt : Expr :=
  .algorithmExpr (alg [] [] [] [(.capture [(.sequenceSpread (.listLiteral [.boolLiteral true])), .num 99])])
#guard obs case_spreadInSeq__lbt == "ok raw=S[true, 99] n=1"

-- spreadInSeq__lbt_bf: ([true, false]*, 99)
def case_spreadInSeq__lbt_bf : Expr :=
  .algorithmExpr (alg [] [] [] [(.capture [(.sequenceSpread (.listLiteral [.boolLiteral true, .boolLiteral false])), .num 99])])
#guard obs case_spreadInSeq__lbt_bf == "ok raw=S[true, false, 99] n=1"

-- spreadInSeq__lpbt_1: ([(true, 1)]*, 99)
def case_spreadInSeq__lpbt_1 : Expr :=
  .algorithmExpr (alg [] [] [] [(.capture [(.sequenceSpread (.listLiteral [(.capture [.boolLiteral true, .num 1])])), .num 99])])
#guard obs case_spreadInSeq__lpbt_1 == "ok raw=S[S[true, 1], 99] n=1"

-- spreadInSeq__p1: ((1)*, 99)
def case_spreadInSeq__p1 : Expr :=
  .algorithmExpr (alg [] [] [] [(.capture [(.sequenceSpread (.num 1)), .num 99])])
#guard obs case_spreadInSeq__p1 == "ok raw=S[1, 99] n=1"

-- spreadInSeq__p12: ((1, 2)*, 99)
def case_spreadInSeq__p12 : Expr :=
  .algorithmExpr (alg [] [] [] [(.capture [(.sequenceSpread (.capture [.num 1, .num 2])), .num 99])])
#guard obs case_spreadInSeq__p12 == "ok raw=S[1, 2, 99] n=1"

-- spreadInSeq__p123: ((1, 2, 3)*, 99)
def case_spreadInSeq__p123 : Expr :=
  .algorithmExpr (alg [] [] [] [(.capture [(.sequenceSpread (.capture [.num 1, .num 2, .num 3])), .num 99])])
#guard obs case_spreadInSeq__p123 == "ok raw=S[1, 2, 3, 99] n=1"

-- spreadInSeq__pee: (((), ())*, 99)
def case_spreadInSeq__pee : Expr :=
  .algorithmExpr (alg [] [] [] [(.capture [(.sequenceSpread (.capture [(.emptySequence 0), (.emptySequence 0)])), .num 99])])
#guard obs case_spreadInSeq__pee == "ok raw=S[S[], S[], 99] n=1"

-- spreadInSeq__pe1: (((), 1)*, 99)
def case_spreadInSeq__pe1 : Expr :=
  .algorithmExpr (alg [] [] [] [(.capture [(.sequenceSpread (.capture [(.emptySequence 0), .num 1])), .num 99])])
#guard obs case_spreadInSeq__pe1 == "ok raw=S[S[], 1, 99] n=1"

-- spreadInSeq__p1e: ((1, ())*, 99)
def case_spreadInSeq__p1e : Expr :=
  .algorithmExpr (alg [] [] [] [(.capture [(.sequenceSpread (.capture [.num 1, (.emptySequence 0)])), .num 99])])
#guard obs case_spreadInSeq__p1e == "ok raw=S[1, S[], 99] n=1"

-- spreadInSeq__p12_3: (((1, 2), 3)*, 99)
def case_spreadInSeq__p12_3 : Expr :=
  .algorithmExpr (alg [] [] [] [(.capture [(.sequenceSpread (.capture [(.capture [.num 1, .num 2]), .num 3])), .num 99])])
#guard obs case_spreadInSeq__p12_3 == "ok raw=S[S[1, 2], 3, 99] n=1"

-- spreadInSeq__p12_34: (((1, 2), (3, 4))*, 99)
def case_spreadInSeq__p12_34 : Expr :=
  .algorithmExpr (alg [] [] [] [(.capture [(.sequenceSpread (.capture [(.capture [.num 1, .num 2]), (.capture [.num 3, .num 4])])), .num 99])])
#guard obs case_spreadInSeq__p12_34 == "ok raw=S[S[1, 2], S[3, 4], 99] n=1"

-- spreadInSeq__pe_12: (((), (1, 2))*, 99)
def case_spreadInSeq__pe_12 : Expr :=
  .algorithmExpr (alg [] [] [] [(.capture [(.sequenceSpread (.capture [(.emptySequence 0), (.capture [.num 1, .num 2])])), .num 99])])
#guard obs case_spreadInSeq__pe_12 == "ok raw=S[S[], S[1, 2], 99] n=1"

-- spreadInSeq__ppe1_2: ((((), 1), 2)*, 99)
def case_spreadInSeq__ppe1_2 : Expr :=
  .algorithmExpr (alg [] [] [] [(.capture [(.sequenceSpread (.capture [(.capture [(.emptySequence 0), .num 1]), .num 2])), .num 99])])
#guard obs case_spreadInSeq__ppe1_2 == "ok raw=S[S[S[], 1], 2, 99] n=1"

-- spreadInSeq__p12_e: (((1, 2), ())*, 99)
def case_spreadInSeq__p12_e : Expr :=
  .algorithmExpr (alg [] [] [] [(.capture [(.sequenceSpread (.capture [(.capture [.num 1, .num 2]), (.emptySequence 0)])), .num 99])])
#guard obs case_spreadInSeq__p12_e == "ok raw=S[S[1, 2], S[], 99] n=1"

-- spreadInSeq__ppe: ((())*, 99)
def case_spreadInSeq__ppe : Expr :=
  .algorithmExpr (alg [] [] [] [(.capture [(.sequenceSpread (.emptySequence 0)), .num 99])])
#guard obs case_spreadInSeq__ppe == "ok raw=99 n=1"

-- spreadInSeq__pp1: (((1))*, 99)
def case_spreadInSeq__pp1 : Expr :=
  .algorithmExpr (alg [] [] [] [(.capture [(.sequenceSpread (.num 1)), .num 99])])
#guard obs case_spreadInSeq__pp1 == "ok raw=S[1, 99] n=1"

-- spreadInSeq__ppp12: ((((1, 2)))*, 99)
def case_spreadInSeq__ppp12 : Expr :=
  .algorithmExpr (alg [] [] [] [(.capture [(.sequenceSpread (.capture [.num 1, .num 2])), .num 99])])
#guard obs case_spreadInSeq__ppp12 == "ok raw=S[1, 2, 99] n=1"

-- spreadInSeq__le: ([]*, 99)
def case_spreadInSeq__le : Expr :=
  .algorithmExpr (alg [] [] [] [(.capture [(.sequenceSpread (.listLiteral [])), .num 99])])
#guard obs case_spreadInSeq__le == "ok raw=99 n=1"

-- spreadInSeq__l7: ([7]*, 99)
def case_spreadInSeq__l7 : Expr :=
  .algorithmExpr (alg [] [] [] [(.capture [(.sequenceSpread (.listLiteral [.num 7])), .num 99])])
#guard obs case_spreadInSeq__l7 == "ok raw=S[7, 99] n=1"

-- spreadInSeq__l12: ([1, 2]*, 99)
def case_spreadInSeq__l12 : Expr :=
  .algorithmExpr (alg [] [] [] [(.capture [(.sequenceSpread (.listLiteral [.num 1, .num 2])), .num 99])])
#guard obs case_spreadInSeq__l12 == "ok raw=S[1, 2, 99] n=1"

-- spreadInSeq__l12_3: ([[1, 2], 3]*, 99)
def case_spreadInSeq__l12_3 : Expr :=
  .algorithmExpr (alg [] [] [] [(.capture [(.sequenceSpread (.listLiteral [(.listLiteral [.num 1, .num 2]), .num 3])), .num 99])])
#guard obs case_spreadInSeq__l12_3 == "ok raw=S[L[1, 2], 3, 99] n=1"

-- spreadInSeq__lle: ([[]]*, 99)
def case_spreadInSeq__lle : Expr :=
  .algorithmExpr (alg [] [] [] [(.capture [(.sequenceSpread (.listLiteral [(.listLiteral [])])), .num 99])])
#guard obs case_spreadInSeq__lle == "ok raw=S[L[], 99] n=1"

-- spreadInSeq__l_e: ([()]*, 99)
def case_spreadInSeq__l_e : Expr :=
  .algorithmExpr (alg [] [] [] [(.capture [(.sequenceSpread (.listLiteral [(.emptySequence 0)])), .num 99])])
#guard obs case_spreadInSeq__l_e == "ok raw=S[S[], 99] n=1"

-- spreadInSeq__l_p12: ([(1, 2)]*, 99)
def case_spreadInSeq__l_p12 : Expr :=
  .algorithmExpr (alg [] [] [] [(.capture [(.sequenceSpread (.listLiteral [(.capture [.num 1, .num 2])])), .num 99])])
#guard obs case_spreadInSeq__l_p12 == "ok raw=S[S[1, 2], 99] n=1"

-- spreadInSeq__p_l12: (([1, 2], 3)*, 99)
def case_spreadInSeq__p_l12 : Expr :=
  .algorithmExpr (alg [] [] [] [(.capture [(.sequenceSpread (.capture [(.listLiteral [.num 1, .num 2]), .num 3])), .num 99])])
#guard obs case_spreadInSeq__p_l12 == "ok raw=S[L[1, 2], 3, 99] n=1"

-- spreadInSeq__pl1: (([1])*, 99)
def case_spreadInSeq__pl1 : Expr :=
  .algorithmExpr (alg [] [] [] [(.capture [(.sequenceSpread (.listLiteral [.num 1])), .num 99])])
#guard obs case_spreadInSeq__pl1 == "ok raw=S[1, 99] n=1"

-- count__e: count(())
def case_count__e : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "count") [(.emptySequence 0)])])
#guard obs case_count__e == "ok raw=0 n=1"

-- count__n0: count(0)
def case_count__n0 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "count") [.num 0])])
#guard obs case_count__n0 == "ok raw=1 n=1"

-- count__n1: count(1)
def case_count__n1 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "count") [.num 1])])
#guard obs case_count__n1 == "ok raw=1 n=1"

-- count__bt: count(true)
def case_count__bt : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "count") [.boolLiteral true])])
#guard obs case_count__bt == "ok raw=1 n=1"

-- count__bf: count(false)
def case_count__bf : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "count") [.boolLiteral false])])
#guard obs case_count__bf == "ok raw=1 n=1"

-- count__pbt: count((true))
def case_count__pbt : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "count") [.boolLiteral true])])
#guard obs case_count__pbt == "ok raw=1 n=1"

-- count__pbt_e: count((true, ()))
def case_count__pbt_e : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "count") [(.capture [.boolLiteral true, (.emptySequence 0)])])])
#guard obs case_count__pbt_e == "ok raw=2 n=1"

-- count__pbt_1: count((true, 1))
def case_count__pbt_1 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "count") [(.capture [.boolLiteral true, .num 1])])])
#guard obs case_count__pbt_1 == "ok raw=2 n=1"

-- count__lbt: count([true])
def case_count__lbt : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "count") [(.listLiteral [.boolLiteral true])])])
#guard obs case_count__lbt == "ok raw=1 n=1"

-- count__lbt_bf: count([true, false])
def case_count__lbt_bf : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "count") [(.listLiteral [.boolLiteral true, .boolLiteral false])])])
#guard obs case_count__lbt_bf == "ok raw=2 n=1"

-- count__lpbt_1: count([(true, 1)])
def case_count__lpbt_1 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "count") [(.listLiteral [(.capture [.boolLiteral true, .num 1])])])])
#guard obs case_count__lpbt_1 == "ok raw=1 n=1"

-- count__p1: count((1))
def case_count__p1 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "count") [.num 1])])
#guard obs case_count__p1 == "ok raw=1 n=1"

-- count__p12: count((1, 2))
def case_count__p12 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "count") [(.capture [.num 1, .num 2])])])
#guard obs case_count__p12 == "ok raw=2 n=1"

-- count__p123: count((1, 2, 3))
def case_count__p123 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "count") [(.capture [.num 1, .num 2, .num 3])])])
#guard obs case_count__p123 == "ok raw=3 n=1"

-- count__pee: count(((), ()))
def case_count__pee : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "count") [(.capture [(.emptySequence 0), (.emptySequence 0)])])])
#guard obs case_count__pee == "ok raw=2 n=1"

-- count__pe1: count(((), 1))
def case_count__pe1 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "count") [(.capture [(.emptySequence 0), .num 1])])])
#guard obs case_count__pe1 == "ok raw=2 n=1"

-- count__p1e: count((1, ()))
def case_count__p1e : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "count") [(.capture [.num 1, (.emptySequence 0)])])])
#guard obs case_count__p1e == "ok raw=2 n=1"

-- count__p12_3: count(((1, 2), 3))
def case_count__p12_3 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "count") [(.capture [(.capture [.num 1, .num 2]), .num 3])])])
#guard obs case_count__p12_3 == "ok raw=2 n=1"

-- count__p12_34: count(((1, 2), (3, 4)))
def case_count__p12_34 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "count") [(.capture [(.capture [.num 1, .num 2]), (.capture [.num 3, .num 4])])])])
#guard obs case_count__p12_34 == "ok raw=2 n=1"

-- count__pe_12: count(((), (1, 2)))
def case_count__pe_12 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "count") [(.capture [(.emptySequence 0), (.capture [.num 1, .num 2])])])])
#guard obs case_count__pe_12 == "ok raw=2 n=1"

-- count__ppe1_2: count((((), 1), 2))
def case_count__ppe1_2 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "count") [(.capture [(.capture [(.emptySequence 0), .num 1]), .num 2])])])
#guard obs case_count__ppe1_2 == "ok raw=2 n=1"

-- count__p12_e: count(((1, 2), ()))
def case_count__p12_e : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "count") [(.capture [(.capture [.num 1, .num 2]), (.emptySequence 0)])])])
#guard obs case_count__p12_e == "ok raw=2 n=1"

-- count__ppe: count((()))
def case_count__ppe : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "count") [(.emptySequence 0)])])
#guard obs case_count__ppe == "ok raw=0 n=1"

-- count__pp1: count(((1)))
def case_count__pp1 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "count") [.num 1])])
#guard obs case_count__pp1 == "ok raw=1 n=1"

-- count__ppp12: count((((1, 2))))
def case_count__ppp12 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "count") [(.capture [.num 1, .num 2])])])
#guard obs case_count__ppp12 == "ok raw=2 n=1"

-- count__le: count([])
def case_count__le : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "count") [(.listLiteral [])])])
#guard obs case_count__le == "ok raw=0 n=1"

-- count__l7: count([7])
def case_count__l7 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "count") [(.listLiteral [.num 7])])])
#guard obs case_count__l7 == "ok raw=1 n=1"

-- count__l12: count([1, 2])
def case_count__l12 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "count") [(.listLiteral [.num 1, .num 2])])])
#guard obs case_count__l12 == "ok raw=2 n=1"

-- count__l12_3: count([[1, 2], 3])
def case_count__l12_3 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "count") [(.listLiteral [(.listLiteral [.num 1, .num 2]), .num 3])])])
#guard obs case_count__l12_3 == "ok raw=2 n=1"

-- count__lle: count([[]])
def case_count__lle : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "count") [(.listLiteral [(.listLiteral [])])])])
#guard obs case_count__lle == "ok raw=1 n=1"

-- count__l_e: count([()])
def case_count__l_e : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "count") [(.listLiteral [(.emptySequence 0)])])])
#guard obs case_count__l_e == "ok raw=1 n=1"

-- count__l_p12: count([(1, 2)])
def case_count__l_p12 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "count") [(.listLiteral [(.capture [.num 1, .num 2])])])])
#guard obs case_count__l_p12 == "ok raw=1 n=1"

-- count__p_l12: count(([1, 2], 3))
def case_count__p_l12 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "count") [(.capture [(.listLiteral [.num 1, .num 2]), .num 3])])])
#guard obs case_count__p_l12 == "ok raw=2 n=1"

-- count__pl1: count(([1]))
def case_count__pl1 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "count") [(.listLiteral [.num 1])])])
#guard obs case_count__pl1 == "ok raw=1 n=1"

-- countSpread__e: count(()*)
def case_countSpread__e : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "count") [(.sequenceSpread (.emptySequence 0))])])
#guard obs case_countSpread__e == "err arity"

-- countSpread__n0: count(0*)
def case_countSpread__n0 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "count") [(.sequenceSpread (.num 0))])])
#guard obs case_countSpread__n0 == "ok raw=1 n=1"

-- countSpread__n1: count(1*)
def case_countSpread__n1 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "count") [(.sequenceSpread (.num 1))])])
#guard obs case_countSpread__n1 == "ok raw=1 n=1"

-- countSpread__bt: count(true*)
def case_countSpread__bt : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "count") [(.sequenceSpread (.boolLiteral true))])])
#guard obs case_countSpread__bt == "ok raw=1 n=1"

-- countSpread__bf: count(false*)
def case_countSpread__bf : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "count") [(.sequenceSpread (.boolLiteral false))])])
#guard obs case_countSpread__bf == "ok raw=1 n=1"

-- countSpread__pbt: count((true)*)
def case_countSpread__pbt : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "count") [(.sequenceSpread (.boolLiteral true))])])
#guard obs case_countSpread__pbt == "ok raw=1 n=1"

-- countSpread__pbt_e: count((true, ())*)
def case_countSpread__pbt_e : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "count") [(.sequenceSpread (.capture [.boolLiteral true, (.emptySequence 0)]))])])
#guard obs case_countSpread__pbt_e == "err arity"

-- countSpread__pbt_1: count((true, 1)*)
def case_countSpread__pbt_1 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "count") [(.sequenceSpread (.capture [.boolLiteral true, .num 1]))])])
#guard obs case_countSpread__pbt_1 == "err arity"

-- countSpread__lbt: count([true]*)
def case_countSpread__lbt : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "count") [(.sequenceSpread (.listLiteral [.boolLiteral true]))])])
#guard obs case_countSpread__lbt == "ok raw=1 n=1"

-- countSpread__lbt_bf: count([true, false]*)
def case_countSpread__lbt_bf : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "count") [(.sequenceSpread (.listLiteral [.boolLiteral true, .boolLiteral false]))])])
#guard obs case_countSpread__lbt_bf == "err arity"

-- countSpread__lpbt_1: count([(true, 1)]*)
def case_countSpread__lpbt_1 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "count") [(.sequenceSpread (.listLiteral [(.capture [.boolLiteral true, .num 1])]))])])
#guard obs case_countSpread__lpbt_1 == "ok raw=2 n=1"

-- countSpread__p1: count((1)*)
def case_countSpread__p1 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "count") [(.sequenceSpread (.num 1))])])
#guard obs case_countSpread__p1 == "ok raw=1 n=1"

-- countSpread__p12: count((1, 2)*)
def case_countSpread__p12 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "count") [(.sequenceSpread (.capture [.num 1, .num 2]))])])
#guard obs case_countSpread__p12 == "err arity"

-- countSpread__p123: count((1, 2, 3)*)
def case_countSpread__p123 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "count") [(.sequenceSpread (.capture [.num 1, .num 2, .num 3]))])])
#guard obs case_countSpread__p123 == "err arity"

-- countSpread__pee: count(((), ())*)
def case_countSpread__pee : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "count") [(.sequenceSpread (.capture [(.emptySequence 0), (.emptySequence 0)]))])])
#guard obs case_countSpread__pee == "err arity"

-- countSpread__pe1: count(((), 1)*)
def case_countSpread__pe1 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "count") [(.sequenceSpread (.capture [(.emptySequence 0), .num 1]))])])
#guard obs case_countSpread__pe1 == "err arity"

-- countSpread__p1e: count((1, ())*)
def case_countSpread__p1e : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "count") [(.sequenceSpread (.capture [.num 1, (.emptySequence 0)]))])])
#guard obs case_countSpread__p1e == "err arity"

-- countSpread__p12_3: count(((1, 2), 3)*)
def case_countSpread__p12_3 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "count") [(.sequenceSpread (.capture [(.capture [.num 1, .num 2]), .num 3]))])])
#guard obs case_countSpread__p12_3 == "err arity"

-- countSpread__p12_34: count(((1, 2), (3, 4))*)
def case_countSpread__p12_34 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "count") [(.sequenceSpread (.capture [(.capture [.num 1, .num 2]), (.capture [.num 3, .num 4])]))])])
#guard obs case_countSpread__p12_34 == "err arity"

-- countSpread__pe_12: count(((), (1, 2))*)
def case_countSpread__pe_12 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "count") [(.sequenceSpread (.capture [(.emptySequence 0), (.capture [.num 1, .num 2])]))])])
#guard obs case_countSpread__pe_12 == "err arity"

-- countSpread__ppe1_2: count((((), 1), 2)*)
def case_countSpread__ppe1_2 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "count") [(.sequenceSpread (.capture [(.capture [(.emptySequence 0), .num 1]), .num 2]))])])
#guard obs case_countSpread__ppe1_2 == "err arity"

-- countSpread__p12_e: count(((1, 2), ())*)
def case_countSpread__p12_e : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "count") [(.sequenceSpread (.capture [(.capture [.num 1, .num 2]), (.emptySequence 0)]))])])
#guard obs case_countSpread__p12_e == "err arity"

-- countSpread__ppe: count((())*)
def case_countSpread__ppe : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "count") [(.sequenceSpread (.emptySequence 0))])])
#guard obs case_countSpread__ppe == "err arity"

-- countSpread__pp1: count(((1))*)
def case_countSpread__pp1 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "count") [(.sequenceSpread (.num 1))])])
#guard obs case_countSpread__pp1 == "ok raw=1 n=1"

-- countSpread__ppp12: count((((1, 2)))*)
def case_countSpread__ppp12 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "count") [(.sequenceSpread (.capture [.num 1, .num 2]))])])
#guard obs case_countSpread__ppp12 == "err arity"

-- countSpread__le: count([]*)
def case_countSpread__le : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "count") [(.sequenceSpread (.listLiteral []))])])
#guard obs case_countSpread__le == "err arity"

-- countSpread__l7: count([7]*)
def case_countSpread__l7 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "count") [(.sequenceSpread (.listLiteral [.num 7]))])])
#guard obs case_countSpread__l7 == "ok raw=1 n=1"

-- countSpread__l12: count([1, 2]*)
def case_countSpread__l12 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "count") [(.sequenceSpread (.listLiteral [.num 1, .num 2]))])])
#guard obs case_countSpread__l12 == "err arity"

-- countSpread__l12_3: count([[1, 2], 3]*)
def case_countSpread__l12_3 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "count") [(.sequenceSpread (.listLiteral [(.listLiteral [.num 1, .num 2]), .num 3]))])])
#guard obs case_countSpread__l12_3 == "err arity"

-- countSpread__lle: count([[]]*)
def case_countSpread__lle : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "count") [(.sequenceSpread (.listLiteral [(.listLiteral [])]))])])
#guard obs case_countSpread__lle == "ok raw=0 n=1"

-- countSpread__l_e: count([()]*)
def case_countSpread__l_e : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "count") [(.sequenceSpread (.listLiteral [(.emptySequence 0)]))])])
#guard obs case_countSpread__l_e == "ok raw=0 n=1"

-- countSpread__l_p12: count([(1, 2)]*)
def case_countSpread__l_p12 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "count") [(.sequenceSpread (.listLiteral [(.capture [.num 1, .num 2])]))])])
#guard obs case_countSpread__l_p12 == "ok raw=2 n=1"

-- countSpread__p_l12: count(([1, 2], 3)*)
def case_countSpread__p_l12 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "count") [(.sequenceSpread (.capture [(.listLiteral [.num 1, .num 2]), .num 3]))])])
#guard obs case_countSpread__p_l12 == "err arity"

-- countSpread__pl1: count(([1])*)
def case_countSpread__pl1 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "count") [(.sequenceSpread (.listLiteral [.num 1]))])])
#guard obs case_countSpread__pl1 == "ok raw=1 n=1"

-- dotCount__e: x = () \n x.count
def case_dotCount__e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.emptySequence 0)])] [(.dotCall (.resolve "x") "count" none)])
#guard obs case_dotCount__e == "ok raw=0 n=1"

-- dotCount__n0: x = 0 \n x.count
def case_dotCount__n0 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [.num 0])] [(.dotCall (.resolve "x") "count" none)])
#guard obs case_dotCount__n0 == "ok raw=1 n=1"

-- dotCount__n1: x = 1 \n x.count
def case_dotCount__n1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [.num 1])] [(.dotCall (.resolve "x") "count" none)])
#guard obs case_dotCount__n1 == "ok raw=1 n=1"

-- dotCount__bt: x = true \n x.count
def case_dotCount__bt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [.boolLiteral true])] [(.dotCall (.resolve "x") "count" none)])
#guard obs case_dotCount__bt == "ok raw=1 n=1"

-- dotCount__bf: x = false \n x.count
def case_dotCount__bf : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [.boolLiteral false])] [(.dotCall (.resolve "x") "count" none)])
#guard obs case_dotCount__bf == "ok raw=1 n=1"

-- dotCount__pbt: x = (true) \n x.count
def case_dotCount__pbt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [.boolLiteral true])] [(.dotCall (.resolve "x") "count" none)])
#guard obs case_dotCount__pbt == "ok raw=1 n=1"

-- dotCount__pbt_e: x = (true, ()) \n x.count
def case_dotCount__pbt_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [.boolLiteral true, (.emptySequence 0)])])] [(.dotCall (.resolve "x") "count" none)])
#guard obs case_dotCount__pbt_e == "ok raw=2 n=1"

-- dotCount__pbt_1: x = (true, 1) \n x.count
def case_dotCount__pbt_1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [.boolLiteral true, .num 1])])] [(.dotCall (.resolve "x") "count" none)])
#guard obs case_dotCount__pbt_1 == "ok raw=2 n=1"

-- dotCount__lbt: x = [true] \n x.count
def case_dotCount__lbt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [.boolLiteral true])])] [(.dotCall (.resolve "x") "count" none)])
#guard obs case_dotCount__lbt == "ok raw=1 n=1"

-- dotCount__lbt_bf: x = [true, false] \n x.count
def case_dotCount__lbt_bf : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [.boolLiteral true, .boolLiteral false])])] [(.dotCall (.resolve "x") "count" none)])
#guard obs case_dotCount__lbt_bf == "ok raw=2 n=1"

-- dotCount__lpbt_1: x = [(true, 1)] \n x.count
def case_dotCount__lpbt_1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [(.capture [.boolLiteral true, .num 1])])])] [(.dotCall (.resolve "x") "count" none)])
#guard obs case_dotCount__lpbt_1 == "ok raw=1 n=1"

-- dotCount__p1: x = (1) \n x.count
def case_dotCount__p1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [.num 1])] [(.dotCall (.resolve "x") "count" none)])
#guard obs case_dotCount__p1 == "ok raw=1 n=1"

-- dotCount__p12: x = (1, 2) \n x.count
def case_dotCount__p12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [.num 1, .num 2])])] [(.dotCall (.resolve "x") "count" none)])
#guard obs case_dotCount__p12 == "ok raw=2 n=1"

-- dotCount__p123: x = (1, 2, 3) \n x.count
def case_dotCount__p123 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [.num 1, .num 2, .num 3])])] [(.dotCall (.resolve "x") "count" none)])
#guard obs case_dotCount__p123 == "ok raw=3 n=1"

-- dotCount__pee: x = ((), ()) \n x.count
def case_dotCount__pee : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.emptySequence 0), (.emptySequence 0)])])] [(.dotCall (.resolve "x") "count" none)])
#guard obs case_dotCount__pee == "ok raw=2 n=1"

-- dotCount__pe1: x = ((), 1) \n x.count
def case_dotCount__pe1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.emptySequence 0), .num 1])])] [(.dotCall (.resolve "x") "count" none)])
#guard obs case_dotCount__pe1 == "ok raw=2 n=1"

-- dotCount__p1e: x = (1, ()) \n x.count
def case_dotCount__p1e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [.num 1, (.emptySequence 0)])])] [(.dotCall (.resolve "x") "count" none)])
#guard obs case_dotCount__p1e == "ok raw=2 n=1"

-- dotCount__p12_3: x = ((1, 2), 3) \n x.count
def case_dotCount__p12_3 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.capture [.num 1, .num 2]), .num 3])])] [(.dotCall (.resolve "x") "count" none)])
#guard obs case_dotCount__p12_3 == "ok raw=2 n=1"

-- dotCount__p12_34: x = ((1, 2), (3, 4)) \n x.count
def case_dotCount__p12_34 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.capture [.num 1, .num 2]), (.capture [.num 3, .num 4])])])] [(.dotCall (.resolve "x") "count" none)])
#guard obs case_dotCount__p12_34 == "ok raw=2 n=1"

-- dotCount__pe_12: x = ((), (1, 2)) \n x.count
def case_dotCount__pe_12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.emptySequence 0), (.capture [.num 1, .num 2])])])] [(.dotCall (.resolve "x") "count" none)])
#guard obs case_dotCount__pe_12 == "ok raw=2 n=1"

-- dotCount__ppe1_2: x = (((), 1), 2) \n x.count
def case_dotCount__ppe1_2 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.capture [(.emptySequence 0), .num 1]), .num 2])])] [(.dotCall (.resolve "x") "count" none)])
#guard obs case_dotCount__ppe1_2 == "ok raw=2 n=1"

-- dotCount__p12_e: x = ((1, 2), ()) \n x.count
def case_dotCount__p12_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.capture [.num 1, .num 2]), (.emptySequence 0)])])] [(.dotCall (.resolve "x") "count" none)])
#guard obs case_dotCount__p12_e == "ok raw=2 n=1"

-- dotCount__ppe: x = (()) \n x.count
def case_dotCount__ppe : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.emptySequence 0)])] [(.dotCall (.resolve "x") "count" none)])
#guard obs case_dotCount__ppe == "ok raw=0 n=1"

-- dotCount__pp1: x = ((1)) \n x.count
def case_dotCount__pp1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [.num 1])] [(.dotCall (.resolve "x") "count" none)])
#guard obs case_dotCount__pp1 == "ok raw=1 n=1"

-- dotCount__ppp12: x = (((1, 2))) \n x.count
def case_dotCount__ppp12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [.num 1, .num 2])])] [(.dotCall (.resolve "x") "count" none)])
#guard obs case_dotCount__ppp12 == "ok raw=2 n=1"

-- dotCount__le: x = [] \n x.count
def case_dotCount__le : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [])])] [(.dotCall (.resolve "x") "count" none)])
#guard obs case_dotCount__le == "ok raw=0 n=1"

-- dotCount__l7: x = [7] \n x.count
def case_dotCount__l7 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [.num 7])])] [(.dotCall (.resolve "x") "count" none)])
#guard obs case_dotCount__l7 == "ok raw=1 n=1"

-- dotCount__l12: x = [1, 2] \n x.count
def case_dotCount__l12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [.num 1, .num 2])])] [(.dotCall (.resolve "x") "count" none)])
#guard obs case_dotCount__l12 == "ok raw=2 n=1"

-- dotCount__l12_3: x = [[1, 2], 3] \n x.count
def case_dotCount__l12_3 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [(.listLiteral [.num 1, .num 2]), .num 3])])] [(.dotCall (.resolve "x") "count" none)])
#guard obs case_dotCount__l12_3 == "ok raw=2 n=1"

-- dotCount__lle: x = [[]] \n x.count
def case_dotCount__lle : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [(.listLiteral [])])])] [(.dotCall (.resolve "x") "count" none)])
#guard obs case_dotCount__lle == "ok raw=1 n=1"

-- dotCount__l_e: x = [()] \n x.count
def case_dotCount__l_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [(.emptySequence 0)])])] [(.dotCall (.resolve "x") "count" none)])
#guard obs case_dotCount__l_e == "ok raw=1 n=1"

-- dotCount__l_p12: x = [(1, 2)] \n x.count
def case_dotCount__l_p12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [(.capture [.num 1, .num 2])])])] [(.dotCall (.resolve "x") "count" none)])
#guard obs case_dotCount__l_p12 == "ok raw=1 n=1"

-- dotCount__p_l12: x = ([1, 2], 3) \n x.count
def case_dotCount__p_l12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.listLiteral [.num 1, .num 2]), .num 3])])] [(.dotCall (.resolve "x") "count" none)])
#guard obs case_dotCount__p_l12 == "ok raw=2 n=1"

-- dotCount__pl1: x = ([1]) \n x.count
def case_dotCount__pl1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [.num 1])])] [(.dotCall (.resolve "x") "count" none)])
#guard obs case_dotCount__pl1 == "ok raw=1 n=1"

-- literalDotCount__e: (()).count
def case_literalDotCount__e : Expr :=
  .algorithmExpr (alg [] [] [] [(.dotCall (.emptySequence 0) "count" none)])
#guard obs case_literalDotCount__e == "ok raw=0 n=1"

-- literalDotCount__n0: (0).count
def case_literalDotCount__n0 : Expr :=
  .algorithmExpr (alg [] [] [] [(.dotCall (.num 0) "count" none)])
#guard obs case_literalDotCount__n0 == "ok raw=1 n=1"

-- literalDotCount__n1: (1).count
def case_literalDotCount__n1 : Expr :=
  .algorithmExpr (alg [] [] [] [(.dotCall (.num 1) "count" none)])
#guard obs case_literalDotCount__n1 == "ok raw=1 n=1"

-- literalDotCount__bt: (true).count
def case_literalDotCount__bt : Expr :=
  .algorithmExpr (alg [] [] [] [(.dotCall (.boolLiteral true) "count" none)])
#guard obs case_literalDotCount__bt == "ok raw=1 n=1"

-- literalDotCount__bf: (false).count
def case_literalDotCount__bf : Expr :=
  .algorithmExpr (alg [] [] [] [(.dotCall (.boolLiteral false) "count" none)])
#guard obs case_literalDotCount__bf == "ok raw=1 n=1"

-- literalDotCount__pbt: ((true)).count
def case_literalDotCount__pbt : Expr :=
  .algorithmExpr (alg [] [] [] [(.dotCall (.boolLiteral true) "count" none)])
#guard obs case_literalDotCount__pbt == "ok raw=1 n=1"

-- literalDotCount__pbt_e: ((true, ())).count
def case_literalDotCount__pbt_e : Expr :=
  .algorithmExpr (alg [] [] [] [(.dotCall (.capture [.boolLiteral true, (.emptySequence 0)]) "count" none)])
#guard obs case_literalDotCount__pbt_e == "ok raw=2 n=1"

-- literalDotCount__pbt_1: ((true, 1)).count
def case_literalDotCount__pbt_1 : Expr :=
  .algorithmExpr (alg [] [] [] [(.dotCall (.capture [.boolLiteral true, .num 1]) "count" none)])
#guard obs case_literalDotCount__pbt_1 == "ok raw=2 n=1"

-- literalDotCount__lbt: ([true]).count
def case_literalDotCount__lbt : Expr :=
  .algorithmExpr (alg [] [] [] [(.dotCall (.listLiteral [.boolLiteral true]) "count" none)])
#guard obs case_literalDotCount__lbt == "ok raw=1 n=1"

-- literalDotCount__lbt_bf: ([true, false]).count
def case_literalDotCount__lbt_bf : Expr :=
  .algorithmExpr (alg [] [] [] [(.dotCall (.listLiteral [.boolLiteral true, .boolLiteral false]) "count" none)])
#guard obs case_literalDotCount__lbt_bf == "ok raw=2 n=1"

-- literalDotCount__lpbt_1: ([(true, 1)]).count
def case_literalDotCount__lpbt_1 : Expr :=
  .algorithmExpr (alg [] [] [] [(.dotCall (.listLiteral [(.capture [.boolLiteral true, .num 1])]) "count" none)])
#guard obs case_literalDotCount__lpbt_1 == "ok raw=1 n=1"

-- literalDotCount__p1: ((1)).count
def case_literalDotCount__p1 : Expr :=
  .algorithmExpr (alg [] [] [] [(.dotCall (.num 1) "count" none)])
#guard obs case_literalDotCount__p1 == "ok raw=1 n=1"

-- literalDotCount__p12: ((1, 2)).count
def case_literalDotCount__p12 : Expr :=
  .algorithmExpr (alg [] [] [] [(.dotCall (.capture [.num 1, .num 2]) "count" none)])
#guard obs case_literalDotCount__p12 == "ok raw=2 n=1"

-- literalDotCount__p123: ((1, 2, 3)).count
def case_literalDotCount__p123 : Expr :=
  .algorithmExpr (alg [] [] [] [(.dotCall (.capture [.num 1, .num 2, .num 3]) "count" none)])
#guard obs case_literalDotCount__p123 == "ok raw=3 n=1"

-- literalDotCount__pee: (((), ())).count
def case_literalDotCount__pee : Expr :=
  .algorithmExpr (alg [] [] [] [(.dotCall (.capture [(.emptySequence 0), (.emptySequence 0)]) "count" none)])
#guard obs case_literalDotCount__pee == "ok raw=2 n=1"

-- literalDotCount__pe1: (((), 1)).count
def case_literalDotCount__pe1 : Expr :=
  .algorithmExpr (alg [] [] [] [(.dotCall (.capture [(.emptySequence 0), .num 1]) "count" none)])
#guard obs case_literalDotCount__pe1 == "ok raw=2 n=1"

-- literalDotCount__p1e: ((1, ())).count
def case_literalDotCount__p1e : Expr :=
  .algorithmExpr (alg [] [] [] [(.dotCall (.capture [.num 1, (.emptySequence 0)]) "count" none)])
#guard obs case_literalDotCount__p1e == "ok raw=2 n=1"

-- literalDotCount__p12_3: (((1, 2), 3)).count
def case_literalDotCount__p12_3 : Expr :=
  .algorithmExpr (alg [] [] [] [(.dotCall (.capture [(.capture [.num 1, .num 2]), .num 3]) "count" none)])
#guard obs case_literalDotCount__p12_3 == "ok raw=2 n=1"

-- literalDotCount__p12_34: (((1, 2), (3, 4))).count
def case_literalDotCount__p12_34 : Expr :=
  .algorithmExpr (alg [] [] [] [(.dotCall (.capture [(.capture [.num 1, .num 2]), (.capture [.num 3, .num 4])]) "count" none)])
#guard obs case_literalDotCount__p12_34 == "ok raw=2 n=1"

-- literalDotCount__pe_12: (((), (1, 2))).count
def case_literalDotCount__pe_12 : Expr :=
  .algorithmExpr (alg [] [] [] [(.dotCall (.capture [(.emptySequence 0), (.capture [.num 1, .num 2])]) "count" none)])
#guard obs case_literalDotCount__pe_12 == "ok raw=2 n=1"

-- literalDotCount__ppe1_2: ((((), 1), 2)).count
def case_literalDotCount__ppe1_2 : Expr :=
  .algorithmExpr (alg [] [] [] [(.dotCall (.capture [(.capture [(.emptySequence 0), .num 1]), .num 2]) "count" none)])
#guard obs case_literalDotCount__ppe1_2 == "ok raw=2 n=1"

-- literalDotCount__p12_e: (((1, 2), ())).count
def case_literalDotCount__p12_e : Expr :=
  .algorithmExpr (alg [] [] [] [(.dotCall (.capture [(.capture [.num 1, .num 2]), (.emptySequence 0)]) "count" none)])
#guard obs case_literalDotCount__p12_e == "ok raw=2 n=1"

-- literalDotCount__ppe: ((())).count
def case_literalDotCount__ppe : Expr :=
  .algorithmExpr (alg [] [] [] [(.dotCall (.emptySequence 0) "count" none)])
#guard obs case_literalDotCount__ppe == "ok raw=0 n=1"

-- literalDotCount__pp1: (((1))).count
def case_literalDotCount__pp1 : Expr :=
  .algorithmExpr (alg [] [] [] [(.dotCall (.num 1) "count" none)])
#guard obs case_literalDotCount__pp1 == "ok raw=1 n=1"

-- literalDotCount__ppp12: ((((1, 2)))).count
def case_literalDotCount__ppp12 : Expr :=
  .algorithmExpr (alg [] [] [] [(.dotCall (.capture [.num 1, .num 2]) "count" none)])
#guard obs case_literalDotCount__ppp12 == "ok raw=2 n=1"

-- literalDotCount__le: ([]).count
def case_literalDotCount__le : Expr :=
  .algorithmExpr (alg [] [] [] [(.dotCall (.listLiteral []) "count" none)])
#guard obs case_literalDotCount__le == "ok raw=0 n=1"

-- literalDotCount__l7: ([7]).count
def case_literalDotCount__l7 : Expr :=
  .algorithmExpr (alg [] [] [] [(.dotCall (.listLiteral [.num 7]) "count" none)])
#guard obs case_literalDotCount__l7 == "ok raw=1 n=1"

-- literalDotCount__l12: ([1, 2]).count
def case_literalDotCount__l12 : Expr :=
  .algorithmExpr (alg [] [] [] [(.dotCall (.listLiteral [.num 1, .num 2]) "count" none)])
#guard obs case_literalDotCount__l12 == "ok raw=2 n=1"

-- literalDotCount__l12_3: ([[1, 2], 3]).count
def case_literalDotCount__l12_3 : Expr :=
  .algorithmExpr (alg [] [] [] [(.dotCall (.listLiteral [(.listLiteral [.num 1, .num 2]), .num 3]) "count" none)])
#guard obs case_literalDotCount__l12_3 == "ok raw=2 n=1"

-- literalDotCount__lle: ([[]]).count
def case_literalDotCount__lle : Expr :=
  .algorithmExpr (alg [] [] [] [(.dotCall (.listLiteral [(.listLiteral [])]) "count" none)])
#guard obs case_literalDotCount__lle == "ok raw=1 n=1"

-- literalDotCount__l_e: ([()]).count
def case_literalDotCount__l_e : Expr :=
  .algorithmExpr (alg [] [] [] [(.dotCall (.listLiteral [(.emptySequence 0)]) "count" none)])
#guard obs case_literalDotCount__l_e == "ok raw=1 n=1"

-- literalDotCount__l_p12: ([(1, 2)]).count
def case_literalDotCount__l_p12 : Expr :=
  .algorithmExpr (alg [] [] [] [(.dotCall (.listLiteral [(.capture [.num 1, .num 2])]) "count" none)])
#guard obs case_literalDotCount__l_p12 == "ok raw=1 n=1"

-- literalDotCount__p_l12: (([1, 2], 3)).count
def case_literalDotCount__p_l12 : Expr :=
  .algorithmExpr (alg [] [] [] [(.dotCall (.capture [(.listLiteral [.num 1, .num 2]), .num 3]) "count" none)])
#guard obs case_literalDotCount__p_l12 == "ok raw=2 n=1"

-- literalDotCount__pl1: (([1])).count
def case_literalDotCount__pl1 : Expr :=
  .algorithmExpr (alg [] [] [] [(.dotCall (.listLiteral [.num 1]) "count" none)])
#guard obs case_literalDotCount__pl1 == "ok raw=1 n=1"

-- index0__e: x = () \n x:0
def case_index0__e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.emptySequence 0)])] [(.index (.resolve "x") (.num 0))])
#guard obs case_index0__e == "err index"

-- index0__n0: x = 0 \n x:0
def case_index0__n0 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [.num 0])] [(.index (.resolve "x") (.num 0))])
#guard obs case_index0__n0 == "ok raw=0 n=1"

-- index0__n1: x = 1 \n x:0
def case_index0__n1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [.num 1])] [(.index (.resolve "x") (.num 0))])
#guard obs case_index0__n1 == "ok raw=1 n=1"

-- index0__bt: x = true \n x:0
def case_index0__bt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [.boolLiteral true])] [(.index (.resolve "x") (.num 0))])
#guard obs case_index0__bt == "ok raw=true n=1"

-- index0__bf: x = false \n x:0
def case_index0__bf : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [.boolLiteral false])] [(.index (.resolve "x") (.num 0))])
#guard obs case_index0__bf == "ok raw=false n=1"

-- index0__pbt: x = (true) \n x:0
def case_index0__pbt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [.boolLiteral true])] [(.index (.resolve "x") (.num 0))])
#guard obs case_index0__pbt == "ok raw=true n=1"

-- index0__pbt_e: x = (true, ()) \n x:0
def case_index0__pbt_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [.boolLiteral true, (.emptySequence 0)])])] [(.index (.resolve "x") (.num 0))])
#guard obs case_index0__pbt_e == "ok raw=true n=1"

-- index0__pbt_1: x = (true, 1) \n x:0
def case_index0__pbt_1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [.boolLiteral true, .num 1])])] [(.index (.resolve "x") (.num 0))])
#guard obs case_index0__pbt_1 == "ok raw=true n=1"

-- index0__lbt: x = [true] \n x:0
def case_index0__lbt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [.boolLiteral true])])] [(.index (.resolve "x") (.num 0))])
#guard obs case_index0__lbt == "ok raw=true n=1"

-- index0__lbt_bf: x = [true, false] \n x:0
def case_index0__lbt_bf : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [.boolLiteral true, .boolLiteral false])])] [(.index (.resolve "x") (.num 0))])
#guard obs case_index0__lbt_bf == "ok raw=true n=1"

-- index0__lpbt_1: x = [(true, 1)] \n x:0
def case_index0__lpbt_1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [(.capture [.boolLiteral true, .num 1])])])] [(.index (.resolve "x") (.num 0))])
#guard obs case_index0__lpbt_1 == "ok raw=S[true, 1] n=1"

-- index0__p1: x = (1) \n x:0
def case_index0__p1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [.num 1])] [(.index (.resolve "x") (.num 0))])
#guard obs case_index0__p1 == "ok raw=1 n=1"

-- index0__p12: x = (1, 2) \n x:0
def case_index0__p12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [.num 1, .num 2])])] [(.index (.resolve "x") (.num 0))])
#guard obs case_index0__p12 == "ok raw=1 n=1"

-- index0__p123: x = (1, 2, 3) \n x:0
def case_index0__p123 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [.num 1, .num 2, .num 3])])] [(.index (.resolve "x") (.num 0))])
#guard obs case_index0__p123 == "ok raw=1 n=1"

-- index0__pee: x = ((), ()) \n x:0
def case_index0__pee : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.emptySequence 0), (.emptySequence 0)])])] [(.index (.resolve "x") (.num 0))])
#guard obs case_index0__pee == "ok raw=S[] n=1"

-- index0__pe1: x = ((), 1) \n x:0
def case_index0__pe1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.emptySequence 0), .num 1])])] [(.index (.resolve "x") (.num 0))])
#guard obs case_index0__pe1 == "ok raw=S[] n=1"

-- index0__p1e: x = (1, ()) \n x:0
def case_index0__p1e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [.num 1, (.emptySequence 0)])])] [(.index (.resolve "x") (.num 0))])
#guard obs case_index0__p1e == "ok raw=1 n=1"

-- index0__p12_3: x = ((1, 2), 3) \n x:0
def case_index0__p12_3 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.capture [.num 1, .num 2]), .num 3])])] [(.index (.resolve "x") (.num 0))])
#guard obs case_index0__p12_3 == "ok raw=S[1, 2] n=1"

-- index0__p12_34: x = ((1, 2), (3, 4)) \n x:0
def case_index0__p12_34 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.capture [.num 1, .num 2]), (.capture [.num 3, .num 4])])])] [(.index (.resolve "x") (.num 0))])
#guard obs case_index0__p12_34 == "ok raw=S[1, 2] n=1"

-- index0__pe_12: x = ((), (1, 2)) \n x:0
def case_index0__pe_12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.emptySequence 0), (.capture [.num 1, .num 2])])])] [(.index (.resolve "x") (.num 0))])
#guard obs case_index0__pe_12 == "ok raw=S[] n=1"

-- index0__ppe1_2: x = (((), 1), 2) \n x:0
def case_index0__ppe1_2 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.capture [(.emptySequence 0), .num 1]), .num 2])])] [(.index (.resolve "x") (.num 0))])
#guard obs case_index0__ppe1_2 == "ok raw=S[S[], 1] n=1"

-- index0__p12_e: x = ((1, 2), ()) \n x:0
def case_index0__p12_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.capture [.num 1, .num 2]), (.emptySequence 0)])])] [(.index (.resolve "x") (.num 0))])
#guard obs case_index0__p12_e == "ok raw=S[1, 2] n=1"

-- index0__ppe: x = (()) \n x:0
def case_index0__ppe : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.emptySequence 0)])] [(.index (.resolve "x") (.num 0))])
#guard obs case_index0__ppe == "err index"

-- index0__pp1: x = ((1)) \n x:0
def case_index0__pp1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [.num 1])] [(.index (.resolve "x") (.num 0))])
#guard obs case_index0__pp1 == "ok raw=1 n=1"

-- index0__ppp12: x = (((1, 2))) \n x:0
def case_index0__ppp12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [.num 1, .num 2])])] [(.index (.resolve "x") (.num 0))])
#guard obs case_index0__ppp12 == "ok raw=1 n=1"

-- index0__le: x = [] \n x:0
def case_index0__le : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [])])] [(.index (.resolve "x") (.num 0))])
#guard obs case_index0__le == "err index"

-- index0__l7: x = [7] \n x:0
def case_index0__l7 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [.num 7])])] [(.index (.resolve "x") (.num 0))])
#guard obs case_index0__l7 == "ok raw=7 n=1"

-- index0__l12: x = [1, 2] \n x:0
def case_index0__l12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [.num 1, .num 2])])] [(.index (.resolve "x") (.num 0))])
#guard obs case_index0__l12 == "ok raw=1 n=1"

-- index0__l12_3: x = [[1, 2], 3] \n x:0
def case_index0__l12_3 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [(.listLiteral [.num 1, .num 2]), .num 3])])] [(.index (.resolve "x") (.num 0))])
#guard obs case_index0__l12_3 == "ok raw=L[1, 2] n=1"

-- index0__lle: x = [[]] \n x:0
def case_index0__lle : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [(.listLiteral [])])])] [(.index (.resolve "x") (.num 0))])
#guard obs case_index0__lle == "ok raw=L[] n=1"

-- index0__l_e: x = [()] \n x:0
def case_index0__l_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [(.emptySequence 0)])])] [(.index (.resolve "x") (.num 0))])
#guard obs case_index0__l_e == "ok raw=S[] n=1"

-- index0__l_p12: x = [(1, 2)] \n x:0
def case_index0__l_p12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [(.capture [.num 1, .num 2])])])] [(.index (.resolve "x") (.num 0))])
#guard obs case_index0__l_p12 == "ok raw=S[1, 2] n=1"

-- index0__p_l12: x = ([1, 2], 3) \n x:0
def case_index0__p_l12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.listLiteral [.num 1, .num 2]), .num 3])])] [(.index (.resolve "x") (.num 0))])
#guard obs case_index0__p_l12 == "ok raw=L[1, 2] n=1"

-- index0__pl1: x = ([1]) \n x:0
def case_index0__pl1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [.num 1])])] [(.index (.resolve "x") (.num 0))])
#guard obs case_index0__pl1 == "ok raw=1 n=1"

-- index1__e: x = () \n x:1
def case_index1__e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.emptySequence 0)])] [(.index (.resolve "x") (.num 1))])
#guard obs case_index1__e == "err index"

-- index1__n0: x = 0 \n x:1
def case_index1__n0 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [.num 0])] [(.index (.resolve "x") (.num 1))])
#guard obs case_index1__n0 == "err index"

-- index1__n1: x = 1 \n x:1
def case_index1__n1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [.num 1])] [(.index (.resolve "x") (.num 1))])
#guard obs case_index1__n1 == "err index"

-- index1__bt: x = true \n x:1
def case_index1__bt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [.boolLiteral true])] [(.index (.resolve "x") (.num 1))])
#guard obs case_index1__bt == "err index"

-- index1__bf: x = false \n x:1
def case_index1__bf : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [.boolLiteral false])] [(.index (.resolve "x") (.num 1))])
#guard obs case_index1__bf == "err index"

-- index1__pbt: x = (true) \n x:1
def case_index1__pbt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [.boolLiteral true])] [(.index (.resolve "x") (.num 1))])
#guard obs case_index1__pbt == "err index"

-- index1__pbt_e: x = (true, ()) \n x:1
def case_index1__pbt_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [.boolLiteral true, (.emptySequence 0)])])] [(.index (.resolve "x") (.num 1))])
#guard obs case_index1__pbt_e == "ok raw=S[] n=1"

-- index1__pbt_1: x = (true, 1) \n x:1
def case_index1__pbt_1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [.boolLiteral true, .num 1])])] [(.index (.resolve "x") (.num 1))])
#guard obs case_index1__pbt_1 == "ok raw=1 n=1"

-- index1__lbt: x = [true] \n x:1
def case_index1__lbt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [.boolLiteral true])])] [(.index (.resolve "x") (.num 1))])
#guard obs case_index1__lbt == "err index"

-- index1__lbt_bf: x = [true, false] \n x:1
def case_index1__lbt_bf : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [.boolLiteral true, .boolLiteral false])])] [(.index (.resolve "x") (.num 1))])
#guard obs case_index1__lbt_bf == "ok raw=false n=1"

-- index1__lpbt_1: x = [(true, 1)] \n x:1
def case_index1__lpbt_1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [(.capture [.boolLiteral true, .num 1])])])] [(.index (.resolve "x") (.num 1))])
#guard obs case_index1__lpbt_1 == "err index"

-- index1__p1: x = (1) \n x:1
def case_index1__p1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [.num 1])] [(.index (.resolve "x") (.num 1))])
#guard obs case_index1__p1 == "err index"

-- index1__p12: x = (1, 2) \n x:1
def case_index1__p12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [.num 1, .num 2])])] [(.index (.resolve "x") (.num 1))])
#guard obs case_index1__p12 == "ok raw=2 n=1"

-- index1__p123: x = (1, 2, 3) \n x:1
def case_index1__p123 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [.num 1, .num 2, .num 3])])] [(.index (.resolve "x") (.num 1))])
#guard obs case_index1__p123 == "ok raw=2 n=1"

-- index1__pee: x = ((), ()) \n x:1
def case_index1__pee : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.emptySequence 0), (.emptySequence 0)])])] [(.index (.resolve "x") (.num 1))])
#guard obs case_index1__pee == "ok raw=S[] n=1"

-- index1__pe1: x = ((), 1) \n x:1
def case_index1__pe1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.emptySequence 0), .num 1])])] [(.index (.resolve "x") (.num 1))])
#guard obs case_index1__pe1 == "ok raw=1 n=1"

-- index1__p1e: x = (1, ()) \n x:1
def case_index1__p1e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [.num 1, (.emptySequence 0)])])] [(.index (.resolve "x") (.num 1))])
#guard obs case_index1__p1e == "ok raw=S[] n=1"

-- index1__p12_3: x = ((1, 2), 3) \n x:1
def case_index1__p12_3 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.capture [.num 1, .num 2]), .num 3])])] [(.index (.resolve "x") (.num 1))])
#guard obs case_index1__p12_3 == "ok raw=3 n=1"

-- index1__p12_34: x = ((1, 2), (3, 4)) \n x:1
def case_index1__p12_34 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.capture [.num 1, .num 2]), (.capture [.num 3, .num 4])])])] [(.index (.resolve "x") (.num 1))])
#guard obs case_index1__p12_34 == "ok raw=S[3, 4] n=1"

-- index1__pe_12: x = ((), (1, 2)) \n x:1
def case_index1__pe_12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.emptySequence 0), (.capture [.num 1, .num 2])])])] [(.index (.resolve "x") (.num 1))])
#guard obs case_index1__pe_12 == "ok raw=S[1, 2] n=1"

-- index1__ppe1_2: x = (((), 1), 2) \n x:1
def case_index1__ppe1_2 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.capture [(.emptySequence 0), .num 1]), .num 2])])] [(.index (.resolve "x") (.num 1))])
#guard obs case_index1__ppe1_2 == "ok raw=2 n=1"

-- index1__p12_e: x = ((1, 2), ()) \n x:1
def case_index1__p12_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.capture [.num 1, .num 2]), (.emptySequence 0)])])] [(.index (.resolve "x") (.num 1))])
#guard obs case_index1__p12_e == "ok raw=S[] n=1"

-- index1__ppe: x = (()) \n x:1
def case_index1__ppe : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.emptySequence 0)])] [(.index (.resolve "x") (.num 1))])
#guard obs case_index1__ppe == "err index"

-- index1__pp1: x = ((1)) \n x:1
def case_index1__pp1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [.num 1])] [(.index (.resolve "x") (.num 1))])
#guard obs case_index1__pp1 == "err index"

-- index1__ppp12: x = (((1, 2))) \n x:1
def case_index1__ppp12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [.num 1, .num 2])])] [(.index (.resolve "x") (.num 1))])
#guard obs case_index1__ppp12 == "ok raw=2 n=1"

-- index1__le: x = [] \n x:1
def case_index1__le : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [])])] [(.index (.resolve "x") (.num 1))])
#guard obs case_index1__le == "err index"

-- index1__l7: x = [7] \n x:1
def case_index1__l7 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [.num 7])])] [(.index (.resolve "x") (.num 1))])
#guard obs case_index1__l7 == "err index"

-- index1__l12: x = [1, 2] \n x:1
def case_index1__l12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [.num 1, .num 2])])] [(.index (.resolve "x") (.num 1))])
#guard obs case_index1__l12 == "ok raw=2 n=1"

-- index1__l12_3: x = [[1, 2], 3] \n x:1
def case_index1__l12_3 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [(.listLiteral [.num 1, .num 2]), .num 3])])] [(.index (.resolve "x") (.num 1))])
#guard obs case_index1__l12_3 == "ok raw=3 n=1"

-- index1__lle: x = [[]] \n x:1
def case_index1__lle : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [(.listLiteral [])])])] [(.index (.resolve "x") (.num 1))])
#guard obs case_index1__lle == "err index"

-- index1__l_e: x = [()] \n x:1
def case_index1__l_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [(.emptySequence 0)])])] [(.index (.resolve "x") (.num 1))])
#guard obs case_index1__l_e == "err index"

-- index1__l_p12: x = [(1, 2)] \n x:1
def case_index1__l_p12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [(.capture [.num 1, .num 2])])])] [(.index (.resolve "x") (.num 1))])
#guard obs case_index1__l_p12 == "err index"

-- index1__p_l12: x = ([1, 2], 3) \n x:1
def case_index1__p_l12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.listLiteral [.num 1, .num 2]), .num 3])])] [(.index (.resolve "x") (.num 1))])
#guard obs case_index1__p_l12 == "ok raw=3 n=1"

-- index1__pl1: x = ([1]) \n x:1
def case_index1__pl1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [.num 1])])] [(.index (.resolve "x") (.num 1))])
#guard obs case_index1__pl1 == "err index"

-- indexBig__e: x = () \n x:9
def case_indexBig__e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.emptySequence 0)])] [(.index (.resolve "x") (.num 9))])
#guard obs case_indexBig__e == "err index"

-- indexBig__n0: x = 0 \n x:9
def case_indexBig__n0 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [.num 0])] [(.index (.resolve "x") (.num 9))])
#guard obs case_indexBig__n0 == "err index"

-- indexBig__n1: x = 1 \n x:9
def case_indexBig__n1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [.num 1])] [(.index (.resolve "x") (.num 9))])
#guard obs case_indexBig__n1 == "err index"

-- indexBig__bt: x = true \n x:9
def case_indexBig__bt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [.boolLiteral true])] [(.index (.resolve "x") (.num 9))])
#guard obs case_indexBig__bt == "err index"

-- indexBig__bf: x = false \n x:9
def case_indexBig__bf : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [.boolLiteral false])] [(.index (.resolve "x") (.num 9))])
#guard obs case_indexBig__bf == "err index"

-- indexBig__pbt: x = (true) \n x:9
def case_indexBig__pbt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [.boolLiteral true])] [(.index (.resolve "x") (.num 9))])
#guard obs case_indexBig__pbt == "err index"

-- indexBig__pbt_e: x = (true, ()) \n x:9
def case_indexBig__pbt_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [.boolLiteral true, (.emptySequence 0)])])] [(.index (.resolve "x") (.num 9))])
#guard obs case_indexBig__pbt_e == "err index"

-- indexBig__pbt_1: x = (true, 1) \n x:9
def case_indexBig__pbt_1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [.boolLiteral true, .num 1])])] [(.index (.resolve "x") (.num 9))])
#guard obs case_indexBig__pbt_1 == "err index"

-- indexBig__lbt: x = [true] \n x:9
def case_indexBig__lbt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [.boolLiteral true])])] [(.index (.resolve "x") (.num 9))])
#guard obs case_indexBig__lbt == "err index"

-- indexBig__lbt_bf: x = [true, false] \n x:9
def case_indexBig__lbt_bf : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [.boolLiteral true, .boolLiteral false])])] [(.index (.resolve "x") (.num 9))])
#guard obs case_indexBig__lbt_bf == "err index"

-- indexBig__lpbt_1: x = [(true, 1)] \n x:9
def case_indexBig__lpbt_1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [(.capture [.boolLiteral true, .num 1])])])] [(.index (.resolve "x") (.num 9))])
#guard obs case_indexBig__lpbt_1 == "err index"

-- indexBig__p1: x = (1) \n x:9
def case_indexBig__p1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [.num 1])] [(.index (.resolve "x") (.num 9))])
#guard obs case_indexBig__p1 == "err index"

-- indexBig__p12: x = (1, 2) \n x:9
def case_indexBig__p12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [.num 1, .num 2])])] [(.index (.resolve "x") (.num 9))])
#guard obs case_indexBig__p12 == "err index"

-- indexBig__p123: x = (1, 2, 3) \n x:9
def case_indexBig__p123 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [.num 1, .num 2, .num 3])])] [(.index (.resolve "x") (.num 9))])
#guard obs case_indexBig__p123 == "err index"

-- indexBig__pee: x = ((), ()) \n x:9
def case_indexBig__pee : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.emptySequence 0), (.emptySequence 0)])])] [(.index (.resolve "x") (.num 9))])
#guard obs case_indexBig__pee == "err index"

-- indexBig__pe1: x = ((), 1) \n x:9
def case_indexBig__pe1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.emptySequence 0), .num 1])])] [(.index (.resolve "x") (.num 9))])
#guard obs case_indexBig__pe1 == "err index"

-- indexBig__p1e: x = (1, ()) \n x:9
def case_indexBig__p1e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [.num 1, (.emptySequence 0)])])] [(.index (.resolve "x") (.num 9))])
#guard obs case_indexBig__p1e == "err index"

-- indexBig__p12_3: x = ((1, 2), 3) \n x:9
def case_indexBig__p12_3 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.capture [.num 1, .num 2]), .num 3])])] [(.index (.resolve "x") (.num 9))])
#guard obs case_indexBig__p12_3 == "err index"

-- indexBig__p12_34: x = ((1, 2), (3, 4)) \n x:9
def case_indexBig__p12_34 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.capture [.num 1, .num 2]), (.capture [.num 3, .num 4])])])] [(.index (.resolve "x") (.num 9))])
#guard obs case_indexBig__p12_34 == "err index"

-- indexBig__pe_12: x = ((), (1, 2)) \n x:9
def case_indexBig__pe_12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.emptySequence 0), (.capture [.num 1, .num 2])])])] [(.index (.resolve "x") (.num 9))])
#guard obs case_indexBig__pe_12 == "err index"

-- indexBig__ppe1_2: x = (((), 1), 2) \n x:9
def case_indexBig__ppe1_2 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.capture [(.emptySequence 0), .num 1]), .num 2])])] [(.index (.resolve "x") (.num 9))])
#guard obs case_indexBig__ppe1_2 == "err index"

-- indexBig__p12_e: x = ((1, 2), ()) \n x:9
def case_indexBig__p12_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.capture [.num 1, .num 2]), (.emptySequence 0)])])] [(.index (.resolve "x") (.num 9))])
#guard obs case_indexBig__p12_e == "err index"

-- indexBig__ppe: x = (()) \n x:9
def case_indexBig__ppe : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.emptySequence 0)])] [(.index (.resolve "x") (.num 9))])
#guard obs case_indexBig__ppe == "err index"

-- indexBig__pp1: x = ((1)) \n x:9
def case_indexBig__pp1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [.num 1])] [(.index (.resolve "x") (.num 9))])
#guard obs case_indexBig__pp1 == "err index"

-- indexBig__ppp12: x = (((1, 2))) \n x:9
def case_indexBig__ppp12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [.num 1, .num 2])])] [(.index (.resolve "x") (.num 9))])
#guard obs case_indexBig__ppp12 == "err index"

-- indexBig__le: x = [] \n x:9
def case_indexBig__le : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [])])] [(.index (.resolve "x") (.num 9))])
#guard obs case_indexBig__le == "err index"

-- indexBig__l7: x = [7] \n x:9
def case_indexBig__l7 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [.num 7])])] [(.index (.resolve "x") (.num 9))])
#guard obs case_indexBig__l7 == "err index"

-- indexBig__l12: x = [1, 2] \n x:9
def case_indexBig__l12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [.num 1, .num 2])])] [(.index (.resolve "x") (.num 9))])
#guard obs case_indexBig__l12 == "err index"

-- indexBig__l12_3: x = [[1, 2], 3] \n x:9
def case_indexBig__l12_3 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [(.listLiteral [.num 1, .num 2]), .num 3])])] [(.index (.resolve "x") (.num 9))])
#guard obs case_indexBig__l12_3 == "err index"

-- indexBig__lle: x = [[]] \n x:9
def case_indexBig__lle : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [(.listLiteral [])])])] [(.index (.resolve "x") (.num 9))])
#guard obs case_indexBig__lle == "err index"

-- indexBig__l_e: x = [()] \n x:9
def case_indexBig__l_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [(.emptySequence 0)])])] [(.index (.resolve "x") (.num 9))])
#guard obs case_indexBig__l_e == "err index"

-- indexBig__l_p12: x = [(1, 2)] \n x:9
def case_indexBig__l_p12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [(.capture [.num 1, .num 2])])])] [(.index (.resolve "x") (.num 9))])
#guard obs case_indexBig__l_p12 == "err index"

-- indexBig__p_l12: x = ([1, 2], 3) \n x:9
def case_indexBig__p_l12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.listLiteral [.num 1, .num 2]), .num 3])])] [(.index (.resolve "x") (.num 9))])
#guard obs case_indexBig__p_l12 == "err index"

-- indexBig__pl1: x = ([1]) \n x:9
def case_indexBig__pl1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [.num 1])])] [(.index (.resolve "x") (.num 9))])
#guard obs case_indexBig__pl1 == "err index"

-- eqSelf__e: x = () \n x == x
def case_eqSelf__e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.emptySequence 0)])] [(.comparison (.resolve "x") [{ op := .eq, operand := (.resolve "x") }])])
#guard obs case_eqSelf__e == "ok raw=true n=1"

-- eqSelf__n0: x = 0 \n x == x
def case_eqSelf__n0 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [.num 0])] [(.comparison (.resolve "x") [{ op := .eq, operand := (.resolve "x") }])])
#guard obs case_eqSelf__n0 == "ok raw=true n=1"

-- eqSelf__n1: x = 1 \n x == x
def case_eqSelf__n1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [.num 1])] [(.comparison (.resolve "x") [{ op := .eq, operand := (.resolve "x") }])])
#guard obs case_eqSelf__n1 == "ok raw=true n=1"

-- eqSelf__bt: x = true \n x == x
def case_eqSelf__bt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [.boolLiteral true])] [(.comparison (.resolve "x") [{ op := .eq, operand := (.resolve "x") }])])
#guard obs case_eqSelf__bt == "ok raw=true n=1"

-- eqSelf__bf: x = false \n x == x
def case_eqSelf__bf : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [.boolLiteral false])] [(.comparison (.resolve "x") [{ op := .eq, operand := (.resolve "x") }])])
#guard obs case_eqSelf__bf == "ok raw=true n=1"

-- eqSelf__pbt: x = (true) \n x == x
def case_eqSelf__pbt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [.boolLiteral true])] [(.comparison (.resolve "x") [{ op := .eq, operand := (.resolve "x") }])])
#guard obs case_eqSelf__pbt == "ok raw=true n=1"

-- eqSelf__pbt_e: x = (true, ()) \n x == x
def case_eqSelf__pbt_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [.boolLiteral true, (.emptySequence 0)])])] [(.comparison (.resolve "x") [{ op := .eq, operand := (.resolve "x") }])])
#guard obs case_eqSelf__pbt_e == "ok raw=true n=1"

-- eqSelf__pbt_1: x = (true, 1) \n x == x
def case_eqSelf__pbt_1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [.boolLiteral true, .num 1])])] [(.comparison (.resolve "x") [{ op := .eq, operand := (.resolve "x") }])])
#guard obs case_eqSelf__pbt_1 == "ok raw=true n=1"

-- eqSelf__lbt: x = [true] \n x == x
def case_eqSelf__lbt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [.boolLiteral true])])] [(.comparison (.resolve "x") [{ op := .eq, operand := (.resolve "x") }])])
#guard obs case_eqSelf__lbt == "ok raw=true n=1"

-- eqSelf__lbt_bf: x = [true, false] \n x == x
def case_eqSelf__lbt_bf : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [.boolLiteral true, .boolLiteral false])])] [(.comparison (.resolve "x") [{ op := .eq, operand := (.resolve "x") }])])
#guard obs case_eqSelf__lbt_bf == "ok raw=true n=1"

-- eqSelf__lpbt_1: x = [(true, 1)] \n x == x
def case_eqSelf__lpbt_1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [(.capture [.boolLiteral true, .num 1])])])] [(.comparison (.resolve "x") [{ op := .eq, operand := (.resolve "x") }])])
#guard obs case_eqSelf__lpbt_1 == "ok raw=true n=1"

-- eqSelf__p1: x = (1) \n x == x
def case_eqSelf__p1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [.num 1])] [(.comparison (.resolve "x") [{ op := .eq, operand := (.resolve "x") }])])
#guard obs case_eqSelf__p1 == "ok raw=true n=1"

-- eqSelf__p12: x = (1, 2) \n x == x
def case_eqSelf__p12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [.num 1, .num 2])])] [(.comparison (.resolve "x") [{ op := .eq, operand := (.resolve "x") }])])
#guard obs case_eqSelf__p12 == "ok raw=true n=1"

-- eqSelf__p123: x = (1, 2, 3) \n x == x
def case_eqSelf__p123 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [.num 1, .num 2, .num 3])])] [(.comparison (.resolve "x") [{ op := .eq, operand := (.resolve "x") }])])
#guard obs case_eqSelf__p123 == "ok raw=true n=1"

-- eqSelf__pee: x = ((), ()) \n x == x
def case_eqSelf__pee : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.emptySequence 0), (.emptySequence 0)])])] [(.comparison (.resolve "x") [{ op := .eq, operand := (.resolve "x") }])])
#guard obs case_eqSelf__pee == "ok raw=true n=1"

-- eqSelf__pe1: x = ((), 1) \n x == x
def case_eqSelf__pe1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.emptySequence 0), .num 1])])] [(.comparison (.resolve "x") [{ op := .eq, operand := (.resolve "x") }])])
#guard obs case_eqSelf__pe1 == "ok raw=true n=1"

-- eqSelf__p1e: x = (1, ()) \n x == x
def case_eqSelf__p1e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [.num 1, (.emptySequence 0)])])] [(.comparison (.resolve "x") [{ op := .eq, operand := (.resolve "x") }])])
#guard obs case_eqSelf__p1e == "ok raw=true n=1"

-- eqSelf__p12_3: x = ((1, 2), 3) \n x == x
def case_eqSelf__p12_3 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.capture [.num 1, .num 2]), .num 3])])] [(.comparison (.resolve "x") [{ op := .eq, operand := (.resolve "x") }])])
#guard obs case_eqSelf__p12_3 == "ok raw=true n=1"

-- eqSelf__p12_34: x = ((1, 2), (3, 4)) \n x == x
def case_eqSelf__p12_34 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.capture [.num 1, .num 2]), (.capture [.num 3, .num 4])])])] [(.comparison (.resolve "x") [{ op := .eq, operand := (.resolve "x") }])])
#guard obs case_eqSelf__p12_34 == "ok raw=true n=1"

-- eqSelf__pe_12: x = ((), (1, 2)) \n x == x
def case_eqSelf__pe_12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.emptySequence 0), (.capture [.num 1, .num 2])])])] [(.comparison (.resolve "x") [{ op := .eq, operand := (.resolve "x") }])])
#guard obs case_eqSelf__pe_12 == "ok raw=true n=1"

-- eqSelf__ppe1_2: x = (((), 1), 2) \n x == x
def case_eqSelf__ppe1_2 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.capture [(.emptySequence 0), .num 1]), .num 2])])] [(.comparison (.resolve "x") [{ op := .eq, operand := (.resolve "x") }])])
#guard obs case_eqSelf__ppe1_2 == "ok raw=true n=1"

-- eqSelf__p12_e: x = ((1, 2), ()) \n x == x
def case_eqSelf__p12_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.capture [.num 1, .num 2]), (.emptySequence 0)])])] [(.comparison (.resolve "x") [{ op := .eq, operand := (.resolve "x") }])])
#guard obs case_eqSelf__p12_e == "ok raw=true n=1"

-- eqSelf__ppe: x = (()) \n x == x
def case_eqSelf__ppe : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.emptySequence 0)])] [(.comparison (.resolve "x") [{ op := .eq, operand := (.resolve "x") }])])
#guard obs case_eqSelf__ppe == "ok raw=true n=1"

-- eqSelf__pp1: x = ((1)) \n x == x
def case_eqSelf__pp1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [.num 1])] [(.comparison (.resolve "x") [{ op := .eq, operand := (.resolve "x") }])])
#guard obs case_eqSelf__pp1 == "ok raw=true n=1"

-- eqSelf__ppp12: x = (((1, 2))) \n x == x
def case_eqSelf__ppp12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [.num 1, .num 2])])] [(.comparison (.resolve "x") [{ op := .eq, operand := (.resolve "x") }])])
#guard obs case_eqSelf__ppp12 == "ok raw=true n=1"

-- eqSelf__le: x = [] \n x == x
def case_eqSelf__le : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [])])] [(.comparison (.resolve "x") [{ op := .eq, operand := (.resolve "x") }])])
#guard obs case_eqSelf__le == "ok raw=true n=1"

-- eqSelf__l7: x = [7] \n x == x
def case_eqSelf__l7 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [.num 7])])] [(.comparison (.resolve "x") [{ op := .eq, operand := (.resolve "x") }])])
#guard obs case_eqSelf__l7 == "ok raw=true n=1"

-- eqSelf__l12: x = [1, 2] \n x == x
def case_eqSelf__l12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [.num 1, .num 2])])] [(.comparison (.resolve "x") [{ op := .eq, operand := (.resolve "x") }])])
#guard obs case_eqSelf__l12 == "ok raw=true n=1"

-- eqSelf__l12_3: x = [[1, 2], 3] \n x == x
def case_eqSelf__l12_3 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [(.listLiteral [.num 1, .num 2]), .num 3])])] [(.comparison (.resolve "x") [{ op := .eq, operand := (.resolve "x") }])])
#guard obs case_eqSelf__l12_3 == "ok raw=true n=1"

-- eqSelf__lle: x = [[]] \n x == x
def case_eqSelf__lle : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [(.listLiteral [])])])] [(.comparison (.resolve "x") [{ op := .eq, operand := (.resolve "x") }])])
#guard obs case_eqSelf__lle == "ok raw=true n=1"

-- eqSelf__l_e: x = [()] \n x == x
def case_eqSelf__l_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [(.emptySequence 0)])])] [(.comparison (.resolve "x") [{ op := .eq, operand := (.resolve "x") }])])
#guard obs case_eqSelf__l_e == "ok raw=true n=1"

-- eqSelf__l_p12: x = [(1, 2)] \n x == x
def case_eqSelf__l_p12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [(.capture [.num 1, .num 2])])])] [(.comparison (.resolve "x") [{ op := .eq, operand := (.resolve "x") }])])
#guard obs case_eqSelf__l_p12 == "ok raw=true n=1"

-- eqSelf__p_l12: x = ([1, 2], 3) \n x == x
def case_eqSelf__p_l12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.listLiteral [.num 1, .num 2]), .num 3])])] [(.comparison (.resolve "x") [{ op := .eq, operand := (.resolve "x") }])])
#guard obs case_eqSelf__p_l12 == "ok raw=true n=1"

-- eqSelf__pl1: x = ([1]) \n x == x
def case_eqSelf__pl1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [.num 1])])] [(.comparison (.resolve "x") [{ op := .eq, operand := (.resolve "x") }])])
#guard obs case_eqSelf__pl1 == "ok raw=true n=1"

-- neqSelf__e: x = () \n x != x
def case_neqSelf__e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.emptySequence 0)])] [(.comparison (.resolve "x") [{ op := .ne, operand := (.resolve "x") }])])
#guard obs case_neqSelf__e == "ok raw=false n=1"

-- neqSelf__n0: x = 0 \n x != x
def case_neqSelf__n0 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [.num 0])] [(.comparison (.resolve "x") [{ op := .ne, operand := (.resolve "x") }])])
#guard obs case_neqSelf__n0 == "ok raw=false n=1"

-- neqSelf__n1: x = 1 \n x != x
def case_neqSelf__n1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [.num 1])] [(.comparison (.resolve "x") [{ op := .ne, operand := (.resolve "x") }])])
#guard obs case_neqSelf__n1 == "ok raw=false n=1"

-- neqSelf__bt: x = true \n x != x
def case_neqSelf__bt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [.boolLiteral true])] [(.comparison (.resolve "x") [{ op := .ne, operand := (.resolve "x") }])])
#guard obs case_neqSelf__bt == "ok raw=false n=1"

-- neqSelf__bf: x = false \n x != x
def case_neqSelf__bf : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [.boolLiteral false])] [(.comparison (.resolve "x") [{ op := .ne, operand := (.resolve "x") }])])
#guard obs case_neqSelf__bf == "ok raw=false n=1"

-- neqSelf__pbt: x = (true) \n x != x
def case_neqSelf__pbt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [.boolLiteral true])] [(.comparison (.resolve "x") [{ op := .ne, operand := (.resolve "x") }])])
#guard obs case_neqSelf__pbt == "ok raw=false n=1"

-- neqSelf__pbt_e: x = (true, ()) \n x != x
def case_neqSelf__pbt_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [.boolLiteral true, (.emptySequence 0)])])] [(.comparison (.resolve "x") [{ op := .ne, operand := (.resolve "x") }])])
#guard obs case_neqSelf__pbt_e == "ok raw=false n=1"

-- neqSelf__pbt_1: x = (true, 1) \n x != x
def case_neqSelf__pbt_1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [.boolLiteral true, .num 1])])] [(.comparison (.resolve "x") [{ op := .ne, operand := (.resolve "x") }])])
#guard obs case_neqSelf__pbt_1 == "ok raw=false n=1"

-- neqSelf__lbt: x = [true] \n x != x
def case_neqSelf__lbt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [.boolLiteral true])])] [(.comparison (.resolve "x") [{ op := .ne, operand := (.resolve "x") }])])
#guard obs case_neqSelf__lbt == "ok raw=false n=1"

-- neqSelf__lbt_bf: x = [true, false] \n x != x
def case_neqSelf__lbt_bf : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [.boolLiteral true, .boolLiteral false])])] [(.comparison (.resolve "x") [{ op := .ne, operand := (.resolve "x") }])])
#guard obs case_neqSelf__lbt_bf == "ok raw=false n=1"

-- neqSelf__lpbt_1: x = [(true, 1)] \n x != x
def case_neqSelf__lpbt_1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [(.capture [.boolLiteral true, .num 1])])])] [(.comparison (.resolve "x") [{ op := .ne, operand := (.resolve "x") }])])
#guard obs case_neqSelf__lpbt_1 == "ok raw=false n=1"

-- neqSelf__p1: x = (1) \n x != x
def case_neqSelf__p1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [.num 1])] [(.comparison (.resolve "x") [{ op := .ne, operand := (.resolve "x") }])])
#guard obs case_neqSelf__p1 == "ok raw=false n=1"

-- neqSelf__p12: x = (1, 2) \n x != x
def case_neqSelf__p12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [.num 1, .num 2])])] [(.comparison (.resolve "x") [{ op := .ne, operand := (.resolve "x") }])])
#guard obs case_neqSelf__p12 == "ok raw=false n=1"

-- neqSelf__p123: x = (1, 2, 3) \n x != x
def case_neqSelf__p123 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [.num 1, .num 2, .num 3])])] [(.comparison (.resolve "x") [{ op := .ne, operand := (.resolve "x") }])])
#guard obs case_neqSelf__p123 == "ok raw=false n=1"

-- neqSelf__pee: x = ((), ()) \n x != x
def case_neqSelf__pee : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.emptySequence 0), (.emptySequence 0)])])] [(.comparison (.resolve "x") [{ op := .ne, operand := (.resolve "x") }])])
#guard obs case_neqSelf__pee == "ok raw=false n=1"

-- neqSelf__pe1: x = ((), 1) \n x != x
def case_neqSelf__pe1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.emptySequence 0), .num 1])])] [(.comparison (.resolve "x") [{ op := .ne, operand := (.resolve "x") }])])
#guard obs case_neqSelf__pe1 == "ok raw=false n=1"

-- neqSelf__p1e: x = (1, ()) \n x != x
def case_neqSelf__p1e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [.num 1, (.emptySequence 0)])])] [(.comparison (.resolve "x") [{ op := .ne, operand := (.resolve "x") }])])
#guard obs case_neqSelf__p1e == "ok raw=false n=1"

-- neqSelf__p12_3: x = ((1, 2), 3) \n x != x
def case_neqSelf__p12_3 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.capture [.num 1, .num 2]), .num 3])])] [(.comparison (.resolve "x") [{ op := .ne, operand := (.resolve "x") }])])
#guard obs case_neqSelf__p12_3 == "ok raw=false n=1"

-- neqSelf__p12_34: x = ((1, 2), (3, 4)) \n x != x
def case_neqSelf__p12_34 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.capture [.num 1, .num 2]), (.capture [.num 3, .num 4])])])] [(.comparison (.resolve "x") [{ op := .ne, operand := (.resolve "x") }])])
#guard obs case_neqSelf__p12_34 == "ok raw=false n=1"

-- neqSelf__pe_12: x = ((), (1, 2)) \n x != x
def case_neqSelf__pe_12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.emptySequence 0), (.capture [.num 1, .num 2])])])] [(.comparison (.resolve "x") [{ op := .ne, operand := (.resolve "x") }])])
#guard obs case_neqSelf__pe_12 == "ok raw=false n=1"

-- neqSelf__ppe1_2: x = (((), 1), 2) \n x != x
def case_neqSelf__ppe1_2 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.capture [(.emptySequence 0), .num 1]), .num 2])])] [(.comparison (.resolve "x") [{ op := .ne, operand := (.resolve "x") }])])
#guard obs case_neqSelf__ppe1_2 == "ok raw=false n=1"

-- neqSelf__p12_e: x = ((1, 2), ()) \n x != x
def case_neqSelf__p12_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.capture [.num 1, .num 2]), (.emptySequence 0)])])] [(.comparison (.resolve "x") [{ op := .ne, operand := (.resolve "x") }])])
#guard obs case_neqSelf__p12_e == "ok raw=false n=1"

-- neqSelf__ppe: x = (()) \n x != x
def case_neqSelf__ppe : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.emptySequence 0)])] [(.comparison (.resolve "x") [{ op := .ne, operand := (.resolve "x") }])])
#guard obs case_neqSelf__ppe == "ok raw=false n=1"

-- neqSelf__pp1: x = ((1)) \n x != x
def case_neqSelf__pp1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [.num 1])] [(.comparison (.resolve "x") [{ op := .ne, operand := (.resolve "x") }])])
#guard obs case_neqSelf__pp1 == "ok raw=false n=1"

-- neqSelf__ppp12: x = (((1, 2))) \n x != x
def case_neqSelf__ppp12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [.num 1, .num 2])])] [(.comparison (.resolve "x") [{ op := .ne, operand := (.resolve "x") }])])
#guard obs case_neqSelf__ppp12 == "ok raw=false n=1"

-- neqSelf__le: x = [] \n x != x
def case_neqSelf__le : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [])])] [(.comparison (.resolve "x") [{ op := .ne, operand := (.resolve "x") }])])
#guard obs case_neqSelf__le == "ok raw=false n=1"

-- neqSelf__l7: x = [7] \n x != x
def case_neqSelf__l7 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [.num 7])])] [(.comparison (.resolve "x") [{ op := .ne, operand := (.resolve "x") }])])
#guard obs case_neqSelf__l7 == "ok raw=false n=1"

-- neqSelf__l12: x = [1, 2] \n x != x
def case_neqSelf__l12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [.num 1, .num 2])])] [(.comparison (.resolve "x") [{ op := .ne, operand := (.resolve "x") }])])
#guard obs case_neqSelf__l12 == "ok raw=false n=1"

-- neqSelf__l12_3: x = [[1, 2], 3] \n x != x
def case_neqSelf__l12_3 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [(.listLiteral [.num 1, .num 2]), .num 3])])] [(.comparison (.resolve "x") [{ op := .ne, operand := (.resolve "x") }])])
#guard obs case_neqSelf__l12_3 == "ok raw=false n=1"

-- neqSelf__lle: x = [[]] \n x != x
def case_neqSelf__lle : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [(.listLiteral [])])])] [(.comparison (.resolve "x") [{ op := .ne, operand := (.resolve "x") }])])
#guard obs case_neqSelf__lle == "ok raw=false n=1"

-- neqSelf__l_e: x = [()] \n x != x
def case_neqSelf__l_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [(.emptySequence 0)])])] [(.comparison (.resolve "x") [{ op := .ne, operand := (.resolve "x") }])])
#guard obs case_neqSelf__l_e == "ok raw=false n=1"

-- neqSelf__l_p12: x = [(1, 2)] \n x != x
def case_neqSelf__l_p12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [(.capture [.num 1, .num 2])])])] [(.comparison (.resolve "x") [{ op := .ne, operand := (.resolve "x") }])])
#guard obs case_neqSelf__l_p12 == "ok raw=false n=1"

-- neqSelf__p_l12: x = ([1, 2], 3) \n x != x
def case_neqSelf__p_l12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.listLiteral [.num 1, .num 2]), .num 3])])] [(.comparison (.resolve "x") [{ op := .ne, operand := (.resolve "x") }])])
#guard obs case_neqSelf__p_l12 == "ok raw=false n=1"

-- neqSelf__pl1: x = ([1]) \n x != x
def case_neqSelf__pl1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [.num 1])])] [(.comparison (.resolve "x") [{ op := .ne, operand := (.resolve "x") }])])
#guard obs case_neqSelf__pl1 == "ok raw=false n=1"

-- eqIdentity__e: I(a) = a \n x = () \n x == I(x)
def case_eqIdentity__e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.emptySequence 0)]), privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.comparison (.resolve "x") [{ op := .eq, operand := (.call (.resolve "I") [.resolve "x"]) }])])
#guard obs case_eqIdentity__e == "ok raw=true n=1"

-- eqIdentity__n0: I(a) = a \n x = 0 \n x == I(x)
def case_eqIdentity__n0 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [.num 0]), privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.comparison (.resolve "x") [{ op := .eq, operand := (.call (.resolve "I") [.resolve "x"]) }])])
#guard obs case_eqIdentity__n0 == "ok raw=true n=1"

-- eqIdentity__n1: I(a) = a \n x = 1 \n x == I(x)
def case_eqIdentity__n1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [.num 1]), privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.comparison (.resolve "x") [{ op := .eq, operand := (.call (.resolve "I") [.resolve "x"]) }])])
#guard obs case_eqIdentity__n1 == "ok raw=true n=1"

-- eqIdentity__bt: I(a) = a \n x = true \n x == I(x)
def case_eqIdentity__bt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [.boolLiteral true]), privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.comparison (.resolve "x") [{ op := .eq, operand := (.call (.resolve "I") [.resolve "x"]) }])])
#guard obs case_eqIdentity__bt == "ok raw=true n=1"

-- eqIdentity__bf: I(a) = a \n x = false \n x == I(x)
def case_eqIdentity__bf : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [.boolLiteral false]), privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.comparison (.resolve "x") [{ op := .eq, operand := (.call (.resolve "I") [.resolve "x"]) }])])
#guard obs case_eqIdentity__bf == "ok raw=true n=1"

-- eqIdentity__pbt: I(a) = a \n x = (true) \n x == I(x)
def case_eqIdentity__pbt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [.boolLiteral true]), privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.comparison (.resolve "x") [{ op := .eq, operand := (.call (.resolve "I") [.resolve "x"]) }])])
#guard obs case_eqIdentity__pbt == "ok raw=true n=1"

-- eqIdentity__pbt_e: I(a) = a \n x = (true, ()) \n x == I(x)
def case_eqIdentity__pbt_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [.boolLiteral true, (.emptySequence 0)])]), privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.comparison (.resolve "x") [{ op := .eq, operand := (.call (.resolve "I") [.resolve "x"]) }])])
#guard obs case_eqIdentity__pbt_e == "ok raw=true n=1"

-- eqIdentity__pbt_1: I(a) = a \n x = (true, 1) \n x == I(x)
def case_eqIdentity__pbt_1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [.boolLiteral true, .num 1])]), privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.comparison (.resolve "x") [{ op := .eq, operand := (.call (.resolve "I") [.resolve "x"]) }])])
#guard obs case_eqIdentity__pbt_1 == "ok raw=true n=1"

-- eqIdentity__lbt: I(a) = a \n x = [true] \n x == I(x)
def case_eqIdentity__lbt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [.boolLiteral true])]), privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.comparison (.resolve "x") [{ op := .eq, operand := (.call (.resolve "I") [.resolve "x"]) }])])
#guard obs case_eqIdentity__lbt == "ok raw=true n=1"

-- eqIdentity__lbt_bf: I(a) = a \n x = [true, false] \n x == I(x)
def case_eqIdentity__lbt_bf : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [.boolLiteral true, .boolLiteral false])]), privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.comparison (.resolve "x") [{ op := .eq, operand := (.call (.resolve "I") [.resolve "x"]) }])])
#guard obs case_eqIdentity__lbt_bf == "ok raw=true n=1"

-- eqIdentity__lpbt_1: I(a) = a \n x = [(true, 1)] \n x == I(x)
def case_eqIdentity__lpbt_1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [(.capture [.boolLiteral true, .num 1])])]), privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.comparison (.resolve "x") [{ op := .eq, operand := (.call (.resolve "I") [.resolve "x"]) }])])
#guard obs case_eqIdentity__lpbt_1 == "ok raw=true n=1"

-- eqIdentity__p1: I(a) = a \n x = (1) \n x == I(x)
def case_eqIdentity__p1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [.num 1]), privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.comparison (.resolve "x") [{ op := .eq, operand := (.call (.resolve "I") [.resolve "x"]) }])])
#guard obs case_eqIdentity__p1 == "ok raw=true n=1"

-- eqIdentity__p12: I(a) = a \n x = (1, 2) \n x == I(x)
def case_eqIdentity__p12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [.num 1, .num 2])]), privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.comparison (.resolve "x") [{ op := .eq, operand := (.call (.resolve "I") [.resolve "x"]) }])])
#guard obs case_eqIdentity__p12 == "ok raw=true n=1"

-- eqIdentity__p123: I(a) = a \n x = (1, 2, 3) \n x == I(x)
def case_eqIdentity__p123 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [.num 1, .num 2, .num 3])]), privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.comparison (.resolve "x") [{ op := .eq, operand := (.call (.resolve "I") [.resolve "x"]) }])])
#guard obs case_eqIdentity__p123 == "ok raw=true n=1"

-- eqIdentity__pee: I(a) = a \n x = ((), ()) \n x == I(x)
def case_eqIdentity__pee : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.emptySequence 0), (.emptySequence 0)])]), privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.comparison (.resolve "x") [{ op := .eq, operand := (.call (.resolve "I") [.resolve "x"]) }])])
#guard obs case_eqIdentity__pee == "ok raw=true n=1"

-- eqIdentity__pe1: I(a) = a \n x = ((), 1) \n x == I(x)
def case_eqIdentity__pe1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.emptySequence 0), .num 1])]), privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.comparison (.resolve "x") [{ op := .eq, operand := (.call (.resolve "I") [.resolve "x"]) }])])
#guard obs case_eqIdentity__pe1 == "ok raw=true n=1"

-- eqIdentity__p1e: I(a) = a \n x = (1, ()) \n x == I(x)
def case_eqIdentity__p1e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [.num 1, (.emptySequence 0)])]), privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.comparison (.resolve "x") [{ op := .eq, operand := (.call (.resolve "I") [.resolve "x"]) }])])
#guard obs case_eqIdentity__p1e == "ok raw=true n=1"

-- eqIdentity__p12_3: I(a) = a \n x = ((1, 2), 3) \n x == I(x)
def case_eqIdentity__p12_3 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.capture [.num 1, .num 2]), .num 3])]), privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.comparison (.resolve "x") [{ op := .eq, operand := (.call (.resolve "I") [.resolve "x"]) }])])
#guard obs case_eqIdentity__p12_3 == "ok raw=true n=1"

-- eqIdentity__p12_34: I(a) = a \n x = ((1, 2), (3, 4)) \n x == I(x)
def case_eqIdentity__p12_34 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.capture [.num 1, .num 2]), (.capture [.num 3, .num 4])])]), privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.comparison (.resolve "x") [{ op := .eq, operand := (.call (.resolve "I") [.resolve "x"]) }])])
#guard obs case_eqIdentity__p12_34 == "ok raw=true n=1"

-- eqIdentity__pe_12: I(a) = a \n x = ((), (1, 2)) \n x == I(x)
def case_eqIdentity__pe_12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.emptySequence 0), (.capture [.num 1, .num 2])])]), privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.comparison (.resolve "x") [{ op := .eq, operand := (.call (.resolve "I") [.resolve "x"]) }])])
#guard obs case_eqIdentity__pe_12 == "ok raw=true n=1"

-- eqIdentity__ppe1_2: I(a) = a \n x = (((), 1), 2) \n x == I(x)
def case_eqIdentity__ppe1_2 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.capture [(.emptySequence 0), .num 1]), .num 2])]), privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.comparison (.resolve "x") [{ op := .eq, operand := (.call (.resolve "I") [.resolve "x"]) }])])
#guard obs case_eqIdentity__ppe1_2 == "ok raw=true n=1"

-- eqIdentity__p12_e: I(a) = a \n x = ((1, 2), ()) \n x == I(x)
def case_eqIdentity__p12_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.capture [.num 1, .num 2]), (.emptySequence 0)])]), privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.comparison (.resolve "x") [{ op := .eq, operand := (.call (.resolve "I") [.resolve "x"]) }])])
#guard obs case_eqIdentity__p12_e == "ok raw=true n=1"

-- eqIdentity__ppe: I(a) = a \n x = (()) \n x == I(x)
def case_eqIdentity__ppe : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.emptySequence 0)]), privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.comparison (.resolve "x") [{ op := .eq, operand := (.call (.resolve "I") [.resolve "x"]) }])])
#guard obs case_eqIdentity__ppe == "ok raw=true n=1"

-- eqIdentity__pp1: I(a) = a \n x = ((1)) \n x == I(x)
def case_eqIdentity__pp1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [.num 1]), privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.comparison (.resolve "x") [{ op := .eq, operand := (.call (.resolve "I") [.resolve "x"]) }])])
#guard obs case_eqIdentity__pp1 == "ok raw=true n=1"

-- eqIdentity__ppp12: I(a) = a \n x = (((1, 2))) \n x == I(x)
def case_eqIdentity__ppp12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [.num 1, .num 2])]), privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.comparison (.resolve "x") [{ op := .eq, operand := (.call (.resolve "I") [.resolve "x"]) }])])
#guard obs case_eqIdentity__ppp12 == "ok raw=true n=1"

-- eqIdentity__le: I(a) = a \n x = [] \n x == I(x)
def case_eqIdentity__le : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [])]), privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.comparison (.resolve "x") [{ op := .eq, operand := (.call (.resolve "I") [.resolve "x"]) }])])
#guard obs case_eqIdentity__le == "ok raw=true n=1"

-- eqIdentity__l7: I(a) = a \n x = [7] \n x == I(x)
def case_eqIdentity__l7 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [.num 7])]), privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.comparison (.resolve "x") [{ op := .eq, operand := (.call (.resolve "I") [.resolve "x"]) }])])
#guard obs case_eqIdentity__l7 == "ok raw=true n=1"

-- eqIdentity__l12: I(a) = a \n x = [1, 2] \n x == I(x)
def case_eqIdentity__l12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [.num 1, .num 2])]), privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.comparison (.resolve "x") [{ op := .eq, operand := (.call (.resolve "I") [.resolve "x"]) }])])
#guard obs case_eqIdentity__l12 == "ok raw=true n=1"

-- eqIdentity__l12_3: I(a) = a \n x = [[1, 2], 3] \n x == I(x)
def case_eqIdentity__l12_3 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [(.listLiteral [.num 1, .num 2]), .num 3])]), privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.comparison (.resolve "x") [{ op := .eq, operand := (.call (.resolve "I") [.resolve "x"]) }])])
#guard obs case_eqIdentity__l12_3 == "ok raw=true n=1"

-- eqIdentity__lle: I(a) = a \n x = [[]] \n x == I(x)
def case_eqIdentity__lle : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [(.listLiteral [])])]), privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.comparison (.resolve "x") [{ op := .eq, operand := (.call (.resolve "I") [.resolve "x"]) }])])
#guard obs case_eqIdentity__lle == "ok raw=true n=1"

-- eqIdentity__l_e: I(a) = a \n x = [()] \n x == I(x)
def case_eqIdentity__l_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [(.emptySequence 0)])]), privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.comparison (.resolve "x") [{ op := .eq, operand := (.call (.resolve "I") [.resolve "x"]) }])])
#guard obs case_eqIdentity__l_e == "ok raw=true n=1"

-- eqIdentity__l_p12: I(a) = a \n x = [(1, 2)] \n x == I(x)
def case_eqIdentity__l_p12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [(.capture [.num 1, .num 2])])]), privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.comparison (.resolve "x") [{ op := .eq, operand := (.call (.resolve "I") [.resolve "x"]) }])])
#guard obs case_eqIdentity__l_p12 == "ok raw=true n=1"

-- eqIdentity__p_l12: I(a) = a \n x = ([1, 2], 3) \n x == I(x)
def case_eqIdentity__p_l12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.listLiteral [.num 1, .num 2]), .num 3])]), privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.comparison (.resolve "x") [{ op := .eq, operand := (.call (.resolve "I") [.resolve "x"]) }])])
#guard obs case_eqIdentity__p_l12 == "ok raw=true n=1"

-- eqIdentity__pl1: I(a) = a \n x = ([1]) \n x == I(x)
def case_eqIdentity__pl1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [.num 1])]), privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.comparison (.resolve "x") [{ op := .eq, operand := (.call (.resolve "I") [.resolve "x"]) }])])
#guard obs case_eqIdentity__pl1 == "ok raw=true n=1"

-- identity__e: I(a) = a \n x = () \n I(x)
def case_identity__e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.emptySequence 0)]), privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "I") [.resolve "x"])])
#guard obs case_identity__e == "ok raw=S[] n=1"

-- identity__n0: I(a) = a \n x = 0 \n I(x)
def case_identity__n0 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [.num 0]), privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "I") [.resolve "x"])])
#guard obs case_identity__n0 == "ok raw=0 n=1"

-- identity__n1: I(a) = a \n x = 1 \n I(x)
def case_identity__n1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [.num 1]), privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "I") [.resolve "x"])])
#guard obs case_identity__n1 == "ok raw=1 n=1"

-- identity__bt: I(a) = a \n x = true \n I(x)
def case_identity__bt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [.boolLiteral true]), privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "I") [.resolve "x"])])
#guard obs case_identity__bt == "ok raw=true n=1"

-- identity__bf: I(a) = a \n x = false \n I(x)
def case_identity__bf : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [.boolLiteral false]), privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "I") [.resolve "x"])])
#guard obs case_identity__bf == "ok raw=false n=1"

-- identity__pbt: I(a) = a \n x = (true) \n I(x)
def case_identity__pbt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [.boolLiteral true]), privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "I") [.resolve "x"])])
#guard obs case_identity__pbt == "ok raw=true n=1"

-- identity__pbt_e: I(a) = a \n x = (true, ()) \n I(x)
def case_identity__pbt_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [.boolLiteral true, (.emptySequence 0)])]), privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "I") [.resolve "x"])])
#guard obs case_identity__pbt_e == "ok raw=S[true, S[]] n=1"

-- identity__pbt_1: I(a) = a \n x = (true, 1) \n I(x)
def case_identity__pbt_1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [.boolLiteral true, .num 1])]), privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "I") [.resolve "x"])])
#guard obs case_identity__pbt_1 == "ok raw=S[true, 1] n=1"

-- identity__lbt: I(a) = a \n x = [true] \n I(x)
def case_identity__lbt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [.boolLiteral true])]), privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "I") [.resolve "x"])])
#guard obs case_identity__lbt == "ok raw=L[true] n=1"

-- identity__lbt_bf: I(a) = a \n x = [true, false] \n I(x)
def case_identity__lbt_bf : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [.boolLiteral true, .boolLiteral false])]), privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "I") [.resolve "x"])])
#guard obs case_identity__lbt_bf == "ok raw=L[true, false] n=1"

-- identity__lpbt_1: I(a) = a \n x = [(true, 1)] \n I(x)
def case_identity__lpbt_1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [(.capture [.boolLiteral true, .num 1])])]), privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "I") [.resolve "x"])])
#guard obs case_identity__lpbt_1 == "ok raw=L[S[true, 1]] n=1"

-- identity__p1: I(a) = a \n x = (1) \n I(x)
def case_identity__p1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [.num 1]), privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "I") [.resolve "x"])])
#guard obs case_identity__p1 == "ok raw=1 n=1"

-- identity__p12: I(a) = a \n x = (1, 2) \n I(x)
def case_identity__p12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [.num 1, .num 2])]), privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "I") [.resolve "x"])])
#guard obs case_identity__p12 == "ok raw=S[1, 2] n=1"

-- identity__p123: I(a) = a \n x = (1, 2, 3) \n I(x)
def case_identity__p123 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [.num 1, .num 2, .num 3])]), privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "I") [.resolve "x"])])
#guard obs case_identity__p123 == "ok raw=S[1, 2, 3] n=1"

-- identity__pee: I(a) = a \n x = ((), ()) \n I(x)
def case_identity__pee : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.emptySequence 0), (.emptySequence 0)])]), privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "I") [.resolve "x"])])
#guard obs case_identity__pee == "ok raw=S[S[], S[]] n=1"

-- identity__pe1: I(a) = a \n x = ((), 1) \n I(x)
def case_identity__pe1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.emptySequence 0), .num 1])]), privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "I") [.resolve "x"])])
#guard obs case_identity__pe1 == "ok raw=S[S[], 1] n=1"

-- identity__p1e: I(a) = a \n x = (1, ()) \n I(x)
def case_identity__p1e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [.num 1, (.emptySequence 0)])]), privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "I") [.resolve "x"])])
#guard obs case_identity__p1e == "ok raw=S[1, S[]] n=1"

-- identity__p12_3: I(a) = a \n x = ((1, 2), 3) \n I(x)
def case_identity__p12_3 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.capture [.num 1, .num 2]), .num 3])]), privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "I") [.resolve "x"])])
#guard obs case_identity__p12_3 == "ok raw=S[S[1, 2], 3] n=1"

-- identity__p12_34: I(a) = a \n x = ((1, 2), (3, 4)) \n I(x)
def case_identity__p12_34 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.capture [.num 1, .num 2]), (.capture [.num 3, .num 4])])]), privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "I") [.resolve "x"])])
#guard obs case_identity__p12_34 == "ok raw=S[S[1, 2], S[3, 4]] n=1"

-- identity__pe_12: I(a) = a \n x = ((), (1, 2)) \n I(x)
def case_identity__pe_12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.emptySequence 0), (.capture [.num 1, .num 2])])]), privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "I") [.resolve "x"])])
#guard obs case_identity__pe_12 == "ok raw=S[S[], S[1, 2]] n=1"

-- identity__ppe1_2: I(a) = a \n x = (((), 1), 2) \n I(x)
def case_identity__ppe1_2 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.capture [(.emptySequence 0), .num 1]), .num 2])]), privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "I") [.resolve "x"])])
#guard obs case_identity__ppe1_2 == "ok raw=S[S[S[], 1], 2] n=1"

-- identity__p12_e: I(a) = a \n x = ((1, 2), ()) \n I(x)
def case_identity__p12_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.capture [.num 1, .num 2]), (.emptySequence 0)])]), privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "I") [.resolve "x"])])
#guard obs case_identity__p12_e == "ok raw=S[S[1, 2], S[]] n=1"

-- identity__ppe: I(a) = a \n x = (()) \n I(x)
def case_identity__ppe : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.emptySequence 0)]), privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "I") [.resolve "x"])])
#guard obs case_identity__ppe == "ok raw=S[] n=1"

-- identity__pp1: I(a) = a \n x = ((1)) \n I(x)
def case_identity__pp1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [.num 1]), privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "I") [.resolve "x"])])
#guard obs case_identity__pp1 == "ok raw=1 n=1"

-- identity__ppp12: I(a) = a \n x = (((1, 2))) \n I(x)
def case_identity__ppp12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [.num 1, .num 2])]), privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "I") [.resolve "x"])])
#guard obs case_identity__ppp12 == "ok raw=S[1, 2] n=1"

-- identity__le: I(a) = a \n x = [] \n I(x)
def case_identity__le : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [])]), privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "I") [.resolve "x"])])
#guard obs case_identity__le == "ok raw=L[] n=1"

-- identity__l7: I(a) = a \n x = [7] \n I(x)
def case_identity__l7 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [.num 7])]), privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "I") [.resolve "x"])])
#guard obs case_identity__l7 == "ok raw=L[7] n=1"

-- identity__l12: I(a) = a \n x = [1, 2] \n I(x)
def case_identity__l12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [.num 1, .num 2])]), privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "I") [.resolve "x"])])
#guard obs case_identity__l12 == "ok raw=L[1, 2] n=1"

-- identity__l12_3: I(a) = a \n x = [[1, 2], 3] \n I(x)
def case_identity__l12_3 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [(.listLiteral [.num 1, .num 2]), .num 3])]), privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "I") [.resolve "x"])])
#guard obs case_identity__l12_3 == "ok raw=L[L[1, 2], 3] n=1"

-- identity__lle: I(a) = a \n x = [[]] \n I(x)
def case_identity__lle : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [(.listLiteral [])])]), privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "I") [.resolve "x"])])
#guard obs case_identity__lle == "ok raw=L[L[]] n=1"

-- identity__l_e: I(a) = a \n x = [()] \n I(x)
def case_identity__l_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [(.emptySequence 0)])]), privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "I") [.resolve "x"])])
#guard obs case_identity__l_e == "ok raw=L[S[]] n=1"

-- identity__l_p12: I(a) = a \n x = [(1, 2)] \n I(x)
def case_identity__l_p12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [(.capture [.num 1, .num 2])])]), privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "I") [.resolve "x"])])
#guard obs case_identity__l_p12 == "ok raw=L[S[1, 2]] n=1"

-- identity__p_l12: I(a) = a \n x = ([1, 2], 3) \n I(x)
def case_identity__p_l12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.listLiteral [.num 1, .num 2]), .num 3])]), privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "I") [.resolve "x"])])
#guard obs case_identity__p_l12 == "ok raw=S[L[1, 2], 3] n=1"

-- identity__pl1: I(a) = a \n x = ([1]) \n I(x)
def case_identity__pl1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [.num 1])]), privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "I") [.resolve "x"])])
#guard obs case_identity__pl1 == "ok raw=L[1] n=1"

-- identityTwice__e: I(a) = a \n x = () \n I(I(x))
def case_identityTwice__e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.emptySequence 0)]), privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "I") [(.call (.resolve "I") [.resolve "x"])])])
#guard obs case_identityTwice__e == "ok raw=S[] n=1"

-- identityTwice__n0: I(a) = a \n x = 0 \n I(I(x))
def case_identityTwice__n0 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [.num 0]), privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "I") [(.call (.resolve "I") [.resolve "x"])])])
#guard obs case_identityTwice__n0 == "ok raw=0 n=1"

-- identityTwice__n1: I(a) = a \n x = 1 \n I(I(x))
def case_identityTwice__n1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [.num 1]), privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "I") [(.call (.resolve "I") [.resolve "x"])])])
#guard obs case_identityTwice__n1 == "ok raw=1 n=1"

-- identityTwice__bt: I(a) = a \n x = true \n I(I(x))
def case_identityTwice__bt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [.boolLiteral true]), privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "I") [(.call (.resolve "I") [.resolve "x"])])])
#guard obs case_identityTwice__bt == "ok raw=true n=1"

-- identityTwice__bf: I(a) = a \n x = false \n I(I(x))
def case_identityTwice__bf : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [.boolLiteral false]), privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "I") [(.call (.resolve "I") [.resolve "x"])])])
#guard obs case_identityTwice__bf == "ok raw=false n=1"

-- identityTwice__pbt: I(a) = a \n x = (true) \n I(I(x))
def case_identityTwice__pbt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [.boolLiteral true]), privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "I") [(.call (.resolve "I") [.resolve "x"])])])
#guard obs case_identityTwice__pbt == "ok raw=true n=1"

-- identityTwice__pbt_e: I(a) = a \n x = (true, ()) \n I(I(x))
def case_identityTwice__pbt_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [.boolLiteral true, (.emptySequence 0)])]), privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "I") [(.call (.resolve "I") [.resolve "x"])])])
#guard obs case_identityTwice__pbt_e == "ok raw=S[true, S[]] n=1"

-- identityTwice__pbt_1: I(a) = a \n x = (true, 1) \n I(I(x))
def case_identityTwice__pbt_1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [.boolLiteral true, .num 1])]), privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "I") [(.call (.resolve "I") [.resolve "x"])])])
#guard obs case_identityTwice__pbt_1 == "ok raw=S[true, 1] n=1"

-- identityTwice__lbt: I(a) = a \n x = [true] \n I(I(x))
def case_identityTwice__lbt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [.boolLiteral true])]), privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "I") [(.call (.resolve "I") [.resolve "x"])])])
#guard obs case_identityTwice__lbt == "ok raw=L[true] n=1"

-- identityTwice__lbt_bf: I(a) = a \n x = [true, false] \n I(I(x))
def case_identityTwice__lbt_bf : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [.boolLiteral true, .boolLiteral false])]), privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "I") [(.call (.resolve "I") [.resolve "x"])])])
#guard obs case_identityTwice__lbt_bf == "ok raw=L[true, false] n=1"

-- identityTwice__lpbt_1: I(a) = a \n x = [(true, 1)] \n I(I(x))
def case_identityTwice__lpbt_1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [(.capture [.boolLiteral true, .num 1])])]), privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "I") [(.call (.resolve "I") [.resolve "x"])])])
#guard obs case_identityTwice__lpbt_1 == "ok raw=L[S[true, 1]] n=1"

-- identityTwice__p1: I(a) = a \n x = (1) \n I(I(x))
def case_identityTwice__p1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [.num 1]), privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "I") [(.call (.resolve "I") [.resolve "x"])])])
#guard obs case_identityTwice__p1 == "ok raw=1 n=1"

-- identityTwice__p12: I(a) = a \n x = (1, 2) \n I(I(x))
def case_identityTwice__p12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [.num 1, .num 2])]), privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "I") [(.call (.resolve "I") [.resolve "x"])])])
#guard obs case_identityTwice__p12 == "ok raw=S[1, 2] n=1"

-- identityTwice__p123: I(a) = a \n x = (1, 2, 3) \n I(I(x))
def case_identityTwice__p123 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [.num 1, .num 2, .num 3])]), privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "I") [(.call (.resolve "I") [.resolve "x"])])])
#guard obs case_identityTwice__p123 == "ok raw=S[1, 2, 3] n=1"

-- identityTwice__pee: I(a) = a \n x = ((), ()) \n I(I(x))
def case_identityTwice__pee : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.emptySequence 0), (.emptySequence 0)])]), privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "I") [(.call (.resolve "I") [.resolve "x"])])])
#guard obs case_identityTwice__pee == "ok raw=S[S[], S[]] n=1"

-- identityTwice__pe1: I(a) = a \n x = ((), 1) \n I(I(x))
def case_identityTwice__pe1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.emptySequence 0), .num 1])]), privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "I") [(.call (.resolve "I") [.resolve "x"])])])
#guard obs case_identityTwice__pe1 == "ok raw=S[S[], 1] n=1"

-- identityTwice__p1e: I(a) = a \n x = (1, ()) \n I(I(x))
def case_identityTwice__p1e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [.num 1, (.emptySequence 0)])]), privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "I") [(.call (.resolve "I") [.resolve "x"])])])
#guard obs case_identityTwice__p1e == "ok raw=S[1, S[]] n=1"

-- identityTwice__p12_3: I(a) = a \n x = ((1, 2), 3) \n I(I(x))
def case_identityTwice__p12_3 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.capture [.num 1, .num 2]), .num 3])]), privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "I") [(.call (.resolve "I") [.resolve "x"])])])
#guard obs case_identityTwice__p12_3 == "ok raw=S[S[1, 2], 3] n=1"

-- identityTwice__p12_34: I(a) = a \n x = ((1, 2), (3, 4)) \n I(I(x))
def case_identityTwice__p12_34 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.capture [.num 1, .num 2]), (.capture [.num 3, .num 4])])]), privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "I") [(.call (.resolve "I") [.resolve "x"])])])
#guard obs case_identityTwice__p12_34 == "ok raw=S[S[1, 2], S[3, 4]] n=1"

-- identityTwice__pe_12: I(a) = a \n x = ((), (1, 2)) \n I(I(x))
def case_identityTwice__pe_12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.emptySequence 0), (.capture [.num 1, .num 2])])]), privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "I") [(.call (.resolve "I") [.resolve "x"])])])
#guard obs case_identityTwice__pe_12 == "ok raw=S[S[], S[1, 2]] n=1"

-- identityTwice__ppe1_2: I(a) = a \n x = (((), 1), 2) \n I(I(x))
def case_identityTwice__ppe1_2 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.capture [(.emptySequence 0), .num 1]), .num 2])]), privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "I") [(.call (.resolve "I") [.resolve "x"])])])
#guard obs case_identityTwice__ppe1_2 == "ok raw=S[S[S[], 1], 2] n=1"

-- identityTwice__p12_e: I(a) = a \n x = ((1, 2), ()) \n I(I(x))
def case_identityTwice__p12_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.capture [.num 1, .num 2]), (.emptySequence 0)])]), privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "I") [(.call (.resolve "I") [.resolve "x"])])])
#guard obs case_identityTwice__p12_e == "ok raw=S[S[1, 2], S[]] n=1"

-- identityTwice__ppe: I(a) = a \n x = (()) \n I(I(x))
def case_identityTwice__ppe : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.emptySequence 0)]), privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "I") [(.call (.resolve "I") [.resolve "x"])])])
#guard obs case_identityTwice__ppe == "ok raw=S[] n=1"

-- identityTwice__pp1: I(a) = a \n x = ((1)) \n I(I(x))
def case_identityTwice__pp1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [.num 1]), privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "I") [(.call (.resolve "I") [.resolve "x"])])])
#guard obs case_identityTwice__pp1 == "ok raw=1 n=1"

-- identityTwice__ppp12: I(a) = a \n x = (((1, 2))) \n I(I(x))
def case_identityTwice__ppp12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [.num 1, .num 2])]), privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "I") [(.call (.resolve "I") [.resolve "x"])])])
#guard obs case_identityTwice__ppp12 == "ok raw=S[1, 2] n=1"

-- identityTwice__le: I(a) = a \n x = [] \n I(I(x))
def case_identityTwice__le : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [])]), privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "I") [(.call (.resolve "I") [.resolve "x"])])])
#guard obs case_identityTwice__le == "ok raw=L[] n=1"

-- identityTwice__l7: I(a) = a \n x = [7] \n I(I(x))
def case_identityTwice__l7 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [.num 7])]), privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "I") [(.call (.resolve "I") [.resolve "x"])])])
#guard obs case_identityTwice__l7 == "ok raw=L[7] n=1"

-- identityTwice__l12: I(a) = a \n x = [1, 2] \n I(I(x))
def case_identityTwice__l12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [.num 1, .num 2])]), privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "I") [(.call (.resolve "I") [.resolve "x"])])])
#guard obs case_identityTwice__l12 == "ok raw=L[1, 2] n=1"

-- identityTwice__l12_3: I(a) = a \n x = [[1, 2], 3] \n I(I(x))
def case_identityTwice__l12_3 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [(.listLiteral [.num 1, .num 2]), .num 3])]), privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "I") [(.call (.resolve "I") [.resolve "x"])])])
#guard obs case_identityTwice__l12_3 == "ok raw=L[L[1, 2], 3] n=1"

-- identityTwice__lle: I(a) = a \n x = [[]] \n I(I(x))
def case_identityTwice__lle : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [(.listLiteral [])])]), privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "I") [(.call (.resolve "I") [.resolve "x"])])])
#guard obs case_identityTwice__lle == "ok raw=L[L[]] n=1"

-- identityTwice__l_e: I(a) = a \n x = [()] \n I(I(x))
def case_identityTwice__l_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [(.emptySequence 0)])]), privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "I") [(.call (.resolve "I") [.resolve "x"])])])
#guard obs case_identityTwice__l_e == "ok raw=L[S[]] n=1"

-- identityTwice__l_p12: I(a) = a \n x = [(1, 2)] \n I(I(x))
def case_identityTwice__l_p12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [(.capture [.num 1, .num 2])])]), privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "I") [(.call (.resolve "I") [.resolve "x"])])])
#guard obs case_identityTwice__l_p12 == "ok raw=L[S[1, 2]] n=1"

-- identityTwice__p_l12: I(a) = a \n x = ([1, 2], 3) \n I(I(x))
def case_identityTwice__p_l12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.listLiteral [.num 1, .num 2]), .num 3])]), privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "I") [(.call (.resolve "I") [.resolve "x"])])])
#guard obs case_identityTwice__p_l12 == "ok raw=S[L[1, 2], 3] n=1"

-- identityTwice__pl1: I(a) = a \n x = ([1]) \n I(I(x))
def case_identityTwice__pl1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [.num 1])]), privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "I") [(.call (.resolve "I") [.resolve "x"])])])
#guard obs case_identityTwice__pl1 == "ok raw=L[1] n=1"

-- propChain__e: P = () \n Q = P \n Q
def case_propChain__e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (alg [] [] [] [(.emptySequence 0)]), privateProp "Q" (alg [] [] [] [.resolve "P"])] [.resolve "Q"])
#guard obs case_propChain__e == "ok raw=S[] n=1"

-- propChain__n0: P = 0 \n Q = P \n Q
def case_propChain__n0 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (alg [] [] [] [.num 0]), privateProp "Q" (alg [] [] [] [.resolve "P"])] [.resolve "Q"])
#guard obs case_propChain__n0 == "ok raw=0 n=1"

-- propChain__n1: P = 1 \n Q = P \n Q
def case_propChain__n1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (alg [] [] [] [.num 1]), privateProp "Q" (alg [] [] [] [.resolve "P"])] [.resolve "Q"])
#guard obs case_propChain__n1 == "ok raw=1 n=1"

-- propChain__bt: P = true \n Q = P \n Q
def case_propChain__bt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (alg [] [] [] [.boolLiteral true]), privateProp "Q" (alg [] [] [] [.resolve "P"])] [.resolve "Q"])
#guard obs case_propChain__bt == "ok raw=true n=1"

-- propChain__bf: P = false \n Q = P \n Q
def case_propChain__bf : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (alg [] [] [] [.boolLiteral false]), privateProp "Q" (alg [] [] [] [.resolve "P"])] [.resolve "Q"])
#guard obs case_propChain__bf == "ok raw=false n=1"

-- propChain__pbt: P = (true) \n Q = P \n Q
def case_propChain__pbt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (alg [] [] [] [.boolLiteral true]), privateProp "Q" (alg [] [] [] [.resolve "P"])] [.resolve "Q"])
#guard obs case_propChain__pbt == "ok raw=true n=1"

-- propChain__pbt_e: P = (true, ()) \n Q = P \n Q
def case_propChain__pbt_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (alg [] [] [] [(.capture [.boolLiteral true, (.emptySequence 0)])]), privateProp "Q" (alg [] [] [] [.resolve "P"])] [.resolve "Q"])
#guard obs case_propChain__pbt_e == "ok raw=S[true, S[]] n=1"

-- propChain__pbt_1: P = (true, 1) \n Q = P \n Q
def case_propChain__pbt_1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (alg [] [] [] [(.capture [.boolLiteral true, .num 1])]), privateProp "Q" (alg [] [] [] [.resolve "P"])] [.resolve "Q"])
#guard obs case_propChain__pbt_1 == "ok raw=S[true, 1] n=1"

-- propChain__lbt: P = [true] \n Q = P \n Q
def case_propChain__lbt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (alg [] [] [] [(.listLiteral [.boolLiteral true])]), privateProp "Q" (alg [] [] [] [.resolve "P"])] [.resolve "Q"])
#guard obs case_propChain__lbt == "ok raw=L[true] n=1"

-- propChain__lbt_bf: P = [true, false] \n Q = P \n Q
def case_propChain__lbt_bf : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (alg [] [] [] [(.listLiteral [.boolLiteral true, .boolLiteral false])]), privateProp "Q" (alg [] [] [] [.resolve "P"])] [.resolve "Q"])
#guard obs case_propChain__lbt_bf == "ok raw=L[true, false] n=1"

-- propChain__lpbt_1: P = [(true, 1)] \n Q = P \n Q
def case_propChain__lpbt_1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (alg [] [] [] [(.listLiteral [(.capture [.boolLiteral true, .num 1])])]), privateProp "Q" (alg [] [] [] [.resolve "P"])] [.resolve "Q"])
#guard obs case_propChain__lpbt_1 == "ok raw=L[S[true, 1]] n=1"

-- propChain__p1: P = (1) \n Q = P \n Q
def case_propChain__p1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (alg [] [] [] [.num 1]), privateProp "Q" (alg [] [] [] [.resolve "P"])] [.resolve "Q"])
#guard obs case_propChain__p1 == "ok raw=1 n=1"

-- propChain__p12: P = (1, 2) \n Q = P \n Q
def case_propChain__p12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (alg [] [] [] [(.capture [.num 1, .num 2])]), privateProp "Q" (alg [] [] [] [.resolve "P"])] [.resolve "Q"])
#guard obs case_propChain__p12 == "ok raw=S[1, 2] n=1"

-- propChain__p123: P = (1, 2, 3) \n Q = P \n Q
def case_propChain__p123 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (alg [] [] [] [(.capture [.num 1, .num 2, .num 3])]), privateProp "Q" (alg [] [] [] [.resolve "P"])] [.resolve "Q"])
#guard obs case_propChain__p123 == "ok raw=S[1, 2, 3] n=1"

-- propChain__pee: P = ((), ()) \n Q = P \n Q
def case_propChain__pee : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (alg [] [] [] [(.capture [(.emptySequence 0), (.emptySequence 0)])]), privateProp "Q" (alg [] [] [] [.resolve "P"])] [.resolve "Q"])
#guard obs case_propChain__pee == "ok raw=S[S[], S[]] n=1"

-- propChain__pe1: P = ((), 1) \n Q = P \n Q
def case_propChain__pe1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (alg [] [] [] [(.capture [(.emptySequence 0), .num 1])]), privateProp "Q" (alg [] [] [] [.resolve "P"])] [.resolve "Q"])
#guard obs case_propChain__pe1 == "ok raw=S[S[], 1] n=1"

-- propChain__p1e: P = (1, ()) \n Q = P \n Q
def case_propChain__p1e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (alg [] [] [] [(.capture [.num 1, (.emptySequence 0)])]), privateProp "Q" (alg [] [] [] [.resolve "P"])] [.resolve "Q"])
#guard obs case_propChain__p1e == "ok raw=S[1, S[]] n=1"

-- propChain__p12_3: P = ((1, 2), 3) \n Q = P \n Q
def case_propChain__p12_3 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (alg [] [] [] [(.capture [(.capture [.num 1, .num 2]), .num 3])]), privateProp "Q" (alg [] [] [] [.resolve "P"])] [.resolve "Q"])
#guard obs case_propChain__p12_3 == "ok raw=S[S[1, 2], 3] n=1"

-- propChain__p12_34: P = ((1, 2), (3, 4)) \n Q = P \n Q
def case_propChain__p12_34 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (alg [] [] [] [(.capture [(.capture [.num 1, .num 2]), (.capture [.num 3, .num 4])])]), privateProp "Q" (alg [] [] [] [.resolve "P"])] [.resolve "Q"])
#guard obs case_propChain__p12_34 == "ok raw=S[S[1, 2], S[3, 4]] n=1"

-- propChain__pe_12: P = ((), (1, 2)) \n Q = P \n Q
def case_propChain__pe_12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (alg [] [] [] [(.capture [(.emptySequence 0), (.capture [.num 1, .num 2])])]), privateProp "Q" (alg [] [] [] [.resolve "P"])] [.resolve "Q"])
#guard obs case_propChain__pe_12 == "ok raw=S[S[], S[1, 2]] n=1"

-- propChain__ppe1_2: P = (((), 1), 2) \n Q = P \n Q
def case_propChain__ppe1_2 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (alg [] [] [] [(.capture [(.capture [(.emptySequence 0), .num 1]), .num 2])]), privateProp "Q" (alg [] [] [] [.resolve "P"])] [.resolve "Q"])
#guard obs case_propChain__ppe1_2 == "ok raw=S[S[S[], 1], 2] n=1"

-- propChain__p12_e: P = ((1, 2), ()) \n Q = P \n Q
def case_propChain__p12_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (alg [] [] [] [(.capture [(.capture [.num 1, .num 2]), (.emptySequence 0)])]), privateProp "Q" (alg [] [] [] [.resolve "P"])] [.resolve "Q"])
#guard obs case_propChain__p12_e == "ok raw=S[S[1, 2], S[]] n=1"

-- propChain__ppe: P = (()) \n Q = P \n Q
def case_propChain__ppe : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (alg [] [] [] [(.emptySequence 0)]), privateProp "Q" (alg [] [] [] [.resolve "P"])] [.resolve "Q"])
#guard obs case_propChain__ppe == "ok raw=S[] n=1"

-- propChain__pp1: P = ((1)) \n Q = P \n Q
def case_propChain__pp1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (alg [] [] [] [.num 1]), privateProp "Q" (alg [] [] [] [.resolve "P"])] [.resolve "Q"])
#guard obs case_propChain__pp1 == "ok raw=1 n=1"

-- propChain__ppp12: P = (((1, 2))) \n Q = P \n Q
def case_propChain__ppp12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (alg [] [] [] [(.capture [.num 1, .num 2])]), privateProp "Q" (alg [] [] [] [.resolve "P"])] [.resolve "Q"])
#guard obs case_propChain__ppp12 == "ok raw=S[1, 2] n=1"

-- propChain__le: P = [] \n Q = P \n Q
def case_propChain__le : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (alg [] [] [] [(.listLiteral [])]), privateProp "Q" (alg [] [] [] [.resolve "P"])] [.resolve "Q"])
#guard obs case_propChain__le == "ok raw=L[] n=1"

-- propChain__l7: P = [7] \n Q = P \n Q
def case_propChain__l7 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (alg [] [] [] [(.listLiteral [.num 7])]), privateProp "Q" (alg [] [] [] [.resolve "P"])] [.resolve "Q"])
#guard obs case_propChain__l7 == "ok raw=L[7] n=1"

-- propChain__l12: P = [1, 2] \n Q = P \n Q
def case_propChain__l12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (alg [] [] [] [(.listLiteral [.num 1, .num 2])]), privateProp "Q" (alg [] [] [] [.resolve "P"])] [.resolve "Q"])
#guard obs case_propChain__l12 == "ok raw=L[1, 2] n=1"

-- propChain__l12_3: P = [[1, 2], 3] \n Q = P \n Q
def case_propChain__l12_3 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (alg [] [] [] [(.listLiteral [(.listLiteral [.num 1, .num 2]), .num 3])]), privateProp "Q" (alg [] [] [] [.resolve "P"])] [.resolve "Q"])
#guard obs case_propChain__l12_3 == "ok raw=L[L[1, 2], 3] n=1"

-- propChain__lle: P = [[]] \n Q = P \n Q
def case_propChain__lle : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (alg [] [] [] [(.listLiteral [(.listLiteral [])])]), privateProp "Q" (alg [] [] [] [.resolve "P"])] [.resolve "Q"])
#guard obs case_propChain__lle == "ok raw=L[L[]] n=1"

-- propChain__l_e: P = [()] \n Q = P \n Q
def case_propChain__l_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (alg [] [] [] [(.listLiteral [(.emptySequence 0)])]), privateProp "Q" (alg [] [] [] [.resolve "P"])] [.resolve "Q"])
#guard obs case_propChain__l_e == "ok raw=L[S[]] n=1"

-- propChain__l_p12: P = [(1, 2)] \n Q = P \n Q
def case_propChain__l_p12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (alg [] [] [] [(.listLiteral [(.capture [.num 1, .num 2])])]), privateProp "Q" (alg [] [] [] [.resolve "P"])] [.resolve "Q"])
#guard obs case_propChain__l_p12 == "ok raw=L[S[1, 2]] n=1"

-- propChain__p_l12: P = ([1, 2], 3) \n Q = P \n Q
def case_propChain__p_l12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (alg [] [] [] [(.capture [(.listLiteral [.num 1, .num 2]), .num 3])]), privateProp "Q" (alg [] [] [] [.resolve "P"])] [.resolve "Q"])
#guard obs case_propChain__p_l12 == "ok raw=S[L[1, 2], 3] n=1"

-- propChain__pl1: P = ([1]) \n Q = P \n Q
def case_propChain__pl1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (alg [] [] [] [(.listLiteral [.num 1])]), privateProp "Q" (alg [] [] [] [.resolve "P"])] [.resolve "Q"])
#guard obs case_propChain__pl1 == "ok raw=L[1] n=1"

-- take1__e: take((), 1)
def case_take1__e : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "take") [(.emptySequence 0), .num 1])])
#guard obs case_take1__e == "ok raw=L[] n=1"

-- take1__n0: take(0, 1)
def case_take1__n0 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "take") [.num 0, .num 1])])
#guard obs case_take1__n0 == "ok raw=L[0] n=1"

-- take1__n1: take(1, 1)
def case_take1__n1 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "take") [.num 1, .num 1])])
#guard obs case_take1__n1 == "ok raw=L[1] n=1"

-- take1__bt: take(true, 1)
def case_take1__bt : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "take") [.boolLiteral true, .num 1])])
#guard obs case_take1__bt == "ok raw=L[true] n=1"

-- take1__bf: take(false, 1)
def case_take1__bf : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "take") [.boolLiteral false, .num 1])])
#guard obs case_take1__bf == "ok raw=L[false] n=1"

-- take1__pbt: take((true), 1)
def case_take1__pbt : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "take") [.boolLiteral true, .num 1])])
#guard obs case_take1__pbt == "ok raw=L[true] n=1"

-- take1__pbt_e: take((true, ()), 1)
def case_take1__pbt_e : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "take") [(.capture [.boolLiteral true, (.emptySequence 0)]), .num 1])])
#guard obs case_take1__pbt_e == "ok raw=L[true] n=1"

-- take1__pbt_1: take((true, 1), 1)
def case_take1__pbt_1 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "take") [(.capture [.boolLiteral true, .num 1]), .num 1])])
#guard obs case_take1__pbt_1 == "ok raw=L[true] n=1"

-- take1__lbt: take([true], 1)
def case_take1__lbt : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "take") [(.listLiteral [.boolLiteral true]), .num 1])])
#guard obs case_take1__lbt == "ok raw=L[true] n=1"

-- take1__lbt_bf: take([true, false], 1)
def case_take1__lbt_bf : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "take") [(.listLiteral [.boolLiteral true, .boolLiteral false]), .num 1])])
#guard obs case_take1__lbt_bf == "ok raw=L[true] n=1"

-- take1__lpbt_1: take([(true, 1)], 1)
def case_take1__lpbt_1 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "take") [(.listLiteral [(.capture [.boolLiteral true, .num 1])]), .num 1])])
#guard obs case_take1__lpbt_1 == "ok raw=L[S[true, 1]] n=1"

-- take1__p1: take((1), 1)
def case_take1__p1 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "take") [.num 1, .num 1])])
#guard obs case_take1__p1 == "ok raw=L[1] n=1"

-- take1__p12: take((1, 2), 1)
def case_take1__p12 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "take") [(.capture [.num 1, .num 2]), .num 1])])
#guard obs case_take1__p12 == "ok raw=L[1] n=1"

-- take1__p123: take((1, 2, 3), 1)
def case_take1__p123 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "take") [(.capture [.num 1, .num 2, .num 3]), .num 1])])
#guard obs case_take1__p123 == "ok raw=L[1] n=1"

-- take1__pee: take(((), ()), 1)
def case_take1__pee : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "take") [(.capture [(.emptySequence 0), (.emptySequence 0)]), .num 1])])
#guard obs case_take1__pee == "ok raw=L[S[]] n=1"

-- take1__pe1: take(((), 1), 1)
def case_take1__pe1 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "take") [(.capture [(.emptySequence 0), .num 1]), .num 1])])
#guard obs case_take1__pe1 == "ok raw=L[S[]] n=1"

-- take1__p1e: take((1, ()), 1)
def case_take1__p1e : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "take") [(.capture [.num 1, (.emptySequence 0)]), .num 1])])
#guard obs case_take1__p1e == "ok raw=L[1] n=1"

-- take1__p12_3: take(((1, 2), 3), 1)
def case_take1__p12_3 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "take") [(.capture [(.capture [.num 1, .num 2]), .num 3]), .num 1])])
#guard obs case_take1__p12_3 == "ok raw=L[S[1, 2]] n=1"

-- take1__p12_34: take(((1, 2), (3, 4)), 1)
def case_take1__p12_34 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "take") [(.capture [(.capture [.num 1, .num 2]), (.capture [.num 3, .num 4])]), .num 1])])
#guard obs case_take1__p12_34 == "ok raw=L[S[1, 2]] n=1"

-- take1__pe_12: take(((), (1, 2)), 1)
def case_take1__pe_12 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "take") [(.capture [(.emptySequence 0), (.capture [.num 1, .num 2])]), .num 1])])
#guard obs case_take1__pe_12 == "ok raw=L[S[]] n=1"

-- take1__ppe1_2: take((((), 1), 2), 1)
def case_take1__ppe1_2 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "take") [(.capture [(.capture [(.emptySequence 0), .num 1]), .num 2]), .num 1])])
#guard obs case_take1__ppe1_2 == "ok raw=L[S[S[], 1]] n=1"

-- take1__p12_e: take(((1, 2), ()), 1)
def case_take1__p12_e : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "take") [(.capture [(.capture [.num 1, .num 2]), (.emptySequence 0)]), .num 1])])
#guard obs case_take1__p12_e == "ok raw=L[S[1, 2]] n=1"

-- take1__ppe: take((()), 1)
def case_take1__ppe : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "take") [(.emptySequence 0), .num 1])])
#guard obs case_take1__ppe == "ok raw=L[] n=1"

-- take1__pp1: take(((1)), 1)
def case_take1__pp1 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "take") [.num 1, .num 1])])
#guard obs case_take1__pp1 == "ok raw=L[1] n=1"

-- take1__ppp12: take((((1, 2))), 1)
def case_take1__ppp12 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "take") [(.capture [.num 1, .num 2]), .num 1])])
#guard obs case_take1__ppp12 == "ok raw=L[1] n=1"

-- take1__le: take([], 1)
def case_take1__le : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "take") [(.listLiteral []), .num 1])])
#guard obs case_take1__le == "ok raw=L[] n=1"

-- take1__l7: take([7], 1)
def case_take1__l7 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "take") [(.listLiteral [.num 7]), .num 1])])
#guard obs case_take1__l7 == "ok raw=L[7] n=1"

-- take1__l12: take([1, 2], 1)
def case_take1__l12 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "take") [(.listLiteral [.num 1, .num 2]), .num 1])])
#guard obs case_take1__l12 == "ok raw=L[1] n=1"

-- take1__l12_3: take([[1, 2], 3], 1)
def case_take1__l12_3 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "take") [(.listLiteral [(.listLiteral [.num 1, .num 2]), .num 3]), .num 1])])
#guard obs case_take1__l12_3 == "ok raw=L[L[1, 2]] n=1"

-- take1__lle: take([[]], 1)
def case_take1__lle : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "take") [(.listLiteral [(.listLiteral [])]), .num 1])])
#guard obs case_take1__lle == "ok raw=L[L[]] n=1"

-- take1__l_e: take([()], 1)
def case_take1__l_e : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "take") [(.listLiteral [(.emptySequence 0)]), .num 1])])
#guard obs case_take1__l_e == "ok raw=L[S[]] n=1"

-- take1__l_p12: take([(1, 2)], 1)
def case_take1__l_p12 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "take") [(.listLiteral [(.capture [.num 1, .num 2])]), .num 1])])
#guard obs case_take1__l_p12 == "ok raw=L[S[1, 2]] n=1"

-- take1__p_l12: take(([1, 2], 3), 1)
def case_take1__p_l12 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "take") [(.capture [(.listLiteral [.num 1, .num 2]), .num 3]), .num 1])])
#guard obs case_take1__p_l12 == "ok raw=L[L[1, 2]] n=1"

-- take1__pl1: take(([1]), 1)
def case_take1__pl1 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "take") [(.listLiteral [.num 1]), .num 1])])
#guard obs case_take1__pl1 == "ok raw=L[1] n=1"

-- take9__e: take((), 9)
def case_take9__e : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "take") [(.emptySequence 0), .num 9])])
#guard obs case_take9__e == "ok raw=L[] n=1"

-- take9__n0: take(0, 9)
def case_take9__n0 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "take") [.num 0, .num 9])])
#guard obs case_take9__n0 == "ok raw=L[0] n=1"

-- take9__n1: take(1, 9)
def case_take9__n1 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "take") [.num 1, .num 9])])
#guard obs case_take9__n1 == "ok raw=L[1] n=1"

-- take9__bt: take(true, 9)
def case_take9__bt : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "take") [.boolLiteral true, .num 9])])
#guard obs case_take9__bt == "ok raw=L[true] n=1"

-- take9__bf: take(false, 9)
def case_take9__bf : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "take") [.boolLiteral false, .num 9])])
#guard obs case_take9__bf == "ok raw=L[false] n=1"

-- take9__pbt: take((true), 9)
def case_take9__pbt : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "take") [.boolLiteral true, .num 9])])
#guard obs case_take9__pbt == "ok raw=L[true] n=1"

-- take9__pbt_e: take((true, ()), 9)
def case_take9__pbt_e : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "take") [(.capture [.boolLiteral true, (.emptySequence 0)]), .num 9])])
#guard obs case_take9__pbt_e == "ok raw=L[true, S[]] n=1"

-- take9__pbt_1: take((true, 1), 9)
def case_take9__pbt_1 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "take") [(.capture [.boolLiteral true, .num 1]), .num 9])])
#guard obs case_take9__pbt_1 == "ok raw=L[true, 1] n=1"

-- take9__lbt: take([true], 9)
def case_take9__lbt : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "take") [(.listLiteral [.boolLiteral true]), .num 9])])
#guard obs case_take9__lbt == "ok raw=L[true] n=1"

-- take9__lbt_bf: take([true, false], 9)
def case_take9__lbt_bf : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "take") [(.listLiteral [.boolLiteral true, .boolLiteral false]), .num 9])])
#guard obs case_take9__lbt_bf == "ok raw=L[true, false] n=1"

-- take9__lpbt_1: take([(true, 1)], 9)
def case_take9__lpbt_1 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "take") [(.listLiteral [(.capture [.boolLiteral true, .num 1])]), .num 9])])
#guard obs case_take9__lpbt_1 == "ok raw=L[S[true, 1]] n=1"

-- take9__p1: take((1), 9)
def case_take9__p1 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "take") [.num 1, .num 9])])
#guard obs case_take9__p1 == "ok raw=L[1] n=1"

-- take9__p12: take((1, 2), 9)
def case_take9__p12 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "take") [(.capture [.num 1, .num 2]), .num 9])])
#guard obs case_take9__p12 == "ok raw=L[1, 2] n=1"

-- take9__p123: take((1, 2, 3), 9)
def case_take9__p123 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "take") [(.capture [.num 1, .num 2, .num 3]), .num 9])])
#guard obs case_take9__p123 == "ok raw=L[1, 2, 3] n=1"

-- take9__pee: take(((), ()), 9)
def case_take9__pee : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "take") [(.capture [(.emptySequence 0), (.emptySequence 0)]), .num 9])])
#guard obs case_take9__pee == "ok raw=L[S[], S[]] n=1"

-- take9__pe1: take(((), 1), 9)
def case_take9__pe1 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "take") [(.capture [(.emptySequence 0), .num 1]), .num 9])])
#guard obs case_take9__pe1 == "ok raw=L[S[], 1] n=1"

-- take9__p1e: take((1, ()), 9)
def case_take9__p1e : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "take") [(.capture [.num 1, (.emptySequence 0)]), .num 9])])
#guard obs case_take9__p1e == "ok raw=L[1, S[]] n=1"

-- take9__p12_3: take(((1, 2), 3), 9)
def case_take9__p12_3 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "take") [(.capture [(.capture [.num 1, .num 2]), .num 3]), .num 9])])
#guard obs case_take9__p12_3 == "ok raw=L[S[1, 2], 3] n=1"

-- take9__p12_34: take(((1, 2), (3, 4)), 9)
def case_take9__p12_34 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "take") [(.capture [(.capture [.num 1, .num 2]), (.capture [.num 3, .num 4])]), .num 9])])
#guard obs case_take9__p12_34 == "ok raw=L[S[1, 2], S[3, 4]] n=1"

-- take9__pe_12: take(((), (1, 2)), 9)
def case_take9__pe_12 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "take") [(.capture [(.emptySequence 0), (.capture [.num 1, .num 2])]), .num 9])])
#guard obs case_take9__pe_12 == "ok raw=L[S[], S[1, 2]] n=1"

-- take9__ppe1_2: take((((), 1), 2), 9)
def case_take9__ppe1_2 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "take") [(.capture [(.capture [(.emptySequence 0), .num 1]), .num 2]), .num 9])])
#guard obs case_take9__ppe1_2 == "ok raw=L[S[S[], 1], 2] n=1"

-- take9__p12_e: take(((1, 2), ()), 9)
def case_take9__p12_e : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "take") [(.capture [(.capture [.num 1, .num 2]), (.emptySequence 0)]), .num 9])])
#guard obs case_take9__p12_e == "ok raw=L[S[1, 2], S[]] n=1"

-- take9__ppe: take((()), 9)
def case_take9__ppe : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "take") [(.emptySequence 0), .num 9])])
#guard obs case_take9__ppe == "ok raw=L[] n=1"

-- take9__pp1: take(((1)), 9)
def case_take9__pp1 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "take") [.num 1, .num 9])])
#guard obs case_take9__pp1 == "ok raw=L[1] n=1"

-- take9__ppp12: take((((1, 2))), 9)
def case_take9__ppp12 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "take") [(.capture [.num 1, .num 2]), .num 9])])
#guard obs case_take9__ppp12 == "ok raw=L[1, 2] n=1"

-- take9__le: take([], 9)
def case_take9__le : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "take") [(.listLiteral []), .num 9])])
#guard obs case_take9__le == "ok raw=L[] n=1"

-- take9__l7: take([7], 9)
def case_take9__l7 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "take") [(.listLiteral [.num 7]), .num 9])])
#guard obs case_take9__l7 == "ok raw=L[7] n=1"

-- take9__l12: take([1, 2], 9)
def case_take9__l12 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "take") [(.listLiteral [.num 1, .num 2]), .num 9])])
#guard obs case_take9__l12 == "ok raw=L[1, 2] n=1"

-- take9__l12_3: take([[1, 2], 3], 9)
def case_take9__l12_3 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "take") [(.listLiteral [(.listLiteral [.num 1, .num 2]), .num 3]), .num 9])])
#guard obs case_take9__l12_3 == "ok raw=L[L[1, 2], 3] n=1"

-- take9__lle: take([[]], 9)
def case_take9__lle : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "take") [(.listLiteral [(.listLiteral [])]), .num 9])])
#guard obs case_take9__lle == "ok raw=L[L[]] n=1"

-- take9__l_e: take([()], 9)
def case_take9__l_e : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "take") [(.listLiteral [(.emptySequence 0)]), .num 9])])
#guard obs case_take9__l_e == "ok raw=L[S[]] n=1"

-- take9__l_p12: take([(1, 2)], 9)
def case_take9__l_p12 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "take") [(.listLiteral [(.capture [.num 1, .num 2])]), .num 9])])
#guard obs case_take9__l_p12 == "ok raw=L[S[1, 2]] n=1"

-- take9__p_l12: take(([1, 2], 3), 9)
def case_take9__p_l12 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "take") [(.capture [(.listLiteral [.num 1, .num 2]), .num 3]), .num 9])])
#guard obs case_take9__p_l12 == "ok raw=L[L[1, 2], 3] n=1"

-- take9__pl1: take(([1]), 9)
def case_take9__pl1 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "take") [(.listLiteral [.num 1]), .num 9])])
#guard obs case_take9__pl1 == "ok raw=L[1] n=1"

-- skip1__e: skip((), 1)
def case_skip1__e : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "skip") [(.emptySequence 0), .num 1])])
#guard obs case_skip1__e == "ok raw=L[] n=1"

-- skip1__n0: skip(0, 1)
def case_skip1__n0 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "skip") [.num 0, .num 1])])
#guard obs case_skip1__n0 == "ok raw=L[] n=1"

-- skip1__n1: skip(1, 1)
def case_skip1__n1 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "skip") [.num 1, .num 1])])
#guard obs case_skip1__n1 == "ok raw=L[] n=1"

-- skip1__bt: skip(true, 1)
def case_skip1__bt : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "skip") [.boolLiteral true, .num 1])])
#guard obs case_skip1__bt == "ok raw=L[] n=1"

-- skip1__bf: skip(false, 1)
def case_skip1__bf : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "skip") [.boolLiteral false, .num 1])])
#guard obs case_skip1__bf == "ok raw=L[] n=1"

-- skip1__pbt: skip((true), 1)
def case_skip1__pbt : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "skip") [.boolLiteral true, .num 1])])
#guard obs case_skip1__pbt == "ok raw=L[] n=1"

-- skip1__pbt_e: skip((true, ()), 1)
def case_skip1__pbt_e : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "skip") [(.capture [.boolLiteral true, (.emptySequence 0)]), .num 1])])
#guard obs case_skip1__pbt_e == "ok raw=L[S[]] n=1"

-- skip1__pbt_1: skip((true, 1), 1)
def case_skip1__pbt_1 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "skip") [(.capture [.boolLiteral true, .num 1]), .num 1])])
#guard obs case_skip1__pbt_1 == "ok raw=L[1] n=1"

-- skip1__lbt: skip([true], 1)
def case_skip1__lbt : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "skip") [(.listLiteral [.boolLiteral true]), .num 1])])
#guard obs case_skip1__lbt == "ok raw=L[] n=1"

-- skip1__lbt_bf: skip([true, false], 1)
def case_skip1__lbt_bf : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "skip") [(.listLiteral [.boolLiteral true, .boolLiteral false]), .num 1])])
#guard obs case_skip1__lbt_bf == "ok raw=L[false] n=1"

-- skip1__lpbt_1: skip([(true, 1)], 1)
def case_skip1__lpbt_1 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "skip") [(.listLiteral [(.capture [.boolLiteral true, .num 1])]), .num 1])])
#guard obs case_skip1__lpbt_1 == "ok raw=L[] n=1"

-- skip1__p1: skip((1), 1)
def case_skip1__p1 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "skip") [.num 1, .num 1])])
#guard obs case_skip1__p1 == "ok raw=L[] n=1"

-- skip1__p12: skip((1, 2), 1)
def case_skip1__p12 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "skip") [(.capture [.num 1, .num 2]), .num 1])])
#guard obs case_skip1__p12 == "ok raw=L[2] n=1"

-- skip1__p123: skip((1, 2, 3), 1)
def case_skip1__p123 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "skip") [(.capture [.num 1, .num 2, .num 3]), .num 1])])
#guard obs case_skip1__p123 == "ok raw=L[2, 3] n=1"

-- skip1__pee: skip(((), ()), 1)
def case_skip1__pee : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "skip") [(.capture [(.emptySequence 0), (.emptySequence 0)]), .num 1])])
#guard obs case_skip1__pee == "ok raw=L[S[]] n=1"

-- skip1__pe1: skip(((), 1), 1)
def case_skip1__pe1 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "skip") [(.capture [(.emptySequence 0), .num 1]), .num 1])])
#guard obs case_skip1__pe1 == "ok raw=L[1] n=1"

-- skip1__p1e: skip((1, ()), 1)
def case_skip1__p1e : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "skip") [(.capture [.num 1, (.emptySequence 0)]), .num 1])])
#guard obs case_skip1__p1e == "ok raw=L[S[]] n=1"

-- skip1__p12_3: skip(((1, 2), 3), 1)
def case_skip1__p12_3 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "skip") [(.capture [(.capture [.num 1, .num 2]), .num 3]), .num 1])])
#guard obs case_skip1__p12_3 == "ok raw=L[3] n=1"

-- skip1__p12_34: skip(((1, 2), (3, 4)), 1)
def case_skip1__p12_34 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "skip") [(.capture [(.capture [.num 1, .num 2]), (.capture [.num 3, .num 4])]), .num 1])])
#guard obs case_skip1__p12_34 == "ok raw=L[S[3, 4]] n=1"

-- skip1__pe_12: skip(((), (1, 2)), 1)
def case_skip1__pe_12 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "skip") [(.capture [(.emptySequence 0), (.capture [.num 1, .num 2])]), .num 1])])
#guard obs case_skip1__pe_12 == "ok raw=L[S[1, 2]] n=1"

-- skip1__ppe1_2: skip((((), 1), 2), 1)
def case_skip1__ppe1_2 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "skip") [(.capture [(.capture [(.emptySequence 0), .num 1]), .num 2]), .num 1])])
#guard obs case_skip1__ppe1_2 == "ok raw=L[2] n=1"

-- skip1__p12_e: skip(((1, 2), ()), 1)
def case_skip1__p12_e : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "skip") [(.capture [(.capture [.num 1, .num 2]), (.emptySequence 0)]), .num 1])])
#guard obs case_skip1__p12_e == "ok raw=L[S[]] n=1"

-- skip1__ppe: skip((()), 1)
def case_skip1__ppe : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "skip") [(.emptySequence 0), .num 1])])
#guard obs case_skip1__ppe == "ok raw=L[] n=1"

-- skip1__pp1: skip(((1)), 1)
def case_skip1__pp1 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "skip") [.num 1, .num 1])])
#guard obs case_skip1__pp1 == "ok raw=L[] n=1"

-- skip1__ppp12: skip((((1, 2))), 1)
def case_skip1__ppp12 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "skip") [(.capture [.num 1, .num 2]), .num 1])])
#guard obs case_skip1__ppp12 == "ok raw=L[2] n=1"

-- skip1__le: skip([], 1)
def case_skip1__le : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "skip") [(.listLiteral []), .num 1])])
#guard obs case_skip1__le == "ok raw=L[] n=1"

-- skip1__l7: skip([7], 1)
def case_skip1__l7 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "skip") [(.listLiteral [.num 7]), .num 1])])
#guard obs case_skip1__l7 == "ok raw=L[] n=1"

-- skip1__l12: skip([1, 2], 1)
def case_skip1__l12 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "skip") [(.listLiteral [.num 1, .num 2]), .num 1])])
#guard obs case_skip1__l12 == "ok raw=L[2] n=1"

-- skip1__l12_3: skip([[1, 2], 3], 1)
def case_skip1__l12_3 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "skip") [(.listLiteral [(.listLiteral [.num 1, .num 2]), .num 3]), .num 1])])
#guard obs case_skip1__l12_3 == "ok raw=L[3] n=1"

-- skip1__lle: skip([[]], 1)
def case_skip1__lle : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "skip") [(.listLiteral [(.listLiteral [])]), .num 1])])
#guard obs case_skip1__lle == "ok raw=L[] n=1"

-- skip1__l_e: skip([()], 1)
def case_skip1__l_e : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "skip") [(.listLiteral [(.emptySequence 0)]), .num 1])])
#guard obs case_skip1__l_e == "ok raw=L[] n=1"

-- skip1__l_p12: skip([(1, 2)], 1)
def case_skip1__l_p12 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "skip") [(.listLiteral [(.capture [.num 1, .num 2])]), .num 1])])
#guard obs case_skip1__l_p12 == "ok raw=L[] n=1"

-- skip1__p_l12: skip(([1, 2], 3), 1)
def case_skip1__p_l12 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "skip") [(.capture [(.listLiteral [.num 1, .num 2]), .num 3]), .num 1])])
#guard obs case_skip1__p_l12 == "ok raw=L[3] n=1"

-- skip1__pl1: skip(([1]), 1)
def case_skip1__pl1 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "skip") [(.listLiteral [.num 1]), .num 1])])
#guard obs case_skip1__pl1 == "ok raw=L[] n=1"

-- distinct__e: distinct(())
def case_distinct__e : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "distinct") [(.emptySequence 0)])])
#guard obs case_distinct__e == "ok raw=L[] n=1"

-- distinct__n0: distinct(0)
def case_distinct__n0 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "distinct") [.num 0])])
#guard obs case_distinct__n0 == "ok raw=L[0] n=1"

-- distinct__n1: distinct(1)
def case_distinct__n1 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "distinct") [.num 1])])
#guard obs case_distinct__n1 == "ok raw=L[1] n=1"

-- distinct__bt: distinct(true)
def case_distinct__bt : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "distinct") [.boolLiteral true])])
#guard obs case_distinct__bt == "ok raw=L[true] n=1"

-- distinct__bf: distinct(false)
def case_distinct__bf : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "distinct") [.boolLiteral false])])
#guard obs case_distinct__bf == "ok raw=L[false] n=1"

-- distinct__pbt: distinct((true))
def case_distinct__pbt : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "distinct") [.boolLiteral true])])
#guard obs case_distinct__pbt == "ok raw=L[true] n=1"

-- distinct__pbt_e: distinct((true, ()))
def case_distinct__pbt_e : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "distinct") [(.capture [.boolLiteral true, (.emptySequence 0)])])])
#guard obs case_distinct__pbt_e == "ok raw=L[true, S[]] n=1"

-- distinct__pbt_1: distinct((true, 1))
def case_distinct__pbt_1 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "distinct") [(.capture [.boolLiteral true, .num 1])])])
#guard obs case_distinct__pbt_1 == "ok raw=L[true, 1] n=1"

-- distinct__lbt: distinct([true])
def case_distinct__lbt : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "distinct") [(.listLiteral [.boolLiteral true])])])
#guard obs case_distinct__lbt == "ok raw=L[true] n=1"

-- distinct__lbt_bf: distinct([true, false])
def case_distinct__lbt_bf : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "distinct") [(.listLiteral [.boolLiteral true, .boolLiteral false])])])
#guard obs case_distinct__lbt_bf == "ok raw=L[true, false] n=1"

-- distinct__lpbt_1: distinct([(true, 1)])
def case_distinct__lpbt_1 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "distinct") [(.listLiteral [(.capture [.boolLiteral true, .num 1])])])])
#guard obs case_distinct__lpbt_1 == "ok raw=L[S[true, 1]] n=1"

-- distinct__p1: distinct((1))
def case_distinct__p1 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "distinct") [.num 1])])
#guard obs case_distinct__p1 == "ok raw=L[1] n=1"

-- distinct__p12: distinct((1, 2))
def case_distinct__p12 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "distinct") [(.capture [.num 1, .num 2])])])
#guard obs case_distinct__p12 == "ok raw=L[1, 2] n=1"

-- distinct__p123: distinct((1, 2, 3))
def case_distinct__p123 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "distinct") [(.capture [.num 1, .num 2, .num 3])])])
#guard obs case_distinct__p123 == "ok raw=L[1, 2, 3] n=1"

-- distinct__pee: distinct(((), ()))
def case_distinct__pee : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "distinct") [(.capture [(.emptySequence 0), (.emptySequence 0)])])])
#guard obs case_distinct__pee == "ok raw=L[S[]] n=1"

-- distinct__pe1: distinct(((), 1))
def case_distinct__pe1 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "distinct") [(.capture [(.emptySequence 0), .num 1])])])
#guard obs case_distinct__pe1 == "ok raw=L[S[], 1] n=1"

-- distinct__p1e: distinct((1, ()))
def case_distinct__p1e : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "distinct") [(.capture [.num 1, (.emptySequence 0)])])])
#guard obs case_distinct__p1e == "ok raw=L[1, S[]] n=1"

-- distinct__p12_3: distinct(((1, 2), 3))
def case_distinct__p12_3 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "distinct") [(.capture [(.capture [.num 1, .num 2]), .num 3])])])
#guard obs case_distinct__p12_3 == "ok raw=L[S[1, 2], 3] n=1"

-- distinct__p12_34: distinct(((1, 2), (3, 4)))
def case_distinct__p12_34 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "distinct") [(.capture [(.capture [.num 1, .num 2]), (.capture [.num 3, .num 4])])])])
#guard obs case_distinct__p12_34 == "ok raw=L[S[1, 2], S[3, 4]] n=1"

-- distinct__pe_12: distinct(((), (1, 2)))
def case_distinct__pe_12 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "distinct") [(.capture [(.emptySequence 0), (.capture [.num 1, .num 2])])])])
#guard obs case_distinct__pe_12 == "ok raw=L[S[], S[1, 2]] n=1"

-- distinct__ppe1_2: distinct((((), 1), 2))
def case_distinct__ppe1_2 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "distinct") [(.capture [(.capture [(.emptySequence 0), .num 1]), .num 2])])])
#guard obs case_distinct__ppe1_2 == "ok raw=L[S[S[], 1], 2] n=1"

-- distinct__p12_e: distinct(((1, 2), ()))
def case_distinct__p12_e : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "distinct") [(.capture [(.capture [.num 1, .num 2]), (.emptySequence 0)])])])
#guard obs case_distinct__p12_e == "ok raw=L[S[1, 2], S[]] n=1"

-- distinct__ppe: distinct((()))
def case_distinct__ppe : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "distinct") [(.emptySequence 0)])])
#guard obs case_distinct__ppe == "ok raw=L[] n=1"

-- distinct__pp1: distinct(((1)))
def case_distinct__pp1 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "distinct") [.num 1])])
#guard obs case_distinct__pp1 == "ok raw=L[1] n=1"

-- distinct__ppp12: distinct((((1, 2))))
def case_distinct__ppp12 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "distinct") [(.capture [.num 1, .num 2])])])
#guard obs case_distinct__ppp12 == "ok raw=L[1, 2] n=1"

-- distinct__le: distinct([])
def case_distinct__le : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "distinct") [(.listLiteral [])])])
#guard obs case_distinct__le == "ok raw=L[] n=1"

-- distinct__l7: distinct([7])
def case_distinct__l7 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "distinct") [(.listLiteral [.num 7])])])
#guard obs case_distinct__l7 == "ok raw=L[7] n=1"

-- distinct__l12: distinct([1, 2])
def case_distinct__l12 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "distinct") [(.listLiteral [.num 1, .num 2])])])
#guard obs case_distinct__l12 == "ok raw=L[1, 2] n=1"

-- distinct__l12_3: distinct([[1, 2], 3])
def case_distinct__l12_3 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "distinct") [(.listLiteral [(.listLiteral [.num 1, .num 2]), .num 3])])])
#guard obs case_distinct__l12_3 == "ok raw=L[L[1, 2], 3] n=1"

-- distinct__lle: distinct([[]])
def case_distinct__lle : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "distinct") [(.listLiteral [(.listLiteral [])])])])
#guard obs case_distinct__lle == "ok raw=L[L[]] n=1"

-- distinct__l_e: distinct([()])
def case_distinct__l_e : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "distinct") [(.listLiteral [(.emptySequence 0)])])])
#guard obs case_distinct__l_e == "ok raw=L[S[]] n=1"

-- distinct__l_p12: distinct([(1, 2)])
def case_distinct__l_p12 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "distinct") [(.listLiteral [(.capture [.num 1, .num 2])])])])
#guard obs case_distinct__l_p12 == "ok raw=L[S[1, 2]] n=1"

-- distinct__p_l12: distinct(([1, 2], 3))
def case_distinct__p_l12 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "distinct") [(.capture [(.listLiteral [.num 1, .num 2]), .num 3])])])
#guard obs case_distinct__p_l12 == "ok raw=L[L[1, 2], 3] n=1"

-- distinct__pl1: distinct(([1]))
def case_distinct__pl1 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "distinct") [(.listLiteral [.num 1])])])
#guard obs case_distinct__pl1 == "ok raw=L[1] n=1"

-- order__e: order(())
def case_order__e : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "order") [(.emptySequence 0)])])
#guard obs case_order__e == "ok raw=L[] n=1"

-- order__n0: order(0)
def case_order__n0 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "order") [.num 0])])
#guard obs case_order__n0 == "ok raw=L[0] n=1"

-- order__n1: order(1)
def case_order__n1 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "order") [.num 1])])
#guard obs case_order__n1 == "ok raw=L[1] n=1"

-- order__bt: order(true)
def case_order__bt : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "order") [.boolLiteral true])])
#guard obs case_order__bt == "err arity"

-- order__bf: order(false)
def case_order__bf : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "order") [.boolLiteral false])])
#guard obs case_order__bf == "err arity"

-- order__pbt: order((true))
def case_order__pbt : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "order") [.boolLiteral true])])
#guard obs case_order__pbt == "err arity"

-- order__pbt_e: order((true, ()))
def case_order__pbt_e : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "order") [(.capture [.boolLiteral true, (.emptySequence 0)])])])
#guard obs case_order__pbt_e == "err arity"

-- order__pbt_1: order((true, 1))
def case_order__pbt_1 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "order") [(.capture [.boolLiteral true, .num 1])])])
#guard obs case_order__pbt_1 == "err arity"

-- order__lbt: order([true])
def case_order__lbt : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "order") [(.listLiteral [.boolLiteral true])])])
#guard obs case_order__lbt == "err arity"

-- order__lbt_bf: order([true, false])
def case_order__lbt_bf : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "order") [(.listLiteral [.boolLiteral true, .boolLiteral false])])])
#guard obs case_order__lbt_bf == "err arity"

-- order__lpbt_1: order([(true, 1)])
def case_order__lpbt_1 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "order") [(.listLiteral [(.capture [.boolLiteral true, .num 1])])])])
#guard obs case_order__lpbt_1 == "err arity"

-- order__p1: order((1))
def case_order__p1 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "order") [.num 1])])
#guard obs case_order__p1 == "ok raw=L[1] n=1"

-- order__p12: order((1, 2))
def case_order__p12 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "order") [(.capture [.num 1, .num 2])])])
#guard obs case_order__p12 == "ok raw=L[1, 2] n=1"

-- order__p123: order((1, 2, 3))
def case_order__p123 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "order") [(.capture [.num 1, .num 2, .num 3])])])
#guard obs case_order__p123 == "ok raw=L[1, 2, 3] n=1"

-- order__pee: order(((), ()))
def case_order__pee : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "order") [(.capture [(.emptySequence 0), (.emptySequence 0)])])])
#guard obs case_order__pee == "err arity"

-- order__pe1: order(((), 1))
def case_order__pe1 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "order") [(.capture [(.emptySequence 0), .num 1])])])
#guard obs case_order__pe1 == "err arity"

-- order__p1e: order((1, ()))
def case_order__p1e : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "order") [(.capture [.num 1, (.emptySequence 0)])])])
#guard obs case_order__p1e == "err arity"

-- order__p12_3: order(((1, 2), 3))
def case_order__p12_3 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "order") [(.capture [(.capture [.num 1, .num 2]), .num 3])])])
#guard obs case_order__p12_3 == "err arity"

-- order__p12_34: order(((1, 2), (3, 4)))
def case_order__p12_34 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "order") [(.capture [(.capture [.num 1, .num 2]), (.capture [.num 3, .num 4])])])])
#guard obs case_order__p12_34 == "err arity"

-- order__pe_12: order(((), (1, 2)))
def case_order__pe_12 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "order") [(.capture [(.emptySequence 0), (.capture [.num 1, .num 2])])])])
#guard obs case_order__pe_12 == "err arity"

-- order__ppe1_2: order((((), 1), 2))
def case_order__ppe1_2 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "order") [(.capture [(.capture [(.emptySequence 0), .num 1]), .num 2])])])
#guard obs case_order__ppe1_2 == "err arity"

-- order__p12_e: order(((1, 2), ()))
def case_order__p12_e : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "order") [(.capture [(.capture [.num 1, .num 2]), (.emptySequence 0)])])])
#guard obs case_order__p12_e == "err arity"

-- order__ppe: order((()))
def case_order__ppe : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "order") [(.emptySequence 0)])])
#guard obs case_order__ppe == "ok raw=L[] n=1"

-- order__pp1: order(((1)))
def case_order__pp1 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "order") [.num 1])])
#guard obs case_order__pp1 == "ok raw=L[1] n=1"

-- order__ppp12: order((((1, 2))))
def case_order__ppp12 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "order") [(.capture [.num 1, .num 2])])])
#guard obs case_order__ppp12 == "ok raw=L[1, 2] n=1"

-- order__le: order([])
def case_order__le : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "order") [(.listLiteral [])])])
#guard obs case_order__le == "ok raw=L[] n=1"

-- order__l7: order([7])
def case_order__l7 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "order") [(.listLiteral [.num 7])])])
#guard obs case_order__l7 == "ok raw=L[7] n=1"

-- order__l12: order([1, 2])
def case_order__l12 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "order") [(.listLiteral [.num 1, .num 2])])])
#guard obs case_order__l12 == "ok raw=L[1, 2] n=1"

-- order__l12_3: order([[1, 2], 3])
def case_order__l12_3 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "order") [(.listLiteral [(.listLiteral [.num 1, .num 2]), .num 3])])])
#guard obs case_order__l12_3 == "err arity"

-- order__lle: order([[]])
def case_order__lle : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "order") [(.listLiteral [(.listLiteral [])])])])
#guard obs case_order__lle == "err arity"

-- order__l_e: order([()])
def case_order__l_e : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "order") [(.listLiteral [(.emptySequence 0)])])])
#guard obs case_order__l_e == "err arity"

-- order__l_p12: order([(1, 2)])
def case_order__l_p12 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "order") [(.listLiteral [(.capture [.num 1, .num 2])])])])
#guard obs case_order__l_p12 == "err arity"

-- order__p_l12: order(([1, 2], 3))
def case_order__p_l12 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "order") [(.capture [(.listLiteral [.num 1, .num 2]), .num 3])])])
#guard obs case_order__p_l12 == "err arity"

-- order__pl1: order(([1]))
def case_order__pl1 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "order") [(.listLiteral [.num 1])])])
#guard obs case_order__pl1 == "ok raw=L[1] n=1"

-- mapId__e: M(a) = a \n map((), M)
def case_mapId__e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "M" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "map") [(.emptySequence 0), .resolve "M"])])
#guard obs case_mapId__e == "ok raw=L[] n=1"

-- mapId__n0: M(a) = a \n map(0, M)
def case_mapId__n0 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "M" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "map") [.num 0, .resolve "M"])])
#guard obs case_mapId__n0 == "ok raw=L[0] n=1"

-- mapId__n1: M(a) = a \n map(1, M)
def case_mapId__n1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "M" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "map") [.num 1, .resolve "M"])])
#guard obs case_mapId__n1 == "ok raw=L[1] n=1"

-- mapId__bt: M(a) = a \n map(true, M)
def case_mapId__bt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "M" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "map") [.boolLiteral true, .resolve "M"])])
#guard obs case_mapId__bt == "ok raw=L[true] n=1"

-- mapId__bf: M(a) = a \n map(false, M)
def case_mapId__bf : Expr :=
  .algorithmExpr (alg [] [] [privateProp "M" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "map") [.boolLiteral false, .resolve "M"])])
#guard obs case_mapId__bf == "ok raw=L[false] n=1"

-- mapId__pbt: M(a) = a \n map((true), M)
def case_mapId__pbt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "M" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "map") [.boolLiteral true, .resolve "M"])])
#guard obs case_mapId__pbt == "ok raw=L[true] n=1"

-- mapId__pbt_e: M(a) = a \n map((true, ()), M)
def case_mapId__pbt_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "M" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "map") [(.capture [.boolLiteral true, (.emptySequence 0)]), .resolve "M"])])
#guard obs case_mapId__pbt_e == "err arity"

-- mapId__pbt_1: M(a) = a \n map((true, 1), M)
def case_mapId__pbt_1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "M" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "map") [(.capture [.boolLiteral true, .num 1]), .resolve "M"])])
#guard obs case_mapId__pbt_1 == "ok raw=L[true, 1] n=1"

-- mapId__lbt: M(a) = a \n map([true], M)
def case_mapId__lbt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "M" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "map") [(.listLiteral [.boolLiteral true]), .resolve "M"])])
#guard obs case_mapId__lbt == "ok raw=L[true] n=1"

-- mapId__lbt_bf: M(a) = a \n map([true, false], M)
def case_mapId__lbt_bf : Expr :=
  .algorithmExpr (alg [] [] [privateProp "M" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "map") [(.listLiteral [.boolLiteral true, .boolLiteral false]), .resolve "M"])])
#guard obs case_mapId__lbt_bf == "ok raw=L[true, false] n=1"

-- mapId__lpbt_1: M(a) = a \n map([(true, 1)], M)
def case_mapId__lpbt_1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "M" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "map") [(.listLiteral [(.capture [.boolLiteral true, .num 1])]), .resolve "M"])])
#guard obs case_mapId__lpbt_1 == "ok raw=L[S[true, 1]] n=1"

-- mapId__p1: M(a) = a \n map((1), M)
def case_mapId__p1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "M" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "map") [.num 1, .resolve "M"])])
#guard obs case_mapId__p1 == "ok raw=L[1] n=1"

-- mapId__p12: M(a) = a \n map((1, 2), M)
def case_mapId__p12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "M" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "map") [(.capture [.num 1, .num 2]), .resolve "M"])])
#guard obs case_mapId__p12 == "ok raw=L[1, 2] n=1"

-- mapId__p123: M(a) = a \n map((1, 2, 3), M)
def case_mapId__p123 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "M" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "map") [(.capture [.num 1, .num 2, .num 3]), .resolve "M"])])
#guard obs case_mapId__p123 == "ok raw=L[1, 2, 3] n=1"

-- mapId__pee: M(a) = a \n map(((), ()), M)
def case_mapId__pee : Expr :=
  .algorithmExpr (alg [] [] [privateProp "M" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "map") [(.capture [(.emptySequence 0), (.emptySequence 0)]), .resolve "M"])])
#guard obs case_mapId__pee == "err arity"

-- mapId__pe1: M(a) = a \n map(((), 1), M)
def case_mapId__pe1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "M" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "map") [(.capture [(.emptySequence 0), .num 1]), .resolve "M"])])
#guard obs case_mapId__pe1 == "err arity"

-- mapId__p1e: M(a) = a \n map((1, ()), M)
def case_mapId__p1e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "M" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "map") [(.capture [.num 1, (.emptySequence 0)]), .resolve "M"])])
#guard obs case_mapId__p1e == "err arity"

-- mapId__p12_3: M(a) = a \n map(((1, 2), 3), M)
def case_mapId__p12_3 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "M" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "map") [(.capture [(.capture [.num 1, .num 2]), .num 3]), .resolve "M"])])
#guard obs case_mapId__p12_3 == "ok raw=L[S[1, 2], 3] n=1"

-- mapId__p12_34: M(a) = a \n map(((1, 2), (3, 4)), M)
def case_mapId__p12_34 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "M" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "map") [(.capture [(.capture [.num 1, .num 2]), (.capture [.num 3, .num 4])]), .resolve "M"])])
#guard obs case_mapId__p12_34 == "ok raw=L[S[1, 2], S[3, 4]] n=1"

-- mapId__pe_12: M(a) = a \n map(((), (1, 2)), M)
def case_mapId__pe_12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "M" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "map") [(.capture [(.emptySequence 0), (.capture [.num 1, .num 2])]), .resolve "M"])])
#guard obs case_mapId__pe_12 == "err arity"

-- mapId__ppe1_2: M(a) = a \n map((((), 1), 2), M)
def case_mapId__ppe1_2 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "M" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "map") [(.capture [(.capture [(.emptySequence 0), .num 1]), .num 2]), .resolve "M"])])
#guard obs case_mapId__ppe1_2 == "ok raw=L[S[S[], 1], 2] n=1"

-- mapId__p12_e: M(a) = a \n map(((1, 2), ()), M)
def case_mapId__p12_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "M" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "map") [(.capture [(.capture [.num 1, .num 2]), (.emptySequence 0)]), .resolve "M"])])
#guard obs case_mapId__p12_e == "err arity"

-- mapId__ppe: M(a) = a \n map((()), M)
def case_mapId__ppe : Expr :=
  .algorithmExpr (alg [] [] [privateProp "M" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "map") [(.emptySequence 0), .resolve "M"])])
#guard obs case_mapId__ppe == "ok raw=L[] n=1"

-- mapId__pp1: M(a) = a \n map(((1)), M)
def case_mapId__pp1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "M" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "map") [.num 1, .resolve "M"])])
#guard obs case_mapId__pp1 == "ok raw=L[1] n=1"

-- mapId__ppp12: M(a) = a \n map((((1, 2))), M)
def case_mapId__ppp12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "M" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "map") [(.capture [.num 1, .num 2]), .resolve "M"])])
#guard obs case_mapId__ppp12 == "ok raw=L[1, 2] n=1"

-- mapId__le: M(a) = a \n map([], M)
def case_mapId__le : Expr :=
  .algorithmExpr (alg [] [] [privateProp "M" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "map") [(.listLiteral []), .resolve "M"])])
#guard obs case_mapId__le == "ok raw=L[] n=1"

-- mapId__l7: M(a) = a \n map([7], M)
def case_mapId__l7 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "M" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "map") [(.listLiteral [.num 7]), .resolve "M"])])
#guard obs case_mapId__l7 == "ok raw=L[7] n=1"

-- mapId__l12: M(a) = a \n map([1, 2], M)
def case_mapId__l12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "M" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "map") [(.listLiteral [.num 1, .num 2]), .resolve "M"])])
#guard obs case_mapId__l12 == "ok raw=L[1, 2] n=1"

-- mapId__l12_3: M(a) = a \n map([[1, 2], 3], M)
def case_mapId__l12_3 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "M" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "map") [(.listLiteral [(.listLiteral [.num 1, .num 2]), .num 3]), .resolve "M"])])
#guard obs case_mapId__l12_3 == "ok raw=L[L[1, 2], 3] n=1"

-- mapId__lle: M(a) = a \n map([[]], M)
def case_mapId__lle : Expr :=
  .algorithmExpr (alg [] [] [privateProp "M" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "map") [(.listLiteral [(.listLiteral [])]), .resolve "M"])])
#guard obs case_mapId__lle == "ok raw=L[L[]] n=1"

-- mapId__l_e: M(a) = a \n map([()], M)
def case_mapId__l_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "M" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "map") [(.listLiteral [(.emptySequence 0)]), .resolve "M"])])
#guard obs case_mapId__l_e == "err arity"

-- mapId__l_p12: M(a) = a \n map([(1, 2)], M)
def case_mapId__l_p12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "M" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "map") [(.listLiteral [(.capture [.num 1, .num 2])]), .resolve "M"])])
#guard obs case_mapId__l_p12 == "ok raw=L[S[1, 2]] n=1"

-- mapId__p_l12: M(a) = a \n map(([1, 2], 3), M)
def case_mapId__p_l12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "M" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "map") [(.capture [(.listLiteral [.num 1, .num 2]), .num 3]), .resolve "M"])])
#guard obs case_mapId__p_l12 == "ok raw=L[L[1, 2], 3] n=1"

-- mapId__pl1: M(a) = a \n map(([1]), M)
def case_mapId__pl1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "M" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "map") [(.listLiteral [.num 1]), .resolve "M"])])
#guard obs case_mapId__pl1 == "ok raw=L[1] n=1"

-- patternHead__e: P((h, *t)) = [h, t] \n P(())
def case_patternHead__e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [(.listLiteral [.param "h", .param "t"])])] [(.call (.resolve "P") [(.emptySequence 0)])])
#guard obs case_patternHead__e == "err arity"

-- patternHead__n0: P((h, *t)) = [h, t] \n P(0)
def case_patternHead__n0 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [(.listLiteral [.param "h", .param "t"])])] [(.call (.resolve "P") [.num 0])])
#guard obs case_patternHead__n0 == "ok raw=L[0, L[]] n=1"

-- patternHead__n1: P((h, *t)) = [h, t] \n P(1)
def case_patternHead__n1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [(.listLiteral [.param "h", .param "t"])])] [(.call (.resolve "P") [.num 1])])
#guard obs case_patternHead__n1 == "ok raw=L[1, L[]] n=1"

-- patternHead__bt: P((h, *t)) = [h, t] \n P(true)
def case_patternHead__bt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [(.listLiteral [.param "h", .param "t"])])] [(.call (.resolve "P") [.boolLiteral true])])
#guard obs case_patternHead__bt == "ok raw=L[true, L[]] n=1"

-- patternHead__bf: P((h, *t)) = [h, t] \n P(false)
def case_patternHead__bf : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [(.listLiteral [.param "h", .param "t"])])] [(.call (.resolve "P") [.boolLiteral false])])
#guard obs case_patternHead__bf == "ok raw=L[false, L[]] n=1"

-- patternHead__pbt: P((h, *t)) = [h, t] \n P((true))
def case_patternHead__pbt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [(.listLiteral [.param "h", .param "t"])])] [(.call (.resolve "P") [.boolLiteral true])])
#guard obs case_patternHead__pbt == "ok raw=L[true, L[]] n=1"

-- patternHead__pbt_e: P((h, *t)) = [h, t] \n P((true, ()))
def case_patternHead__pbt_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [(.listLiteral [.param "h", .param "t"])])] [(.call (.resolve "P") [(.capture [.boolLiteral true, (.emptySequence 0)])])])
#guard obs case_patternHead__pbt_e == "ok raw=L[true, L[S[]]] n=1"

-- patternHead__pbt_1: P((h, *t)) = [h, t] \n P((true, 1))
def case_patternHead__pbt_1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [(.listLiteral [.param "h", .param "t"])])] [(.call (.resolve "P") [(.capture [.boolLiteral true, .num 1])])])
#guard obs case_patternHead__pbt_1 == "ok raw=L[true, L[1]] n=1"

-- patternHead__lbt: P((h, *t)) = [h, t] \n P([true])
def case_patternHead__lbt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [(.listLiteral [.param "h", .param "t"])])] [(.call (.resolve "P") [(.listLiteral [.boolLiteral true])])])
#guard obs case_patternHead__lbt == "ok raw=L[true, L[]] n=1"

-- patternHead__lbt_bf: P((h, *t)) = [h, t] \n P([true, false])
def case_patternHead__lbt_bf : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [(.listLiteral [.param "h", .param "t"])])] [(.call (.resolve "P") [(.listLiteral [.boolLiteral true, .boolLiteral false])])])
#guard obs case_patternHead__lbt_bf == "ok raw=L[true, L[false]] n=1"

-- patternHead__lpbt_1: P((h, *t)) = [h, t] \n P([(true, 1)])
def case_patternHead__lpbt_1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [(.listLiteral [.param "h", .param "t"])])] [(.call (.resolve "P") [(.listLiteral [(.capture [.boolLiteral true, .num 1])])])])
#guard obs case_patternHead__lpbt_1 == "ok raw=L[S[true, 1], L[]] n=1"

-- patternHead__p1: P((h, *t)) = [h, t] \n P((1))
def case_patternHead__p1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [(.listLiteral [.param "h", .param "t"])])] [(.call (.resolve "P") [.num 1])])
#guard obs case_patternHead__p1 == "ok raw=L[1, L[]] n=1"

-- patternHead__p12: P((h, *t)) = [h, t] \n P((1, 2))
def case_patternHead__p12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [(.listLiteral [.param "h", .param "t"])])] [(.call (.resolve "P") [(.capture [.num 1, .num 2])])])
#guard obs case_patternHead__p12 == "ok raw=L[1, L[2]] n=1"

-- patternHead__p123: P((h, *t)) = [h, t] \n P((1, 2, 3))
def case_patternHead__p123 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [(.listLiteral [.param "h", .param "t"])])] [(.call (.resolve "P") [(.capture [.num 1, .num 2, .num 3])])])
#guard obs case_patternHead__p123 == "ok raw=L[1, L[2, 3]] n=1"

-- patternHead__pee: P((h, *t)) = [h, t] \n P(((), ()))
def case_patternHead__pee : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [(.listLiteral [.param "h", .param "t"])])] [(.call (.resolve "P") [(.capture [(.emptySequence 0), (.emptySequence 0)])])])
#guard obs case_patternHead__pee == "ok raw=L[S[], L[S[]]] n=1"

-- patternHead__pe1: P((h, *t)) = [h, t] \n P(((), 1))
def case_patternHead__pe1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [(.listLiteral [.param "h", .param "t"])])] [(.call (.resolve "P") [(.capture [(.emptySequence 0), .num 1])])])
#guard obs case_patternHead__pe1 == "ok raw=L[S[], L[1]] n=1"

-- patternHead__p1e: P((h, *t)) = [h, t] \n P((1, ()))
def case_patternHead__p1e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [(.listLiteral [.param "h", .param "t"])])] [(.call (.resolve "P") [(.capture [.num 1, (.emptySequence 0)])])])
#guard obs case_patternHead__p1e == "ok raw=L[1, L[S[]]] n=1"

-- patternHead__p12_3: P((h, *t)) = [h, t] \n P(((1, 2), 3))
def case_patternHead__p12_3 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [(.listLiteral [.param "h", .param "t"])])] [(.call (.resolve "P") [(.capture [(.capture [.num 1, .num 2]), .num 3])])])
#guard obs case_patternHead__p12_3 == "ok raw=L[S[1, 2], L[3]] n=1"

-- patternHead__p12_34: P((h, *t)) = [h, t] \n P(((1, 2), (3, 4)))
def case_patternHead__p12_34 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [(.listLiteral [.param "h", .param "t"])])] [(.call (.resolve "P") [(.capture [(.capture [.num 1, .num 2]), (.capture [.num 3, .num 4])])])])
#guard obs case_patternHead__p12_34 == "ok raw=L[S[1, 2], L[S[3, 4]]] n=1"

-- patternHead__pe_12: P((h, *t)) = [h, t] \n P(((), (1, 2)))
def case_patternHead__pe_12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [(.listLiteral [.param "h", .param "t"])])] [(.call (.resolve "P") [(.capture [(.emptySequence 0), (.capture [.num 1, .num 2])])])])
#guard obs case_patternHead__pe_12 == "ok raw=L[S[], L[S[1, 2]]] n=1"

-- patternHead__ppe1_2: P((h, *t)) = [h, t] \n P((((), 1), 2))
def case_patternHead__ppe1_2 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [(.listLiteral [.param "h", .param "t"])])] [(.call (.resolve "P") [(.capture [(.capture [(.emptySequence 0), .num 1]), .num 2])])])
#guard obs case_patternHead__ppe1_2 == "ok raw=L[S[S[], 1], L[2]] n=1"

-- patternHead__p12_e: P((h, *t)) = [h, t] \n P(((1, 2), ()))
def case_patternHead__p12_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [(.listLiteral [.param "h", .param "t"])])] [(.call (.resolve "P") [(.capture [(.capture [.num 1, .num 2]), (.emptySequence 0)])])])
#guard obs case_patternHead__p12_e == "ok raw=L[S[1, 2], L[S[]]] n=1"

-- patternHead__ppe: P((h, *t)) = [h, t] \n P((()))
def case_patternHead__ppe : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [(.listLiteral [.param "h", .param "t"])])] [(.call (.resolve "P") [(.emptySequence 0)])])
#guard obs case_patternHead__ppe == "err arity"

-- patternHead__pp1: P((h, *t)) = [h, t] \n P(((1)))
def case_patternHead__pp1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [(.listLiteral [.param "h", .param "t"])])] [(.call (.resolve "P") [.num 1])])
#guard obs case_patternHead__pp1 == "ok raw=L[1, L[]] n=1"

-- patternHead__ppp12: P((h, *t)) = [h, t] \n P((((1, 2))))
def case_patternHead__ppp12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [(.listLiteral [.param "h", .param "t"])])] [(.call (.resolve "P") [(.capture [.num 1, .num 2])])])
#guard obs case_patternHead__ppp12 == "ok raw=L[1, L[2]] n=1"

-- patternHead__le: P((h, *t)) = [h, t] \n P([])
def case_patternHead__le : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [(.listLiteral [.param "h", .param "t"])])] [(.call (.resolve "P") [(.listLiteral [])])])
#guard obs case_patternHead__le == "err arity"

-- patternHead__l7: P((h, *t)) = [h, t] \n P([7])
def case_patternHead__l7 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [(.listLiteral [.param "h", .param "t"])])] [(.call (.resolve "P") [(.listLiteral [.num 7])])])
#guard obs case_patternHead__l7 == "ok raw=L[7, L[]] n=1"

-- patternHead__l12: P((h, *t)) = [h, t] \n P([1, 2])
def case_patternHead__l12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [(.listLiteral [.param "h", .param "t"])])] [(.call (.resolve "P") [(.listLiteral [.num 1, .num 2])])])
#guard obs case_patternHead__l12 == "ok raw=L[1, L[2]] n=1"

-- patternHead__l12_3: P((h, *t)) = [h, t] \n P([[1, 2], 3])
def case_patternHead__l12_3 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [(.listLiteral [.param "h", .param "t"])])] [(.call (.resolve "P") [(.listLiteral [(.listLiteral [.num 1, .num 2]), .num 3])])])
#guard obs case_patternHead__l12_3 == "ok raw=L[L[1, 2], L[3]] n=1"

-- patternHead__lle: P((h, *t)) = [h, t] \n P([[]])
def case_patternHead__lle : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [(.listLiteral [.param "h", .param "t"])])] [(.call (.resolve "P") [(.listLiteral [(.listLiteral [])])])])
#guard obs case_patternHead__lle == "ok raw=L[L[], L[]] n=1"

-- patternHead__l_e: P((h, *t)) = [h, t] \n P([()])
def case_patternHead__l_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [(.listLiteral [.param "h", .param "t"])])] [(.call (.resolve "P") [(.listLiteral [(.emptySequence 0)])])])
#guard obs case_patternHead__l_e == "ok raw=L[S[], L[]] n=1"

-- patternHead__l_p12: P((h, *t)) = [h, t] \n P([(1, 2)])
def case_patternHead__l_p12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [(.listLiteral [.param "h", .param "t"])])] [(.call (.resolve "P") [(.listLiteral [(.capture [.num 1, .num 2])])])])
#guard obs case_patternHead__l_p12 == "ok raw=L[S[1, 2], L[]] n=1"

-- patternHead__p_l12: P((h, *t)) = [h, t] \n P(([1, 2], 3))
def case_patternHead__p_l12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [(.listLiteral [.param "h", .param "t"])])] [(.call (.resolve "P") [(.capture [(.listLiteral [.num 1, .num 2]), .num 3])])])
#guard obs case_patternHead__p_l12 == "ok raw=L[L[1, 2], L[3]] n=1"

-- patternHead__pl1: P((h, *t)) = [h, t] \n P(([1]))
def case_patternHead__pl1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [(.listLiteral [.param "h", .param "t"])])] [(.call (.resolve "P") [(.listLiteral [.num 1])])])
#guard obs case_patternHead__pl1 == "ok raw=L[1, L[]] n=1"

-- patternHeadMap__e: P((h, *t)) = [h, t] \n map([()], P)
def case_patternHeadMap__e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [(.listLiteral [.param "h", .param "t"])])] [(.call (.resolve "map") [(.listLiteral [(.emptySequence 0)]), .resolve "P"])])
#guard obs case_patternHeadMap__e == "err arity"

-- patternHeadMap__n0: P((h, *t)) = [h, t] \n map([0], P)
def case_patternHeadMap__n0 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [(.listLiteral [.param "h", .param "t"])])] [(.call (.resolve "map") [(.listLiteral [.num 0]), .resolve "P"])])
#guard obs case_patternHeadMap__n0 == "ok raw=L[L[0, L[]]] n=1"

-- patternHeadMap__n1: P((h, *t)) = [h, t] \n map([1], P)
def case_patternHeadMap__n1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [(.listLiteral [.param "h", .param "t"])])] [(.call (.resolve "map") [(.listLiteral [.num 1]), .resolve "P"])])
#guard obs case_patternHeadMap__n1 == "ok raw=L[L[1, L[]]] n=1"

-- patternHeadMap__bt: P((h, *t)) = [h, t] \n map([true], P)
def case_patternHeadMap__bt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [(.listLiteral [.param "h", .param "t"])])] [(.call (.resolve "map") [(.listLiteral [.boolLiteral true]), .resolve "P"])])
#guard obs case_patternHeadMap__bt == "ok raw=L[L[true, L[]]] n=1"

-- patternHeadMap__bf: P((h, *t)) = [h, t] \n map([false], P)
def case_patternHeadMap__bf : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [(.listLiteral [.param "h", .param "t"])])] [(.call (.resolve "map") [(.listLiteral [.boolLiteral false]), .resolve "P"])])
#guard obs case_patternHeadMap__bf == "ok raw=L[L[false, L[]]] n=1"

-- patternHeadMap__pbt: P((h, *t)) = [h, t] \n map([(true)], P)
def case_patternHeadMap__pbt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [(.listLiteral [.param "h", .param "t"])])] [(.call (.resolve "map") [(.listLiteral [.boolLiteral true]), .resolve "P"])])
#guard obs case_patternHeadMap__pbt == "ok raw=L[L[true, L[]]] n=1"

-- patternHeadMap__pbt_e: P((h, *t)) = [h, t] \n map([(true, ())], P)
def case_patternHeadMap__pbt_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [(.listLiteral [.param "h", .param "t"])])] [(.call (.resolve "map") [(.listLiteral [(.capture [.boolLiteral true, (.emptySequence 0)])]), .resolve "P"])])
#guard obs case_patternHeadMap__pbt_e == "ok raw=L[L[true, L[S[]]]] n=1"

-- patternHeadMap__pbt_1: P((h, *t)) = [h, t] \n map([(true, 1)], P)
def case_patternHeadMap__pbt_1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [(.listLiteral [.param "h", .param "t"])])] [(.call (.resolve "map") [(.listLiteral [(.capture [.boolLiteral true, .num 1])]), .resolve "P"])])
#guard obs case_patternHeadMap__pbt_1 == "ok raw=L[L[true, L[1]]] n=1"

-- patternHeadMap__lbt: P((h, *t)) = [h, t] \n map([[true]], P)
def case_patternHeadMap__lbt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [(.listLiteral [.param "h", .param "t"])])] [(.call (.resolve "map") [(.listLiteral [(.listLiteral [.boolLiteral true])]), .resolve "P"])])
#guard obs case_patternHeadMap__lbt == "ok raw=L[L[true, L[]]] n=1"

-- patternHeadMap__lbt_bf: P((h, *t)) = [h, t] \n map([[true, false]], P)
def case_patternHeadMap__lbt_bf : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [(.listLiteral [.param "h", .param "t"])])] [(.call (.resolve "map") [(.listLiteral [(.listLiteral [.boolLiteral true, .boolLiteral false])]), .resolve "P"])])
#guard obs case_patternHeadMap__lbt_bf == "ok raw=L[L[true, L[false]]] n=1"

-- patternHeadMap__lpbt_1: P((h, *t)) = [h, t] \n map([[(true, 1)]], P)
def case_patternHeadMap__lpbt_1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [(.listLiteral [.param "h", .param "t"])])] [(.call (.resolve "map") [(.listLiteral [(.listLiteral [(.capture [.boolLiteral true, .num 1])])]), .resolve "P"])])
#guard obs case_patternHeadMap__lpbt_1 == "ok raw=L[L[S[true, 1], L[]]] n=1"

-- patternHeadMap__p1: P((h, *t)) = [h, t] \n map([(1)], P)
def case_patternHeadMap__p1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [(.listLiteral [.param "h", .param "t"])])] [(.call (.resolve "map") [(.listLiteral [.num 1]), .resolve "P"])])
#guard obs case_patternHeadMap__p1 == "ok raw=L[L[1, L[]]] n=1"

-- patternHeadMap__p12: P((h, *t)) = [h, t] \n map([(1, 2)], P)
def case_patternHeadMap__p12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [(.listLiteral [.param "h", .param "t"])])] [(.call (.resolve "map") [(.listLiteral [(.capture [.num 1, .num 2])]), .resolve "P"])])
#guard obs case_patternHeadMap__p12 == "ok raw=L[L[1, L[2]]] n=1"

-- patternHeadMap__p123: P((h, *t)) = [h, t] \n map([(1, 2, 3)], P)
def case_patternHeadMap__p123 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [(.listLiteral [.param "h", .param "t"])])] [(.call (.resolve "map") [(.listLiteral [(.capture [.num 1, .num 2, .num 3])]), .resolve "P"])])
#guard obs case_patternHeadMap__p123 == "ok raw=L[L[1, L[2, 3]]] n=1"

-- patternHeadMap__pee: P((h, *t)) = [h, t] \n map([((), ())], P)
def case_patternHeadMap__pee : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [(.listLiteral [.param "h", .param "t"])])] [(.call (.resolve "map") [(.listLiteral [(.capture [(.emptySequence 0), (.emptySequence 0)])]), .resolve "P"])])
#guard obs case_patternHeadMap__pee == "ok raw=L[L[S[], L[S[]]]] n=1"

-- patternHeadMap__pe1: P((h, *t)) = [h, t] \n map([((), 1)], P)
def case_patternHeadMap__pe1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [(.listLiteral [.param "h", .param "t"])])] [(.call (.resolve "map") [(.listLiteral [(.capture [(.emptySequence 0), .num 1])]), .resolve "P"])])
#guard obs case_patternHeadMap__pe1 == "ok raw=L[L[S[], L[1]]] n=1"

-- patternHeadMap__p1e: P((h, *t)) = [h, t] \n map([(1, ())], P)
def case_patternHeadMap__p1e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [(.listLiteral [.param "h", .param "t"])])] [(.call (.resolve "map") [(.listLiteral [(.capture [.num 1, (.emptySequence 0)])]), .resolve "P"])])
#guard obs case_patternHeadMap__p1e == "ok raw=L[L[1, L[S[]]]] n=1"

-- patternHeadMap__p12_3: P((h, *t)) = [h, t] \n map([((1, 2), 3)], P)
def case_patternHeadMap__p12_3 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [(.listLiteral [.param "h", .param "t"])])] [(.call (.resolve "map") [(.listLiteral [(.capture [(.capture [.num 1, .num 2]), .num 3])]), .resolve "P"])])
#guard obs case_patternHeadMap__p12_3 == "ok raw=L[L[S[1, 2], L[3]]] n=1"

-- patternHeadMap__p12_34: P((h, *t)) = [h, t] \n map([((1, 2), (3, 4))], P)
def case_patternHeadMap__p12_34 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [(.listLiteral [.param "h", .param "t"])])] [(.call (.resolve "map") [(.listLiteral [(.capture [(.capture [.num 1, .num 2]), (.capture [.num 3, .num 4])])]), .resolve "P"])])
#guard obs case_patternHeadMap__p12_34 == "ok raw=L[L[S[1, 2], L[S[3, 4]]]] n=1"

-- patternHeadMap__pe_12: P((h, *t)) = [h, t] \n map([((), (1, 2))], P)
def case_patternHeadMap__pe_12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [(.listLiteral [.param "h", .param "t"])])] [(.call (.resolve "map") [(.listLiteral [(.capture [(.emptySequence 0), (.capture [.num 1, .num 2])])]), .resolve "P"])])
#guard obs case_patternHeadMap__pe_12 == "ok raw=L[L[S[], L[S[1, 2]]]] n=1"

-- patternHeadMap__ppe1_2: P((h, *t)) = [h, t] \n map([(((), 1), 2)], P)
def case_patternHeadMap__ppe1_2 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [(.listLiteral [.param "h", .param "t"])])] [(.call (.resolve "map") [(.listLiteral [(.capture [(.capture [(.emptySequence 0), .num 1]), .num 2])]), .resolve "P"])])
#guard obs case_patternHeadMap__ppe1_2 == "ok raw=L[L[S[S[], 1], L[2]]] n=1"

-- patternHeadMap__p12_e: P((h, *t)) = [h, t] \n map([((1, 2), ())], P)
def case_patternHeadMap__p12_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [(.listLiteral [.param "h", .param "t"])])] [(.call (.resolve "map") [(.listLiteral [(.capture [(.capture [.num 1, .num 2]), (.emptySequence 0)])]), .resolve "P"])])
#guard obs case_patternHeadMap__p12_e == "ok raw=L[L[S[1, 2], L[S[]]]] n=1"

-- patternHeadMap__ppe: P((h, *t)) = [h, t] \n map([(())], P)
def case_patternHeadMap__ppe : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [(.listLiteral [.param "h", .param "t"])])] [(.call (.resolve "map") [(.listLiteral [(.emptySequence 0)]), .resolve "P"])])
#guard obs case_patternHeadMap__ppe == "err arity"

-- patternHeadMap__pp1: P((h, *t)) = [h, t] \n map([((1))], P)
def case_patternHeadMap__pp1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [(.listLiteral [.param "h", .param "t"])])] [(.call (.resolve "map") [(.listLiteral [.num 1]), .resolve "P"])])
#guard obs case_patternHeadMap__pp1 == "ok raw=L[L[1, L[]]] n=1"

-- patternHeadMap__ppp12: P((h, *t)) = [h, t] \n map([(((1, 2)))], P)
def case_patternHeadMap__ppp12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [(.listLiteral [.param "h", .param "t"])])] [(.call (.resolve "map") [(.listLiteral [(.capture [.num 1, .num 2])]), .resolve "P"])])
#guard obs case_patternHeadMap__ppp12 == "ok raw=L[L[1, L[2]]] n=1"

-- patternHeadMap__le: P((h, *t)) = [h, t] \n map([[]], P)
def case_patternHeadMap__le : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [(.listLiteral [.param "h", .param "t"])])] [(.call (.resolve "map") [(.listLiteral [(.listLiteral [])]), .resolve "P"])])
#guard obs case_patternHeadMap__le == "err arity"

-- patternHeadMap__l7: P((h, *t)) = [h, t] \n map([[7]], P)
def case_patternHeadMap__l7 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [(.listLiteral [.param "h", .param "t"])])] [(.call (.resolve "map") [(.listLiteral [(.listLiteral [.num 7])]), .resolve "P"])])
#guard obs case_patternHeadMap__l7 == "ok raw=L[L[7, L[]]] n=1"

-- patternHeadMap__l12: P((h, *t)) = [h, t] \n map([[1, 2]], P)
def case_patternHeadMap__l12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [(.listLiteral [.param "h", .param "t"])])] [(.call (.resolve "map") [(.listLiteral [(.listLiteral [.num 1, .num 2])]), .resolve "P"])])
#guard obs case_patternHeadMap__l12 == "ok raw=L[L[1, L[2]]] n=1"

-- patternHeadMap__l12_3: P((h, *t)) = [h, t] \n map([[[1, 2], 3]], P)
def case_patternHeadMap__l12_3 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [(.listLiteral [.param "h", .param "t"])])] [(.call (.resolve "map") [(.listLiteral [(.listLiteral [(.listLiteral [.num 1, .num 2]), .num 3])]), .resolve "P"])])
#guard obs case_patternHeadMap__l12_3 == "ok raw=L[L[L[1, 2], L[3]]] n=1"

-- patternHeadMap__lle: P((h, *t)) = [h, t] \n map([[[]]], P)
def case_patternHeadMap__lle : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [(.listLiteral [.param "h", .param "t"])])] [(.call (.resolve "map") [(.listLiteral [(.listLiteral [(.listLiteral [])])]), .resolve "P"])])
#guard obs case_patternHeadMap__lle == "ok raw=L[L[L[], L[]]] n=1"

-- patternHeadMap__l_e: P((h, *t)) = [h, t] \n map([[()]], P)
def case_patternHeadMap__l_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [(.listLiteral [.param "h", .param "t"])])] [(.call (.resolve "map") [(.listLiteral [(.listLiteral [(.emptySequence 0)])]), .resolve "P"])])
#guard obs case_patternHeadMap__l_e == "ok raw=L[L[S[], L[]]] n=1"

-- patternHeadMap__l_p12: P((h, *t)) = [h, t] \n map([[(1, 2)]], P)
def case_patternHeadMap__l_p12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [(.listLiteral [.param "h", .param "t"])])] [(.call (.resolve "map") [(.listLiteral [(.listLiteral [(.capture [.num 1, .num 2])])]), .resolve "P"])])
#guard obs case_patternHeadMap__l_p12 == "ok raw=L[L[S[1, 2], L[]]] n=1"

-- patternHeadMap__p_l12: P((h, *t)) = [h, t] \n map([([1, 2], 3)], P)
def case_patternHeadMap__p_l12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [(.listLiteral [.param "h", .param "t"])])] [(.call (.resolve "map") [(.listLiteral [(.capture [(.listLiteral [.num 1, .num 2]), .num 3])]), .resolve "P"])])
#guard obs case_patternHeadMap__p_l12 == "ok raw=L[L[L[1, 2], L[3]]] n=1"

-- patternHeadMap__pl1: P((h, *t)) = [h, t] \n map([([1])], P)
def case_patternHeadMap__pl1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "h" }, .capture { name := "t", kind := .collecting }]] [] [] [(.listLiteral [.param "h", .param "t"])])] [(.call (.resolve "map") [(.listLiteral [(.listLiteral [.num 1])]), .resolve "P"])])
#guard obs case_patternHeadMap__pl1 == "ok raw=L[L[1, L[]]] n=1"

-- patternPair__e: P((x, y)) = [x, y] \n P(())
def case_patternPair__e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [(.listLiteral [.param "x", .param "y"])])] [(.call (.resolve "P") [(.emptySequence 0)])])
#guard obs case_patternPair__e == "err arity"

-- patternPair__n0: P((x, y)) = [x, y] \n P(0)
def case_patternPair__n0 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [(.listLiteral [.param "x", .param "y"])])] [(.call (.resolve "P") [.num 0])])
#guard obs case_patternPair__n0 == "err arity"

-- patternPair__n1: P((x, y)) = [x, y] \n P(1)
def case_patternPair__n1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [(.listLiteral [.param "x", .param "y"])])] [(.call (.resolve "P") [.num 1])])
#guard obs case_patternPair__n1 == "err arity"

-- patternPair__bt: P((x, y)) = [x, y] \n P(true)
def case_patternPair__bt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [(.listLiteral [.param "x", .param "y"])])] [(.call (.resolve "P") [.boolLiteral true])])
#guard obs case_patternPair__bt == "err arity"

-- patternPair__bf: P((x, y)) = [x, y] \n P(false)
def case_patternPair__bf : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [(.listLiteral [.param "x", .param "y"])])] [(.call (.resolve "P") [.boolLiteral false])])
#guard obs case_patternPair__bf == "err arity"

-- patternPair__pbt: P((x, y)) = [x, y] \n P((true))
def case_patternPair__pbt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [(.listLiteral [.param "x", .param "y"])])] [(.call (.resolve "P") [.boolLiteral true])])
#guard obs case_patternPair__pbt == "err arity"

-- patternPair__pbt_e: P((x, y)) = [x, y] \n P((true, ()))
def case_patternPair__pbt_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [(.listLiteral [.param "x", .param "y"])])] [(.call (.resolve "P") [(.capture [.boolLiteral true, (.emptySequence 0)])])])
#guard obs case_patternPair__pbt_e == "ok raw=L[true, S[]] n=1"

-- patternPair__pbt_1: P((x, y)) = [x, y] \n P((true, 1))
def case_patternPair__pbt_1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [(.listLiteral [.param "x", .param "y"])])] [(.call (.resolve "P") [(.capture [.boolLiteral true, .num 1])])])
#guard obs case_patternPair__pbt_1 == "ok raw=L[true, 1] n=1"

-- patternPair__lbt: P((x, y)) = [x, y] \n P([true])
def case_patternPair__lbt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [(.listLiteral [.param "x", .param "y"])])] [(.call (.resolve "P") [(.listLiteral [.boolLiteral true])])])
#guard obs case_patternPair__lbt == "err arity"

-- patternPair__lbt_bf: P((x, y)) = [x, y] \n P([true, false])
def case_patternPair__lbt_bf : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [(.listLiteral [.param "x", .param "y"])])] [(.call (.resolve "P") [(.listLiteral [.boolLiteral true, .boolLiteral false])])])
#guard obs case_patternPair__lbt_bf == "ok raw=L[true, false] n=1"

-- patternPair__lpbt_1: P((x, y)) = [x, y] \n P([(true, 1)])
def case_patternPair__lpbt_1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [(.listLiteral [.param "x", .param "y"])])] [(.call (.resolve "P") [(.listLiteral [(.capture [.boolLiteral true, .num 1])])])])
#guard obs case_patternPair__lpbt_1 == "err arity"

-- patternPair__p1: P((x, y)) = [x, y] \n P((1))
def case_patternPair__p1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [(.listLiteral [.param "x", .param "y"])])] [(.call (.resolve "P") [.num 1])])
#guard obs case_patternPair__p1 == "err arity"

-- patternPair__p12: P((x, y)) = [x, y] \n P((1, 2))
def case_patternPair__p12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [(.listLiteral [.param "x", .param "y"])])] [(.call (.resolve "P") [(.capture [.num 1, .num 2])])])
#guard obs case_patternPair__p12 == "ok raw=L[1, 2] n=1"

-- patternPair__p123: P((x, y)) = [x, y] \n P((1, 2, 3))
def case_patternPair__p123 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [(.listLiteral [.param "x", .param "y"])])] [(.call (.resolve "P") [(.capture [.num 1, .num 2, .num 3])])])
#guard obs case_patternPair__p123 == "err arity"

-- patternPair__pee: P((x, y)) = [x, y] \n P(((), ()))
def case_patternPair__pee : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [(.listLiteral [.param "x", .param "y"])])] [(.call (.resolve "P") [(.capture [(.emptySequence 0), (.emptySequence 0)])])])
#guard obs case_patternPair__pee == "ok raw=L[S[], S[]] n=1"

-- patternPair__pe1: P((x, y)) = [x, y] \n P(((), 1))
def case_patternPair__pe1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [(.listLiteral [.param "x", .param "y"])])] [(.call (.resolve "P") [(.capture [(.emptySequence 0), .num 1])])])
#guard obs case_patternPair__pe1 == "ok raw=L[S[], 1] n=1"

-- patternPair__p1e: P((x, y)) = [x, y] \n P((1, ()))
def case_patternPair__p1e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [(.listLiteral [.param "x", .param "y"])])] [(.call (.resolve "P") [(.capture [.num 1, (.emptySequence 0)])])])
#guard obs case_patternPair__p1e == "ok raw=L[1, S[]] n=1"

-- patternPair__p12_3: P((x, y)) = [x, y] \n P(((1, 2), 3))
def case_patternPair__p12_3 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [(.listLiteral [.param "x", .param "y"])])] [(.call (.resolve "P") [(.capture [(.capture [.num 1, .num 2]), .num 3])])])
#guard obs case_patternPair__p12_3 == "ok raw=L[S[1, 2], 3] n=1"

-- patternPair__p12_34: P((x, y)) = [x, y] \n P(((1, 2), (3, 4)))
def case_patternPair__p12_34 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [(.listLiteral [.param "x", .param "y"])])] [(.call (.resolve "P") [(.capture [(.capture [.num 1, .num 2]), (.capture [.num 3, .num 4])])])])
#guard obs case_patternPair__p12_34 == "ok raw=L[S[1, 2], S[3, 4]] n=1"

-- patternPair__pe_12: P((x, y)) = [x, y] \n P(((), (1, 2)))
def case_patternPair__pe_12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [(.listLiteral [.param "x", .param "y"])])] [(.call (.resolve "P") [(.capture [(.emptySequence 0), (.capture [.num 1, .num 2])])])])
#guard obs case_patternPair__pe_12 == "ok raw=L[S[], S[1, 2]] n=1"

-- patternPair__ppe1_2: P((x, y)) = [x, y] \n P((((), 1), 2))
def case_patternPair__ppe1_2 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [(.listLiteral [.param "x", .param "y"])])] [(.call (.resolve "P") [(.capture [(.capture [(.emptySequence 0), .num 1]), .num 2])])])
#guard obs case_patternPair__ppe1_2 == "ok raw=L[S[S[], 1], 2] n=1"

-- patternPair__p12_e: P((x, y)) = [x, y] \n P(((1, 2), ()))
def case_patternPair__p12_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [(.listLiteral [.param "x", .param "y"])])] [(.call (.resolve "P") [(.capture [(.capture [.num 1, .num 2]), (.emptySequence 0)])])])
#guard obs case_patternPair__p12_e == "ok raw=L[S[1, 2], S[]] n=1"

-- patternPair__ppe: P((x, y)) = [x, y] \n P((()))
def case_patternPair__ppe : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [(.listLiteral [.param "x", .param "y"])])] [(.call (.resolve "P") [(.emptySequence 0)])])
#guard obs case_patternPair__ppe == "err arity"

-- patternPair__pp1: P((x, y)) = [x, y] \n P(((1)))
def case_patternPair__pp1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [(.listLiteral [.param "x", .param "y"])])] [(.call (.resolve "P") [.num 1])])
#guard obs case_patternPair__pp1 == "err arity"

-- patternPair__ppp12: P((x, y)) = [x, y] \n P((((1, 2))))
def case_patternPair__ppp12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [(.listLiteral [.param "x", .param "y"])])] [(.call (.resolve "P") [(.capture [.num 1, .num 2])])])
#guard obs case_patternPair__ppp12 == "ok raw=L[1, 2] n=1"

-- patternPair__le: P((x, y)) = [x, y] \n P([])
def case_patternPair__le : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [(.listLiteral [.param "x", .param "y"])])] [(.call (.resolve "P") [(.listLiteral [])])])
#guard obs case_patternPair__le == "err arity"

-- patternPair__l7: P((x, y)) = [x, y] \n P([7])
def case_patternPair__l7 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [(.listLiteral [.param "x", .param "y"])])] [(.call (.resolve "P") [(.listLiteral [.num 7])])])
#guard obs case_patternPair__l7 == "err arity"

-- patternPair__l12: P((x, y)) = [x, y] \n P([1, 2])
def case_patternPair__l12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [(.listLiteral [.param "x", .param "y"])])] [(.call (.resolve "P") [(.listLiteral [.num 1, .num 2])])])
#guard obs case_patternPair__l12 == "ok raw=L[1, 2] n=1"

-- patternPair__l12_3: P((x, y)) = [x, y] \n P([[1, 2], 3])
def case_patternPair__l12_3 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [(.listLiteral [.param "x", .param "y"])])] [(.call (.resolve "P") [(.listLiteral [(.listLiteral [.num 1, .num 2]), .num 3])])])
#guard obs case_patternPair__l12_3 == "ok raw=L[L[1, 2], 3] n=1"

-- patternPair__lle: P((x, y)) = [x, y] \n P([[]])
def case_patternPair__lle : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [(.listLiteral [.param "x", .param "y"])])] [(.call (.resolve "P") [(.listLiteral [(.listLiteral [])])])])
#guard obs case_patternPair__lle == "err arity"

-- patternPair__l_e: P((x, y)) = [x, y] \n P([()])
def case_patternPair__l_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [(.listLiteral [.param "x", .param "y"])])] [(.call (.resolve "P") [(.listLiteral [(.emptySequence 0)])])])
#guard obs case_patternPair__l_e == "err arity"

-- patternPair__l_p12: P((x, y)) = [x, y] \n P([(1, 2)])
def case_patternPair__l_p12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [(.listLiteral [.param "x", .param "y"])])] [(.call (.resolve "P") [(.listLiteral [(.capture [.num 1, .num 2])])])])
#guard obs case_patternPair__l_p12 == "err arity"

-- patternPair__p_l12: P((x, y)) = [x, y] \n P(([1, 2], 3))
def case_patternPair__p_l12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [(.listLiteral [.param "x", .param "y"])])] [(.call (.resolve "P") [(.capture [(.listLiteral [.num 1, .num 2]), .num 3])])])
#guard obs case_patternPair__p_l12 == "ok raw=L[L[1, 2], 3] n=1"

-- patternPair__pl1: P((x, y)) = [x, y] \n P(([1]))
def case_patternPair__pl1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [(.listLiteral [.param "x", .param "y"])])] [(.call (.resolve "P") [(.listLiteral [.num 1])])])
#guard obs case_patternPair__pl1 == "err arity"

-- patternPairMap__e: P((x, y)) = [x, y] \n map([()], P)
def case_patternPairMap__e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [(.listLiteral [.param "x", .param "y"])])] [(.call (.resolve "map") [(.listLiteral [(.emptySequence 0)]), .resolve "P"])])
#guard obs case_patternPairMap__e == "err arity"

-- patternPairMap__n0: P((x, y)) = [x, y] \n map([0], P)
def case_patternPairMap__n0 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [(.listLiteral [.param "x", .param "y"])])] [(.call (.resolve "map") [(.listLiteral [.num 0]), .resolve "P"])])
#guard obs case_patternPairMap__n0 == "err arity"

-- patternPairMap__n1: P((x, y)) = [x, y] \n map([1], P)
def case_patternPairMap__n1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [(.listLiteral [.param "x", .param "y"])])] [(.call (.resolve "map") [(.listLiteral [.num 1]), .resolve "P"])])
#guard obs case_patternPairMap__n1 == "err arity"

-- patternPairMap__bt: P((x, y)) = [x, y] \n map([true], P)
def case_patternPairMap__bt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [(.listLiteral [.param "x", .param "y"])])] [(.call (.resolve "map") [(.listLiteral [.boolLiteral true]), .resolve "P"])])
#guard obs case_patternPairMap__bt == "err arity"

-- patternPairMap__bf: P((x, y)) = [x, y] \n map([false], P)
def case_patternPairMap__bf : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [(.listLiteral [.param "x", .param "y"])])] [(.call (.resolve "map") [(.listLiteral [.boolLiteral false]), .resolve "P"])])
#guard obs case_patternPairMap__bf == "err arity"

-- patternPairMap__pbt: P((x, y)) = [x, y] \n map([(true)], P)
def case_patternPairMap__pbt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [(.listLiteral [.param "x", .param "y"])])] [(.call (.resolve "map") [(.listLiteral [.boolLiteral true]), .resolve "P"])])
#guard obs case_patternPairMap__pbt == "err arity"

-- patternPairMap__pbt_e: P((x, y)) = [x, y] \n map([(true, ())], P)
def case_patternPairMap__pbt_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [(.listLiteral [.param "x", .param "y"])])] [(.call (.resolve "map") [(.listLiteral [(.capture [.boolLiteral true, (.emptySequence 0)])]), .resolve "P"])])
#guard obs case_patternPairMap__pbt_e == "ok raw=L[L[true, S[]]] n=1"

-- patternPairMap__pbt_1: P((x, y)) = [x, y] \n map([(true, 1)], P)
def case_patternPairMap__pbt_1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [(.listLiteral [.param "x", .param "y"])])] [(.call (.resolve "map") [(.listLiteral [(.capture [.boolLiteral true, .num 1])]), .resolve "P"])])
#guard obs case_patternPairMap__pbt_1 == "ok raw=L[L[true, 1]] n=1"

-- patternPairMap__lbt: P((x, y)) = [x, y] \n map([[true]], P)
def case_patternPairMap__lbt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [(.listLiteral [.param "x", .param "y"])])] [(.call (.resolve "map") [(.listLiteral [(.listLiteral [.boolLiteral true])]), .resolve "P"])])
#guard obs case_patternPairMap__lbt == "err arity"

-- patternPairMap__lbt_bf: P((x, y)) = [x, y] \n map([[true, false]], P)
def case_patternPairMap__lbt_bf : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [(.listLiteral [.param "x", .param "y"])])] [(.call (.resolve "map") [(.listLiteral [(.listLiteral [.boolLiteral true, .boolLiteral false])]), .resolve "P"])])
#guard obs case_patternPairMap__lbt_bf == "ok raw=L[L[true, false]] n=1"

-- patternPairMap__lpbt_1: P((x, y)) = [x, y] \n map([[(true, 1)]], P)
def case_patternPairMap__lpbt_1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [(.listLiteral [.param "x", .param "y"])])] [(.call (.resolve "map") [(.listLiteral [(.listLiteral [(.capture [.boolLiteral true, .num 1])])]), .resolve "P"])])
#guard obs case_patternPairMap__lpbt_1 == "err arity"

-- patternPairMap__p1: P((x, y)) = [x, y] \n map([(1)], P)
def case_patternPairMap__p1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [(.listLiteral [.param "x", .param "y"])])] [(.call (.resolve "map") [(.listLiteral [.num 1]), .resolve "P"])])
#guard obs case_patternPairMap__p1 == "err arity"

-- patternPairMap__p12: P((x, y)) = [x, y] \n map([(1, 2)], P)
def case_patternPairMap__p12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [(.listLiteral [.param "x", .param "y"])])] [(.call (.resolve "map") [(.listLiteral [(.capture [.num 1, .num 2])]), .resolve "P"])])
#guard obs case_patternPairMap__p12 == "ok raw=L[L[1, 2]] n=1"

-- patternPairMap__p123: P((x, y)) = [x, y] \n map([(1, 2, 3)], P)
def case_patternPairMap__p123 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [(.listLiteral [.param "x", .param "y"])])] [(.call (.resolve "map") [(.listLiteral [(.capture [.num 1, .num 2, .num 3])]), .resolve "P"])])
#guard obs case_patternPairMap__p123 == "err arity"

-- patternPairMap__pee: P((x, y)) = [x, y] \n map([((), ())], P)
def case_patternPairMap__pee : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [(.listLiteral [.param "x", .param "y"])])] [(.call (.resolve "map") [(.listLiteral [(.capture [(.emptySequence 0), (.emptySequence 0)])]), .resolve "P"])])
#guard obs case_patternPairMap__pee == "ok raw=L[L[S[], S[]]] n=1"

-- patternPairMap__pe1: P((x, y)) = [x, y] \n map([((), 1)], P)
def case_patternPairMap__pe1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [(.listLiteral [.param "x", .param "y"])])] [(.call (.resolve "map") [(.listLiteral [(.capture [(.emptySequence 0), .num 1])]), .resolve "P"])])
#guard obs case_patternPairMap__pe1 == "ok raw=L[L[S[], 1]] n=1"

-- patternPairMap__p1e: P((x, y)) = [x, y] \n map([(1, ())], P)
def case_patternPairMap__p1e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [(.listLiteral [.param "x", .param "y"])])] [(.call (.resolve "map") [(.listLiteral [(.capture [.num 1, (.emptySequence 0)])]), .resolve "P"])])
#guard obs case_patternPairMap__p1e == "ok raw=L[L[1, S[]]] n=1"

-- patternPairMap__p12_3: P((x, y)) = [x, y] \n map([((1, 2), 3)], P)
def case_patternPairMap__p12_3 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [(.listLiteral [.param "x", .param "y"])])] [(.call (.resolve "map") [(.listLiteral [(.capture [(.capture [.num 1, .num 2]), .num 3])]), .resolve "P"])])
#guard obs case_patternPairMap__p12_3 == "ok raw=L[L[S[1, 2], 3]] n=1"

-- patternPairMap__p12_34: P((x, y)) = [x, y] \n map([((1, 2), (3, 4))], P)
def case_patternPairMap__p12_34 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [(.listLiteral [.param "x", .param "y"])])] [(.call (.resolve "map") [(.listLiteral [(.capture [(.capture [.num 1, .num 2]), (.capture [.num 3, .num 4])])]), .resolve "P"])])
#guard obs case_patternPairMap__p12_34 == "ok raw=L[L[S[1, 2], S[3, 4]]] n=1"

-- patternPairMap__pe_12: P((x, y)) = [x, y] \n map([((), (1, 2))], P)
def case_patternPairMap__pe_12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [(.listLiteral [.param "x", .param "y"])])] [(.call (.resolve "map") [(.listLiteral [(.capture [(.emptySequence 0), (.capture [.num 1, .num 2])])]), .resolve "P"])])
#guard obs case_patternPairMap__pe_12 == "ok raw=L[L[S[], S[1, 2]]] n=1"

-- patternPairMap__ppe1_2: P((x, y)) = [x, y] \n map([(((), 1), 2)], P)
def case_patternPairMap__ppe1_2 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [(.listLiteral [.param "x", .param "y"])])] [(.call (.resolve "map") [(.listLiteral [(.capture [(.capture [(.emptySequence 0), .num 1]), .num 2])]), .resolve "P"])])
#guard obs case_patternPairMap__ppe1_2 == "ok raw=L[L[S[S[], 1], 2]] n=1"

-- patternPairMap__p12_e: P((x, y)) = [x, y] \n map([((1, 2), ())], P)
def case_patternPairMap__p12_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [(.listLiteral [.param "x", .param "y"])])] [(.call (.resolve "map") [(.listLiteral [(.capture [(.capture [.num 1, .num 2]), (.emptySequence 0)])]), .resolve "P"])])
#guard obs case_patternPairMap__p12_e == "ok raw=L[L[S[1, 2], S[]]] n=1"

-- patternPairMap__ppe: P((x, y)) = [x, y] \n map([(())], P)
def case_patternPairMap__ppe : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [(.listLiteral [.param "x", .param "y"])])] [(.call (.resolve "map") [(.listLiteral [(.emptySequence 0)]), .resolve "P"])])
#guard obs case_patternPairMap__ppe == "err arity"

-- patternPairMap__pp1: P((x, y)) = [x, y] \n map([((1))], P)
def case_patternPairMap__pp1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [(.listLiteral [.param "x", .param "y"])])] [(.call (.resolve "map") [(.listLiteral [.num 1]), .resolve "P"])])
#guard obs case_patternPairMap__pp1 == "err arity"

-- patternPairMap__ppp12: P((x, y)) = [x, y] \n map([(((1, 2)))], P)
def case_patternPairMap__ppp12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [(.listLiteral [.param "x", .param "y"])])] [(.call (.resolve "map") [(.listLiteral [(.capture [.num 1, .num 2])]), .resolve "P"])])
#guard obs case_patternPairMap__ppp12 == "ok raw=L[L[1, 2]] n=1"

-- patternPairMap__le: P((x, y)) = [x, y] \n map([[]], P)
def case_patternPairMap__le : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [(.listLiteral [.param "x", .param "y"])])] [(.call (.resolve "map") [(.listLiteral [(.listLiteral [])]), .resolve "P"])])
#guard obs case_patternPairMap__le == "err arity"

-- patternPairMap__l7: P((x, y)) = [x, y] \n map([[7]], P)
def case_patternPairMap__l7 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [(.listLiteral [.param "x", .param "y"])])] [(.call (.resolve "map") [(.listLiteral [(.listLiteral [.num 7])]), .resolve "P"])])
#guard obs case_patternPairMap__l7 == "err arity"

-- patternPairMap__l12: P((x, y)) = [x, y] \n map([[1, 2]], P)
def case_patternPairMap__l12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [(.listLiteral [.param "x", .param "y"])])] [(.call (.resolve "map") [(.listLiteral [(.listLiteral [.num 1, .num 2])]), .resolve "P"])])
#guard obs case_patternPairMap__l12 == "ok raw=L[L[1, 2]] n=1"

-- patternPairMap__l12_3: P((x, y)) = [x, y] \n map([[[1, 2], 3]], P)
def case_patternPairMap__l12_3 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [(.listLiteral [.param "x", .param "y"])])] [(.call (.resolve "map") [(.listLiteral [(.listLiteral [(.listLiteral [.num 1, .num 2]), .num 3])]), .resolve "P"])])
#guard obs case_patternPairMap__l12_3 == "ok raw=L[L[L[1, 2], 3]] n=1"

-- patternPairMap__lle: P((x, y)) = [x, y] \n map([[[]]], P)
def case_patternPairMap__lle : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [(.listLiteral [.param "x", .param "y"])])] [(.call (.resolve "map") [(.listLiteral [(.listLiteral [(.listLiteral [])])]), .resolve "P"])])
#guard obs case_patternPairMap__lle == "err arity"

-- patternPairMap__l_e: P((x, y)) = [x, y] \n map([[()]], P)
def case_patternPairMap__l_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [(.listLiteral [.param "x", .param "y"])])] [(.call (.resolve "map") [(.listLiteral [(.listLiteral [(.emptySequence 0)])]), .resolve "P"])])
#guard obs case_patternPairMap__l_e == "err arity"

-- patternPairMap__l_p12: P((x, y)) = [x, y] \n map([[(1, 2)]], P)
def case_patternPairMap__l_p12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [(.listLiteral [.param "x", .param "y"])])] [(.call (.resolve "map") [(.listLiteral [(.listLiteral [(.capture [.num 1, .num 2])])]), .resolve "P"])])
#guard obs case_patternPairMap__l_p12 == "err arity"

-- patternPairMap__p_l12: P((x, y)) = [x, y] \n map([([1, 2], 3)], P)
def case_patternPairMap__p_l12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [(.listLiteral [.param "x", .param "y"])])] [(.call (.resolve "map") [(.listLiteral [(.capture [(.listLiteral [.num 1, .num 2]), .num 3])]), .resolve "P"])])
#guard obs case_patternPairMap__p_l12 == "ok raw=L[L[L[1, 2], 3]] n=1"

-- patternPairMap__pl1: P((x, y)) = [x, y] \n map([([1])], P)
def case_patternPairMap__pl1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "y" }]] [] [] [(.listLiteral [.param "x", .param "y"])])] [(.call (.resolve "map") [(.listLiteral [(.listLiteral [.num 1])]), .resolve "P"])])
#guard obs case_patternPairMap__pl1 == "err arity"

-- filterKeep__e: T(a) = true \n filter((), T)
def case_filterKeep__e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "T" (alg ["a"] [] [] [.boolLiteral true])] [(.call (.resolve "filter") [(.emptySequence 0), .resolve "T"])])
#guard obs case_filterKeep__e == "ok raw=L[] n=1"

-- filterKeep__n0: T(a) = true \n filter(0, T)
def case_filterKeep__n0 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "T" (alg ["a"] [] [] [.boolLiteral true])] [(.call (.resolve "filter") [.num 0, .resolve "T"])])
#guard obs case_filterKeep__n0 == "ok raw=L[0] n=1"

-- filterKeep__n1: T(a) = true \n filter(1, T)
def case_filterKeep__n1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "T" (alg ["a"] [] [] [.boolLiteral true])] [(.call (.resolve "filter") [.num 1, .resolve "T"])])
#guard obs case_filterKeep__n1 == "ok raw=L[1] n=1"

-- filterKeep__bt: T(a) = true \n filter(true, T)
def case_filterKeep__bt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "T" (alg ["a"] [] [] [.boolLiteral true])] [(.call (.resolve "filter") [.boolLiteral true, .resolve "T"])])
#guard obs case_filterKeep__bt == "ok raw=L[true] n=1"

-- filterKeep__bf: T(a) = true \n filter(false, T)
def case_filterKeep__bf : Expr :=
  .algorithmExpr (alg [] [] [privateProp "T" (alg ["a"] [] [] [.boolLiteral true])] [(.call (.resolve "filter") [.boolLiteral false, .resolve "T"])])
#guard obs case_filterKeep__bf == "ok raw=L[false] n=1"

-- filterKeep__pbt: T(a) = true \n filter((true), T)
def case_filterKeep__pbt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "T" (alg ["a"] [] [] [.boolLiteral true])] [(.call (.resolve "filter") [.boolLiteral true, .resolve "T"])])
#guard obs case_filterKeep__pbt == "ok raw=L[true] n=1"

-- filterKeep__pbt_e: T(a) = true \n filter((true, ()), T)
def case_filterKeep__pbt_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "T" (alg ["a"] [] [] [.boolLiteral true])] [(.call (.resolve "filter") [(.capture [.boolLiteral true, (.emptySequence 0)]), .resolve "T"])])
#guard obs case_filterKeep__pbt_e == "ok raw=L[true, S[]] n=1"

-- filterKeep__pbt_1: T(a) = true \n filter((true, 1), T)
def case_filterKeep__pbt_1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "T" (alg ["a"] [] [] [.boolLiteral true])] [(.call (.resolve "filter") [(.capture [.boolLiteral true, .num 1]), .resolve "T"])])
#guard obs case_filterKeep__pbt_1 == "ok raw=L[true, 1] n=1"

-- filterKeep__lbt: T(a) = true \n filter([true], T)
def case_filterKeep__lbt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "T" (alg ["a"] [] [] [.boolLiteral true])] [(.call (.resolve "filter") [(.listLiteral [.boolLiteral true]), .resolve "T"])])
#guard obs case_filterKeep__lbt == "ok raw=L[true] n=1"

-- filterKeep__lbt_bf: T(a) = true \n filter([true, false], T)
def case_filterKeep__lbt_bf : Expr :=
  .algorithmExpr (alg [] [] [privateProp "T" (alg ["a"] [] [] [.boolLiteral true])] [(.call (.resolve "filter") [(.listLiteral [.boolLiteral true, .boolLiteral false]), .resolve "T"])])
#guard obs case_filterKeep__lbt_bf == "ok raw=L[true, false] n=1"

-- filterKeep__lpbt_1: T(a) = true \n filter([(true, 1)], T)
def case_filterKeep__lpbt_1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "T" (alg ["a"] [] [] [.boolLiteral true])] [(.call (.resolve "filter") [(.listLiteral [(.capture [.boolLiteral true, .num 1])]), .resolve "T"])])
#guard obs case_filterKeep__lpbt_1 == "ok raw=L[S[true, 1]] n=1"

-- filterKeep__p1: T(a) = true \n filter((1), T)
def case_filterKeep__p1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "T" (alg ["a"] [] [] [.boolLiteral true])] [(.call (.resolve "filter") [.num 1, .resolve "T"])])
#guard obs case_filterKeep__p1 == "ok raw=L[1] n=1"

-- filterKeep__p12: T(a) = true \n filter((1, 2), T)
def case_filterKeep__p12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "T" (alg ["a"] [] [] [.boolLiteral true])] [(.call (.resolve "filter") [(.capture [.num 1, .num 2]), .resolve "T"])])
#guard obs case_filterKeep__p12 == "ok raw=L[1, 2] n=1"

-- filterKeep__p123: T(a) = true \n filter((1, 2, 3), T)
def case_filterKeep__p123 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "T" (alg ["a"] [] [] [.boolLiteral true])] [(.call (.resolve "filter") [(.capture [.num 1, .num 2, .num 3]), .resolve "T"])])
#guard obs case_filterKeep__p123 == "ok raw=L[1, 2, 3] n=1"

-- filterKeep__pee: T(a) = true \n filter(((), ()), T)
def case_filterKeep__pee : Expr :=
  .algorithmExpr (alg [] [] [privateProp "T" (alg ["a"] [] [] [.boolLiteral true])] [(.call (.resolve "filter") [(.capture [(.emptySequence 0), (.emptySequence 0)]), .resolve "T"])])
#guard obs case_filterKeep__pee == "ok raw=L[S[], S[]] n=1"

-- filterKeep__pe1: T(a) = true \n filter(((), 1), T)
def case_filterKeep__pe1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "T" (alg ["a"] [] [] [.boolLiteral true])] [(.call (.resolve "filter") [(.capture [(.emptySequence 0), .num 1]), .resolve "T"])])
#guard obs case_filterKeep__pe1 == "ok raw=L[S[], 1] n=1"

-- filterKeep__p1e: T(a) = true \n filter((1, ()), T)
def case_filterKeep__p1e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "T" (alg ["a"] [] [] [.boolLiteral true])] [(.call (.resolve "filter") [(.capture [.num 1, (.emptySequence 0)]), .resolve "T"])])
#guard obs case_filterKeep__p1e == "ok raw=L[1, S[]] n=1"

-- filterKeep__p12_3: T(a) = true \n filter(((1, 2), 3), T)
def case_filterKeep__p12_3 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "T" (alg ["a"] [] [] [.boolLiteral true])] [(.call (.resolve "filter") [(.capture [(.capture [.num 1, .num 2]), .num 3]), .resolve "T"])])
#guard obs case_filterKeep__p12_3 == "ok raw=L[S[1, 2], 3] n=1"

-- filterKeep__p12_34: T(a) = true \n filter(((1, 2), (3, 4)), T)
def case_filterKeep__p12_34 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "T" (alg ["a"] [] [] [.boolLiteral true])] [(.call (.resolve "filter") [(.capture [(.capture [.num 1, .num 2]), (.capture [.num 3, .num 4])]), .resolve "T"])])
#guard obs case_filterKeep__p12_34 == "ok raw=L[S[1, 2], S[3, 4]] n=1"

-- filterKeep__pe_12: T(a) = true \n filter(((), (1, 2)), T)
def case_filterKeep__pe_12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "T" (alg ["a"] [] [] [.boolLiteral true])] [(.call (.resolve "filter") [(.capture [(.emptySequence 0), (.capture [.num 1, .num 2])]), .resolve "T"])])
#guard obs case_filterKeep__pe_12 == "ok raw=L[S[], S[1, 2]] n=1"

-- filterKeep__ppe1_2: T(a) = true \n filter((((), 1), 2), T)
def case_filterKeep__ppe1_2 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "T" (alg ["a"] [] [] [.boolLiteral true])] [(.call (.resolve "filter") [(.capture [(.capture [(.emptySequence 0), .num 1]), .num 2]), .resolve "T"])])
#guard obs case_filterKeep__ppe1_2 == "ok raw=L[S[S[], 1], 2] n=1"

-- filterKeep__p12_e: T(a) = true \n filter(((1, 2), ()), T)
def case_filterKeep__p12_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "T" (alg ["a"] [] [] [.boolLiteral true])] [(.call (.resolve "filter") [(.capture [(.capture [.num 1, .num 2]), (.emptySequence 0)]), .resolve "T"])])
#guard obs case_filterKeep__p12_e == "ok raw=L[S[1, 2], S[]] n=1"

-- filterKeep__ppe: T(a) = true \n filter((()), T)
def case_filterKeep__ppe : Expr :=
  .algorithmExpr (alg [] [] [privateProp "T" (alg ["a"] [] [] [.boolLiteral true])] [(.call (.resolve "filter") [(.emptySequence 0), .resolve "T"])])
#guard obs case_filterKeep__ppe == "ok raw=L[] n=1"

-- filterKeep__pp1: T(a) = true \n filter(((1)), T)
def case_filterKeep__pp1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "T" (alg ["a"] [] [] [.boolLiteral true])] [(.call (.resolve "filter") [.num 1, .resolve "T"])])
#guard obs case_filterKeep__pp1 == "ok raw=L[1] n=1"

-- filterKeep__ppp12: T(a) = true \n filter((((1, 2))), T)
def case_filterKeep__ppp12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "T" (alg ["a"] [] [] [.boolLiteral true])] [(.call (.resolve "filter") [(.capture [.num 1, .num 2]), .resolve "T"])])
#guard obs case_filterKeep__ppp12 == "ok raw=L[1, 2] n=1"

-- filterKeep__le: T(a) = true \n filter([], T)
def case_filterKeep__le : Expr :=
  .algorithmExpr (alg [] [] [privateProp "T" (alg ["a"] [] [] [.boolLiteral true])] [(.call (.resolve "filter") [(.listLiteral []), .resolve "T"])])
#guard obs case_filterKeep__le == "ok raw=L[] n=1"

-- filterKeep__l7: T(a) = true \n filter([7], T)
def case_filterKeep__l7 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "T" (alg ["a"] [] [] [.boolLiteral true])] [(.call (.resolve "filter") [(.listLiteral [.num 7]), .resolve "T"])])
#guard obs case_filterKeep__l7 == "ok raw=L[7] n=1"

-- filterKeep__l12: T(a) = true \n filter([1, 2], T)
def case_filterKeep__l12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "T" (alg ["a"] [] [] [.boolLiteral true])] [(.call (.resolve "filter") [(.listLiteral [.num 1, .num 2]), .resolve "T"])])
#guard obs case_filterKeep__l12 == "ok raw=L[1, 2] n=1"

-- filterKeep__l12_3: T(a) = true \n filter([[1, 2], 3], T)
def case_filterKeep__l12_3 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "T" (alg ["a"] [] [] [.boolLiteral true])] [(.call (.resolve "filter") [(.listLiteral [(.listLiteral [.num 1, .num 2]), .num 3]), .resolve "T"])])
#guard obs case_filterKeep__l12_3 == "ok raw=L[L[1, 2], 3] n=1"

-- filterKeep__lle: T(a) = true \n filter([[]], T)
def case_filterKeep__lle : Expr :=
  .algorithmExpr (alg [] [] [privateProp "T" (alg ["a"] [] [] [.boolLiteral true])] [(.call (.resolve "filter") [(.listLiteral [(.listLiteral [])]), .resolve "T"])])
#guard obs case_filterKeep__lle == "ok raw=L[L[]] n=1"

-- filterKeep__l_e: T(a) = true \n filter([()], T)
def case_filterKeep__l_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "T" (alg ["a"] [] [] [.boolLiteral true])] [(.call (.resolve "filter") [(.listLiteral [(.emptySequence 0)]), .resolve "T"])])
#guard obs case_filterKeep__l_e == "ok raw=L[S[]] n=1"

-- filterKeep__l_p12: T(a) = true \n filter([(1, 2)], T)
def case_filterKeep__l_p12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "T" (alg ["a"] [] [] [.boolLiteral true])] [(.call (.resolve "filter") [(.listLiteral [(.capture [.num 1, .num 2])]), .resolve "T"])])
#guard obs case_filterKeep__l_p12 == "ok raw=L[S[1, 2]] n=1"

-- filterKeep__p_l12: T(a) = true \n filter(([1, 2], 3), T)
def case_filterKeep__p_l12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "T" (alg ["a"] [] [] [.boolLiteral true])] [(.call (.resolve "filter") [(.capture [(.listLiteral [.num 1, .num 2]), .num 3]), .resolve "T"])])
#guard obs case_filterKeep__p_l12 == "ok raw=L[L[1, 2], 3] n=1"

-- filterKeep__pl1: T(a) = true \n filter(([1]), T)
def case_filterKeep__pl1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "T" (alg ["a"] [] [] [.boolLiteral true])] [(.call (.resolve "filter") [(.listLiteral [.num 1]), .resolve "T"])])
#guard obs case_filterKeep__pl1 == "ok raw=L[1] n=1"

-- atoms__e: atoms(())
def case_atoms__e : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "atoms") [(.emptySequence 0)])])
#guard obs case_atoms__e == "ok raw=L[] n=1"

-- atoms__n0: atoms(0)
def case_atoms__n0 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "atoms") [.num 0])])
#guard obs case_atoms__n0 == "ok raw=L[0] n=1"

-- atoms__n1: atoms(1)
def case_atoms__n1 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "atoms") [.num 1])])
#guard obs case_atoms__n1 == "ok raw=L[1] n=1"

-- atoms__bt: atoms(true)
def case_atoms__bt : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "atoms") [.boolLiteral true])])
#guard obs case_atoms__bt == "ok raw=L[] n=1"

-- atoms__bf: atoms(false)
def case_atoms__bf : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "atoms") [.boolLiteral false])])
#guard obs case_atoms__bf == "ok raw=L[] n=1"

-- atoms__pbt: atoms((true))
def case_atoms__pbt : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "atoms") [.boolLiteral true])])
#guard obs case_atoms__pbt == "ok raw=L[] n=1"

-- atoms__pbt_e: atoms((true, ()))
def case_atoms__pbt_e : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "atoms") [(.capture [.boolLiteral true, (.emptySequence 0)])])])
#guard obs case_atoms__pbt_e == "ok raw=L[] n=1"

-- atoms__pbt_1: atoms((true, 1))
def case_atoms__pbt_1 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "atoms") [(.capture [.boolLiteral true, .num 1])])])
#guard obs case_atoms__pbt_1 == "ok raw=L[1] n=1"

-- atoms__lbt: atoms([true])
def case_atoms__lbt : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "atoms") [(.listLiteral [.boolLiteral true])])])
#guard obs case_atoms__lbt == "ok raw=L[] n=1"

-- atoms__lbt_bf: atoms([true, false])
def case_atoms__lbt_bf : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "atoms") [(.listLiteral [.boolLiteral true, .boolLiteral false])])])
#guard obs case_atoms__lbt_bf == "ok raw=L[] n=1"

-- atoms__lpbt_1: atoms([(true, 1)])
def case_atoms__lpbt_1 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "atoms") [(.listLiteral [(.capture [.boolLiteral true, .num 1])])])])
#guard obs case_atoms__lpbt_1 == "ok raw=L[1] n=1"

-- atoms__p1: atoms((1))
def case_atoms__p1 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "atoms") [.num 1])])
#guard obs case_atoms__p1 == "ok raw=L[1] n=1"

-- atoms__p12: atoms((1, 2))
def case_atoms__p12 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "atoms") [(.capture [.num 1, .num 2])])])
#guard obs case_atoms__p12 == "ok raw=L[1, 2] n=1"

-- atoms__p123: atoms((1, 2, 3))
def case_atoms__p123 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "atoms") [(.capture [.num 1, .num 2, .num 3])])])
#guard obs case_atoms__p123 == "ok raw=L[1, 2, 3] n=1"

-- atoms__pee: atoms(((), ()))
def case_atoms__pee : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "atoms") [(.capture [(.emptySequence 0), (.emptySequence 0)])])])
#guard obs case_atoms__pee == "ok raw=L[] n=1"

-- atoms__pe1: atoms(((), 1))
def case_atoms__pe1 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "atoms") [(.capture [(.emptySequence 0), .num 1])])])
#guard obs case_atoms__pe1 == "ok raw=L[1] n=1"

-- atoms__p1e: atoms((1, ()))
def case_atoms__p1e : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "atoms") [(.capture [.num 1, (.emptySequence 0)])])])
#guard obs case_atoms__p1e == "ok raw=L[1] n=1"

-- atoms__p12_3: atoms(((1, 2), 3))
def case_atoms__p12_3 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "atoms") [(.capture [(.capture [.num 1, .num 2]), .num 3])])])
#guard obs case_atoms__p12_3 == "ok raw=L[1, 2, 3] n=1"

-- atoms__p12_34: atoms(((1, 2), (3, 4)))
def case_atoms__p12_34 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "atoms") [(.capture [(.capture [.num 1, .num 2]), (.capture [.num 3, .num 4])])])])
#guard obs case_atoms__p12_34 == "ok raw=L[1, 2, 3, 4] n=1"

-- atoms__pe_12: atoms(((), (1, 2)))
def case_atoms__pe_12 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "atoms") [(.capture [(.emptySequence 0), (.capture [.num 1, .num 2])])])])
#guard obs case_atoms__pe_12 == "ok raw=L[1, 2] n=1"

-- atoms__ppe1_2: atoms((((), 1), 2))
def case_atoms__ppe1_2 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "atoms") [(.capture [(.capture [(.emptySequence 0), .num 1]), .num 2])])])
#guard obs case_atoms__ppe1_2 == "ok raw=L[1, 2] n=1"

-- atoms__p12_e: atoms(((1, 2), ()))
def case_atoms__p12_e : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "atoms") [(.capture [(.capture [.num 1, .num 2]), (.emptySequence 0)])])])
#guard obs case_atoms__p12_e == "ok raw=L[1, 2] n=1"

-- atoms__ppe: atoms((()))
def case_atoms__ppe : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "atoms") [(.emptySequence 0)])])
#guard obs case_atoms__ppe == "ok raw=L[] n=1"

-- atoms__pp1: atoms(((1)))
def case_atoms__pp1 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "atoms") [.num 1])])
#guard obs case_atoms__pp1 == "ok raw=L[1] n=1"

-- atoms__ppp12: atoms((((1, 2))))
def case_atoms__ppp12 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "atoms") [(.capture [.num 1, .num 2])])])
#guard obs case_atoms__ppp12 == "ok raw=L[1, 2] n=1"

-- atoms__le: atoms([])
def case_atoms__le : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "atoms") [(.listLiteral [])])])
#guard obs case_atoms__le == "ok raw=L[] n=1"

-- atoms__l7: atoms([7])
def case_atoms__l7 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "atoms") [(.listLiteral [.num 7])])])
#guard obs case_atoms__l7 == "ok raw=L[7] n=1"

-- atoms__l12: atoms([1, 2])
def case_atoms__l12 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "atoms") [(.listLiteral [.num 1, .num 2])])])
#guard obs case_atoms__l12 == "ok raw=L[1, 2] n=1"

-- atoms__l12_3: atoms([[1, 2], 3])
def case_atoms__l12_3 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "atoms") [(.listLiteral [(.listLiteral [.num 1, .num 2]), .num 3])])])
#guard obs case_atoms__l12_3 == "ok raw=L[1, 2, 3] n=1"

-- atoms__lle: atoms([[]])
def case_atoms__lle : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "atoms") [(.listLiteral [(.listLiteral [])])])])
#guard obs case_atoms__lle == "ok raw=L[] n=1"

-- atoms__l_e: atoms([()])
def case_atoms__l_e : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "atoms") [(.listLiteral [(.emptySequence 0)])])])
#guard obs case_atoms__l_e == "ok raw=L[] n=1"

-- atoms__l_p12: atoms([(1, 2)])
def case_atoms__l_p12 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "atoms") [(.listLiteral [(.capture [.num 1, .num 2])])])])
#guard obs case_atoms__l_p12 == "ok raw=L[1, 2] n=1"

-- atoms__p_l12: atoms(([1, 2], 3))
def case_atoms__p_l12 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "atoms") [(.capture [(.listLiteral [.num 1, .num 2]), .num 3])])])
#guard obs case_atoms__p_l12 == "ok raw=L[1, 2, 3] n=1"

-- atoms__pl1: atoms(([1]))
def case_atoms__pl1 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "atoms") [(.listLiteral [.num 1])])])
#guard obs case_atoms__pl1 == "ok raw=L[1] n=1"

-- takeCapture__e: x = take((), 1) \n x
def case_takeCapture__e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.call (.resolve "take") [(.emptySequence 0), .num 1])])] [.resolve "x"])
#guard obs case_takeCapture__e == "ok raw=L[] n=1"

-- takeCapture__n0: x = take(0, 1) \n x
def case_takeCapture__n0 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.call (.resolve "take") [.num 0, .num 1])])] [.resolve "x"])
#guard obs case_takeCapture__n0 == "ok raw=L[0] n=1"

-- takeCapture__n1: x = take(1, 1) \n x
def case_takeCapture__n1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.call (.resolve "take") [.num 1, .num 1])])] [.resolve "x"])
#guard obs case_takeCapture__n1 == "ok raw=L[1] n=1"

-- takeCapture__bt: x = take(true, 1) \n x
def case_takeCapture__bt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.call (.resolve "take") [.boolLiteral true, .num 1])])] [.resolve "x"])
#guard obs case_takeCapture__bt == "ok raw=L[true] n=1"

-- takeCapture__bf: x = take(false, 1) \n x
def case_takeCapture__bf : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.call (.resolve "take") [.boolLiteral false, .num 1])])] [.resolve "x"])
#guard obs case_takeCapture__bf == "ok raw=L[false] n=1"

-- takeCapture__pbt: x = take((true), 1) \n x
def case_takeCapture__pbt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.call (.resolve "take") [.boolLiteral true, .num 1])])] [.resolve "x"])
#guard obs case_takeCapture__pbt == "ok raw=L[true] n=1"

-- takeCapture__pbt_e: x = take((true, ()), 1) \n x
def case_takeCapture__pbt_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.call (.resolve "take") [(.capture [.boolLiteral true, (.emptySequence 0)]), .num 1])])] [.resolve "x"])
#guard obs case_takeCapture__pbt_e == "ok raw=L[true] n=1"

-- takeCapture__pbt_1: x = take((true, 1), 1) \n x
def case_takeCapture__pbt_1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.call (.resolve "take") [(.capture [.boolLiteral true, .num 1]), .num 1])])] [.resolve "x"])
#guard obs case_takeCapture__pbt_1 == "ok raw=L[true] n=1"

-- takeCapture__lbt: x = take([true], 1) \n x
def case_takeCapture__lbt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.call (.resolve "take") [(.listLiteral [.boolLiteral true]), .num 1])])] [.resolve "x"])
#guard obs case_takeCapture__lbt == "ok raw=L[true] n=1"

-- takeCapture__lbt_bf: x = take([true, false], 1) \n x
def case_takeCapture__lbt_bf : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.call (.resolve "take") [(.listLiteral [.boolLiteral true, .boolLiteral false]), .num 1])])] [.resolve "x"])
#guard obs case_takeCapture__lbt_bf == "ok raw=L[true] n=1"

-- takeCapture__lpbt_1: x = take([(true, 1)], 1) \n x
def case_takeCapture__lpbt_1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.call (.resolve "take") [(.listLiteral [(.capture [.boolLiteral true, .num 1])]), .num 1])])] [.resolve "x"])
#guard obs case_takeCapture__lpbt_1 == "ok raw=L[S[true, 1]] n=1"

-- takeCapture__p1: x = take((1), 1) \n x
def case_takeCapture__p1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.call (.resolve "take") [.num 1, .num 1])])] [.resolve "x"])
#guard obs case_takeCapture__p1 == "ok raw=L[1] n=1"

-- takeCapture__p12: x = take((1, 2), 1) \n x
def case_takeCapture__p12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.call (.resolve "take") [(.capture [.num 1, .num 2]), .num 1])])] [.resolve "x"])
#guard obs case_takeCapture__p12 == "ok raw=L[1] n=1"

-- takeCapture__p123: x = take((1, 2, 3), 1) \n x
def case_takeCapture__p123 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.call (.resolve "take") [(.capture [.num 1, .num 2, .num 3]), .num 1])])] [.resolve "x"])
#guard obs case_takeCapture__p123 == "ok raw=L[1] n=1"

-- takeCapture__pee: x = take(((), ()), 1) \n x
def case_takeCapture__pee : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.call (.resolve "take") [(.capture [(.emptySequence 0), (.emptySequence 0)]), .num 1])])] [.resolve "x"])
#guard obs case_takeCapture__pee == "ok raw=L[S[]] n=1"

-- takeCapture__pe1: x = take(((), 1), 1) \n x
def case_takeCapture__pe1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.call (.resolve "take") [(.capture [(.emptySequence 0), .num 1]), .num 1])])] [.resolve "x"])
#guard obs case_takeCapture__pe1 == "ok raw=L[S[]] n=1"

-- takeCapture__p1e: x = take((1, ()), 1) \n x
def case_takeCapture__p1e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.call (.resolve "take") [(.capture [.num 1, (.emptySequence 0)]), .num 1])])] [.resolve "x"])
#guard obs case_takeCapture__p1e == "ok raw=L[1] n=1"

-- takeCapture__p12_3: x = take(((1, 2), 3), 1) \n x
def case_takeCapture__p12_3 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.call (.resolve "take") [(.capture [(.capture [.num 1, .num 2]), .num 3]), .num 1])])] [.resolve "x"])
#guard obs case_takeCapture__p12_3 == "ok raw=L[S[1, 2]] n=1"

-- takeCapture__p12_34: x = take(((1, 2), (3, 4)), 1) \n x
def case_takeCapture__p12_34 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.call (.resolve "take") [(.capture [(.capture [.num 1, .num 2]), (.capture [.num 3, .num 4])]), .num 1])])] [.resolve "x"])
#guard obs case_takeCapture__p12_34 == "ok raw=L[S[1, 2]] n=1"

-- takeCapture__pe_12: x = take(((), (1, 2)), 1) \n x
def case_takeCapture__pe_12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.call (.resolve "take") [(.capture [(.emptySequence 0), (.capture [.num 1, .num 2])]), .num 1])])] [.resolve "x"])
#guard obs case_takeCapture__pe_12 == "ok raw=L[S[]] n=1"

-- takeCapture__ppe1_2: x = take((((), 1), 2), 1) \n x
def case_takeCapture__ppe1_2 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.call (.resolve "take") [(.capture [(.capture [(.emptySequence 0), .num 1]), .num 2]), .num 1])])] [.resolve "x"])
#guard obs case_takeCapture__ppe1_2 == "ok raw=L[S[S[], 1]] n=1"

-- takeCapture__p12_e: x = take(((1, 2), ()), 1) \n x
def case_takeCapture__p12_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.call (.resolve "take") [(.capture [(.capture [.num 1, .num 2]), (.emptySequence 0)]), .num 1])])] [.resolve "x"])
#guard obs case_takeCapture__p12_e == "ok raw=L[S[1, 2]] n=1"

-- takeCapture__ppe: x = take((()), 1) \n x
def case_takeCapture__ppe : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.call (.resolve "take") [(.emptySequence 0), .num 1])])] [.resolve "x"])
#guard obs case_takeCapture__ppe == "ok raw=L[] n=1"

-- takeCapture__pp1: x = take(((1)), 1) \n x
def case_takeCapture__pp1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.call (.resolve "take") [.num 1, .num 1])])] [.resolve "x"])
#guard obs case_takeCapture__pp1 == "ok raw=L[1] n=1"

-- takeCapture__ppp12: x = take((((1, 2))), 1) \n x
def case_takeCapture__ppp12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.call (.resolve "take") [(.capture [.num 1, .num 2]), .num 1])])] [.resolve "x"])
#guard obs case_takeCapture__ppp12 == "ok raw=L[1] n=1"

-- takeCapture__le: x = take([], 1) \n x
def case_takeCapture__le : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.call (.resolve "take") [(.listLiteral []), .num 1])])] [.resolve "x"])
#guard obs case_takeCapture__le == "ok raw=L[] n=1"

-- takeCapture__l7: x = take([7], 1) \n x
def case_takeCapture__l7 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.call (.resolve "take") [(.listLiteral [.num 7]), .num 1])])] [.resolve "x"])
#guard obs case_takeCapture__l7 == "ok raw=L[7] n=1"

-- takeCapture__l12: x = take([1, 2], 1) \n x
def case_takeCapture__l12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.call (.resolve "take") [(.listLiteral [.num 1, .num 2]), .num 1])])] [.resolve "x"])
#guard obs case_takeCapture__l12 == "ok raw=L[1] n=1"

-- takeCapture__l12_3: x = take([[1, 2], 3], 1) \n x
def case_takeCapture__l12_3 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.call (.resolve "take") [(.listLiteral [(.listLiteral [.num 1, .num 2]), .num 3]), .num 1])])] [.resolve "x"])
#guard obs case_takeCapture__l12_3 == "ok raw=L[L[1, 2]] n=1"

-- takeCapture__lle: x = take([[]], 1) \n x
def case_takeCapture__lle : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.call (.resolve "take") [(.listLiteral [(.listLiteral [])]), .num 1])])] [.resolve "x"])
#guard obs case_takeCapture__lle == "ok raw=L[L[]] n=1"

-- takeCapture__l_e: x = take([()], 1) \n x
def case_takeCapture__l_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.call (.resolve "take") [(.listLiteral [(.emptySequence 0)]), .num 1])])] [.resolve "x"])
#guard obs case_takeCapture__l_e == "ok raw=L[S[]] n=1"

-- takeCapture__l_p12: x = take([(1, 2)], 1) \n x
def case_takeCapture__l_p12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.call (.resolve "take") [(.listLiteral [(.capture [.num 1, .num 2])]), .num 1])])] [.resolve "x"])
#guard obs case_takeCapture__l_p12 == "ok raw=L[S[1, 2]] n=1"

-- takeCapture__p_l12: x = take(([1, 2], 3), 1) \n x
def case_takeCapture__p_l12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.call (.resolve "take") [(.capture [(.listLiteral [.num 1, .num 2]), .num 3]), .num 1])])] [.resolve "x"])
#guard obs case_takeCapture__p_l12 == "ok raw=L[L[1, 2]] n=1"

-- takeCapture__pl1: x = take(([1]), 1) \n x
def case_takeCapture__pl1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.call (.resolve "take") [(.listLiteral [.num 1]), .num 1])])] [.resolve "x"])
#guard obs case_takeCapture__pl1 == "ok raw=L[1] n=1"

-- takeIdentity__e: I(a) = a \n I(take((), 1))
def case_takeIdentity__e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "I") [(.call (.resolve "take") [(.emptySequence 0), .num 1])])])
#guard obs case_takeIdentity__e == "ok raw=L[] n=1"

-- takeIdentity__n0: I(a) = a \n I(take(0, 1))
def case_takeIdentity__n0 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "I") [(.call (.resolve "take") [.num 0, .num 1])])])
#guard obs case_takeIdentity__n0 == "ok raw=L[0] n=1"

-- takeIdentity__n1: I(a) = a \n I(take(1, 1))
def case_takeIdentity__n1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "I") [(.call (.resolve "take") [.num 1, .num 1])])])
#guard obs case_takeIdentity__n1 == "ok raw=L[1] n=1"

-- takeIdentity__bt: I(a) = a \n I(take(true, 1))
def case_takeIdentity__bt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "I") [(.call (.resolve "take") [.boolLiteral true, .num 1])])])
#guard obs case_takeIdentity__bt == "ok raw=L[true] n=1"

-- takeIdentity__bf: I(a) = a \n I(take(false, 1))
def case_takeIdentity__bf : Expr :=
  .algorithmExpr (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "I") [(.call (.resolve "take") [.boolLiteral false, .num 1])])])
#guard obs case_takeIdentity__bf == "ok raw=L[false] n=1"

-- takeIdentity__pbt: I(a) = a \n I(take((true), 1))
def case_takeIdentity__pbt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "I") [(.call (.resolve "take") [.boolLiteral true, .num 1])])])
#guard obs case_takeIdentity__pbt == "ok raw=L[true] n=1"

-- takeIdentity__pbt_e: I(a) = a \n I(take((true, ()), 1))
def case_takeIdentity__pbt_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "I") [(.call (.resolve "take") [(.capture [.boolLiteral true, (.emptySequence 0)]), .num 1])])])
#guard obs case_takeIdentity__pbt_e == "ok raw=L[true] n=1"

-- takeIdentity__pbt_1: I(a) = a \n I(take((true, 1), 1))
def case_takeIdentity__pbt_1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "I") [(.call (.resolve "take") [(.capture [.boolLiteral true, .num 1]), .num 1])])])
#guard obs case_takeIdentity__pbt_1 == "ok raw=L[true] n=1"

-- takeIdentity__lbt: I(a) = a \n I(take([true], 1))
def case_takeIdentity__lbt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "I") [(.call (.resolve "take") [(.listLiteral [.boolLiteral true]), .num 1])])])
#guard obs case_takeIdentity__lbt == "ok raw=L[true] n=1"

-- takeIdentity__lbt_bf: I(a) = a \n I(take([true, false], 1))
def case_takeIdentity__lbt_bf : Expr :=
  .algorithmExpr (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "I") [(.call (.resolve "take") [(.listLiteral [.boolLiteral true, .boolLiteral false]), .num 1])])])
#guard obs case_takeIdentity__lbt_bf == "ok raw=L[true] n=1"

-- takeIdentity__lpbt_1: I(a) = a \n I(take([(true, 1)], 1))
def case_takeIdentity__lpbt_1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "I") [(.call (.resolve "take") [(.listLiteral [(.capture [.boolLiteral true, .num 1])]), .num 1])])])
#guard obs case_takeIdentity__lpbt_1 == "ok raw=L[S[true, 1]] n=1"

-- takeIdentity__p1: I(a) = a \n I(take((1), 1))
def case_takeIdentity__p1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "I") [(.call (.resolve "take") [.num 1, .num 1])])])
#guard obs case_takeIdentity__p1 == "ok raw=L[1] n=1"

-- takeIdentity__p12: I(a) = a \n I(take((1, 2), 1))
def case_takeIdentity__p12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "I") [(.call (.resolve "take") [(.capture [.num 1, .num 2]), .num 1])])])
#guard obs case_takeIdentity__p12 == "ok raw=L[1] n=1"

-- takeIdentity__p123: I(a) = a \n I(take((1, 2, 3), 1))
def case_takeIdentity__p123 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "I") [(.call (.resolve "take") [(.capture [.num 1, .num 2, .num 3]), .num 1])])])
#guard obs case_takeIdentity__p123 == "ok raw=L[1] n=1"

-- takeIdentity__pee: I(a) = a \n I(take(((), ()), 1))
def case_takeIdentity__pee : Expr :=
  .algorithmExpr (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "I") [(.call (.resolve "take") [(.capture [(.emptySequence 0), (.emptySequence 0)]), .num 1])])])
#guard obs case_takeIdentity__pee == "ok raw=L[S[]] n=1"

-- takeIdentity__pe1: I(a) = a \n I(take(((), 1), 1))
def case_takeIdentity__pe1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "I") [(.call (.resolve "take") [(.capture [(.emptySequence 0), .num 1]), .num 1])])])
#guard obs case_takeIdentity__pe1 == "ok raw=L[S[]] n=1"

-- takeIdentity__p1e: I(a) = a \n I(take((1, ()), 1))
def case_takeIdentity__p1e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "I") [(.call (.resolve "take") [(.capture [.num 1, (.emptySequence 0)]), .num 1])])])
#guard obs case_takeIdentity__p1e == "ok raw=L[1] n=1"

-- takeIdentity__p12_3: I(a) = a \n I(take(((1, 2), 3), 1))
def case_takeIdentity__p12_3 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "I") [(.call (.resolve "take") [(.capture [(.capture [.num 1, .num 2]), .num 3]), .num 1])])])
#guard obs case_takeIdentity__p12_3 == "ok raw=L[S[1, 2]] n=1"

-- takeIdentity__p12_34: I(a) = a \n I(take(((1, 2), (3, 4)), 1))
def case_takeIdentity__p12_34 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "I") [(.call (.resolve "take") [(.capture [(.capture [.num 1, .num 2]), (.capture [.num 3, .num 4])]), .num 1])])])
#guard obs case_takeIdentity__p12_34 == "ok raw=L[S[1, 2]] n=1"

-- takeIdentity__pe_12: I(a) = a \n I(take(((), (1, 2)), 1))
def case_takeIdentity__pe_12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "I") [(.call (.resolve "take") [(.capture [(.emptySequence 0), (.capture [.num 1, .num 2])]), .num 1])])])
#guard obs case_takeIdentity__pe_12 == "ok raw=L[S[]] n=1"

-- takeIdentity__ppe1_2: I(a) = a \n I(take((((), 1), 2), 1))
def case_takeIdentity__ppe1_2 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "I") [(.call (.resolve "take") [(.capture [(.capture [(.emptySequence 0), .num 1]), .num 2]), .num 1])])])
#guard obs case_takeIdentity__ppe1_2 == "ok raw=L[S[S[], 1]] n=1"

-- takeIdentity__p12_e: I(a) = a \n I(take(((1, 2), ()), 1))
def case_takeIdentity__p12_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "I") [(.call (.resolve "take") [(.capture [(.capture [.num 1, .num 2]), (.emptySequence 0)]), .num 1])])])
#guard obs case_takeIdentity__p12_e == "ok raw=L[S[1, 2]] n=1"

-- takeIdentity__ppe: I(a) = a \n I(take((()), 1))
def case_takeIdentity__ppe : Expr :=
  .algorithmExpr (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "I") [(.call (.resolve "take") [(.emptySequence 0), .num 1])])])
#guard obs case_takeIdentity__ppe == "ok raw=L[] n=1"

-- takeIdentity__pp1: I(a) = a \n I(take(((1)), 1))
def case_takeIdentity__pp1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "I") [(.call (.resolve "take") [.num 1, .num 1])])])
#guard obs case_takeIdentity__pp1 == "ok raw=L[1] n=1"

-- takeIdentity__ppp12: I(a) = a \n I(take((((1, 2))), 1))
def case_takeIdentity__ppp12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "I") [(.call (.resolve "take") [(.capture [.num 1, .num 2]), .num 1])])])
#guard obs case_takeIdentity__ppp12 == "ok raw=L[1] n=1"

-- takeIdentity__le: I(a) = a \n I(take([], 1))
def case_takeIdentity__le : Expr :=
  .algorithmExpr (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "I") [(.call (.resolve "take") [(.listLiteral []), .num 1])])])
#guard obs case_takeIdentity__le == "ok raw=L[] n=1"

-- takeIdentity__l7: I(a) = a \n I(take([7], 1))
def case_takeIdentity__l7 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "I") [(.call (.resolve "take") [(.listLiteral [.num 7]), .num 1])])])
#guard obs case_takeIdentity__l7 == "ok raw=L[7] n=1"

-- takeIdentity__l12: I(a) = a \n I(take([1, 2], 1))
def case_takeIdentity__l12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "I") [(.call (.resolve "take") [(.listLiteral [.num 1, .num 2]), .num 1])])])
#guard obs case_takeIdentity__l12 == "ok raw=L[1] n=1"

-- takeIdentity__l12_3: I(a) = a \n I(take([[1, 2], 3], 1))
def case_takeIdentity__l12_3 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "I") [(.call (.resolve "take") [(.listLiteral [(.listLiteral [.num 1, .num 2]), .num 3]), .num 1])])])
#guard obs case_takeIdentity__l12_3 == "ok raw=L[L[1, 2]] n=1"

-- takeIdentity__lle: I(a) = a \n I(take([[]], 1))
def case_takeIdentity__lle : Expr :=
  .algorithmExpr (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "I") [(.call (.resolve "take") [(.listLiteral [(.listLiteral [])]), .num 1])])])
#guard obs case_takeIdentity__lle == "ok raw=L[L[]] n=1"

-- takeIdentity__l_e: I(a) = a \n I(take([()], 1))
def case_takeIdentity__l_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "I") [(.call (.resolve "take") [(.listLiteral [(.emptySequence 0)]), .num 1])])])
#guard obs case_takeIdentity__l_e == "ok raw=L[S[]] n=1"

-- takeIdentity__l_p12: I(a) = a \n I(take([(1, 2)], 1))
def case_takeIdentity__l_p12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "I") [(.call (.resolve "take") [(.listLiteral [(.capture [.num 1, .num 2])]), .num 1])])])
#guard obs case_takeIdentity__l_p12 == "ok raw=L[S[1, 2]] n=1"

-- takeIdentity__p_l12: I(a) = a \n I(take(([1, 2], 3), 1))
def case_takeIdentity__p_l12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "I") [(.call (.resolve "take") [(.capture [(.listLiteral [.num 1, .num 2]), .num 3]), .num 1])])])
#guard obs case_takeIdentity__p_l12 == "ok raw=L[L[1, 2]] n=1"

-- takeIdentity__pl1: I(a) = a \n I(take(([1]), 1))
def case_takeIdentity__pl1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "I" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "I") [(.call (.resolve "take") [(.listLiteral [.num 1]), .num 1])])])
#guard obs case_takeIdentity__pl1 == "ok raw=L[1] n=1"

-- takeCount__e: count(take((), 1))
def case_takeCount__e : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "count") [(.call (.resolve "take") [(.emptySequence 0), .num 1])])])
#guard obs case_takeCount__e == "ok raw=0 n=1"

-- takeCount__n0: count(take(0, 1))
def case_takeCount__n0 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "count") [(.call (.resolve "take") [.num 0, .num 1])])])
#guard obs case_takeCount__n0 == "ok raw=1 n=1"

-- takeCount__n1: count(take(1, 1))
def case_takeCount__n1 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "count") [(.call (.resolve "take") [.num 1, .num 1])])])
#guard obs case_takeCount__n1 == "ok raw=1 n=1"

-- takeCount__bt: count(take(true, 1))
def case_takeCount__bt : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "count") [(.call (.resolve "take") [.boolLiteral true, .num 1])])])
#guard obs case_takeCount__bt == "ok raw=1 n=1"

-- takeCount__bf: count(take(false, 1))
def case_takeCount__bf : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "count") [(.call (.resolve "take") [.boolLiteral false, .num 1])])])
#guard obs case_takeCount__bf == "ok raw=1 n=1"

-- takeCount__pbt: count(take((true), 1))
def case_takeCount__pbt : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "count") [(.call (.resolve "take") [.boolLiteral true, .num 1])])])
#guard obs case_takeCount__pbt == "ok raw=1 n=1"

-- takeCount__pbt_e: count(take((true, ()), 1))
def case_takeCount__pbt_e : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "count") [(.call (.resolve "take") [(.capture [.boolLiteral true, (.emptySequence 0)]), .num 1])])])
#guard obs case_takeCount__pbt_e == "ok raw=1 n=1"

-- takeCount__pbt_1: count(take((true, 1), 1))
def case_takeCount__pbt_1 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "count") [(.call (.resolve "take") [(.capture [.boolLiteral true, .num 1]), .num 1])])])
#guard obs case_takeCount__pbt_1 == "ok raw=1 n=1"

-- takeCount__lbt: count(take([true], 1))
def case_takeCount__lbt : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "count") [(.call (.resolve "take") [(.listLiteral [.boolLiteral true]), .num 1])])])
#guard obs case_takeCount__lbt == "ok raw=1 n=1"

-- takeCount__lbt_bf: count(take([true, false], 1))
def case_takeCount__lbt_bf : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "count") [(.call (.resolve "take") [(.listLiteral [.boolLiteral true, .boolLiteral false]), .num 1])])])
#guard obs case_takeCount__lbt_bf == "ok raw=1 n=1"

-- takeCount__lpbt_1: count(take([(true, 1)], 1))
def case_takeCount__lpbt_1 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "count") [(.call (.resolve "take") [(.listLiteral [(.capture [.boolLiteral true, .num 1])]), .num 1])])])
#guard obs case_takeCount__lpbt_1 == "ok raw=1 n=1"

-- takeCount__p1: count(take((1), 1))
def case_takeCount__p1 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "count") [(.call (.resolve "take") [.num 1, .num 1])])])
#guard obs case_takeCount__p1 == "ok raw=1 n=1"

-- takeCount__p12: count(take((1, 2), 1))
def case_takeCount__p12 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "count") [(.call (.resolve "take") [(.capture [.num 1, .num 2]), .num 1])])])
#guard obs case_takeCount__p12 == "ok raw=1 n=1"

-- takeCount__p123: count(take((1, 2, 3), 1))
def case_takeCount__p123 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "count") [(.call (.resolve "take") [(.capture [.num 1, .num 2, .num 3]), .num 1])])])
#guard obs case_takeCount__p123 == "ok raw=1 n=1"

-- takeCount__pee: count(take(((), ()), 1))
def case_takeCount__pee : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "count") [(.call (.resolve "take") [(.capture [(.emptySequence 0), (.emptySequence 0)]), .num 1])])])
#guard obs case_takeCount__pee == "ok raw=1 n=1"

-- takeCount__pe1: count(take(((), 1), 1))
def case_takeCount__pe1 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "count") [(.call (.resolve "take") [(.capture [(.emptySequence 0), .num 1]), .num 1])])])
#guard obs case_takeCount__pe1 == "ok raw=1 n=1"

-- takeCount__p1e: count(take((1, ()), 1))
def case_takeCount__p1e : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "count") [(.call (.resolve "take") [(.capture [.num 1, (.emptySequence 0)]), .num 1])])])
#guard obs case_takeCount__p1e == "ok raw=1 n=1"

-- takeCount__p12_3: count(take(((1, 2), 3), 1))
def case_takeCount__p12_3 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "count") [(.call (.resolve "take") [(.capture [(.capture [.num 1, .num 2]), .num 3]), .num 1])])])
#guard obs case_takeCount__p12_3 == "ok raw=1 n=1"

-- takeCount__p12_34: count(take(((1, 2), (3, 4)), 1))
def case_takeCount__p12_34 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "count") [(.call (.resolve "take") [(.capture [(.capture [.num 1, .num 2]), (.capture [.num 3, .num 4])]), .num 1])])])
#guard obs case_takeCount__p12_34 == "ok raw=1 n=1"

-- takeCount__pe_12: count(take(((), (1, 2)), 1))
def case_takeCount__pe_12 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "count") [(.call (.resolve "take") [(.capture [(.emptySequence 0), (.capture [.num 1, .num 2])]), .num 1])])])
#guard obs case_takeCount__pe_12 == "ok raw=1 n=1"

-- takeCount__ppe1_2: count(take((((), 1), 2), 1))
def case_takeCount__ppe1_2 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "count") [(.call (.resolve "take") [(.capture [(.capture [(.emptySequence 0), .num 1]), .num 2]), .num 1])])])
#guard obs case_takeCount__ppe1_2 == "ok raw=1 n=1"

-- takeCount__p12_e: count(take(((1, 2), ()), 1))
def case_takeCount__p12_e : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "count") [(.call (.resolve "take") [(.capture [(.capture [.num 1, .num 2]), (.emptySequence 0)]), .num 1])])])
#guard obs case_takeCount__p12_e == "ok raw=1 n=1"

-- takeCount__ppe: count(take((()), 1))
def case_takeCount__ppe : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "count") [(.call (.resolve "take") [(.emptySequence 0), .num 1])])])
#guard obs case_takeCount__ppe == "ok raw=0 n=1"

-- takeCount__pp1: count(take(((1)), 1))
def case_takeCount__pp1 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "count") [(.call (.resolve "take") [.num 1, .num 1])])])
#guard obs case_takeCount__pp1 == "ok raw=1 n=1"

-- takeCount__ppp12: count(take((((1, 2))), 1))
def case_takeCount__ppp12 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "count") [(.call (.resolve "take") [(.capture [.num 1, .num 2]), .num 1])])])
#guard obs case_takeCount__ppp12 == "ok raw=1 n=1"

-- takeCount__le: count(take([], 1))
def case_takeCount__le : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "count") [(.call (.resolve "take") [(.listLiteral []), .num 1])])])
#guard obs case_takeCount__le == "ok raw=0 n=1"

-- takeCount__l7: count(take([7], 1))
def case_takeCount__l7 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "count") [(.call (.resolve "take") [(.listLiteral [.num 7]), .num 1])])])
#guard obs case_takeCount__l7 == "ok raw=1 n=1"

-- takeCount__l12: count(take([1, 2], 1))
def case_takeCount__l12 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "count") [(.call (.resolve "take") [(.listLiteral [.num 1, .num 2]), .num 1])])])
#guard obs case_takeCount__l12 == "ok raw=1 n=1"

-- takeCount__l12_3: count(take([[1, 2], 3], 1))
def case_takeCount__l12_3 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "count") [(.call (.resolve "take") [(.listLiteral [(.listLiteral [.num 1, .num 2]), .num 3]), .num 1])])])
#guard obs case_takeCount__l12_3 == "ok raw=1 n=1"

-- takeCount__lle: count(take([[]], 1))
def case_takeCount__lle : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "count") [(.call (.resolve "take") [(.listLiteral [(.listLiteral [])]), .num 1])])])
#guard obs case_takeCount__lle == "ok raw=1 n=1"

-- takeCount__l_e: count(take([()], 1))
def case_takeCount__l_e : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "count") [(.call (.resolve "take") [(.listLiteral [(.emptySequence 0)]), .num 1])])])
#guard obs case_takeCount__l_e == "ok raw=1 n=1"

-- takeCount__l_p12: count(take([(1, 2)], 1))
def case_takeCount__l_p12 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "count") [(.call (.resolve "take") [(.listLiteral [(.capture [.num 1, .num 2])]), .num 1])])])
#guard obs case_takeCount__l_p12 == "ok raw=1 n=1"

-- takeCount__p_l12: count(take(([1, 2], 3), 1))
def case_takeCount__p_l12 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "count") [(.call (.resolve "take") [(.capture [(.listLiteral [.num 1, .num 2]), .num 3]), .num 1])])])
#guard obs case_takeCount__p_l12 == "ok raw=1 n=1"

-- takeCount__pl1: count(take(([1]), 1))
def case_takeCount__pl1 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "count") [(.call (.resolve "take") [(.listLiteral [.num 1]), .num 1])])])
#guard obs case_takeCount__pl1 == "ok raw=1 n=1"

-- takeCollecting__e: G(*a) = a \n G(take((), 1))
def case_takeCollecting__e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "G" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "G") [(.call (.resolve "take") [(.emptySequence 0), .num 1])])])
#guard obs case_takeCollecting__e == "ok raw=L[L[]] n=1"

-- takeCollecting__n0: G(*a) = a \n G(take(0, 1))
def case_takeCollecting__n0 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "G" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "G") [(.call (.resolve "take") [.num 0, .num 1])])])
#guard obs case_takeCollecting__n0 == "ok raw=L[L[0]] n=1"

-- takeCollecting__n1: G(*a) = a \n G(take(1, 1))
def case_takeCollecting__n1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "G" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "G") [(.call (.resolve "take") [.num 1, .num 1])])])
#guard obs case_takeCollecting__n1 == "ok raw=L[L[1]] n=1"

-- takeCollecting__bt: G(*a) = a \n G(take(true, 1))
def case_takeCollecting__bt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "G" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "G") [(.call (.resolve "take") [.boolLiteral true, .num 1])])])
#guard obs case_takeCollecting__bt == "ok raw=L[L[true]] n=1"

-- takeCollecting__bf: G(*a) = a \n G(take(false, 1))
def case_takeCollecting__bf : Expr :=
  .algorithmExpr (alg [] [] [privateProp "G" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "G") [(.call (.resolve "take") [.boolLiteral false, .num 1])])])
#guard obs case_takeCollecting__bf == "ok raw=L[L[false]] n=1"

-- takeCollecting__pbt: G(*a) = a \n G(take((true), 1))
def case_takeCollecting__pbt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "G" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "G") [(.call (.resolve "take") [.boolLiteral true, .num 1])])])
#guard obs case_takeCollecting__pbt == "ok raw=L[L[true]] n=1"

-- takeCollecting__pbt_e: G(*a) = a \n G(take((true, ()), 1))
def case_takeCollecting__pbt_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "G" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "G") [(.call (.resolve "take") [(.capture [.boolLiteral true, (.emptySequence 0)]), .num 1])])])
#guard obs case_takeCollecting__pbt_e == "ok raw=L[L[true]] n=1"

-- takeCollecting__pbt_1: G(*a) = a \n G(take((true, 1), 1))
def case_takeCollecting__pbt_1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "G" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "G") [(.call (.resolve "take") [(.capture [.boolLiteral true, .num 1]), .num 1])])])
#guard obs case_takeCollecting__pbt_1 == "ok raw=L[L[true]] n=1"

-- takeCollecting__lbt: G(*a) = a \n G(take([true], 1))
def case_takeCollecting__lbt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "G" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "G") [(.call (.resolve "take") [(.listLiteral [.boolLiteral true]), .num 1])])])
#guard obs case_takeCollecting__lbt == "ok raw=L[L[true]] n=1"

-- takeCollecting__lbt_bf: G(*a) = a \n G(take([true, false], 1))
def case_takeCollecting__lbt_bf : Expr :=
  .algorithmExpr (alg [] [] [privateProp "G" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "G") [(.call (.resolve "take") [(.listLiteral [.boolLiteral true, .boolLiteral false]), .num 1])])])
#guard obs case_takeCollecting__lbt_bf == "ok raw=L[L[true]] n=1"

-- takeCollecting__lpbt_1: G(*a) = a \n G(take([(true, 1)], 1))
def case_takeCollecting__lpbt_1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "G" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "G") [(.call (.resolve "take") [(.listLiteral [(.capture [.boolLiteral true, .num 1])]), .num 1])])])
#guard obs case_takeCollecting__lpbt_1 == "ok raw=L[L[S[true, 1]]] n=1"

-- takeCollecting__p1: G(*a) = a \n G(take((1), 1))
def case_takeCollecting__p1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "G" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "G") [(.call (.resolve "take") [.num 1, .num 1])])])
#guard obs case_takeCollecting__p1 == "ok raw=L[L[1]] n=1"

-- takeCollecting__p12: G(*a) = a \n G(take((1, 2), 1))
def case_takeCollecting__p12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "G" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "G") [(.call (.resolve "take") [(.capture [.num 1, .num 2]), .num 1])])])
#guard obs case_takeCollecting__p12 == "ok raw=L[L[1]] n=1"

-- takeCollecting__p123: G(*a) = a \n G(take((1, 2, 3), 1))
def case_takeCollecting__p123 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "G" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "G") [(.call (.resolve "take") [(.capture [.num 1, .num 2, .num 3]), .num 1])])])
#guard obs case_takeCollecting__p123 == "ok raw=L[L[1]] n=1"

-- takeCollecting__pee: G(*a) = a \n G(take(((), ()), 1))
def case_takeCollecting__pee : Expr :=
  .algorithmExpr (alg [] [] [privateProp "G" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "G") [(.call (.resolve "take") [(.capture [(.emptySequence 0), (.emptySequence 0)]), .num 1])])])
#guard obs case_takeCollecting__pee == "ok raw=L[L[S[]]] n=1"

-- takeCollecting__pe1: G(*a) = a \n G(take(((), 1), 1))
def case_takeCollecting__pe1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "G" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "G") [(.call (.resolve "take") [(.capture [(.emptySequence 0), .num 1]), .num 1])])])
#guard obs case_takeCollecting__pe1 == "ok raw=L[L[S[]]] n=1"

-- takeCollecting__p1e: G(*a) = a \n G(take((1, ()), 1))
def case_takeCollecting__p1e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "G" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "G") [(.call (.resolve "take") [(.capture [.num 1, (.emptySequence 0)]), .num 1])])])
#guard obs case_takeCollecting__p1e == "ok raw=L[L[1]] n=1"

-- takeCollecting__p12_3: G(*a) = a \n G(take(((1, 2), 3), 1))
def case_takeCollecting__p12_3 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "G" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "G") [(.call (.resolve "take") [(.capture [(.capture [.num 1, .num 2]), .num 3]), .num 1])])])
#guard obs case_takeCollecting__p12_3 == "ok raw=L[L[S[1, 2]]] n=1"

-- takeCollecting__p12_34: G(*a) = a \n G(take(((1, 2), (3, 4)), 1))
def case_takeCollecting__p12_34 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "G" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "G") [(.call (.resolve "take") [(.capture [(.capture [.num 1, .num 2]), (.capture [.num 3, .num 4])]), .num 1])])])
#guard obs case_takeCollecting__p12_34 == "ok raw=L[L[S[1, 2]]] n=1"

-- takeCollecting__pe_12: G(*a) = a \n G(take(((), (1, 2)), 1))
def case_takeCollecting__pe_12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "G" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "G") [(.call (.resolve "take") [(.capture [(.emptySequence 0), (.capture [.num 1, .num 2])]), .num 1])])])
#guard obs case_takeCollecting__pe_12 == "ok raw=L[L[S[]]] n=1"

-- takeCollecting__ppe1_2: G(*a) = a \n G(take((((), 1), 2), 1))
def case_takeCollecting__ppe1_2 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "G" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "G") [(.call (.resolve "take") [(.capture [(.capture [(.emptySequence 0), .num 1]), .num 2]), .num 1])])])
#guard obs case_takeCollecting__ppe1_2 == "ok raw=L[L[S[S[], 1]]] n=1"

-- takeCollecting__p12_e: G(*a) = a \n G(take(((1, 2), ()), 1))
def case_takeCollecting__p12_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "G" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "G") [(.call (.resolve "take") [(.capture [(.capture [.num 1, .num 2]), (.emptySequence 0)]), .num 1])])])
#guard obs case_takeCollecting__p12_e == "ok raw=L[L[S[1, 2]]] n=1"

-- takeCollecting__ppe: G(*a) = a \n G(take((()), 1))
def case_takeCollecting__ppe : Expr :=
  .algorithmExpr (alg [] [] [privateProp "G" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "G") [(.call (.resolve "take") [(.emptySequence 0), .num 1])])])
#guard obs case_takeCollecting__ppe == "ok raw=L[L[]] n=1"

-- takeCollecting__pp1: G(*a) = a \n G(take(((1)), 1))
def case_takeCollecting__pp1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "G" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "G") [(.call (.resolve "take") [.num 1, .num 1])])])
#guard obs case_takeCollecting__pp1 == "ok raw=L[L[1]] n=1"

-- takeCollecting__ppp12: G(*a) = a \n G(take((((1, 2))), 1))
def case_takeCollecting__ppp12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "G" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "G") [(.call (.resolve "take") [(.capture [.num 1, .num 2]), .num 1])])])
#guard obs case_takeCollecting__ppp12 == "ok raw=L[L[1]] n=1"

-- takeCollecting__le: G(*a) = a \n G(take([], 1))
def case_takeCollecting__le : Expr :=
  .algorithmExpr (alg [] [] [privateProp "G" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "G") [(.call (.resolve "take") [(.listLiteral []), .num 1])])])
#guard obs case_takeCollecting__le == "ok raw=L[L[]] n=1"

-- takeCollecting__l7: G(*a) = a \n G(take([7], 1))
def case_takeCollecting__l7 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "G" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "G") [(.call (.resolve "take") [(.listLiteral [.num 7]), .num 1])])])
#guard obs case_takeCollecting__l7 == "ok raw=L[L[7]] n=1"

-- takeCollecting__l12: G(*a) = a \n G(take([1, 2], 1))
def case_takeCollecting__l12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "G" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "G") [(.call (.resolve "take") [(.listLiteral [.num 1, .num 2]), .num 1])])])
#guard obs case_takeCollecting__l12 == "ok raw=L[L[1]] n=1"

-- takeCollecting__l12_3: G(*a) = a \n G(take([[1, 2], 3], 1))
def case_takeCollecting__l12_3 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "G" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "G") [(.call (.resolve "take") [(.listLiteral [(.listLiteral [.num 1, .num 2]), .num 3]), .num 1])])])
#guard obs case_takeCollecting__l12_3 == "ok raw=L[L[L[1, 2]]] n=1"

-- takeCollecting__lle: G(*a) = a \n G(take([[]], 1))
def case_takeCollecting__lle : Expr :=
  .algorithmExpr (alg [] [] [privateProp "G" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "G") [(.call (.resolve "take") [(.listLiteral [(.listLiteral [])]), .num 1])])])
#guard obs case_takeCollecting__lle == "ok raw=L[L[L[]]] n=1"

-- takeCollecting__l_e: G(*a) = a \n G(take([()], 1))
def case_takeCollecting__l_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "G" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "G") [(.call (.resolve "take") [(.listLiteral [(.emptySequence 0)]), .num 1])])])
#guard obs case_takeCollecting__l_e == "ok raw=L[L[S[]]] n=1"

-- takeCollecting__l_p12: G(*a) = a \n G(take([(1, 2)], 1))
def case_takeCollecting__l_p12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "G" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "G") [(.call (.resolve "take") [(.listLiteral [(.capture [.num 1, .num 2])]), .num 1])])])
#guard obs case_takeCollecting__l_p12 == "ok raw=L[L[S[1, 2]]] n=1"

-- takeCollecting__p_l12: G(*a) = a \n G(take(([1, 2], 3), 1))
def case_takeCollecting__p_l12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "G" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "G") [(.call (.resolve "take") [(.capture [(.listLiteral [.num 1, .num 2]), .num 3]), .num 1])])])
#guard obs case_takeCollecting__p_l12 == "ok raw=L[L[L[1, 2]]] n=1"

-- takeCollecting__pl1: G(*a) = a \n G(take(([1]), 1))
def case_takeCollecting__pl1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "G" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "G") [(.call (.resolve "take") [(.listLiteral [.num 1]), .num 1])])])
#guard obs case_takeCollecting__pl1 == "ok raw=L[L[1]] n=1"

-- spreadRootStacked__e: ()**
def case_spreadRootStacked__e : Expr :=
  .algorithmExpr (alg [] [] [] [(.sequenceSpread (.sequenceSpread (.emptySequence 0)))])
#guard obs case_spreadRootStacked__e == "ok raw=S[] n=0"

-- spreadRootStacked__n0: 0**
def case_spreadRootStacked__n0 : Expr :=
  .algorithmExpr (alg [] [] [] [(.sequenceSpread (.sequenceSpread (.num 0)))])
#guard obs case_spreadRootStacked__n0 == "ok raw=0 n=1"

-- spreadRootStacked__n1: 1**
def case_spreadRootStacked__n1 : Expr :=
  .algorithmExpr (alg [] [] [] [(.sequenceSpread (.sequenceSpread (.num 1)))])
#guard obs case_spreadRootStacked__n1 == "ok raw=1 n=1"

-- spreadRootStacked__bt: true**
def case_spreadRootStacked__bt : Expr :=
  .algorithmExpr (alg [] [] [] [(.sequenceSpread (.sequenceSpread (.boolLiteral true)))])
#guard obs case_spreadRootStacked__bt == "ok raw=true n=1"

-- spreadRootStacked__bf: false**
def case_spreadRootStacked__bf : Expr :=
  .algorithmExpr (alg [] [] [] [(.sequenceSpread (.sequenceSpread (.boolLiteral false)))])
#guard obs case_spreadRootStacked__bf == "ok raw=false n=1"

-- spreadRootStacked__pbt: (true)**
def case_spreadRootStacked__pbt : Expr :=
  .algorithmExpr (alg [] [] [] [(.sequenceSpread (.sequenceSpread (.boolLiteral true)))])
#guard obs case_spreadRootStacked__pbt == "ok raw=true n=1"

-- spreadRootStacked__pbt_e: (true, ())**
def case_spreadRootStacked__pbt_e : Expr :=
  .algorithmExpr (alg [] [] [] [(.sequenceSpread (.sequenceSpread (.capture [.boolLiteral true, (.emptySequence 0)])))])
#guard obs case_spreadRootStacked__pbt_e == "ok raw=S[true, S[]] n=2"

-- spreadRootStacked__pbt_1: (true, 1)**
def case_spreadRootStacked__pbt_1 : Expr :=
  .algorithmExpr (alg [] [] [] [(.sequenceSpread (.sequenceSpread (.capture [.boolLiteral true, .num 1])))])
#guard obs case_spreadRootStacked__pbt_1 == "ok raw=S[true, 1] n=2"

-- spreadRootStacked__lbt: [true]**
def case_spreadRootStacked__lbt : Expr :=
  .algorithmExpr (alg [] [] [] [(.sequenceSpread (.sequenceSpread (.listLiteral [.boolLiteral true])))])
#guard obs case_spreadRootStacked__lbt == "ok raw=true n=1"

-- spreadRootStacked__lbt_bf: [true, false]**
def case_spreadRootStacked__lbt_bf : Expr :=
  .algorithmExpr (alg [] [] [] [(.sequenceSpread (.sequenceSpread (.listLiteral [.boolLiteral true, .boolLiteral false])))])
#guard obs case_spreadRootStacked__lbt_bf == "ok raw=S[true, false] n=2"

-- spreadRootStacked__lpbt_1: [(true, 1)]**
def case_spreadRootStacked__lpbt_1 : Expr :=
  .algorithmExpr (alg [] [] [] [(.sequenceSpread (.sequenceSpread (.listLiteral [(.capture [.boolLiteral true, .num 1])])))])
#guard obs case_spreadRootStacked__lpbt_1 == "ok raw=S[true, 1] n=2"

-- spreadRootStacked__p1: (1)**
def case_spreadRootStacked__p1 : Expr :=
  .algorithmExpr (alg [] [] [] [(.sequenceSpread (.sequenceSpread (.num 1)))])
#guard obs case_spreadRootStacked__p1 == "ok raw=1 n=1"

-- spreadRootStacked__p12: (1, 2)**
def case_spreadRootStacked__p12 : Expr :=
  .algorithmExpr (alg [] [] [] [(.sequenceSpread (.sequenceSpread (.capture [.num 1, .num 2])))])
#guard obs case_spreadRootStacked__p12 == "ok raw=S[1, 2] n=2"

-- spreadRootStacked__p123: (1, 2, 3)**
def case_spreadRootStacked__p123 : Expr :=
  .algorithmExpr (alg [] [] [] [(.sequenceSpread (.sequenceSpread (.capture [.num 1, .num 2, .num 3])))])
#guard obs case_spreadRootStacked__p123 == "ok raw=S[1, 2, 3] n=3"

-- spreadRootStacked__pee: ((), ())**
def case_spreadRootStacked__pee : Expr :=
  .algorithmExpr (alg [] [] [] [(.sequenceSpread (.sequenceSpread (.capture [(.emptySequence 0), (.emptySequence 0)])))])
#guard obs case_spreadRootStacked__pee == "ok raw=S[S[], S[]] n=2"

-- spreadRootStacked__pe1: ((), 1)**
def case_spreadRootStacked__pe1 : Expr :=
  .algorithmExpr (alg [] [] [] [(.sequenceSpread (.sequenceSpread (.capture [(.emptySequence 0), .num 1])))])
#guard obs case_spreadRootStacked__pe1 == "ok raw=S[S[], 1] n=2"

-- spreadRootStacked__p1e: (1, ())**
def case_spreadRootStacked__p1e : Expr :=
  .algorithmExpr (alg [] [] [] [(.sequenceSpread (.sequenceSpread (.capture [.num 1, (.emptySequence 0)])))])
#guard obs case_spreadRootStacked__p1e == "ok raw=S[1, S[]] n=2"

-- spreadRootStacked__p12_3: ((1, 2), 3)**
def case_spreadRootStacked__p12_3 : Expr :=
  .algorithmExpr (alg [] [] [] [(.sequenceSpread (.sequenceSpread (.capture [(.capture [.num 1, .num 2]), .num 3])))])
#guard obs case_spreadRootStacked__p12_3 == "ok raw=S[S[1, 2], 3] n=2"

-- spreadRootStacked__p12_34: ((1, 2), (3, 4))**
def case_spreadRootStacked__p12_34 : Expr :=
  .algorithmExpr (alg [] [] [] [(.sequenceSpread (.sequenceSpread (.capture [(.capture [.num 1, .num 2]), (.capture [.num 3, .num 4])])))])
#guard obs case_spreadRootStacked__p12_34 == "ok raw=S[S[1, 2], S[3, 4]] n=2"

-- spreadRootStacked__pe_12: ((), (1, 2))**
def case_spreadRootStacked__pe_12 : Expr :=
  .algorithmExpr (alg [] [] [] [(.sequenceSpread (.sequenceSpread (.capture [(.emptySequence 0), (.capture [.num 1, .num 2])])))])
#guard obs case_spreadRootStacked__pe_12 == "ok raw=S[S[], S[1, 2]] n=2"

-- spreadRootStacked__ppe1_2: (((), 1), 2)**
def case_spreadRootStacked__ppe1_2 : Expr :=
  .algorithmExpr (alg [] [] [] [(.sequenceSpread (.sequenceSpread (.capture [(.capture [(.emptySequence 0), .num 1]), .num 2])))])
#guard obs case_spreadRootStacked__ppe1_2 == "ok raw=S[S[S[], 1], 2] n=2"

-- spreadRootStacked__p12_e: ((1, 2), ())**
def case_spreadRootStacked__p12_e : Expr :=
  .algorithmExpr (alg [] [] [] [(.sequenceSpread (.sequenceSpread (.capture [(.capture [.num 1, .num 2]), (.emptySequence 0)])))])
#guard obs case_spreadRootStacked__p12_e == "ok raw=S[S[1, 2], S[]] n=2"

-- spreadRootStacked__ppe: (())**
def case_spreadRootStacked__ppe : Expr :=
  .algorithmExpr (alg [] [] [] [(.sequenceSpread (.sequenceSpread (.emptySequence 0)))])
#guard obs case_spreadRootStacked__ppe == "ok raw=S[] n=0"

-- spreadRootStacked__pp1: ((1))**
def case_spreadRootStacked__pp1 : Expr :=
  .algorithmExpr (alg [] [] [] [(.sequenceSpread (.sequenceSpread (.num 1)))])
#guard obs case_spreadRootStacked__pp1 == "ok raw=1 n=1"

-- spreadRootStacked__ppp12: (((1, 2)))**
def case_spreadRootStacked__ppp12 : Expr :=
  .algorithmExpr (alg [] [] [] [(.sequenceSpread (.sequenceSpread (.capture [.num 1, .num 2])))])
#guard obs case_spreadRootStacked__ppp12 == "ok raw=S[1, 2] n=2"

-- spreadRootStacked__le: []**
def case_spreadRootStacked__le : Expr :=
  .algorithmExpr (alg [] [] [] [(.sequenceSpread (.sequenceSpread (.listLiteral [])))])
#guard obs case_spreadRootStacked__le == "ok raw=S[] n=0"

-- spreadRootStacked__l7: [7]**
def case_spreadRootStacked__l7 : Expr :=
  .algorithmExpr (alg [] [] [] [(.sequenceSpread (.sequenceSpread (.listLiteral [.num 7])))])
#guard obs case_spreadRootStacked__l7 == "ok raw=7 n=1"

-- spreadRootStacked__l12: [1, 2]**
def case_spreadRootStacked__l12 : Expr :=
  .algorithmExpr (alg [] [] [] [(.sequenceSpread (.sequenceSpread (.listLiteral [.num 1, .num 2])))])
#guard obs case_spreadRootStacked__l12 == "ok raw=S[1, 2] n=2"

-- spreadRootStacked__l12_3: [[1, 2], 3]**
def case_spreadRootStacked__l12_3 : Expr :=
  .algorithmExpr (alg [] [] [] [(.sequenceSpread (.sequenceSpread (.listLiteral [(.listLiteral [.num 1, .num 2]), .num 3])))])
#guard obs case_spreadRootStacked__l12_3 == "ok raw=S[L[1, 2], 3] n=2"

-- spreadRootStacked__lle: [[]]**
def case_spreadRootStacked__lle : Expr :=
  .algorithmExpr (alg [] [] [] [(.sequenceSpread (.sequenceSpread (.listLiteral [(.listLiteral [])])))])
#guard obs case_spreadRootStacked__lle == "ok raw=S[] n=0"

-- spreadRootStacked__l_e: [()]**
def case_spreadRootStacked__l_e : Expr :=
  .algorithmExpr (alg [] [] [] [(.sequenceSpread (.sequenceSpread (.listLiteral [(.emptySequence 0)])))])
#guard obs case_spreadRootStacked__l_e == "ok raw=S[] n=0"

-- spreadRootStacked__l_p12: [(1, 2)]**
def case_spreadRootStacked__l_p12 : Expr :=
  .algorithmExpr (alg [] [] [] [(.sequenceSpread (.sequenceSpread (.listLiteral [(.capture [.num 1, .num 2])])))])
#guard obs case_spreadRootStacked__l_p12 == "ok raw=S[1, 2] n=2"

-- spreadRootStacked__p_l12: ([1, 2], 3)**
def case_spreadRootStacked__p_l12 : Expr :=
  .algorithmExpr (alg [] [] [] [(.sequenceSpread (.sequenceSpread (.capture [(.listLiteral [.num 1, .num 2]), .num 3])))])
#guard obs case_spreadRootStacked__p_l12 == "ok raw=S[L[1, 2], 3] n=2"

-- spreadRootStacked__pl1: ([1])**
def case_spreadRootStacked__pl1 : Expr :=
  .algorithmExpr (alg [] [] [] [(.sequenceSpread (.sequenceSpread (.listLiteral [.num 1])))])
#guard obs case_spreadRootStacked__pl1 == "ok raw=1 n=1"

-- collectingStacked__e: F(*a) = a \n F(()**)
def case_collectingStacked__e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.sequenceSpread (.emptySequence 0)))])])
#guard obs case_collectingStacked__e == "ok raw=L[] n=1"

-- collectingStacked__n0: F(*a) = a \n F(0**)
def case_collectingStacked__n0 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.sequenceSpread (.num 0)))])])
#guard obs case_collectingStacked__n0 == "ok raw=L[0] n=1"

-- collectingStacked__n1: F(*a) = a \n F(1**)
def case_collectingStacked__n1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.sequenceSpread (.num 1)))])])
#guard obs case_collectingStacked__n1 == "ok raw=L[1] n=1"

-- collectingStacked__bt: F(*a) = a \n F(true**)
def case_collectingStacked__bt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.sequenceSpread (.boolLiteral true)))])])
#guard obs case_collectingStacked__bt == "ok raw=L[true] n=1"

-- collectingStacked__bf: F(*a) = a \n F(false**)
def case_collectingStacked__bf : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.sequenceSpread (.boolLiteral false)))])])
#guard obs case_collectingStacked__bf == "ok raw=L[false] n=1"

-- collectingStacked__pbt: F(*a) = a \n F((true)**)
def case_collectingStacked__pbt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.sequenceSpread (.boolLiteral true)))])])
#guard obs case_collectingStacked__pbt == "ok raw=L[true] n=1"

-- collectingStacked__pbt_e: F(*a) = a \n F((true, ())**)
def case_collectingStacked__pbt_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.sequenceSpread (.capture [.boolLiteral true, (.emptySequence 0)])))])])
#guard obs case_collectingStacked__pbt_e == "ok raw=L[true, S[]] n=1"

-- collectingStacked__pbt_1: F(*a) = a \n F((true, 1)**)
def case_collectingStacked__pbt_1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.sequenceSpread (.capture [.boolLiteral true, .num 1])))])])
#guard obs case_collectingStacked__pbt_1 == "ok raw=L[true, 1] n=1"

-- collectingStacked__lbt: F(*a) = a \n F([true]**)
def case_collectingStacked__lbt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.sequenceSpread (.listLiteral [.boolLiteral true])))])])
#guard obs case_collectingStacked__lbt == "ok raw=L[true] n=1"

-- collectingStacked__lbt_bf: F(*a) = a \n F([true, false]**)
def case_collectingStacked__lbt_bf : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.sequenceSpread (.listLiteral [.boolLiteral true, .boolLiteral false])))])])
#guard obs case_collectingStacked__lbt_bf == "ok raw=L[true, false] n=1"

-- collectingStacked__lpbt_1: F(*a) = a \n F([(true, 1)]**)
def case_collectingStacked__lpbt_1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.sequenceSpread (.listLiteral [(.capture [.boolLiteral true, .num 1])])))])])
#guard obs case_collectingStacked__lpbt_1 == "ok raw=L[true, 1] n=1"

-- collectingStacked__p1: F(*a) = a \n F((1)**)
def case_collectingStacked__p1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.sequenceSpread (.num 1)))])])
#guard obs case_collectingStacked__p1 == "ok raw=L[1] n=1"

-- collectingStacked__p12: F(*a) = a \n F((1, 2)**)
def case_collectingStacked__p12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.sequenceSpread (.capture [.num 1, .num 2])))])])
#guard obs case_collectingStacked__p12 == "ok raw=L[1, 2] n=1"

-- collectingStacked__p123: F(*a) = a \n F((1, 2, 3)**)
def case_collectingStacked__p123 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.sequenceSpread (.capture [.num 1, .num 2, .num 3])))])])
#guard obs case_collectingStacked__p123 == "ok raw=L[1, 2, 3] n=1"

-- collectingStacked__pee: F(*a) = a \n F(((), ())**)
def case_collectingStacked__pee : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.sequenceSpread (.capture [(.emptySequence 0), (.emptySequence 0)])))])])
#guard obs case_collectingStacked__pee == "ok raw=L[S[], S[]] n=1"

-- collectingStacked__pe1: F(*a) = a \n F(((), 1)**)
def case_collectingStacked__pe1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.sequenceSpread (.capture [(.emptySequence 0), .num 1])))])])
#guard obs case_collectingStacked__pe1 == "ok raw=L[S[], 1] n=1"

-- collectingStacked__p1e: F(*a) = a \n F((1, ())**)
def case_collectingStacked__p1e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.sequenceSpread (.capture [.num 1, (.emptySequence 0)])))])])
#guard obs case_collectingStacked__p1e == "ok raw=L[1, S[]] n=1"

-- collectingStacked__p12_3: F(*a) = a \n F(((1, 2), 3)**)
def case_collectingStacked__p12_3 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.sequenceSpread (.capture [(.capture [.num 1, .num 2]), .num 3])))])])
#guard obs case_collectingStacked__p12_3 == "ok raw=L[S[1, 2], 3] n=1"

-- collectingStacked__p12_34: F(*a) = a \n F(((1, 2), (3, 4))**)
def case_collectingStacked__p12_34 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.sequenceSpread (.capture [(.capture [.num 1, .num 2]), (.capture [.num 3, .num 4])])))])])
#guard obs case_collectingStacked__p12_34 == "ok raw=L[S[1, 2], S[3, 4]] n=1"

-- collectingStacked__pe_12: F(*a) = a \n F(((), (1, 2))**)
def case_collectingStacked__pe_12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.sequenceSpread (.capture [(.emptySequence 0), (.capture [.num 1, .num 2])])))])])
#guard obs case_collectingStacked__pe_12 == "ok raw=L[S[], S[1, 2]] n=1"

-- collectingStacked__ppe1_2: F(*a) = a \n F((((), 1), 2)**)
def case_collectingStacked__ppe1_2 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.sequenceSpread (.capture [(.capture [(.emptySequence 0), .num 1]), .num 2])))])])
#guard obs case_collectingStacked__ppe1_2 == "ok raw=L[S[S[], 1], 2] n=1"

-- collectingStacked__p12_e: F(*a) = a \n F(((1, 2), ())**)
def case_collectingStacked__p12_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.sequenceSpread (.capture [(.capture [.num 1, .num 2]), (.emptySequence 0)])))])])
#guard obs case_collectingStacked__p12_e == "ok raw=L[S[1, 2], S[]] n=1"

-- collectingStacked__ppe: F(*a) = a \n F((())**)
def case_collectingStacked__ppe : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.sequenceSpread (.emptySequence 0)))])])
#guard obs case_collectingStacked__ppe == "ok raw=L[] n=1"

-- collectingStacked__pp1: F(*a) = a \n F(((1))**)
def case_collectingStacked__pp1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.sequenceSpread (.num 1)))])])
#guard obs case_collectingStacked__pp1 == "ok raw=L[1] n=1"

-- collectingStacked__ppp12: F(*a) = a \n F((((1, 2)))**)
def case_collectingStacked__ppp12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.sequenceSpread (.capture [.num 1, .num 2])))])])
#guard obs case_collectingStacked__ppp12 == "ok raw=L[1, 2] n=1"

-- collectingStacked__le: F(*a) = a \n F([]**)
def case_collectingStacked__le : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.sequenceSpread (.listLiteral [])))])])
#guard obs case_collectingStacked__le == "ok raw=L[] n=1"

-- collectingStacked__l7: F(*a) = a \n F([7]**)
def case_collectingStacked__l7 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.sequenceSpread (.listLiteral [.num 7])))])])
#guard obs case_collectingStacked__l7 == "ok raw=L[7] n=1"

-- collectingStacked__l12: F(*a) = a \n F([1, 2]**)
def case_collectingStacked__l12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.sequenceSpread (.listLiteral [.num 1, .num 2])))])])
#guard obs case_collectingStacked__l12 == "ok raw=L[1, 2] n=1"

-- collectingStacked__l12_3: F(*a) = a \n F([[1, 2], 3]**)
def case_collectingStacked__l12_3 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.sequenceSpread (.listLiteral [(.listLiteral [.num 1, .num 2]), .num 3])))])])
#guard obs case_collectingStacked__l12_3 == "ok raw=L[L[1, 2], 3] n=1"

-- collectingStacked__lle: F(*a) = a \n F([[]]**)
def case_collectingStacked__lle : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.sequenceSpread (.listLiteral [(.listLiteral [])])))])])
#guard obs case_collectingStacked__lle == "ok raw=L[] n=1"

-- collectingStacked__l_e: F(*a) = a \n F([()]**)
def case_collectingStacked__l_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.sequenceSpread (.listLiteral [(.emptySequence 0)])))])])
#guard obs case_collectingStacked__l_e == "ok raw=L[] n=1"

-- collectingStacked__l_p12: F(*a) = a \n F([(1, 2)]**)
def case_collectingStacked__l_p12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.sequenceSpread (.listLiteral [(.capture [.num 1, .num 2])])))])])
#guard obs case_collectingStacked__l_p12 == "ok raw=L[1, 2] n=1"

-- collectingStacked__p_l12: F(*a) = a \n F(([1, 2], 3)**)
def case_collectingStacked__p_l12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.sequenceSpread (.capture [(.listLiteral [.num 1, .num 2]), .num 3])))])])
#guard obs case_collectingStacked__p_l12 == "ok raw=L[L[1, 2], 3] n=1"

-- collectingStacked__pl1: F(*a) = a \n F(([1])**)
def case_collectingStacked__pl1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.sequenceSpread (.listLiteral [.num 1])))])])
#guard obs case_collectingStacked__pl1 == "ok raw=L[1] n=1"

-- captureStacked__e: x = (()**) \n x
def case_captureStacked__e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.sequenceSpread (.sequenceSpread (.emptySequence 0)))])])] [.resolve "x"])
#guard obs case_captureStacked__e == "ok raw=S[] n=1"

-- captureStacked__n0: x = (0**) \n x
def case_captureStacked__n0 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.sequenceSpread (.sequenceSpread (.num 0)))])])] [.resolve "x"])
#guard obs case_captureStacked__n0 == "ok raw=0 n=1"

-- captureStacked__n1: x = (1**) \n x
def case_captureStacked__n1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.sequenceSpread (.sequenceSpread (.num 1)))])])] [.resolve "x"])
#guard obs case_captureStacked__n1 == "ok raw=1 n=1"

-- captureStacked__bt: x = (true**) \n x
def case_captureStacked__bt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.sequenceSpread (.sequenceSpread (.boolLiteral true)))])])] [.resolve "x"])
#guard obs case_captureStacked__bt == "ok raw=true n=1"

-- captureStacked__bf: x = (false**) \n x
def case_captureStacked__bf : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.sequenceSpread (.sequenceSpread (.boolLiteral false)))])])] [.resolve "x"])
#guard obs case_captureStacked__bf == "ok raw=false n=1"

-- captureStacked__pbt: x = ((true)**) \n x
def case_captureStacked__pbt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.sequenceSpread (.sequenceSpread (.boolLiteral true)))])])] [.resolve "x"])
#guard obs case_captureStacked__pbt == "ok raw=true n=1"

-- captureStacked__pbt_e: x = ((true, ())**) \n x
def case_captureStacked__pbt_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.sequenceSpread (.sequenceSpread (.capture [.boolLiteral true, (.emptySequence 0)])))])])] [.resolve "x"])
#guard obs case_captureStacked__pbt_e == "ok raw=S[true, S[]] n=1"

-- captureStacked__pbt_1: x = ((true, 1)**) \n x
def case_captureStacked__pbt_1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.sequenceSpread (.sequenceSpread (.capture [.boolLiteral true, .num 1])))])])] [.resolve "x"])
#guard obs case_captureStacked__pbt_1 == "ok raw=S[true, 1] n=1"

-- captureStacked__lbt: x = ([true]**) \n x
def case_captureStacked__lbt : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.sequenceSpread (.sequenceSpread (.listLiteral [.boolLiteral true])))])])] [.resolve "x"])
#guard obs case_captureStacked__lbt == "ok raw=true n=1"

-- captureStacked__lbt_bf: x = ([true, false]**) \n x
def case_captureStacked__lbt_bf : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.sequenceSpread (.sequenceSpread (.listLiteral [.boolLiteral true, .boolLiteral false])))])])] [.resolve "x"])
#guard obs case_captureStacked__lbt_bf == "ok raw=S[true, false] n=1"

-- captureStacked__lpbt_1: x = ([(true, 1)]**) \n x
def case_captureStacked__lpbt_1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.sequenceSpread (.sequenceSpread (.listLiteral [(.capture [.boolLiteral true, .num 1])])))])])] [.resolve "x"])
#guard obs case_captureStacked__lpbt_1 == "ok raw=S[true, 1] n=1"

-- captureStacked__p1: x = ((1)**) \n x
def case_captureStacked__p1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.sequenceSpread (.sequenceSpread (.num 1)))])])] [.resolve "x"])
#guard obs case_captureStacked__p1 == "ok raw=1 n=1"

-- captureStacked__p12: x = ((1, 2)**) \n x
def case_captureStacked__p12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.sequenceSpread (.sequenceSpread (.capture [.num 1, .num 2])))])])] [.resolve "x"])
#guard obs case_captureStacked__p12 == "ok raw=S[1, 2] n=1"

-- captureStacked__p123: x = ((1, 2, 3)**) \n x
def case_captureStacked__p123 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.sequenceSpread (.sequenceSpread (.capture [.num 1, .num 2, .num 3])))])])] [.resolve "x"])
#guard obs case_captureStacked__p123 == "ok raw=S[1, 2, 3] n=1"

-- captureStacked__pee: x = (((), ())**) \n x
def case_captureStacked__pee : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.sequenceSpread (.sequenceSpread (.capture [(.emptySequence 0), (.emptySequence 0)])))])])] [.resolve "x"])
#guard obs case_captureStacked__pee == "ok raw=S[S[], S[]] n=1"

-- captureStacked__pe1: x = (((), 1)**) \n x
def case_captureStacked__pe1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.sequenceSpread (.sequenceSpread (.capture [(.emptySequence 0), .num 1])))])])] [.resolve "x"])
#guard obs case_captureStacked__pe1 == "ok raw=S[S[], 1] n=1"

-- captureStacked__p1e: x = ((1, ())**) \n x
def case_captureStacked__p1e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.sequenceSpread (.sequenceSpread (.capture [.num 1, (.emptySequence 0)])))])])] [.resolve "x"])
#guard obs case_captureStacked__p1e == "ok raw=S[1, S[]] n=1"

-- captureStacked__p12_3: x = (((1, 2), 3)**) \n x
def case_captureStacked__p12_3 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.sequenceSpread (.sequenceSpread (.capture [(.capture [.num 1, .num 2]), .num 3])))])])] [.resolve "x"])
#guard obs case_captureStacked__p12_3 == "ok raw=S[S[1, 2], 3] n=1"

-- captureStacked__p12_34: x = (((1, 2), (3, 4))**) \n x
def case_captureStacked__p12_34 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.sequenceSpread (.sequenceSpread (.capture [(.capture [.num 1, .num 2]), (.capture [.num 3, .num 4])])))])])] [.resolve "x"])
#guard obs case_captureStacked__p12_34 == "ok raw=S[S[1, 2], S[3, 4]] n=1"

-- captureStacked__pe_12: x = (((), (1, 2))**) \n x
def case_captureStacked__pe_12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.sequenceSpread (.sequenceSpread (.capture [(.emptySequence 0), (.capture [.num 1, .num 2])])))])])] [.resolve "x"])
#guard obs case_captureStacked__pe_12 == "ok raw=S[S[], S[1, 2]] n=1"

-- captureStacked__ppe1_2: x = ((((), 1), 2)**) \n x
def case_captureStacked__ppe1_2 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.sequenceSpread (.sequenceSpread (.capture [(.capture [(.emptySequence 0), .num 1]), .num 2])))])])] [.resolve "x"])
#guard obs case_captureStacked__ppe1_2 == "ok raw=S[S[S[], 1], 2] n=1"

-- captureStacked__p12_e: x = (((1, 2), ())**) \n x
def case_captureStacked__p12_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.sequenceSpread (.sequenceSpread (.capture [(.capture [.num 1, .num 2]), (.emptySequence 0)])))])])] [.resolve "x"])
#guard obs case_captureStacked__p12_e == "ok raw=S[S[1, 2], S[]] n=1"

-- captureStacked__ppe: x = ((())**) \n x
def case_captureStacked__ppe : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.sequenceSpread (.sequenceSpread (.emptySequence 0)))])])] [.resolve "x"])
#guard obs case_captureStacked__ppe == "ok raw=S[] n=1"

-- captureStacked__pp1: x = (((1))**) \n x
def case_captureStacked__pp1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.sequenceSpread (.sequenceSpread (.num 1)))])])] [.resolve "x"])
#guard obs case_captureStacked__pp1 == "ok raw=1 n=1"

-- captureStacked__ppp12: x = ((((1, 2)))**) \n x
def case_captureStacked__ppp12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.sequenceSpread (.sequenceSpread (.capture [.num 1, .num 2])))])])] [.resolve "x"])
#guard obs case_captureStacked__ppp12 == "ok raw=S[1, 2] n=1"

-- captureStacked__le: x = ([]**) \n x
def case_captureStacked__le : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.sequenceSpread (.sequenceSpread (.listLiteral [])))])])] [.resolve "x"])
#guard obs case_captureStacked__le == "ok raw=S[] n=1"

-- captureStacked__l7: x = ([7]**) \n x
def case_captureStacked__l7 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.sequenceSpread (.sequenceSpread (.listLiteral [.num 7])))])])] [.resolve "x"])
#guard obs case_captureStacked__l7 == "ok raw=7 n=1"

-- captureStacked__l12: x = ([1, 2]**) \n x
def case_captureStacked__l12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.sequenceSpread (.sequenceSpread (.listLiteral [.num 1, .num 2])))])])] [.resolve "x"])
#guard obs case_captureStacked__l12 == "ok raw=S[1, 2] n=1"

-- captureStacked__l12_3: x = ([[1, 2], 3]**) \n x
def case_captureStacked__l12_3 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.sequenceSpread (.sequenceSpread (.listLiteral [(.listLiteral [.num 1, .num 2]), .num 3])))])])] [.resolve "x"])
#guard obs case_captureStacked__l12_3 == "ok raw=S[L[1, 2], 3] n=1"

-- captureStacked__lle: x = ([[]]**) \n x
def case_captureStacked__lle : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.sequenceSpread (.sequenceSpread (.listLiteral [(.listLiteral [])])))])])] [.resolve "x"])
#guard obs case_captureStacked__lle == "ok raw=S[] n=1"

-- captureStacked__l_e: x = ([()]**) \n x
def case_captureStacked__l_e : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.sequenceSpread (.sequenceSpread (.listLiteral [(.emptySequence 0)])))])])] [.resolve "x"])
#guard obs case_captureStacked__l_e == "ok raw=S[] n=1"

-- captureStacked__l_p12: x = ([(1, 2)]**) \n x
def case_captureStacked__l_p12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.sequenceSpread (.sequenceSpread (.listLiteral [(.capture [.num 1, .num 2])])))])])] [.resolve "x"])
#guard obs case_captureStacked__l_p12 == "ok raw=S[1, 2] n=1"

-- captureStacked__p_l12: x = (([1, 2], 3)**) \n x
def case_captureStacked__p_l12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.sequenceSpread (.sequenceSpread (.capture [(.listLiteral [.num 1, .num 2]), .num 3])))])])] [.resolve "x"])
#guard obs case_captureStacked__p_l12 == "ok raw=S[L[1, 2], 3] n=1"

-- captureStacked__pl1: x = (([1])**) \n x
def case_captureStacked__pl1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.sequenceSpread (.sequenceSpread (.listLiteral [.num 1])))])])] [.resolve "x"])
#guard obs case_captureStacked__pl1 == "ok raw=1 n=1"

-- special__multiProp: P = 1, 2, 3 \n P
def case_special__multiProp : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (alg [] [] [] [.num 1, .num 2, .num 3])] [.resolve "P"])
#guard obs case_special__multiProp == "ok raw=S[1, 2, 3] n=1"

-- special__multiPropCall: P = 1, 2, 3 \n P()
def case_special__multiPropCall : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (alg [] [] [] [.num 1, .num 2, .num 3])] [(.call (.resolve "P") [])])
#guard obs case_special__multiPropCall == "ok raw=S[1, 2, 3] n=1"

-- special__multiPropCount: P = 1, 2, 3 \n count(P)
def case_special__multiPropCount : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (alg [] [] [] [.num 1, .num 2, .num 3])] [(.call (.resolve "count") [.resolve "P"])])
#guard obs case_special__multiPropCount == "ok raw=3 n=1"

-- special__multiPropDotCount: P = 1, 2, 3 \n P.count
def case_special__multiPropDotCount : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (alg [] [] [] [.num 1, .num 2, .num 3])] [(.dotCall (.resolve "P") "count" none)])
#guard obs case_special__multiPropDotCount == "ok raw=3 n=1"

-- special__multiPropDot: A = { \n     X = 1, 2, 3 \n } \n A.X
def case_special__multiPropDot : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [privateProp "X" (alg [] [] [] [.num 1, .num 2, .num 3])] [])] [(.dotCall (.resolve "A") "X" none)])
#guard obs case_special__multiPropDot == "ok raw=S[1, 2, 3] n=1"

-- special__dotAccessPublicMember: A = { \n     public X = 1, 2, 3 \n } \n A.X
def case_special__dotAccessPublicMember : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [publicProp "X" (alg [] [] [] [.num 1, .num 2, .num 3])] [])] [(.dotCall (.resolve "A") "X" none)])
#guard obs case_special__dotAccessPublicMember == "ok raw=S[1, 2, 3] n=1"

-- special__dotAccessCallPublicMember: A = { \n     public X = 1, 2, 3 \n } \n A.X()
def case_special__dotAccessCallPublicMember : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [publicProp "X" (alg [] [] [] [.num 1, .num 2, .num 3])] [])] [(.dotCall (.resolve "A") "X" (some []))])
#guard obs case_special__dotAccessCallPublicMember == "ok raw=S[1, 2, 3] n=1"

-- special__multiPropIndex0: P = 1, 2, 3 \n P:0
def case_special__multiPropIndex0 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (alg [] [] [] [.num 1, .num 2, .num 3])] [(.index (.resolve "P") (.num 0))])
#guard obs case_special__multiPropIndex0 == "ok raw=1 n=1"

-- special__multiPropEq: P = 1, 2, 3 \n P == (1, 2, 3)
def case_special__multiPropEq : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (alg [] [] [] [.num 1, .num 2, .num 3])] [(.comparison (.resolve "P") [{ op := .eq, operand := (.capture [.num 1, .num 2, .num 3]) }])])
#guard obs case_special__multiPropEq == "ok raw=true n=1"

-- special__multiCollecting: F(*a) = a \n F(1, 2, 3)
def case_special__multiCollecting : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [.num 1, .num 2, .num 3])])
#guard obs case_special__multiCollecting == "ok raw=L[1, 2, 3] n=1"

-- special__multiCollectingCount: F(*a) = a \n count(F(1, 2, 3))
def case_special__multiCollectingCount : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "count") [(.call (.resolve "F") [.num 1, .num 2, .num 3])])])
#guard obs case_special__multiCollectingCount == "ok raw=3 n=1"

-- special__collectingEmptyCall: F(*a) = a \n F()
def case_special__collectingEmptyCall : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [])])
#guard obs case_special__collectingEmptyCall == "ok raw=L[] n=1"

-- special__collectingFwdSum: F(*a) = sum(a) \n F(1, 2, 3)
def case_special__collectingFwdSum : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [(.call (.resolve "sum") [.param "a"])])] [(.call (.resolve "F") [.num 1, .num 2, .num 3])])
#guard obs case_special__collectingFwdSum == "ok raw=6 n=1"

-- special__collectingFwdSpread: F(*a) = G(a*) \n G(*b) = b \n F(1, 2, 3)
def case_special__collectingFwdSpread : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [(.call (.resolve "G") [(.sequenceSpread (.param "a"))])]), privateProp "G" (algWithParameters [{ name := "b", kind := .collecting }] [] [] [.param "b"])] [(.call (.resolve "F") [.num 1, .num 2, .num 3])])
#guard obs case_special__collectingFwdSpread == "ok raw=L[1, 2, 3] n=1"

-- special__collectingJoin: F(*a) = a \n F((1, 2)*, (3, 4)*)
def case_special__collectingJoin : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.capture [.num 1, .num 2])), (.sequenceSpread (.capture [.num 3, .num 4]))])])
#guard obs case_special__collectingJoin == "ok raw=L[1, 2, 3, 4] n=1"

-- special__range13: range(1, 3)
def case_special__range13 : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "range") [.num 1, .num 3])])
#guard obs case_special__range13 == "ok raw=L[1, 2, 3] n=1"

-- special__rangeCapture: x = range(1, 3) \n x
def case_special__rangeCapture : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.call (.resolve "range") [.num 1, .num 3])])] [.resolve "x"])
#guard obs case_special__rangeCapture == "ok raw=L[1, 2, 3] n=1"

-- special__rangeCount: count(range(1, 3))
def case_special__rangeCount : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "count") [(.call (.resolve "range") [.num 1, .num 3])])])
#guard obs case_special__rangeCount == "ok raw=3 n=1"

-- special__rangeIndex0: range(1, 3):0
def case_special__rangeIndex0 : Expr :=
  .algorithmExpr (alg [] [] [] [(.index (.call (.resolve "range") [.num 1, .num 3]) (.num 0))])
#guard obs case_special__rangeIndex0 == "ok raw=1 n=1"

-- special__takeOneSurvivorPair: take(((1, 2), (3, 4)), 1)
def case_special__takeOneSurvivorPair : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "take") [(.capture [(.capture [.num 1, .num 2]), (.capture [.num 3, .num 4])]), .num 1])])
#guard obs case_special__takeOneSurvivorPair == "ok raw=L[S[1, 2]] n=1"

-- special__takeOneSurvivorPairCount: count(take(((1, 2), (3, 4)), 1))
def case_special__takeOneSurvivorPairCount : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "count") [(.call (.resolve "take") [(.capture [(.capture [.num 1, .num 2]), (.capture [.num 3, .num 4])]), .num 1])])])
#guard obs case_special__takeOneSurvivorPairCount == "ok raw=1 n=1"

-- special__takeOneSurvivorPairEq: take(((1, 2), (3, 4)), 1) == (1, 2)
def case_special__takeOneSurvivorPairEq : Expr :=
  .algorithmExpr (alg [] [] [] [(.comparison (.call (.resolve "take") [(.capture [(.capture [.num 1, .num 2]), (.capture [.num 3, .num 4])]), .num 1]) [{ op := .eq, operand := (.capture [.num 1, .num 2]) }])])
#guard obs case_special__takeOneSurvivorPairEq == "ok raw=false n=1"

-- special__skipToOnePair: skip(((1, 2), (3, 4)), 1)
def case_special__skipToOnePair : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "skip") [(.capture [(.capture [.num 1, .num 2]), (.capture [.num 3, .num 4])]), .num 1])])
#guard obs case_special__skipToOnePair == "ok raw=L[S[3, 4]] n=1"

-- special__distinctEmpties: distinct((), ())
def case_special__distinctEmpties : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "distinct") [(.emptySequence 0), (.emptySequence 0)])])
#guard obs case_special__distinctEmpties == "err arity"

-- special__distinctPairsToOne: distinct((1, 2), (1, 2))
def case_special__distinctPairsToOne : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "distinct") [(.capture [.num 1, .num 2]), (.capture [.num 1, .num 2])])])
#guard obs case_special__distinctPairsToOne == "err arity"

-- special__takeEmpties: take((), (), 2)
def case_special__takeEmpties : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "take") [(.emptySequence 0), (.emptySequence 0), .num 2])])
#guard obs case_special__takeEmpties == "err arity"

-- special__filterOneSurvivor: Big(a) = a > 2 \n filter((1, 2, 3), Big)
def case_special__filterOneSurvivor : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Big" (alg ["a"] [] [] [(.comparison (.param "a") [{ op := .gt, operand := (.num 2) }])])] [(.call (.resolve "filter") [(.capture [.num 1, .num 2, .num 3]), .resolve "Big"])])
#guard obs case_special__filterOneSurvivor == "ok raw=L[3] n=1"

-- special__filterOneSurvivorCount: Big(a) = a > 2 \n count(filter((1, 2, 3), Big))
def case_special__filterOneSurvivorCount : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Big" (alg ["a"] [] [] [(.comparison (.param "a") [{ op := .gt, operand := (.num 2) }])])] [(.call (.resolve "count") [(.call (.resolve "filter") [(.capture [.num 1, .num 2, .num 3]), .resolve "Big"])])])
#guard obs case_special__filterOneSurvivorCount == "ok raw=1 n=1"

-- special__filterZeroSurvivors: No(a) = false \n filter((1, 2, 3), No)
def case_special__filterZeroSurvivors : Expr :=
  .algorithmExpr (alg [] [] [privateProp "No" (alg ["a"] [] [] [.boolLiteral false])] [(.call (.resolve "filter") [(.capture [.num 1, .num 2, .num 3]), .resolve "No"])])
#guard obs case_special__filterZeroSurvivors == "ok raw=L[] n=1"

-- special__mapPairSwap: Swap(a, b) = b, a \n map(((1, 2), (3, 4)), Swap)
def case_special__mapPairSwap : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Swap" (alg ["a", "b"] [] [] [.param "b", .param "a"])] [(.call (.resolve "map") [(.capture [(.capture [.num 1, .num 2]), (.capture [.num 3, .num 4])]), .resolve "Swap"])])
#guard obs case_special__mapPairSwap == "err arity"

-- special__mapPairSwapOk: Swap((a, b)) = (b, a) \n map(((1, 2), (3, 4)), Swap)
def case_special__mapPairSwapOk : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Swap" (algWithParameterPatterns [.sequenceValue [.capture { name := "a" }, .capture { name := "b" }]] [] [] [(.capture [.param "b", .param "a"])])] [(.call (.resolve "map") [(.capture [(.capture [.num 1, .num 2]), (.capture [.num 3, .num 4])]), .resolve "Swap"])])
#guard obs case_special__mapPairSwapOk == "ok raw=L[S[2, 1], S[4, 3]] n=1"

-- special__mapPairSwapFlatIsArity: Swap(a, b) = (b, a) \n map(((1, 2), (3, 4)), Swap)
def case_special__mapPairSwapFlatIsArity : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Swap" (alg ["a", "b"] [] [] [(.capture [.param "b", .param "a"])])] [(.call (.resolve "map") [(.capture [(.capture [.num 1, .num 2]), (.capture [.num 3, .num 4])]), .resolve "Swap"])])
#guard obs case_special__mapPairSwapFlatIsArity == "err arity"

-- special__mapToOne: M(a) = a \n map((7), M)
def case_special__mapToOne : Expr :=
  .algorithmExpr (alg [] [] [privateProp "M" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "map") [.num 7, .resolve "M"])])
#guard obs case_special__mapToOne == "ok raw=L[7] n=1"

-- special__orderSingle: order(5)
def case_special__orderSingle : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "order") [.num 5])])
#guard obs case_special__orderSingle == "ok raw=L[5] n=1"

-- special__orderEmpty: order(())
def case_special__orderEmpty : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "order") [(.emptySequence 0)])])
#guard obs case_special__orderEmpty == "ok raw=L[] n=1"

-- special__atomsNested: atoms(((1, 2), (3, 4)))
def case_special__atomsNested : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "atoms") [(.capture [(.capture [.num 1, .num 2]), (.capture [.num 3, .num 4])])])])
#guard obs case_special__atomsNested == "ok raw=L[1, 2, 3, 4] n=1"

-- special__emptyOpGreater: () > 1
def case_special__emptyOpGreater : Expr :=
  .algorithmExpr (alg [] [] [] [(.comparison (.emptySequence 0) [{ op := .gt, operand := (.num 1) }])])
#guard obs case_special__emptyOpGreater == "err type"

-- special__emptyOpPlus: () + 1
def case_special__emptyOpPlus : Expr :=
  .algorithmExpr (alg [] [] [] [(.binary .add (.emptySequence 0) (.num 1))])
#guard obs case_special__emptyOpPlus == "err type"

-- special__emptyOpPlusRight: 1 + ()
def case_special__emptyOpPlusRight : Expr :=
  .algorithmExpr (alg [] [] [] [(.binary .add (.num 1) (.emptySequence 0))])
#guard obs case_special__emptyOpPlusRight == "err type"

-- special__emptyOpDivRight: 10 / ()
def case_special__emptyOpDivRight : Expr :=
  .algorithmExpr (alg [] [] [] [(.binary .div (.num 10) (.emptySequence 0))])
#guard obs case_special__emptyOpDivRight == "err type"

-- special__emptyOpAnd: () and 7
def case_special__emptyOpAnd : Expr :=
  .algorithmExpr (alg [] [] [] [(.binary .and (.emptySequence 0) (.num 7))])
#guard obs case_special__emptyOpAnd == "err type"

-- special__emptyOpString: () + 'text'
def case_special__emptyOpString : Expr :=
  .algorithmExpr (alg [] [] [] [(.binary .add (.emptySequence 0) (.stringLiteral "text"))])
#guard obs case_special__emptyOpString == "err type"

-- special__emptyOpBoth: () + ()
def case_special__emptyOpBoth : Expr :=
  .algorithmExpr (alg [] [] [] [(.binary .add (.emptySequence 0) (.emptySequence 0))])
#guard obs case_special__emptyOpBoth == "err type"

-- special__emptyUnaryMinus: -()
def case_special__emptyUnaryMinus : Expr :=
  .algorithmExpr (alg [] [] [] [(.unary .minus (.emptySequence 0))])
#guard obs case_special__emptyUnaryMinus == "err arity"

-- special__emptyUnaryNot: not ()
def case_special__emptyUnaryNot : Expr :=
  .algorithmExpr (alg [] [] [] [(.unary .not (.emptySequence 0))])
#guard obs case_special__emptyUnaryNot == "err type"

-- special__emptyEqEmpty: () == ()
def case_special__emptyEqEmpty : Expr :=
  .algorithmExpr (alg [] [] [] [(.comparison (.emptySequence 0) [{ op := .eq, operand := (.emptySequence 0) }])])
#guard obs case_special__emptyEqEmpty == "ok raw=true n=1"

-- special__emptyEqNestedEmpty: () == (())
def case_special__emptyEqNestedEmpty : Expr :=
  .algorithmExpr (alg [] [] [] [(.comparison (.emptySequence 0) [{ op := .eq, operand := (.emptySequence 0) }])])
#guard obs case_special__emptyEqNestedEmpty == "ok raw=true n=1"

-- special__emptyNeNestedEmpty: () != (())
def case_special__emptyNeNestedEmpty : Expr :=
  .algorithmExpr (alg [] [] [] [(.comparison (.emptySequence 0) [{ op := .ne, operand := (.emptySequence 0) }])])
#guard obs case_special__emptyNeNestedEmpty == "ok raw=false n=1"

-- special__propBodyEmptySlot: P = (), 99 \n P
def case_special__propBodyEmptySlot : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (alg [] [] [] [(.emptySequence 0), .num 99])] [.resolve "P"])
#guard obs case_special__propBodyEmptySlot == "ok raw=S[S[], 99] n=1"

-- special__rootEmptySlots: (), 99
def case_special__rootEmptySlots : Expr :=
  .algorithmExpr (alg [] [] [] [(.emptySequence 0), .num 99])
#guard obs case_special__rootEmptySlots == "ok raw=S[S[], 99] n=2"

-- special__seqOfSpreadEmpty: ((()*), 1)
def case_special__seqOfSpreadEmpty : Expr :=
  .algorithmExpr (alg [] [] [] [(.capture [(.capture [(.sequenceSpread (.emptySequence 0))]), .num 1])])
#guard obs case_special__seqOfSpreadEmpty == "ok raw=S[S[], 1] n=1"

-- special__indexPairInSeq: x = ((1, 2), (3, 4)) \n (x:0, 99)
def case_special__indexPairInSeq : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.capture [.num 1, .num 2]), (.capture [.num 3, .num 4])])])] [(.capture [(.index (.resolve "x") (.num 0)), .num 99])])
#guard obs case_special__indexPairInSeq == "ok raw=S[S[1, 2], 99] n=1"

-- special__indexEmptyItemRoot: x = ((), ()) \n x:0
def case_special__indexEmptyItemRoot : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.emptySequence 0), (.emptySequence 0)])])] [(.index (.resolve "x") (.num 0))])
#guard obs case_special__indexEmptyItemRoot == "ok raw=S[] n=1"

-- special__indexCapturedEq: x = ((1, 2), (3, 4)) \n y = x:0 \n y == (1, 2)
def case_special__indexCapturedEq : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [(.capture [.num 1, .num 2]), (.capture [.num 3, .num 4])])]), privateProp "y" (alg [] [] [] [(.index (.resolve "x") (.num 0))])] [(.comparison (.resolve "y") [{ op := .eq, operand := (.capture [.num 1, .num 2]) }])])
#guard obs case_special__indexCapturedEq == "ok raw=true n=1"

-- special__chainedListIndex: x = [[1, 2], [3, 4]] \n x:1:0
def case_special__chainedListIndex : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [(.listLiteral [.num 1, .num 2]), (.listLiteral [.num 3, .num 4])])])] [(.index (.index (.resolve "x") (.num 1)) (.num 0))])
#guard obs case_special__chainedListIndex == "ok raw=3 n=1"

-- special__listIndexCapturedEq: x = [[1, 2]] \n y = x:0 \n y == [1, 2]
def case_special__listIndexCapturedEq : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.listLiteral [(.listLiteral [.num 1, .num 2])])]), privateProp "y" (alg [] [] [] [(.index (.resolve "x") (.num 0))])] [(.comparison (.resolve "y") [{ op := .eq, operand := (.listLiteral [.num 1, .num 2]) }])])
#guard obs case_special__listIndexCapturedEq == "ok raw=true n=1"

-- special__listIndexSelectedKindEqFalse: [[1, 2]]:0 == (1, 2)
def case_special__listIndexSelectedKindEqFalse : Expr :=
  .algorithmExpr (alg [] [] [] [(.comparison (.index (.listLiteral [(.listLiteral [.num 1, .num 2])]) (.num 0)) [{ op := .eq, operand := (.capture [.num 1, .num 2]) }])])
#guard obs case_special__listIndexSelectedKindEqFalse == "ok raw=false n=1"

-- special__orderIndex0: [3, 1, 2].order:0
def case_special__orderIndex0 : Expr :=
  .algorithmExpr (alg [] [] [] [(.index (.dotCall (.listLiteral [.num 3, .num 1, .num 2]) "order" none) (.num 0))])
#guard obs case_special__orderIndex0 == "ok raw=1 n=1"

-- special__nestedWrittenArg: F(a, b) = a \n F(((1, 2)), 3)
def case_special__nestedWrittenArg : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["a", "b"] [] [] [.param "a"])] [(.call (.resolve "F") [(.capture [.num 1, .num 2]), .num 3])])
#guard obs case_special__nestedWrittenArg == "ok raw=S[1, 2] n=1"

-- special__writtenSlotArity: F(a, b) = a + b \n F(((1, 2)))
def case_special__writtenSlotArity : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["a", "b"] [] [] [(.binary .add (.param "a") (.param "b"))])] [(.call (.resolve "F") [(.capture [.num 1, .num 2])])])
#guard obs case_special__writtenSlotArity == "err arity"

-- special__mixedSingleGrouped: F(x, *y, z) = y \n A = (1, 2, 3, 4) \n F(A)
def case_special__mixedSingleGrouped : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [] [(.capture [.num 1, .num 2, .num 3, .num 4])]), privateProp "F" (algWithParameters [{ name := "x" }, { name := "y", kind := .collecting }, { name := "z" }] [] [] [.param "y"])] [(.call (.resolve "F") [.resolve "A"])])
#guard obs case_special__mixedSingleGrouped == "err arity"

-- special__sumEmpty: sum(())
def case_special__sumEmpty : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "sum") [(.emptySequence 0)])])
#guard obs case_special__sumEmpty == "ok raw=0 n=1"

-- special__spreadWithSiblingSeqLiteral: x = (1, 2) \n (x*, 99)
def case_special__spreadWithSiblingSeqLiteral : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [(.capture [.num 1, .num 2])])] [(.capture [(.sequenceSpread (.resolve "x")), .num 99])])
#guard obs case_special__spreadWithSiblingSeqLiteral == "ok raw=S[1, 2, 99] n=1"

-- special__spreadEmptyBetween: (1*, (), 2*)
def case_special__spreadEmptyBetween : Expr :=
  .algorithmExpr (alg [] [] [] [(.capture [(.sequenceSpread (.num 1)), (.emptySequence 0), (.sequenceSpread (.num 2))])])
#guard obs case_special__spreadEmptyBetween == "ok raw=S[1, S[], 2] n=1"

-- special__rootSpreadExtra: A = (1, 2) \n A*, 99
def case_special__rootSpreadExtra : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [] [(.capture [.num 1, .num 2])])] [(.sequenceSpread (.resolve "A")), .num 99])
#guard obs case_special__rootSpreadExtra == "ok raw=S[1, 2, 99] n=3"

-- special__spreadOfSpreadSeqLiteral: A = (1, 2) \n ((A*, 99))*
def case_special__spreadOfSpreadSeqLiteral : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [] [(.capture [.num 1, .num 2])])] [(.sequenceSpread (.capture [(.sequenceSpread (.resolve "A")), .num 99]))])
#guard obs case_special__spreadOfSpreadSeqLiteral == "ok raw=S[1, 2, 99] n=3"

-- special__eqSpreadSeqLiteral: P = (1, 2) \n (P*, 99) == (1, 2, 99)
def case_special__eqSpreadSeqLiteral : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (alg [] [] [] [(.capture [.num 1, .num 2])])] [(.comparison (.capture [(.sequenceSpread (.resolve "P")), .num 99]) [{ op := .eq, operand := (.capture [.num 1, .num 2, .num 99]) }])])
#guard obs case_special__eqSpreadSeqLiteral == "ok raw=true n=1"

-- special__loopSpreadHistoryFlat: Step((*history), previous) = (history*, previous + 1), previous + 1 \n Step.repeat(2, (1, 2), 2):0
def case_special__loopSpreadHistoryFlat : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Step" (algWithParameterPatterns [.sequenceValue [.capture { name := "history", kind := .collecting }], .capture { name := "previous" }] [] [] [(.capture [(.sequenceSpread (.param "history")), (.binary .add (.param "previous") (.num 1))]), (.binary .add (.param "previous") (.num 1))])] [(.index (.dotCall (.resolve "Step") "repeat" (some [.num 2, (.capture [.num 1, .num 2]), .num 2])) (.num 0))])
#guard obs case_special__loopSpreadHistoryFlat == "ok raw=S[1, 2, 3, 4] n=1"

-- special__ifBranchSeq: if(true, (1, 2), 3)
def case_special__ifBranchSeq : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "if") [.boolLiteral true, (.capture [.num 1, .num 2]), .num 3])])
#guard obs case_special__ifBranchSeq == "ok raw=S[1, 2] n=1"

-- special__divZero: 1 / 0
def case_special__divZero : Expr :=
  .algorithmExpr (alg [] [] [] [(.binary .div (.num 1) (.num 0))])
#guard obs case_special__divZero == "err div0"

-- special__negativeResult: 0 - 1
def case_special__negativeResult : Expr :=
  .algorithmExpr (alg [] [] [] [(.binary .sub (.num 0) (.num 1))])
#guard obs case_special__negativeResult == "ok raw=-1 n=1"

-- special__strEq: 'ab' == 'ab'
def case_special__strEq : Expr :=
  .algorithmExpr (alg [] [] [] [(.comparison (.stringLiteral "ab") [{ op := .eq, operand := (.stringLiteral "ab") }])])
#guard obs case_special__strEq == "ok raw=true n=1"

-- special__chainAllTrue: 1 < 2 < 3
def case_special__chainAllTrue : Expr :=
  .algorithmExpr (alg [] [] [] [(.comparison (.num 1) [{ op := .lt, operand := (.num 2) }, { op := .lt, operand := (.num 3) }])])
#guard obs case_special__chainAllTrue == "ok raw=true n=1"

-- special__chainMixed: 1 < 2 <= 2 == 2 != 3
def case_special__chainMixed : Expr :=
  .algorithmExpr (alg [] [] [] [(.comparison (.num 1) [{ op := .lt, operand := (.num 2) }, { op := .le, operand := (.num 2) }, { op := .eq, operand := (.num 2) }, { op := .ne, operand := (.num 3) }])])
#guard obs case_special__chainMixed == "ok raw=true n=1"

-- special__chainFalseMiddle: 1 < 3 < 2 < 4
def case_special__chainFalseMiddle : Expr :=
  .algorithmExpr (alg [] [] [] [(.comparison (.num 1) [{ op := .lt, operand := (.num 3) }, { op := .lt, operand := (.num 2) }, { op := .lt, operand := (.num 4) }])])
#guard obs case_special__chainFalseMiddle == "ok raw=false n=1"

-- special__chainFalseLast: 1 < 2 < 2
def case_special__chainFalseLast : Expr :=
  .algorithmExpr (alg [] [] [] [(.comparison (.num 1) [{ op := .lt, operand := (.num 2) }, { op := .lt, operand := (.num 2) }])])
#guard obs case_special__chainFalseLast == "ok raw=false n=1"

-- special__chainEqOnly: 1 == 1 == 1
def case_special__chainEqOnly : Expr :=
  .algorithmExpr (alg [] [] [] [(.comparison (.num 1) [{ op := .eq, operand := (.num 1) }, { op := .eq, operand := (.num 1) }])])
#guard obs case_special__chainEqOnly == "ok raw=true n=1"

-- special__chainNeAdjacent: 1 != 2 != 1
def case_special__chainNeAdjacent : Expr :=
  .algorithmExpr (alg [] [] [] [(.comparison (.num 1) [{ op := .ne, operand := (.num 2) }, { op := .ne, operand := (.num 1) }])])
#guard obs case_special__chainNeAdjacent == "ok raw=true n=1"

-- special__chainNeAdjacentFalse: 1 != 1 != 1
def case_special__chainNeAdjacentFalse : Expr :=
  .algorithmExpr (alg [] [] [] [(.comparison (.num 1) [{ op := .ne, operand := (.num 1) }, { op := .ne, operand := (.num 1) }])])
#guard obs case_special__chainNeAdjacentFalse == "ok raw=false n=1"

-- special__chainEqThenLt: 1 == 1 < 2
def case_special__chainEqThenLt : Expr :=
  .algorithmExpr (alg [] [] [] [(.comparison (.num 1) [{ op := .eq, operand := (.num 1) }, { op := .lt, operand := (.num 2) }])])
#guard obs case_special__chainEqThenLt == "ok raw=true n=1"

-- special__chainBoolEqMixed: 1 < 2 == true
def case_special__chainBoolEqMixed : Expr :=
  .algorithmExpr (alg [] [] [] [(.comparison (.num 1) [{ op := .lt, operand := (.num 2) }, { op := .eq, operand := (.boolLiteral true) }])])
#guard obs case_special__chainBoolEqMixed == "ok raw=false n=1"

-- special__chainSeqEq: (1, 2) == (1, 2) == (1, 2)
def case_special__chainSeqEq : Expr :=
  .algorithmExpr (alg [] [] [] [(.comparison (.capture [.num 1, .num 2]) [{ op := .eq, operand := (.capture [.num 1, .num 2]) }, { op := .eq, operand := (.capture [.num 1, .num 2]) }])])
#guard obs case_special__chainSeqEq == "ok raw=true n=1"

-- special__chainStrEq: 'a' == 'a' != 'b'
def case_special__chainStrEq : Expr :=
  .algorithmExpr (alg [] [] [] [(.comparison (.stringLiteral "a") [{ op := .eq, operand := (.stringLiteral "a") }, { op := .ne, operand := (.stringLiteral "b") }])])
#guard obs case_special__chainStrEq == "ok raw=true n=1"

-- special__chainParenFirst: (1 < 2) == true
def case_special__chainParenFirst : Expr :=
  .algorithmExpr (alg [] [] [] [(.comparison (.comparison (.num 1) [{ op := .lt, operand := (.num 2) }]) [{ op := .eq, operand := (.boolLiteral true) }])])
#guard obs case_special__chainParenFirst == "ok raw=true n=1"

-- special__chainParenRight: 1 < (2 == 2)
def case_special__chainParenRight : Expr :=
  .algorithmExpr (alg [] [] [] [(.comparison (.num 1) [{ op := .lt, operand := (.comparison (.num 2) [{ op := .eq, operand := (.num 2) }]) }])])
#guard obs case_special__chainParenRight == "err type"

-- special__chainParenBoth: (1 < 2) == (3 < 4)
def case_special__chainParenBoth : Expr :=
  .algorithmExpr (alg [] [] [] [(.comparison (.comparison (.num 1) [{ op := .lt, operand := (.num 2) }]) [{ op := .eq, operand := (.comparison (.num 3) [{ op := .lt, operand := (.num 4) }]) }])])
#guard obs case_special__chainParenBoth == "ok raw=true n=1"

-- special__chainUnderNot: not 1 < 2 < 3
def case_special__chainUnderNot : Expr :=
  .algorithmExpr (alg [] [] [] [(.unary .not (.comparison (.num 1) [{ op := .lt, operand := (.num 2) }, { op := .lt, operand := (.num 3) }]))])
#guard obs case_special__chainUnderNot == "ok raw=false n=1"

-- special__chainUnderAnd: 1 < 2 < 3 and 4 < 5
def case_special__chainUnderAnd : Expr :=
  .algorithmExpr (alg [] [] [] [(.binary .and (.comparison (.num 1) [{ op := .lt, operand := (.num 2) }, { op := .lt, operand := (.num 3) }]) (.comparison (.num 4) [{ op := .lt, operand := (.num 5) }]))])
#guard obs case_special__chainUnderAnd == "ok raw=true n=1"

-- special__chainArithmeticOperands: 1 + 1 < 3 * 1 <= 4 - 1
def case_special__chainArithmeticOperands : Expr :=
  .algorithmExpr (alg [] [] [] [(.comparison (.binary .add (.num 1) (.num 1)) [{ op := .lt, operand := (.binary .mul (.num 3) (.num 1)) }, { op := .le, operand := (.binary .sub (.num 4) (.num 1)) }])])
#guard obs case_special__chainArithmeticOperands == "ok raw=true n=1"

-- special__chainInvalidLater: 3 < 2 < true
def case_special__chainInvalidLater : Expr :=
  .algorithmExpr (alg [] [] [] [(.comparison (.num 3) [{ op := .lt, operand := (.num 2) }, { op := .lt, operand := (.boolLiteral true) }])])
#guard obs case_special__chainInvalidLater == "err type"

-- special__chainErrorFirstOperand: 1 / 0 < true < 1
def case_special__chainErrorFirstOperand : Expr :=
  .algorithmExpr (alg [] [] [] [(.comparison (.binary .div (.num 1) (.num 0)) [{ op := .lt, operand := (.boolLiteral true) }, { op := .lt, operand := (.num 1) }])])
#guard obs case_special__chainErrorFirstOperand == "err div0"

-- special__chainErrorAfterFalse: 3 < 2 < 1 / 0
def case_special__chainErrorAfterFalse : Expr :=
  .algorithmExpr (alg [] [] [] [(.comparison (.num 3) [{ op := .lt, operand := (.num 2) }, { op := .lt, operand := (.binary .div (.num 1) (.num 0)) }])])
#guard obs case_special__chainErrorAfterFalse == "err div0"

-- special__chainPropertyOperands: P = 2 \n 1 < P < 3, P == P == 2
def case_special__chainPropertyOperands : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (alg [] [] [] [.num 2])] [(.comparison (.num 1) [{ op := .lt, operand := (.resolve "P") }, { op := .lt, operand := (.num 3) }]), (.comparison (.resolve "P") [{ op := .eq, operand := (.resolve "P") }, { op := .eq, operand := (.num 2) }])])
#guard obs case_special__chainPropertyOperands == "ok raw=S[true, true] n=2"

-- special__chainCallOperands: F(x) = x + 1 \n F(0) < F(1) < F(2)
def case_special__chainCallOperands : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 1))])] [(.comparison (.call (.resolve "F") [.num 0]) [{ op := .lt, operand := (.call (.resolve "F") [.num 1]) }, { op := .lt, operand := (.call (.resolve "F") [.num 2]) }])])
#guard obs case_special__chainCallOperands == "ok raw=true n=1"

-- special__strCount: count('ab')
def case_special__strCount : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "count") [.stringLiteral "ab"])])
#guard obs case_special__strCount == "ok raw=1 n=1"

-- special__strCapture: x = 'ab' \n x
def case_special__strCapture : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [.stringLiteral "ab"])] [.resolve "x"])
#guard obs case_special__strCapture == "ok raw='ab' n=1"

-- special__listSpreadOfSeqProp: A = 1, 2, 3 \n [A*]
def case_special__listSpreadOfSeqProp : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [] [.num 1, .num 2, .num 3])] [(.listLiteral [(.sequenceSpread (.resolve "A"))])])
#guard obs case_special__listSpreadOfSeqProp == "ok raw=L[1, 2, 3] n=1"

-- special__listSpreadBetween: A = 1, 2, 3 \n [0, A*, 4]
def case_special__listSpreadBetween : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [] [.num 1, .num 2, .num 3])] [(.listLiteral [.num 0, (.sequenceSpread (.resolve "A")), .num 4])])
#guard obs case_special__listSpreadBetween == "ok raw=L[0, 1, 2, 3, 4] n=1"

-- special__listOfLists: A = [1, 2] \n B = [3, 4] \n [A, B]
def case_special__listOfLists : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [] [(.listLiteral [.num 1, .num 2])]), privateProp "B" (alg [] [] [] [(.listLiteral [.num 3, .num 4])])] [(.listLiteral [.resolve "A", .resolve "B"])])
#guard obs case_special__listOfLists == "ok raw=L[L[1, 2], L[3, 4]] n=1"

-- special__listSpreadConcat: A = [1, 2] \n B = [3, 4] \n [A*, B*]
def case_special__listSpreadConcat : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [] [(.listLiteral [.num 1, .num 2])]), privateProp "B" (alg [] [] [] [(.listLiteral [.num 3, .num 4])])] [(.listLiteral [(.sequenceSpread (.resolve "A")), (.sequenceSpread (.resolve "B"))])])
#guard obs case_special__listSpreadConcat == "ok raw=L[1, 2, 3, 4] n=1"

-- special__listMixedSpread: A = [1, 2] \n B = [3, 4] \n [A, B*]
def case_special__listMixedSpread : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [] [(.listLiteral [.num 1, .num 2])]), privateProp "B" (alg [] [] [] [(.listLiteral [.num 3, .num 4])])] [(.listLiteral [.resolve "A", (.sequenceSpread (.resolve "B"))])])
#guard obs case_special__listMixedSpread == "ok raw=L[L[1, 2], 3, 4] n=1"

-- special__listEmptyListSpreadBetween: [1, []*, 2]
def case_special__listEmptyListSpreadBetween : Expr :=
  .algorithmExpr (alg [] [] [] [(.listLiteral [.num 1, (.sequenceSpread (.listLiteral [])), .num 2])])
#guard obs case_special__listEmptyListSpreadBetween == "ok raw=L[1, 2] n=1"

-- special__listEmptySeqSpreadBetween: [1, ()*, 2]
def case_special__listEmptySeqSpreadBetween : Expr :=
  .algorithmExpr (alg [] [] [] [(.listLiteral [.num 1, (.sequenceSpread (.emptySequence 0)), .num 2])])
#guard obs case_special__listEmptySeqSpreadBetween == "ok raw=L[1, 2] n=1"

-- special__listNeSeq: [1, 2] == (1, 2)
def case_special__listNeSeq : Expr :=
  .algorithmExpr (alg [] [] [] [(.comparison (.listLiteral [.num 1, .num 2]) [{ op := .eq, operand := (.capture [.num 1, .num 2]) }])])
#guard obs case_special__listNeSeq == "ok raw=false n=1"

-- special__listEmptyNeEmptySeq: [] == ()
def case_special__listEmptyNeEmptySeq : Expr :=
  .algorithmExpr (alg [] [] [] [(.comparison (.listLiteral []) [{ op := .eq, operand := (.emptySequence 0) }])])
#guard obs case_special__listEmptyNeEmptySeq == "ok raw=false n=1"

-- special__listSingletonNeItem: [7] == 7
def case_special__listSingletonNeItem : Expr :=
  .algorithmExpr (alg [] [] [] [(.comparison (.listLiteral [.num 7]) [{ op := .eq, operand := (.num 7) }])])
#guard obs case_special__listSingletonNeItem == "ok raw=false n=1"

-- special__listWrapCanonicalizes: ([1, 2]) == [1, 2]
def case_special__listWrapCanonicalizes : Expr :=
  .algorithmExpr (alg [] [] [] [(.comparison (.listLiteral [.num 1, .num 2]) [{ op := .eq, operand := (.listLiteral [.num 1, .num 2]) }])])
#guard obs case_special__listWrapCanonicalizes == "ok raw=true n=1"

-- special__listSpreadCaptureRoundTrip: A = [1, 2, 3] \n B = { A* } \n B == (1, 2, 3)
def case_special__listSpreadCaptureRoundTrip : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [] [(.listLiteral [.num 1, .num 2, .num 3])]), privateProp "B" (alg [] [] [] [(.sequenceSpread (.resolve "A"))])] [(.comparison (.resolve "B") [{ op := .eq, operand := (.capture [.num 1, .num 2, .num 3]) }])])
#guard obs case_special__listSpreadCaptureRoundTrip == "ok raw=true n=1"

-- special__listCollectingNotSequenceKind: x, *rest = [1, 2, 3] \n rest == (2, 3)
def case_special__listCollectingNotSequenceKind : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.listLiteral [.num 1, .num 2, .num 3])]), privateProp "x" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "rest", kind := .collecting }]] [] [] [.param "x"])) [.resolve "$deconstruct$0"])]), privateProp "rest" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "rest", kind := .collecting }]] [] [] [.param "rest"])) [.resolve "$deconstruct$0"])])] [(.comparison (.resolve "rest") [{ op := .eq, operand := (.capture [.num 2, .num 3]) }])])
#guard obs case_special__listCollectingNotSequenceKind == "ok raw=false n=1"

-- special__listCollectingCollectsExactList: x, *rest = [1, 2, 3] \n rest == [2, 3]
def case_special__listCollectingCollectsExactList : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.listLiteral [.num 1, .num 2, .num 3])]), privateProp "x" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "rest", kind := .collecting }]] [] [] [.param "x"])) [.resolve "$deconstruct$0"])]), privateProp "rest" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "rest", kind := .collecting }]] [] [] [.param "rest"])) [.resolve "$deconstruct$0"])])] [(.comparison (.resolve "rest") [{ op := .eq, operand := (.listLiteral [.num 2, .num 3]) }])])
#guard obs case_special__listCollectingCollectsExactList == "ok raw=true n=1"

-- special__implicitForwardOrdinarySource: Target(*items) = items \n Use(items) = Target \n Use([1, 2])
def case_special__implicitForwardOrdinarySource : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Target" (algWithParameters [{ name := "items", kind := .collecting }] [] [] [.param "items"]), privateProp "Use" (alg ["items"] [] [] [(.call (.resolve "Target") [.param "items"])])] [(.call (.resolve "Use") [(.listLiteral [.num 1, .num 2])])])
#guard obs case_special__implicitForwardOrdinarySource == "ok raw=L[L[1, 2]] n=1"

-- special__callbackSingleCollectingMap: Collect(*items) = items \n [7].map(Collect)
def case_special__callbackSingleCollectingMap : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Collect" (algWithParameters [{ name := "items", kind := .collecting }] [] [] [.param "items"])] [(.dotCall (.listLiteral [.num 7]) "map" (some [.resolve "Collect"]))])
#guard obs case_special__callbackSingleCollectingMap == "ok raw=L[L[7]] n=1"

-- special__callbackMixedCollectingRow: F(first, *middle, last) = middle \n [(1, 2, 3, 4)].map(F)
def case_special__callbackMixedCollectingRow : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameters [{ name := "first" }, { name := "middle", kind := .collecting }, { name := "last" }] [] [] [.param "middle"])] [(.dotCall (.listLiteral [(.capture [.num 1, .num 2, .num 3, .num 4])]) "map" (some [.resolve "F"]))])
#guard obs case_special__callbackMixedCollectingRow == "err arity"

-- special__callbackMixedCollectingRowPattern: F((first, *middle, last)) = middle \n [(1, 2, 3, 4)].map(F)
def case_special__callbackMixedCollectingRowPattern : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (algWithParameterPatterns [.sequenceValue [.capture { name := "first" }, .capture { name := "middle", kind := .collecting }, .capture { name := "last" }]] [] [] [.param "middle"])] [(.dotCall (.listLiteral [(.capture [.num 1, .num 2, .num 3, .num 4])]) "map" (some [.resolve "F"]))])
#guard obs case_special__callbackMixedCollectingRowPattern == "ok raw=L[L[2, 3]] n=1"

-- special__callbackCollectingElementIsOneArgument: Cnt(*xs) = xs.count \n map([(10, 7), [10, 7], 20], Cnt)
def case_special__callbackCollectingElementIsOneArgument : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Cnt" (algWithParameters [{ name := "xs", kind := .collecting }] [] [] [(.dotCall (.param "xs") "count" none)])] [(.call (.resolve "map") [(.listLiteral [(.capture [.num 10, .num 7]), (.listLiteral [.num 10, .num 7]), .num 20]), .resolve "Cnt"])])
#guard obs case_special__callbackCollectingElementIsOneArgument == "ok raw=L[1, 1, 1] n=1"

-- special__listInSeqSpreadKeepsList: A = [1, 2] \n (A, 9)*
def case_special__listInSeqSpreadKeepsList : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [] [(.listLiteral [.num 1, .num 2])])] [(.sequenceSpread (.capture [.resolve "A", .num 9]))])
#guard obs case_special__listInSeqSpreadKeepsList == "ok raw=S[L[1, 2], 9] n=2"

-- special__listFixedCallBoundary: F(a, b) = a \n F([1, 2], 3)
def case_special__listFixedCallBoundary : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["a", "b"] [] [] [.param "a"])] [(.call (.resolve "F") [(.listLiteral [.num 1, .num 2]), .num 3])])
#guard obs case_special__listFixedCallBoundary == "ok raw=L[1, 2] n=1"

-- special__listCollectingSpreadCall: F(*a) = a \n A = [1, 2] \n F(A*, 9)
def case_special__listCollectingSpreadCall : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [] [(.listLiteral [.num 1, .num 2])]), privateProp "F" (algWithParameters [{ name := "a", kind := .collecting }] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.resolve "A")), .num 9])])
#guard obs case_special__listCollectingSpreadCall == "ok raw=L[1, 2, 9] n=1"

-- special__spreadNoOutputBlockRoot: {A = 1}*
def case_special__spreadNoOutputBlockRoot : Expr :=
  .algorithmExpr (alg [] [] [] [(.sequenceSpread (.algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [] [.num 1])] [])))])
#guard obs case_special__spreadNoOutputBlockRoot == "err spreadMissingOutput"

-- special__spreadNoOutputBlockList: [{A = 1}*]
def case_special__spreadNoOutputBlockList : Expr :=
  .algorithmExpr (alg [] [] [] [(.listLiteral [(.sequenceSpread (.algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [] [.num 1])] [])))])])
#guard obs case_special__spreadNoOutputBlockList == "err spreadMissingOutput"

-- special__spreadNoOutputBlockCallArg: F(a) = a \n F({A = 1}*)
def case_special__spreadNoOutputBlockCallArg : Expr :=
  .algorithmExpr (alg [] [] [privateProp "F" (alg ["a"] [] [] [.param "a"])] [(.call (.resolve "F") [(.sequenceSpread (.algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [] [.num 1])] [])))])])
#guard obs case_special__spreadNoOutputBlockCallArg == "err spreadMissingOutput"

-- special__spreadNoOutputResolved: X = {A = 1} \n X*
def case_special__spreadNoOutputResolved : Expr :=
  .algorithmExpr (alg [] [] [privateProp "X" (alg [] [] [privateProp "A" (alg [] [] [] [.num 1])] [])] [(.sequenceSpread (.resolve "X"))])
#guard obs case_special__spreadNoOutputResolved == "err spreadMissingOutput"

-- special__listLoneCollectingAssignment: *items = [1, 2, 3]
def case_special__listLoneCollectingAssignment : Expr :=
  .algorithmExpr (alg [] [] [privateProp "$deconstruct$0" (alg [] [] [] [(.listLiteral [.num 1, .num 2, .num 3])]), privateProp "items" (alg [] [] [] [(.call (.algorithmExpr (algWithParameterPatterns [.sequenceValue [.capture { name := "items", kind := .collecting }]] [] [] [.param "items"])) [.resolve "$deconstruct$0"])])] [])
#guard obs case_special__listLoneCollectingAssignment == "err missingOutput"

-- special__minSeq: min((3, 1, 2))
def case_special__minSeq : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "min") [(.capture [.num 3, .num 1, .num 2])])])
#guard obs case_special__minSeq == "ok raw=1 n=1"

-- special__minList: min([3, 1])
def case_special__minList : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "min") [(.listLiteral [.num 3, .num 1])])])
#guard obs case_special__minList == "ok raw=1 n=1"

-- special__minScalar: min(7)
def case_special__minScalar : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "min") [.num 7])])
#guard obs case_special__minScalar == "ok raw=7 n=1"

-- special__minEmpty: min(())
def case_special__minEmpty : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "min") [(.emptySequence 0)])])
#guard obs case_special__minEmpty == "err arity"

-- special__minNestedItem: min(((1, 2), 3))
def case_special__minNestedItem : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "min") [(.capture [(.capture [.num 1, .num 2]), .num 3])])])
#guard obs case_special__minNestedItem == "err arity"

-- special__minDot: x = 3, 1, 2 \n x.min
def case_special__minDot : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [.num 3, .num 1, .num 2])] [(.dotCall (.resolve "x") "min" none)])
#guard obs case_special__minDot == "ok raw=1 n=1"

-- special__maxSeq: max((3, 1, 2))
def case_special__maxSeq : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "max") [(.capture [.num 3, .num 1, .num 2])])])
#guard obs case_special__maxSeq == "ok raw=3 n=1"

-- special__maxList: max([3, 1])
def case_special__maxList : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "max") [(.listLiteral [.num 3, .num 1])])])
#guard obs case_special__maxList == "ok raw=3 n=1"

-- special__maxEmpty: max(())
def case_special__maxEmpty : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "max") [(.emptySequence 0)])])
#guard obs case_special__maxEmpty == "err arity"

-- special__maxDot: x = 3, 1, 2 \n x.max
def case_special__maxDot : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [.num 3, .num 1, .num 2])] [(.dotCall (.resolve "x") "max" none)])
#guard obs case_special__maxDot == "ok raw=3 n=1"

-- special__firstSeq: first((1, 2, 3))
def case_special__firstSeq : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "first") [(.capture [.num 1, .num 2, .num 3])])])
#guard obs case_special__firstSeq == "ok raw=1 n=1"

-- special__firstScalar: first(7)
def case_special__firstScalar : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "first") [.num 7])])
#guard obs case_special__firstScalar == "ok raw=7 n=1"

-- special__firstListElementStaysExact: first([[1, 2], 3])
def case_special__firstListElementStaysExact : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "first") [(.listLiteral [(.listLiteral [.num 1, .num 2]), .num 3])])])
#guard obs case_special__firstListElementStaysExact == "ok raw=L[1, 2] n=1"

-- special__firstEmptyItem: first(((), 1))
def case_special__firstEmptyItem : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "first") [(.capture [(.emptySequence 0), .num 1])])])
#guard obs case_special__firstEmptyItem == "ok raw=S[] n=1"

-- special__firstEmpty: first(())
def case_special__firstEmpty : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "first") [(.emptySequence 0)])])
#guard obs case_special__firstEmpty == "err arity"

-- special__firstDot: x = 1, 2, 3 \n x.first
def case_special__firstDot : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [.num 1, .num 2, .num 3])] [(.dotCall (.resolve "x") "first" none)])
#guard obs case_special__firstDot == "ok raw=1 n=1"

-- special__lastSeq: last((1, 2, 3))
def case_special__lastSeq : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "last") [(.capture [.num 1, .num 2, .num 3])])])
#guard obs case_special__lastSeq == "ok raw=3 n=1"

-- special__lastListElementStaysExact: last([1, [2, 3]])
def case_special__lastListElementStaysExact : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "last") [(.listLiteral [.num 1, (.listLiteral [.num 2, .num 3])])])])
#guard obs case_special__lastListElementStaysExact == "ok raw=L[2, 3] n=1"

-- special__lastEmpty: last(())
def case_special__lastEmpty : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "last") [(.emptySequence 0)])])
#guard obs case_special__lastEmpty == "err arity"

-- special__orderDescSeq: orderDesc((1, 3, 2))
def case_special__orderDescSeq : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "orderDesc") [(.capture [.num 1, .num 3, .num 2])])])
#guard obs case_special__orderDescSeq == "ok raw=L[3, 2, 1] n=1"

-- special__orderDescList: orderDesc([2, 1])
def case_special__orderDescList : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "orderDesc") [(.listLiteral [.num 2, .num 1])])])
#guard obs case_special__orderDescList == "ok raw=L[2, 1] n=1"

-- special__orderDescDuplicates: orderDesc((2, 1, 2))
def case_special__orderDescDuplicates : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "orderDesc") [(.capture [.num 2, .num 1, .num 2])])])
#guard obs case_special__orderDescDuplicates == "ok raw=L[2, 2, 1] n=1"

-- special__orderDescScalar: orderDesc(7)
def case_special__orderDescScalar : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "orderDesc") [.num 7])])
#guard obs case_special__orderDescScalar == "ok raw=L[7] n=1"

-- special__orderDescEmpty: orderDesc(())
def case_special__orderDescEmpty : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "orderDesc") [(.emptySequence 0)])])
#guard obs case_special__orderDescEmpty == "ok raw=L[] n=1"

-- special__orderDescString: orderDesc(('b', 'a'))
def case_special__orderDescString : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "orderDesc") [(.capture [.stringLiteral "b", .stringLiteral "a"])])])
#guard obs case_special__orderDescString == "err arity"

-- special__orderDescDot: x = 1, 3, 2 \n x.orderDesc
def case_special__orderDescDot : Expr :=
  .algorithmExpr (alg [] [] [privateProp "x" (alg [] [] [] [.num 1, .num 3, .num 2])] [(.dotCall (.resolve "x") "orderDesc" none)])
#guard obs case_special__orderDescDot == "ok raw=L[3, 2, 1] n=1"

-- special__whileCountdown: S(a) = a - 1, a > 1 \n while(S, 3)
def case_special__whileCountdown : Expr :=
  .algorithmExpr (alg [] [] [privateProp "S" (alg ["a"] [] [] [(.binary .sub (.param "a") (.num 1)), (.comparison (.param "a") [{ op := .gt, operand := (.num 1) }])])] [(.call (.resolve "while") [.resolve "S", .num 3])])
#guard obs case_special__whileCountdown == "ok raw=1 n=1"

-- special__whileZeroIterations: S(a) = a, 0 \n while(S, 5)
def case_special__whileZeroIterations : Expr :=
  .algorithmExpr (alg [] [] [privateProp "S" (alg ["a"] [] [] [.param "a", .num 0])] [(.call (.resolve "while") [.resolve "S", .num 5])])
#guard obs case_special__whileZeroIterations == "err type"

-- special__whileTwoSlotState: S(a, b) = a + 1, b * 2, a < 3 \n while(S, 1, 1)
def case_special__whileTwoSlotState : Expr :=
  .algorithmExpr (alg [] [] [privateProp "S" (alg ["a", "b"] [] [] [(.binary .add (.param "a") (.num 1)), (.binary .mul (.param "b") (.num 2)), (.comparison (.param "a") [{ op := .lt, operand := (.num 3) }])])] [(.call (.resolve "while") [.resolve "S", .num 1, .num 1])])
#guard obs case_special__whileTwoSlotState == "ok raw=S[3, 4] n=2"

-- special__whileEmptyInitialState: S(a) = a, 0 \n while(S, ())
def case_special__whileEmptyInitialState : Expr :=
  .algorithmExpr (alg [] [] [privateProp "S" (alg ["a"] [] [] [.param "a", .num 0])] [(.call (.resolve "while") [.resolve "S", (.emptySequence 0)])])
#guard obs case_special__whileEmptyInitialState == "err type"

-- special__whileNonNumericContinuation: S(a) = a, () \n while(S, 1)
def case_special__whileNonNumericContinuation : Expr :=
  .algorithmExpr (alg [] [] [privateProp "S" (alg ["a"] [] [] [.param "a", (.emptySequence 0)])] [(.call (.resolve "while") [.resolve "S", .num 1])])
#guard obs case_special__whileNonNumericContinuation == "err type"

-- special__whileDot: S(a) = a - 1, a > 1 \n S.while(3)
def case_special__whileDot : Expr :=
  .algorithmExpr (alg [] [] [privateProp "S" (alg ["a"] [] [] [(.binary .sub (.param "a") (.num 1)), (.comparison (.param "a") [{ op := .gt, operand := (.num 1) }])])] [(.dotCall (.resolve "S") "while" (some [.num 3]))])
#guard obs case_special__whileDot == "ok raw=1 n=1"

-- special__containsSequenceItem: contains(((1, 2), 3), (1, 2))
def case_special__containsSequenceItem : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "contains") [(.capture [(.capture [.num 1, .num 2]), .num 3]), (.capture [.num 1, .num 2])])])
#guard obs case_special__containsSequenceItem == "ok raw=true n=1"

-- special__containsListItem: contains([[1, 2], 3], [1, 2])
def case_special__containsListItem : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "contains") [(.listLiteral [(.listLiteral [.num 1, .num 2]), .num 3]), (.listLiteral [.num 1, .num 2])])])
#guard obs case_special__containsListItem == "ok raw=true n=1"

-- special__containsEmptyItem: contains(((), 1), ())
def case_special__containsEmptyItem : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "contains") [(.capture [(.emptySequence 0), .num 1]), (.emptySequence 0)])])
#guard obs case_special__containsEmptyItem == "ok raw=true n=1"

-- special__containsScalarCollection: contains(7, 7)
def case_special__containsScalarCollection : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "contains") [.num 7, .num 7])])
#guard obs case_special__containsScalarCollection == "ok raw=true n=1"

-- special__containsAcrossKinds: contains(([1, 2], 3), (1, 2))
def case_special__containsAcrossKinds : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "contains") [(.capture [(.listLiteral [.num 1, .num 2]), .num 3]), (.capture [.num 1, .num 2])])])
#guard obs case_special__containsAcrossKinds == "ok raw=false n=1"

-- special__openPublicMember: Lib = { \n     public X = 101 \n } \n A = { \n     open Lib \n     X \n } \n A
def case_special__openPublicMember : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Lib" (alg [] [] [publicProp "X" (alg [] [] [] [.num 101])] []), privateProp "A" (alg [] [.resolve "Lib"] [] [.resolve "X"])] [.resolve "A"])
#guard obs case_special__openPublicMember == "ok raw=101 n=1"

-- special__openPrivateMemberHidden: Lib = { \n     X = 101 \n } \n A = { \n     open Lib \n     X \n } \n A(707)
def case_special__openPrivateMemberHidden : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Lib" (alg [] [] [privateProp "X" (alg [] [] [] [.num 101])] []), privateProp "A" (alg ["X"] [.resolve "Lib"] [] [.param "X"])] [(.call (.resolve "A") [.num 707])])
#guard obs case_special__openPrivateMemberHidden == "ok raw=707 n=1"

-- special__openLocalOnlyCapturedParamsInsideOwner: Outer(p) = { \n     open Lib \n     Lib = { \n         public X = p + 101 \n     } \n     X \n } \n Outer(1)
def case_special__openLocalOnlyCapturedParamsInsideOwner : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Outer" (alg ["p"] [.resolve "Lib"] [privateProp "Lib" (alg [] [] [{ (publicLocalProp "X" (.localCapturedAncestorParams ["p"]) (alg [] [] [] [(.binary .add (.param "p") (.num 101))])) with requiredOwnerDepths := some [("p", some 1)] }] [])] [.resolve "X"])] [(.call (.resolve "Outer") [.num 1])])
#guard obs case_special__openLocalOnlyCapturedParamsInsideOwner == "ok raw=102 n=1"

-- special__openLocalOnlyCapturedParamsOutsideOwner: Outer(p) = { \n     public Lib = { \n         public X = p + 101 \n     } \n     0 \n } \n A = { \n     open Outer.Lib \n     X \n } \n A
def case_special__openLocalOnlyCapturedParamsOutsideOwner : Expr :=
  .algorithmExpr (alg [] [] [{ (privateLocalProp "A" (.localCapturedAncestorParams ["p"]) (alg [] [(.dotCall (.resolve "Outer") "Lib" none)] [] [.resolve "X"])) with requiredOwnerDepths := some [("p", none)] }, privateProp "Outer" (alg ["p"] [] [publicProp "Lib" (alg [] [] [{ (publicLocalProp "X" (.localCapturedAncestorParams ["p"]) (alg [] [] [] [(.binary .add (.param "p") (.num 101))])) with requiredOwnerDepths := some [("p", some 1)] }] [])] [.num 0])] [.resolve "A"])
#guard obs case_special__openLocalOnlyCapturedParamsOutsideOwner == "err localOnlyProperty"

-- special__openTwoProvidersAmbiguous: L1 = { \n     public X = 101 \n } \n L2 = { \n     public X = 202 \n } \n A = { \n     open L1, L2 \n     X \n } \n A
def case_special__openTwoProvidersAmbiguous : Expr :=
  .algorithmExpr (alg [] [] [privateProp "L1" (alg [] [] [publicProp "X" (alg [] [] [] [.num 101])] []), privateProp "L2" (alg [] [] [publicProp "X" (alg [] [] [] [.num 202])] []), privateProp "A" (alg [] [.resolve "L1", .resolve "L2"] [] [.resolve "X"])] [.resolve "A"])
#guard obs case_special__openTwoProvidersAmbiguous == "err ambiguousOpen"

-- special__openDuplicateTargetDedup: Lib = { \n     public X = 101 \n } \n A = { \n     open Lib, Lib \n     X \n } \n A
def case_special__openDuplicateTargetDedup : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Lib" (alg [] [] [publicProp "X" (alg [] [] [] [.num 101])] []), privateProp "A" (alg [] [.resolve "Lib", .resolve "Lib"] [] [.resolve "X"])] [.resolve "A"])
#guard obs case_special__openDuplicateTargetDedup == "ok raw=101 n=1"

-- special__openDuplicateDottedTargetDedup: Lib = { \n     public S = { \n         public X = 101 \n     } \n } \n A = { \n     open Lib.S, Lib.S \n     X \n } \n A
def case_special__openDuplicateDottedTargetDedup : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Lib" (alg [] [] [publicProp "S" (alg [] [] [publicProp "X" (alg [] [] [] [.num 101])] [])] []), privateProp "A" (alg [] [(.dotCall (.resolve "Lib") "S" none), (.dotCall (.resolve "Lib") "S" none)] [] [.resolve "X"])] [.resolve "A"])
#guard obs case_special__openDuplicateDottedTargetDedup == "ok raw=101 n=1"

-- special__openDuplicateInlineBlocksAmbiguous: A = { \n     open { public X = 101 }, { public X = 202 } \n     X \n } \n A
def case_special__openDuplicateInlineBlocksAmbiguous : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [(.algorithmExpr (alg [] [] [publicProp "X" (alg [] [] [] [.num 101])] [])), (.algorithmExpr (alg [] [] [publicProp "X" (alg [] [] [] [.num 202])] []))] [] [.resolve "X"])] [.resolve "A"])
#guard obs case_special__openDuplicateInlineBlocksAmbiguous == "err ambiguousOpen"

-- special__openInlineBlock: A = { \n     open { public X = 101 } \n     X \n } \n A
def case_special__openInlineBlock : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [(.algorithmExpr (alg [] [] [publicProp "X" (alg [] [] [] [.num 101])] []))] [] [.resolve "X"])] [.resolve "A"])
#guard obs case_special__openInlineBlock == "ok raw=101 n=1"

-- special__openInlineBlockPrivateHidden: A = { \n     open { X = 101 } \n     X \n } \n A(707)
def case_special__openInlineBlockPrivateHidden : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg ["X"] [(.algorithmExpr (alg [] [] [privateProp "X" (alg [] [] [] [.num 101])] []))] [] [.param "X"])] [(.call (.resolve "A") [.num 707])])
#guard obs case_special__openInlineBlockPrivateHidden == "ok raw=707 n=1"

-- special__openDottedPath: Lib = { \n     public S = { \n         public X = 101 \n     } \n } \n A = { \n     open Lib.S \n     X \n } \n A
def case_special__openDottedPath : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Lib" (alg [] [] [publicProp "S" (alg [] [] [publicProp "X" (alg [] [] [] [.num 101])] [])] []), privateProp "A" (alg [] [(.dotCall (.resolve "Lib") "S" none)] [] [.resolve "X"])] [.resolve "A"])
#guard obs case_special__openDottedPath == "ok raw=101 n=1"

-- special__openLocalShadowsOpenedName: Lib = { \n     public X = 101 \n } \n A = { \n     open Lib \n     X = 202 \n     X \n } \n A
def case_special__openLocalShadowsOpenedName : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Lib" (alg [] [] [publicProp "X" (alg [] [] [] [.num 101])] []), privateProp "A" (alg [] [.resolve "Lib"] [privateProp "X" (alg [] [] [] [.num 202])] [.resolve "X"])] [.resolve "A"])
#guard obs case_special__openLocalShadowsOpenedName == "ok raw=202 n=1"

-- special__openAncestorPropertyWins: Lib = { \n     public X = 101 \n } \n A = { \n     X = 202 \n     Inner = { \n         open Lib \n         X \n     } \n     Inner \n } \n A
def case_special__openAncestorPropertyWins : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Lib" (alg [] [] [publicProp "X" (alg [] [] [] [.num 101])] []), privateProp "A" (alg [] [] [privateProp "X" (alg [] [] [] [.num 202]), privateProp "Inner" (alg [] [.resolve "Lib"] [] [.resolve "X"])] [.resolve "Inner"])] [.resolve "A"])
#guard obs case_special__openAncestorPropertyWins == "ok raw=202 n=1"

-- special__openParentScopeReachesChild: Lib = { \n     public X = 101 \n } \n A = { \n     open Lib \n     Inner = { \n         X \n     } \n     Inner \n } \n A
def case_special__openParentScopeReachesChild : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Lib" (alg [] [] [publicProp "X" (alg [] [] [] [.num 101])] []), privateProp "A" (alg [] [.resolve "Lib"] [privateProp "Inner" (alg [] [] [] [.resolve "X"])] [.resolve "Inner"])] [.resolve "A"])
#guard obs case_special__openParentScopeReachesChild == "ok raw=101 n=1"

-- special__openNestedDoesNotLeakOutward: Lib = { \n     public X = 101 \n } \n A = { \n     Inner = { \n         open Lib \n         X \n     } \n     X \n } \n A(707)
def case_special__openNestedDoesNotLeakOutward : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Lib" (alg [] [] [publicProp "X" (alg [] [] [] [.num 101])] []), privateProp "A" (alg ["X"] [] [{ (privateLocalProp "Inner" (.localCapturedAncestorParams ["X"]) (alg [] [.resolve "Lib"] [] [.param "X"])) with requiredOwnerDepths := some [("X", some 0)] }] [.param "X"])] [(.call (.resolve "A") [.num 707])])
#guard obs case_special__openNestedDoesNotLeakOutward == "ok raw=707 n=1"

-- special__openHeadDefinedLater: A = { \n     open Lib \n     X \n } \n Lib = { \n     public X = 101 \n } \n A
def case_special__openHeadDefinedLater : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [.resolve "Lib"] [] [.resolve "X"]), privateProp "Lib" (alg [] [] [publicProp "X" (alg [] [] [] [.num 101])] [])] [.resolve "A"])
#guard obs case_special__openHeadDefinedLater == "ok raw=101 n=1"

-- special__openBuiltinNameCollision: Lib = { \n     public count = 101 \n } \n A = { \n     open Lib \n     count([1, 2, 3]) \n } \n A
def case_special__openBuiltinNameCollision : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Lib" (alg [] [] [publicProp "count" (alg [] [] [] [.num 101])] []), privateProp "A" (alg [] [.resolve "Lib"] [] [(.call (.resolve "count") [(.listLiteral [.num 1, .num 2, .num 3])])])] [.resolve "A"])
#guard obs case_special__openBuiltinNameCollision == "ok raw=3 n=1"

-- special__structuralDotSeesPrivateMember: Lib = { \n     X = 101 \n } \n Lib.X
def case_special__structuralDotSeesPrivateMember : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Lib" (alg [] [] [privateProp "X" (alg [] [] [] [.num 101])] [])] [(.dotCall (.resolve "Lib") "X" none)])
#guard obs case_special__structuralDotSeesPrivateMember == "ok raw=101 n=1"

-- special__openPrivateMemberIsNotASecondProvider: Pub = { \n     public X = 101 \n } \n Lib = { \n     X = 202 \n } \n A = { \n     open Pub, Lib \n     X \n } \n A
def case_special__openPrivateMemberIsNotASecondProvider : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Pub" (alg [] [] [publicProp "X" (alg [] [] [] [.num 101])] []), privateProp "Lib" (alg [] [] [privateProp "X" (alg [] [] [] [.num 202])] []), privateProp "A" (alg [] [.resolve "Pub", .resolve "Lib"] [] [.resolve "X"])] [.resolve "A"])
#guard obs case_special__openPrivateMemberIsNotASecondProvider == "ok raw=101 n=1"

-- special__openLocalOnlyMemberIsASecondProvider: Pub = { \n     public X = 101 \n } \n Outer(p) = { \n     public Lib = { \n         public X = p + 202 \n     } \n     0 \n } \n A = { \n     open Pub, Outer.Lib \n     X \n } \n A
def case_special__openLocalOnlyMemberIsASecondProvider : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Pub" (alg [] [] [publicProp "X" (alg [] [] [] [.num 101])] []), privateProp "A" (alg [] [.resolve "Pub", (.dotCall (.resolve "Outer") "Lib" none)] [] [.resolve "X"]), privateProp "Outer" (alg ["p"] [] [publicProp "Lib" (alg [] [] [{ (publicLocalProp "X" (.localCapturedAncestorParams ["p"]) (alg [] [] [] [(.binary .add (.param "p") (.num 202))])) with requiredOwnerDepths := some [("p", some 1)] }] [])] [.num 0])] [.resolve "A"])
#guard obs case_special__openLocalOnlyMemberIsASecondProvider == "err ambiguousOpen"

-- special__ifSelectedParameterizedBranchIsArity: Inc(x) = x + 1 \n if(true, Inc, 0)
def case_special__ifSelectedParameterizedBranchIsArity : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Inc" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 1))])] [(.call (.resolve "if") [.boolLiteral true, .resolve "Inc", .num 0])])
#guard obs case_special__ifSelectedParameterizedBranchIsArity == "err arity"

-- special__ifSelectedParameterizedFalseBranchIsArity: Inc(x) = x + 1 \n if(false, 0, Inc)
def case_special__ifSelectedParameterizedFalseBranchIsArity : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Inc" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 1))])] [(.call (.resolve "if") [.boolLiteral false, .num 0, .resolve "Inc"])])
#guard obs case_special__ifSelectedParameterizedFalseBranchIsArity == "err arity"

-- special__ifParameterizedConditionIsArity: Inc(x) = x + 1 \n if(Inc, 1, 0)
def case_special__ifParameterizedConditionIsArity : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Inc" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 1))])] [(.call (.resolve "if") [.resolve "Inc", .num 1, .num 0])])
#guard obs case_special__ifParameterizedConditionIsArity == "err arity"

-- special__ifUnselectedParameterizedBranchStaysLazy: Inc(x) = x + 1 \n if(false, Inc, 7)
def case_special__ifUnselectedParameterizedBranchStaysLazy : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Inc" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 1))])] [(.call (.resolve "if") [.boolLiteral false, .resolve "Inc", .num 7])])
#guard obs case_special__ifUnselectedParameterizedBranchStaysLazy == "ok raw=7 n=1"

-- special__ifZeroParameterBranchIsValue: A = 7 \n if(true, A, 0)
def case_special__ifZeroParameterBranchIsValue : Expr :=
  .algorithmExpr (alg [] [] [privateProp "A" (alg [] [] [] [.num 7])] [(.call (.resolve "if") [.boolLiteral true, .resolve "A", .num 0])])
#guard obs case_special__ifZeroParameterBranchIsValue == "ok raw=7 n=1"

-- special__ifParameterIgnoringBodyStillArity: K(x) = 5 \n if(true, K, 0)
def case_special__ifParameterIgnoringBodyStillArity : Expr :=
  .algorithmExpr (alg [] [] [privateProp "K" (alg ["x"] [] [] [.num 5])] [(.call (.resolve "if") [.boolLiteral true, .resolve "K", .num 0])])
#guard obs case_special__ifParameterIgnoringBodyStillArity == "err arity"

-- special__ifCollectingCallableSlotIsCollectedValue: Collect(*xs) = xs \n if(true, Collect, 0)
def case_special__ifCollectingCallableSlotIsCollectedValue : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Collect" (algWithParameters [{ name := "xs", kind := .collecting }] [] [] [.param "xs"])] [(.call (.resolve "if") [.boolLiteral true, .resolve "Collect", .num 0])])
#guard obs case_special__ifCollectingCallableSlotIsCollectedValue == "ok raw=L[] n=1"

-- special__ifCollectingCallableExplicitCallIsSameValue: Collect(*xs) = xs \n if(true, Collect(), 0)
def case_special__ifCollectingCallableExplicitCallIsSameValue : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Collect" (algWithParameters [{ name := "xs", kind := .collecting }] [] [] [.param "xs"])] [(.call (.resolve "if") [.boolLiteral true, (.call (.resolve "Collect") []), .num 0])])
#guard obs case_special__ifCollectingCallableExplicitCallIsSameValue == "ok raw=L[] n=1"

-- special__bareCollectingCallableIsAValue: Only(*xs) = xs \n Only
def case_special__bareCollectingCallableIsAValue : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Only" (algWithParameters [{ name := "xs", kind := .collecting }] [] [] [.param "xs"])] [.resolve "Only"])
#guard obs case_special__bareCollectingCallableIsAValue == "ok raw=L[] n=1"

-- special__bareCollectingCallableCountAgreesWithDottedForm: Only(*xs) = xs \n count(Only), Only.count
def case_special__bareCollectingCallableCountAgreesWithDottedForm : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Only" (algWithParameters [{ name := "xs", kind := .collecting }] [] [] [.param "xs"])] [(.call (.resolve "count") [.resolve "Only"]), (.dotCall (.resolve "Only") "count" none)])
#guard obs case_special__bareCollectingCallableCountAgreesWithDottedForm == "ok raw=S[0, 0] n=2"

-- special__ifRequiredPrefixBesideCollectorIsArity: Head(x, *rest) = x \n if(true, Head, 0)
def case_special__ifRequiredPrefixBesideCollectorIsArity : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Head" (algWithParameters [{ name := "x" }, { name := "rest", kind := .collecting }] [] [] [.param "x"])] [(.call (.resolve "if") [.boolLiteral true, .resolve "Head", .num 0])])
#guard obs case_special__ifRequiredPrefixBesideCollectorIsArity == "err arity"

-- special__ifRequiredSuffixBesideCollectorIsArity: Tail(*rest, z) = z \n if(true, Tail, 0)
def case_special__ifRequiredSuffixBesideCollectorIsArity : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Tail" (algWithParameters [{ name := "rest", kind := .collecting }, { name := "z" }] [] [] [.param "z"])] [(.call (.resolve "if") [.boolLiteral true, .resolve "Tail", .num 0])])
#guard obs case_special__ifRequiredSuffixBesideCollectorIsArity == "err arity"

-- special__ifNestedCollectingPatternIsArity: P((x, *rest)) = x \n if(true, P, 0)
def case_special__ifNestedCollectingPatternIsArity : Expr :=
  .algorithmExpr (alg [] [] [privateProp "P" (algWithParameterPatterns [.sequenceValue [.capture { name := "x" }, .capture { name := "rest", kind := .collecting }]] [] [] [.param "x"])] [(.call (.resolve "if") [.boolLiteral true, .resolve "P", .num 0])])
#guard obs case_special__ifNestedCollectingPatternIsArity == "err arity"

-- special__collectingCallableStaysACallbackAlgorithm: Only(*xs) = xs \n map((1, 2), Only)
def case_special__collectingCallableStaysACallbackAlgorithm : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Only" (algWithParameters [{ name := "xs", kind := .collecting }] [] [] [.param "xs"])] [(.call (.resolve "map") [(.capture [.num 1, .num 2]), .resolve "Only"])])
#guard obs case_special__collectingCallableStaysACallbackAlgorithm == "ok raw=L[L[1], L[2]] n=1"

-- special__ifAlgorithmChannelParameterSlotIsArity: Inc(x) = x + 1 \n Apply(g) = if(true, g, 0) \n Apply(Inc)
def case_special__ifAlgorithmChannelParameterSlotIsArity : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Inc" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 1))]), privateProp "Apply" (alg ["g"] [] [] [(.call (.resolve "if") [.boolLiteral true, .param "g", .num 0])])] [(.call (.resolve "Apply") [.resolve "Inc"])])
#guard obs case_special__ifAlgorithmChannelParameterSlotIsArity == "err arity"

-- special__repeatInitialParameterizedSlotIsArity: Inc(x) = x + 1 \n Step(s) = s + 1 \n repeat(Step, 1, Inc)
def case_special__repeatInitialParameterizedSlotIsArity : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Inc" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 1))]), privateProp "Step" (alg ["s"] [] [] [(.binary .add (.param "s") (.num 1))])] [(.call (.resolve "repeat") [.resolve "Step", .num 1, .resolve "Inc"])])
#guard obs case_special__repeatInitialParameterizedSlotIsArity == "err arity"

-- special__repeatCountParameterizedSlotIsArity: Inc(x) = x + 1 \n Step(s) = s + 1 \n repeat(Step, Inc, 0)
def case_special__repeatCountParameterizedSlotIsArity : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Inc" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 1))]), privateProp "Step" (alg ["s"] [] [] [(.binary .add (.param "s") (.num 1))])] [(.call (.resolve "repeat") [.resolve "Step", .resolve "Inc", .num 0])])
#guard obs case_special__repeatCountParameterizedSlotIsArity == "err arity"

-- special__whileInitialParameterizedSlotIsArity: Inc(x) = x + 1 \n Down(s) = s - 1, s \n while(Down, Inc)
def case_special__whileInitialParameterizedSlotIsArity : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Inc" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 1))]), privateProp "Down" (alg ["s"] [] [] [(.binary .sub (.param "s") (.num 1)), .param "s"])] [(.call (.resolve "while") [.resolve "Down", .resolve "Inc"])])
#guard obs case_special__whileInitialParameterizedSlotIsArity == "err arity"

-- special__atomsParameterizedSlotIsArity: Inc(x) = x + 1 \n atoms(Inc)
def case_special__atomsParameterizedSlotIsArity : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Inc" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 1))])] [(.call (.resolve "atoms") [.resolve "Inc"])])
#guard obs case_special__atomsParameterizedSlotIsArity == "err arity"

-- special__rangeParameterizedSlotIsArity: Inc(x) = x + 1 \n range(1, Inc)
def case_special__rangeParameterizedSlotIsArity : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Inc" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 1))])] [(.call (.resolve "range") [.num 1, .resolve "Inc"])])
#guard obs case_special__rangeParameterizedSlotIsArity == "err arity"

-- special__dotStringParameterizedReceiverIsArity: Inc(x) = x + 1 \n Inc.string
def case_special__dotStringParameterizedReceiverIsArity : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Inc" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 1))])] [(.dotCall (.resolve "Inc") "string" none)])
#guard obs case_special__dotStringParameterizedReceiverIsArity == "err arity"

-- special__dotStringNavigatedParameterizedMemberIsArity: Lib = { Sub(x) = x } \n Lib.Sub.string
def case_special__dotStringNavigatedParameterizedMemberIsArity : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Lib" (alg [] [] [privateProp "Sub" (alg ["x"] [] [] [.param "x"])] [])] [(.dotCall (.dotCall (.resolve "Lib") "Sub" none) "string" none)])
#guard obs case_special__dotStringNavigatedParameterizedMemberIsArity == "err arity"

-- special__reduceParameterIgnoringInitialStillRejected: K(x) = 5 \n Add(e, a) = e + a \n reduce([1, 2], Add, K)
def case_special__reduceParameterIgnoringInitialStillRejected : Expr :=
  .algorithmExpr (alg [] [] [privateProp "K" (alg ["x"] [] [] [.num 5]), privateProp "Add" (alg ["e", "a"] [] [] [(.binary .add (.param "e") (.param "a"))])] [(.call (.resolve "reduce") [(.listLiteral [.num 1, .num 2]), .resolve "Add", .resolve "K"])])
#guard obs case_special__reduceParameterIgnoringInitialStillRejected == "err arity"

-- special__repeatParameterizedStepIsCallback: Inc(x) = x + 1 \n repeat(Inc, 2, 0)
def case_special__repeatParameterizedStepIsCallback : Expr :=
  .algorithmExpr (alg [] [] [privateProp "Inc" (alg ["x"] [] [] [(.binary .add (.param "x") (.num 1))])] [(.call (.resolve "repeat") [.resolve "Inc", .num 2, .num 0])])
#guard obs case_special__repeatParameterizedStepIsCallback == "ok raw=2 n=1"

-- 2244 differential cases.

/--
Machine-checked surface partition count: the id list is built by the same
loop that emits the guards above, while the expected total is computed
independently from the corpus partition, so a generation bug fails `lake build`.
-/
def surfaceCaseIds : List String := [
  "root__e",
  "root__n0",
  "root__n1",
  "root__bt",
  "root__bf",
  "root__pbt",
  "root__pbt_e",
  "root__pbt_1",
  "root__lbt",
  "root__lbt_bf",
  "root__lpbt_1",
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
  "capture__bt",
  "capture__bf",
  "capture__pbt",
  "capture__pbt_e",
  "capture__pbt_1",
  "capture__lbt",
  "capture__lbt_bf",
  "capture__lpbt_1",
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
  "captureCall__bt",
  "captureCall__bf",
  "captureCall__pbt",
  "captureCall__pbt_e",
  "captureCall__pbt_1",
  "captureCall__lbt",
  "captureCall__lbt_bf",
  "captureCall__lpbt_1",
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
  "dotAccess__bt",
  "dotAccess__bf",
  "dotAccess__pbt",
  "dotAccess__pbt_e",
  "dotAccess__pbt_1",
  "dotAccess__lbt",
  "dotAccess__lbt_bf",
  "dotAccess__lpbt_1",
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
  "dotAccessCall__bt",
  "dotAccessCall__bf",
  "dotAccessCall__pbt",
  "dotAccessCall__pbt_e",
  "dotAccessCall__pbt_1",
  "dotAccessCall__lbt",
  "dotAccessCall__lbt_bf",
  "dotAccessCall__lpbt_1",
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
  "fixed__bt",
  "fixed__bf",
  "fixed__pbt",
  "fixed__pbt_e",
  "fixed__pbt_1",
  "fixed__lbt",
  "fixed__lbt_bf",
  "fixed__lpbt_1",
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
  "fixedSpread__bt",
  "fixedSpread__bf",
  "fixedSpread__pbt",
  "fixedSpread__pbt_e",
  "fixedSpread__pbt_1",
  "fixedSpread__lbt",
  "fixedSpread__lbt_bf",
  "fixedSpread__lpbt_1",
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
  "collecting__e",
  "collecting__n0",
  "collecting__n1",
  "collecting__bt",
  "collecting__bf",
  "collecting__pbt",
  "collecting__pbt_e",
  "collecting__pbt_1",
  "collecting__lbt",
  "collecting__lbt_bf",
  "collecting__lpbt_1",
  "collecting__p1",
  "collecting__p12",
  "collecting__p123",
  "collecting__pee",
  "collecting__pe1",
  "collecting__p1e",
  "collecting__p12_3",
  "collecting__p12_34",
  "collecting__pe_12",
  "collecting__ppe1_2",
  "collecting__p12_e",
  "collecting__ppe",
  "collecting__pp1",
  "collecting__ppp12",
  "collecting__le",
  "collecting__l7",
  "collecting__l12",
  "collecting__l12_3",
  "collecting__lle",
  "collecting__l_e",
  "collecting__l_p12",
  "collecting__p_l12",
  "collecting__pl1",
  "collectingSpread__e",
  "collectingSpread__n0",
  "collectingSpread__n1",
  "collectingSpread__bt",
  "collectingSpread__bf",
  "collectingSpread__pbt",
  "collectingSpread__pbt_e",
  "collectingSpread__pbt_1",
  "collectingSpread__lbt",
  "collectingSpread__lbt_bf",
  "collectingSpread__lpbt_1",
  "collectingSpread__p1",
  "collectingSpread__p12",
  "collectingSpread__p123",
  "collectingSpread__pee",
  "collectingSpread__pe1",
  "collectingSpread__p1e",
  "collectingSpread__p12_3",
  "collectingSpread__p12_34",
  "collectingSpread__pe_12",
  "collectingSpread__ppe1_2",
  "collectingSpread__p12_e",
  "collectingSpread__ppe",
  "collectingSpread__pp1",
  "collectingSpread__ppp12",
  "collectingSpread__le",
  "collectingSpread__l7",
  "collectingSpread__l12",
  "collectingSpread__l12_3",
  "collectingSpread__lle",
  "collectingSpread__l_e",
  "collectingSpread__l_p12",
  "collectingSpread__p_l12",
  "collectingSpread__pl1",
  "collectingViaProp__e",
  "collectingViaProp__n0",
  "collectingViaProp__n1",
  "collectingViaProp__bt",
  "collectingViaProp__bf",
  "collectingViaProp__pbt",
  "collectingViaProp__pbt_e",
  "collectingViaProp__pbt_1",
  "collectingViaProp__lbt",
  "collectingViaProp__lbt_bf",
  "collectingViaProp__lpbt_1",
  "collectingViaProp__p1",
  "collectingViaProp__p12",
  "collectingViaProp__p123",
  "collectingViaProp__pee",
  "collectingViaProp__pe1",
  "collectingViaProp__p1e",
  "collectingViaProp__p12_3",
  "collectingViaProp__p12_34",
  "collectingViaProp__pe_12",
  "collectingViaProp__ppe1_2",
  "collectingViaProp__p12_e",
  "collectingViaProp__ppe",
  "collectingViaProp__pp1",
  "collectingViaProp__ppp12",
  "collectingViaProp__le",
  "collectingViaProp__l7",
  "collectingViaProp__l12",
  "collectingViaProp__l12_3",
  "collectingViaProp__lle",
  "collectingViaProp__l_e",
  "collectingViaProp__l_p12",
  "collectingViaProp__p_l12",
  "collectingViaProp__pl1",
  "dotCollectingViaProp__e",
  "dotCollectingViaProp__n0",
  "dotCollectingViaProp__n1",
  "dotCollectingViaProp__bt",
  "dotCollectingViaProp__bf",
  "dotCollectingViaProp__pbt",
  "dotCollectingViaProp__pbt_e",
  "dotCollectingViaProp__pbt_1",
  "dotCollectingViaProp__lbt",
  "dotCollectingViaProp__lbt_bf",
  "dotCollectingViaProp__lpbt_1",
  "dotCollectingViaProp__p1",
  "dotCollectingViaProp__p12",
  "dotCollectingViaProp__p123",
  "dotCollectingViaProp__pee",
  "dotCollectingViaProp__pe1",
  "dotCollectingViaProp__p1e",
  "dotCollectingViaProp__p12_3",
  "dotCollectingViaProp__p12_34",
  "dotCollectingViaProp__pe_12",
  "dotCollectingViaProp__ppe1_2",
  "dotCollectingViaProp__p12_e",
  "dotCollectingViaProp__ppe",
  "dotCollectingViaProp__pp1",
  "dotCollectingViaProp__ppp12",
  "dotCollectingViaProp__le",
  "dotCollectingViaProp__l7",
  "dotCollectingViaProp__l12",
  "dotCollectingViaProp__l12_3",
  "dotCollectingViaProp__lle",
  "dotCollectingViaProp__l_e",
  "dotCollectingViaProp__l_p12",
  "dotCollectingViaProp__p_l12",
  "dotCollectingViaProp__pl1",
  "literalDotCollecting__e",
  "literalDotCollecting__n0",
  "literalDotCollecting__n1",
  "literalDotCollecting__bt",
  "literalDotCollecting__bf",
  "literalDotCollecting__pbt",
  "literalDotCollecting__pbt_e",
  "literalDotCollecting__pbt_1",
  "literalDotCollecting__lbt",
  "literalDotCollecting__lbt_bf",
  "literalDotCollecting__lpbt_1",
  "literalDotCollecting__p1",
  "literalDotCollecting__p12",
  "literalDotCollecting__p123",
  "literalDotCollecting__pee",
  "literalDotCollecting__pe1",
  "literalDotCollecting__p1e",
  "literalDotCollecting__p12_3",
  "literalDotCollecting__p12_34",
  "literalDotCollecting__pe_12",
  "literalDotCollecting__ppe1_2",
  "literalDotCollecting__p12_e",
  "literalDotCollecting__ppe",
  "literalDotCollecting__pp1",
  "literalDotCollecting__ppp12",
  "literalDotCollecting__le",
  "literalDotCollecting__l7",
  "literalDotCollecting__l12",
  "literalDotCollecting__l12_3",
  "literalDotCollecting__lle",
  "literalDotCollecting__l_e",
  "literalDotCollecting__l_p12",
  "literalDotCollecting__p_l12",
  "literalDotCollecting__pl1",
  "fluentSpreadCollecting__e",
  "fluentSpreadCollecting__n0",
  "fluentSpreadCollecting__n1",
  "fluentSpreadCollecting__bt",
  "fluentSpreadCollecting__bf",
  "fluentSpreadCollecting__pbt",
  "fluentSpreadCollecting__pbt_e",
  "fluentSpreadCollecting__pbt_1",
  "fluentSpreadCollecting__lbt",
  "fluentSpreadCollecting__lbt_bf",
  "fluentSpreadCollecting__lpbt_1",
  "fluentSpreadCollecting__p1",
  "fluentSpreadCollecting__p12",
  "fluentSpreadCollecting__p123",
  "fluentSpreadCollecting__pee",
  "fluentSpreadCollecting__pe1",
  "fluentSpreadCollecting__p1e",
  "fluentSpreadCollecting__p12_3",
  "fluentSpreadCollecting__p12_34",
  "fluentSpreadCollecting__pe_12",
  "fluentSpreadCollecting__ppe1_2",
  "fluentSpreadCollecting__p12_e",
  "fluentSpreadCollecting__ppe",
  "fluentSpreadCollecting__pp1",
  "fluentSpreadCollecting__ppp12",
  "fluentSpreadCollecting__le",
  "fluentSpreadCollecting__l7",
  "fluentSpreadCollecting__l12",
  "fluentSpreadCollecting__l12_3",
  "fluentSpreadCollecting__lle",
  "fluentSpreadCollecting__l_e",
  "fluentSpreadCollecting__l_p12",
  "fluentSpreadCollecting__p_l12",
  "fluentSpreadCollecting__pl1",
  "mixed_h__e",
  "mixed_h__n0",
  "mixed_h__n1",
  "mixed_h__bt",
  "mixed_h__bf",
  "mixed_h__pbt",
  "mixed_h__pbt_e",
  "mixed_h__pbt_1",
  "mixed_h__lbt",
  "mixed_h__lbt_bf",
  "mixed_h__lpbt_1",
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
  "mixed_t__bt",
  "mixed_t__bf",
  "mixed_t__pbt",
  "mixed_t__pbt_e",
  "mixed_t__pbt_1",
  "mixed_t__lbt",
  "mixed_t__lbt_bf",
  "mixed_t__lpbt_1",
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
  "mixedBack_t__bt",
  "mixedBack_t__bf",
  "mixedBack_t__pbt",
  "mixedBack_t__pbt_e",
  "mixedBack_t__pbt_1",
  "mixedBack_t__lbt",
  "mixedBack_t__lbt_bf",
  "mixedBack_t__lpbt_1",
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
  "mixedBack_z__bt",
  "mixedBack_z__bf",
  "mixedBack_z__pbt",
  "mixedBack_z__pbt_e",
  "mixedBack_z__pbt_1",
  "mixedBack_z__lbt",
  "mixedBack_z__lbt_bf",
  "mixedBack_z__lpbt_1",
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
  "deconPair_x__bt",
  "deconPair_x__bf",
  "deconPair_x__pbt",
  "deconPair_x__pbt_e",
  "deconPair_x__pbt_1",
  "deconPair_x__lbt",
  "deconPair_x__lbt_bf",
  "deconPair_x__lpbt_1",
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
  "deconPair_y__bt",
  "deconPair_y__bf",
  "deconPair_y__pbt",
  "deconPair_y__pbt_e",
  "deconPair_y__pbt_1",
  "deconPair_y__lbt",
  "deconPair_y__lbt_bf",
  "deconPair_y__lpbt_1",
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
  "deconPairSpread_x__bt",
  "deconPairSpread_x__bf",
  "deconPairSpread_x__pbt",
  "deconPairSpread_x__pbt_e",
  "deconPairSpread_x__pbt_1",
  "deconPairSpread_x__lbt",
  "deconPairSpread_x__lbt_bf",
  "deconPairSpread_x__lpbt_1",
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
  "deconCollect_t__bt",
  "deconCollect_t__bf",
  "deconCollect_t__pbt",
  "deconCollect_t__pbt_e",
  "deconCollect_t__pbt_1",
  "deconCollect_t__lbt",
  "deconCollect_t__lbt_bf",
  "deconCollect_t__lpbt_1",
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
  "deconCollectSpread_t__bt",
  "deconCollectSpread_t__bf",
  "deconCollectSpread_t__pbt",
  "deconCollectSpread_t__pbt_e",
  "deconCollectSpread_t__pbt_1",
  "deconCollectSpread_t__lbt",
  "deconCollectSpread_t__lbt_bf",
  "deconCollectSpread_t__lpbt_1",
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
  "deconPrefix_p__bt",
  "deconPrefix_p__bf",
  "deconPrefix_p__pbt",
  "deconPrefix_p__pbt_e",
  "deconPrefix_p__pbt_1",
  "deconPrefix_p__lbt",
  "deconPrefix_p__lbt_bf",
  "deconPrefix_p__lpbt_1",
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
  "deconPrefix_z__bt",
  "deconPrefix_z__bf",
  "deconPrefix_z__pbt",
  "deconPrefix_z__pbt_e",
  "deconPrefix_z__pbt_1",
  "deconPrefix_z__lbt",
  "deconPrefix_z__lbt_bf",
  "deconPrefix_z__lpbt_1",
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
  "seqWrapPair__bt",
  "seqWrapPair__bf",
  "seqWrapPair__pbt",
  "seqWrapPair__pbt_e",
  "seqWrapPair__pbt_1",
  "seqWrapPair__lbt",
  "seqWrapPair__lbt_bf",
  "seqWrapPair__lpbt_1",
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
  "seqWrapSolo__bt",
  "seqWrapSolo__bf",
  "seqWrapSolo__pbt",
  "seqWrapSolo__pbt_e",
  "seqWrapSolo__pbt_1",
  "seqWrapSolo__lbt",
  "seqWrapSolo__lbt_bf",
  "seqWrapSolo__lpbt_1",
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
  "spreadRoot__bt",
  "spreadRoot__bf",
  "spreadRoot__pbt",
  "spreadRoot__pbt_e",
  "spreadRoot__pbt_1",
  "spreadRoot__lbt",
  "spreadRoot__lbt_bf",
  "spreadRoot__lpbt_1",
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
  "spreadInSeq__bt",
  "spreadInSeq__bf",
  "spreadInSeq__pbt",
  "spreadInSeq__pbt_e",
  "spreadInSeq__pbt_1",
  "spreadInSeq__lbt",
  "spreadInSeq__lbt_bf",
  "spreadInSeq__lpbt_1",
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
  "count__bt",
  "count__bf",
  "count__pbt",
  "count__pbt_e",
  "count__pbt_1",
  "count__lbt",
  "count__lbt_bf",
  "count__lpbt_1",
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
  "countSpread__bt",
  "countSpread__bf",
  "countSpread__pbt",
  "countSpread__pbt_e",
  "countSpread__pbt_1",
  "countSpread__lbt",
  "countSpread__lbt_bf",
  "countSpread__lpbt_1",
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
  "dotCount__bt",
  "dotCount__bf",
  "dotCount__pbt",
  "dotCount__pbt_e",
  "dotCount__pbt_1",
  "dotCount__lbt",
  "dotCount__lbt_bf",
  "dotCount__lpbt_1",
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
  "literalDotCount__bt",
  "literalDotCount__bf",
  "literalDotCount__pbt",
  "literalDotCount__pbt_e",
  "literalDotCount__pbt_1",
  "literalDotCount__lbt",
  "literalDotCount__lbt_bf",
  "literalDotCount__lpbt_1",
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
  "index0__bt",
  "index0__bf",
  "index0__pbt",
  "index0__pbt_e",
  "index0__pbt_1",
  "index0__lbt",
  "index0__lbt_bf",
  "index0__lpbt_1",
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
  "index1__bt",
  "index1__bf",
  "index1__pbt",
  "index1__pbt_e",
  "index1__pbt_1",
  "index1__lbt",
  "index1__lbt_bf",
  "index1__lpbt_1",
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
  "indexBig__bt",
  "indexBig__bf",
  "indexBig__pbt",
  "indexBig__pbt_e",
  "indexBig__pbt_1",
  "indexBig__lbt",
  "indexBig__lbt_bf",
  "indexBig__lpbt_1",
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
  "eqSelf__bt",
  "eqSelf__bf",
  "eqSelf__pbt",
  "eqSelf__pbt_e",
  "eqSelf__pbt_1",
  "eqSelf__lbt",
  "eqSelf__lbt_bf",
  "eqSelf__lpbt_1",
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
  "neqSelf__bt",
  "neqSelf__bf",
  "neqSelf__pbt",
  "neqSelf__pbt_e",
  "neqSelf__pbt_1",
  "neqSelf__lbt",
  "neqSelf__lbt_bf",
  "neqSelf__lpbt_1",
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
  "eqIdentity__bt",
  "eqIdentity__bf",
  "eqIdentity__pbt",
  "eqIdentity__pbt_e",
  "eqIdentity__pbt_1",
  "eqIdentity__lbt",
  "eqIdentity__lbt_bf",
  "eqIdentity__lpbt_1",
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
  "identity__bt",
  "identity__bf",
  "identity__pbt",
  "identity__pbt_e",
  "identity__pbt_1",
  "identity__lbt",
  "identity__lbt_bf",
  "identity__lpbt_1",
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
  "identityTwice__bt",
  "identityTwice__bf",
  "identityTwice__pbt",
  "identityTwice__pbt_e",
  "identityTwice__pbt_1",
  "identityTwice__lbt",
  "identityTwice__lbt_bf",
  "identityTwice__lpbt_1",
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
  "propChain__bt",
  "propChain__bf",
  "propChain__pbt",
  "propChain__pbt_e",
  "propChain__pbt_1",
  "propChain__lbt",
  "propChain__lbt_bf",
  "propChain__lpbt_1",
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
  "take1__bt",
  "take1__bf",
  "take1__pbt",
  "take1__pbt_e",
  "take1__pbt_1",
  "take1__lbt",
  "take1__lbt_bf",
  "take1__lpbt_1",
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
  "take9__bt",
  "take9__bf",
  "take9__pbt",
  "take9__pbt_e",
  "take9__pbt_1",
  "take9__lbt",
  "take9__lbt_bf",
  "take9__lpbt_1",
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
  "skip1__bt",
  "skip1__bf",
  "skip1__pbt",
  "skip1__pbt_e",
  "skip1__pbt_1",
  "skip1__lbt",
  "skip1__lbt_bf",
  "skip1__lpbt_1",
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
  "distinct__bt",
  "distinct__bf",
  "distinct__pbt",
  "distinct__pbt_e",
  "distinct__pbt_1",
  "distinct__lbt",
  "distinct__lbt_bf",
  "distinct__lpbt_1",
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
  "order__bt",
  "order__bf",
  "order__pbt",
  "order__pbt_e",
  "order__pbt_1",
  "order__lbt",
  "order__lbt_bf",
  "order__lpbt_1",
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
  "mapId__bt",
  "mapId__bf",
  "mapId__pbt",
  "mapId__pbt_e",
  "mapId__pbt_1",
  "mapId__lbt",
  "mapId__lbt_bf",
  "mapId__lpbt_1",
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
  "patternHead__e",
  "patternHead__n0",
  "patternHead__n1",
  "patternHead__bt",
  "patternHead__bf",
  "patternHead__pbt",
  "patternHead__pbt_e",
  "patternHead__pbt_1",
  "patternHead__lbt",
  "patternHead__lbt_bf",
  "patternHead__lpbt_1",
  "patternHead__p1",
  "patternHead__p12",
  "patternHead__p123",
  "patternHead__pee",
  "patternHead__pe1",
  "patternHead__p1e",
  "patternHead__p12_3",
  "patternHead__p12_34",
  "patternHead__pe_12",
  "patternHead__ppe1_2",
  "patternHead__p12_e",
  "patternHead__ppe",
  "patternHead__pp1",
  "patternHead__ppp12",
  "patternHead__le",
  "patternHead__l7",
  "patternHead__l12",
  "patternHead__l12_3",
  "patternHead__lle",
  "patternHead__l_e",
  "patternHead__l_p12",
  "patternHead__p_l12",
  "patternHead__pl1",
  "patternHeadMap__e",
  "patternHeadMap__n0",
  "patternHeadMap__n1",
  "patternHeadMap__bt",
  "patternHeadMap__bf",
  "patternHeadMap__pbt",
  "patternHeadMap__pbt_e",
  "patternHeadMap__pbt_1",
  "patternHeadMap__lbt",
  "patternHeadMap__lbt_bf",
  "patternHeadMap__lpbt_1",
  "patternHeadMap__p1",
  "patternHeadMap__p12",
  "patternHeadMap__p123",
  "patternHeadMap__pee",
  "patternHeadMap__pe1",
  "patternHeadMap__p1e",
  "patternHeadMap__p12_3",
  "patternHeadMap__p12_34",
  "patternHeadMap__pe_12",
  "patternHeadMap__ppe1_2",
  "patternHeadMap__p12_e",
  "patternHeadMap__ppe",
  "patternHeadMap__pp1",
  "patternHeadMap__ppp12",
  "patternHeadMap__le",
  "patternHeadMap__l7",
  "patternHeadMap__l12",
  "patternHeadMap__l12_3",
  "patternHeadMap__lle",
  "patternHeadMap__l_e",
  "patternHeadMap__l_p12",
  "patternHeadMap__p_l12",
  "patternHeadMap__pl1",
  "patternPair__e",
  "patternPair__n0",
  "patternPair__n1",
  "patternPair__bt",
  "patternPair__bf",
  "patternPair__pbt",
  "patternPair__pbt_e",
  "patternPair__pbt_1",
  "patternPair__lbt",
  "patternPair__lbt_bf",
  "patternPair__lpbt_1",
  "patternPair__p1",
  "patternPair__p12",
  "patternPair__p123",
  "patternPair__pee",
  "patternPair__pe1",
  "patternPair__p1e",
  "patternPair__p12_3",
  "patternPair__p12_34",
  "patternPair__pe_12",
  "patternPair__ppe1_2",
  "patternPair__p12_e",
  "patternPair__ppe",
  "patternPair__pp1",
  "patternPair__ppp12",
  "patternPair__le",
  "patternPair__l7",
  "patternPair__l12",
  "patternPair__l12_3",
  "patternPair__lle",
  "patternPair__l_e",
  "patternPair__l_p12",
  "patternPair__p_l12",
  "patternPair__pl1",
  "patternPairMap__e",
  "patternPairMap__n0",
  "patternPairMap__n1",
  "patternPairMap__bt",
  "patternPairMap__bf",
  "patternPairMap__pbt",
  "patternPairMap__pbt_e",
  "patternPairMap__pbt_1",
  "patternPairMap__lbt",
  "patternPairMap__lbt_bf",
  "patternPairMap__lpbt_1",
  "patternPairMap__p1",
  "patternPairMap__p12",
  "patternPairMap__p123",
  "patternPairMap__pee",
  "patternPairMap__pe1",
  "patternPairMap__p1e",
  "patternPairMap__p12_3",
  "patternPairMap__p12_34",
  "patternPairMap__pe_12",
  "patternPairMap__ppe1_2",
  "patternPairMap__p12_e",
  "patternPairMap__ppe",
  "patternPairMap__pp1",
  "patternPairMap__ppp12",
  "patternPairMap__le",
  "patternPairMap__l7",
  "patternPairMap__l12",
  "patternPairMap__l12_3",
  "patternPairMap__lle",
  "patternPairMap__l_e",
  "patternPairMap__l_p12",
  "patternPairMap__p_l12",
  "patternPairMap__pl1",
  "filterKeep__e",
  "filterKeep__n0",
  "filterKeep__n1",
  "filterKeep__bt",
  "filterKeep__bf",
  "filterKeep__pbt",
  "filterKeep__pbt_e",
  "filterKeep__pbt_1",
  "filterKeep__lbt",
  "filterKeep__lbt_bf",
  "filterKeep__lpbt_1",
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
  "atoms__bt",
  "atoms__bf",
  "atoms__pbt",
  "atoms__pbt_e",
  "atoms__pbt_1",
  "atoms__lbt",
  "atoms__lbt_bf",
  "atoms__lpbt_1",
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
  "takeCapture__bt",
  "takeCapture__bf",
  "takeCapture__pbt",
  "takeCapture__pbt_e",
  "takeCapture__pbt_1",
  "takeCapture__lbt",
  "takeCapture__lbt_bf",
  "takeCapture__lpbt_1",
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
  "takeIdentity__bt",
  "takeIdentity__bf",
  "takeIdentity__pbt",
  "takeIdentity__pbt_e",
  "takeIdentity__pbt_1",
  "takeIdentity__lbt",
  "takeIdentity__lbt_bf",
  "takeIdentity__lpbt_1",
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
  "takeCount__bt",
  "takeCount__bf",
  "takeCount__pbt",
  "takeCount__pbt_e",
  "takeCount__pbt_1",
  "takeCount__lbt",
  "takeCount__lbt_bf",
  "takeCount__lpbt_1",
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
  "takeCollecting__e",
  "takeCollecting__n0",
  "takeCollecting__n1",
  "takeCollecting__bt",
  "takeCollecting__bf",
  "takeCollecting__pbt",
  "takeCollecting__pbt_e",
  "takeCollecting__pbt_1",
  "takeCollecting__lbt",
  "takeCollecting__lbt_bf",
  "takeCollecting__lpbt_1",
  "takeCollecting__p1",
  "takeCollecting__p12",
  "takeCollecting__p123",
  "takeCollecting__pee",
  "takeCollecting__pe1",
  "takeCollecting__p1e",
  "takeCollecting__p12_3",
  "takeCollecting__p12_34",
  "takeCollecting__pe_12",
  "takeCollecting__ppe1_2",
  "takeCollecting__p12_e",
  "takeCollecting__ppe",
  "takeCollecting__pp1",
  "takeCollecting__ppp12",
  "takeCollecting__le",
  "takeCollecting__l7",
  "takeCollecting__l12",
  "takeCollecting__l12_3",
  "takeCollecting__lle",
  "takeCollecting__l_e",
  "takeCollecting__l_p12",
  "takeCollecting__p_l12",
  "takeCollecting__pl1",
  "spreadRootStacked__e",
  "spreadRootStacked__n0",
  "spreadRootStacked__n1",
  "spreadRootStacked__bt",
  "spreadRootStacked__bf",
  "spreadRootStacked__pbt",
  "spreadRootStacked__pbt_e",
  "spreadRootStacked__pbt_1",
  "spreadRootStacked__lbt",
  "spreadRootStacked__lbt_bf",
  "spreadRootStacked__lpbt_1",
  "spreadRootStacked__p1",
  "spreadRootStacked__p12",
  "spreadRootStacked__p123",
  "spreadRootStacked__pee",
  "spreadRootStacked__pe1",
  "spreadRootStacked__p1e",
  "spreadRootStacked__p12_3",
  "spreadRootStacked__p12_34",
  "spreadRootStacked__pe_12",
  "spreadRootStacked__ppe1_2",
  "spreadRootStacked__p12_e",
  "spreadRootStacked__ppe",
  "spreadRootStacked__pp1",
  "spreadRootStacked__ppp12",
  "spreadRootStacked__le",
  "spreadRootStacked__l7",
  "spreadRootStacked__l12",
  "spreadRootStacked__l12_3",
  "spreadRootStacked__lle",
  "spreadRootStacked__l_e",
  "spreadRootStacked__l_p12",
  "spreadRootStacked__p_l12",
  "spreadRootStacked__pl1",
  "collectingStacked__e",
  "collectingStacked__n0",
  "collectingStacked__n1",
  "collectingStacked__bt",
  "collectingStacked__bf",
  "collectingStacked__pbt",
  "collectingStacked__pbt_e",
  "collectingStacked__pbt_1",
  "collectingStacked__lbt",
  "collectingStacked__lbt_bf",
  "collectingStacked__lpbt_1",
  "collectingStacked__p1",
  "collectingStacked__p12",
  "collectingStacked__p123",
  "collectingStacked__pee",
  "collectingStacked__pe1",
  "collectingStacked__p1e",
  "collectingStacked__p12_3",
  "collectingStacked__p12_34",
  "collectingStacked__pe_12",
  "collectingStacked__ppe1_2",
  "collectingStacked__p12_e",
  "collectingStacked__ppe",
  "collectingStacked__pp1",
  "collectingStacked__ppp12",
  "collectingStacked__le",
  "collectingStacked__l7",
  "collectingStacked__l12",
  "collectingStacked__l12_3",
  "collectingStacked__lle",
  "collectingStacked__l_e",
  "collectingStacked__l_p12",
  "collectingStacked__p_l12",
  "collectingStacked__pl1",
  "captureStacked__e",
  "captureStacked__n0",
  "captureStacked__n1",
  "captureStacked__bt",
  "captureStacked__bf",
  "captureStacked__pbt",
  "captureStacked__pbt_e",
  "captureStacked__pbt_1",
  "captureStacked__lbt",
  "captureStacked__lbt_bf",
  "captureStacked__lpbt_1",
  "captureStacked__p1",
  "captureStacked__p12",
  "captureStacked__p123",
  "captureStacked__pee",
  "captureStacked__pe1",
  "captureStacked__p1e",
  "captureStacked__p12_3",
  "captureStacked__p12_34",
  "captureStacked__pe_12",
  "captureStacked__ppe1_2",
  "captureStacked__p12_e",
  "captureStacked__ppe",
  "captureStacked__pp1",
  "captureStacked__ppp12",
  "captureStacked__le",
  "captureStacked__l7",
  "captureStacked__l12",
  "captureStacked__l12_3",
  "captureStacked__lle",
  "captureStacked__l_e",
  "captureStacked__l_p12",
  "captureStacked__p_l12",
  "captureStacked__pl1",
  "special__multiProp",
  "special__multiPropCall",
  "special__multiPropCount",
  "special__multiPropDotCount",
  "special__multiPropDot",
  "special__dotAccessPublicMember",
  "special__dotAccessCallPublicMember",
  "special__multiPropIndex0",
  "special__multiPropEq",
  "special__multiCollecting",
  "special__multiCollectingCount",
  "special__collectingEmptyCall",
  "special__collectingFwdSum",
  "special__collectingFwdSpread",
  "special__collectingJoin",
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
  "special__mapPairSwapFlatIsArity",
  "special__mapToOne",
  "special__orderSingle",
  "special__orderEmpty",
  "special__atomsNested",
  "special__emptyOpGreater",
  "special__emptyOpPlus",
  "special__emptyOpPlusRight",
  "special__emptyOpDivRight",
  "special__emptyOpAnd",
  "special__emptyOpString",
  "special__emptyOpBoth",
  "special__emptyUnaryMinus",
  "special__emptyUnaryNot",
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
  "special__chainAllTrue",
  "special__chainMixed",
  "special__chainFalseMiddle",
  "special__chainFalseLast",
  "special__chainEqOnly",
  "special__chainNeAdjacent",
  "special__chainNeAdjacentFalse",
  "special__chainEqThenLt",
  "special__chainBoolEqMixed",
  "special__chainSeqEq",
  "special__chainStrEq",
  "special__chainParenFirst",
  "special__chainParenRight",
  "special__chainParenBoth",
  "special__chainUnderNot",
  "special__chainUnderAnd",
  "special__chainArithmeticOperands",
  "special__chainInvalidLater",
  "special__chainErrorFirstOperand",
  "special__chainErrorAfterFalse",
  "special__chainPropertyOperands",
  "special__chainCallOperands",
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
  "special__callbackSingleCollectingMap",
  "special__callbackMixedCollectingRow",
  "special__callbackMixedCollectingRowPattern",
  "special__callbackCollectingElementIsOneArgument",
  "special__listInSeqSpreadKeepsList",
  "special__listFixedCallBoundary",
  "special__listCollectingSpreadCall",
  "special__spreadNoOutputBlockRoot",
  "special__spreadNoOutputBlockList",
  "special__spreadNoOutputBlockCallArg",
  "special__spreadNoOutputResolved",
  "special__listLoneCollectingAssignment",
  "special__minSeq",
  "special__minList",
  "special__minScalar",
  "special__minEmpty",
  "special__minNestedItem",
  "special__minDot",
  "special__maxSeq",
  "special__maxList",
  "special__maxEmpty",
  "special__maxDot",
  "special__firstSeq",
  "special__firstScalar",
  "special__firstListElementStaysExact",
  "special__firstEmptyItem",
  "special__firstEmpty",
  "special__firstDot",
  "special__lastSeq",
  "special__lastListElementStaysExact",
  "special__lastEmpty",
  "special__orderDescSeq",
  "special__orderDescList",
  "special__orderDescDuplicates",
  "special__orderDescScalar",
  "special__orderDescEmpty",
  "special__orderDescString",
  "special__orderDescDot",
  "special__whileCountdown",
  "special__whileZeroIterations",
  "special__whileTwoSlotState",
  "special__whileEmptyInitialState",
  "special__whileNonNumericContinuation",
  "special__whileDot",
  "special__containsSequenceItem",
  "special__containsListItem",
  "special__containsEmptyItem",
  "special__containsScalarCollection",
  "special__containsAcrossKinds",
  "special__openPublicMember",
  "special__openPrivateMemberHidden",
  "special__openLocalOnlyCapturedParamsInsideOwner",
  "special__openLocalOnlyCapturedParamsOutsideOwner",
  "special__openTwoProvidersAmbiguous",
  "special__openDuplicateTargetDedup",
  "special__openDuplicateDottedTargetDedup",
  "special__openDuplicateInlineBlocksAmbiguous",
  "special__openInlineBlock",
  "special__openInlineBlockPrivateHidden",
  "special__openDottedPath",
  "special__openLocalShadowsOpenedName",
  "special__openAncestorPropertyWins",
  "special__openParentScopeReachesChild",
  "special__openNestedDoesNotLeakOutward",
  "special__openHeadDefinedLater",
  "special__openBuiltinNameCollision",
  "special__structuralDotSeesPrivateMember",
  "special__openPrivateMemberIsNotASecondProvider",
  "special__openLocalOnlyMemberIsASecondProvider",
  "special__ifSelectedParameterizedBranchIsArity",
  "special__ifSelectedParameterizedFalseBranchIsArity",
  "special__ifParameterizedConditionIsArity",
  "special__ifUnselectedParameterizedBranchStaysLazy",
  "special__ifZeroParameterBranchIsValue",
  "special__ifParameterIgnoringBodyStillArity",
  "special__ifCollectingCallableSlotIsCollectedValue",
  "special__ifCollectingCallableExplicitCallIsSameValue",
  "special__bareCollectingCallableIsAValue",
  "special__bareCollectingCallableCountAgreesWithDottedForm",
  "special__ifRequiredPrefixBesideCollectorIsArity",
  "special__ifRequiredSuffixBesideCollectorIsArity",
  "special__ifNestedCollectingPatternIsArity",
  "special__collectingCallableStaysACallbackAlgorithm",
  "special__ifAlgorithmChannelParameterSlotIsArity",
  "special__repeatInitialParameterizedSlotIsArity",
  "special__repeatCountParameterizedSlotIsArity",
  "special__whileInitialParameterizedSlotIsArity",
  "special__atomsParameterizedSlotIsArity",
  "special__rangeParameterizedSlotIsArity",
  "special__dotStringParameterizedReceiverIsArity",
  "special__dotStringNavigatedParameterizedMemberIsArity",
  "special__reduceParameterIgnoringInitialStillRejected",
  "special__repeatParameterizedStepIsCallback"
]
#guard surfaceCaseIds.length == 2244

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
  .algorithmExpr (alg [] [] [] [(.sequenceConstruct (.emptySequence 0) (.num 1))])
#guard obs case_internal__sc_e_1 == "ok raw=1 n=1"

-- internal__sc_1_e: SequenceConstruct[1, ()] drops the () leaf and singleton-collapses
def case_internal__sc_1_e : Expr :=
  .algorithmExpr (alg [] [] [] [(.sequenceConstruct (.num 1) (.emptySequence 0))])
#guard obs case_internal__sc_1_e == "ok raw=1 n=1"

-- internal__sc_e_e: SequenceConstruct[(), ()] drops both () leaves to the empty sequence
def case_internal__sc_e_e : Expr :=
  .algorithmExpr (alg [] [] [] [(.sequenceConstruct (.emptySequence 0) (.emptySequence 0))])
#guard obs case_internal__sc_e_e == "ok raw=S[] n=1"

-- internal__sc_p12_e: SequenceConstruct[(1,2), ()] drops () and collapses to the pair
def case_internal__sc_p12_e : Expr :=
  .algorithmExpr (alg [] [] [] [(.sequenceConstruct (.capture [.num 1, .num 2]) (.emptySequence 0))])
#guard obs case_internal__sc_p12_e == "ok raw=S[1, 2] n=1"

-- internal__sc_e_p12: SequenceConstruct[(), (1,2)] drops () and collapses to the pair
def case_internal__sc_e_p12 : Expr :=
  .algorithmExpr (alg [] [] [] [(.sequenceConstruct (.emptySequence 0) (.capture [.num 1, .num 2]))])
#guard obs case_internal__sc_e_p12 == "ok raw=S[1, 2] n=1"

-- internal__sc_1_2: SequenceConstruct[1, 2] matches written (1, 2)
def case_internal__sc_1_2 : Expr :=
  .algorithmExpr (alg [] [] [] [(.sequenceConstruct (.num 1) (.num 2))])
#guard obs case_internal__sc_1_2 == "ok raw=S[1, 2] n=1"

-- internal__sc_p12_p34: SequenceConstruct of two pairs preserves nested structure
def case_internal__sc_p12_p34 : Expr :=
  .algorithmExpr (alg [] [] [] [(.sequenceConstruct (.capture [.num 1, .num 2]) (.capture [.num 3, .num 4]))])
#guard obs case_internal__sc_p12_p34 == "ok raw=S[S[1, 2], S[3, 4]] n=1"

-- internal__sc_spread_3: SequenceConstruct[(1,2)*, 3] splices the spread leaf
def case_internal__sc_spread_3 : Expr :=
  .algorithmExpr (alg [] [] [] [(.sequenceConstruct (.sequenceSpread (.capture [.num 1, .num 2])) (.num 3))])
#guard obs case_internal__sc_spread_3 == "ok raw=S[1, 2, 3] n=1"

-- internal__sc_count_arg: count of the internal node observes the ()-dropped value
def case_internal__sc_count_arg : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "count") [(.sequenceConstruct (.emptySequence 0) (.num 1))])])
#guard obs case_internal__sc_count_arg == "ok raw=1 n=1"

-- internal__sc_take_collection: a SequenceConstruct collection argument binds like the grouped surface form
def case_internal__sc_take_collection : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "take") [(.sequenceConstruct (.sequenceConstruct (.num 1) (.num 2)) (.num 5)), .num 2])])
#guard obs case_internal__sc_take_collection == "ok raw=L[1, 2] n=1"

-- internal__sc_take_collection_empty: () leaf vanishes from a SequenceConstruct collection argument (written parens keep it)
def case_internal__sc_take_collection_empty : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "take") [(.sequenceConstruct (.sequenceConstruct (.emptySequence 0) (.num 1)) (.num 2)), .num 2])])
#guard obs case_internal__sc_take_collection_empty == "ok raw=L[1, 2] n=1"

-- internal__sc_take_block_leaf: a nested pair inside a SequenceConstruct collection argument stays one item
def case_internal__sc_take_block_leaf : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "take") [(.sequenceConstruct (.num 1) (.capture [.num 2, .num 5])), .num 2])])
#guard obs case_internal__sc_take_block_leaf == "ok raw=L[1, S[2, 5]] n=1"

-- internal__sc_sum_arg: sum of the internal node matches the grouped surface form
def case_internal__sc_sum_arg : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.resolve "sum") [(.sequenceConstruct (.num 1) (.num 2))])])
#guard obs case_internal__sc_sum_arg == "ok raw=3 n=1"

-- internal__sc_call_function: SequenceConstruct in call-function position is notAnAlgorithm
def case_internal__sc_call_function : Expr :=
  .algorithmExpr (alg [] [] [] [(.call (.sequenceConstruct (.num 1) (.num 2)) [.num 3])])
#guard obs case_internal__sc_call_function == "err notAnAlgorithm"

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
  "internal__sc_sum_arg",
  "internal__sc_call_function"
]
#guard internalNodeCaseIds.length == 14

-- 14 internal-node cases.
-- Total: 2258 case guards (2244 surface + 14 internal-node).
end SemanticExplorerCases
