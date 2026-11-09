import KatLang

/-!
GENERATED FILE - DO NOT EDIT BY HAND.

SEM-2C: Lean/C# differential corpus of the SEM-2B generated cases
(fuzz/KatLang.ParserFuzz/Semantic/SemanticCorpus.cs). For every valid case the program below is
`LeanAstEncoder`'s encoding of the parsed IDENTITY-PRELUDE MEMBER: the case's base source with
`trace(x) = x` and `wait(x) = x` prepended in place of the SEM-2B host operations, which Lean
does not model. C# checked each member against the generator's constructed expectation (value
and emitted count, or error kind); each `#guard` pins the member's C# neutral observation. A
failing guard is a Lean/C# divergence on that case.

Not checked here: the host-operation base program itself, host events, async suspension and
cancellation, and optimizer paths (all C# evidence of the SEM-2B profiles).

Partition (machine-checked by the `includedCaseIds.length` guard below):
- corpus cases: 273
- excluded by kind (invalid front-end programs; Lean has no surface front end): 9
- excluded by exact id: 0
- included cases: 264 (187 success, 77 runtime failure)

Regenerate from the repo root with:
  $env:KATLANG_REGENERATE_SEMANTIC_GENERATED = "1"
  dotnet test ./tests/KatLang.Tests/KatLang.Tests.csproj --filter SemanticGeneratedLeanArtifact
-/

namespace SemanticGeneratedCases
open KatLang

/-- Neutral raw-structure encoding shared with the C# harness:
    atom -> `1`, string -> `'x'`, Boolean -> `true` / `false`,
    sequence -> `S[a, b]`, empty -> `S[]`, exact list -> `L[a, b]`,
    call reference and argument view -> `CallReference` (never a run result: the run boundary refuses both). -/
partial def neutral : Result -> String
  | .atom n => toString n
  | .str s => "'" ++ s ++ "'"
  | .bool b => Result.boolText b
  | .sequenceValue rs => "S[" ++ String.intercalate ", " (rs.map neutral) ++ "]"
  | .listValue rs => "L[" ++ String.intercalate ", " (rs.map neutral) ++ "]"
  | .callRef _ => "CallReference"
  | .argView _ => "CallReference"

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
  | .missingOutput _ => "missingOutput"
  | .spreadMissingOutput => "spreadMissingOutput"
  | .unknownName _ => "unknownName"
  | .divByZero => "div0"
  | .demandCycle => "demandCycle"
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
  -- Lean-only: the R7 incomplete outcome of the fuel-indexed core; no public run returns it.
  | .fuelExhausted => "incomplete"

/-- Supplementary Q-67 fields; not a change to FORMAL-06 or `obs`.
    Descriptions, messages, contexts, branch display names and host policy are excluded. -/
structure SharedErrorPayload where
  kind : String
  names : List String := []
  counts : List Nat := []
  deriving BEq, Repr

inductive SharedErrorObservation where
  | matched (payload : Option SharedErrorPayload)
  | mismatch
  deriving BEq, Repr

def exposureKind : PropExposure -> String
  | .exported => "exported"
  | .localCapturedAncestorParams _ => "captured"
  | .localConditional => "conditional"

partial def sharedError : Error -> Option SharedErrorPayload
  | .withContext _ inner => sharedError inner
  | .arityMismatch expected actual => some { kind := "arity", counts := [expected, actual] }
  | .badArity => some { kind := "badArity" }
  | .branchArityMismatch _ expected actual => some { kind := "branchArity", counts := [expected, actual] }
  | .branchOutputArityMismatch _ expected actual => some { kind := "branchOutputArity", counts := [expected, actual] }
  | .unknownName name => some { kind := "unknownName", names := [name] }
  | .unknownProperty _ name => some { kind := "unknownProperty", names := [name] }
  | .notPublicProperty _ name => some { kind := "notPublicProperty", names := [name] }
  | .localOnlyProperty _ name exposure => some { kind := "localOnlyProperty", names := [name, exposureKind exposure] }
  | .ambiguousOpen name _ => some { kind := "ambiguousOpen", names := [name] }
  | .duplicateProperty name => some { kind := "duplicateProperty", names := [name] }
  | .unresolvedImplicitParams names => some { kind := "unresolvedImplicitParams", names := names }
  | .badIndex => some { kind := "index" }
  | .divByZero => some { kind := "div0" }
  | .demandCycle => some { kind := "demandCycle" }
  | .duplicateBranchPattern => some { kind := "duplicateBranchPattern" }
  | .explicitParamsRequireOutput => some { kind := "explicitParamsRequireOutput" }
  | .missingOutput _ => some { kind := "missingOutput" }
  | .spreadMissingOutput => some { kind := "spreadMissingOutput" }
  | .typeMismatch _ | .noMatchingBranch _ | .notAnAlgorithm _
    | .illegalInOpen _ | .badOpenForm _ | .illegalInEval _ | .fuelExhausted => none

/-- Counted variant of `runResultM`: the same declaration identification and root wiring, but keeping the
    root emitted count (`evalAlgOutputCounted` / `evalCounted`), matching the
    C# `Evaluator.RunCounted` observation. -/
def runCountedM (e : Expr) : EvalM CountedResult := do
  let e := (identifyPropertyExpr e).run' 0
  validateExplicitParamOutputInvariantExpr e
  let ctx := { callStack := [preludeAlg] }
  -- The run result boundary of `runResultM` (CallReference S1): a counted run result
  -- that contains a call reference is refused exactly as the plain one is.
  let counted <- match e with
    | .algorithmExpr a =>
        let wired := wireToCaller ctx a
        if Algorithm.acceptsZeroSuppliedArguments wired then
          evalZeroArgumentDemandOutputCounted wired ctx []
        else
          .error (Error.unresolvedImplicitParams (Algorithm.params wired))
    | _ => evalCounted e ctx []
  let _ <- exportRunValue counted.fst
  pure counted

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

/-- Extra guards are emitted only for supported failures, so successful cases incur
    no extra evaluator runs. Both Lean routes must agree independently. -/
def errorObs (e : Expr) : SharedErrorObservation :=
  match runCountedM e |>.run EvalState.empty, runResult e with
  | .error e1, .error e2 =>
      if sharedError e1 == sharedError e2 then .matched (sharedError e1)
      else .mismatch
  | _, _ => .mismatch

-- sem2b/v1/sys/meta/0: v1(meta v2) = v2 \n v3 = v1 \n v4(v5, v6, v7) = trace((v5 * 100) + (v6 * 10) + v7) \n v8 = v3(v4(trace(1), trace(2), trace(3))) \n v9(v10, v11, v12) = v12 \n [v9(v8.Arguments*), v8.Algorithm(4, 5, 6), v8.Algorithm(v8.Arguments*)] \n 997
def case_sem2b_2Fv1_2Fsys_2Fmeta_2F0 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v3" (.alias none [] [] (.resolve "v1")), privateProp "v8" (alg [] [] [] [(.call (.resolve "v3") [(.call (.resolve "v4") [(.call (.resolve "trace") [.num 1]), (.call (.resolve "trace") [.num 2]), (.call (.resolve "trace") [.num 3])])])]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (algWithParameters [{ name := "v2", kind := .metaRef }] [] [] [.param "v2"]), privateProp "v4" (alg ["v5", "v6", "v7"] [] [] [(.call (.resolve "trace") [(.binary .add (.binary .add (.binary .mul (.param "v5") (.num 100)) (.binary .mul (.param "v6") (.num 10))) (.param "v7"))])]), privateProp "v9" (alg ["v10", "v11", "v12"] [] [] [.param "v12"])] [(.listLiteral [(.call (.resolve "v9") [(.sequenceSpread (.dotCall (.resolve "v8") "Arguments" none))]), (.dotCall (.resolve "v8") "Algorithm" (some [.num 4, .num 5, .num 6])), (.dotCall (.resolve "v8") "Algorithm" (some [(.sequenceSpread (.dotCall (.resolve "v8") "Arguments" none))]))]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fmeta_2F0 == "ok raw=S[L[3, 456, 123], 997] n=2"

-- sem2b/v1/sys/meta/1: v1(meta v2) = v2 \n v3(v4) = v1(v4) \n v5(v6) = v6 \n v7 = v3(v5(trace(1))) \n [v7.Algorithm(2), v7.Algorithm(v7.Arguments*), v7.Arguments.count, v7.Arguments[0]] \n 997
def case_sem2b_2Fv1_2Fsys_2Fmeta_2F1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v7" (alg [] [] [] [(.call (.resolve "v3") [(.call (.resolve "v5") [(.call (.resolve "trace") [.num 1])])])]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (algWithParameters [{ name := "v2", kind := .metaRef }] [] [] [.param "v2"]), privateProp "v3" (alg ["v4"] [] [] [(.call (.resolve "v1") [.param "v4"])]), privateProp "v5" (alg ["v6"] [] [] [.param "v6"])] [(.listLiteral [(.dotCall (.resolve "v7") "Algorithm" (some [.num 2])), (.dotCall (.resolve "v7") "Algorithm" (some [(.sequenceSpread (.dotCall (.resolve "v7") "Arguments" none))])), (.dotCall (.dotCall (.resolve "v7") "Arguments" none) "count" none), (.index (.dotCall (.resolve "v7") "Arguments" none) [.num 0])]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fmeta_2F1 == "ok raw=S[L[2, 1, 1, 1], 997] n=2"

-- sem2b/v1/sys/meta/2: v1(meta v2) = v2 \n v3 = 11, 12 \n v4(*v5) = trace(count(v5)) \n v6 = v1(v4(trace(1), trace(2), v3*)) \n [v6.Algorithm(v6.Arguments*)] \n 997
def case_sem2b_2Fv1_2Fsys_2Fmeta_2F2 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v3" (alg [] [] [] [.num 11, .num 12]), privateProp "v6" (alg [] [] [] [(.call (.resolve "v1") [(.call (.resolve "v4") [(.call (.resolve "trace") [.num 1]), (.call (.resolve "trace") [.num 2]), (.sequenceSpread (.resolve "v3"))])])]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (algWithParameters [{ name := "v2", kind := .metaRef }] [] [] [.param "v2"]), privateProp "v4" (algWithParameters [{ name := "v5", kind := .collecting }] [] [] [(.call (.resolve "trace") [(.call (.resolve "count") [.param "v5"])])])] [(.listLiteral [(.dotCall (.resolve "v6") "Algorithm" (some [(.sequenceSpread (.dotCall (.resolve "v6") "Arguments" none))]))]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fmeta_2F2 == "ok raw=S[L[4], 997] n=2"

-- sem2b/v1/sys/meta/3: v1(meta v2) = v2 \n v3 = v1 \n v4(v5, v6, v7) = (v5 * 100) + (v6 * 10) + v7 \n v8 = v3(v4(trace(1), trace(2), trace(3))) \n [v8.Arguments.count, v8.Arguments[1]] \n 997
def case_sem2b_2Fv1_2Fsys_2Fmeta_2F3 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v3" (.alias none [] [] (.resolve "v1")), privateProp "v8" (alg [] [] [] [(.call (.resolve "v3") [(.call (.resolve "v4") [(.call (.resolve "trace") [.num 1]), (.call (.resolve "trace") [.num 2]), (.call (.resolve "trace") [.num 3])])])]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (algWithParameters [{ name := "v2", kind := .metaRef }] [] [] [.param "v2"]), privateProp "v4" (alg ["v5", "v6", "v7"] [] [] [(.binary .add (.binary .add (.binary .mul (.param "v5") (.num 100)) (.binary .mul (.param "v6") (.num 10))) (.param "v7"))])] [(.listLiteral [(.dotCall (.dotCall (.resolve "v8") "Arguments" none) "count" none), (.index (.dotCall (.resolve "v8") "Arguments" none) [.num 1])]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fmeta_2F3 == "ok raw=S[L[3, 2], 997] n=2"

-- sem2b/v1/sys/meta/4: v1(meta v2) = v2 \n v3(v4) = v1(v4) \n v5(v6) = trace(v6) \n v7 = v3(v5(trace(1))) \n v8(v9) = v9 \n [v7.Arguments[0], v7.Invoke(), v8(v7.Arguments*)] \n 997
def case_sem2b_2Fv1_2Fsys_2Fmeta_2F4 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v7" (alg [] [] [] [(.call (.resolve "v3") [(.call (.resolve "v5") [(.call (.resolve "trace") [.num 1])])])]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (algWithParameters [{ name := "v2", kind := .metaRef }] [] [] [.param "v2"]), privateProp "v3" (alg ["v4"] [] [] [(.call (.resolve "v1") [.param "v4"])]), privateProp "v5" (alg ["v6"] [] [] [(.call (.resolve "trace") [.param "v6"])]), privateProp "v8" (alg ["v9"] [] [] [.param "v9"])] [(.listLiteral [(.index (.dotCall (.resolve "v7") "Arguments" none) [.num 0]), (.dotCall (.resolve "v7") "Invoke" (some [])), (.call (.resolve "v8") [(.sequenceSpread (.dotCall (.resolve "v7") "Arguments" none))])]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fmeta_2F4 == "ok raw=S[L[1, 1, 1], 997] n=2"

-- sem2b/v1/sys/meta/5: v1(meta v2) = v2 \n v3 = 11, 12 \n v4(*v5) = count(v5) \n v6 = v1(v4(trace(1), trace(2), v3*)) \n v7(v8, v9, v10, v11) = v8 \n [v6.Invoke(), v7(v6.Arguments*), v6.Algorithm(3, 4), v6.Algorithm(v6.Arguments*)] \n 997
def case_sem2b_2Fv1_2Fsys_2Fmeta_2F5 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v3" (alg [] [] [] [.num 11, .num 12]), privateProp "v6" (alg [] [] [] [(.call (.resolve "v1") [(.call (.resolve "v4") [(.call (.resolve "trace") [.num 1]), (.call (.resolve "trace") [.num 2]), (.sequenceSpread (.resolve "v3"))])])]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (algWithParameters [{ name := "v2", kind := .metaRef }] [] [] [.param "v2"]), privateProp "v4" (algWithParameters [{ name := "v5", kind := .collecting }] [] [] [(.call (.resolve "count") [.param "v5"])]), privateProp "v7" (alg ["v8", "v9", "v10", "v11"] [] [] [.param "v8"])] [(.listLiteral [(.dotCall (.resolve "v6") "Invoke" (some [])), (.call (.resolve "v7") [(.sequenceSpread (.dotCall (.resolve "v6") "Arguments" none))]), (.dotCall (.resolve "v6") "Algorithm" (some [.num 3, .num 4])), (.dotCall (.resolve "v6") "Algorithm" (some [(.sequenceSpread (.dotCall (.resolve "v6") "Arguments" none))]))]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fmeta_2F5 == "ok raw=S[L[4, 1, 2, 4], 997] n=2"

-- sem2b/v1/sys/meta/6: v1(meta v2) = v2 \n v3 = v1 \n v4(v5, v6, v7) = trace((v5 * 100) + (v6 * 10) + v7) \n v8 = v3(v4(trace(1), trace(2), trace(3))) \n v9(v10, v11, v12) = v12 \n [v9(v8.Arguments*)] \n 997
def case_sem2b_2Fv1_2Fsys_2Fmeta_2F6 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v3" (.alias none [] [] (.resolve "v1")), privateProp "v8" (alg [] [] [] [(.call (.resolve "v3") [(.call (.resolve "v4") [(.call (.resolve "trace") [.num 1]), (.call (.resolve "trace") [.num 2]), (.call (.resolve "trace") [.num 3])])])]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (algWithParameters [{ name := "v2", kind := .metaRef }] [] [] [.param "v2"]), privateProp "v4" (alg ["v5", "v6", "v7"] [] [] [(.call (.resolve "trace") [(.binary .add (.binary .add (.binary .mul (.param "v5") (.num 100)) (.binary .mul (.param "v6") (.num 10))) (.param "v7"))])]), privateProp "v9" (alg ["v10", "v11", "v12"] [] [] [.param "v12"])] [(.listLiteral [(.call (.resolve "v9") [(.sequenceSpread (.dotCall (.resolve "v8") "Arguments" none))])]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fmeta_2F6 == "ok raw=S[L[3], 997] n=2"

-- sem2b/v1/sys/meta/7: v1(meta v2) = v2 \n v3(v4) = v1(v4) \n v5(v6) = v6 \n v7 = v3(v5(trace(1))) \n [v7.Algorithm(2), v7.Algorithm(v7.Arguments*)] \n 997
def case_sem2b_2Fv1_2Fsys_2Fmeta_2F7 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v7" (alg [] [] [] [(.call (.resolve "v3") [(.call (.resolve "v5") [(.call (.resolve "trace") [.num 1])])])]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (algWithParameters [{ name := "v2", kind := .metaRef }] [] [] [.param "v2"]), privateProp "v3" (alg ["v4"] [] [] [(.call (.resolve "v1") [.param "v4"])]), privateProp "v5" (alg ["v6"] [] [] [.param "v6"])] [(.listLiteral [(.dotCall (.resolve "v7") "Algorithm" (some [.num 2])), (.dotCall (.resolve "v7") "Algorithm" (some [(.sequenceSpread (.dotCall (.resolve "v7") "Arguments" none))]))]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fmeta_2F7 == "ok raw=S[L[2, 1], 997] n=2"

-- sem2b/v1/sys/meta-fail/0: v1(meta v2) = v2 \n v3 = v1 \n v4(v5, v6, v7) = trace((v5 * 100) + (v6 * 10) + v7) \n v8 = v3(v4(trace(1), trace(2), trace(3))) \n v9(v10, v11, v12) = v12 \n [v9(v8.Arguments*), v8.Algorithm(4, 5, 6), v8.Arguments[1 / 0]] \n 997
def case_sem2b_2Fv1_2Fsys_2Fmeta_2Dfail_2F0 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v3" (.alias none [] [] (.resolve "v1")), privateProp "v8" (alg [] [] [] [(.call (.resolve "v3") [(.call (.resolve "v4") [(.call (.resolve "trace") [.num 1]), (.call (.resolve "trace") [.num 2]), (.call (.resolve "trace") [.num 3])])])]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (algWithParameters [{ name := "v2", kind := .metaRef }] [] [] [.param "v2"]), privateProp "v4" (alg ["v5", "v6", "v7"] [] [] [(.call (.resolve "trace") [(.binary .add (.binary .add (.binary .mul (.param "v5") (.num 100)) (.binary .mul (.param "v6") (.num 10))) (.param "v7"))])]), privateProp "v9" (alg ["v10", "v11", "v12"] [] [] [.param "v12"])] [(.listLiteral [(.call (.resolve "v9") [(.sequenceSpread (.dotCall (.resolve "v8") "Arguments" none))]), (.dotCall (.resolve "v8") "Algorithm" (some [.num 4, .num 5, .num 6])), (.index (.dotCall (.resolve "v8") "Arguments" none) [(.binary .div (.num 1) (.num 0))])]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fmeta_2Dfail_2F0 == "err div0"
#guard errorObs case_sem2b_2Fv1_2Fsys_2Fmeta_2Dfail_2F0 == .matched (some { kind := "div0", names := [], counts := [] })

-- sem2b/v1/sys/meta-fail/1: v1(meta v2) = v2 \n v3(v4) = v1(v4) \n v5(v6) = v6 \n v7 = v3(v5(trace(1))) \n [v7] \n 997
def case_sem2b_2Fv1_2Fsys_2Fmeta_2Dfail_2F1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v7" (alg [] [] [] [(.call (.resolve "v3") [(.call (.resolve "v5") [(.call (.resolve "trace") [.num 1])])])]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (algWithParameters [{ name := "v2", kind := .metaRef }] [] [] [.param "v2"]), privateProp "v3" (alg ["v4"] [] [] [(.call (.resolve "v1") [.param "v4"])]), privateProp "v5" (alg ["v6"] [] [] [.param "v6"])] [(.listLiteral [.resolve "v7"]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fmeta_2Dfail_2F1 == "err type"

-- sem2b/v1/sys/meta-fail/2: v1(meta v2) = v2 \n v3(meta v4) = v1(v4) \n v5(v6, v7) = trace((v6 * 10) + v7) \n v8 = v3(v5(trace(1), trace(2))) \n [v8.Invoke()] \n 997
def case_sem2b_2Fv1_2Fsys_2Fmeta_2Dfail_2F2 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v8" (alg [] [] [] [(.call (.resolve "v3") [(.call (.resolve "v5") [(.call (.resolve "trace") [.num 1]), (.call (.resolve "trace") [.num 2])])])]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (algWithParameters [{ name := "v2", kind := .metaRef }] [] [] [.param "v2"]), privateProp "v3" (algWithParameters [{ name := "v4", kind := .metaRef }] [] [] [(.call (.resolve "v1") [.param "v4"])]), privateProp "v5" (alg ["v6", "v7"] [] [] [(.call (.resolve "trace") [(.binary .add (.binary .mul (.param "v6") (.num 10)) (.param "v7"))])])] [(.listLiteral [(.dotCall (.resolve "v8") "Invoke" (some []))]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fmeta_2Dfail_2F2 == "err notAnAlgorithm"

-- sem2b/v1/sys/meta-fail/3: v1(meta v2) = v2 \n v3 = v1 \n v4(v5, v6, v7) = (v5 * 100) + (v6 * 10) + v7 \n v8 = v3(5) \n [v8.Invoke()] \n 997
def case_sem2b_2Fv1_2Fsys_2Fmeta_2Dfail_2F3 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v3" (.alias none [] [] (.resolve "v1")), privateProp "v8" (alg [] [] [] [(.call (.resolve "v3") [.num 5])]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (algWithParameters [{ name := "v2", kind := .metaRef }] [] [] [.param "v2"]), privateProp "v4" (alg ["v5", "v6", "v7"] [] [] [(.binary .add (.binary .add (.binary .mul (.param "v5") (.num 100)) (.binary .mul (.param "v6") (.num 10))) (.param "v7"))])] [(.listLiteral [(.dotCall (.resolve "v8") "Invoke" (some []))]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fmeta_2Dfail_2F3 == "err notAnAlgorithm"

-- sem2b/v1/sys/collect/0: v1(v2, *v3) = v2 \n v4 = () \n v1(trace(1), trace(2), trace(3), trace(4), v4*) \n 997
def case_sem2b_2Fv1_2Fsys_2Fcollect_2F0 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v4" (alg [] [] [] [(.emptySequence 0)]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (algWithParameters [{ name := "v2" }, { name := "v3", kind := .collecting }] [] [] [.param "v2"])] [(.call (.resolve "v1") [(.call (.resolve "trace") [.num 1]), (.call (.resolve "trace") [.num 2]), (.call (.resolve "trace") [.num 3]), (.call (.resolve "trace") [.num 4]), (.sequenceSpread (.resolve "v4"))]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fcollect_2F0 == "ok raw=S[1, 997] n=2"

-- sem2b/v1/sys/collect/1: v1(*v2, v3) = v2 \n v4(*v5) = v1(v5*) \n v4(trace(1)) \n 997
def case_sem2b_2Fv1_2Fsys_2Fcollect_2F1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (algWithParameters [{ name := "v2", kind := .collecting }, { name := "v3" }] [] [] [.param "v2"]), privateProp "v4" (algWithParameters [{ name := "v5", kind := .collecting }] [] [] [(.call (.resolve "v1") [(.sequenceSpread (.param "v5"))])])] [(.call (.resolve "v4") [(.call (.resolve "trace") [.num 1])]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fcollect_2F1 == "ok raw=S[L[], 997] n=2"

-- sem2b/v1/sys/collect/2: v1((v2, *v3)) = (count(v3) * 10) + v2 \n v4 = 1, 2, 3 \n v1(v4) \n 997
def case_sem2b_2Fv1_2Fsys_2Fcollect_2F2 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v4" (alg [] [] [] [.num 1, .num 2, .num 3]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (algWithParameterPatterns [.sequenceValue [.capture { name := "v2" }, .capture { name := "v3", kind := .collecting }]] [] [] [(.binary .add (.binary .mul (.call (.resolve "count") [.param "v3"]) (.num 10)) (.param "v2"))])] [(.call (.resolve "v1") [.resolve "v4"]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fcollect_2F2 == "ok raw=S[21, 997] n=2"

-- sem2b/v1/sys/collect/3: v1([v2, *v3]) = v2 + count(v3) \n v1([1, 2, 3]) \n 997
def case_sem2b_2Fv1_2Fsys_2Fcollect_2F3 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (algWithParameterPatterns [.listValue [.capture { name := "v2" }, .capture { name := "v3", kind := .collecting }]] [] [] [(.binary .add (.param "v2") (.call (.resolve "count") [.param "v3"]))])] [(.call (.resolve "v1") [(.listLiteral [.num 1, .num 2, .num 3])]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fcollect_2F3 == "ok raw=S[3, 997] n=2"

-- sem2b/v1/sys/collect/4: v1(v2, *v3) = v2 \n v4 = () \n v1(trace(1), trace(2), trace(3), trace(4), v4*) \n 997
def case_sem2b_2Fv1_2Fsys_2Fcollect_2F4 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v4" (alg [] [] [] [(.emptySequence 0)]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (algWithParameters [{ name := "v2" }, { name := "v3", kind := .collecting }] [] [] [.param "v2"])] [(.call (.resolve "v1") [(.call (.resolve "trace") [.num 1]), (.call (.resolve "trace") [.num 2]), (.call (.resolve "trace") [.num 3]), (.call (.resolve "trace") [.num 4]), (.sequenceSpread (.resolve "v4"))]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fcollect_2F4 == "ok raw=S[1, 997] n=2"

-- sem2b/v1/sys/collect/5: v1(*v2, v3) = v2 \n v4(*v5) = v1(v5*) \n v4(trace(1)) \n 997
def case_sem2b_2Fv1_2Fsys_2Fcollect_2F5 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (algWithParameters [{ name := "v2", kind := .collecting }, { name := "v3" }] [] [] [.param "v2"]), privateProp "v4" (algWithParameters [{ name := "v5", kind := .collecting }] [] [] [(.call (.resolve "v1") [(.sequenceSpread (.param "v5"))])])] [(.call (.resolve "v4") [(.call (.resolve "trace") [.num 1])]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fcollect_2F5 == "ok raw=S[L[], 997] n=2"

-- sem2b/v1/sys/collect/6: v1((v2, *v3)) = (count(v3) * 10) + v2 \n v4 = 1, 2, 3, 4 \n v1(v4) \n 997
def case_sem2b_2Fv1_2Fsys_2Fcollect_2F6 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v4" (alg [] [] [] [.num 1, .num 2, .num 3, .num 4]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (algWithParameterPatterns [.sequenceValue [.capture { name := "v2" }, .capture { name := "v3", kind := .collecting }]] [] [] [(.binary .add (.binary .mul (.call (.resolve "count") [.param "v3"]) (.num 10)) (.param "v2"))])] [(.call (.resolve "v1") [.resolve "v4"]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fcollect_2F6 == "ok raw=S[31, 997] n=2"

-- sem2b/v1/sys/collect/7: v1([v2, *v3]) = v2 + count(v3) \n v1([1]) \n 997
def case_sem2b_2Fv1_2Fsys_2Fcollect_2F7 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (algWithParameterPatterns [.listValue [.capture { name := "v2" }, .capture { name := "v3", kind := .collecting }]] [] [] [(.binary .add (.param "v2") (.call (.resolve "count") [.param "v3"]))])] [(.call (.resolve "v1") [(.listLiteral [.num 1])]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fcollect_2F7 == "ok raw=S[1, 997] n=2"

-- sem2b/v1/sys/collect-fail/0: v1(v2, v3) = v2 + v3 \n v1(trace(1), trace(2), trace(3)) \n 997
def case_sem2b_2Fv1_2Fsys_2Fcollect_2Dfail_2F0 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (alg ["v2", "v3"] [] [] [(.binary .add (.param "v2") (.param "v3"))])] [(.call (.resolve "v1") [(.call (.resolve "trace") [.num 1]), (.call (.resolve "trace") [.num 2]), (.call (.resolve "trace") [.num 3])]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fcollect_2Dfail_2F0 == "err arity"
#guard errorObs case_sem2b_2Fv1_2Fsys_2Fcollect_2Dfail_2F0 == .matched (some { kind := "arity", names := [], counts := [2, 3] })

-- sem2b/v1/sys/collect-fail/1: v1([v2, *v3]) = v2 + count(v3) \n v1([]) \n 997
def case_sem2b_2Fv1_2Fsys_2Fcollect_2Dfail_2F1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (algWithParameterPatterns [.listValue [.capture { name := "v2" }, .capture { name := "v3", kind := .collecting }]] [] [] [(.binary .add (.param "v2") (.call (.resolve "count") [.param "v3"]))])] [(.call (.resolve "v1") [(.listLiteral [])]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fcollect_2Dfail_2F1 == "err arity"
#guard errorObs case_sem2b_2Fv1_2Fsys_2Fcollect_2Dfail_2F1 == .matched (some { kind := "arity", names := [], counts := [1, 0] })

-- sem2b/v1/sys/collect-fail/2: v1((v2, *v3)) = (count(v3) * 10) + v2 \n v1(11) \n 997
def case_sem2b_2Fv1_2Fsys_2Fcollect_2Dfail_2F2 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (algWithParameterPatterns [.sequenceValue [.capture { name := "v2" }, .capture { name := "v3", kind := .collecting }]] [] [] [(.binary .add (.binary .mul (.call (.resolve "count") [.param "v3"]) (.num 10)) (.param "v2"))])] [(.call (.resolve "v1") [.num 11]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fcollect_2Dfail_2F2 == "err type"

-- sem2b/v1/sys/collect-fail/3: v1(v2, *v3, v4) = v2 \n v1(trace(1)) \n 997
def case_sem2b_2Fv1_2Fsys_2Fcollect_2Dfail_2F3 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (algWithParameters [{ name := "v2" }, { name := "v3", kind := .collecting }, { name := "v4" }] [] [] [.param "v2"])] [(.call (.resolve "v1") [(.call (.resolve "trace") [.num 1])]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fcollect_2Dfail_2F3 == "err arity"
#guard errorObs case_sem2b_2Fv1_2Fsys_2Fcollect_2Dfail_2F3 == .matched (some { kind := "arity", names := [], counts := [2, 1] })

-- sem2b/v1/sys/alias/0: v1(v2) = v2 + 1 \n v3(v4) = { \n   v1(v5) = v5 + 100 \n   v1(v4) \n } \n [v3(1), v1(1)] \n 997
def case_sem2b_2Fv1_2Fsys_2Falias_2F0 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (alg ["v2"] [] [] [(.binary .add (.param "v2") (.num 1))]), privateProp "v3" (alg ["v4"] [] [privateProp "v1" (alg ["v5"] [] [] [(.binary .add (.param "v5") (.num 100))])] [(.call (.resolve "v1") [.param "v4"])])] [(.listLiteral [(.call (.resolve "v3") [.num 1]), (.call (.resolve "v1") [.num 1])]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Falias_2F0 == "ok raw=S[L[101, 2], 997] n=2"

-- sem2b/v1/sys/alias/1: v1(meta v2) = v2 \n v3(v4, v5) = (v4 * 10) + v5 \n v6 = v1(v3(trace(1), trace(2))) \n v7 = v6.Algorithm \n [v7(3, 4)] \n 997
def case_sem2b_2Fv1_2Fsys_2Falias_2F1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v6" (alg [] [] [] [(.call (.resolve "v1") [(.call (.resolve "v3") [(.call (.resolve "trace") [.num 1]), (.call (.resolve "trace") [.num 2])])])]), privateProp "v7" (.alias none [] [] ((.dotCall (.resolve "v6") "Algorithm" none))), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (algWithParameters [{ name := "v2", kind := .metaRef }] [] [] [.param "v2"]), privateProp "v3" (alg ["v4", "v5"] [] [] [(.binary .add (.binary .mul (.param "v4") (.num 10)) (.param "v5"))])] [(.listLiteral [(.call (.resolve "v7") [.num 3, .num 4])]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Falias_2F1 == "ok raw=S[L[34], 997] n=2"

-- sem2b/v1/sys/alias/2: v1(v2) = { \n   v3 = trace(v2) \n   v3 + v3 \n } \n [v1(1), v1(1)] \n 997
def case_sem2b_2Fv1_2Fsys_2Falias_2F2 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (alg ["v2"] [] [{ (privateLocalProp "v3" (.localCapturedAncestorParams ["v2"]) (alg [] [] [] [(.call (.resolve "trace") [.param "v2"])])) with requiredOwnerDepths := some [("v2", some 0)] }] [(.binary .add (.resolve "v3") (.resolve "v3"))])] [(.listLiteral [(.call (.resolve "v1") [.num 1]), (.call (.resolve "v1") [.num 1])]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Falias_2F2 == "ok raw=S[L[2, 2], 997] n=2"

-- sem2b/v1/sys/alias/3: v1(v2) = v2 * 5 \n v3 = v1 \n v4 = v3 \n v4(1) \n 997
def case_sem2b_2Fv1_2Fsys_2Falias_2F3 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v3" (.alias none [] [] (.resolve "v1")), privateProp "v4" (.alias none [] [] (.resolve "v3")), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (alg ["v2"] [] [] [(.binary .mul (.param "v2") (.num 5))])] [(.call (.resolve "v4") [.num 1]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Falias_2F3 == "ok raw=S[5, 997] n=2"

-- sem2b/v1/sys/alias/4: v1(v2) = { \n   v3(v4) = v4 + v2 \n   v3(1) \n } \n [v1(11), v1(12)] \n 997
def case_sem2b_2Fv1_2Fsys_2Falias_2F4 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (alg ["v2"] [] [{ (privateLocalProp "v3" (.localCapturedAncestorParams ["v2"]) (alg ["v4"] [] [] [(.binary .add (.param "v4") (.param "v2"))])) with requiredOwnerDepths := some [("v2", some 0)] }] [(.call (.resolve "v3") [.num 1])])] [(.listLiteral [(.call (.resolve "v1") [.num 11]), (.call (.resolve "v1") [.num 12])]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Falias_2F4 == "ok raw=S[L[12, 13], 997] n=2"

-- sem2b/v1/sys/alias/5: v1(v2) = v2 + 1 \n v3(v4) = { \n   v1(v5) = v5 + 100 \n   v1(v4) \n } \n [v3(1), v1(1)] \n 997
def case_sem2b_2Fv1_2Fsys_2Falias_2F5 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (alg ["v2"] [] [] [(.binary .add (.param "v2") (.num 1))]), privateProp "v3" (alg ["v4"] [] [privateProp "v1" (alg ["v5"] [] [] [(.binary .add (.param "v5") (.num 100))])] [(.call (.resolve "v1") [.param "v4"])])] [(.listLiteral [(.call (.resolve "v3") [.num 1]), (.call (.resolve "v1") [.num 1])]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Falias_2F5 == "ok raw=S[L[101, 2], 997] n=2"

-- sem2b/v1/sys/alias/6: v1(meta v2) = v2 \n v3(v4, v5) = (v4 * 10) + v5 \n v6 = v1(v3(trace(1), trace(2))) \n v7 = v6.Algorithm \n [v7(3, 4)] \n 997
def case_sem2b_2Fv1_2Fsys_2Falias_2F6 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v6" (alg [] [] [] [(.call (.resolve "v1") [(.call (.resolve "v3") [(.call (.resolve "trace") [.num 1]), (.call (.resolve "trace") [.num 2])])])]), privateProp "v7" (.alias none [] [] ((.dotCall (.resolve "v6") "Algorithm" none))), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (algWithParameters [{ name := "v2", kind := .metaRef }] [] [] [.param "v2"]), privateProp "v3" (alg ["v4", "v5"] [] [] [(.binary .add (.binary .mul (.param "v4") (.num 10)) (.param "v5"))])] [(.listLiteral [(.call (.resolve "v7") [.num 3, .num 4])]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Falias_2F6 == "ok raw=S[L[34], 997] n=2"

-- sem2b/v1/sys/alias/7: v1(v2) = { \n   v3 = trace(v2) \n   v3 + v3 \n } \n [v1(1), v1(1)] \n 997
def case_sem2b_2Fv1_2Fsys_2Falias_2F7 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (alg ["v2"] [] [{ (privateLocalProp "v3" (.localCapturedAncestorParams ["v2"]) (alg [] [] [] [(.call (.resolve "trace") [.param "v2"])])) with requiredOwnerDepths := some [("v2", some 0)] }] [(.binary .add (.resolve "v3") (.resolve "v3"))])] [(.listLiteral [(.call (.resolve "v1") [.num 1]), (.call (.resolve "v1") [.num 1])]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Falias_2F7 == "ok raw=S[L[2, 2], 997] n=2"

-- sem2b/v1/sys/alias-fail/0: v1(meta v2) = v2 \n v3(v4) = v4 \n v5 = v1(v3(1)) \n v6 = v5.Algorithm \n v6 \n 997
def case_sem2b_2Fv1_2Fsys_2Falias_2Dfail_2F0 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v5" (alg [] [] [] [(.call (.resolve "v1") [(.call (.resolve "v3") [.num 1])])]), privateProp "v6" (.alias none [] [] ((.dotCall (.resolve "v5") "Algorithm" none))), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (algWithParameters [{ name := "v2", kind := .metaRef }] [] [] [.param "v2"]), privateProp "v3" (alg ["v4"] [] [] [.param "v4"])] [.resolve "v6", .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Falias_2Dfail_2F0 == "err arity"
#guard errorObs case_sem2b_2Fv1_2Fsys_2Falias_2Dfail_2F0 == .matched (some { kind := "arity", names := [], counts := [1, 0] })

-- sem2b/v1/sys/alias-fail/1: v1(meta v2) = v2 \n v3(v4) = v4 \n v5 = v1(v3(1)) \n v6 = v5.Algorithm \n v6 \n 997
def case_sem2b_2Fv1_2Fsys_2Falias_2Dfail_2F1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v5" (alg [] [] [] [(.call (.resolve "v1") [(.call (.resolve "v3") [.num 1])])]), privateProp "v6" (.alias none [] [] ((.dotCall (.resolve "v5") "Algorithm" none))), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (algWithParameters [{ name := "v2", kind := .metaRef }] [] [] [.param "v2"]), privateProp "v3" (alg ["v4"] [] [] [.param "v4"])] [.resolve "v6", .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Falias_2Dfail_2F1 == "err arity"
#guard errorObs case_sem2b_2Fv1_2Fsys_2Falias_2Dfail_2F1 == .matched (some { kind := "arity", names := [], counts := [1, 0] })

-- sem2b/v1/sys/alias-fail/2: v1(meta v2) = v2 \n v3(v4) = v4 \n v5 = v1(v3(1)) \n v6 = v5.Algorithm \n v6 \n 997
def case_sem2b_2Fv1_2Fsys_2Falias_2Dfail_2F2 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v5" (alg [] [] [] [(.call (.resolve "v1") [(.call (.resolve "v3") [.num 1])])]), privateProp "v6" (.alias none [] [] ((.dotCall (.resolve "v5") "Algorithm" none))), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (algWithParameters [{ name := "v2", kind := .metaRef }] [] [] [.param "v2"]), privateProp "v3" (alg ["v4"] [] [] [.param "v4"])] [.resolve "v6", .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Falias_2Dfail_2F2 == "err arity"
#guard errorObs case_sem2b_2Fv1_2Fsys_2Falias_2Dfail_2F2 == .matched (some { kind := "arity", names := [], counts := [1, 0] })

-- sem2b/v1/sys/alias-fail/3: v1(meta v2) = v2 \n v3(v4) = v4 \n v5 = v1(v3(1)) \n v6 = v5.Algorithm \n v6 \n 997
def case_sem2b_2Fv1_2Fsys_2Falias_2Dfail_2F3 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v5" (alg [] [] [] [(.call (.resolve "v1") [(.call (.resolve "v3") [.num 1])])]), privateProp "v6" (.alias none [] [] ((.dotCall (.resolve "v5") "Algorithm" none))), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (algWithParameters [{ name := "v2", kind := .metaRef }] [] [] [.param "v2"]), privateProp "v3" (alg ["v4"] [] [] [.param "v4"])] [.resolve "v6", .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Falias_2Dfail_2F3 == "err arity"
#guard errorObs case_sem2b_2Fv1_2Fsys_2Falias_2Dfail_2F3 == .matched (some { kind := "arity", names := [], counts := [1, 0] })

-- sem2b/v1/sys/cache/0: v1 = wait(1) \n [v1, v1()] \n 997
def case_sem2b_2Fv1_2Fsys_2Fcache_2F0 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v1" (alg [] [] [] [(.call (.resolve "wait") [.num 1])]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"])] [(.listLiteral [.resolve "v1", (.call (.resolve "v1") [])]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fcache_2F0 == "ok raw=S[L[1, 1], 997] n=2"

-- sem2b/v1/sys/cache/1: v1 = wait(1) \n [v1(), v1] \n 997
def case_sem2b_2Fv1_2Fsys_2Fcache_2F1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v1" (alg [] [] [] [(.call (.resolve "wait") [.num 1])]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"])] [(.listLiteral [(.call (.resolve "v1") []), .resolve "v1"]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fcache_2F1 == "ok raw=S[L[1, 1], 997] n=2"

-- sem2b/v1/sys/cache/2: v1(v2) = v2 + v2 \n v1(wait(1)) \n 997
def case_sem2b_2Fv1_2Fsys_2Fcache_2F2 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (alg ["v2"] [] [] [(.binary .add (.param "v2") (.param "v2"))])] [(.call (.resolve "v1") [(.call (.resolve "wait") [.num 1])]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fcache_2F2 == "ok raw=S[2, 997] n=2"

-- sem2b/v1/sys/cache/3: v1(v2) = v2 + v2 \n v3(v4) = v1(v4) \n v3(wait(1)) \n 997
def case_sem2b_2Fv1_2Fsys_2Fcache_2F3 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (alg ["v2"] [] [] [(.binary .add (.param "v2") (.param "v2"))]), privateProp "v3" (alg ["v4"] [] [] [(.call (.resolve "v1") [.param "v4"])])] [(.call (.resolve "v3") [(.call (.resolve "wait") [.num 1])]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fcache_2F3 == "ok raw=S[2, 997] n=2"

-- sem2b/v1/sys/cache/4: v1(v2) = v2 + v2 \n [v1(wait(1)), v1(wait(1))] \n 997
def case_sem2b_2Fv1_2Fsys_2Fcache_2F4 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (alg ["v2"] [] [] [(.binary .add (.param "v2") (.param "v2"))])] [(.listLiteral [(.call (.resolve "v1") [(.call (.resolve "wait") [.num 1])]), (.call (.resolve "v1") [(.call (.resolve "wait") [.num 1])])]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fcache_2F4 == "ok raw=S[L[2, 2], 997] n=2"

-- sem2b/v1/sys/cache/5: v1 = wait(1) \n [v1, v1] \n 997
def case_sem2b_2Fv1_2Fsys_2Fcache_2F5 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v1" (alg [] [] [] [(.call (.resolve "wait") [.num 1])]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"])] [(.listLiteral [.resolve "v1", .resolve "v1"]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fcache_2F5 == "ok raw=S[L[1, 1], 997] n=2"

-- sem2b/v1/sys/cache/6: v1 = wait(1) \n [v1(), v1()] \n 997
def case_sem2b_2Fv1_2Fsys_2Fcache_2F6 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v1" (alg [] [] [] [(.call (.resolve "wait") [.num 1])]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"])] [(.listLiteral [(.call (.resolve "v1") []), (.call (.resolve "v1") [])]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fcache_2F6 == "ok raw=S[L[1, 1], 997] n=2"

-- sem2b/v1/sys/cache/7: v1 = wait(1) \n [v1, v1()] \n 997
def case_sem2b_2Fv1_2Fsys_2Fcache_2F7 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v1" (alg [] [] [] [(.call (.resolve "wait") [.num 1])]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"])] [(.listLiteral [.resolve "v1", (.call (.resolve "v1") [])]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fcache_2F7 == "ok raw=S[L[1, 1], 997] n=2"

-- sem2b/v1/sys/cache-fail/0: v1 = wait(1) / 0 \n [v1, v1] \n 997
def case_sem2b_2Fv1_2Fsys_2Fcache_2Dfail_2F0 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v1" (alg [] [] [] [(.binary .div (.call (.resolve "wait") [.num 1]) (.num 0))]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"])] [(.listLiteral [.resolve "v1", .resolve "v1"]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fcache_2Dfail_2F0 == "err div0"
#guard errorObs case_sem2b_2Fv1_2Fsys_2Fcache_2Dfail_2F0 == .matched (some { kind := "div0", names := [], counts := [] })

-- sem2b/v1/sys/cache-fail/1: v1 = wait(1) / 0 \n [v1, v1] \n 997
def case_sem2b_2Fv1_2Fsys_2Fcache_2Dfail_2F1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v1" (alg [] [] [] [(.binary .div (.call (.resolve "wait") [.num 1]) (.num 0))]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"])] [(.listLiteral [.resolve "v1", .resolve "v1"]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fcache_2Dfail_2F1 == "err div0"
#guard errorObs case_sem2b_2Fv1_2Fsys_2Fcache_2Dfail_2F1 == .matched (some { kind := "div0", names := [], counts := [] })

-- sem2b/v1/sys/cache-fail/2: v1 = wait(1) / 0 \n [v1, v1] \n 997
def case_sem2b_2Fv1_2Fsys_2Fcache_2Dfail_2F2 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v1" (alg [] [] [] [(.binary .div (.call (.resolve "wait") [.num 1]) (.num 0))]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"])] [(.listLiteral [.resolve "v1", .resolve "v1"]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fcache_2Dfail_2F2 == "err div0"
#guard errorObs case_sem2b_2Fv1_2Fsys_2Fcache_2Dfail_2F2 == .matched (some { kind := "div0", names := [], counts := [] })

-- sem2b/v1/sys/cache-fail/3: v1 = wait(1) / 0 \n [v1, v1] \n 997
def case_sem2b_2Fv1_2Fsys_2Fcache_2Dfail_2F3 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v1" (alg [] [] [] [(.binary .div (.call (.resolve "wait") [.num 1]) (.num 0))]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"])] [(.listLiteral [.resolve "v1", .resolve "v1"]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fcache_2Dfail_2F3 == "err div0"
#guard errorObs case_sem2b_2Fv1_2Fsys_2Fcache_2Dfail_2F3 == .matched (some { kind := "div0", names := [], counts := [] })

-- sem2b/v1/sys/select/0: v1 = 11, 12, 13 \n v1[0, 2] \n 997
def case_sem2b_2Fv1_2Fsys_2Fselect_2F0 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v1" (alg [] [] [] [.num 11, .num 12, .num 13]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"])] [(.index (.resolve "v1") [.num 0, .num 2]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fselect_2F0 == "ok raw=S[S[11, 13], 997] n=2"

-- sem2b/v1/sys/select/1: v1 = 11, 12, 13 \n v1[] \n 997
def case_sem2b_2Fv1_2Fsys_2Fselect_2F1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v1" (alg [] [] [] [.num 11, .num 12, .num 13]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"])] [(.index (.resolve "v1") []), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fselect_2F1 == "ok raw=S[S[], 997] n=2"

-- sem2b/v1/sys/select/2: v2(v3, v4) = v3 + v4 \n v2([11, 12, 13][2, 1]*) \n 997
def case_sem2b_2Fv1_2Fsys_2Fselect_2F2 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v2" (alg ["v3", "v4"] [] [] [(.binary .add (.param "v3") (.param "v4"))])] [(.call (.resolve "v2") [(.sequenceSpread (.index (.listLiteral [.num 11, .num 12, .num 13]) [.num 2, .num 1]))]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fselect_2F2 == "ok raw=S[25, 997] n=2"

-- sem2b/v1/sys/select/3: v1 = 11, 12, 13 \n v1[trace(0), trace(2)] \n 997
def case_sem2b_2Fv1_2Fsys_2Fselect_2F3 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v1" (alg [] [] [] [.num 11, .num 12, .num 13]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"])] [(.index (.resolve "v1") [(.call (.resolve "trace") [.num 0]), (.call (.resolve "trace") [.num 2])]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fselect_2F3 == "ok raw=S[S[11, 13], 997] n=2"

-- sem2b/v1/sys/select/4: v1 = 11, 12, 13 \n v1[1] \n 997
def case_sem2b_2Fv1_2Fsys_2Fselect_2F4 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v1" (alg [] [] [] [.num 11, .num 12, .num 13]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"])] [(.index (.resolve "v1") [.num 1]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fselect_2F4 == "ok raw=S[12, 997] n=2"

-- sem2b/v1/sys/select/5: [11, 12, 13][2, 1] \n 997
def case_sem2b_2Fv1_2Fsys_2Fselect_2F5 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"])] [(.index (.listLiteral [.num 11, .num 12, .num 13]) [.num 2, .num 1]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fselect_2F5 == "ok raw=S[S[13, 12], 997] n=2"

-- sem2b/v1/sys/select/6: v1 = 11, 12, 13 \n v1[] \n 997
def case_sem2b_2Fv1_2Fsys_2Fselect_2F6 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v1" (alg [] [] [] [.num 11, .num 12, .num 13]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"])] [(.index (.resolve "v1") []), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fselect_2F6 == "ok raw=S[S[], 997] n=2"

-- sem2b/v1/sys/select/7: v1 = 11, 12, 13 \n v2(v3, v4) = v3 + v4 \n v2(v1[1, 0]*) \n 997
def case_sem2b_2Fv1_2Fsys_2Fselect_2F7 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v1" (alg [] [] [] [.num 11, .num 12, .num 13]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v2" (alg ["v3", "v4"] [] [] [(.binary .add (.param "v3") (.param "v4"))])] [(.call (.resolve "v2") [(.sequenceSpread (.index (.resolve "v1") [.num 1, .num 0]))]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fselect_2F7 == "ok raw=S[23, 997] n=2"

-- sem2b/v1/sys/select-fail/0: v1 = 11, 12, 13 \n v1[trace(0), 9, trace(1)] \n 997
def case_sem2b_2Fv1_2Fsys_2Fselect_2Dfail_2F0 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v1" (alg [] [] [] [.num 11, .num 12, .num 13]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"])] [(.index (.resolve "v1") [(.call (.resolve "trace") [.num 0]), .num 9, (.call (.resolve "trace") [.num 1])]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fselect_2Dfail_2F0 == "err index"
#guard errorObs case_sem2b_2Fv1_2Fsys_2Fselect_2Dfail_2F0 == .matched (some { kind := "index", names := [], counts := [] })

-- sem2b/v1/sys/select-fail/1: v1 = 11, 12, 13 \n v1[9, (1 / 0)*] \n 997
def case_sem2b_2Fv1_2Fsys_2Fselect_2Dfail_2F1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v1" (alg [] [] [] [.num 11, .num 12, .num 13]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"])] [(.index (.resolve "v1") [.num 9, (.sequenceSpread (.binary .div (.num 1) (.num 0)))]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fselect_2Dfail_2F1 == "err div0"
#guard errorObs case_sem2b_2Fv1_2Fsys_2Fselect_2Dfail_2F1 == .matched (some { kind := "div0", names := [], counts := [] })

-- sem2b/v1/sys/select-fail/2: [11, 12, 13][1 / 0, 9] \n 997
def case_sem2b_2Fv1_2Fsys_2Fselect_2Dfail_2F2 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"])] [(.index (.listLiteral [.num 11, .num 12, .num 13]) [(.binary .div (.num 1) (.num 0)), .num 9]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fselect_2Dfail_2F2 == "err div0"
#guard errorObs case_sem2b_2Fv1_2Fsys_2Fselect_2Dfail_2F2 == .matched (some { kind := "div0", names := [], counts := [] })

-- sem2b/v1/sys/select-fail/3: v1 = 11, 12, 13 \n v1[9] \n 997
def case_sem2b_2Fv1_2Fsys_2Fselect_2Dfail_2F3 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v1" (alg [] [] [] [.num 11, .num 12, .num 13]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"])] [(.index (.resolve "v1") [.num 9]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fselect_2Dfail_2F3 == "err index"
#guard errorObs case_sem2b_2Fv1_2Fsys_2Fselect_2Dfail_2F3 == .matched (some { kind := "index", names := [], counts := [] })

-- sem2b/v1/sys/loop/0: v1(v2) = v2 + 1 \n repeat(v1(1), 0) \n 997
def case_sem2b_2Fv1_2Fsys_2Floop_2F0 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (alg ["v2"] [] [] [(.binary .add (.param "v2") (.num 1))])] [(.call (.resolve "repeat") [(.call (.resolve "v1") [.num 1]), .num 0]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Floop_2F0 == "ok raw=S[1, 997] n=2"

-- sem2b/v1/sys/loop/1: v1(v2) = { \n   v2 + 1 \n   v2 < 2 \n } \n v1(0).while \n 997
def case_sem2b_2Fv1_2Fsys_2Floop_2F1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (alg ["v2"] [] [] [(.binary .add (.param "v2") (.num 1)), (.comparison (.param "v2") [{ op := .lt, operand := (.num 2) }])])] [(.dotCall (.call (.resolve "v1") [.num 0]) "while" none), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Floop_2F1 == "ok raw=S[2, 997] n=2"

-- sem2b/v1/sys/loop/2: v1(0) = 100 \n v1(v2) = v2 + 1 \n repeat(v1(1), 1) \n 997
def case_sem2b_2Fv1_2Fsys_2Floop_2F2 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (.conditional none [] [⟨.litInt 0, (alg [] [] [] [.num 100])⟩, ⟨.bind "v2", (alg [] [] [] [(.binary .add (.param "v2") (.num 1))])⟩])] [(.call (.resolve "repeat") [(.call (.resolve "v1") [.num 1]), .num 1]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Floop_2F2 == "ok raw=S[2, 997] n=2"

-- sem2b/v1/sys/loop/3: v1(v2) = trace(v2) + 1 \n v1(1).repeat(2) \n 997
def case_sem2b_2Fv1_2Fsys_2Floop_2F3 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (alg ["v2"] [] [] [(.binary .add (.call (.resolve "trace") [.param "v2"]) (.num 1))])] [(.dotCall (.call (.resolve "v1") [.num 1]) "repeat" (some [.num 2])), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Floop_2F3 == "ok raw=S[3, 997] n=2"

-- sem2b/v1/sys/loop/4: v1(meta v2) = v2.Algorithm(v2.Arguments*).repeat(3) \n v3(v4) = v4 + 1 \n v1(v3(1)) \n 997
def case_sem2b_2Fv1_2Fsys_2Floop_2F4 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (algWithParameters [{ name := "v2", kind := .metaRef }] [] [] [(.dotCall (.dotCall (.param "v2") "Algorithm" (some [(.sequenceSpread (.dotCall (.param "v2") "Arguments" none))])) "repeat" (some [.num 3]))]), privateProp "v3" (alg ["v4"] [] [] [(.binary .add (.param "v4") (.num 1))])] [(.call (.resolve "v1") [(.call (.resolve "v3") [.num 1])]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Floop_2F4 == "ok raw=S[4, 997] n=2"

-- sem2b/v1/sys/loop/5: v1(v2) = v2 + 3 \n v1(1).repeat(4) \n 997
def case_sem2b_2Fv1_2Fsys_2Floop_2F5 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (alg ["v2"] [] [] [(.binary .add (.param "v2") (.num 3))])] [(.dotCall (.call (.resolve "v1") [.num 1]) "repeat" (some [.num 4])), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Floop_2F5 == "ok raw=S[13, 997] n=2"

-- sem2b/v1/sys/loop/6: v1(v2) = v2 + 1 \n repeat(v1(1), 0) \n 997
def case_sem2b_2Fv1_2Fsys_2Floop_2F6 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (alg ["v2"] [] [] [(.binary .add (.param "v2") (.num 1))])] [(.call (.resolve "repeat") [(.call (.resolve "v1") [.num 1]), .num 0]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Floop_2F6 == "ok raw=S[1, 997] n=2"

-- sem2b/v1/sys/loop/7: v1(v2) = { \n   v2 + 1 \n   v2 < 3 \n } \n v1(0).while \n 997
def case_sem2b_2Fv1_2Fsys_2Floop_2F7 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (alg ["v2"] [] [] [(.binary .add (.param "v2") (.num 1)), (.comparison (.param "v2") [{ op := .lt, operand := (.num 3) }])])] [(.dotCall (.call (.resolve "v1") [.num 0]) "while" none), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Floop_2F7 == "ok raw=S[3, 997] n=2"

-- sem2b/v1/sys/loop-fail/0: v1(v2) = { \n   v2 + 1 \n   v2 + 2 \n } \n v1(0).while \n 997
def case_sem2b_2Fv1_2Fsys_2Floop_2Dfail_2F0 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (alg ["v2"] [] [] [(.binary .add (.param "v2") (.num 1)), (.binary .add (.param "v2") (.num 2))])] [(.dotCall (.call (.resolve "v1") [.num 0]) "while" none), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Floop_2Dfail_2F0 == "err type"

-- sem2b/v1/sys/loop-fail/1: v1(meta v2) = v2.repeat(2) \n v3(v4) = v4 + 1 \n v1(v3(1)) \n 997
def case_sem2b_2Fv1_2Fsys_2Floop_2Dfail_2F1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (algWithParameters [{ name := "v2", kind := .metaRef }] [] [] [(.dotCall (.param "v2") "repeat" (some [.num 2]))]), privateProp "v3" (alg ["v4"] [] [] [(.binary .add (.param "v4") (.num 1))])] [(.call (.resolve "v1") [(.call (.resolve "v3") [.num 1])]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Floop_2Dfail_2F1 == "err notAnAlgorithm"

-- sem2b/v1/sys/loop-fail/2: v1(v2) = { \n   v2 + 1 \n   v2 < 3 \n } \n v3 = v1(0) \n v3.while \n 997
def case_sem2b_2Fv1_2Fsys_2Floop_2Dfail_2F2 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v3" (alg [] [] [] [(.call (.resolve "v1") [.num 0])]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (alg ["v2"] [] [] [(.binary .add (.param "v2") (.num 1)), (.comparison (.param "v2") [{ op := .lt, operand := (.num 3) }])])] [(.dotCall (.resolve "v3") "while" none), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Floop_2Dfail_2F2 == "err notAnAlgorithm"

-- sem2b/v1/sys/loop-fail/3: v1(v2) = { \n   v2 + 1 \n   v2 + 2 \n } \n v1(0).while \n 997
def case_sem2b_2Fv1_2Fsys_2Floop_2Dfail_2F3 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (alg ["v2"] [] [] [(.binary .add (.param "v2") (.num 1)), (.binary .add (.param "v2") (.num 2))])] [(.dotCall (.call (.resolve "v1") [.num 0]) "while" none), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Floop_2Dfail_2F3 == "err type"

-- sem2b/v1/sys/failure/0: if(true, 1, trace(666) / 0) \n 997
def case_sem2b_2Fv1_2Fsys_2Ffailure_2F0 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"])] [(.call (.resolve "if") [.boolLiteral true, .num 1, (.binary .div (.call (.resolve "trace") [.num 666]) (.num 0))]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Ffailure_2F0 == "ok raw=S[1, 997] n=2"

-- sem2b/v1/sys/failure/1: v1(v2, v3) = v2 \n v1(trace(1), trace(666) / 0) \n 997
def case_sem2b_2Fv1_2Fsys_2Ffailure_2F1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (alg ["v2", "v3"] [] [] [.param "v2"])] [(.call (.resolve "v1") [(.call (.resolve "trace") [.num 1]), (.binary .div (.call (.resolve "trace") [.num 666]) (.num 0))]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Ffailure_2F1 == "ok raw=S[1, 997] n=2"

-- sem2b/v1/sys/failure/2: if(true, 1, trace(666) / 0) \n 997
def case_sem2b_2Fv1_2Fsys_2Ffailure_2F2 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"])] [(.call (.resolve "if") [.boolLiteral true, .num 1, (.binary .div (.call (.resolve "trace") [.num 666]) (.num 0))]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Ffailure_2F2 == "ok raw=S[1, 997] n=2"

-- sem2b/v1/sys/failure/3: v1(v2, v3) = v2 \n v1(trace(1), trace(666) / 0) \n 997
def case_sem2b_2Fv1_2Fsys_2Ffailure_2F3 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (alg ["v2", "v3"] [] [] [.param "v2"])] [(.call (.resolve "v1") [(.call (.resolve "trace") [.num 1]), (.binary .div (.call (.resolve "trace") [.num 666]) (.num 0))]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Ffailure_2F3 == "ok raw=S[1, 997] n=2"

-- sem2b/v1/sys/failure/4: if(true, 1, trace(666) / 0) \n 997
def case_sem2b_2Fv1_2Fsys_2Ffailure_2F4 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"])] [(.call (.resolve "if") [.boolLiteral true, .num 1, (.binary .div (.call (.resolve "trace") [.num 666]) (.num 0))]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Ffailure_2F4 == "ok raw=S[1, 997] n=2"

-- sem2b/v1/sys/failure/5: v1(v2, v3) = v2 \n v1(trace(1), trace(666) / 0) \n 997
def case_sem2b_2Fv1_2Fsys_2Ffailure_2F5 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (alg ["v2", "v3"] [] [] [.param "v2"])] [(.call (.resolve "v1") [(.call (.resolve "trace") [.num 1]), (.binary .div (.call (.resolve "trace") [.num 666]) (.num 0))]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Ffailure_2F5 == "ok raw=S[1, 997] n=2"

-- sem2b/v1/sys/failure/6: if(true, 1, trace(666) / 0) \n 997
def case_sem2b_2Fv1_2Fsys_2Ffailure_2F6 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"])] [(.call (.resolve "if") [.boolLiteral true, .num 1, (.binary .div (.call (.resolve "trace") [.num 666]) (.num 0))]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Ffailure_2F6 == "ok raw=S[1, 997] n=2"

-- sem2b/v1/sys/failure/7: v1(v2, v3) = v2 \n v1(trace(1), trace(666) / 0) \n 997
def case_sem2b_2Fv1_2Fsys_2Ffailure_2F7 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (alg ["v2", "v3"] [] [] [.param "v2"])] [(.call (.resolve "v1") [(.call (.resolve "trace") [.num 1]), (.binary .div (.call (.resolve "trace") [.num 666]) (.num 0))]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Ffailure_2F7 == "ok raw=S[1, 997] n=2"

-- sem2b/v1/sys/failure-fail/0: v1(v2, v3) = v2 + v3 \n v1(trace(1), trace(2), trace(3)) \n 997
def case_sem2b_2Fv1_2Fsys_2Ffailure_2Dfail_2F0 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (alg ["v2", "v3"] [] [] [(.binary .add (.param "v2") (.param "v3"))])] [(.call (.resolve "v1") [(.call (.resolve "trace") [.num 1]), (.call (.resolve "trace") [.num 2]), (.call (.resolve "trace") [.num 3])]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Ffailure_2Dfail_2F0 == "err arity"
#guard errorObs case_sem2b_2Fv1_2Fsys_2Ffailure_2Dfail_2F0 == .matched (some { kind := "arity", names := [], counts := [2, 3] })

-- sem2b/v1/sys/failure-fail/1: [trace(1), 1 / 0, trace(2)] \n 997
def case_sem2b_2Fv1_2Fsys_2Ffailure_2Dfail_2F1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"])] [(.listLiteral [(.call (.resolve "trace") [.num 1]), (.binary .div (.num 1) (.num 0)), (.call (.resolve "trace") [.num 2])]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Ffailure_2Dfail_2F1 == "err div0"
#guard errorObs case_sem2b_2Fv1_2Fsys_2Ffailure_2Dfail_2F1 == .matched (some { kind := "div0", names := [], counts := [] })

-- sem2b/v1/sys/failure-fail/2: if(false, trace(666), 1 / 0) \n 997
def case_sem2b_2Fv1_2Fsys_2Ffailure_2Dfail_2F2 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"])] [(.call (.resolve "if") [.boolLiteral false, (.call (.resolve "trace") [.num 666]), (.binary .div (.num 1) (.num 0))]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Ffailure_2Dfail_2F2 == "err div0"
#guard errorObs case_sem2b_2Fv1_2Fsys_2Ffailure_2Dfail_2F2 == .matched (some { kind := "div0", names := [], counts := [] })

-- sem2b/v1/sys/failure-fail/3: v1(v2, v3) = v2 + v3 \n v1(trace(1) / 0, [trace(2)][5]) \n 997
def case_sem2b_2Fv1_2Fsys_2Ffailure_2Dfail_2F3 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (alg ["v2", "v3"] [] [] [(.binary .add (.param "v2") (.param "v3"))])] [(.call (.resolve "v1") [(.binary .div (.call (.resolve "trace") [.num 1]) (.num 0)), (.index (.listLiteral [(.call (.resolve "trace") [.num 2])]) [.num 5])]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Ffailure_2Dfail_2F3 == "err div0"
#guard errorObs case_sem2b_2Fv1_2Fsys_2Ffailure_2Dfail_2F3 == .matched (some { kind := "div0", names := [], counts := [] })

-- sem2b/v1/sys/async/0: v1 = wait(1) \n [v1, v1] \n 997
def case_sem2b_2Fv1_2Fsys_2Fasync_2F0 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v1" (alg [] [] [] [(.call (.resolve "wait") [.num 1])]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"])] [(.listLiteral [.resolve "v1", .resolve "v1"]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fasync_2F0 == "ok raw=S[L[1, 1], 997] n=2"

-- sem2b/v1/sys/async/1: [wait(1), wait(2)] \n 997
def case_sem2b_2Fv1_2Fsys_2Fasync_2F1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"])] [(.listLiteral [(.call (.resolve "wait") [.num 1]), (.call (.resolve "wait") [.num 2])]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fasync_2F1 == "ok raw=S[L[1, 2], 997] n=2"

-- sem2b/v1/sys/async/2: v1(meta v2) = v2 \n v3(v4, v5) = (v4 * 10) + v5 \n v6 = v1(v3(wait(1), wait(2))) \n [v6.Arguments[1], v6.Invoke()] \n 997
def case_sem2b_2Fv1_2Fsys_2Fasync_2F2 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v6" (alg [] [] [] [(.call (.resolve "v1") [(.call (.resolve "v3") [(.call (.resolve "wait") [.num 1]), (.call (.resolve "wait") [.num 2])])])]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (algWithParameters [{ name := "v2", kind := .metaRef }] [] [] [.param "v2"]), privateProp "v3" (alg ["v4", "v5"] [] [] [(.binary .add (.binary .mul (.param "v4") (.num 10)) (.param "v5"))])] [(.listLiteral [(.index (.dotCall (.resolve "v6") "Arguments" none) [.num 1]), (.dotCall (.resolve "v6") "Invoke" (some []))]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fasync_2F2 == "ok raw=S[L[2, 12], 997] n=2"

-- sem2b/v1/sys/async/3: v1(v2) = v2 + v2 \n v1(wait(1)) \n 997
def case_sem2b_2Fv1_2Fsys_2Fasync_2F3 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (alg ["v2"] [] [] [(.binary .add (.param "v2") (.param "v2"))])] [(.call (.resolve "v1") [(.call (.resolve "wait") [.num 1])]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fasync_2F3 == "ok raw=S[2, 997] n=2"

-- sem2b/v1/sys/async/4: v1 = wait(1) \n [v1, v1] \n 997
def case_sem2b_2Fv1_2Fsys_2Fasync_2F4 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v1" (alg [] [] [] [(.call (.resolve "wait") [.num 1])]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"])] [(.listLiteral [.resolve "v1", .resolve "v1"]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fasync_2F4 == "ok raw=S[L[1, 1], 997] n=2"

-- sem2b/v1/sys/async/5: [wait(1), wait(2)] \n 997
def case_sem2b_2Fv1_2Fsys_2Fasync_2F5 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"])] [(.listLiteral [(.call (.resolve "wait") [.num 1]), (.call (.resolve "wait") [.num 2])]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fasync_2F5 == "ok raw=S[L[1, 2], 997] n=2"

-- sem2b/v1/sys/async/6: v1(meta v2) = v2 \n v3(v4, v5) = (v4 * 10) + v5 \n v6 = v1(v3(wait(1), wait(2))) \n [v6.Arguments[1], v6.Invoke()] \n 997
def case_sem2b_2Fv1_2Fsys_2Fasync_2F6 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v6" (alg [] [] [] [(.call (.resolve "v1") [(.call (.resolve "v3") [(.call (.resolve "wait") [.num 1]), (.call (.resolve "wait") [.num 2])])])]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (algWithParameters [{ name := "v2", kind := .metaRef }] [] [] [.param "v2"]), privateProp "v3" (alg ["v4", "v5"] [] [] [(.binary .add (.binary .mul (.param "v4") (.num 10)) (.param "v5"))])] [(.listLiteral [(.index (.dotCall (.resolve "v6") "Arguments" none) [.num 1]), (.dotCall (.resolve "v6") "Invoke" (some []))]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fasync_2F6 == "ok raw=S[L[2, 12], 997] n=2"

-- sem2b/v1/sys/async/7: v1(v2) = v2 + v2 \n v1(wait(1)) \n 997
def case_sem2b_2Fv1_2Fsys_2Fasync_2F7 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (alg ["v2"] [] [] [(.binary .add (.param "v2") (.param "v2"))])] [(.call (.resolve "v1") [(.call (.resolve "wait") [.num 1])]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fasync_2F7 == "ok raw=S[2, 997] n=2"

-- sem2b/v1/sys/async-fail/0: [wait(1), 1 / 0, wait(2)] \n 997
def case_sem2b_2Fv1_2Fsys_2Fasync_2Dfail_2F0 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"])] [(.listLiteral [(.call (.resolve "wait") [.num 1]), (.binary .div (.num 1) (.num 0)), (.call (.resolve "wait") [.num 2])]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fasync_2Dfail_2F0 == "err div0"
#guard errorObs case_sem2b_2Fv1_2Fsys_2Fasync_2Dfail_2F0 == .matched (some { kind := "div0", names := [], counts := [] })

-- sem2b/v1/sys/async-fail/1: [wait(1), 1 / 0, wait(2)] \n 997
def case_sem2b_2Fv1_2Fsys_2Fasync_2Dfail_2F1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"])] [(.listLiteral [(.call (.resolve "wait") [.num 1]), (.binary .div (.num 1) (.num 0)), (.call (.resolve "wait") [.num 2])]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fasync_2Dfail_2F1 == "err div0"
#guard errorObs case_sem2b_2Fv1_2Fsys_2Fasync_2Dfail_2F1 == .matched (some { kind := "div0", names := [], counts := [] })

-- sem2b/v1/sys/async-fail/2: [wait(1), 1 / 0, wait(2)] \n 997
def case_sem2b_2Fv1_2Fsys_2Fasync_2Dfail_2F2 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"])] [(.listLiteral [(.call (.resolve "wait") [.num 1]), (.binary .div (.num 1) (.num 0)), (.call (.resolve "wait") [.num 2])]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fasync_2Dfail_2F2 == "err div0"
#guard errorObs case_sem2b_2Fv1_2Fsys_2Fasync_2Dfail_2F2 == .matched (some { kind := "div0", names := [], counts := [] })

-- sem2b/v1/sys/async-fail/3: [wait(1), 1 / 0, wait(2)] \n 997
def case_sem2b_2Fv1_2Fsys_2Fasync_2Dfail_2F3 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"])] [(.listLiteral [(.call (.resolve "wait") [.num 1]), (.binary .div (.num 1) (.num 0)), (.call (.resolve "wait") [.num 2])]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fasync_2Dfail_2F3 == "err div0"
#guard errorObs case_sem2b_2Fv1_2Fsys_2Fasync_2Dfail_2F3 == .matched (some { kind := "div0", names := [], counts := [] })

-- sem2b/v1/sys/context/list/alias: v1(meta v2) = v2 \n v3(v4, v5) = (v4 * 10) + v5 \n v6 = v1(v3(trace(1), trace(2))) \n v7 = v6.Algorithm \n [[v7(3, 4)]] \n 997
def case_sem2b_2Fv1_2Fsys_2Fcontext_2Flist_2Falias : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v6" (alg [] [] [] [(.call (.resolve "v1") [(.call (.resolve "v3") [(.call (.resolve "trace") [.num 1]), (.call (.resolve "trace") [.num 2])])])]), privateProp "v7" (.alias none [] [] ((.dotCall (.resolve "v6") "Algorithm" none))), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (algWithParameters [{ name := "v2", kind := .metaRef }] [] [] [.param "v2"]), privateProp "v3" (alg ["v4", "v5"] [] [] [(.binary .add (.binary .mul (.param "v4") (.num 10)) (.param "v5"))])] [(.listLiteral [(.listLiteral [(.call (.resolve "v7") [.num 3, .num 4])])]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fcontext_2Flist_2Falias == "ok raw=S[L[L[34]], 997] n=2"

-- sem2b/v1/sys/context/list/cache: v1(v2) = v2 + v2 \n [v1(wait(1))] \n 997
def case_sem2b_2Fv1_2Fsys_2Fcontext_2Flist_2Fcache : Expr :=
  .algorithmExpr (alg [] [] [privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (alg ["v2"] [] [] [(.binary .add (.param "v2") (.param "v2"))])] [(.listLiteral [(.call (.resolve "v1") [(.call (.resolve "wait") [.num 1])])]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fcontext_2Flist_2Fcache == "ok raw=S[L[2], 997] n=2"

-- sem2b/v1/sys/context/if-true/select: v2(v3, v4) = v3 + v4 \n if(true, v2([11, 12, 13][2, 1]*), trace(666)) \n 997
def case_sem2b_2Fv1_2Fsys_2Fcontext_2Fif_2Dtrue_2Fselect : Expr :=
  .algorithmExpr (alg [] [] [privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v2" (alg ["v3", "v4"] [] [] [(.binary .add (.param "v3") (.param "v4"))])] [(.call (.resolve "if") [.boolLiteral true, (.call (.resolve "v2") [(.sequenceSpread (.index (.listLiteral [.num 11, .num 12, .num 13]) [.num 2, .num 1]))]), (.call (.resolve "trace") [.num 666])]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fcontext_2Fif_2Dtrue_2Fselect == "ok raw=S[25, 997] n=2"

-- sem2b/v1/sys/context/if-true/loop: v1(v2) = trace(v2) + 1 \n if(true, v1(1).repeat(2), trace(666)) \n 997
def case_sem2b_2Fv1_2Fsys_2Fcontext_2Fif_2Dtrue_2Floop : Expr :=
  .algorithmExpr (alg [] [] [privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (alg ["v2"] [] [] [(.binary .add (.call (.resolve "trace") [.param "v2"]) (.num 1))])] [(.call (.resolve "if") [.boolLiteral true, (.dotCall (.call (.resolve "v1") [.num 1]) "repeat" (some [.num 2])), (.call (.resolve "trace") [.num 666])]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fcontext_2Fif_2Dtrue_2Floop == "ok raw=S[3, 997] n=2"

-- sem2b/v1/sys/context/if-false/failure: v1(v2, v3) = v2 \n if(false, trace(666), v1(trace(1), trace(666) / 0)) \n 997
def case_sem2b_2Fv1_2Fsys_2Fcontext_2Fif_2Dfalse_2Ffailure : Expr :=
  .algorithmExpr (alg [] [] [privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (alg ["v2", "v3"] [] [] [.param "v2"])] [(.call (.resolve "if") [.boolLiteral false, (.call (.resolve "trace") [.num 666]), (.call (.resolve "v1") [(.call (.resolve "trace") [.num 1]), (.binary .div (.call (.resolve "trace") [.num 666]) (.num 0))])]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fcontext_2Fif_2Dfalse_2Ffailure == "ok raw=S[1, 997] n=2"

-- sem2b/v1/sys/context/if-false/async: v1 = wait(1) \n if(false, trace(666), [v1, v1]) \n 997
def case_sem2b_2Fv1_2Fsys_2Fcontext_2Fif_2Dfalse_2Fasync : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v1" (alg [] [] [] [(.call (.resolve "wait") [.num 1])]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"])] [(.call (.resolve "if") [.boolLiteral false, (.call (.resolve "trace") [.num 666]), (.listLiteral [.resolve "v1", .resolve "v1"])]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fcontext_2Fif_2Dfalse_2Fasync == "ok raw=S[L[1, 1], 997] n=2"

-- sem2b/v1/sys/context/property/meta: v1(meta v2) = v2 \n v3(v4) = v1(v4) \n v5(v6) = trace(v6) \n v7 = v3(v5(trace(1))) \n v8(v9) = v9 \n v10 = [v7.Arguments[0], v7.Invoke(), v8(v7.Arguments*)] \n v10 \n 997
def case_sem2b_2Fv1_2Fsys_2Fcontext_2Fproperty_2Fmeta : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v7" (alg [] [] [] [(.call (.resolve "v3") [(.call (.resolve "v5") [(.call (.resolve "trace") [.num 1])])])]), privateProp "v10" (alg [] [] [] [(.listLiteral [(.index (.dotCall (.resolve "v7") "Arguments" none) [.num 0]), (.dotCall (.resolve "v7") "Invoke" (some [])), (.call (.resolve "v8") [(.sequenceSpread (.dotCall (.resolve "v7") "Arguments" none))])])]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (algWithParameters [{ name := "v2", kind := .metaRef }] [] [] [.param "v2"]), privateProp "v3" (alg ["v4"] [] [] [(.call (.resolve "v1") [.param "v4"])]), privateProp "v5" (alg ["v6"] [] [] [(.call (.resolve "trace") [.param "v6"])]), privateProp "v8" (alg ["v9"] [] [] [.param "v9"])] [.resolve "v10", .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fcontext_2Fproperty_2Fmeta == "ok raw=S[L[1, 1, 1], 997] n=2"

-- sem2b/v1/sys/context/property/collect: v1(*v2, v3) = v2 \n v4(*v5) = v1(v5*) \n v6 = v4(trace(1)) \n v6 \n 997
def case_sem2b_2Fv1_2Fsys_2Fcontext_2Fproperty_2Fcollect : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v6" (alg [] [] [] [(.call (.resolve "v4") [(.call (.resolve "trace") [.num 1])])]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (algWithParameters [{ name := "v2", kind := .collecting }, { name := "v3" }] [] [] [.param "v2"]), privateProp "v4" (algWithParameters [{ name := "v5", kind := .collecting }] [] [] [(.call (.resolve "v1") [(.sequenceSpread (.param "v5"))])])] [.resolve "v6", .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fcontext_2Fproperty_2Fcollect == "ok raw=S[L[], 997] n=2"

-- sem2b/v1/sys/context/property-double/alias: v1(v2) = v2 + 1 \n v3(v4) = { \n   v1(v5) = v5 + 100 \n   v1(v4) \n } \n v6 = [v3(1), v1(1)] \n [v6, v6] \n 997
def case_sem2b_2Fv1_2Fsys_2Fcontext_2Fproperty_2Ddouble_2Falias : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v6" (alg [] [] [] [(.listLiteral [(.call (.resolve "v3") [.num 1]), (.call (.resolve "v1") [.num 1])])]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (alg ["v2"] [] [] [(.binary .add (.param "v2") (.num 1))]), privateProp "v3" (alg ["v4"] [] [privateProp "v1" (alg ["v5"] [] [] [(.binary .add (.param "v5") (.num 100))])] [(.call (.resolve "v1") [.param "v4"])])] [(.listLiteral [.resolve "v6", .resolve "v6"]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fcontext_2Fproperty_2Ddouble_2Falias == "ok raw=S[L[L[101, 2], L[101, 2]], 997] n=2"

-- sem2b/v1/sys/context/property-double/cache: v1 = wait(1) \n v2 = [v1(), v1()] \n [v2, v2] \n 997
def case_sem2b_2Fv1_2Fsys_2Fcontext_2Fproperty_2Ddouble_2Fcache : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v1" (alg [] [] [] [(.call (.resolve "wait") [.num 1])]), privateProp "v2" (alg [] [] [] [(.listLiteral [(.call (.resolve "v1") []), (.call (.resolve "v1") [])])]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"])] [(.listLiteral [.resolve "v2", .resolve "v2"]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fcontext_2Fproperty_2Ddouble_2Fcache == "ok raw=S[L[L[1, 1], L[1, 1]], 997] n=2"

-- sem2b/v1/sys/context/wrapper/select: v1 = 11, 12, 13 \n v2(v3) = v3 \n v2(v1[]) \n 997
def case_sem2b_2Fv1_2Fsys_2Fcontext_2Fwrapper_2Fselect : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v1" (alg [] [] [] [.num 11, .num 12, .num 13]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v2" (alg ["v3"] [] [] [.param "v3"])] [(.call (.resolve "v2") [(.index (.resolve "v1") [])]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fcontext_2Fwrapper_2Fselect == "ok raw=S[S[], 997] n=2"

-- sem2b/v1/sys/context/wrapper/loop: v1(v2) = { \n   v2 + 1 \n   v2 < 3 \n } \n v3(v4) = v4 \n v3(v1(0).while) \n 997
def case_sem2b_2Fv1_2Fsys_2Fcontext_2Fwrapper_2Floop : Expr :=
  .algorithmExpr (alg [] [] [privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (alg ["v2"] [] [] [(.binary .add (.param "v2") (.num 1)), (.comparison (.param "v2") [{ op := .lt, operand := (.num 3) }])]), privateProp "v3" (alg ["v4"] [] [] [.param "v4"])] [(.call (.resolve "v3") [(.dotCall (.call (.resolve "v1") [.num 0]) "while" none)]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fcontext_2Fwrapper_2Floop == "ok raw=S[3, 997] n=2"

-- sem2b/v1/sys/context/brace/failure: v1(v2, v3) = v2 \n { \n   v4 = 0 \n   v1(trace(1), trace(666) / 0) \n } \n 997
def case_sem2b_2Fv1_2Fsys_2Fcontext_2Fbrace_2Ffailure : Expr :=
  .algorithmExpr (alg [] [] [privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (alg ["v2", "v3"] [] [] [.param "v2"])] [(.algorithmExpr (alg [] [] [privateProp "v4" (alg [] [] [] [.num 0])] [(.call (.resolve "v1") [(.call (.resolve "trace") [.num 1]), (.binary .div (.call (.resolve "trace") [.num 666]) (.num 0))])])), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fcontext_2Fbrace_2Ffailure == "ok raw=S[1, 997] n=2"

-- sem2b/v1/sys/context/brace/async: v1 = wait(1) \n { \n   v2 = 0 \n   [v1, v1] \n } \n 997
def case_sem2b_2Fv1_2Fsys_2Fcontext_2Fbrace_2Fasync : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v1" (alg [] [] [] [(.call (.resolve "wait") [.num 1])]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"])] [(.algorithmExpr (alg [] [] [privateProp "v2" (alg [] [] [] [.num 0])] [(.listLiteral [.resolve "v1", .resolve "v1"])])), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fcontext_2Fbrace_2Fasync == "ok raw=S[L[1, 1], 997] n=2"

-- sem2b/v1/sys/pair/meta+cache: v1(meta v2) = v2 \n v3 = v1 \n v4(v5, v6, v7) = trace((v5 * 100) + (v6 * 10) + v7) \n v8 = v3(v4(trace(1), trace(2), trace(3))) \n v9(v10, v11, v12) = v12 \n v13 = wait(7) \n [v9(v8.Arguments*), v8.Algorithm(4, 5, 6), v8.Algorithm(v8.Arguments*)] \n [v13, v13()] \n 997
def case_sem2b_2Fv1_2Fsys_2Fpair_2Fmeta_2Bcache : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v3" (.alias none [] [] (.resolve "v1")), privateProp "v8" (alg [] [] [] [(.call (.resolve "v3") [(.call (.resolve "v4") [(.call (.resolve "trace") [.num 1]), (.call (.resolve "trace") [.num 2]), (.call (.resolve "trace") [.num 3])])])]), privateProp "v13" (alg [] [] [] [(.call (.resolve "wait") [.num 7])]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (algWithParameters [{ name := "v2", kind := .metaRef }] [] [] [.param "v2"]), privateProp "v4" (alg ["v5", "v6", "v7"] [] [] [(.call (.resolve "trace") [(.binary .add (.binary .add (.binary .mul (.param "v5") (.num 100)) (.binary .mul (.param "v6") (.num 10))) (.param "v7"))])]), privateProp "v9" (alg ["v10", "v11", "v12"] [] [] [.param "v12"])] [(.listLiteral [(.call (.resolve "v9") [(.sequenceSpread (.dotCall (.resolve "v8") "Arguments" none))]), (.dotCall (.resolve "v8") "Algorithm" (some [.num 4, .num 5, .num 6])), (.dotCall (.resolve "v8") "Algorithm" (some [(.sequenceSpread (.dotCall (.resolve "v8") "Arguments" none))]))]), (.listLiteral [.resolve "v13", (.call (.resolve "v13") [])]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fpair_2Fmeta_2Bcache == "ok raw=S[L[3, 456, 123], L[7, 7], 997] n=3"

-- sem2b/v1/sys/pair/meta+select-fail: v1(meta v2) = v2 \n v3(v4) = v1(v4) \n v5(v6) = v6 \n v7 = v3(v5(trace(1))) \n v8 = 11, 12, 13 \n [v7.Algorithm(2), v7.Algorithm(v7.Arguments*), v7.Arguments.count, v7.Arguments[0]] \n v8[9, (1 / 0)*] \n 997
def case_sem2b_2Fv1_2Fsys_2Fpair_2Fmeta_2Bselect_2Dfail : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v7" (alg [] [] [] [(.call (.resolve "v3") [(.call (.resolve "v5") [(.call (.resolve "trace") [.num 1])])])]), privateProp "v8" (alg [] [] [] [.num 11, .num 12, .num 13]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (algWithParameters [{ name := "v2", kind := .metaRef }] [] [] [.param "v2"]), privateProp "v3" (alg ["v4"] [] [] [(.call (.resolve "v1") [.param "v4"])]), privateProp "v5" (alg ["v6"] [] [] [.param "v6"])] [(.listLiteral [(.dotCall (.resolve "v7") "Algorithm" (some [.num 2])), (.dotCall (.resolve "v7") "Algorithm" (some [(.sequenceSpread (.dotCall (.resolve "v7") "Arguments" none))])), (.dotCall (.dotCall (.resolve "v7") "Arguments" none) "count" none), (.index (.dotCall (.resolve "v7") "Arguments" none) [.num 0])]), (.index (.resolve "v8") [.num 9, (.sequenceSpread (.binary .div (.num 1) (.num 0)))]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fpair_2Fmeta_2Bselect_2Dfail == "err div0"
#guard errorObs case_sem2b_2Fv1_2Fsys_2Fpair_2Fmeta_2Bselect_2Dfail == .matched (some { kind := "div0", names := [], counts := [] })

-- sem2b/v1/sys/pair/collect+select: v1((v2, *v3)) = (count(v3) * 10) + v2 \n v4 = 1, 2, 3 \n v6(v7, v8) = v7 + v8 \n v1(v4) \n v6([11, 12, 13][2, 1]*) \n 997
def case_sem2b_2Fv1_2Fsys_2Fpair_2Fcollect_2Bselect : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v4" (alg [] [] [] [.num 1, .num 2, .num 3]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (algWithParameterPatterns [.sequenceValue [.capture { name := "v2" }, .capture { name := "v3", kind := .collecting }]] [] [] [(.binary .add (.binary .mul (.call (.resolve "count") [.param "v3"]) (.num 10)) (.param "v2"))]), privateProp "v6" (alg ["v7", "v8"] [] [] [(.binary .add (.param "v7") (.param "v8"))])] [(.call (.resolve "v1") [.resolve "v4"]), (.call (.resolve "v6") [(.sequenceSpread (.index (.listLiteral [.num 11, .num 12, .num 13]) [.num 2, .num 1]))]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fpair_2Fcollect_2Bselect == "ok raw=S[21, 25, 997] n=3"

-- sem2b/v1/sys/pair/alias+meta: v1(v2) = v2 * 5 \n v3 = v1 \n v4 = v3 \n v5(meta v6) = v6 \n v7 = v5 \n v8(v9, v10, v11) = (v9 * 100) + (v10 * 10) + v11 \n v12 = v7(v8(trace(2), trace(3), trace(4))) \n v4(1) \n [v12.Arguments.count, v12.Arguments[1]] \n 997
def case_sem2b_2Fv1_2Fsys_2Fpair_2Falias_2Bmeta : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v3" (.alias none [] [] (.resolve "v1")), privateProp "v4" (.alias none [] [] (.resolve "v3")), privateProp "v7" (.alias none [] [] (.resolve "v5")), privateProp "v12" (alg [] [] [] [(.call (.resolve "v7") [(.call (.resolve "v8") [(.call (.resolve "trace") [.num 2]), (.call (.resolve "trace") [.num 3]), (.call (.resolve "trace") [.num 4])])])]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (alg ["v2"] [] [] [(.binary .mul (.param "v2") (.num 5))]), privateProp "v5" (algWithParameters [{ name := "v6", kind := .metaRef }] [] [] [.param "v6"]), privateProp "v8" (alg ["v9", "v10", "v11"] [] [] [(.binary .add (.binary .add (.binary .mul (.param "v9") (.num 100)) (.binary .mul (.param "v10") (.num 10))) (.param "v11"))])] [(.call (.resolve "v4") [.num 1]), (.listLiteral [(.dotCall (.dotCall (.resolve "v12") "Arguments" none) "count" none), (.index (.dotCall (.resolve "v12") "Arguments" none) [.num 1])]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fpair_2Falias_2Bmeta == "ok raw=S[5, L[3, 3], 997] n=3"

-- sem2b/v1/sys/pair/cache+async: v1(v2) = v2 + v2 \n v3 = wait(2) \n [v1(wait(1)), v1(wait(1))] \n [v3, v3] \n 997
def case_sem2b_2Fv1_2Fsys_2Fpair_2Fcache_2Basync : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v3" (alg [] [] [] [(.call (.resolve "wait") [.num 2])]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (alg ["v2"] [] [] [(.binary .add (.param "v2") (.param "v2"))])] [(.listLiteral [(.call (.resolve "v1") [(.call (.resolve "wait") [.num 1])]), (.call (.resolve "v1") [(.call (.resolve "wait") [.num 1])])]), (.listLiteral [.resolve "v3", .resolve "v3"]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fpair_2Fcache_2Basync == "ok raw=S[L[2, 2], L[2, 2], 997] n=3"

-- sem2b/v1/sys/pair/loop+meta: v1(v2) = v2 + 3 \n v3(meta v4) = v4 \n v5 = 11, 12 \n v6(*v7) = count(v7) \n v8 = v3(v6(trace(2), trace(3), v5*)) \n v9(v10, v11, v12, v13) = v10 \n v1(1).repeat(4) \n [v8.Invoke(), v9(v8.Arguments*), v8.Algorithm(4, 5), v8.Algorithm(v8.Arguments*)] \n 997
def case_sem2b_2Fv1_2Fsys_2Fpair_2Floop_2Bmeta : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v5" (alg [] [] [] [.num 11, .num 12]), privateProp "v8" (alg [] [] [] [(.call (.resolve "v3") [(.call (.resolve "v6") [(.call (.resolve "trace") [.num 2]), (.call (.resolve "trace") [.num 3]), (.sequenceSpread (.resolve "v5"))])])]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (alg ["v2"] [] [] [(.binary .add (.param "v2") (.num 3))]), privateProp "v3" (algWithParameters [{ name := "v4", kind := .metaRef }] [] [] [.param "v4"]), privateProp "v6" (algWithParameters [{ name := "v7", kind := .collecting }] [] [] [(.call (.resolve "count") [.param "v7"])]), privateProp "v9" (alg ["v10", "v11", "v12", "v13"] [] [] [.param "v10"])] [(.dotCall (.call (.resolve "v1") [.num 1]) "repeat" (some [.num 4])), (.listLiteral [(.dotCall (.resolve "v8") "Invoke" (some [])), (.call (.resolve "v9") [(.sequenceSpread (.dotCall (.resolve "v8") "Arguments" none))]), (.dotCall (.resolve "v8") "Algorithm" (some [.num 4, .num 5])), (.dotCall (.resolve "v8") "Algorithm" (some [(.sequenceSpread (.dotCall (.resolve "v8") "Arguments" none))]))]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fpair_2Floop_2Bmeta == "ok raw=S[13, L[4, 2, 2, 4], 997] n=3"

-- sem2b/v1/sys/pair/select+failure-fail: v1 = 11, 12, 13 \n v1[] \n [trace(1), 1 / 0, trace(2)] \n 997
def case_sem2b_2Fv1_2Fsys_2Fpair_2Fselect_2Bfailure_2Dfail : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v1" (alg [] [] [] [.num 11, .num 12, .num 13]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"])] [(.index (.resolve "v1") []), (.listLiteral [(.call (.resolve "trace") [.num 1]), (.binary .div (.num 1) (.num 0)), (.call (.resolve "trace") [.num 2])]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fpair_2Fselect_2Bfailure_2Dfail == "err div0"
#guard errorObs case_sem2b_2Fv1_2Fsys_2Fpair_2Fselect_2Bfailure_2Dfail == .matched (some { kind := "div0", names := [], counts := [] })

-- sem2b/v1/sys/pair/async+collect-fail: v1(v2) = v2 + v2 \n v3(v4, *v5, v6) = v4 \n v1(wait(1)) \n v3(trace(2)) \n 997
def case_sem2b_2Fv1_2Fsys_2Fpair_2Fasync_2Bcollect_2Dfail : Expr :=
  .algorithmExpr (alg [] [] [privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (alg ["v2"] [] [] [(.binary .add (.param "v2") (.param "v2"))]), privateProp "v3" (algWithParameters [{ name := "v4" }, { name := "v5", kind := .collecting }, { name := "v6" }] [] [] [.param "v4"])] [(.call (.resolve "v1") [(.call (.resolve "wait") [.num 1])]), (.call (.resolve "v3") [(.call (.resolve "trace") [.num 2])]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fpair_2Fasync_2Bcollect_2Dfail == "err arity"
#guard errorObs case_sem2b_2Fv1_2Fsys_2Fpair_2Fasync_2Bcollect_2Dfail == .matched (some { kind := "arity", names := [], counts := [2, 1] })

-- sem2b/v1/sys/pair/loop+async: v1(0) = 100 \n v1(v2) = v2 + 1 \n v3 = wait(2) \n repeat(v1(1), 3) \n [v3, v3] \n 997
def case_sem2b_2Fv1_2Fsys_2Fpair_2Floop_2Basync : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v3" (alg [] [] [] [(.call (.resolve "wait") [.num 2])]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (.conditional none [] [⟨.litInt 0, (alg [] [] [] [.num 100])⟩, ⟨.bind "v2", (alg [] [] [] [(.binary .add (.param "v2") (.num 1))])⟩])] [(.call (.resolve "repeat") [(.call (.resolve "v1") [.num 1]), .num 3]), (.listLiteral [.resolve "v3", .resolve "v3"]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fpair_2Floop_2Basync == "ok raw=S[4, L[2, 2], 997] n=3"

-- sem2b/v1/sys/pair/collect+cache-fail: v1(*v2, v3) = v2 \n v4(*v5) = v1(v5*) \n v6 = wait(2) / 0 \n v4(trace(1)) \n [v6, v6] \n 997
def case_sem2b_2Fv1_2Fsys_2Fpair_2Fcollect_2Bcache_2Dfail : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v6" (alg [] [] [] [(.binary .div (.call (.resolve "wait") [.num 2]) (.num 0))]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (algWithParameters [{ name := "v2", kind := .collecting }, { name := "v3" }] [] [] [.param "v2"]), privateProp "v4" (algWithParameters [{ name := "v5", kind := .collecting }] [] [] [(.call (.resolve "v1") [(.sequenceSpread (.param "v5"))])])] [(.call (.resolve "v4") [(.call (.resolve "trace") [.num 1])]), (.listLiteral [.resolve "v6", .resolve "v6"]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fpair_2Fcollect_2Bcache_2Dfail == "err div0"
#guard errorObs case_sem2b_2Fv1_2Fsys_2Fpair_2Fcollect_2Bcache_2Dfail == .matched (some { kind := "div0", names := [], counts := [] })

-- sem2b/v1/sys/triple/meta+loop+async: v1(meta v2) = v2 \n v3(v4) = v1(v4) \n v5(v6) = v6 \n v7 = v3(v5(trace(1))) \n v8(v9) = { \n   v9 + 1 \n   v9 < 2 \n } \n [[v7.Algorithm(2), v7.Algorithm(v7.Arguments*), v7.Arguments.count, v7.Arguments[0]]] \n v8(0).while \n [wait(4), wait(5)] \n 997
def case_sem2b_2Fv1_2Fsys_2Ftriple_2Fmeta_2Bloop_2Basync : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v7" (alg [] [] [] [(.call (.resolve "v3") [(.call (.resolve "v5") [(.call (.resolve "trace") [.num 1])])])]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (algWithParameters [{ name := "v2", kind := .metaRef }] [] [] [.param "v2"]), privateProp "v3" (alg ["v4"] [] [] [(.call (.resolve "v1") [.param "v4"])]), privateProp "v5" (alg ["v6"] [] [] [.param "v6"]), privateProp "v8" (alg ["v9"] [] [] [(.binary .add (.param "v9") (.num 1)), (.comparison (.param "v9") [{ op := .lt, operand := (.num 2) }])])] [(.listLiteral [(.listLiteral [(.dotCall (.resolve "v7") "Algorithm" (some [.num 2])), (.dotCall (.resolve "v7") "Algorithm" (some [(.sequenceSpread (.dotCall (.resolve "v7") "Arguments" none))])), (.dotCall (.dotCall (.resolve "v7") "Arguments" none) "count" none), (.index (.dotCall (.resolve "v7") "Arguments" none) [.num 0])])]), (.dotCall (.call (.resolve "v8") [.num 0]) "while" none), (.listLiteral [(.call (.resolve "wait") [.num 4]), (.call (.resolve "wait") [.num 5])]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Ftriple_2Fmeta_2Bloop_2Basync == "ok raw=S[L[L[2, 1, 1, 1]], 2, L[4, 5], 997] n=4"

-- sem2b/v1/sys/triple/collect+meta+failure-fail: v1((v2, *v3)) = (count(v3) * 10) + v2 \n v4 = 1, 2, 3 \n v5(meta v6) = v6 \n v7 = 11, 12 \n v8(*v9) = trace(count(v9)) \n v10 = v5(v8(trace(4), trace(5), v7*)) \n if(true, v1(v4), trace(666)) \n [v10.Algorithm(v10.Arguments*)] \n if(false, trace(666), 1 / 0) \n 997
def case_sem2b_2Fv1_2Fsys_2Ftriple_2Fcollect_2Bmeta_2Bfailure_2Dfail : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v4" (alg [] [] [] [.num 1, .num 2, .num 3]), privateProp "v7" (alg [] [] [] [.num 11, .num 12]), privateProp "v10" (alg [] [] [] [(.call (.resolve "v5") [(.call (.resolve "v8") [(.call (.resolve "trace") [.num 4]), (.call (.resolve "trace") [.num 5]), (.sequenceSpread (.resolve "v7"))])])]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (algWithParameterPatterns [.sequenceValue [.capture { name := "v2" }, .capture { name := "v3", kind := .collecting }]] [] [] [(.binary .add (.binary .mul (.call (.resolve "count") [.param "v3"]) (.num 10)) (.param "v2"))]), privateProp "v5" (algWithParameters [{ name := "v6", kind := .metaRef }] [] [] [.param "v6"]), privateProp "v8" (algWithParameters [{ name := "v9", kind := .collecting }] [] [] [(.call (.resolve "trace") [(.call (.resolve "count") [.param "v9"])])])] [(.call (.resolve "if") [.boolLiteral true, (.call (.resolve "v1") [.resolve "v4"]), (.call (.resolve "trace") [.num 666])]), (.listLiteral [(.dotCall (.resolve "v10") "Algorithm" (some [(.sequenceSpread (.dotCall (.resolve "v10") "Arguments" none))]))]), (.call (.resolve "if") [.boolLiteral false, (.call (.resolve "trace") [.num 666]), (.binary .div (.num 1) (.num 0))]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Ftriple_2Fcollect_2Bmeta_2Bfailure_2Dfail == "err div0"
#guard errorObs case_sem2b_2Fv1_2Fsys_2Ftriple_2Fcollect_2Bmeta_2Bfailure_2Dfail == .matched (some { kind := "div0", names := [], counts := [] })

-- sem2b/v1/sys/triple/alias+cache+select: v1(v2) = v2 * 5 \n v3 = v1 \n v4 = v3 \n v5(v6) = v6 + v6 \n v7(v8) = v5(v8) \n v9 = 11, 12, 13 \n if(false, trace(666), v4(1)) \n v7(wait(2)) \n v9[trace(0), trace(2)] \n 997
def case_sem2b_2Fv1_2Fsys_2Ftriple_2Falias_2Bcache_2Bselect : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v3" (.alias none [] [] (.resolve "v1")), privateProp "v4" (.alias none [] [] (.resolve "v3")), privateProp "v9" (alg [] [] [] [.num 11, .num 12, .num 13]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (alg ["v2"] [] [] [(.binary .mul (.param "v2") (.num 5))]), privateProp "v5" (alg ["v6"] [] [] [(.binary .add (.param "v6") (.param "v6"))]), privateProp "v7" (alg ["v8"] [] [] [(.call (.resolve "v5") [.param "v8"])])] [(.call (.resolve "if") [.boolLiteral false, (.call (.resolve "trace") [.num 666]), (.call (.resolve "v4") [.num 1])]), (.call (.resolve "v7") [(.call (.resolve "wait") [.num 2])]), (.index (.resolve "v9") [(.call (.resolve "trace") [.num 0]), (.call (.resolve "trace") [.num 2])]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Ftriple_2Falias_2Bcache_2Bselect == "ok raw=S[5, 4, S[11, 13], 997] n=4"

-- sem2b/v1/sys/cancel/0: v1 = wait(1) \n v2 = wait(2) \n [v1, v1] \n [v2, v2()] \n 997
def case_sem2b_2Fv1_2Fsys_2Fcancel_2F0 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v1" (alg [] [] [] [(.call (.resolve "wait") [.num 1])]), privateProp "v2" (alg [] [] [] [(.call (.resolve "wait") [.num 2])]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"])] [(.listLiteral [.resolve "v1", .resolve "v1"]), (.listLiteral [.resolve "v2", (.call (.resolve "v2") [])]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fcancel_2F0 == "ok raw=S[L[1, 1], L[2, 2], 997] n=3"

-- sem2b/v1/sys/cancel/1: v1(meta v2) = v2 \n v3(v4) = v1(v4) \n v5(v6) = v6 \n v7 = v3(v5(trace(3))) \n [wait(1), wait(2)] \n [v7.Algorithm(4), v7.Algorithm(v7.Arguments*), v7.Arguments.count, v7.Arguments[0]] \n 997
def case_sem2b_2Fv1_2Fsys_2Fcancel_2F1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v7" (alg [] [] [] [(.call (.resolve "v3") [(.call (.resolve "v5") [(.call (.resolve "trace") [.num 3])])])]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (algWithParameters [{ name := "v2", kind := .metaRef }] [] [] [.param "v2"]), privateProp "v3" (alg ["v4"] [] [] [(.call (.resolve "v1") [.param "v4"])]), privateProp "v5" (alg ["v6"] [] [] [.param "v6"])] [(.listLiteral [(.call (.resolve "wait") [.num 1]), (.call (.resolve "wait") [.num 2])]), (.listLiteral [(.dotCall (.resolve "v7") "Algorithm" (some [.num 4])), (.dotCall (.resolve "v7") "Algorithm" (some [(.sequenceSpread (.dotCall (.resolve "v7") "Arguments" none))])), (.dotCall (.dotCall (.resolve "v7") "Arguments" none) "count" none), (.index (.dotCall (.resolve "v7") "Arguments" none) [.num 0])]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fcancel_2F1 == "ok raw=S[L[1, 2], L[4, 3, 1, 3], 997] n=3"

-- sem2b/v1/sys/guard/while-condition-first/0: v1(v2) = { \n   trace(666) / 0 \n   v2 < 0 \n } \n v1(0).while \n 997
def case_sem2b_2Fv1_2Fsys_2Fguard_2Fwhile_2Dcondition_2Dfirst_2F0 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (alg ["v2"] [] [] [(.binary .div (.call (.resolve "trace") [.num 666]) (.num 0)), (.comparison (.param "v2") [{ op := .lt, operand := (.num 0) }])])] [(.dotCall (.call (.resolve "v1") [.num 0]) "while" none), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fguard_2Fwhile_2Dcondition_2Dfirst_2F0 == "ok raw=S[0, 997] n=2"

-- sem2b/v1/sys/guard/nested-pattern/0: v1(([v2, *v3], v4)) = [v2, count(v3), v4] \n v1(([wait(1), wait(2), wait(3), wait(4)], trace(5))) \n 997
def case_sem2b_2Fv1_2Fsys_2Fguard_2Fnested_2Dpattern_2F0 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (algWithParameterPatterns [.sequenceValue [.listValue [.capture { name := "v2" }, .capture { name := "v3", kind := .collecting }], .capture { name := "v4" }]] [] [] [(.listLiteral [.param "v2", (.call (.resolve "count") [.param "v3"]), .param "v4"])])] [(.call (.resolve "v1") [(.capture [(.listLiteral [(.call (.resolve "wait") [.num 1]), (.call (.resolve "wait") [.num 2]), (.call (.resolve "wait") [.num 3]), (.call (.resolve "wait") [.num 4])]), (.call (.resolve "trace") [.num 5])])]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fguard_2Fnested_2Dpattern_2F0 == "ok raw=S[L[1, 3, 5], 997] n=2"

-- sem2b/v1/sys/guard/while-condition-first/1: v1(v2) = { \n   wait(v2 + 1) \n   v2 < 2 \n } \n v1(0).while \n 997
def case_sem2b_2Fv1_2Fsys_2Fguard_2Fwhile_2Dcondition_2Dfirst_2F1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (alg ["v2"] [] [] [(.call (.resolve "wait") [(.binary .add (.param "v2") (.num 1))]), (.comparison (.param "v2") [{ op := .lt, operand := (.num 2) }])])] [(.dotCall (.call (.resolve "v1") [.num 0]) "while" none), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fguard_2Fwhile_2Dcondition_2Dfirst_2F1 == "ok raw=S[2, 997] n=2"

-- sem2b/v1/sys/guard/nested-pattern/1: v1([(v2, *v3), v4]) = [v2, count(v3), v4] \n v1([(wait(1), wait(2)), trace(3)]) \n 997
def case_sem2b_2Fv1_2Fsys_2Fguard_2Fnested_2Dpattern_2F1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (algWithParameterPatterns [.listValue [.sequenceValue [.capture { name := "v2" }, .capture { name := "v3", kind := .collecting }], .capture { name := "v4" }]] [] [] [(.listLiteral [.param "v2", (.call (.resolve "count") [.param "v3"]), .param "v4"])])] [(.call (.resolve "v1") [(.listLiteral [(.capture [(.call (.resolve "wait") [.num 1]), (.call (.resolve "wait") [.num 2])]), (.call (.resolve "trace") [.num 3])])]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fguard_2Fnested_2Dpattern_2F1 == "ok raw=S[L[1, 1, 3], 997] n=2"

-- sem2b/v1/sys/guard/while-condition-first/2: v1(v2) = { \n   trace(666) / 0 \n   42 \n } \n v1(0).while \n 997
def case_sem2b_2Fv1_2Fsys_2Fguard_2Fwhile_2Dcondition_2Dfirst_2F2 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (alg ["v2"] [] [] [(.binary .div (.call (.resolve "trace") [.num 666]) (.num 0)), .num 42])] [(.dotCall (.call (.resolve "v1") [.num 0]) "while" none), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fguard_2Fwhile_2Dcondition_2Dfirst_2F2 == "err type"

-- sem2b/v1/sys/guard/nested-pattern/2: v1(([v2, *v3], v4)) = [v2, count(v3), v4] \n v1((99, trace(4))) \n 997
def case_sem2b_2Fv1_2Fsys_2Fguard_2Fnested_2Dpattern_2F2 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (algWithParameterPatterns [.sequenceValue [.listValue [.capture { name := "v2" }, .capture { name := "v3", kind := .collecting }], .capture { name := "v4" }]] [] [] [(.listLiteral [.param "v2", (.call (.resolve "count") [.param "v3"]), .param "v4"])])] [(.call (.resolve "v1") [(.capture [.num 99, (.call (.resolve "trace") [.num 4])])]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fguard_2Fnested_2Dpattern_2F2 == "err type"

-- sem2b/v1/sys/path/LoopShortCircuit/dot-bare: v1(v2) = v2 + 1 \n v1(1).repeat(0) \n 997
def case_sem2b_2Fv1_2Fsys_2Fpath_2FLoopShortCircuit_2Fdot_2Dbare : Expr :=
  .algorithmExpr (alg [] [] [privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (alg ["v2"] [] [] [(.binary .add (.param "v2") (.num 1))])] [(.dotCall (.call (.resolve "v1") [.num 1]) "repeat" (some [.num 0])), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fpath_2FLoopShortCircuit_2Fdot_2Dbare == "ok raw=S[1, 997] n=2"

-- sem2b/v1/sys/path/LoopShortCircuit/plain-bare: v1(v2) = v2 + 1 \n repeat(v1(1), 0) \n 997
def case_sem2b_2Fv1_2Fsys_2Fpath_2FLoopShortCircuit_2Fplain_2Dbare : Expr :=
  .algorithmExpr (alg [] [] [privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (alg ["v2"] [] [] [(.binary .add (.param "v2") (.num 1))])] [(.call (.resolve "repeat") [(.call (.resolve "v1") [.num 1]), .num 0]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fpath_2FLoopShortCircuit_2Fplain_2Dbare == "ok raw=S[1, 997] n=2"

-- sem2b/v1/sys/path/LoopShortCircuit/dot-list: v1(v2) = v2 + 1 \n [v1(1).repeat(0)] \n 997
def case_sem2b_2Fv1_2Fsys_2Fpath_2FLoopShortCircuit_2Fdot_2Dlist : Expr :=
  .algorithmExpr (alg [] [] [privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (alg ["v2"] [] [] [(.binary .add (.param "v2") (.num 1))])] [(.listLiteral [(.dotCall (.call (.resolve "v1") [.num 1]) "repeat" (some [.num 0]))]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fpath_2FLoopShortCircuit_2Fdot_2Dlist == "ok raw=S[L[1], 997] n=2"

-- sem2b/v1/sys/path/LoopShortCircuit/plain-property: v1(v2) = v2 + 1 \n v3 = repeat(v1(1), 0) \n v3 \n 997
def case_sem2b_2Fv1_2Fsys_2Fpath_2FLoopShortCircuit_2Fplain_2Dproperty : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v3" (alg [] [] [] [(.call (.resolve "repeat") [(.call (.resolve "v1") [.num 1]), .num 0])]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (alg ["v2"] [] [] [(.binary .add (.param "v2") (.num 1))])] [.resolve "v3", .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fpath_2FLoopShortCircuit_2Fplain_2Dproperty == "ok raw=S[1, 997] n=2"

-- sem2b/v1/sys/path/LoopShortCircuit/dot-wrapper: v1(v2) = v2 + 1 \n v3(v4) = v4 \n v3(v1(1).repeat(0)) \n 997
def case_sem2b_2Fv1_2Fsys_2Fpath_2FLoopShortCircuit_2Fdot_2Dwrapper : Expr :=
  .algorithmExpr (alg [] [] [privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (alg ["v2"] [] [] [(.binary .add (.param "v2") (.num 1))]), privateProp "v3" (alg ["v4"] [] [] [.param "v4"])] [(.call (.resolve "v3") [(.dotCall (.call (.resolve "v1") [.num 1]) "repeat" (some [.num 0]))]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fpath_2FLoopShortCircuit_2Fdot_2Dwrapper == "ok raw=S[1, 997] n=2"

-- sem2b/v1/sys/path/LoopShortCircuit/plain-if-true: v1(v2) = v2 + 1 \n if(true, repeat(v1(1), 0), trace(666)) \n 997
def case_sem2b_2Fv1_2Fsys_2Fpath_2FLoopShortCircuit_2Fplain_2Dif_2Dtrue : Expr :=
  .algorithmExpr (alg [] [] [privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (alg ["v2"] [] [] [(.binary .add (.param "v2") (.num 1))])] [(.call (.resolve "if") [.boolLiteral true, (.call (.resolve "repeat") [(.call (.resolve "v1") [.num 1]), .num 0]), (.call (.resolve "trace") [.num 666])]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fpath_2FLoopShortCircuit_2Fplain_2Dif_2Dtrue == "ok raw=S[1, 997] n=2"

-- sem2b/v1/sys/path/LoopShortCircuit/dot-brace: v1(v2) = v2 + 1 \n { \n   v3 = 0 \n   v1(1).repeat(0) \n } \n 997
def case_sem2b_2Fv1_2Fsys_2Fpath_2FLoopShortCircuit_2Fdot_2Dbrace : Expr :=
  .algorithmExpr (alg [] [] [privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (alg ["v2"] [] [] [(.binary .add (.param "v2") (.num 1))])] [(.algorithmExpr (alg [] [] [privateProp "v3" (alg [] [] [] [.num 0])] [(.dotCall (.call (.resolve "v1") [.num 1]) "repeat" (some [.num 0]))])), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fpath_2FLoopShortCircuit_2Fdot_2Dbrace == "ok raw=S[1, 997] n=2"

-- sem2b/v1/sys/path/LoopShortCircuit/plain-property-double: v1(v2) = v2 + 1 \n v3 = repeat(v1(1), 0) \n [v3, v3] \n 997
def case_sem2b_2Fv1_2Fsys_2Fpath_2FLoopShortCircuit_2Fplain_2Dproperty_2Ddouble : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v3" (alg [] [] [] [(.call (.resolve "repeat") [(.call (.resolve "v1") [.num 1]), .num 0])]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (alg ["v2"] [] [] [(.binary .add (.param "v2") (.num 1))])] [(.listLiteral [.resolve "v3", .resolve "v3"]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fpath_2FLoopShortCircuit_2Fplain_2Dproperty_2Ddouble == "ok raw=S[L[1, 1], 997] n=2"

-- sem2b/v1/sys/path/LoopShortCircuit/dot-then-cache: v1(v2) = v2 + 1 \n v3 = wait(2) \n v1(1).repeat(0) \n [v3(), v3] \n 997
def case_sem2b_2Fv1_2Fsys_2Fpath_2FLoopShortCircuit_2Fdot_2Dthen_2Dcache : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v3" (alg [] [] [] [(.call (.resolve "wait") [.num 2])]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (alg ["v2"] [] [] [(.binary .add (.param "v2") (.num 1))])] [(.dotCall (.call (.resolve "v1") [.num 1]) "repeat" (some [.num 0])), (.listLiteral [(.call (.resolve "v3") []), .resolve "v3"]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fpath_2FLoopShortCircuit_2Fdot_2Dthen_2Dcache == "ok raw=S[1, L[2, 2], 997] n=3"

-- sem2b/v1/sys/path/LoopShortCircuit/meta-then-plain-list: v1(meta v2) = v2 \n v3 = v1 \n v4(v5, v6, v7) = (v5 * 100) + (v6 * 10) + v7 \n v8 = v3(v4(trace(1), trace(2), trace(3))) \n v9(v10, v11, v12) = v12 \n v13(v14) = v14 + 1 \n [v8.Arguments.count, v8.Arguments[1], v8.Invoke(), v9(v8.Arguments*)] \n [repeat(v13(4), 0)] \n 997
def case_sem2b_2Fv1_2Fsys_2Fpath_2FLoopShortCircuit_2Fmeta_2Dthen_2Dplain_2Dlist : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v3" (.alias none [] [] (.resolve "v1")), privateProp "v8" (alg [] [] [] [(.call (.resolve "v3") [(.call (.resolve "v4") [(.call (.resolve "trace") [.num 1]), (.call (.resolve "trace") [.num 2]), (.call (.resolve "trace") [.num 3])])])]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (algWithParameters [{ name := "v2", kind := .metaRef }] [] [] [.param "v2"]), privateProp "v4" (alg ["v5", "v6", "v7"] [] [] [(.binary .add (.binary .add (.binary .mul (.param "v5") (.num 100)) (.binary .mul (.param "v6") (.num 10))) (.param "v7"))]), privateProp "v9" (alg ["v10", "v11", "v12"] [] [] [.param "v12"]), privateProp "v13" (alg ["v14"] [] [] [(.binary .add (.param "v14") (.num 1))])] [(.listLiteral [(.dotCall (.dotCall (.resolve "v8") "Arguments" none) "count" none), (.index (.dotCall (.resolve "v8") "Arguments" none) [.num 1]), (.dotCall (.resolve "v8") "Invoke" (some [])), (.call (.resolve "v9") [(.sequenceSpread (.dotCall (.resolve "v8") "Arguments" none))])]), (.listLiteral [(.call (.resolve "repeat") [(.call (.resolve "v13") [.num 4]), .num 0])]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fpath_2FLoopShortCircuit_2Fmeta_2Dthen_2Dplain_2Dlist == "ok raw=S[L[3, 2, 123, 3], L[4], 997] n=3"

-- sem2b/v1/sys/path/LoopShortCircuit/clause-family-step-dot: v1(0) = 100 \n v1(v2) = v2 + 1 \n v1(1).repeat(0) \n 997
def case_sem2b_2Fv1_2Fsys_2Fpath_2FLoopShortCircuit_2Fclause_2Dfamily_2Dstep_2Ddot : Expr :=
  .algorithmExpr (alg [] [] [privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (.conditional none [] [⟨.litInt 0, (alg [] [] [] [.num 100])⟩, ⟨.bind "v2", (alg [] [] [] [(.binary .add (.param "v2") (.num 1))])⟩])] [(.dotCall (.call (.resolve "v1") [.num 1]) "repeat" (some [.num 0])), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fpath_2FLoopShortCircuit_2Fclause_2Dfamily_2Dstep_2Ddot == "ok raw=S[1, 997] n=2"

-- sem2b/v1/sys/path/LoopShortCircuit/collecting-step-plain: v1(*v2) = v2[0] + 1 \n repeat(v1(1), 0) \n 997
def case_sem2b_2Fv1_2Fsys_2Fpath_2FLoopShortCircuit_2Fcollecting_2Dstep_2Dplain : Expr :=
  .algorithmExpr (alg [] [] [privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (algWithParameters [{ name := "v2", kind := .collecting }] [] [] [(.binary .add (.index (.param "v2") [.num 0]) (.num 1))])] [(.call (.resolve "repeat") [(.call (.resolve "v1") [.num 1]), .num 0]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fpath_2FLoopShortCircuit_2Fcollecting_2Dstep_2Dplain == "ok raw=S[1, 997] n=2"

-- sem2b/v1/sys/path/LoopShortCircuit/traced-step-dot-wrapper: v1(v2) = trace(v2) + 1 \n v3(v4) = v4 \n v3(v1(1).repeat(0)) \n 997
def case_sem2b_2Fv1_2Fsys_2Fpath_2FLoopShortCircuit_2Ftraced_2Dstep_2Ddot_2Dwrapper : Expr :=
  .algorithmExpr (alg [] [] [privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (alg ["v2"] [] [] [(.binary .add (.call (.resolve "trace") [.param "v2"]) (.num 1))]), privateProp "v3" (alg ["v4"] [] [] [.param "v4"])] [(.call (.resolve "v3") [(.dotCall (.call (.resolve "v1") [.num 1]) "repeat" (some [.num 0]))]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fpath_2FLoopShortCircuit_2Ftraced_2Dstep_2Ddot_2Dwrapper == "ok raw=S[1, 997] n=2"

-- sem2b/v1/sys/path/LoopFallback/clause-family-1-dot-bare: v1(0) = 100 \n v1(v2) = v2 + 1 \n v1(1).repeat(1) \n 997
def case_sem2b_2Fv1_2Fsys_2Fpath_2FLoopFallback_2Fclause_2Dfamily_2D1_2Ddot_2Dbare : Expr :=
  .algorithmExpr (alg [] [] [privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (.conditional none [] [⟨.litInt 0, (alg [] [] [] [.num 100])⟩, ⟨.bind "v2", (alg [] [] [] [(.binary .add (.param "v2") (.num 1))])⟩])] [(.dotCall (.call (.resolve "v1") [.num 1]) "repeat" (some [.num 1])), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fpath_2FLoopFallback_2Fclause_2Dfamily_2D1_2Ddot_2Dbare == "ok raw=S[2, 997] n=2"

-- sem2b/v1/sys/path/LoopFallback/clause-family-2-plain-bare: v1(0) = 100 \n v1(v2) = v2 + 1 \n repeat(v1(1), 2) \n 997
def case_sem2b_2Fv1_2Fsys_2Fpath_2FLoopFallback_2Fclause_2Dfamily_2D2_2Dplain_2Dbare : Expr :=
  .algorithmExpr (alg [] [] [privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (.conditional none [] [⟨.litInt 0, (alg [] [] [] [.num 100])⟩, ⟨.bind "v2", (alg [] [] [] [(.binary .add (.param "v2") (.num 1))])⟩])] [(.call (.resolve "repeat") [(.call (.resolve "v1") [.num 1]), .num 2]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fpath_2FLoopFallback_2Fclause_2Dfamily_2D2_2Dplain_2Dbare == "ok raw=S[3, 997] n=2"

-- sem2b/v1/sys/path/LoopFallback/clause-family-3-dot-list: v1(0) = 100 \n v1(v2) = v2 + 1 \n [v1(1).repeat(3)] \n 997
def case_sem2b_2Fv1_2Fsys_2Fpath_2FLoopFallback_2Fclause_2Dfamily_2D3_2Ddot_2Dlist : Expr :=
  .algorithmExpr (alg [] [] [privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (.conditional none [] [⟨.litInt 0, (alg [] [] [] [.num 100])⟩, ⟨.bind "v2", (alg [] [] [] [(.binary .add (.param "v2") (.num 1))])⟩])] [(.listLiteral [(.dotCall (.call (.resolve "v1") [.num 1]) "repeat" (some [.num 3]))]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fpath_2FLoopFallback_2Fclause_2Dfamily_2D3_2Ddot_2Dlist == "ok raw=S[L[4], 997] n=2"

-- sem2b/v1/sys/path/LoopFallback/clause-family-4-plain-property: v1(0) = 100 \n v1(v2) = v2 + 1 \n v3 = repeat(v1(1), 4) \n v3 \n 997
def case_sem2b_2Fv1_2Fsys_2Fpath_2FLoopFallback_2Fclause_2Dfamily_2D4_2Dplain_2Dproperty : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v3" (alg [] [] [] [(.call (.resolve "repeat") [(.call (.resolve "v1") [.num 1]), .num 4])]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (.conditional none [] [⟨.litInt 0, (alg [] [] [] [.num 100])⟩, ⟨.bind "v2", (alg [] [] [] [(.binary .add (.param "v2") (.num 1))])⟩])] [.resolve "v3", .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fpath_2FLoopFallback_2Fclause_2Dfamily_2D4_2Dplain_2Dproperty == "ok raw=S[5, 997] n=2"

-- sem2b/v1/sys/path/LoopFallback/collecting-1-plain-bare: v1(*v2) = v2[0] + 1 \n repeat(v1(1), 1) \n 997
def case_sem2b_2Fv1_2Fsys_2Fpath_2FLoopFallback_2Fcollecting_2D1_2Dplain_2Dbare : Expr :=
  .algorithmExpr (alg [] [] [privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (algWithParameters [{ name := "v2", kind := .collecting }] [] [] [(.binary .add (.index (.param "v2") [.num 0]) (.num 1))])] [(.call (.resolve "repeat") [(.call (.resolve "v1") [.num 1]), .num 1]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fpath_2FLoopFallback_2Fcollecting_2D1_2Dplain_2Dbare == "ok raw=S[2, 997] n=2"

-- sem2b/v1/sys/path/LoopFallback/collecting-2-dot-wrapper: v1(*v2) = v2[0] + 1 \n v3(v4) = v4 \n v3(v1(1).repeat(2)) \n 997
def case_sem2b_2Fv1_2Fsys_2Fpath_2FLoopFallback_2Fcollecting_2D2_2Ddot_2Dwrapper : Expr :=
  .algorithmExpr (alg [] [] [privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (algWithParameters [{ name := "v2", kind := .collecting }] [] [] [(.binary .add (.index (.param "v2") [.num 0]) (.num 1))]), privateProp "v3" (alg ["v4"] [] [] [.param "v4"])] [(.call (.resolve "v3") [(.dotCall (.call (.resolve "v1") [.num 1]) "repeat" (some [.num 2]))]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fpath_2FLoopFallback_2Fcollecting_2D2_2Ddot_2Dwrapper == "ok raw=S[3, 997] n=2"

-- sem2b/v1/sys/path/LoopFallback/collecting-3-plain-if-true: v1(*v2) = v2[0] + 1 \n if(true, repeat(v1(1), 3), trace(666)) \n 997
def case_sem2b_2Fv1_2Fsys_2Fpath_2FLoopFallback_2Fcollecting_2D3_2Dplain_2Dif_2Dtrue : Expr :=
  .algorithmExpr (alg [] [] [privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (algWithParameters [{ name := "v2", kind := .collecting }] [] [] [(.binary .add (.index (.param "v2") [.num 0]) (.num 1))])] [(.call (.resolve "if") [.boolLiteral true, (.call (.resolve "repeat") [(.call (.resolve "v1") [.num 1]), .num 3]), (.call (.resolve "trace") [.num 666])]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fpath_2FLoopFallback_2Fcollecting_2D3_2Dplain_2Dif_2Dtrue == "ok raw=S[4, 997] n=2"

-- sem2b/v1/sys/path/LoopFallback/collecting-4-dot-brace: v1(*v2) = v2[0] + 1 \n { \n   v3 = 0 \n   v1(1).repeat(4) \n } \n 997
def case_sem2b_2Fv1_2Fsys_2Fpath_2FLoopFallback_2Fcollecting_2D4_2Ddot_2Dbrace : Expr :=
  .algorithmExpr (alg [] [] [privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (algWithParameters [{ name := "v2", kind := .collecting }] [] [] [(.binary .add (.index (.param "v2") [.num 0]) (.num 1))])] [(.algorithmExpr (alg [] [] [privateProp "v3" (alg [] [] [] [.num 0])] [(.dotCall (.call (.resolve "v1") [.num 1]) "repeat" (some [.num 4]))])), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fpath_2FLoopFallback_2Fcollecting_2D4_2Ddot_2Dbrace == "ok raw=S[5, 997] n=2"

-- sem2b/v1/sys/path/LoopFallback/collecting-1-dot-property-double: v1(*v2) = v2[0] + 1 \n v3 = v1(1).repeat(1) \n [v3, v3] \n 997
def case_sem2b_2Fv1_2Fsys_2Fpath_2FLoopFallback_2Fcollecting_2D1_2Ddot_2Dproperty_2Ddouble : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v3" (alg [] [] [] [(.dotCall (.call (.resolve "v1") [.num 1]) "repeat" (some [.num 1]))]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (algWithParameters [{ name := "v2", kind := .collecting }] [] [] [(.binary .add (.index (.param "v2") [.num 0]) (.num 1))])] [(.listLiteral [.resolve "v3", .resolve "v3"]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fpath_2FLoopFallback_2Fcollecting_2D1_2Ddot_2Dproperty_2Ddouble == "ok raw=S[L[2, 2], 997] n=2"

-- sem2b/v1/sys/path/LoopFallback/clause-family-2-dot-then-meta: v1(0) = 100 \n v1(v2) = v2 + 1 \n v3(meta v4) = v4 \n v5(v6) = v3(v6) \n v7(v8) = trace(v8) \n v9 = v5(v7(trace(2))) \n v1(1).repeat(2) \n [v9.Arguments[0]] \n 997
def case_sem2b_2Fv1_2Fsys_2Fpath_2FLoopFallback_2Fclause_2Dfamily_2D2_2Ddot_2Dthen_2Dmeta : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v9" (alg [] [] [] [(.call (.resolve "v5") [(.call (.resolve "v7") [(.call (.resolve "trace") [.num 2])])])]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (.conditional none [] [⟨.litInt 0, (alg [] [] [] [.num 100])⟩, ⟨.bind "v2", (alg [] [] [] [(.binary .add (.param "v2") (.num 1))])⟩]), privateProp "v3" (algWithParameters [{ name := "v4", kind := .metaRef }] [] [] [.param "v4"]), privateProp "v5" (alg ["v6"] [] [] [(.call (.resolve "v3") [.param "v6"])]), privateProp "v7" (alg ["v8"] [] [] [(.call (.resolve "trace") [.param "v8"])])] [(.dotCall (.call (.resolve "v1") [.num 1]) "repeat" (some [.num 2])), (.listLiteral [(.index (.dotCall (.resolve "v9") "Arguments" none) [.num 0])]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fpath_2FLoopFallback_2Fclause_2Dfamily_2D2_2Ddot_2Dthen_2Dmeta == "ok raw=S[3, L[2], 997] n=3"

-- sem2b/v1/sys/path/LoopFallback/collect-then-collecting-3-plain: v1([v2, *v3]) = v2 + count(v3) \n v4(*v5) = v5[0] + 1 \n v1([1, 2]) \n repeat(v4(3), 3) \n 997
def case_sem2b_2Fv1_2Fsys_2Fpath_2FLoopFallback_2Fcollect_2Dthen_2Dcollecting_2D3_2Dplain : Expr :=
  .algorithmExpr (alg [] [] [privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (algWithParameterPatterns [.listValue [.capture { name := "v2" }, .capture { name := "v3", kind := .collecting }]] [] [] [(.binary .add (.param "v2") (.call (.resolve "count") [.param "v3"]))]), privateProp "v4" (algWithParameters [{ name := "v5", kind := .collecting }] [] [] [(.binary .add (.index (.param "v5") [.num 0]) (.num 1))])] [(.call (.resolve "v1") [(.listLiteral [.num 1, .num 2])]), (.call (.resolve "repeat") [(.call (.resolve "v4") [.num 3]), .num 3]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fpath_2FLoopFallback_2Fcollect_2Dthen_2Dcollecting_2D3_2Dplain == "ok raw=S[2, 6, 997] n=3"

-- sem2b/v1/sys/path/GenericInsideOptimizedLoop/trace-1-dot-bare: v1(v2) = trace(v2) + 1 \n v1(1).repeat(1) \n 997
def case_sem2b_2Fv1_2Fsys_2Fpath_2FGenericInsideOptimizedLoop_2Ftrace_2D1_2Ddot_2Dbare : Expr :=
  .algorithmExpr (alg [] [] [privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (alg ["v2"] [] [] [(.binary .add (.call (.resolve "trace") [.param "v2"]) (.num 1))])] [(.dotCall (.call (.resolve "v1") [.num 1]) "repeat" (some [.num 1])), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fpath_2FGenericInsideOptimizedLoop_2Ftrace_2D1_2Ddot_2Dbare == "ok raw=S[2, 997] n=2"

-- sem2b/v1/sys/path/GenericInsideOptimizedLoop/trace-2-plain-bare: v1(v2) = trace(v2) + 1 \n repeat(v1(1), 2) \n 997
def case_sem2b_2Fv1_2Fsys_2Fpath_2FGenericInsideOptimizedLoop_2Ftrace_2D2_2Dplain_2Dbare : Expr :=
  .algorithmExpr (alg [] [] [privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (alg ["v2"] [] [] [(.binary .add (.call (.resolve "trace") [.param "v2"]) (.num 1))])] [(.call (.resolve "repeat") [(.call (.resolve "v1") [.num 1]), .num 2]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fpath_2FGenericInsideOptimizedLoop_2Ftrace_2D2_2Dplain_2Dbare == "ok raw=S[3, 997] n=2"

-- sem2b/v1/sys/path/GenericInsideOptimizedLoop/trace-3-dot-list: v1(v2) = trace(v2) + 1 \n [v1(1).repeat(3)] \n 997
def case_sem2b_2Fv1_2Fsys_2Fpath_2FGenericInsideOptimizedLoop_2Ftrace_2D3_2Ddot_2Dlist : Expr :=
  .algorithmExpr (alg [] [] [privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (alg ["v2"] [] [] [(.binary .add (.call (.resolve "trace") [.param "v2"]) (.num 1))])] [(.listLiteral [(.dotCall (.call (.resolve "v1") [.num 1]) "repeat" (some [.num 3]))]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fpath_2FGenericInsideOptimizedLoop_2Ftrace_2D3_2Ddot_2Dlist == "ok raw=S[L[4], 997] n=2"

-- sem2b/v1/sys/path/GenericInsideOptimizedLoop/trace-4-plain-wrapper: v1(v2) = trace(v2) + 1 \n v3(v4) = v4 \n v3(repeat(v1(1), 4)) \n 997
def case_sem2b_2Fv1_2Fsys_2Fpath_2FGenericInsideOptimizedLoop_2Ftrace_2D4_2Dplain_2Dwrapper : Expr :=
  .algorithmExpr (alg [] [] [privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (alg ["v2"] [] [] [(.binary .add (.call (.resolve "trace") [.param "v2"]) (.num 1))]), privateProp "v3" (alg ["v4"] [] [] [.param "v4"])] [(.call (.resolve "v3") [(.call (.resolve "repeat") [(.call (.resolve "v1") [.num 1]), .num 4])]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fpath_2FGenericInsideOptimizedLoop_2Ftrace_2D4_2Dplain_2Dwrapper == "ok raw=S[5, 997] n=2"

-- sem2b/v1/sys/path/GenericInsideOptimizedLoop/wait-1-dot-bare: v1(v2) = wait(v2) + 1 \n v1(1).repeat(1) \n 997
def case_sem2b_2Fv1_2Fsys_2Fpath_2FGenericInsideOptimizedLoop_2Fwait_2D1_2Ddot_2Dbare : Expr :=
  .algorithmExpr (alg [] [] [privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (alg ["v2"] [] [] [(.binary .add (.call (.resolve "wait") [.param "v2"]) (.num 1))])] [(.dotCall (.call (.resolve "v1") [.num 1]) "repeat" (some [.num 1])), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fpath_2FGenericInsideOptimizedLoop_2Fwait_2D1_2Ddot_2Dbare == "ok raw=S[2, 997] n=2"

-- sem2b/v1/sys/path/GenericInsideOptimizedLoop/wait-2-plain-property: v1(v2) = wait(v2) + 1 \n v3 = repeat(v1(1), 2) \n v3 \n 997
def case_sem2b_2Fv1_2Fsys_2Fpath_2FGenericInsideOptimizedLoop_2Fwait_2D2_2Dplain_2Dproperty : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v3" (alg [] [] [] [(.call (.resolve "repeat") [(.call (.resolve "v1") [.num 1]), .num 2])]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (alg ["v2"] [] [] [(.binary .add (.call (.resolve "wait") [.param "v2"]) (.num 1))])] [.resolve "v3", .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fpath_2FGenericInsideOptimizedLoop_2Fwait_2D2_2Dplain_2Dproperty == "ok raw=S[3, 997] n=2"

-- sem2b/v1/sys/path/GenericInsideOptimizedLoop/wait-3-dot-if-true: v1(v2) = wait(v2) + 1 \n if(true, v1(1).repeat(3), trace(666)) \n 997
def case_sem2b_2Fv1_2Fsys_2Fpath_2FGenericInsideOptimizedLoop_2Fwait_2D3_2Ddot_2Dif_2Dtrue : Expr :=
  .algorithmExpr (alg [] [] [privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (alg ["v2"] [] [] [(.binary .add (.call (.resolve "wait") [.param "v2"]) (.num 1))])] [(.call (.resolve "if") [.boolLiteral true, (.dotCall (.call (.resolve "v1") [.num 1]) "repeat" (some [.num 3])), (.call (.resolve "trace") [.num 666])]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fpath_2FGenericInsideOptimizedLoop_2Fwait_2D3_2Ddot_2Dif_2Dtrue == "ok raw=S[4, 997] n=2"

-- sem2b/v1/sys/path/GenericInsideOptimizedLoop/wait-4-plain-brace: v1(v2) = wait(v2) + 1 \n { \n   v3 = 0 \n   repeat(v1(1), 4) \n } \n 997
def case_sem2b_2Fv1_2Fsys_2Fpath_2FGenericInsideOptimizedLoop_2Fwait_2D4_2Dplain_2Dbrace : Expr :=
  .algorithmExpr (alg [] [] [privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (alg ["v2"] [] [] [(.binary .add (.call (.resolve "wait") [.param "v2"]) (.num 1))])] [(.algorithmExpr (alg [] [] [privateProp "v3" (alg [] [] [] [.num 0])] [(.call (.resolve "repeat") [(.call (.resolve "v1") [.num 1]), .num 4])])), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fpath_2FGenericInsideOptimizedLoop_2Fwait_2D4_2Dplain_2Dbrace == "ok raw=S[5, 997] n=2"

-- sem2b/v1/sys/path/GenericInsideOptimizedLoop/trace-2-dot-then-collect: v1(v2) = trace(v2) + 1 \n v3(v4, *v5) = v4 \n v6 = () \n v1(1).repeat(2) \n v3(trace(2), trace(3), trace(4), trace(5), v6*) \n 997
def case_sem2b_2Fv1_2Fsys_2Fpath_2FGenericInsideOptimizedLoop_2Ftrace_2D2_2Ddot_2Dthen_2Dcollect : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v6" (alg [] [] [] [(.emptySequence 0)]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (alg ["v2"] [] [] [(.binary .add (.call (.resolve "trace") [.param "v2"]) (.num 1))]), privateProp "v3" (algWithParameters [{ name := "v4" }, { name := "v5", kind := .collecting }] [] [] [.param "v4"])] [(.dotCall (.call (.resolve "v1") [.num 1]) "repeat" (some [.num 2])), (.call (.resolve "v3") [(.call (.resolve "trace") [.num 2]), (.call (.resolve "trace") [.num 3]), (.call (.resolve "trace") [.num 4]), (.call (.resolve "trace") [.num 5]), (.sequenceSpread (.resolve "v6"))]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fpath_2FGenericInsideOptimizedLoop_2Ftrace_2D2_2Ddot_2Dthen_2Dcollect == "ok raw=S[3, 2, 997] n=3"

-- sem2b/v1/sys/path/GenericInsideOptimizedLoop/cache-then-wait-2-plain: v1 = trace(1) \n v2(v3) = wait(v3) + 1 \n [v1, v1] \n repeat(v2(2), 2) \n 997
def case_sem2b_2Fv1_2Fsys_2Fpath_2FGenericInsideOptimizedLoop_2Fcache_2Dthen_2Dwait_2D2_2Dplain : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v1" (alg [] [] [] [(.call (.resolve "trace") [.num 1])]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v2" (alg ["v3"] [] [] [(.binary .add (.call (.resolve "wait") [.param "v3"]) (.num 1))])] [(.listLiteral [.resolve "v1", .resolve "v1"]), (.call (.resolve "repeat") [(.call (.resolve "v2") [.num 2]), .num 2]), .num 997])
#guard obs case_sem2b_2Fv1_2Fsys_2Fpath_2FGenericInsideOptimizedLoop_2Fcache_2Dthen_2Dwait_2D2_2Dplain == "ok raw=S[L[1, 1], 4, 997] n=3"

-- sem2b/v1/seed/5EED2B000001/0: v1(v2) = v2 + v2 \n v3(v4) = v4 + 1 \n v5 = repeat(v3(2), 0) \n v6 = v5 \n [[[v1(trace(1)), v1(trace(1))]]] \n [v6, v6] \n 997
def case_sem2b_2Fv1_2Fseed_2F5EED2B000001_2F0 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v5" (alg [] [] [] [(.call (.resolve "repeat") [(.call (.resolve "v3") [.num 2]), .num 0])]), privateProp "v6" (.alias none [] [] (.resolve "v5")), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (alg ["v2"] [] [] [(.binary .add (.param "v2") (.param "v2"))]), privateProp "v3" (alg ["v4"] [] [] [(.binary .add (.param "v4") (.num 1))])] [(.listLiteral [(.listLiteral [(.listLiteral [(.call (.resolve "v1") [(.call (.resolve "trace") [.num 1])]), (.call (.resolve "v1") [(.call (.resolve "trace") [.num 1])])])])]), (.listLiteral [.resolve "v6", .resolve "v6"]), .num 997])
#guard obs case_sem2b_2Fv1_2Fseed_2F5EED2B000001_2F0 == "ok raw=S[L[L[L[2, 2]]], L[2, 2], 997] n=3"

-- sem2b/v1/seed/5EED2B000001/1: v1(meta v2) = v2 \n v3(v4, v5) = (v4 * 10) + v5 \n v6 = v1(v3(trace(1), trace(2))) \n v7 = v6.Algorithm \n v8(meta v9) = v9 \n v10(v11) = v8(v11) \n v12(v13, v14) = (v13 * 10) + v14 \n v15 = v10(v12(trace(5), wait(6))) \n v16(v17, v18) = v17 \n [[v7(3, 4)]] \n [v16(v15.Arguments*), v15.Algorithm(v15.Arguments*)] \n [wait(7), wait(8)] \n 997
def case_sem2b_2Fv1_2Fseed_2F5EED2B000001_2F1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v6" (alg [] [] [] [(.call (.resolve "v1") [(.call (.resolve "v3") [(.call (.resolve "trace") [.num 1]), (.call (.resolve "trace") [.num 2])])])]), privateProp "v7" (.alias none [] [] ((.dotCall (.resolve "v6") "Algorithm" none))), privateProp "v15" (alg [] [] [] [(.call (.resolve "v10") [(.call (.resolve "v12") [(.call (.resolve "trace") [.num 5]), (.call (.resolve "wait") [.num 6])])])]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (algWithParameters [{ name := "v2", kind := .metaRef }] [] [] [.param "v2"]), privateProp "v3" (alg ["v4", "v5"] [] [] [(.binary .add (.binary .mul (.param "v4") (.num 10)) (.param "v5"))]), privateProp "v8" (algWithParameters [{ name := "v9", kind := .metaRef }] [] [] [.param "v9"]), privateProp "v10" (alg ["v11"] [] [] [(.call (.resolve "v8") [.param "v11"])]), privateProp "v12" (alg ["v13", "v14"] [] [] [(.binary .add (.binary .mul (.param "v13") (.num 10)) (.param "v14"))]), privateProp "v16" (alg ["v17", "v18"] [] [] [.param "v17"])] [(.listLiteral [(.listLiteral [(.call (.resolve "v7") [.num 3, .num 4])])]), (.listLiteral [(.call (.resolve "v16") [(.sequenceSpread (.dotCall (.resolve "v15") "Arguments" none))]), (.dotCall (.resolve "v15") "Algorithm" (some [(.sequenceSpread (.dotCall (.resolve "v15") "Arguments" none))]))]), (.listLiteral [(.call (.resolve "wait") [.num 7]), (.call (.resolve "wait") [.num 8])]), .num 997])
#guard obs case_sem2b_2Fv1_2Fseed_2F5EED2B000001_2F1 == "ok raw=S[L[L[34]], L[5, 56], L[7, 8], 997] n=4"

-- sem2b/v1/seed/5EED2B000001/2: v1(*v2, v3) = v2[0] \n v4(*v5) = v1(v5*) \n v7(meta v8) = v8 \n v9(v10, v11) = (v10 * 10) + v11 \n v12 = v7(v9(trace(5), trace(6))) \n v13 = v12.Algorithm \n { \n   v6 = 0 \n   if(false, trace(666), v4(trace(2), trace(3), trace(4), trace(1))) \n } \n [v13(7, 8)] \n 997
def case_sem2b_2Fv1_2Fseed_2F5EED2B000001_2F2 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v12" (alg [] [] [] [(.call (.resolve "v7") [(.call (.resolve "v9") [(.call (.resolve "trace") [.num 5]), (.call (.resolve "trace") [.num 6])])])]), privateProp "v13" (.alias none [] [] ((.dotCall (.resolve "v12") "Algorithm" none))), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (algWithParameters [{ name := "v2", kind := .collecting }, { name := "v3" }] [] [] [(.index (.param "v2") [.num 0])]), privateProp "v4" (algWithParameters [{ name := "v5", kind := .collecting }] [] [] [(.call (.resolve "v1") [(.sequenceSpread (.param "v5"))])]), privateProp "v7" (algWithParameters [{ name := "v8", kind := .metaRef }] [] [] [.param "v8"]), privateProp "v9" (alg ["v10", "v11"] [] [] [(.binary .add (.binary .mul (.param "v10") (.num 10)) (.param "v11"))])] [(.algorithmExpr (alg [] [] [privateProp "v6" (alg [] [] [] [.num 0])] [(.call (.resolve "if") [.boolLiteral false, (.call (.resolve "trace") [.num 666]), (.call (.resolve "v4") [(.call (.resolve "trace") [.num 2]), (.call (.resolve "trace") [.num 3]), (.call (.resolve "trace") [.num 4]), (.call (.resolve "trace") [.num 1])])])])), (.listLiteral [(.call (.resolve "v13") [.num 7, .num 8])]), .num 997])
#guard obs case_sem2b_2Fv1_2Fseed_2F5EED2B000001_2F2 == "ok raw=S[2, L[78], 997] n=3"

-- sem2b/v1/seed/5EED2B000001/3: v1(meta v2) = v2.Algorithm(v2.Arguments*).repeat(3) \n v3(v4) = v4 + 1 \n v5 = trace(4) / 0 \n [wait(1), wait(2)] \n if(false, trace(666), [v1(v3(3))]) \n { \n   v6 = 0 \n   [v5, v5] \n } \n 997
def case_sem2b_2Fv1_2Fseed_2F5EED2B000001_2F3 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v5" (alg [] [] [] [(.binary .div (.call (.resolve "trace") [.num 4]) (.num 0))]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (algWithParameters [{ name := "v2", kind := .metaRef }] [] [] [(.dotCall (.dotCall (.param "v2") "Algorithm" (some [(.sequenceSpread (.dotCall (.param "v2") "Arguments" none))])) "repeat" (some [.num 3]))]), privateProp "v3" (alg ["v4"] [] [] [(.binary .add (.param "v4") (.num 1))])] [(.listLiteral [(.call (.resolve "wait") [.num 1]), (.call (.resolve "wait") [.num 2])]), (.call (.resolve "if") [.boolLiteral false, (.call (.resolve "trace") [.num 666]), (.listLiteral [(.call (.resolve "v1") [(.call (.resolve "v3") [.num 3])])])]), (.algorithmExpr (alg [] [] [privateProp "v6" (alg [] [] [] [.num 0])] [(.listLiteral [.resolve "v5", .resolve "v5"])])), .num 997])
#guard obs case_sem2b_2Fv1_2Fseed_2F5EED2B000001_2F3 == "err div0"
#guard errorObs case_sem2b_2Fv1_2Fseed_2F5EED2B000001_2F3 == .matched (some { kind := "div0", names := [], counts := [] })

-- sem2b/v1/seed/5EED2B000001/4: v1(meta v2) = v2 \n v3(v4, v5) = (v4 * 10) + v5 \n v6 = v1(v3(trace(1), trace(2))) \n v7 = v6.Algorithm \n [v7(3, 4), v7(v6.Arguments*)] \n 997
def case_sem2b_2Fv1_2Fseed_2F5EED2B000001_2F4 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v6" (alg [] [] [] [(.call (.resolve "v1") [(.call (.resolve "v3") [(.call (.resolve "trace") [.num 1]), (.call (.resolve "trace") [.num 2])])])]), privateProp "v7" (.alias none [] [] ((.dotCall (.resolve "v6") "Algorithm" none))), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (algWithParameters [{ name := "v2", kind := .metaRef }] [] [] [.param "v2"]), privateProp "v3" (alg ["v4", "v5"] [] [] [(.binary .add (.binary .mul (.param "v4") (.num 10)) (.param "v5"))])] [(.listLiteral [(.call (.resolve "v7") [.num 3, .num 4]), (.call (.resolve "v7") [(.sequenceSpread (.dotCall (.resolve "v6") "Arguments" none))])]), .num 997])
#guard obs case_sem2b_2Fv1_2Fseed_2F5EED2B000001_2F4 == "ok raw=S[L[34, 12], 997] n=2"

-- sem2b/v1/seed/5EED2B000001/5: v1([v2, *v3]) = v2 + count(v3) \n v4(v5) = v5 \n v6(v7, v8) = v7 \n v9 = wait(3) / 0 \n v10(v11) = v11 \n v12(v13) = v13 \n [v4(v1([1]))] \n v6(trace(2), trace(666) / 0) \n v12(v10([v9, v9])) \n 997
def case_sem2b_2Fv1_2Fseed_2F5EED2B000001_2F5 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v9" (alg [] [] [] [(.binary .div (.call (.resolve "wait") [.num 3]) (.num 0))]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (algWithParameterPatterns [.listValue [.capture { name := "v2" }, .capture { name := "v3", kind := .collecting }]] [] [] [(.binary .add (.param "v2") (.call (.resolve "count") [.param "v3"]))]), privateProp "v4" (alg ["v5"] [] [] [.param "v5"]), privateProp "v6" (alg ["v7", "v8"] [] [] [.param "v7"]), privateProp "v10" (alg ["v11"] [] [] [.param "v11"]), privateProp "v12" (alg ["v13"] [] [] [.param "v13"])] [(.listLiteral [(.call (.resolve "v4") [(.call (.resolve "v1") [(.listLiteral [.num 1])])])]), (.call (.resolve "v6") [(.call (.resolve "trace") [.num 2]), (.binary .div (.call (.resolve "trace") [.num 666]) (.num 0))]), (.call (.resolve "v12") [(.call (.resolve "v10") [(.listLiteral [.resolve "v9", .resolve "v9"])])]), .num 997])
#guard obs case_sem2b_2Fv1_2Fseed_2F5EED2B000001_2F5 == "err div0"
#guard errorObs case_sem2b_2Fv1_2Fseed_2F5EED2B000001_2F5 == .matched (some { kind := "div0", names := [], counts := [] })

-- sem2b/v1/seed/5EED2B000001/6: v1(*v2) = v2[0] \n v3((v4, *v5)) = (count(v5) * 10) + v4 \n v6(v7) = { \n   v8 = trace(v7) \n   v8 + v8 \n } \n v1(trace(1), trace(2), trace(3)) \n if(false, trace(666), v3(11)) \n [v6(4), v6(4)] \n 997
def case_sem2b_2Fv1_2Fseed_2F5EED2B000001_2F6 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (algWithParameters [{ name := "v2", kind := .collecting }] [] [] [(.index (.param "v2") [.num 0])]), privateProp "v3" (algWithParameterPatterns [.sequenceValue [.capture { name := "v4" }, .capture { name := "v5", kind := .collecting }]] [] [] [(.binary .add (.binary .mul (.call (.resolve "count") [.param "v5"]) (.num 10)) (.param "v4"))]), privateProp "v6" (alg ["v7"] [] [{ (privateLocalProp "v8" (.localCapturedAncestorParams ["v7"]) (alg [] [] [] [(.call (.resolve "trace") [.param "v7"])])) with requiredOwnerDepths := some [("v7", some 0)] }] [(.binary .add (.resolve "v8") (.resolve "v8"))])] [(.call (.resolve "v1") [(.call (.resolve "trace") [.num 1]), (.call (.resolve "trace") [.num 2]), (.call (.resolve "trace") [.num 3])]), (.call (.resolve "if") [.boolLiteral false, (.call (.resolve "trace") [.num 666]), (.call (.resolve "v3") [.num 11])]), (.listLiteral [(.call (.resolve "v6") [.num 4]), (.call (.resolve "v6") [.num 4])]), .num 997])
#guard obs case_sem2b_2Fv1_2Fseed_2F5EED2B000001_2F6 == "err type"

-- sem2b/v1/seed/5EED2B000001/7: v1(v2) = { \n   v2 + 1 \n   v2 < 0 \n } \n if(false, trace(666), v1(0).while) \n 997
def case_sem2b_2Fv1_2Fseed_2F5EED2B000001_2F7 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (alg ["v2"] [] [] [(.binary .add (.param "v2") (.num 1)), (.comparison (.param "v2") [{ op := .lt, operand := (.num 0) }])])] [(.call (.resolve "if") [.boolLiteral false, (.call (.resolve "trace") [.num 666]), (.dotCall (.call (.resolve "v1") [.num 0]) "while" none)]), .num 997])
#guard obs case_sem2b_2Fv1_2Fseed_2F5EED2B000001_2F7 == "ok raw=S[0, 997] n=2"

-- sem2b/v1/seed/5EED2B000001/8: v1(meta v2) = v2 \n v3(v4) = v1(v4) \n v5(v6, v7, v8) = trace((v6 * 100) + (v7 * 10) + v8) \n v9 = v3(v5(trace(1), wait(2), wait(3))) \n v10 = [v9.Algorithm(4, 5, 6)] \n v12((v13, *v14)) = (count(v14) * 10) + v13 \n v15 = 7, 8, 9 \n v16 = if(false, trace(666), v12(v15)) \n v17(v18) = { \n   v18 + 1 \n   v18 < 3 \n } \n { \n   v11 = 0 \n   [v10, v10] \n } \n [v16, v16] \n v17(0).while \n 997
def case_sem2b_2Fv1_2Fseed_2F5EED2B000001_2F8 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v9" (alg [] [] [] [(.call (.resolve "v3") [(.call (.resolve "v5") [(.call (.resolve "trace") [.num 1]), (.call (.resolve "wait") [.num 2]), (.call (.resolve "wait") [.num 3])])])]), privateProp "v10" (alg [] [] [] [(.listLiteral [(.dotCall (.resolve "v9") "Algorithm" (some [.num 4, .num 5, .num 6]))])]), privateProp "v15" (alg [] [] [] [.num 7, .num 8, .num 9]), privateProp "v16" (alg [] [] [] [(.call (.resolve "if") [.boolLiteral false, (.call (.resolve "trace") [.num 666]), (.call (.resolve "v12") [.resolve "v15"])])]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (algWithParameters [{ name := "v2", kind := .metaRef }] [] [] [.param "v2"]), privateProp "v3" (alg ["v4"] [] [] [(.call (.resolve "v1") [.param "v4"])]), privateProp "v5" (alg ["v6", "v7", "v8"] [] [] [(.call (.resolve "trace") [(.binary .add (.binary .add (.binary .mul (.param "v6") (.num 100)) (.binary .mul (.param "v7") (.num 10))) (.param "v8"))])]), privateProp "v12" (algWithParameterPatterns [.sequenceValue [.capture { name := "v13" }, .capture { name := "v14", kind := .collecting }]] [] [] [(.binary .add (.binary .mul (.call (.resolve "count") [.param "v14"]) (.num 10)) (.param "v13"))]), privateProp "v17" (alg ["v18"] [] [] [(.binary .add (.param "v18") (.num 1)), (.comparison (.param "v18") [{ op := .lt, operand := (.num 3) }])])] [(.algorithmExpr (alg [] [] [privateProp "v11" (alg [] [] [] [.num 0])] [(.listLiteral [.resolve "v10", .resolve "v10"])])), (.listLiteral [.resolve "v16", .resolve "v16"]), (.dotCall (.call (.resolve "v17") [.num 0]) "while" none), .num 997])
#guard obs case_sem2b_2Fv1_2Fseed_2F5EED2B000001_2F8 == "ok raw=S[L[L[456], L[456]], L[27, 27], 3, 997] n=4"

-- sem2b/v1/seed/5EED2B000001/9: v1(meta v2) = v2 \n v3(v4, v5) = (v4 * 10) + v5 \n v6 = v1(v3(trace(1), trace(2))) \n v7 = v6.Algorithm \n v8 = [v7(3, 4)] \n v9(meta v10) = v10 \n v11(v12, v13, v14) = trace((v12 * 100) + (v13 * 10) + v14) \n v15 = v9(v11(wait(5), trace(6), trace(7))) \n v16(v17, v18, v19) = v17 \n v20 = [v16(v15.Arguments*), v15.Invoke(), v15.Algorithm(v15.Arguments*), v15.Algorithm(v15.Arguments*)] \n v21 = trace(8) \n v8 \n [v20, v20] \n if(true, [[v21, v21]], trace(666)) \n 997
def case_sem2b_2Fv1_2Fseed_2F5EED2B000001_2F9 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v6" (alg [] [] [] [(.call (.resolve "v1") [(.call (.resolve "v3") [(.call (.resolve "trace") [.num 1]), (.call (.resolve "trace") [.num 2])])])]), privateProp "v7" (.alias none [] [] ((.dotCall (.resolve "v6") "Algorithm" none))), privateProp "v8" (alg [] [] [] [(.listLiteral [(.call (.resolve "v7") [.num 3, .num 4])])]), privateProp "v15" (alg [] [] [] [(.call (.resolve "v9") [(.call (.resolve "v11") [(.call (.resolve "wait") [.num 5]), (.call (.resolve "trace") [.num 6]), (.call (.resolve "trace") [.num 7])])])]), privateProp "v20" (alg [] [] [] [(.listLiteral [(.call (.resolve "v16") [(.sequenceSpread (.dotCall (.resolve "v15") "Arguments" none))]), (.dotCall (.resolve "v15") "Invoke" (some [])), (.dotCall (.resolve "v15") "Algorithm" (some [(.sequenceSpread (.dotCall (.resolve "v15") "Arguments" none))])), (.dotCall (.resolve "v15") "Algorithm" (some [(.sequenceSpread (.dotCall (.resolve "v15") "Arguments" none))]))])]), privateProp "v21" (alg [] [] [] [(.call (.resolve "trace") [.num 8])]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (algWithParameters [{ name := "v2", kind := .metaRef }] [] [] [.param "v2"]), privateProp "v3" (alg ["v4", "v5"] [] [] [(.binary .add (.binary .mul (.param "v4") (.num 10)) (.param "v5"))]), privateProp "v9" (algWithParameters [{ name := "v10", kind := .metaRef }] [] [] [.param "v10"]), privateProp "v11" (alg ["v12", "v13", "v14"] [] [] [(.call (.resolve "trace") [(.binary .add (.binary .add (.binary .mul (.param "v12") (.num 100)) (.binary .mul (.param "v13") (.num 10))) (.param "v14"))])]), privateProp "v16" (alg ["v17", "v18", "v19"] [] [] [.param "v17"])] [.resolve "v8", (.listLiteral [.resolve "v20", .resolve "v20"]), (.call (.resolve "if") [.boolLiteral true, (.listLiteral [(.listLiteral [.resolve "v21", .resolve "v21"])]), (.call (.resolve "trace") [.num 666])]), .num 997])
#guard obs case_sem2b_2Fv1_2Fseed_2F5EED2B000001_2F9 == "ok raw=S[L[34], L[L[5, 567, 567, 567], L[5, 567, 567, 567]], L[L[8, 8]], 997] n=4"

-- sem2b/v1/seed/5EED2B000001/10: v1 = wait(1) \n [{ \n   v2 = 0 \n   [v1(), v1()] \n }] \n 997
def case_sem2b_2Fv1_2Fseed_2F5EED2B000001_2F10 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v1" (alg [] [] [] [(.call (.resolve "wait") [.num 1])]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"])] [(.listLiteral [(.algorithmExpr (alg [] [] [privateProp "v2" (alg [] [] [] [.num 0])] [(.listLiteral [(.call (.resolve "v1") []), (.call (.resolve "v1") [])])]))]), .num 997])
#guard obs case_sem2b_2Fv1_2Fseed_2F5EED2B000001_2F10 == "ok raw=S[L[L[1, 1]], 997] n=2"

-- sem2b/v1/seed/5EED2B000001/11: v1 = 11, 12, 13 \n [v1[trace(1), trace(1)]] \n 997
def case_sem2b_2Fv1_2Fseed_2F5EED2B000001_2F11 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v1" (alg [] [] [] [.num 11, .num 12, .num 13]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"])] [(.listLiteral [(.index (.resolve "v1") [(.call (.resolve "trace") [.num 1]), (.call (.resolve "trace") [.num 1])])]), .num 997])
#guard obs case_sem2b_2Fv1_2Fseed_2F5EED2B000001_2F11 == "ok raw=S[L[S[12, 12]], 997] n=2"

-- sem2b/v1/seed/5EED2B000001/13: v1(v2, v3) = v2 \n v4 = v1(trace(1), trace(666) / 0) \n v5(v6) = v6 + 1 \n if(true, [v4, v4], trace(666)) \n if(true, 2, trace(666) / 0) \n { \n   v7 = 0 \n   repeat(v5(3), 0) \n } \n 997
def case_sem2b_2Fv1_2Fseed_2F5EED2B000001_2F13 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v4" (alg [] [] [] [(.call (.resolve "v1") [(.call (.resolve "trace") [.num 1]), (.binary .div (.call (.resolve "trace") [.num 666]) (.num 0))])]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (alg ["v2", "v3"] [] [] [.param "v2"]), privateProp "v5" (alg ["v6"] [] [] [(.binary .add (.param "v6") (.num 1))])] [(.call (.resolve "if") [.boolLiteral true, (.listLiteral [.resolve "v4", .resolve "v4"]), (.call (.resolve "trace") [.num 666])]), (.call (.resolve "if") [.boolLiteral true, .num 2, (.binary .div (.call (.resolve "trace") [.num 666]) (.num 0))]), (.algorithmExpr (alg [] [] [privateProp "v7" (alg [] [] [] [.num 0])] [(.call (.resolve "repeat") [(.call (.resolve "v5") [.num 3]), .num 0])])), .num 997])
#guard obs case_sem2b_2Fv1_2Fseed_2F5EED2B000001_2F13 == "ok raw=S[L[1, 1], 2, 3, 997] n=4"

-- sem2b/v1/seed/5EED2B000001/15: v1(meta v2) = v2 \n v3(v4, v5) = (v4 * 10) + v5 \n v6 = v1(v3(wait(1), wait(2))) \n v8(v9, v10) = v9 + v10 \n [v6.Arguments[1], v6.Invoke()] \n if(false, trace(666), { \n   v11 = 0 \n   v8([11, 12, 13][0, 1]*) \n }) \n 997
def case_sem2b_2Fv1_2Fseed_2F5EED2B000001_2F15 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v6" (alg [] [] [] [(.call (.resolve "v1") [(.call (.resolve "v3") [(.call (.resolve "wait") [.num 1]), (.call (.resolve "wait") [.num 2])])])]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (algWithParameters [{ name := "v2", kind := .metaRef }] [] [] [.param "v2"]), privateProp "v3" (alg ["v4", "v5"] [] [] [(.binary .add (.binary .mul (.param "v4") (.num 10)) (.param "v5"))]), privateProp "v8" (alg ["v9", "v10"] [] [] [(.binary .add (.param "v9") (.param "v10"))])] [(.listLiteral [(.index (.dotCall (.resolve "v6") "Arguments" none) [.num 1]), (.dotCall (.resolve "v6") "Invoke" (some []))]), (.call (.resolve "if") [.boolLiteral false, (.call (.resolve "trace") [.num 666]), (.algorithmExpr (alg [] [] [privateProp "v11" (alg [] [] [] [.num 0])] [(.call (.resolve "v8") [(.sequenceSpread (.index (.listLiteral [.num 11, .num 12, .num 13]) [.num 0, .num 1]))])]))]), .num 997])
#guard obs case_sem2b_2Fv1_2Fseed_2F5EED2B000001_2F15 == "ok raw=S[L[2, 12], 23, 997] n=3"

-- sem2b/v1/seed/5EED2B000002/0: v1 = 11, 12, 13 \n v2(v3, v4) = v3 + v4 \n v5(v6) = v6 \n v7(v8) = v8 + v8 \n v9(v10) = v7(v10) \n v11(v12) = v12 \n v5(if(true, v2(v1[0, 2]*), trace(666))) \n v11([v9(trace(1))]) \n 997
def case_sem2b_2Fv1_2Fseed_2F5EED2B000002_2F0 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v1" (alg [] [] [] [.num 11, .num 12, .num 13]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v2" (alg ["v3", "v4"] [] [] [(.binary .add (.param "v3") (.param "v4"))]), privateProp "v5" (alg ["v6"] [] [] [.param "v6"]), privateProp "v7" (alg ["v8"] [] [] [(.binary .add (.param "v8") (.param "v8"))]), privateProp "v9" (alg ["v10"] [] [] [(.call (.resolve "v7") [.param "v10"])]), privateProp "v11" (alg ["v12"] [] [] [.param "v12"])] [(.call (.resolve "v5") [(.call (.resolve "if") [.boolLiteral true, (.call (.resolve "v2") [(.sequenceSpread (.index (.resolve "v1") [.num 0, .num 2]))]), (.call (.resolve "trace") [.num 666])])]), (.call (.resolve "v11") [(.listLiteral [(.call (.resolve "v9") [(.call (.resolve "trace") [.num 1])])])]), .num 997])
#guard obs case_sem2b_2Fv1_2Fseed_2F5EED2B000002_2F0 == "ok raw=S[24, L[2], 997] n=3"

-- sem2b/v1/seed/5EED2B000002/1: v2 = [[11, 12, 13][]] \n v3(v4, *v5) = v4 \n v6 = () \n v7(v8) = v8 \n [v2, v2] \n v7(v3(trace(1), trace(2), trace(3), v6*)) \n 997
def case_sem2b_2Fv1_2Fseed_2F5EED2B000002_2F1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v2" (alg [] [] [] [(.listLiteral [(.index (.listLiteral [.num 11, .num 12, .num 13]) [])])]), privateProp "v6" (alg [] [] [] [(.emptySequence 0)]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v3" (algWithParameters [{ name := "v4" }, { name := "v5", kind := .collecting }] [] [] [.param "v4"]), privateProp "v7" (alg ["v8"] [] [] [.param "v8"])] [(.listLiteral [.resolve "v2", .resolve "v2"]), (.call (.resolve "v7") [(.call (.resolve "v3") [(.call (.resolve "trace") [.num 1]), (.call (.resolve "trace") [.num 2]), (.call (.resolve "trace") [.num 3]), (.sequenceSpread (.resolve "v6"))])]), .num 997])
#guard obs case_sem2b_2Fv1_2Fseed_2F5EED2B000002_2F1 == "ok raw=S[L[L[S[]], L[S[]]], 1, 997] n=3"

-- sem2b/v1/seed/5EED2B000002/2: v1(meta v2) = v2 \n v3(v4, v5) = (v4 * 10) + v5 \n v6 = v1(v3(wait(1), wait(2))) \n v7(v8, v9) = v9 + v8 \n v11 = { \n   v10 = 0 \n   v7(trace(3) / 0, [trace(4)][5]) \n } \n v12(v13) = v13 + v13 \n v14(v15) = v15 \n [v6.Arguments[1], v6.Invoke()] \n [v11, v11] \n v14(v12(trace(5))) \n 997
def case_sem2b_2Fv1_2Fseed_2F5EED2B000002_2F2 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v6" (alg [] [] [] [(.call (.resolve "v1") [(.call (.resolve "v3") [(.call (.resolve "wait") [.num 1]), (.call (.resolve "wait") [.num 2])])])]), privateProp "v11" (alg [] [] [privateProp "v10" (alg [] [] [] [.num 0])] [(.call (.resolve "v7") [(.binary .div (.call (.resolve "trace") [.num 3]) (.num 0)), (.index (.listLiteral [(.call (.resolve "trace") [.num 4])]) [.num 5])])]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (algWithParameters [{ name := "v2", kind := .metaRef }] [] [] [.param "v2"]), privateProp "v3" (alg ["v4", "v5"] [] [] [(.binary .add (.binary .mul (.param "v4") (.num 10)) (.param "v5"))]), privateProp "v7" (alg ["v8", "v9"] [] [] [(.binary .add (.param "v9") (.param "v8"))]), privateProp "v12" (alg ["v13"] [] [] [(.binary .add (.param "v13") (.param "v13"))]), privateProp "v14" (alg ["v15"] [] [] [.param "v15"])] [(.listLiteral [(.index (.dotCall (.resolve "v6") "Arguments" none) [.num 1]), (.dotCall (.resolve "v6") "Invoke" (some []))]), (.listLiteral [.resolve "v11", .resolve "v11"]), (.call (.resolve "v14") [(.call (.resolve "v12") [(.call (.resolve "trace") [.num 5])])]), .num 997])
#guard obs case_sem2b_2Fv1_2Fseed_2F5EED2B000002_2F2 == "err index"
#guard errorObs case_sem2b_2Fv1_2Fseed_2F5EED2B000002_2F2 == .matched (some { kind := "index", names := [], counts := [] })

-- sem2b/v1/seed/5EED2B000002/3: v1 = trace(1) \n v3 = wait(2) \n if(true, [v1(), v1()], trace(666)) \n [11, 12, 13][trace(2), trace(2)] \n if(false, trace(666), if(false, trace(666), [v3, v3])) \n 997
def case_sem2b_2Fv1_2Fseed_2F5EED2B000002_2F3 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v1" (alg [] [] [] [(.call (.resolve "trace") [.num 1])]), privateProp "v3" (alg [] [] [] [(.call (.resolve "wait") [.num 2])]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"])] [(.call (.resolve "if") [.boolLiteral true, (.listLiteral [(.call (.resolve "v1") []), (.call (.resolve "v1") [])]), (.call (.resolve "trace") [.num 666])]), (.index (.listLiteral [.num 11, .num 12, .num 13]) [(.call (.resolve "trace") [.num 2]), (.call (.resolve "trace") [.num 2])]), (.call (.resolve "if") [.boolLiteral false, (.call (.resolve "trace") [.num 666]), (.call (.resolve "if") [.boolLiteral false, (.call (.resolve "trace") [.num 666]), (.listLiteral [.resolve "v3", .resolve "v3"])])]), .num 997])
#guard obs case_sem2b_2Fv1_2Fseed_2F5EED2B000002_2F3 == "ok raw=S[L[1, 1], S[13, 13], L[2, 2], 997] n=4"

-- sem2b/v1/seed/5EED2B000002/4: v1(v2) = { \n   v3(v4) = v4 + v2 \n   v3(1) \n } \n v5 = wait(2) \n v6(meta v7) = v7 \n v8(v9, v10) = trace((v9 * 10) + v10) \n v11 = v6(v8(trace(3), trace(4))) \n v12 = [v11.Invoke()] \n v13 = [v12, v12] \n if(false, trace(666), [v1(11), v1(12)]) \n [[v5, v5]] \n [v13, v13] \n 997
def case_sem2b_2Fv1_2Fseed_2F5EED2B000002_2F4 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v5" (alg [] [] [] [(.call (.resolve "wait") [.num 2])]), privateProp "v11" (alg [] [] [] [(.call (.resolve "v6") [(.call (.resolve "v8") [(.call (.resolve "trace") [.num 3]), (.call (.resolve "trace") [.num 4])])])]), privateProp "v12" (alg [] [] [] [(.listLiteral [(.dotCall (.resolve "v11") "Invoke" (some []))])]), privateProp "v13" (alg [] [] [] [(.listLiteral [.resolve "v12", .resolve "v12"])]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (alg ["v2"] [] [{ (privateLocalProp "v3" (.localCapturedAncestorParams ["v2"]) (alg ["v4"] [] [] [(.binary .add (.param "v4") (.param "v2"))])) with requiredOwnerDepths := some [("v2", some 0)] }] [(.call (.resolve "v3") [.num 1])]), privateProp "v6" (algWithParameters [{ name := "v7", kind := .metaRef }] [] [] [.param "v7"]), privateProp "v8" (alg ["v9", "v10"] [] [] [(.call (.resolve "trace") [(.binary .add (.binary .mul (.param "v9") (.num 10)) (.param "v10"))])])] [(.call (.resolve "if") [.boolLiteral false, (.call (.resolve "trace") [.num 666]), (.listLiteral [(.call (.resolve "v1") [.num 11]), (.call (.resolve "v1") [.num 12])])]), (.listLiteral [(.listLiteral [.resolve "v5", .resolve "v5"])]), (.listLiteral [.resolve "v13", .resolve "v13"]), .num 997])
#guard obs case_sem2b_2Fv1_2Fseed_2F5EED2B000002_2F4 == "ok raw=S[L[12, 13], L[L[2, 2]], L[L[L[34], L[34]], L[L[34], L[34]]], 997] n=4"

-- sem2b/v1/seed/5EED2B000002/5: v1(meta v2) = v2 \n v3 = v1 \n v4(v5, v6, v7) = (v5 * 100) + (v6 * 10) + v7 \n v8 = v3(v4(trace(1), wait(2), trace(3))) \n v9(v10, v11, v12) = v11 \n [v8.Algorithm(v8.Arguments*), v9(v8.Arguments*)] \n 997
def case_sem2b_2Fv1_2Fseed_2F5EED2B000002_2F5 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v3" (.alias none [] [] (.resolve "v1")), privateProp "v8" (alg [] [] [] [(.call (.resolve "v3") [(.call (.resolve "v4") [(.call (.resolve "trace") [.num 1]), (.call (.resolve "wait") [.num 2]), (.call (.resolve "trace") [.num 3])])])]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (algWithParameters [{ name := "v2", kind := .metaRef }] [] [] [.param "v2"]), privateProp "v4" (alg ["v5", "v6", "v7"] [] [] [(.binary .add (.binary .add (.binary .mul (.param "v5") (.num 100)) (.binary .mul (.param "v6") (.num 10))) (.param "v7"))]), privateProp "v9" (alg ["v10", "v11", "v12"] [] [] [.param "v11"])] [(.listLiteral [(.dotCall (.resolve "v8") "Algorithm" (some [(.sequenceSpread (.dotCall (.resolve "v8") "Arguments" none))])), (.call (.resolve "v9") [(.sequenceSpread (.dotCall (.resolve "v8") "Arguments" none))])]), .num 997])
#guard obs case_sem2b_2Fv1_2Fseed_2F5EED2B000002_2F5 == "ok raw=S[L[123, 2], 997] n=2"

-- sem2b/v1/seed/5EED2B000002/6: v1 = wait(1) \n v2 = [wait(2), 1 / 0, wait(3)] \n [v1(), v1()] \n v2 \n 997
def case_sem2b_2Fv1_2Fseed_2F5EED2B000002_2F6 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v1" (alg [] [] [] [(.call (.resolve "wait") [.num 1])]), privateProp "v2" (alg [] [] [] [(.listLiteral [(.call (.resolve "wait") [.num 2]), (.binary .div (.num 1) (.num 0)), (.call (.resolve "wait") [.num 3])])]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"])] [(.listLiteral [(.call (.resolve "v1") []), (.call (.resolve "v1") [])]), .resolve "v2", .num 997])
#guard obs case_sem2b_2Fv1_2Fseed_2F5EED2B000002_2F6 == "err div0"
#guard errorObs case_sem2b_2Fv1_2Fseed_2F5EED2B000002_2F6 == .matched (some { kind := "div0", names := [], counts := [] })

-- sem2b/v1/seed/5EED2B000002/8: v1(meta v2) = v2 \n v3 = v1 \n v4(v5, v6, v7) = (v5 * 100) + (v6 * 10) + v7 \n v8 = v3(v4(trace(1), trace(2), trace(3))) \n v9(v10, v11, v12) = v12 \n v14 = 11, 12, 13 \n v15(v16, v17) = v16 + v17 \n v18(meta v19) = v19.Algorithm(v19.Arguments*).repeat(1) \n v20(v21) = v21 + 1 \n v22 = [v18(v20(4))] \n { \n   v13 = 0 \n   [[v9(v8.Arguments*), v8.Arguments.count]] \n } \n if(true, [v15(v14[1, 2]*)], trace(666)) \n [v22, v22] \n 997
def case_sem2b_2Fv1_2Fseed_2F5EED2B000002_2F8 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v3" (.alias none [] [] (.resolve "v1")), privateProp "v8" (alg [] [] [] [(.call (.resolve "v3") [(.call (.resolve "v4") [(.call (.resolve "trace") [.num 1]), (.call (.resolve "trace") [.num 2]), (.call (.resolve "trace") [.num 3])])])]), privateProp "v14" (alg [] [] [] [.num 11, .num 12, .num 13]), privateProp "v22" (alg [] [] [] [(.listLiteral [(.call (.resolve "v18") [(.call (.resolve "v20") [.num 4])])])]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (algWithParameters [{ name := "v2", kind := .metaRef }] [] [] [.param "v2"]), privateProp "v4" (alg ["v5", "v6", "v7"] [] [] [(.binary .add (.binary .add (.binary .mul (.param "v5") (.num 100)) (.binary .mul (.param "v6") (.num 10))) (.param "v7"))]), privateProp "v9" (alg ["v10", "v11", "v12"] [] [] [.param "v12"]), privateProp "v15" (alg ["v16", "v17"] [] [] [(.binary .add (.param "v16") (.param "v17"))]), privateProp "v18" (algWithParameters [{ name := "v19", kind := .metaRef }] [] [] [(.dotCall (.dotCall (.param "v19") "Algorithm" (some [(.sequenceSpread (.dotCall (.param "v19") "Arguments" none))])) "repeat" (some [.num 1]))]), privateProp "v20" (alg ["v21"] [] [] [(.binary .add (.param "v21") (.num 1))])] [(.algorithmExpr (alg [] [] [privateProp "v13" (alg [] [] [] [.num 0])] [(.listLiteral [(.listLiteral [(.call (.resolve "v9") [(.sequenceSpread (.dotCall (.resolve "v8") "Arguments" none))]), (.dotCall (.dotCall (.resolve "v8") "Arguments" none) "count" none)])])])), (.call (.resolve "if") [.boolLiteral true, (.listLiteral [(.call (.resolve "v15") [(.sequenceSpread (.index (.resolve "v14") [.num 1, .num 2]))])]), (.call (.resolve "trace") [.num 666])]), (.listLiteral [.resolve "v22", .resolve "v22"]), .num 997])
#guard obs case_sem2b_2Fv1_2Fseed_2F5EED2B000002_2F8 == "ok raw=S[L[L[3, 3]], L[25], L[L[5], L[5]], 997] n=4"

-- sem2b/v1/seed/5EED2B000002/9: v1(meta v2) = v2 \n v3(v4) = v1(v4) \n v5(v6, v7) = trace((v6 * 10) + v7) \n v8 = v3(v5(trace(1), wait(2))) \n v9(v10, v11) = v10 \n v12(v13) = v13 \n if(true, v12([v8.Algorithm(v8.Arguments*), v8.Algorithm(v8.Arguments*), v9(v8.Arguments*)]), trace(666)) \n 997
def case_sem2b_2Fv1_2Fseed_2F5EED2B000002_2F9 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v8" (alg [] [] [] [(.call (.resolve "v3") [(.call (.resolve "v5") [(.call (.resolve "trace") [.num 1]), (.call (.resolve "wait") [.num 2])])])]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (algWithParameters [{ name := "v2", kind := .metaRef }] [] [] [.param "v2"]), privateProp "v3" (alg ["v4"] [] [] [(.call (.resolve "v1") [.param "v4"])]), privateProp "v5" (alg ["v6", "v7"] [] [] [(.call (.resolve "trace") [(.binary .add (.binary .mul (.param "v6") (.num 10)) (.param "v7"))])]), privateProp "v9" (alg ["v10", "v11"] [] [] [.param "v10"]), privateProp "v12" (alg ["v13"] [] [] [.param "v13"])] [(.call (.resolve "if") [.boolLiteral true, (.call (.resolve "v12") [(.listLiteral [(.dotCall (.resolve "v8") "Algorithm" (some [(.sequenceSpread (.dotCall (.resolve "v8") "Arguments" none))])), (.dotCall (.resolve "v8") "Algorithm" (some [(.sequenceSpread (.dotCall (.resolve "v8") "Arguments" none))])), (.call (.resolve "v9") [(.sequenceSpread (.dotCall (.resolve "v8") "Arguments" none))])])]), (.call (.resolve "trace") [.num 666])]), .num 997])
#guard obs case_sem2b_2Fv1_2Fseed_2F5EED2B000002_2F9 == "ok raw=S[L[12, 12, 1], 997] n=2"

-- sem2b/v1/seed/5EED2B000002/10: v1(v2, v3) = v2 + v3 \n if(true, 1, trace(666) / 0) \n v1(trace(2), trace(3), trace(4)) \n 997
def case_sem2b_2Fv1_2Fseed_2F5EED2B000002_2F10 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (alg ["v2", "v3"] [] [] [(.binary .add (.param "v2") (.param "v3"))])] [(.call (.resolve "if") [.boolLiteral true, .num 1, (.binary .div (.call (.resolve "trace") [.num 666]) (.num 0))]), (.call (.resolve "v1") [(.call (.resolve "trace") [.num 2]), (.call (.resolve "trace") [.num 3]), (.call (.resolve "trace") [.num 4])]), .num 997])
#guard obs case_sem2b_2Fv1_2Fseed_2F5EED2B000002_2F10 == "err arity"
#guard errorObs case_sem2b_2Fv1_2Fseed_2F5EED2B000002_2F10 == .matched (some { kind := "arity", names := [], counts := [2, 3] })

-- sem2b/v1/seed/5EED2B000002/11: v1 = wait(1) \n [v1, v1] \n 997
def case_sem2b_2Fv1_2Fseed_2F5EED2B000002_2F11 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v1" (alg [] [] [] [(.call (.resolve "wait") [.num 1])]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"])] [(.listLiteral [.resolve "v1", .resolve "v1"]), .num 997])
#guard obs case_sem2b_2Fv1_2Fseed_2F5EED2B000002_2F11 == "ok raw=S[L[1, 1], 997] n=2"

-- sem2b/v1/seed/5EED2B000002/12: v1 = 11, 12, 13 \n v2(v3, v4) = v3 + v4 \n v5 = trace(1) \n v6(v7) = v7 \n v2(v1[1, 2]*) \n if(false, trace(666), v6([v5(), v5()])) \n 997
def case_sem2b_2Fv1_2Fseed_2F5EED2B000002_2F12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v1" (alg [] [] [] [.num 11, .num 12, .num 13]), privateProp "v5" (alg [] [] [] [(.call (.resolve "trace") [.num 1])]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v2" (alg ["v3", "v4"] [] [] [(.binary .add (.param "v3") (.param "v4"))]), privateProp "v6" (alg ["v7"] [] [] [.param "v7"])] [(.call (.resolve "v2") [(.sequenceSpread (.index (.resolve "v1") [.num 1, .num 2]))]), (.call (.resolve "if") [.boolLiteral false, (.call (.resolve "trace") [.num 666]), (.call (.resolve "v6") [(.listLiteral [(.call (.resolve "v5") []), (.call (.resolve "v5") [])])])]), .num 997])
#guard obs case_sem2b_2Fv1_2Fseed_2F5EED2B000002_2F12 == "ok raw=S[25, L[1, 1], 997] n=3"

-- sem2b/v1/seed/5EED2B000002/13: v1(meta v2) = v2 \n v3 = v1 \n v4(v5, v6) = (v5 * 10) + v6 \n v7 = v3(v4(trace(1), trace(2))) \n [v7.Invoke(8)] \n 997
def case_sem2b_2Fv1_2Fseed_2F5EED2B000002_2F13 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v3" (.alias none [] [] (.resolve "v1")), privateProp "v7" (alg [] [] [] [(.call (.resolve "v3") [(.call (.resolve "v4") [(.call (.resolve "trace") [.num 1]), (.call (.resolve "trace") [.num 2])])])]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (algWithParameters [{ name := "v2", kind := .metaRef }] [] [] [.param "v2"]), privateProp "v4" (alg ["v5", "v6"] [] [] [(.binary .add (.binary .mul (.param "v5") (.num 10)) (.param "v6"))])] [(.listLiteral [(.dotCall (.resolve "v7") "Invoke" (some [.num 8]))]), .num 997])
#guard obs case_sem2b_2Fv1_2Fseed_2F5EED2B000002_2F13 == "err arity"
#guard errorObs case_sem2b_2Fv1_2Fseed_2F5EED2B000002_2F13 == .matched (some { kind := "arity", names := [], counts := [0, 1] })

-- sem2b/v1/seed/5EED2B000002/14: v1(v2, *v3, v4) = count(v3) \n v5 = () \n v6(v7) = v7 + v7 \n v8(meta v9) = v9 \n v10(v11, v12) = (v11 * 10) + v12 \n v13 = v8(v10(wait(4), wait(5))) \n v1(trace(1), v5*, trace(2)) \n v6(wait(3)) \n [[[v13.Arguments[1], v13.Invoke()]]] \n 997
def case_sem2b_2Fv1_2Fseed_2F5EED2B000002_2F14 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v5" (alg [] [] [] [(.emptySequence 0)]), privateProp "v13" (alg [] [] [] [(.call (.resolve "v8") [(.call (.resolve "v10") [(.call (.resolve "wait") [.num 4]), (.call (.resolve "wait") [.num 5])])])]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (algWithParameters [{ name := "v2" }, { name := "v3", kind := .collecting }, { name := "v4" }] [] [] [(.call (.resolve "count") [.param "v3"])]), privateProp "v6" (alg ["v7"] [] [] [(.binary .add (.param "v7") (.param "v7"))]), privateProp "v8" (algWithParameters [{ name := "v9", kind := .metaRef }] [] [] [.param "v9"]), privateProp "v10" (alg ["v11", "v12"] [] [] [(.binary .add (.binary .mul (.param "v11") (.num 10)) (.param "v12"))])] [(.call (.resolve "v1") [(.call (.resolve "trace") [.num 1]), (.sequenceSpread (.resolve "v5")), (.call (.resolve "trace") [.num 2])]), (.call (.resolve "v6") [(.call (.resolve "wait") [.num 3])]), (.listLiteral [(.listLiteral [(.listLiteral [(.index (.dotCall (.resolve "v13") "Arguments" none) [.num 1]), (.dotCall (.resolve "v13") "Invoke" (some []))])])]), .num 997])
#guard obs case_sem2b_2Fv1_2Fseed_2F5EED2B000002_2F14 == "ok raw=S[0, 6, L[L[L[5, 45]]], 997] n=4"

-- sem2b/v1/seed/5EED2B000002/15: v1(v2) = v2 * 3 \n v3 = v1 \n v4 = v3 \n v5(v6) = v6 \n v7 = 11, 12, 13 \n v8(v9) = v9 \n v10(v11) = v11 * 3 \n v12 = v10 \n v5(if(true, v4(1), trace(666))) \n v8(v7[0, 1]) \n v12(2) \n 997
def case_sem2b_2Fv1_2Fseed_2F5EED2B000002_2F15 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v3" (.alias none [] [] (.resolve "v1")), privateProp "v4" (.alias none [] [] (.resolve "v3")), privateProp "v7" (alg [] [] [] [.num 11, .num 12, .num 13]), privateProp "v12" (.alias none [] [] (.resolve "v10")), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (alg ["v2"] [] [] [(.binary .mul (.param "v2") (.num 3))]), privateProp "v5" (alg ["v6"] [] [] [.param "v6"]), privateProp "v8" (alg ["v9"] [] [] [.param "v9"]), privateProp "v10" (alg ["v11"] [] [] [(.binary .mul (.param "v11") (.num 3))])] [(.call (.resolve "v5") [(.call (.resolve "if") [.boolLiteral true, (.call (.resolve "v4") [.num 1]), (.call (.resolve "trace") [.num 666])])]), (.call (.resolve "v8") [(.index (.resolve "v7") [.num 0, .num 1])]), (.call (.resolve "v12") [.num 2]), .num 997])
#guard obs case_sem2b_2Fv1_2Fseed_2F5EED2B000002_2F15 == "ok raw=S[3, S[11, 12], 6, 997] n=4"

-- sem2b/v1/seed/5EED2B000003/0: v1(v2) = v2 + v2 \n if(false, trace(666), { \n   v3 = 0 \n   v1(wait(1)) \n }) \n 997
def case_sem2b_2Fv1_2Fseed_2F5EED2B000003_2F0 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (alg ["v2"] [] [] [(.binary .add (.param "v2") (.param "v2"))])] [(.call (.resolve "if") [.boolLiteral false, (.call (.resolve "trace") [.num 666]), (.algorithmExpr (alg [] [] [privateProp "v3" (alg [] [] [] [.num 0])] [(.call (.resolve "v1") [(.call (.resolve "wait") [.num 1])])]))]), .num 997])
#guard obs case_sem2b_2Fv1_2Fseed_2F5EED2B000003_2F0 == "ok raw=S[2, 997] n=2"

-- sem2b/v1/seed/5EED2B000003/1: v1 = if(true, 1, trace(666) / 0) \n v2((v3, *v4)) = (count(v4) * 10) + v3 \n v5 = 2, 3 \n v6(v7) = v7 + 1 \n v8(v9) = { \n   v6(v10) = v10 + 100 \n   v6(v9) \n } \n v11 = [v8(4), v6(4)] \n v1 \n if(true, v2(v5), trace(666)) \n [v11, v11] \n 997
def case_sem2b_2Fv1_2Fseed_2F5EED2B000003_2F1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v1" (alg [] [] [] [(.call (.resolve "if") [.boolLiteral true, .num 1, (.binary .div (.call (.resolve "trace") [.num 666]) (.num 0))])]), privateProp "v5" (alg [] [] [] [.num 2, .num 3]), privateProp "v11" (alg [] [] [] [(.listLiteral [(.call (.resolve "v8") [.num 4]), (.call (.resolve "v6") [.num 4])])]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v2" (algWithParameterPatterns [.sequenceValue [.capture { name := "v3" }, .capture { name := "v4", kind := .collecting }]] [] [] [(.binary .add (.binary .mul (.call (.resolve "count") [.param "v4"]) (.num 10)) (.param "v3"))]), privateProp "v6" (alg ["v7"] [] [] [(.binary .add (.param "v7") (.num 1))]), privateProp "v8" (alg ["v9"] [] [privateProp "v6" (alg ["v10"] [] [] [(.binary .add (.param "v10") (.num 100))])] [(.call (.resolve "v6") [.param "v9"])])] [.resolve "v1", (.call (.resolve "if") [.boolLiteral true, (.call (.resolve "v2") [.resolve "v5"]), (.call (.resolve "trace") [.num 666])]), (.listLiteral [.resolve "v11", .resolve "v11"]), .num 997])
#guard obs case_sem2b_2Fv1_2Fseed_2F5EED2B000003_2F1 == "ok raw=S[1, 12, L[L[104, 5], L[104, 5]], 997] n=4"

-- sem2b/v1/seed/5EED2B000003/2: v1(meta v2) = v2 \n v3(v4) = v4 \n v5 = v1(v3(1)) \n v6 = v5.Algorithm \n v6 \n 997
def case_sem2b_2Fv1_2Fseed_2F5EED2B000003_2F2 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v5" (alg [] [] [] [(.call (.resolve "v1") [(.call (.resolve "v3") [.num 1])])]), privateProp "v6" (.alias none [] [] ((.dotCall (.resolve "v5") "Algorithm" none))), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (algWithParameters [{ name := "v2", kind := .metaRef }] [] [] [.param "v2"]), privateProp "v3" (alg ["v4"] [] [] [.param "v4"])] [.resolve "v6", .num 997])
#guard obs case_sem2b_2Fv1_2Fseed_2F5EED2B000003_2F2 == "err arity"
#guard errorObs case_sem2b_2Fv1_2Fseed_2F5EED2B000003_2F2 == .matched (some { kind := "arity", names := [], counts := [1, 0] })

-- sem2b/v1/seed/5EED2B000003/3: v1(v2, *v3, v4) = v3 \n v5(*v6) = v1(v6*) \n v8 = { \n   v7 = 0 \n   v5(trace(1), trace(3), trace(4), trace(5), trace(2)) \n } \n [v8, v8] \n 997
def case_sem2b_2Fv1_2Fseed_2F5EED2B000003_2F3 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v8" (alg [] [] [privateProp "v7" (alg [] [] [] [.num 0])] [(.call (.resolve "v5") [(.call (.resolve "trace") [.num 1]), (.call (.resolve "trace") [.num 3]), (.call (.resolve "trace") [.num 4]), (.call (.resolve "trace") [.num 5]), (.call (.resolve "trace") [.num 2])])]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (algWithParameters [{ name := "v2" }, { name := "v3", kind := .collecting }, { name := "v4" }] [] [] [.param "v3"]), privateProp "v5" (algWithParameters [{ name := "v6", kind := .collecting }] [] [] [(.call (.resolve "v1") [(.sequenceSpread (.param "v6"))])])] [(.listLiteral [.resolve "v8", .resolve "v8"]), .num 997])
#guard obs case_sem2b_2Fv1_2Fseed_2F5EED2B000003_2F3 == "ok raw=S[L[L[3, 4, 5], L[3, 4, 5]], 997] n=2"

-- sem2b/v1/seed/5EED2B000003/4: v1(v2, v3) = v2 + v3 \n v1(trace(1) / 0, [trace(2)][5]) \n 997
def case_sem2b_2Fv1_2Fseed_2F5EED2B000003_2F4 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (alg ["v2", "v3"] [] [] [(.binary .add (.param "v2") (.param "v3"))])] [(.call (.resolve "v1") [(.binary .div (.call (.resolve "trace") [.num 1]) (.num 0)), (.index (.listLiteral [(.call (.resolve "trace") [.num 2])]) [.num 5])]), .num 997])
#guard obs case_sem2b_2Fv1_2Fseed_2F5EED2B000003_2F4 == "err div0"
#guard errorObs case_sem2b_2Fv1_2Fseed_2F5EED2B000003_2F4 == .matched (some { kind := "div0", names := [], counts := [] })

-- sem2b/v1/seed/5EED2B000003/5: v1 = [[wait(1), 1 / 0, wait(2)]] \n v1 \n 997
def case_sem2b_2Fv1_2Fseed_2F5EED2B000003_2F5 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v1" (alg [] [] [] [(.listLiteral [(.listLiteral [(.call (.resolve "wait") [.num 1]), (.binary .div (.num 1) (.num 0)), (.call (.resolve "wait") [.num 2])])])]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"])] [.resolve "v1", .num 997])
#guard obs case_sem2b_2Fv1_2Fseed_2F5EED2B000003_2F5 == "err div0"
#guard errorObs case_sem2b_2Fv1_2Fseed_2F5EED2B000003_2F5 == .matched (some { kind := "div0", names := [], counts := [] })

-- sem2b/v1/seed/5EED2B000003/6: v1(meta v2) = v2 \n v3(v4) = v1(v4) \n v5(v6) = v6 \n v7 = v3(v5(trace(1))) \n [v7.Arguments()] \n 997
def case_sem2b_2Fv1_2Fseed_2F5EED2B000003_2F6 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v7" (alg [] [] [] [(.call (.resolve "v3") [(.call (.resolve "v5") [(.call (.resolve "trace") [.num 1])])])]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (algWithParameters [{ name := "v2", kind := .metaRef }] [] [] [.param "v2"]), privateProp "v3" (alg ["v4"] [] [] [(.call (.resolve "v1") [.param "v4"])]), privateProp "v5" (alg ["v6"] [] [] [.param "v6"])] [(.listLiteral [(.dotCall (.resolve "v7") "Arguments" (some []))]), .num 997])
#guard obs case_sem2b_2Fv1_2Fseed_2F5EED2B000003_2F6 == "err illegalInEval"

-- sem2b/v1/seed/5EED2B000003/7: v1 = 11, 12, 13 \n v2(v3, v4) = v3 + v4 \n v5(v6) = { \n   v7(v8) = v8 + v6 \n   v7(1) \n } \n v9 = [v5(14), v5(15)] \n v10(v11, v12) = v11 \n if(false, trace(666), v2(v1[1, 2]*)) \n v9 \n v10(trace(2), trace(666) / 0) \n 997
def case_sem2b_2Fv1_2Fseed_2F5EED2B000003_2F7 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v1" (alg [] [] [] [.num 11, .num 12, .num 13]), privateProp "v9" (alg [] [] [] [(.listLiteral [(.call (.resolve "v5") [.num 14]), (.call (.resolve "v5") [.num 15])])]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v2" (alg ["v3", "v4"] [] [] [(.binary .add (.param "v3") (.param "v4"))]), privateProp "v5" (alg ["v6"] [] [{ (privateLocalProp "v7" (.localCapturedAncestorParams ["v6"]) (alg ["v8"] [] [] [(.binary .add (.param "v8") (.param "v6"))])) with requiredOwnerDepths := some [("v6", some 0)] }] [(.call (.resolve "v7") [.num 1])]), privateProp "v10" (alg ["v11", "v12"] [] [] [.param "v11"])] [(.call (.resolve "if") [.boolLiteral false, (.call (.resolve "trace") [.num 666]), (.call (.resolve "v2") [(.sequenceSpread (.index (.resolve "v1") [.num 1, .num 2]))])]), .resolve "v9", (.call (.resolve "v10") [(.call (.resolve "trace") [.num 2]), (.binary .div (.call (.resolve "trace") [.num 666]) (.num 0))]), .num 997])
#guard obs case_sem2b_2Fv1_2Fseed_2F5EED2B000003_2F7 == "ok raw=S[25, L[15, 16], 2, 997] n=4"

-- sem2b/v1/seed/5EED2B000003/8: v1(v2) = v2 + v2 \n v3(meta v4) = v4.Algorithm(v4.Arguments*).while \n v5(v6) = { \n   v6 + 1 \n   v6 < 1 \n } \n v8(v9) = v9 \n [trace(1), 1 / 0, trace(2)] \n if(true, [v1(wait(3))], trace(666)) \n v8({ \n   v7 = 0 \n   v3(v5(0)) \n }) \n 997
def case_sem2b_2Fv1_2Fseed_2F5EED2B000003_2F8 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (alg ["v2"] [] [] [(.binary .add (.param "v2") (.param "v2"))]), privateProp "v3" (algWithParameters [{ name := "v4", kind := .metaRef }] [] [] [(.dotCall (.dotCall (.param "v4") "Algorithm" (some [(.sequenceSpread (.dotCall (.param "v4") "Arguments" none))])) "while" none)]), privateProp "v5" (alg ["v6"] [] [] [(.binary .add (.param "v6") (.num 1)), (.comparison (.param "v6") [{ op := .lt, operand := (.num 1) }])]), privateProp "v8" (alg ["v9"] [] [] [.param "v9"])] [(.listLiteral [(.call (.resolve "trace") [.num 1]), (.binary .div (.num 1) (.num 0)), (.call (.resolve "trace") [.num 2])]), (.call (.resolve "if") [.boolLiteral true, (.listLiteral [(.call (.resolve "v1") [(.call (.resolve "wait") [.num 3])])]), (.call (.resolve "trace") [.num 666])]), (.call (.resolve "v8") [(.algorithmExpr (alg [] [] [privateProp "v7" (alg [] [] [] [.num 0])] [(.call (.resolve "v3") [(.call (.resolve "v5") [.num 0])])]))]), .num 997])
#guard obs case_sem2b_2Fv1_2Fseed_2F5EED2B000003_2F8 == "err div0"
#guard errorObs case_sem2b_2Fv1_2Fseed_2F5EED2B000003_2F8 == .matched (some { kind := "div0", names := [], counts := [] })

-- sem2b/v1/seed/5EED2B000003/9: v1(v2) = v2 + 3 \n v4(meta v5) = v5 \n v6(v7, v8) = (v7 * 10) + v8 \n v9 = v4(v6(trace(2), trace(3))) \n v10 = v9.Algorithm \n v11(v12) = v12 \n v13 = v11([v10(4, 5), v10(v9.Arguments*)]) \n if(false, trace(666), { \n   v3 = 0 \n   repeat(v1(1), 1) \n }) \n [v13, v13] \n 997
def case_sem2b_2Fv1_2Fseed_2F5EED2B000003_2F9 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v9" (alg [] [] [] [(.call (.resolve "v4") [(.call (.resolve "v6") [(.call (.resolve "trace") [.num 2]), (.call (.resolve "trace") [.num 3])])])]), privateProp "v10" (.alias none [] [] ((.dotCall (.resolve "v9") "Algorithm" none))), privateProp "v13" (alg [] [] [] [(.call (.resolve "v11") [(.listLiteral [(.call (.resolve "v10") [.num 4, .num 5]), (.call (.resolve "v10") [(.sequenceSpread (.dotCall (.resolve "v9") "Arguments" none))])])])]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (alg ["v2"] [] [] [(.binary .add (.param "v2") (.num 3))]), privateProp "v4" (algWithParameters [{ name := "v5", kind := .metaRef }] [] [] [.param "v5"]), privateProp "v6" (alg ["v7", "v8"] [] [] [(.binary .add (.binary .mul (.param "v7") (.num 10)) (.param "v8"))]), privateProp "v11" (alg ["v12"] [] [] [.param "v12"])] [(.call (.resolve "if") [.boolLiteral false, (.call (.resolve "trace") [.num 666]), (.algorithmExpr (alg [] [] [privateProp "v3" (alg [] [] [] [.num 0])] [(.call (.resolve "repeat") [(.call (.resolve "v1") [.num 1]), .num 1])]))]), (.listLiteral [.resolve "v13", .resolve "v13"]), .num 997])
#guard obs case_sem2b_2Fv1_2Fseed_2F5EED2B000003_2F9 == "ok raw=S[4, L[L[45, 23], L[45, 23]], 997] n=3"

-- sem2b/v1/seed/5EED2B000003/10: v1 = 11, 12, 13 \n v2(v3, *v4, v5) = v3 \n v1[trace(1), trace(1)] \n if(false, trace(666), { \n   v6 = 0 \n   v2(trace(1)) \n }) \n { \n   v8 = 0 \n   [14, 15, 16][trace(1), trace(2)] \n } \n 997
def case_sem2b_2Fv1_2Fseed_2F5EED2B000003_2F10 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v1" (alg [] [] [] [.num 11, .num 12, .num 13]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v2" (algWithParameters [{ name := "v3" }, { name := "v4", kind := .collecting }, { name := "v5" }] [] [] [.param "v3"])] [(.index (.resolve "v1") [(.call (.resolve "trace") [.num 1]), (.call (.resolve "trace") [.num 1])]), (.call (.resolve "if") [.boolLiteral false, (.call (.resolve "trace") [.num 666]), (.algorithmExpr (alg [] [] [privateProp "v6" (alg [] [] [] [.num 0])] [(.call (.resolve "v2") [(.call (.resolve "trace") [.num 1])])]))]), (.algorithmExpr (alg [] [] [privateProp "v8" (alg [] [] [] [.num 0])] [(.index (.listLiteral [.num 14, .num 15, .num 16]) [(.call (.resolve "trace") [.num 1]), (.call (.resolve "trace") [.num 2])])])), .num 997])
#guard obs case_sem2b_2Fv1_2Fseed_2F5EED2B000003_2F10 == "err arity"
#guard errorObs case_sem2b_2Fv1_2Fseed_2F5EED2B000003_2F10 == .matched (some { kind := "arity", names := [], counts := [2, 1] })

-- sem2b/v1/seed/5EED2B000003/11: v1 = 11, 12, 13 \n v2(meta v3) = v3 \n v4(v5, v6) = (v5 * 10) + v6 \n v7 = v2(v4(trace(1), trace(2))) \n v8 = v7.Algorithm \n if(true, [v1[]], trace(666)) \n [v8(3, 4)] \n 997
def case_sem2b_2Fv1_2Fseed_2F5EED2B000003_2F11 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v1" (alg [] [] [] [.num 11, .num 12, .num 13]), privateProp "v7" (alg [] [] [] [(.call (.resolve "v2") [(.call (.resolve "v4") [(.call (.resolve "trace") [.num 1]), (.call (.resolve "trace") [.num 2])])])]), privateProp "v8" (.alias none [] [] ((.dotCall (.resolve "v7") "Algorithm" none))), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v2" (algWithParameters [{ name := "v3", kind := .metaRef }] [] [] [.param "v3"]), privateProp "v4" (alg ["v5", "v6"] [] [] [(.binary .add (.binary .mul (.param "v5") (.num 10)) (.param "v6"))])] [(.call (.resolve "if") [.boolLiteral true, (.listLiteral [(.index (.resolve "v1") [])]), (.call (.resolve "trace") [.num 666])]), (.listLiteral [(.call (.resolve "v8") [.num 3, .num 4])]), .num 997])
#guard obs case_sem2b_2Fv1_2Fseed_2F5EED2B000003_2F11 == "ok raw=S[L[S[]], L[34], 997] n=3"

-- sem2b/v1/seed/5EED2B000003/12: v1 = trace(1) \n v2 = [v1, v1()] \n v3 = [wait(2), 1 / 0, wait(3)] \n v4(v5) = v5 + v5 \n v6(v7) = v4(v7) \n v8 = if(false, trace(666), v6(trace(4))) \n v2 \n [v3, v3] \n [v8, v8] \n 997
def case_sem2b_2Fv1_2Fseed_2F5EED2B000003_2F12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v1" (alg [] [] [] [(.call (.resolve "trace") [.num 1])]), privateProp "v2" (alg [] [] [] [(.listLiteral [.resolve "v1", (.call (.resolve "v1") [])])]), privateProp "v3" (alg [] [] [] [(.listLiteral [(.call (.resolve "wait") [.num 2]), (.binary .div (.num 1) (.num 0)), (.call (.resolve "wait") [.num 3])])]), privateProp "v8" (alg [] [] [] [(.call (.resolve "if") [.boolLiteral false, (.call (.resolve "trace") [.num 666]), (.call (.resolve "v6") [(.call (.resolve "trace") [.num 4])])])]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v4" (alg ["v5"] [] [] [(.binary .add (.param "v5") (.param "v5"))]), privateProp "v6" (alg ["v7"] [] [] [(.call (.resolve "v4") [.param "v7"])])] [.resolve "v2", (.listLiteral [.resolve "v3", .resolve "v3"]), (.listLiteral [.resolve "v8", .resolve "v8"]), .num 997])
#guard obs case_sem2b_2Fv1_2Fseed_2F5EED2B000003_2F12 == "err div0"
#guard errorObs case_sem2b_2Fv1_2Fseed_2F5EED2B000003_2F12 == .matched (some { kind := "div0", names := [], counts := [] })

-- sem2b/v1/seed/5EED2B000003/13: v1((v2, *v3)) = (count(v3) * 10) + v2 \n v4 = 1, 2 \n v5 = 11, 12, 13 \n if(true, if(false, trace(666), v1(v4)), trace(666)) \n if(false, trace(666), v5[0]) \n 997
def case_sem2b_2Fv1_2Fseed_2F5EED2B000003_2F13 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v4" (alg [] [] [] [.num 1, .num 2]), privateProp "v5" (alg [] [] [] [.num 11, .num 12, .num 13]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (algWithParameterPatterns [.sequenceValue [.capture { name := "v2" }, .capture { name := "v3", kind := .collecting }]] [] [] [(.binary .add (.binary .mul (.call (.resolve "count") [.param "v3"]) (.num 10)) (.param "v2"))])] [(.call (.resolve "if") [.boolLiteral true, (.call (.resolve "if") [.boolLiteral false, (.call (.resolve "trace") [.num 666]), (.call (.resolve "v1") [.resolve "v4"])]), (.call (.resolve "trace") [.num 666])]), (.call (.resolve "if") [.boolLiteral false, (.call (.resolve "trace") [.num 666]), (.index (.resolve "v5") [.num 0])]), .num 997])
#guard obs case_sem2b_2Fv1_2Fseed_2F5EED2B000003_2F13 == "ok raw=S[11, 11, 997] n=3"

-- sem2b/v1/seed/5EED2B000003/14: v1(meta v2) = v2.Algorithm(v2.Arguments*).while \n v3(v4) = { \n   v4 + 1 \n   v4 < 4 \n } \n if(true, 1, trace(666) / 0) \n v1(v3(0)) \n 997
def case_sem2b_2Fv1_2Fseed_2F5EED2B000003_2F14 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (algWithParameters [{ name := "v2", kind := .metaRef }] [] [] [(.dotCall (.dotCall (.param "v2") "Algorithm" (some [(.sequenceSpread (.dotCall (.param "v2") "Arguments" none))])) "while" none)]), privateProp "v3" (alg ["v4"] [] [] [(.binary .add (.param "v4") (.num 1)), (.comparison (.param "v4") [{ op := .lt, operand := (.num 4) }])])] [(.call (.resolve "if") [.boolLiteral true, .num 1, (.binary .div (.call (.resolve "trace") [.num 666]) (.num 0))]), (.call (.resolve "v1") [(.call (.resolve "v3") [.num 0])]), .num 997])
#guard obs case_sem2b_2Fv1_2Fseed_2F5EED2B000003_2F14 == "ok raw=S[1, 4, 997] n=3"

-- sem2b/v1/seed/5EED2B000003/15: v1(v2) = v2 + v2 \n v3 = v1(wait(1)) \n v4 = [v3, v3] \n v5(meta v6) = v6 \n v7 = v5 \n v8 = 11, 12 \n v9(*v10) = count(v10) \n v11 = v7(v9(wait(2), trace(3), v8*)) \n v12(meta v13) = v13 \n v14(v15) = v12(v15) \n v16(*v17) = count(v17) \n v18 = v14(v16(trace(6))) \n v19(v20) = v20 \n [v4, v4] \n [v11.Algorithm(4, 5)] \n [v19(v18.Arguments*), v18.Arguments[0], v18.Algorithm(7, 8, 9), v18.Algorithm(1)] \n 997
def case_sem2b_2Fv1_2Fseed_2F5EED2B000003_2F15 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v3" (alg [] [] [] [(.call (.resolve "v1") [(.call (.resolve "wait") [.num 1])])]), privateProp "v4" (alg [] [] [] [(.listLiteral [.resolve "v3", .resolve "v3"])]), privateProp "v7" (.alias none [] [] (.resolve "v5")), privateProp "v8" (alg [] [] [] [.num 11, .num 12]), privateProp "v11" (alg [] [] [] [(.call (.resolve "v7") [(.call (.resolve "v9") [(.call (.resolve "wait") [.num 2]), (.call (.resolve "trace") [.num 3]), (.sequenceSpread (.resolve "v8"))])])]), privateProp "v18" (alg [] [] [] [(.call (.resolve "v14") [(.call (.resolve "v16") [(.call (.resolve "trace") [.num 6])])])]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (alg ["v2"] [] [] [(.binary .add (.param "v2") (.param "v2"))]), privateProp "v5" (algWithParameters [{ name := "v6", kind := .metaRef }] [] [] [.param "v6"]), privateProp "v9" (algWithParameters [{ name := "v10", kind := .collecting }] [] [] [(.call (.resolve "count") [.param "v10"])]), privateProp "v12" (algWithParameters [{ name := "v13", kind := .metaRef }] [] [] [.param "v13"]), privateProp "v14" (alg ["v15"] [] [] [(.call (.resolve "v12") [.param "v15"])]), privateProp "v16" (algWithParameters [{ name := "v17", kind := .collecting }] [] [] [(.call (.resolve "count") [.param "v17"])]), privateProp "v19" (alg ["v20"] [] [] [.param "v20"])] [(.listLiteral [.resolve "v4", .resolve "v4"]), (.listLiteral [(.dotCall (.resolve "v11") "Algorithm" (some [.num 4, .num 5]))]), (.listLiteral [(.call (.resolve "v19") [(.sequenceSpread (.dotCall (.resolve "v18") "Arguments" none))]), (.index (.dotCall (.resolve "v18") "Arguments" none) [.num 0]), (.dotCall (.resolve "v18") "Algorithm" (some [.num 7, .num 8, .num 9])), (.dotCall (.resolve "v18") "Algorithm" (some [.num 1]))]), .num 997])
#guard obs case_sem2b_2Fv1_2Fseed_2F5EED2B000003_2F15 == "ok raw=S[L[L[2, 2], L[2, 2]], L[2], L[6, 6, 3, 1], 997] n=4"

-- sem2b/v1/seed/5EED2B000004/0: v1(meta v2) = v2 \n v3(v4, v5) = (v4 * 10) + v5 \n v6 = v1(v3(trace(1), trace(2))) \n v7 = v6.Algorithm \n v8(v9) = v9 + 1 \n v10(v11) = { \n   v8(v12) = v12 + 100 \n   v8(v11) \n } \n v13 = [v10(7), v8(7)] \n [v7(3, 4), v7(v6.Arguments*)] \n [wait(5), 1 / 0, wait(6)] \n v13 \n 997
def case_sem2b_2Fv1_2Fseed_2F5EED2B000004_2F0 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v6" (alg [] [] [] [(.call (.resolve "v1") [(.call (.resolve "v3") [(.call (.resolve "trace") [.num 1]), (.call (.resolve "trace") [.num 2])])])]), privateProp "v7" (.alias none [] [] ((.dotCall (.resolve "v6") "Algorithm" none))), privateProp "v13" (alg [] [] [] [(.listLiteral [(.call (.resolve "v10") [.num 7]), (.call (.resolve "v8") [.num 7])])]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (algWithParameters [{ name := "v2", kind := .metaRef }] [] [] [.param "v2"]), privateProp "v3" (alg ["v4", "v5"] [] [] [(.binary .add (.binary .mul (.param "v4") (.num 10)) (.param "v5"))]), privateProp "v8" (alg ["v9"] [] [] [(.binary .add (.param "v9") (.num 1))]), privateProp "v10" (alg ["v11"] [] [privateProp "v8" (alg ["v12"] [] [] [(.binary .add (.param "v12") (.num 100))])] [(.call (.resolve "v8") [.param "v11"])])] [(.listLiteral [(.call (.resolve "v7") [.num 3, .num 4]), (.call (.resolve "v7") [(.sequenceSpread (.dotCall (.resolve "v6") "Arguments" none))])]), (.listLiteral [(.call (.resolve "wait") [.num 5]), (.binary .div (.num 1) (.num 0)), (.call (.resolve "wait") [.num 6])]), .resolve "v13", .num 997])
#guard obs case_sem2b_2Fv1_2Fseed_2F5EED2B000004_2F0 == "err div0"
#guard errorObs case_sem2b_2Fv1_2Fseed_2F5EED2B000004_2F0 == .matched (some { kind := "div0", names := [], counts := [] })

-- sem2b/v1/seed/5EED2B000004/1: v1 = if(false, trace(666), [wait(1), 1 / 0, wait(2)]) \n v2(v3) = { \n   v4 = trace(v3) \n   v4 + v4 \n } \n v1 \n { \n   v5 = 0 \n   [v2(3), v2(3)] \n } \n 997
def case_sem2b_2Fv1_2Fseed_2F5EED2B000004_2F1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v1" (alg [] [] [] [(.call (.resolve "if") [.boolLiteral false, (.call (.resolve "trace") [.num 666]), (.listLiteral [(.call (.resolve "wait") [.num 1]), (.binary .div (.num 1) (.num 0)), (.call (.resolve "wait") [.num 2])])])]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v2" (alg ["v3"] [] [{ (privateLocalProp "v4" (.localCapturedAncestorParams ["v3"]) (alg [] [] [] [(.call (.resolve "trace") [.param "v3"])])) with requiredOwnerDepths := some [("v3", some 0)] }] [(.binary .add (.resolve "v4") (.resolve "v4"))])] [.resolve "v1", (.algorithmExpr (alg [] [] [privateProp "v5" (alg [] [] [] [.num 0])] [(.listLiteral [(.call (.resolve "v2") [.num 3]), (.call (.resolve "v2") [.num 3])])])), .num 997])
#guard obs case_sem2b_2Fv1_2Fseed_2F5EED2B000004_2F1 == "err div0"
#guard errorObs case_sem2b_2Fv1_2Fseed_2F5EED2B000004_2F1 == .matched (some { kind := "div0", names := [], counts := [] })

-- sem2b/v1/seed/5EED2B000004/2: v1(v2) = v2 + 1 \n v3(v4) = { \n   v1(v5) = v5 + 100 \n   v1(v4) \n } \n v6 = [v3(1), v1(1)] \n v7 = trace(2) / 0 \n v6 \n [[[v7, v7]]] \n 997
def case_sem2b_2Fv1_2Fseed_2F5EED2B000004_2F2 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v6" (alg [] [] [] [(.listLiteral [(.call (.resolve "v3") [.num 1]), (.call (.resolve "v1") [.num 1])])]), privateProp "v7" (alg [] [] [] [(.binary .div (.call (.resolve "trace") [.num 2]) (.num 0))]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (alg ["v2"] [] [] [(.binary .add (.param "v2") (.num 1))]), privateProp "v3" (alg ["v4"] [] [privateProp "v1" (alg ["v5"] [] [] [(.binary .add (.param "v5") (.num 100))])] [(.call (.resolve "v1") [.param "v4"])])] [.resolve "v6", (.listLiteral [(.listLiteral [(.listLiteral [.resolve "v7", .resolve "v7"])])]), .num 997])
#guard obs case_sem2b_2Fv1_2Fseed_2F5EED2B000004_2F2 == "err div0"
#guard errorObs case_sem2b_2Fv1_2Fseed_2F5EED2B000004_2F2 == .matched (some { kind := "div0", names := [], counts := [] })

-- sem2b/v1/seed/5EED2B000004/3: v1(meta v2) = v2 \n v3(v4, v5) = (v4 * 10) + v5 \n v6 = v1(v3(trace(1), trace(2))) \n v7 = v6.Algorithm \n v8 = [v7(3, 4)] \n v9 = wait(5) \n v8 \n [v9, v9] \n 997
def case_sem2b_2Fv1_2Fseed_2F5EED2B000004_2F3 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v6" (alg [] [] [] [(.call (.resolve "v1") [(.call (.resolve "v3") [(.call (.resolve "trace") [.num 1]), (.call (.resolve "trace") [.num 2])])])]), privateProp "v7" (.alias none [] [] ((.dotCall (.resolve "v6") "Algorithm" none))), privateProp "v8" (alg [] [] [] [(.listLiteral [(.call (.resolve "v7") [.num 3, .num 4])])]), privateProp "v9" (alg [] [] [] [(.call (.resolve "wait") [.num 5])]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (algWithParameters [{ name := "v2", kind := .metaRef }] [] [] [.param "v2"]), privateProp "v3" (alg ["v4", "v5"] [] [] [(.binary .add (.binary .mul (.param "v4") (.num 10)) (.param "v5"))])] [.resolve "v8", (.listLiteral [.resolve "v9", .resolve "v9"]), .num 997])
#guard obs case_sem2b_2Fv1_2Fseed_2F5EED2B000004_2F3 == "ok raw=S[L[34], L[5, 5], 997] n=3"

-- sem2b/v1/seed/5EED2B000004/4: v1([v2, *v3]) = v2 + count(v3) \n v4 = v1([1, 2]) \n if(true, v4, trace(666)) \n 997
def case_sem2b_2Fv1_2Fseed_2F5EED2B000004_2F4 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v4" (alg [] [] [] [(.call (.resolve "v1") [(.listLiteral [.num 1, .num 2])])]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (algWithParameterPatterns [.listValue [.capture { name := "v2" }, .capture { name := "v3", kind := .collecting }]] [] [] [(.binary .add (.param "v2") (.call (.resolve "count") [.param "v3"]))])] [(.call (.resolve "if") [.boolLiteral true, .resolve "v4", (.call (.resolve "trace") [.num 666])]), .num 997])
#guard obs case_sem2b_2Fv1_2Fseed_2F5EED2B000004_2F4 == "ok raw=S[2, 997] n=2"

-- sem2b/v1/seed/5EED2B000004/5: v1(meta v2) = v2 \n v3(v4) = v1(v4) \n v5(v6, v7, v8) = trace((v6 * 100) + (v7 * 10) + v8) \n v9 = v3(v5(wait(1), trace(2), trace(3))) \n v10(v11, v12, v13) = v12 \n if(false, trace(666), if(true, [v10(v9.Arguments*), v9.Algorithm(v9.Arguments*)], trace(666))) \n 997
def case_sem2b_2Fv1_2Fseed_2F5EED2B000004_2F5 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v9" (alg [] [] [] [(.call (.resolve "v3") [(.call (.resolve "v5") [(.call (.resolve "wait") [.num 1]), (.call (.resolve "trace") [.num 2]), (.call (.resolve "trace") [.num 3])])])]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (algWithParameters [{ name := "v2", kind := .metaRef }] [] [] [.param "v2"]), privateProp "v3" (alg ["v4"] [] [] [(.call (.resolve "v1") [.param "v4"])]), privateProp "v5" (alg ["v6", "v7", "v8"] [] [] [(.call (.resolve "trace") [(.binary .add (.binary .add (.binary .mul (.param "v6") (.num 100)) (.binary .mul (.param "v7") (.num 10))) (.param "v8"))])]), privateProp "v10" (alg ["v11", "v12", "v13"] [] [] [.param "v12"])] [(.call (.resolve "if") [.boolLiteral false, (.call (.resolve "trace") [.num 666]), (.call (.resolve "if") [.boolLiteral true, (.listLiteral [(.call (.resolve "v10") [(.sequenceSpread (.dotCall (.resolve "v9") "Arguments" none))]), (.dotCall (.resolve "v9") "Algorithm" (some [(.sequenceSpread (.dotCall (.resolve "v9") "Arguments" none))]))]), (.call (.resolve "trace") [.num 666])])]), .num 997])
#guard obs case_sem2b_2Fv1_2Fseed_2F5EED2B000004_2F5 == "ok raw=S[L[2, 123], 997] n=2"

-- sem2b/v1/seed/5EED2B000004/6: v1 = trace(1) / 0 \n [v1, v1] \n 997
def case_sem2b_2Fv1_2Fseed_2F5EED2B000004_2F6 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v1" (alg [] [] [] [(.binary .div (.call (.resolve "trace") [.num 1]) (.num 0))]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"])] [(.listLiteral [.resolve "v1", .resolve "v1"]), .num 997])
#guard obs case_sem2b_2Fv1_2Fseed_2F5EED2B000004_2F6 == "err div0"
#guard errorObs case_sem2b_2Fv1_2Fseed_2F5EED2B000004_2F6 == .matched (some { kind := "div0", names := [], counts := [] })

-- sem2b/v1/seed/5EED2B000004/7: v1(v2) = v2 + v2 \n v1(wait(1)) \n 997
def case_sem2b_2Fv1_2Fseed_2F5EED2B000004_2F7 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (alg ["v2"] [] [] [(.binary .add (.param "v2") (.param "v2"))])] [(.call (.resolve "v1") [(.call (.resolve "wait") [.num 1])]), .num 997])
#guard obs case_sem2b_2Fv1_2Fseed_2F5EED2B000004_2F7 == "ok raw=S[2, 997] n=2"

-- sem2b/v1/seed/5EED2B000004/8: [11, 12, 13][9] \n 997
def case_sem2b_2Fv1_2Fseed_2F5EED2B000004_2F8 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"])] [(.index (.listLiteral [.num 11, .num 12, .num 13]) [.num 9]), .num 997])
#guard obs case_sem2b_2Fv1_2Fseed_2F5EED2B000004_2F8 == "err index"
#guard errorObs case_sem2b_2Fv1_2Fseed_2F5EED2B000004_2F8 == .matched (some { kind := "index", names := [], counts := [] })

-- sem2b/v1/seed/5EED2B000004/9: v1 = trace(1) / 0 \n if(true, [v1, v1], trace(666)) \n 997
def case_sem2b_2Fv1_2Fseed_2F5EED2B000004_2F9 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v1" (alg [] [] [] [(.binary .div (.call (.resolve "trace") [.num 1]) (.num 0))]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"])] [(.call (.resolve "if") [.boolLiteral true, (.listLiteral [.resolve "v1", .resolve "v1"]), (.call (.resolve "trace") [.num 666])]), .num 997])
#guard obs case_sem2b_2Fv1_2Fseed_2F5EED2B000004_2F9 == "err div0"
#guard errorObs case_sem2b_2Fv1_2Fseed_2F5EED2B000004_2F9 == .matched (some { kind := "div0", names := [], counts := [] })

-- sem2b/v1/seed/5EED2B000004/10: v1(meta v2) = v2 \n v3(v4) = v1(v4) \n v5(v6, v7, v8) = (v6 * 100) + (v7 * 10) + v8 \n v9 = v3(v5(trace(1), trace(2), wait(3))) \n v10 = [v9.Algorithm(4, 5, 6), v9.Algorithm(v9.Arguments*), v9.Arguments.count] \n v11(meta v12) = v12 \n v13(v14, v15) = (v14 * 10) + v15 \n v16 = v11(v13(wait(7), wait(8))) \n v17(meta v18) = v18 \n v19(v20, v21) = (v20 * 10) + v21 \n v22 = v17(v19(trace(9), trace(1))) \n v23 = v22.Algorithm \n v24(v25) = v25 \n v26 = v24([v23(2, 3), v23(v22.Arguments*)]) \n v10 \n if(true, [v16.Arguments[1], v16.Invoke()], trace(666)) \n [v26, v26] \n 997
def case_sem2b_2Fv1_2Fseed_2F5EED2B000004_2F10 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v9" (alg [] [] [] [(.call (.resolve "v3") [(.call (.resolve "v5") [(.call (.resolve "trace") [.num 1]), (.call (.resolve "trace") [.num 2]), (.call (.resolve "wait") [.num 3])])])]), privateProp "v10" (alg [] [] [] [(.listLiteral [(.dotCall (.resolve "v9") "Algorithm" (some [.num 4, .num 5, .num 6])), (.dotCall (.resolve "v9") "Algorithm" (some [(.sequenceSpread (.dotCall (.resolve "v9") "Arguments" none))])), (.dotCall (.dotCall (.resolve "v9") "Arguments" none) "count" none)])]), privateProp "v16" (alg [] [] [] [(.call (.resolve "v11") [(.call (.resolve "v13") [(.call (.resolve "wait") [.num 7]), (.call (.resolve "wait") [.num 8])])])]), privateProp "v22" (alg [] [] [] [(.call (.resolve "v17") [(.call (.resolve "v19") [(.call (.resolve "trace") [.num 9]), (.call (.resolve "trace") [.num 1])])])]), privateProp "v23" (.alias none [] [] ((.dotCall (.resolve "v22") "Algorithm" none))), privateProp "v26" (alg [] [] [] [(.call (.resolve "v24") [(.listLiteral [(.call (.resolve "v23") [.num 2, .num 3]), (.call (.resolve "v23") [(.sequenceSpread (.dotCall (.resolve "v22") "Arguments" none))])])])]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (algWithParameters [{ name := "v2", kind := .metaRef }] [] [] [.param "v2"]), privateProp "v3" (alg ["v4"] [] [] [(.call (.resolve "v1") [.param "v4"])]), privateProp "v5" (alg ["v6", "v7", "v8"] [] [] [(.binary .add (.binary .add (.binary .mul (.param "v6") (.num 100)) (.binary .mul (.param "v7") (.num 10))) (.param "v8"))]), privateProp "v11" (algWithParameters [{ name := "v12", kind := .metaRef }] [] [] [.param "v12"]), privateProp "v13" (alg ["v14", "v15"] [] [] [(.binary .add (.binary .mul (.param "v14") (.num 10)) (.param "v15"))]), privateProp "v17" (algWithParameters [{ name := "v18", kind := .metaRef }] [] [] [.param "v18"]), privateProp "v19" (alg ["v20", "v21"] [] [] [(.binary .add (.binary .mul (.param "v20") (.num 10)) (.param "v21"))]), privateProp "v24" (alg ["v25"] [] [] [.param "v25"])] [.resolve "v10", (.call (.resolve "if") [.boolLiteral true, (.listLiteral [(.index (.dotCall (.resolve "v16") "Arguments" none) [.num 1]), (.dotCall (.resolve "v16") "Invoke" (some []))]), (.call (.resolve "trace") [.num 666])]), (.listLiteral [.resolve "v26", .resolve "v26"]), .num 997])
#guard obs case_sem2b_2Fv1_2Fseed_2F5EED2B000004_2F10 == "ok raw=S[L[456, 123, 3], L[8, 78], L[L[23, 91], L[23, 91]], 997] n=4"

-- sem2b/v1/seed/5EED2B000004/11: v1(meta v2) = v2.repeat(2) \n v3(v4) = v4 + 1 \n v5 = if(true, v1(v3(1)), trace(666)) \n v6(v7) = { \n   v8(v9) = v9 + v7 \n   v8(2) \n } \n v5 \n { \n   v11 = 0 \n   { \n     v10 = 0 \n     [v6(11), v6(12)] \n   } \n } \n 997
def case_sem2b_2Fv1_2Fseed_2F5EED2B000004_2F11 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v5" (alg [] [] [] [(.call (.resolve "if") [.boolLiteral true, (.call (.resolve "v1") [(.call (.resolve "v3") [.num 1])]), (.call (.resolve "trace") [.num 666])])]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (algWithParameters [{ name := "v2", kind := .metaRef }] [] [] [(.dotCall (.param "v2") "repeat" (some [.num 2]))]), privateProp "v3" (alg ["v4"] [] [] [(.binary .add (.param "v4") (.num 1))]), privateProp "v6" (alg ["v7"] [] [{ (privateLocalProp "v8" (.localCapturedAncestorParams ["v7"]) (alg ["v9"] [] [] [(.binary .add (.param "v9") (.param "v7"))])) with requiredOwnerDepths := some [("v7", some 0)] }] [(.call (.resolve "v8") [.num 2])])] [.resolve "v5", (.algorithmExpr (alg [] [] [privateProp "v11" (alg [] [] [] [.num 0])] [(.algorithmExpr (alg [] [] [privateProp "v10" (alg [] [] [] [.num 0])] [(.listLiteral [(.call (.resolve "v6") [.num 11]), (.call (.resolve "v6") [.num 12])])]))])), .num 997])
#guard obs case_sem2b_2Fv1_2Fseed_2F5EED2B000004_2F11 == "err notAnAlgorithm"

-- sem2b/v1/seed/5EED2B000004/12: v1(v2) = { \n   v2 + 1 \n   v2 + 2 \n } \n v3 = wait(1) \n v5 = wait(2) \n v1(0).while \n { \n   v4 = 0 \n   if(false, trace(666), [v3, v3]) \n } \n if(false, trace(666), if(true, [v5, v5], trace(666))) \n 997
def case_sem2b_2Fv1_2Fseed_2F5EED2B000004_2F12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v3" (alg [] [] [] [(.call (.resolve "wait") [.num 1])]), privateProp "v5" (alg [] [] [] [(.call (.resolve "wait") [.num 2])]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (alg ["v2"] [] [] [(.binary .add (.param "v2") (.num 1)), (.binary .add (.param "v2") (.num 2))])] [(.dotCall (.call (.resolve "v1") [.num 0]) "while" none), (.algorithmExpr (alg [] [] [privateProp "v4" (alg [] [] [] [.num 0])] [(.call (.resolve "if") [.boolLiteral false, (.call (.resolve "trace") [.num 666]), (.listLiteral [.resolve "v3", .resolve "v3"])])])), (.call (.resolve "if") [.boolLiteral false, (.call (.resolve "trace") [.num 666]), (.call (.resolve "if") [.boolLiteral true, (.listLiteral [.resolve "v5", .resolve "v5"]), (.call (.resolve "trace") [.num 666])])]), .num 997])
#guard obs case_sem2b_2Fv1_2Fseed_2F5EED2B000004_2F12 == "err type"

-- sem2b/v1/seed/5EED2B000004/13: v1(meta v2) = v2 \n v3(*v4) = count(v4) \n v5 = v1(v3(trace(1), trace(2), trace(3))) \n v6(v7, v8, v9) = v7 \n v10(v11, *v12, v13) = v11 \n [v6(v5.Arguments*)] \n [wait(4), wait(5)] \n v10(trace(6)) \n 997
def case_sem2b_2Fv1_2Fseed_2F5EED2B000004_2F13 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v5" (alg [] [] [] [(.call (.resolve "v1") [(.call (.resolve "v3") [(.call (.resolve "trace") [.num 1]), (.call (.resolve "trace") [.num 2]), (.call (.resolve "trace") [.num 3])])])]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (algWithParameters [{ name := "v2", kind := .metaRef }] [] [] [.param "v2"]), privateProp "v3" (algWithParameters [{ name := "v4", kind := .collecting }] [] [] [(.call (.resolve "count") [.param "v4"])]), privateProp "v6" (alg ["v7", "v8", "v9"] [] [] [.param "v7"]), privateProp "v10" (algWithParameters [{ name := "v11" }, { name := "v12", kind := .collecting }, { name := "v13" }] [] [] [.param "v11"])] [(.listLiteral [(.call (.resolve "v6") [(.sequenceSpread (.dotCall (.resolve "v5") "Arguments" none))])]), (.listLiteral [(.call (.resolve "wait") [.num 4]), (.call (.resolve "wait") [.num 5])]), (.call (.resolve "v10") [(.call (.resolve "trace") [.num 6])]), .num 997])
#guard obs case_sem2b_2Fv1_2Fseed_2F5EED2B000004_2F13 == "err arity"
#guard errorObs case_sem2b_2Fv1_2Fseed_2F5EED2B000004_2F13 == .matched (some { kind := "arity", names := [], counts := [2, 1] })

-- sem2b/v1/seed/5EED2B000004/14: v1(meta v2) = v2 \n v3(v4) = v1(v4) \n v5(*v6) = trace(count(v6)) \n v7 = v3(v5(trace(1), trace(2))) \n v8(v9, v10) = v9 \n if(true, [v8(v7.Arguments*), v7.Arguments.count], trace(666)) \n 997
def case_sem2b_2Fv1_2Fseed_2F5EED2B000004_2F14 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v7" (alg [] [] [] [(.call (.resolve "v3") [(.call (.resolve "v5") [(.call (.resolve "trace") [.num 1]), (.call (.resolve "trace") [.num 2])])])]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (algWithParameters [{ name := "v2", kind := .metaRef }] [] [] [.param "v2"]), privateProp "v3" (alg ["v4"] [] [] [(.call (.resolve "v1") [.param "v4"])]), privateProp "v5" (algWithParameters [{ name := "v6", kind := .collecting }] [] [] [(.call (.resolve "trace") [(.call (.resolve "count") [.param "v6"])])]), privateProp "v8" (alg ["v9", "v10"] [] [] [.param "v9"])] [(.call (.resolve "if") [.boolLiteral true, (.listLiteral [(.call (.resolve "v8") [(.sequenceSpread (.dotCall (.resolve "v7") "Arguments" none))]), (.dotCall (.dotCall (.resolve "v7") "Arguments" none) "count" none)]), (.call (.resolve "trace") [.num 666])]), .num 997])
#guard obs case_sem2b_2Fv1_2Fseed_2F5EED2B000004_2F14 == "ok raw=S[L[1, 2], 997] n=2"

-- sem2b/v1/seed/5EED2B000004/15: v1((v2, *v3)) = (count(v3) * 10) + v2 \n v4 = if(true, 1, trace(666) / 0) \n v5(meta v6) = v6.Algorithm(v6.Arguments*).while \n v7(v8) = { \n   v8 + 1 \n   v8 < 3 \n } \n v9 = v5(v7(0)) \n v1(11) \n v4 \n v9 \n 997
def case_sem2b_2Fv1_2Fseed_2F5EED2B000004_2F15 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v4" (alg [] [] [] [(.call (.resolve "if") [.boolLiteral true, .num 1, (.binary .div (.call (.resolve "trace") [.num 666]) (.num 0))])]), privateProp "v9" (alg [] [] [] [(.call (.resolve "v5") [(.call (.resolve "v7") [.num 0])])]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (algWithParameterPatterns [.sequenceValue [.capture { name := "v2" }, .capture { name := "v3", kind := .collecting }]] [] [] [(.binary .add (.binary .mul (.call (.resolve "count") [.param "v3"]) (.num 10)) (.param "v2"))]), privateProp "v5" (algWithParameters [{ name := "v6", kind := .metaRef }] [] [] [(.dotCall (.dotCall (.param "v6") "Algorithm" (some [(.sequenceSpread (.dotCall (.param "v6") "Arguments" none))])) "while" none)]), privateProp "v7" (alg ["v8"] [] [] [(.binary .add (.param "v8") (.num 1)), (.comparison (.param "v8") [{ op := .lt, operand := (.num 3) }])])] [(.call (.resolve "v1") [.num 11]), .resolve "v4", .resolve "v9", .num 997])
#guard obs case_sem2b_2Fv1_2Fseed_2F5EED2B000004_2F15 == "err type"

-- sem2b/v1/seed/5EED2B000005/0: v1(meta v2) = v2 \n v3(v4) = v4 \n v5 = v1(v3(1)) \n v6 = v5.Algorithm \n v7 = v6 \n [v7, v7] \n 997
def case_sem2b_2Fv1_2Fseed_2F5EED2B000005_2F0 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v5" (alg [] [] [] [(.call (.resolve "v1") [(.call (.resolve "v3") [.num 1])])]), privateProp "v6" (.alias none [] [] ((.dotCall (.resolve "v5") "Algorithm" none))), privateProp "v7" (.alias none [] [] (.resolve "v6")), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (algWithParameters [{ name := "v2", kind := .metaRef }] [] [] [.param "v2"]), privateProp "v3" (alg ["v4"] [] [] [.param "v4"])] [(.listLiteral [.resolve "v7", .resolve "v7"]), .num 997])
#guard obs case_sem2b_2Fv1_2Fseed_2F5EED2B000005_2F0 == "err arity"
#guard errorObs case_sem2b_2Fv1_2Fseed_2F5EED2B000005_2F0 == .matched (some { kind := "arity", names := [], counts := [1, 0] })

-- sem2b/v1/seed/5EED2B000005/1: v1(meta v2) = v2 \n v3 = v1 \n v4(v5, v6, v7) = (v5 * 100) + (v6 * 10) + v7 \n v8 = v3(v4(trace(1), trace(2), trace(3))) \n v9 = wait(7) / 0 \n [v8.Invoke(), v8.Algorithm(4, 5, 6)] \n if(false, trace(666), [v9, v9]) \n 997
def case_sem2b_2Fv1_2Fseed_2F5EED2B000005_2F1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v3" (.alias none [] [] (.resolve "v1")), privateProp "v8" (alg [] [] [] [(.call (.resolve "v3") [(.call (.resolve "v4") [(.call (.resolve "trace") [.num 1]), (.call (.resolve "trace") [.num 2]), (.call (.resolve "trace") [.num 3])])])]), privateProp "v9" (alg [] [] [] [(.binary .div (.call (.resolve "wait") [.num 7]) (.num 0))]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (algWithParameters [{ name := "v2", kind := .metaRef }] [] [] [.param "v2"]), privateProp "v4" (alg ["v5", "v6", "v7"] [] [] [(.binary .add (.binary .add (.binary .mul (.param "v5") (.num 100)) (.binary .mul (.param "v6") (.num 10))) (.param "v7"))])] [(.listLiteral [(.dotCall (.resolve "v8") "Invoke" (some [])), (.dotCall (.resolve "v8") "Algorithm" (some [.num 4, .num 5, .num 6]))]), (.call (.resolve "if") [.boolLiteral false, (.call (.resolve "trace") [.num 666]), (.listLiteral [.resolve "v9", .resolve "v9"])]), .num 997])
#guard obs case_sem2b_2Fv1_2Fseed_2F5EED2B000005_2F1 == "err div0"
#guard errorObs case_sem2b_2Fv1_2Fseed_2F5EED2B000005_2F1 == .matched (some { kind := "div0", names := [], counts := [] })

-- sem2b/v1/seed/5EED2B000005/2: v1(meta v2) = v2 \n v3(v4) = v4 \n v5 = v1(v3(1)) \n v6 = v5.Algorithm \n v8(v9) = { \n   v10(v11) = v11 + v9 \n   v10(2) \n } \n v12 = [v8(11), v8(12)] \n if(true, { \n   v7 = 0 \n   v6 \n }, trace(666)) \n v12 \n 997
def case_sem2b_2Fv1_2Fseed_2F5EED2B000005_2F2 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v5" (alg [] [] [] [(.call (.resolve "v1") [(.call (.resolve "v3") [.num 1])])]), privateProp "v6" (.alias none [] [] ((.dotCall (.resolve "v5") "Algorithm" none))), privateProp "v12" (alg [] [] [] [(.listLiteral [(.call (.resolve "v8") [.num 11]), (.call (.resolve "v8") [.num 12])])]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (algWithParameters [{ name := "v2", kind := .metaRef }] [] [] [.param "v2"]), privateProp "v3" (alg ["v4"] [] [] [.param "v4"]), privateProp "v8" (alg ["v9"] [] [{ (privateLocalProp "v10" (.localCapturedAncestorParams ["v9"]) (alg ["v11"] [] [] [(.binary .add (.param "v11") (.param "v9"))])) with requiredOwnerDepths := some [("v9", some 0)] }] [(.call (.resolve "v10") [.num 2])])] [(.call (.resolve "if") [.boolLiteral true, (.algorithmExpr (.alias none [] [privateProp "v7" (alg [] [] [] [.num 0])] (.resolve "v6") none false)), (.call (.resolve "trace") [.num 666])]), .resolve "v12", .num 997])
#guard obs case_sem2b_2Fv1_2Fseed_2F5EED2B000005_2F2 == "err arity"
#guard errorObs case_sem2b_2Fv1_2Fseed_2F5EED2B000005_2F2 == .matched (some { kind := "arity", names := [], counts := [1, 0] })

-- sem2b/v1/seed/5EED2B000005/3: v1(v2, v3) = v2 + v3 \n v4 = if(true, 3, trace(666) / 0) \n v1(trace(1) / 0, [trace(2)][5]) \n [v4, v4] \n 997
def case_sem2b_2Fv1_2Fseed_2F5EED2B000005_2F3 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v4" (alg [] [] [] [(.call (.resolve "if") [.boolLiteral true, .num 3, (.binary .div (.call (.resolve "trace") [.num 666]) (.num 0))])]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (alg ["v2", "v3"] [] [] [(.binary .add (.param "v2") (.param "v3"))])] [(.call (.resolve "v1") [(.binary .div (.call (.resolve "trace") [.num 1]) (.num 0)), (.index (.listLiteral [(.call (.resolve "trace") [.num 2])]) [.num 5])]), (.listLiteral [.resolve "v4", .resolve "v4"]), .num 997])
#guard obs case_sem2b_2Fv1_2Fseed_2F5EED2B000005_2F3 == "err div0"
#guard errorObs case_sem2b_2Fv1_2Fseed_2F5EED2B000005_2F3 == .matched (some { kind := "div0", names := [], counts := [] })

-- sem2b/v1/seed/5EED2B000005/5: v1(meta v2) = v2 \n v3 = v1 \n v4(v5, v6, v7) = (v5 * 100) + (v6 * 10) + v7 \n v8 = v3(5) \n [v8.Invoke()] \n 997
def case_sem2b_2Fv1_2Fseed_2F5EED2B000005_2F5 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v3" (.alias none [] [] (.resolve "v1")), privateProp "v8" (alg [] [] [] [(.call (.resolve "v3") [.num 5])]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (algWithParameters [{ name := "v2", kind := .metaRef }] [] [] [.param "v2"]), privateProp "v4" (alg ["v5", "v6", "v7"] [] [] [(.binary .add (.binary .add (.binary .mul (.param "v5") (.num 100)) (.binary .mul (.param "v6") (.num 10))) (.param "v7"))])] [(.listLiteral [(.dotCall (.resolve "v8") "Invoke" (some []))]), .num 997])
#guard obs case_sem2b_2Fv1_2Fseed_2F5EED2B000005_2F5 == "err notAnAlgorithm"

-- sem2b/v1/seed/5EED2B000005/6: v1([v2, *v3]) = v2 + count(v3) \n v1([1, 2, 3]) \n 997
def case_sem2b_2Fv1_2Fseed_2F5EED2B000005_2F6 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (algWithParameterPatterns [.listValue [.capture { name := "v2" }, .capture { name := "v3", kind := .collecting }]] [] [] [(.binary .add (.param "v2") (.call (.resolve "count") [.param "v3"]))])] [(.call (.resolve "v1") [(.listLiteral [.num 1, .num 2, .num 3])]), .num 997])
#guard obs case_sem2b_2Fv1_2Fseed_2F5EED2B000005_2F6 == "ok raw=S[3, 997] n=2"

-- sem2b/v1/seed/5EED2B000005/7: v1 = 11, 12, 13 \n v3 = { \n   v2 = 0 \n   v1[2] \n } \n if(true, 1, trace(666) / 0) \n [wait(2), wait(3)] \n [v3, v3] \n 997
def case_sem2b_2Fv1_2Fseed_2F5EED2B000005_2F7 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v1" (alg [] [] [] [.num 11, .num 12, .num 13]), privateProp "v3" (alg [] [] [privateProp "v2" (alg [] [] [] [.num 0])] [(.index (.resolve "v1") [.num 2])]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"])] [(.call (.resolve "if") [.boolLiteral true, .num 1, (.binary .div (.call (.resolve "trace") [.num 666]) (.num 0))]), (.listLiteral [(.call (.resolve "wait") [.num 2]), (.call (.resolve "wait") [.num 3])]), (.listLiteral [.resolve "v3", .resolve "v3"]), .num 997])
#guard obs case_sem2b_2Fv1_2Fseed_2F5EED2B000005_2F7 == "ok raw=S[1, L[2, 3], L[13, 13], 997] n=4"

-- sem2b/v1/seed/5EED2B000005/8: v2(v3, v4) = v3 + v4 \n v5(v6) = v6 \n v5(v2([11, 12, 13][0, 1]*)) \n 997
def case_sem2b_2Fv1_2Fseed_2F5EED2B000005_2F8 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v2" (alg ["v3", "v4"] [] [] [(.binary .add (.param "v3") (.param "v4"))]), privateProp "v5" (alg ["v6"] [] [] [.param "v6"])] [(.call (.resolve "v5") [(.call (.resolve "v2") [(.sequenceSpread (.index (.listLiteral [.num 11, .num 12, .num 13]) [.num 0, .num 1]))])]), .num 997])
#guard obs case_sem2b_2Fv1_2Fseed_2F5EED2B000005_2F8 == "ok raw=S[23, 997] n=2"

-- sem2b/v1/seed/5EED2B000005/9: v1 = 11, 12, 13 \n v2(v3) = v3 + v3 \n v4 = v2(wait(1)) \n v5(*v6) = v6[0] + 1 \n if(true, v1[9], trace(666)) \n v4 \n repeat(v5(2), 4) \n 997
def case_sem2b_2Fv1_2Fseed_2F5EED2B000005_2F9 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v1" (alg [] [] [] [.num 11, .num 12, .num 13]), privateProp "v4" (alg [] [] [] [(.call (.resolve "v2") [(.call (.resolve "wait") [.num 1])])]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v2" (alg ["v3"] [] [] [(.binary .add (.param "v3") (.param "v3"))]), privateProp "v5" (algWithParameters [{ name := "v6", kind := .collecting }] [] [] [(.binary .add (.index (.param "v6") [.num 0]) (.num 1))])] [(.call (.resolve "if") [.boolLiteral true, (.index (.resolve "v1") [.num 9]), (.call (.resolve "trace") [.num 666])]), .resolve "v4", (.call (.resolve "repeat") [(.call (.resolve "v5") [.num 2]), .num 4]), .num 997])
#guard obs case_sem2b_2Fv1_2Fseed_2F5EED2B000005_2F9 == "err index"
#guard errorObs case_sem2b_2Fv1_2Fseed_2F5EED2B000005_2F9 == .matched (some { kind := "index", names := [], counts := [] })

-- sem2b/v1/seed/5EED2B000005/10: v1(v2, v3) = v2 \n v4 = if(false, trace(666), v1(trace(1), trace(666) / 0)) \n [v4, v4] \n 997
def case_sem2b_2Fv1_2Fseed_2F5EED2B000005_2F10 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v4" (alg [] [] [] [(.call (.resolve "if") [.boolLiteral false, (.call (.resolve "trace") [.num 666]), (.call (.resolve "v1") [(.call (.resolve "trace") [.num 1]), (.binary .div (.call (.resolve "trace") [.num 666]) (.num 0))])])]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (alg ["v2", "v3"] [] [] [.param "v2"])] [(.listLiteral [.resolve "v4", .resolve "v4"]), .num 997])
#guard obs case_sem2b_2Fv1_2Fseed_2F5EED2B000005_2F10 == "ok raw=S[L[1, 1], 997] n=2"

-- sem2b/v1/seed/5EED2B000005/11: v1(meta v2) = v2 \n v3(v4) = v1(v4) \n v5(v6, v7, v8) = trace((v6 * 100) + (v7 * 10) + v8) \n v9 = v3(v5(trace(1), trace(2), trace(3))) \n v10 = if(true, [v9.Arguments[0], v9.Arguments[1]], trace(666)) \n v11 = trace(4) \n [v10, v10] \n [v11, v11()] \n 997
def case_sem2b_2Fv1_2Fseed_2F5EED2B000005_2F11 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v9" (alg [] [] [] [(.call (.resolve "v3") [(.call (.resolve "v5") [(.call (.resolve "trace") [.num 1]), (.call (.resolve "trace") [.num 2]), (.call (.resolve "trace") [.num 3])])])]), privateProp "v10" (alg [] [] [] [(.call (.resolve "if") [.boolLiteral true, (.listLiteral [(.index (.dotCall (.resolve "v9") "Arguments" none) [.num 0]), (.index (.dotCall (.resolve "v9") "Arguments" none) [.num 1])]), (.call (.resolve "trace") [.num 666])])]), privateProp "v11" (alg [] [] [] [(.call (.resolve "trace") [.num 4])]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (algWithParameters [{ name := "v2", kind := .metaRef }] [] [] [.param "v2"]), privateProp "v3" (alg ["v4"] [] [] [(.call (.resolve "v1") [.param "v4"])]), privateProp "v5" (alg ["v6", "v7", "v8"] [] [] [(.call (.resolve "trace") [(.binary .add (.binary .add (.binary .mul (.param "v6") (.num 100)) (.binary .mul (.param "v7") (.num 10))) (.param "v8"))])])] [(.listLiteral [.resolve "v10", .resolve "v10"]), (.listLiteral [.resolve "v11", (.call (.resolve "v11") [])]), .num 997])
#guard obs case_sem2b_2Fv1_2Fseed_2F5EED2B000005_2F11 == "ok raw=S[L[L[1, 2], L[1, 2]], L[4, 4], 997] n=3"

-- sem2b/v1/seed/5EED2B000005/12: v1 = trace(1) \n v2(meta v3) = v3 \n v4(v5, v6) = (v5 * 10) + v6 \n v7 = v2(v4(trace(2), trace(3))) \n v8 = v7.Algorithm \n v9(v10) = v10 \n v11(v12) = { \n   v13 = trace(v12) \n   v13 + v13 \n } \n [v1(), v1] \n v9([v8(4, 5)]) \n if(false, trace(666), if(false, trace(666), [v11(6), v11(6)])) \n 997
def case_sem2b_2Fv1_2Fseed_2F5EED2B000005_2F12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v1" (alg [] [] [] [(.call (.resolve "trace") [.num 1])]), privateProp "v7" (alg [] [] [] [(.call (.resolve "v2") [(.call (.resolve "v4") [(.call (.resolve "trace") [.num 2]), (.call (.resolve "trace") [.num 3])])])]), privateProp "v8" (.alias none [] [] ((.dotCall (.resolve "v7") "Algorithm" none))), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v2" (algWithParameters [{ name := "v3", kind := .metaRef }] [] [] [.param "v3"]), privateProp "v4" (alg ["v5", "v6"] [] [] [(.binary .add (.binary .mul (.param "v5") (.num 10)) (.param "v6"))]), privateProp "v9" (alg ["v10"] [] [] [.param "v10"]), privateProp "v11" (alg ["v12"] [] [{ (privateLocalProp "v13" (.localCapturedAncestorParams ["v12"]) (alg [] [] [] [(.call (.resolve "trace") [.param "v12"])])) with requiredOwnerDepths := some [("v12", some 0)] }] [(.binary .add (.resolve "v13") (.resolve "v13"))])] [(.listLiteral [(.call (.resolve "v1") []), .resolve "v1"]), (.call (.resolve "v9") [(.listLiteral [(.call (.resolve "v8") [.num 4, .num 5])])]), (.call (.resolve "if") [.boolLiteral false, (.call (.resolve "trace") [.num 666]), (.call (.resolve "if") [.boolLiteral false, (.call (.resolve "trace") [.num 666]), (.listLiteral [(.call (.resolve "v11") [.num 6]), (.call (.resolve "v11") [.num 6])])])]), .num 997])
#guard obs case_sem2b_2Fv1_2Fseed_2F5EED2B000005_2F12 == "ok raw=S[L[1, 1], L[45], L[12, 12], 997] n=4"

-- sem2b/v1/seed/5EED2B000005/13: v1(meta v2) = v2 \n v3(v4) = v1(v4) \n v5(*v6) = count(v6) \n v7 = v3(v5(trace(1), trace(2))) \n v8(v9, v10) = v9 \n [v8(v7.Arguments*), v7.Arguments.count] \n 997
def case_sem2b_2Fv1_2Fseed_2F5EED2B000005_2F13 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v7" (alg [] [] [] [(.call (.resolve "v3") [(.call (.resolve "v5") [(.call (.resolve "trace") [.num 1]), (.call (.resolve "trace") [.num 2])])])]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (algWithParameters [{ name := "v2", kind := .metaRef }] [] [] [.param "v2"]), privateProp "v3" (alg ["v4"] [] [] [(.call (.resolve "v1") [.param "v4"])]), privateProp "v5" (algWithParameters [{ name := "v6", kind := .collecting }] [] [] [(.call (.resolve "count") [.param "v6"])]), privateProp "v8" (alg ["v9", "v10"] [] [] [.param "v9"])] [(.listLiteral [(.call (.resolve "v8") [(.sequenceSpread (.dotCall (.resolve "v7") "Arguments" none))]), (.dotCall (.dotCall (.resolve "v7") "Arguments" none) "count" none)]), .num 997])
#guard obs case_sem2b_2Fv1_2Fseed_2F5EED2B000005_2F13 == "ok raw=S[L[1, 2], 997] n=2"

-- sem2b/v1/seed/5EED2B000005/14: v1(*v2, v3) = v2 \n v4(*v5) = v1(v5*) \n { \n   v6 = 0 \n   if(true, v4(trace(2), trace(3), trace(1)), trace(666)) \n } \n 997
def case_sem2b_2Fv1_2Fseed_2F5EED2B000005_2F14 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (algWithParameters [{ name := "v2", kind := .collecting }, { name := "v3" }] [] [] [.param "v2"]), privateProp "v4" (algWithParameters [{ name := "v5", kind := .collecting }] [] [] [(.call (.resolve "v1") [(.sequenceSpread (.param "v5"))])])] [(.algorithmExpr (alg [] [] [privateProp "v6" (alg [] [] [] [.num 0])] [(.call (.resolve "if") [.boolLiteral true, (.call (.resolve "v4") [(.call (.resolve "trace") [.num 2]), (.call (.resolve "trace") [.num 3]), (.call (.resolve "trace") [.num 1])]), (.call (.resolve "trace") [.num 666])])])), .num 997])
#guard obs case_sem2b_2Fv1_2Fseed_2F5EED2B000005_2F14 == "ok raw=S[L[2, 3], 997] n=2"

-- sem2b/v1/seed/5EED2B000005/15: v1(v2) = v2 + 1 \n v3(v4) = { \n   v1(v5) = v5 + 100 \n   v1(v4) \n } \n v8(v9) = wait(v9) + 1 \n v10(v11) = v11 \n { \n   v7 = 0 \n   { \n     v6 = 0 \n     [v3(1), v1(1)] \n   } \n } \n v10(repeat(v8(2), 3)) \n 997
def case_sem2b_2Fv1_2Fseed_2F5EED2B000005_2F15 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (alg ["v2"] [] [] [(.binary .add (.param "v2") (.num 1))]), privateProp "v3" (alg ["v4"] [] [privateProp "v1" (alg ["v5"] [] [] [(.binary .add (.param "v5") (.num 100))])] [(.call (.resolve "v1") [.param "v4"])]), privateProp "v8" (alg ["v9"] [] [] [(.binary .add (.call (.resolve "wait") [.param "v9"]) (.num 1))]), privateProp "v10" (alg ["v11"] [] [] [.param "v11"])] [(.algorithmExpr (alg [] [] [privateProp "v7" (alg [] [] [] [.num 0])] [(.algorithmExpr (alg [] [] [privateProp "v6" (alg [] [] [] [.num 0])] [(.listLiteral [(.call (.resolve "v3") [.num 1]), (.call (.resolve "v1") [.num 1])])]))])), (.call (.resolve "v10") [(.call (.resolve "repeat") [(.call (.resolve "v8") [.num 2]), .num 3])]), .num 997])
#guard obs case_sem2b_2Fv1_2Fseed_2F5EED2B000005_2F15 == "ok raw=S[L[101, 2], 5, 997] n=3"

-- sem2b/v1/seed/5EED2B000006/0: v1(v2, v3) = v2 \n if(true, v1(trace(1), trace(666) / 0), trace(666)) \n 997
def case_sem2b_2Fv1_2Fseed_2F5EED2B000006_2F0 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (alg ["v2", "v3"] [] [] [.param "v2"])] [(.call (.resolve "if") [.boolLiteral true, (.call (.resolve "v1") [(.call (.resolve "trace") [.num 1]), (.binary .div (.call (.resolve "trace") [.num 666]) (.num 0))]), (.call (.resolve "trace") [.num 666])]), .num 997])
#guard obs case_sem2b_2Fv1_2Fseed_2F5EED2B000006_2F0 == "ok raw=S[1, 997] n=2"

-- sem2b/v1/seed/5EED2B000006/1: v1(v2, v3) = v2 \n if(false, trace(666), [v1(trace(1), trace(666) / 0)]) \n 997
def case_sem2b_2Fv1_2Fseed_2F5EED2B000006_2F1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (alg ["v2", "v3"] [] [] [.param "v2"])] [(.call (.resolve "if") [.boolLiteral false, (.call (.resolve "trace") [.num 666]), (.listLiteral [(.call (.resolve "v1") [(.call (.resolve "trace") [.num 1]), (.binary .div (.call (.resolve "trace") [.num 666]) (.num 0))])])]), .num 997])
#guard obs case_sem2b_2Fv1_2Fseed_2F5EED2B000006_2F1 == "ok raw=S[L[1], 997] n=2"

-- sem2b/v1/seed/5EED2B000006/3: v1(v2) = v2 + 1 \n v3(v4) = { \n   v1(v5) = v5 + 100 \n   v1(v4) \n } \n v6(v7) = v7 + v7 \n v8(v9) = v9 + v9 \n [v3(1), v1(1)] \n if(true, v6(wait(2)), trace(666)) \n [v8(trace(3))] \n 997
def case_sem2b_2Fv1_2Fseed_2F5EED2B000006_2F3 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (alg ["v2"] [] [] [(.binary .add (.param "v2") (.num 1))]), privateProp "v3" (alg ["v4"] [] [privateProp "v1" (alg ["v5"] [] [] [(.binary .add (.param "v5") (.num 100))])] [(.call (.resolve "v1") [.param "v4"])]), privateProp "v6" (alg ["v7"] [] [] [(.binary .add (.param "v7") (.param "v7"))]), privateProp "v8" (alg ["v9"] [] [] [(.binary .add (.param "v9") (.param "v9"))])] [(.listLiteral [(.call (.resolve "v3") [.num 1]), (.call (.resolve "v1") [.num 1])]), (.call (.resolve "if") [.boolLiteral true, (.call (.resolve "v6") [(.call (.resolve "wait") [.num 2])]), (.call (.resolve "trace") [.num 666])]), (.listLiteral [(.call (.resolve "v8") [(.call (.resolve "trace") [.num 3])])]), .num 997])
#guard obs case_sem2b_2Fv1_2Fseed_2F5EED2B000006_2F3 == "ok raw=S[L[101, 2], 4, L[6], 997] n=4"

-- sem2b/v1/seed/5EED2B000006/4: v1(meta v2) = v2 \n v3(v4, v5) = (v4 * 10) + v5 \n v6 = v1(v3(trace(1), trace(2))) \n v7 = v6.Algorithm \n [v7(3, 4)] \n 997
def case_sem2b_2Fv1_2Fseed_2F5EED2B000006_2F4 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v6" (alg [] [] [] [(.call (.resolve "v1") [(.call (.resolve "v3") [(.call (.resolve "trace") [.num 1]), (.call (.resolve "trace") [.num 2])])])]), privateProp "v7" (.alias none [] [] ((.dotCall (.resolve "v6") "Algorithm" none))), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (algWithParameters [{ name := "v2", kind := .metaRef }] [] [] [.param "v2"]), privateProp "v3" (alg ["v4", "v5"] [] [] [(.binary .add (.binary .mul (.param "v4") (.num 10)) (.param "v5"))])] [(.listLiteral [(.call (.resolve "v7") [.num 3, .num 4])]), .num 997])
#guard obs case_sem2b_2Fv1_2Fseed_2F5EED2B000006_2F4 == "ok raw=S[L[34], 997] n=2"

-- sem2b/v1/seed/5EED2B000006/5: v1(v2) = { \n   v3 = trace(v2) \n   v3 + v3 \n } \n v4 = [v1(1), v1(1)] \n v5 = trace(2) \n v6(meta v7) = v7 \n v8(v9) = v9 \n v10 = v6(v8(3)) \n v11 = v10.Algorithm \n v12(v13) = v13 \n [v4, v4] \n [v5(), v5] \n v12(v11) \n 997
def case_sem2b_2Fv1_2Fseed_2F5EED2B000006_2F5 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v4" (alg [] [] [] [(.listLiteral [(.call (.resolve "v1") [.num 1]), (.call (.resolve "v1") [.num 1])])]), privateProp "v5" (alg [] [] [] [(.call (.resolve "trace") [.num 2])]), privateProp "v10" (alg [] [] [] [(.call (.resolve "v6") [(.call (.resolve "v8") [.num 3])])]), privateProp "v11" (.alias none [] [] ((.dotCall (.resolve "v10") "Algorithm" none))), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (alg ["v2"] [] [{ (privateLocalProp "v3" (.localCapturedAncestorParams ["v2"]) (alg [] [] [] [(.call (.resolve "trace") [.param "v2"])])) with requiredOwnerDepths := some [("v2", some 0)] }] [(.binary .add (.resolve "v3") (.resolve "v3"))]), privateProp "v6" (algWithParameters [{ name := "v7", kind := .metaRef }] [] [] [.param "v7"]), privateProp "v8" (alg ["v9"] [] [] [.param "v9"]), privateProp "v12" (alg ["v13"] [] [] [.param "v13"])] [(.listLiteral [.resolve "v4", .resolve "v4"]), (.listLiteral [(.call (.resolve "v5") []), .resolve "v5"]), (.call (.resolve "v12") [.resolve "v11"]), .num 997])
#guard obs case_sem2b_2Fv1_2Fseed_2F5EED2B000006_2F5 == "err arity"
#guard errorObs case_sem2b_2Fv1_2Fseed_2F5EED2B000006_2F5 == .matched (some { kind := "arity", names := [], counts := [1, 0] })

-- sem2b/v1/seed/5EED2B000006/6: v1([v2, *v3]) = v2 + count(v3) \n v4 = 11, 12, 13 \n v5(v6) = { \n   v7(v8) = v8 + v6 \n   v7(2) \n } \n v9(v10) = v10 \n v1([1]) \n v4[1 / 0, 9] \n v9([v5(14), v5(15)]) \n 997
def case_sem2b_2Fv1_2Fseed_2F5EED2B000006_2F6 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v4" (alg [] [] [] [.num 11, .num 12, .num 13]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (algWithParameterPatterns [.listValue [.capture { name := "v2" }, .capture { name := "v3", kind := .collecting }]] [] [] [(.binary .add (.param "v2") (.call (.resolve "count") [.param "v3"]))]), privateProp "v5" (alg ["v6"] [] [{ (privateLocalProp "v7" (.localCapturedAncestorParams ["v6"]) (alg ["v8"] [] [] [(.binary .add (.param "v8") (.param "v6"))])) with requiredOwnerDepths := some [("v6", some 0)] }] [(.call (.resolve "v7") [.num 2])]), privateProp "v9" (alg ["v10"] [] [] [.param "v10"])] [(.call (.resolve "v1") [(.listLiteral [.num 1])]), (.index (.resolve "v4") [(.binary .div (.num 1) (.num 0)), .num 9]), (.call (.resolve "v9") [(.listLiteral [(.call (.resolve "v5") [.num 14]), (.call (.resolve "v5") [.num 15])])]), .num 997])
#guard obs case_sem2b_2Fv1_2Fseed_2F5EED2B000006_2F6 == "err div0"
#guard errorObs case_sem2b_2Fv1_2Fseed_2F5EED2B000006_2F6 == .matched (some { kind := "div0", names := [], counts := [] })

-- sem2b/v1/seed/5EED2B000006/7: v1(v2) = v2 + 1 \n v3(v4) = { \n   v1(v5) = v5 + 100 \n   v1(v4) \n } \n v6 = [v3(1), v1(1)] \n v7(0) = 100 \n v7(v8) = v8 + 1 \n v9(meta v10) = v10 \n v11(v12, v13) = (v12 * 10) + v13 \n v14 = v9(v11(wait(3), wait(4))) \n v15 = [v14.Arguments[1], v14.Invoke()] \n if(false, trace(666), v6) \n repeat(v7(2), 4) \n [v15] \n 997
def case_sem2b_2Fv1_2Fseed_2F5EED2B000006_2F7 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v6" (alg [] [] [] [(.listLiteral [(.call (.resolve "v3") [.num 1]), (.call (.resolve "v1") [.num 1])])]), privateProp "v14" (alg [] [] [] [(.call (.resolve "v9") [(.call (.resolve "v11") [(.call (.resolve "wait") [.num 3]), (.call (.resolve "wait") [.num 4])])])]), privateProp "v15" (alg [] [] [] [(.listLiteral [(.index (.dotCall (.resolve "v14") "Arguments" none) [.num 1]), (.dotCall (.resolve "v14") "Invoke" (some []))])]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (alg ["v2"] [] [] [(.binary .add (.param "v2") (.num 1))]), privateProp "v3" (alg ["v4"] [] [privateProp "v1" (alg ["v5"] [] [] [(.binary .add (.param "v5") (.num 100))])] [(.call (.resolve "v1") [.param "v4"])]), privateProp "v7" (.conditional none [] [⟨.litInt 0, (alg [] [] [] [.num 100])⟩, ⟨.bind "v8", (alg [] [] [] [(.binary .add (.param "v8") (.num 1))])⟩]), privateProp "v9" (algWithParameters [{ name := "v10", kind := .metaRef }] [] [] [.param "v10"]), privateProp "v11" (alg ["v12", "v13"] [] [] [(.binary .add (.binary .mul (.param "v12") (.num 10)) (.param "v13"))])] [(.call (.resolve "if") [.boolLiteral false, (.call (.resolve "trace") [.num 666]), .resolve "v6"]), (.call (.resolve "repeat") [(.call (.resolve "v7") [.num 2]), .num 4]), (.listLiteral [.resolve "v15"]), .num 997])
#guard obs case_sem2b_2Fv1_2Fseed_2F5EED2B000006_2F7 == "ok raw=S[L[101, 2], 6, L[L[4, 34]], 997] n=4"

-- sem2b/v1/seed/5EED2B000006/8: v1(meta v2) = v2 \n v3(v4) = v4 \n v5 = v1(v3(1)) \n v6 = v5.Algorithm \n v7(v8) = v8 \n v9(meta v10) = v10.Algorithm(v10.Arguments*).repeat(4) \n v11(v12) = v12 + 1 \n v13 = 11, 12, 13 \n if(true, v7(v6), trace(666)) \n if(true, if(false, trace(666), v9(v11(2))), trace(666)) \n if(false, trace(666), v13[2]) \n 997
def case_sem2b_2Fv1_2Fseed_2F5EED2B000006_2F8 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v5" (alg [] [] [] [(.call (.resolve "v1") [(.call (.resolve "v3") [.num 1])])]), privateProp "v6" (.alias none [] [] ((.dotCall (.resolve "v5") "Algorithm" none))), privateProp "v13" (alg [] [] [] [.num 11, .num 12, .num 13]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (algWithParameters [{ name := "v2", kind := .metaRef }] [] [] [.param "v2"]), privateProp "v3" (alg ["v4"] [] [] [.param "v4"]), privateProp "v7" (alg ["v8"] [] [] [.param "v8"]), privateProp "v9" (algWithParameters [{ name := "v10", kind := .metaRef }] [] [] [(.dotCall (.dotCall (.param "v10") "Algorithm" (some [(.sequenceSpread (.dotCall (.param "v10") "Arguments" none))])) "repeat" (some [.num 4]))]), privateProp "v11" (alg ["v12"] [] [] [(.binary .add (.param "v12") (.num 1))])] [(.call (.resolve "if") [.boolLiteral true, (.call (.resolve "v7") [.resolve "v6"]), (.call (.resolve "trace") [.num 666])]), (.call (.resolve "if") [.boolLiteral true, (.call (.resolve "if") [.boolLiteral false, (.call (.resolve "trace") [.num 666]), (.call (.resolve "v9") [(.call (.resolve "v11") [.num 2])])]), (.call (.resolve "trace") [.num 666])]), (.call (.resolve "if") [.boolLiteral false, (.call (.resolve "trace") [.num 666]), (.index (.resolve "v13") [.num 2])]), .num 997])
#guard obs case_sem2b_2Fv1_2Fseed_2F5EED2B000006_2F8 == "err arity"
#guard errorObs case_sem2b_2Fv1_2Fseed_2F5EED2B000006_2F8 == .matched (some { kind := "arity", names := [], counts := [1, 0] })

-- sem2b/v1/seed/5EED2B000006/9: v1 = wait(1) \n v2 = [v1, v1] \n v3 = v2 \n v4(v5) = v5 + v5 \n v6 = v4(trace(2)) \n v7(v8) = v8 \n v3 \n v7([v6, v6]) \n 997
def case_sem2b_2Fv1_2Fseed_2F5EED2B000006_2F9 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v1" (alg [] [] [] [(.call (.resolve "wait") [.num 1])]), privateProp "v2" (alg [] [] [] [(.listLiteral [.resolve "v1", .resolve "v1"])]), privateProp "v3" (.alias none [] [] (.resolve "v2")), privateProp "v6" (alg [] [] [] [(.call (.resolve "v4") [(.call (.resolve "trace") [.num 2])])]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v4" (alg ["v5"] [] [] [(.binary .add (.param "v5") (.param "v5"))]), privateProp "v7" (alg ["v8"] [] [] [.param "v8"])] [.resolve "v3", (.call (.resolve "v7") [(.listLiteral [.resolve "v6", .resolve "v6"])]), .num 997])
#guard obs case_sem2b_2Fv1_2Fseed_2F5EED2B000006_2F9 == "ok raw=S[L[1, 1], L[4, 4], 997] n=3"

-- sem2b/v1/seed/5EED2B000006/10: v1(v2) = v2 \n v4(v5) = v5 \n if(true, 1, trace(666) / 0) \n [v1(if(true, 2, trace(666) / 0))] \n if(true, v4([11, 12, 13][1]), trace(666)) \n 997
def case_sem2b_2Fv1_2Fseed_2F5EED2B000006_2F10 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (alg ["v2"] [] [] [.param "v2"]), privateProp "v4" (alg ["v5"] [] [] [.param "v5"])] [(.call (.resolve "if") [.boolLiteral true, .num 1, (.binary .div (.call (.resolve "trace") [.num 666]) (.num 0))]), (.listLiteral [(.call (.resolve "v1") [(.call (.resolve "if") [.boolLiteral true, .num 2, (.binary .div (.call (.resolve "trace") [.num 666]) (.num 0))])])]), (.call (.resolve "if") [.boolLiteral true, (.call (.resolve "v4") [(.index (.listLiteral [.num 11, .num 12, .num 13]) [.num 1])]), (.call (.resolve "trace") [.num 666])]), .num 997])
#guard obs case_sem2b_2Fv1_2Fseed_2F5EED2B000006_2F10 == "ok raw=S[1, L[2], 12, 997] n=4"

-- sem2b/v1/seed/5EED2B000006/11: v1 = trace(1) \n v2 = [v1, v1()] \n v3(*v4) = v4[0] + 1 \n if(true, v2, trace(666)) \n [v3(2).repeat(2)] \n 997
def case_sem2b_2Fv1_2Fseed_2F5EED2B000006_2F11 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v1" (alg [] [] [] [(.call (.resolve "trace") [.num 1])]), privateProp "v2" (alg [] [] [] [(.listLiteral [.resolve "v1", (.call (.resolve "v1") [])])]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v3" (algWithParameters [{ name := "v4", kind := .collecting }] [] [] [(.binary .add (.index (.param "v4") [.num 0]) (.num 1))])] [(.call (.resolve "if") [.boolLiteral true, .resolve "v2", (.call (.resolve "trace") [.num 666])]), (.listLiteral [(.dotCall (.call (.resolve "v3") [.num 2]) "repeat" (some [.num 2]))]), .num 997])
#guard obs case_sem2b_2Fv1_2Fseed_2F5EED2B000006_2F11 == "ok raw=S[L[1, 1], L[4], 997] n=3"

-- sem2b/v1/seed/5EED2B000006/12: v1(v2, v3) = v2 + v3 \n v1(trace(1), trace(2), trace(3)) \n { \n   v4 = 0 \n   [wait(4), wait(5)] \n } \n 997
def case_sem2b_2Fv1_2Fseed_2F5EED2B000006_2F12 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (alg ["v2", "v3"] [] [] [(.binary .add (.param "v2") (.param "v3"))])] [(.call (.resolve "v1") [(.call (.resolve "trace") [.num 1]), (.call (.resolve "trace") [.num 2]), (.call (.resolve "trace") [.num 3])]), (.algorithmExpr (alg [] [] [privateProp "v4" (alg [] [] [] [.num 0])] [(.listLiteral [(.call (.resolve "wait") [.num 4]), (.call (.resolve "wait") [.num 5])])])), .num 997])
#guard obs case_sem2b_2Fv1_2Fseed_2F5EED2B000006_2F12 == "err arity"
#guard errorObs case_sem2b_2Fv1_2Fseed_2F5EED2B000006_2F12 == .matched (some { kind := "arity", names := [], counts := [2, 3] })

-- sem2b/v1/seed/5EED2B000006/13: v1(v2) = v2 \n v1([[wait(1), 1 / 0, wait(2)]]) \n 997
def case_sem2b_2Fv1_2Fseed_2F5EED2B000006_2F13 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (alg ["v2"] [] [] [.param "v2"])] [(.call (.resolve "v1") [(.listLiteral [(.listLiteral [(.call (.resolve "wait") [.num 1]), (.binary .div (.num 1) (.num 0)), (.call (.resolve "wait") [.num 2])])])]), .num 997])
#guard obs case_sem2b_2Fv1_2Fseed_2F5EED2B000006_2F13 == "err div0"
#guard errorObs case_sem2b_2Fv1_2Fseed_2F5EED2B000006_2F13 == .matched (some { kind := "div0", names := [], counts := [] })

-- sem2b/v1/seed/5EED2B000006/14: v1((v2, *v3)) = (count(v3) * 10) + v2 \n v4 = 1, 2 \n if(true, v1(v4), trace(666)) \n if(true, 3, trace(666) / 0) \n 997
def case_sem2b_2Fv1_2Fseed_2F5EED2B000006_2F14 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v4" (alg [] [] [] [.num 1, .num 2]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (algWithParameterPatterns [.sequenceValue [.capture { name := "v2" }, .capture { name := "v3", kind := .collecting }]] [] [] [(.binary .add (.binary .mul (.call (.resolve "count") [.param "v3"]) (.num 10)) (.param "v2"))])] [(.call (.resolve "if") [.boolLiteral true, (.call (.resolve "v1") [.resolve "v4"]), (.call (.resolve "trace") [.num 666])]), (.call (.resolve "if") [.boolLiteral true, .num 3, (.binary .div (.call (.resolve "trace") [.num 666]) (.num 0))]), .num 997])
#guard obs case_sem2b_2Fv1_2Fseed_2F5EED2B000006_2F14 == "ok raw=S[11, 3, 997] n=3"

-- sem2b/v1/seed/5EED2B000006/15: v1(meta v2) = v2 \n v3(v4) = trace(v4) \n v5 = v1(v3(trace(1))) \n v6 = 11, 12, 13 \n v7 = 14, 15, 16 \n if(false, trace(666), if(true, [v5.Arguments[0], v5.Arguments.count, v5.Arguments[0]], trace(666))) \n [v6[9, (1 / 0)*]] \n if(true, v7[], trace(666)) \n 997
def case_sem2b_2Fv1_2Fseed_2F5EED2B000006_2F15 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v5" (alg [] [] [] [(.call (.resolve "v1") [(.call (.resolve "v3") [(.call (.resolve "trace") [.num 1])])])]), privateProp "v6" (alg [] [] [] [.num 11, .num 12, .num 13]), privateProp "v7" (alg [] [] [] [.num 14, .num 15, .num 16]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (algWithParameters [{ name := "v2", kind := .metaRef }] [] [] [.param "v2"]), privateProp "v3" (alg ["v4"] [] [] [(.call (.resolve "trace") [.param "v4"])])] [(.call (.resolve "if") [.boolLiteral false, (.call (.resolve "trace") [.num 666]), (.call (.resolve "if") [.boolLiteral true, (.listLiteral [(.index (.dotCall (.resolve "v5") "Arguments" none) [.num 0]), (.dotCall (.dotCall (.resolve "v5") "Arguments" none) "count" none), (.index (.dotCall (.resolve "v5") "Arguments" none) [.num 0])]), (.call (.resolve "trace") [.num 666])])]), (.listLiteral [(.index (.resolve "v6") [.num 9, (.sequenceSpread (.binary .div (.num 1) (.num 0)))])]), (.call (.resolve "if") [.boolLiteral true, (.index (.resolve "v7") []), (.call (.resolve "trace") [.num 666])]), .num 997])
#guard obs case_sem2b_2Fv1_2Fseed_2F5EED2B000006_2F15 == "err div0"
#guard errorObs case_sem2b_2Fv1_2Fseed_2F5EED2B000006_2F15 == .matched (some { kind := "div0", names := [], counts := [] })

-- sem2b/v1/seed-nested/5EED2B000001/0: v1(([v2, *v3], v4)) = [v2, count(v3), v4] \n v5 = if(true, v1(([trace(1), trace(2), wait(3), trace(4)], trace(5))), trace(666)) \n v5 \n 997
def case_sem2b_2Fv1_2Fseed_2Dnested_2F5EED2B000001_2F0 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v5" (alg [] [] [] [(.call (.resolve "if") [.boolLiteral true, (.call (.resolve "v1") [(.capture [(.listLiteral [(.call (.resolve "trace") [.num 1]), (.call (.resolve "trace") [.num 2]), (.call (.resolve "wait") [.num 3]), (.call (.resolve "trace") [.num 4])]), (.call (.resolve "trace") [.num 5])])]), (.call (.resolve "trace") [.num 666])])]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (algWithParameterPatterns [.sequenceValue [.listValue [.capture { name := "v2" }, .capture { name := "v3", kind := .collecting }], .capture { name := "v4" }]] [] [] [(.listLiteral [.param "v2", (.call (.resolve "count") [.param "v3"]), .param "v4"])])] [.resolve "v5", .num 997])
#guard obs case_sem2b_2Fv1_2Fseed_2Dnested_2F5EED2B000001_2F0 == "ok raw=S[L[1, 3, 5], 997] n=2"

-- sem2b/v1/seed-nested/5EED2B000001/1: v1([(v2, *v3), v4]) = [v2, count(v3), v4] \n v5 = [v1([(wait(1), trace(2)), trace(3)])] \n [v5, v5] \n 997
def case_sem2b_2Fv1_2Fseed_2Dnested_2F5EED2B000001_2F1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v5" (alg [] [] [] [(.listLiteral [(.call (.resolve "v1") [(.listLiteral [(.capture [(.call (.resolve "wait") [.num 1]), (.call (.resolve "trace") [.num 2])]), (.call (.resolve "trace") [.num 3])])])])]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (algWithParameterPatterns [.listValue [.sequenceValue [.capture { name := "v2" }, .capture { name := "v3", kind := .collecting }], .capture { name := "v4" }]] [] [] [(.listLiteral [.param "v2", (.call (.resolve "count") [.param "v3"]), .param "v4"])])] [(.listLiteral [.resolve "v5", .resolve "v5"]), .num 997])
#guard obs case_sem2b_2Fv1_2Fseed_2Dnested_2F5EED2B000001_2F1 == "ok raw=S[L[L[L[1, 1, 3]], L[L[1, 1, 3]]], 997] n=2"

-- sem2b/v1/seed-nested/5EED2B000001/2: v1(([v2, *v3], v4)) = [v2, count(v3), v4] \n v5 = v1(([trace(1), trace(2), trace(3), trace(4)], trace(5))) \n if(false, trace(666), v5) \n 997
def case_sem2b_2Fv1_2Fseed_2Dnested_2F5EED2B000001_2F2 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "v5" (alg [] [] [] [(.call (.resolve "v1") [(.capture [(.listLiteral [(.call (.resolve "trace") [.num 1]), (.call (.resolve "trace") [.num 2]), (.call (.resolve "trace") [.num 3]), (.call (.resolve "trace") [.num 4])]), (.call (.resolve "trace") [.num 5])])])]), privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (algWithParameterPatterns [.sequenceValue [.listValue [.capture { name := "v2" }, .capture { name := "v3", kind := .collecting }], .capture { name := "v4" }]] [] [] [(.listLiteral [.param "v2", (.call (.resolve "count") [.param "v3"]), .param "v4"])])] [(.call (.resolve "if") [.boolLiteral false, (.call (.resolve "trace") [.num 666]), .resolve "v5"]), .num 997])
#guard obs case_sem2b_2Fv1_2Fseed_2Dnested_2F5EED2B000001_2F2 == "ok raw=S[L[1, 3, 5], 997] n=2"

-- sem2b/v1/seed-nested/5EED2B000001/3: v1([(v2, *v3), v4]) = [v2, count(v3), v4] \n v5(v6) = v6 \n { \n   v7 = 0 \n   v5(v1([99, trace(5)])) \n } \n 997
def case_sem2b_2Fv1_2Fseed_2Dnested_2F5EED2B000001_2F3 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (algWithParameterPatterns [.listValue [.sequenceValue [.capture { name := "v2" }, .capture { name := "v3", kind := .collecting }], .capture { name := "v4" }]] [] [] [(.listLiteral [.param "v2", (.call (.resolve "count") [.param "v3"]), .param "v4"])]), privateProp "v5" (alg ["v6"] [] [] [.param "v6"])] [(.algorithmExpr (alg [] [] [privateProp "v7" (alg [] [] [] [.num 0])] [(.call (.resolve "v5") [(.call (.resolve "v1") [(.listLiteral [.num 99, (.call (.resolve "trace") [.num 5])])])])])), .num 997])
#guard obs case_sem2b_2Fv1_2Fseed_2Dnested_2F5EED2B000001_2F3 == "err type"

-- sem2b/v1/seed-nested/5EED2B000002/0: v1([(v2, *v3), v4]) = [v2, count(v3), v4] \n v5(v6) = v6 \n v5(if(true, v1([(wait(1), wait(2), trace(3), trace(4)), trace(5)]), trace(666))) \n 997
def case_sem2b_2Fv1_2Fseed_2Dnested_2F5EED2B000002_2F0 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (algWithParameterPatterns [.listValue [.sequenceValue [.capture { name := "v2" }, .capture { name := "v3", kind := .collecting }], .capture { name := "v4" }]] [] [] [(.listLiteral [.param "v2", (.call (.resolve "count") [.param "v3"]), .param "v4"])]), privateProp "v5" (alg ["v6"] [] [] [.param "v6"])] [(.call (.resolve "v5") [(.call (.resolve "if") [.boolLiteral true, (.call (.resolve "v1") [(.listLiteral [(.capture [(.call (.resolve "wait") [.num 1]), (.call (.resolve "wait") [.num 2]), (.call (.resolve "trace") [.num 3]), (.call (.resolve "trace") [.num 4])]), (.call (.resolve "trace") [.num 5])])]), (.call (.resolve "trace") [.num 666])])]), .num 997])
#guard obs case_sem2b_2Fv1_2Fseed_2Dnested_2F5EED2B000002_2F0 == "ok raw=S[L[1, 3, 5], 997] n=2"

-- sem2b/v1/seed-nested/5EED2B000002/1: v1([(v2, *v3), v4]) = [v2, count(v3), v4] \n [[v1([(wait(1), wait(2), trace(3), trace(4)), trace(5)])]] \n 997
def case_sem2b_2Fv1_2Fseed_2Dnested_2F5EED2B000002_2F1 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (algWithParameterPatterns [.listValue [.sequenceValue [.capture { name := "v2" }, .capture { name := "v3", kind := .collecting }], .capture { name := "v4" }]] [] [] [(.listLiteral [.param "v2", (.call (.resolve "count") [.param "v3"]), .param "v4"])])] [(.listLiteral [(.listLiteral [(.call (.resolve "v1") [(.listLiteral [(.capture [(.call (.resolve "wait") [.num 1]), (.call (.resolve "wait") [.num 2]), (.call (.resolve "trace") [.num 3]), (.call (.resolve "trace") [.num 4])]), (.call (.resolve "trace") [.num 5])])])])]), .num 997])
#guard obs case_sem2b_2Fv1_2Fseed_2Dnested_2F5EED2B000002_2F1 == "ok raw=S[L[L[L[1, 3, 5]]], 997] n=2"

-- sem2b/v1/seed-nested/5EED2B000002/2: v1([(v2, *v3), v4]) = [v2, count(v3), v4] \n { \n   v5 = 0 \n   if(false, trace(666), v1([99, trace(4)])) \n } \n 997
def case_sem2b_2Fv1_2Fseed_2Dnested_2F5EED2B000002_2F2 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (algWithParameterPatterns [.listValue [.sequenceValue [.capture { name := "v2" }, .capture { name := "v3", kind := .collecting }], .capture { name := "v4" }]] [] [] [(.listLiteral [.param "v2", (.call (.resolve "count") [.param "v3"]), .param "v4"])])] [(.algorithmExpr (alg [] [] [privateProp "v5" (alg [] [] [] [.num 0])] [(.call (.resolve "if") [.boolLiteral false, (.call (.resolve "trace") [.num 666]), (.call (.resolve "v1") [(.listLiteral [.num 99, (.call (.resolve "trace") [.num 4])])])])])), .num 997])
#guard obs case_sem2b_2Fv1_2Fseed_2Dnested_2F5EED2B000002_2F2 == "err type"

-- sem2b/v1/seed-nested/5EED2B000002/3: v1(([v2, *v3], v4)) = [v2, count(v3), v4] \n v5(v6) = v6 \n v5(if(true, v1(([wait(1), trace(2)], trace(3))), trace(666))) \n 997
def case_sem2b_2Fv1_2Fseed_2Dnested_2F5EED2B000002_2F3 : Expr :=
  .algorithmExpr (alg [] [] [privateProp "trace" (alg ["x"] [] [] [.param "x"]), privateProp "wait" (alg ["x"] [] [] [.param "x"]), privateProp "v1" (algWithParameterPatterns [.sequenceValue [.listValue [.capture { name := "v2" }, .capture { name := "v3", kind := .collecting }], .capture { name := "v4" }]] [] [] [(.listLiteral [.param "v2", (.call (.resolve "count") [.param "v3"]), .param "v4"])]), privateProp "v5" (alg ["v6"] [] [] [.param "v6"])] [(.call (.resolve "v5") [(.call (.resolve "if") [.boolLiteral true, (.call (.resolve "v1") [(.capture [(.listLiteral [(.call (.resolve "wait") [.num 1]), (.call (.resolve "trace") [.num 2])]), (.call (.resolve "trace") [.num 3])])]), (.call (.resolve "trace") [.num 666])])]), .num 997])
#guard obs case_sem2b_2Fv1_2Fseed_2Dnested_2F5EED2B000002_2F3 == "ok raw=S[L[1, 1, 3], 997] n=2"

/--
Machine-checked included partition count: the id list is built by the same loop that emits
the guards above, while the expected total is computed independently from the corpus
partition, so a generation bug fails `lake build`.
-/
def includedCaseIds : List String := [
  "sem2b/v1/sys/meta/0",
  "sem2b/v1/sys/meta/1",
  "sem2b/v1/sys/meta/2",
  "sem2b/v1/sys/meta/3",
  "sem2b/v1/sys/meta/4",
  "sem2b/v1/sys/meta/5",
  "sem2b/v1/sys/meta/6",
  "sem2b/v1/sys/meta/7",
  "sem2b/v1/sys/meta-fail/0",
  "sem2b/v1/sys/meta-fail/1",
  "sem2b/v1/sys/meta-fail/2",
  "sem2b/v1/sys/meta-fail/3",
  "sem2b/v1/sys/collect/0",
  "sem2b/v1/sys/collect/1",
  "sem2b/v1/sys/collect/2",
  "sem2b/v1/sys/collect/3",
  "sem2b/v1/sys/collect/4",
  "sem2b/v1/sys/collect/5",
  "sem2b/v1/sys/collect/6",
  "sem2b/v1/sys/collect/7",
  "sem2b/v1/sys/collect-fail/0",
  "sem2b/v1/sys/collect-fail/1",
  "sem2b/v1/sys/collect-fail/2",
  "sem2b/v1/sys/collect-fail/3",
  "sem2b/v1/sys/alias/0",
  "sem2b/v1/sys/alias/1",
  "sem2b/v1/sys/alias/2",
  "sem2b/v1/sys/alias/3",
  "sem2b/v1/sys/alias/4",
  "sem2b/v1/sys/alias/5",
  "sem2b/v1/sys/alias/6",
  "sem2b/v1/sys/alias/7",
  "sem2b/v1/sys/alias-fail/0",
  "sem2b/v1/sys/alias-fail/1",
  "sem2b/v1/sys/alias-fail/2",
  "sem2b/v1/sys/alias-fail/3",
  "sem2b/v1/sys/cache/0",
  "sem2b/v1/sys/cache/1",
  "sem2b/v1/sys/cache/2",
  "sem2b/v1/sys/cache/3",
  "sem2b/v1/sys/cache/4",
  "sem2b/v1/sys/cache/5",
  "sem2b/v1/sys/cache/6",
  "sem2b/v1/sys/cache/7",
  "sem2b/v1/sys/cache-fail/0",
  "sem2b/v1/sys/cache-fail/1",
  "sem2b/v1/sys/cache-fail/2",
  "sem2b/v1/sys/cache-fail/3",
  "sem2b/v1/sys/select/0",
  "sem2b/v1/sys/select/1",
  "sem2b/v1/sys/select/2",
  "sem2b/v1/sys/select/3",
  "sem2b/v1/sys/select/4",
  "sem2b/v1/sys/select/5",
  "sem2b/v1/sys/select/6",
  "sem2b/v1/sys/select/7",
  "sem2b/v1/sys/select-fail/0",
  "sem2b/v1/sys/select-fail/1",
  "sem2b/v1/sys/select-fail/2",
  "sem2b/v1/sys/select-fail/3",
  "sem2b/v1/sys/loop/0",
  "sem2b/v1/sys/loop/1",
  "sem2b/v1/sys/loop/2",
  "sem2b/v1/sys/loop/3",
  "sem2b/v1/sys/loop/4",
  "sem2b/v1/sys/loop/5",
  "sem2b/v1/sys/loop/6",
  "sem2b/v1/sys/loop/7",
  "sem2b/v1/sys/loop-fail/0",
  "sem2b/v1/sys/loop-fail/1",
  "sem2b/v1/sys/loop-fail/2",
  "sem2b/v1/sys/loop-fail/3",
  "sem2b/v1/sys/failure/0",
  "sem2b/v1/sys/failure/1",
  "sem2b/v1/sys/failure/2",
  "sem2b/v1/sys/failure/3",
  "sem2b/v1/sys/failure/4",
  "sem2b/v1/sys/failure/5",
  "sem2b/v1/sys/failure/6",
  "sem2b/v1/sys/failure/7",
  "sem2b/v1/sys/failure-fail/0",
  "sem2b/v1/sys/failure-fail/1",
  "sem2b/v1/sys/failure-fail/2",
  "sem2b/v1/sys/failure-fail/3",
  "sem2b/v1/sys/async/0",
  "sem2b/v1/sys/async/1",
  "sem2b/v1/sys/async/2",
  "sem2b/v1/sys/async/3",
  "sem2b/v1/sys/async/4",
  "sem2b/v1/sys/async/5",
  "sem2b/v1/sys/async/6",
  "sem2b/v1/sys/async/7",
  "sem2b/v1/sys/async-fail/0",
  "sem2b/v1/sys/async-fail/1",
  "sem2b/v1/sys/async-fail/2",
  "sem2b/v1/sys/async-fail/3",
  "sem2b/v1/sys/context/list/alias",
  "sem2b/v1/sys/context/list/cache",
  "sem2b/v1/sys/context/if-true/select",
  "sem2b/v1/sys/context/if-true/loop",
  "sem2b/v1/sys/context/if-false/failure",
  "sem2b/v1/sys/context/if-false/async",
  "sem2b/v1/sys/context/property/meta",
  "sem2b/v1/sys/context/property/collect",
  "sem2b/v1/sys/context/property-double/alias",
  "sem2b/v1/sys/context/property-double/cache",
  "sem2b/v1/sys/context/wrapper/select",
  "sem2b/v1/sys/context/wrapper/loop",
  "sem2b/v1/sys/context/brace/failure",
  "sem2b/v1/sys/context/brace/async",
  "sem2b/v1/sys/pair/meta+cache",
  "sem2b/v1/sys/pair/meta+select-fail",
  "sem2b/v1/sys/pair/collect+select",
  "sem2b/v1/sys/pair/alias+meta",
  "sem2b/v1/sys/pair/cache+async",
  "sem2b/v1/sys/pair/loop+meta",
  "sem2b/v1/sys/pair/select+failure-fail",
  "sem2b/v1/sys/pair/async+collect-fail",
  "sem2b/v1/sys/pair/loop+async",
  "sem2b/v1/sys/pair/collect+cache-fail",
  "sem2b/v1/sys/triple/meta+loop+async",
  "sem2b/v1/sys/triple/collect+meta+failure-fail",
  "sem2b/v1/sys/triple/alias+cache+select",
  "sem2b/v1/sys/cancel/0",
  "sem2b/v1/sys/cancel/1",
  "sem2b/v1/sys/guard/while-condition-first/0",
  "sem2b/v1/sys/guard/nested-pattern/0",
  "sem2b/v1/sys/guard/while-condition-first/1",
  "sem2b/v1/sys/guard/nested-pattern/1",
  "sem2b/v1/sys/guard/while-condition-first/2",
  "sem2b/v1/sys/guard/nested-pattern/2",
  "sem2b/v1/sys/path/LoopShortCircuit/dot-bare",
  "sem2b/v1/sys/path/LoopShortCircuit/plain-bare",
  "sem2b/v1/sys/path/LoopShortCircuit/dot-list",
  "sem2b/v1/sys/path/LoopShortCircuit/plain-property",
  "sem2b/v1/sys/path/LoopShortCircuit/dot-wrapper",
  "sem2b/v1/sys/path/LoopShortCircuit/plain-if-true",
  "sem2b/v1/sys/path/LoopShortCircuit/dot-brace",
  "sem2b/v1/sys/path/LoopShortCircuit/plain-property-double",
  "sem2b/v1/sys/path/LoopShortCircuit/dot-then-cache",
  "sem2b/v1/sys/path/LoopShortCircuit/meta-then-plain-list",
  "sem2b/v1/sys/path/LoopShortCircuit/clause-family-step-dot",
  "sem2b/v1/sys/path/LoopShortCircuit/collecting-step-plain",
  "sem2b/v1/sys/path/LoopShortCircuit/traced-step-dot-wrapper",
  "sem2b/v1/sys/path/LoopFallback/clause-family-1-dot-bare",
  "sem2b/v1/sys/path/LoopFallback/clause-family-2-plain-bare",
  "sem2b/v1/sys/path/LoopFallback/clause-family-3-dot-list",
  "sem2b/v1/sys/path/LoopFallback/clause-family-4-plain-property",
  "sem2b/v1/sys/path/LoopFallback/collecting-1-plain-bare",
  "sem2b/v1/sys/path/LoopFallback/collecting-2-dot-wrapper",
  "sem2b/v1/sys/path/LoopFallback/collecting-3-plain-if-true",
  "sem2b/v1/sys/path/LoopFallback/collecting-4-dot-brace",
  "sem2b/v1/sys/path/LoopFallback/collecting-1-dot-property-double",
  "sem2b/v1/sys/path/LoopFallback/clause-family-2-dot-then-meta",
  "sem2b/v1/sys/path/LoopFallback/collect-then-collecting-3-plain",
  "sem2b/v1/sys/path/GenericInsideOptimizedLoop/trace-1-dot-bare",
  "sem2b/v1/sys/path/GenericInsideOptimizedLoop/trace-2-plain-bare",
  "sem2b/v1/sys/path/GenericInsideOptimizedLoop/trace-3-dot-list",
  "sem2b/v1/sys/path/GenericInsideOptimizedLoop/trace-4-plain-wrapper",
  "sem2b/v1/sys/path/GenericInsideOptimizedLoop/wait-1-dot-bare",
  "sem2b/v1/sys/path/GenericInsideOptimizedLoop/wait-2-plain-property",
  "sem2b/v1/sys/path/GenericInsideOptimizedLoop/wait-3-dot-if-true",
  "sem2b/v1/sys/path/GenericInsideOptimizedLoop/wait-4-plain-brace",
  "sem2b/v1/sys/path/GenericInsideOptimizedLoop/trace-2-dot-then-collect",
  "sem2b/v1/sys/path/GenericInsideOptimizedLoop/cache-then-wait-2-plain",
  "sem2b/v1/seed/5EED2B000001/0",
  "sem2b/v1/seed/5EED2B000001/1",
  "sem2b/v1/seed/5EED2B000001/2",
  "sem2b/v1/seed/5EED2B000001/3",
  "sem2b/v1/seed/5EED2B000001/4",
  "sem2b/v1/seed/5EED2B000001/5",
  "sem2b/v1/seed/5EED2B000001/6",
  "sem2b/v1/seed/5EED2B000001/7",
  "sem2b/v1/seed/5EED2B000001/8",
  "sem2b/v1/seed/5EED2B000001/9",
  "sem2b/v1/seed/5EED2B000001/10",
  "sem2b/v1/seed/5EED2B000001/11",
  "sem2b/v1/seed/5EED2B000001/13",
  "sem2b/v1/seed/5EED2B000001/15",
  "sem2b/v1/seed/5EED2B000002/0",
  "sem2b/v1/seed/5EED2B000002/1",
  "sem2b/v1/seed/5EED2B000002/2",
  "sem2b/v1/seed/5EED2B000002/3",
  "sem2b/v1/seed/5EED2B000002/4",
  "sem2b/v1/seed/5EED2B000002/5",
  "sem2b/v1/seed/5EED2B000002/6",
  "sem2b/v1/seed/5EED2B000002/8",
  "sem2b/v1/seed/5EED2B000002/9",
  "sem2b/v1/seed/5EED2B000002/10",
  "sem2b/v1/seed/5EED2B000002/11",
  "sem2b/v1/seed/5EED2B000002/12",
  "sem2b/v1/seed/5EED2B000002/13",
  "sem2b/v1/seed/5EED2B000002/14",
  "sem2b/v1/seed/5EED2B000002/15",
  "sem2b/v1/seed/5EED2B000003/0",
  "sem2b/v1/seed/5EED2B000003/1",
  "sem2b/v1/seed/5EED2B000003/2",
  "sem2b/v1/seed/5EED2B000003/3",
  "sem2b/v1/seed/5EED2B000003/4",
  "sem2b/v1/seed/5EED2B000003/5",
  "sem2b/v1/seed/5EED2B000003/6",
  "sem2b/v1/seed/5EED2B000003/7",
  "sem2b/v1/seed/5EED2B000003/8",
  "sem2b/v1/seed/5EED2B000003/9",
  "sem2b/v1/seed/5EED2B000003/10",
  "sem2b/v1/seed/5EED2B000003/11",
  "sem2b/v1/seed/5EED2B000003/12",
  "sem2b/v1/seed/5EED2B000003/13",
  "sem2b/v1/seed/5EED2B000003/14",
  "sem2b/v1/seed/5EED2B000003/15",
  "sem2b/v1/seed/5EED2B000004/0",
  "sem2b/v1/seed/5EED2B000004/1",
  "sem2b/v1/seed/5EED2B000004/2",
  "sem2b/v1/seed/5EED2B000004/3",
  "sem2b/v1/seed/5EED2B000004/4",
  "sem2b/v1/seed/5EED2B000004/5",
  "sem2b/v1/seed/5EED2B000004/6",
  "sem2b/v1/seed/5EED2B000004/7",
  "sem2b/v1/seed/5EED2B000004/8",
  "sem2b/v1/seed/5EED2B000004/9",
  "sem2b/v1/seed/5EED2B000004/10",
  "sem2b/v1/seed/5EED2B000004/11",
  "sem2b/v1/seed/5EED2B000004/12",
  "sem2b/v1/seed/5EED2B000004/13",
  "sem2b/v1/seed/5EED2B000004/14",
  "sem2b/v1/seed/5EED2B000004/15",
  "sem2b/v1/seed/5EED2B000005/0",
  "sem2b/v1/seed/5EED2B000005/1",
  "sem2b/v1/seed/5EED2B000005/2",
  "sem2b/v1/seed/5EED2B000005/3",
  "sem2b/v1/seed/5EED2B000005/5",
  "sem2b/v1/seed/5EED2B000005/6",
  "sem2b/v1/seed/5EED2B000005/7",
  "sem2b/v1/seed/5EED2B000005/8",
  "sem2b/v1/seed/5EED2B000005/9",
  "sem2b/v1/seed/5EED2B000005/10",
  "sem2b/v1/seed/5EED2B000005/11",
  "sem2b/v1/seed/5EED2B000005/12",
  "sem2b/v1/seed/5EED2B000005/13",
  "sem2b/v1/seed/5EED2B000005/14",
  "sem2b/v1/seed/5EED2B000005/15",
  "sem2b/v1/seed/5EED2B000006/0",
  "sem2b/v1/seed/5EED2B000006/1",
  "sem2b/v1/seed/5EED2B000006/3",
  "sem2b/v1/seed/5EED2B000006/4",
  "sem2b/v1/seed/5EED2B000006/5",
  "sem2b/v1/seed/5EED2B000006/6",
  "sem2b/v1/seed/5EED2B000006/7",
  "sem2b/v1/seed/5EED2B000006/8",
  "sem2b/v1/seed/5EED2B000006/9",
  "sem2b/v1/seed/5EED2B000006/10",
  "sem2b/v1/seed/5EED2B000006/11",
  "sem2b/v1/seed/5EED2B000006/12",
  "sem2b/v1/seed/5EED2B000006/13",
  "sem2b/v1/seed/5EED2B000006/14",
  "sem2b/v1/seed/5EED2B000006/15",
  "sem2b/v1/seed-nested/5EED2B000001/0",
  "sem2b/v1/seed-nested/5EED2B000001/1",
  "sem2b/v1/seed-nested/5EED2B000001/2",
  "sem2b/v1/seed-nested/5EED2B000001/3",
  "sem2b/v1/seed-nested/5EED2B000002/0",
  "sem2b/v1/seed-nested/5EED2B000002/1",
  "sem2b/v1/seed-nested/5EED2B000002/2",
  "sem2b/v1/seed-nested/5EED2B000002/3"
]
#guard includedCaseIds.length == 264

-- 264 differential cases.
end SemanticGeneratedCases
